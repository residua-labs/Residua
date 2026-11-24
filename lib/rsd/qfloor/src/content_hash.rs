//! `content_hash` / `canonical_repr` — the q/SHA floor, in Rust.
//!
//! BYTE-IDENTICAL mirror of the Python AUTHORITY
//! `src/residua/grow/content_store.py` (`_canonical_repr` / `_canonical_field`
//! → `content_hash = sha256(canonical_repr.encode("utf-8")).hexdigest()`).
//!
//! This is the primitive the ENTIRE trust architecture binds on: every
//! `program_q` / `entry_q` / `verdict_q` / `attestation_q` / `cap_q`, the QBE
//! quotient key, and the distribution key are `content_hash(...)`. The Python
//! is the authority; THIS module is the sealed mirror that moves the q floor
//! onto the Rust executor. Faithfulness is SEALED by
//! `src/residua/verify/content_hash_conformance.py` (Python == Rust hex-q over
//! the corpus, incl. the trust-payload record shapes), NOT asserted by these
//! definitions.
//!
//! --- The canonical string (mirrors `_canonical_repr` / `_canonical_field`) ---
//!
//! A frozen-base dataclass node serializes to `TypeName(field,field,…)` in the
//! Python dataclass's DECLARED FIELD ORDER (positional, order-significant). A
//! tuple field serializes to `[elem,elem,…]` preserving order. Leaves are
//! TYPE-TAGGED so cross-type values can never collide:
//!
//!   * bool  → `bool:True` / `bool:False`   (Python `f"bool:{value}"`)
//!   * int   → `int:{n}`                     (Python `f"int:{value}"`)
//!   * float → `float:{repr}`                (Python `f"float:{value!r}"`)
//!   * str   → `str:{len}:{value}`           (length = Unicode codepoint count)
//!   * None  → `none`
//!
//! TYPE-NAME crux: the Python `content_hash` tags each node with
//! `type(node).__name__` over the `residua.lang.slot_ast` classes. The Rust
//! `Expr` enum variant names DIFFER from those class names in a few spots
//! (`EmptyList` vs Python `EmptyListE`; the Rust enum has no `Neq`/`StrLit` —
//! neither is reachable through the wire decoder). `tag()` below pins the
//! Python class name for every variant; a wrong tag (or a reordered field, or
//! a divergent leaf rendering) computes a DIFFERENT q for the SAME expr and is
//! exactly the [wire_q_mismatch] the seal refuses (§15).
//!
//! LEAF crux — `Num`: Python `Num.value` is a FLOAT, and the wire is
//! integer-core (`Num.value.is_integer()`), so Python renders e.g. `Num(7.0)`
//! as `float:7.0` (`repr(7.0) == "7.0"`). The Rust `Expr::Num` carries an
//! `i64`; we render it as `float:{n}.0` to reproduce Python's
//! `repr(float(n))` byte-for-byte for every integer value in range (the
//! corpus's operands are small; `repr` of an integer-valued float is always
//! `"<int>.0"`). The golden vectors in the unit tests pin this.

use crate::ast::Expr;
use crate::json;
use crate::sha256::sha256_hex;

/// STABLE structural hash of a slot AST expression — hex SHA-256 of its
/// canonical repr's UTF-8 bytes. Byte-identical to the Python
/// `content_store.content_hash`.
pub fn content_hash(expr: &Expr) -> String {
    sha256_hex(canonical_repr(expr).as_bytes())
}

/// Canonical structural serialization of `expr` → a deterministic string,
/// byte-identical to the Python `_canonical_repr`.
pub fn canonical_repr(expr: &Expr) -> String {
    let mut out = String::new();
    write_node(expr, &mut out);
    out
}

// ---------------------------------------------------------------------------
// Leaf renderings — type-tagged, mirroring `_canonical_field`.
// ---------------------------------------------------------------------------

fn leaf_bool(b: bool) -> String {
    // Python `f"bool:{value}"` → `bool:True` / `bool:False`.
    if b {
        "bool:True".to_string()
    } else {
        "bool:False".to_string()
    }
}

fn leaf_int(n: i64) -> String {
    format!("int:{}", n)
}

/// Canonical leaf for `Num(n)` — exact-int + float compat (mirrors Python
/// `content_store._num_value_canonical`).
///
/// * Small ints whose `float` repr is the simple `"<n>.0"` form keep
///   `float:{n}.0` (byte-identical to the pre-exact-int floor).
/// * All other ints (non-IEEE-exact, or scientific-repr like INT64_MIN) use
///   `int:{n}` so neighbors that float-narrowed together become distinct.
fn leaf_num(n: i64) -> String {
    if simple_float_dot_zero(n) {
        format!("float:{}.0", n)
    } else {
        format!("int:{}", n)
    }
}

/// True when Python would emit `float:{n}.0` for this integer (IEEE-exact and
/// `repr(float(n)) == f"{n}.0"`). Empirically holds for every integer with
/// absolute value ≤ 2^53; fails for non-exact ints and for exact powers of two
/// past that range that print in scientific notation.
fn simple_float_dot_zero(n: i64) -> bool {
    let f = n as f64;
    if !f.is_finite() || (f as i64) != n {
        return false;
    }
    // Mirror Python: `f"{n}.0" == repr(float(n))` for the simple-dot form.
    // For |n| ≤ 2^53, IEEE-exact integers always print as `<n>.0` in both
    // CPython and this formatter.
    const MAX_SIMPLE: i64 = 9_007_199_254_740_992; // 2^53
    (-MAX_SIMPLE..=MAX_SIMPLE).contains(&n)
}

fn leaf_str(s: &str) -> String {
    // Python `f"str:{len(value)}:{value}"`; `len` = Unicode codepoint count,
    // which `.chars().count()` reproduces (ASCII keys match either way).
    format!("str:{}:{}", s.chars().count(), s)
}

// ---------------------------------------------------------------------------
// `pyval` — the VALUE domain of the same canonical form. Python `content_hash`
// is called on bare leaves and tuples thereof (schema tags, q-strings, agent
// ids) as well as on AST nodes: `_canonical_field` accepts
// `str | int | bool | None | tuple[…]`. The wire form is
//
//   V ::= {"t":"str","s":<string>} | {"t":"int","s":"<decimal>"}
//       | {"t":"bool","b":<bool>} | {"t":"none"} | {"t":"tuple","xs":[V,…]}
//
// `int` travels as a decimal STRING: JSON numbers cannot carry arbitrary
// width, and Python accepts ints of ANY width (canonical bytes are the digits
// verbatim). Strictly validated: `-?(0|[1-9][0-9]*)` — Python's `str(int)`
// never produces leading zeros, `+`, or `-0`.
// ---------------------------------------------------------------------------

/// A string that can serve as a Python `repr(float)` payload. CPython's
/// grammar: `-?(inf|nan)` or `-? MANT ['e' EXP]` where MANT = digits with at
/// most one '.' (≥1 digit) and EXP = `[+-]?digits` (leading zeros allowed —
/// repr emits `1e-05`). A bare mantissa must carry the '.' — repr never emits
/// "5" for a float. Shared by the `pyval` float leaf and the `num` wire
/// leaf's string form (`Expr::NumF`); mirrored clause-for-clause by
/// `is_float_repr` in evalgleam's content_hash.gleam. Validates, never
/// formats — the substrate cannot re-derive CPython float formatting.
pub(crate) fn is_float_repr(s: &str) -> bool {
    let body = s.strip_prefix('-').unwrap_or(s);
    if matches!(body, "inf" | "nan") {
        return true;
    }
    if body.is_empty() {
        return false;
    }
    let (mant, exp) = match body.split_once('e') {
        Some((m, e)) => (m, Some(e)),
        None => (body, None),
    };
    let dots = mant.bytes().filter(|&b| b == b'.').count();
    let digits = mant.bytes().filter(|b| b.is_ascii_digit()).count();
    if mant.is_empty() || dots > 1 || digits == 0 || dots + digits != mant.len() {
        return false;
    }
    match exp {
        Some(e) => {
            let e = e.strip_prefix(['+', '-']).unwrap_or(e);
            !e.is_empty() && e.bytes().all(|b| b.is_ascii_digit())
        }
        None => dots == 1,
    }
}

fn valid_pyint(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if digits.is_empty() {
        return false;
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return false; // no leading zeros ("007")
    }
    if s.starts_with('-') && digits == "0" {
        return false; // Python str(int) never emits "-0"
    }
    digits.bytes().all(|b| b.is_ascii_digit())
}

/// Canonical bytes of one `pyval` wire value — byte-identical to Python
/// `_canonical_field`. Errors name the offending shape (fail-closed: a bad
/// encoding is never hashed into a wrong-but-plausible q).
/// Exact key-set check: a pyval object must carry exactly `t` plus the listed
/// payload keys — extra keys would make the wire form non-canonical.
fn pyval_keys(v: &json::Json, payload_keys: &[&str]) -> Result<(), String> {
    let kvs = match v {
        json::Json::Obj(kvs) => kvs,
        _ => return Err("pyval must be an object".to_string()),
    };
    let want = 1 + payload_keys.len();
    if kvs.len() != want
        || kvs
            .iter()
            .any(|(k, _)| k != "t" && !payload_keys.contains(&k.as_str()))
    {
        return Err(format!("pyval keys must be exactly t+{:?}", payload_keys));
    }
    Ok(())
}

pub fn canonical_pyval(v: &json::Json) -> Result<String, String> {
    let t = v
        .get("t")
        .and_then(json::Json::as_str)
        .ok_or("pyval missing 't' (str|int|bool|none|tuple)")?;
    match t {
        "str" => {
            pyval_keys(v, &["s"])?;
            let s = v
                .get("s")
                .and_then(json::Json::as_str)
                .ok_or("pyval str missing 's' (string)")?;
            Ok(leaf_str(s))
        }
        "int" => {
            pyval_keys(v, &["s"])?;
            let s = v
                .get("s")
                .and_then(json::Json::as_str)
                .ok_or("pyval int missing 's' (decimal string)")?;
            if !valid_pyint(s) {
                return Err(format!("pyval int not a canonical decimal: {:?}", s));
            }
            Ok(format!("int:{}", s))
        }
        "float" => {
            // Python `float:{value!r}` — the canonical repr string travels
            // verbatim (the producer is Python `repr`; the substrate cannot
            // re-derive CPython float formatting, so it validates + emits).
            pyval_keys(v, &["s"])?;
            let s = v
                .get("s")
                .and_then(json::Json::as_str)
                .ok_or("pyval float missing 's' (repr string)")?;
            if !is_float_repr(s) {
                return Err(format!("pyval float not a float repr: {:?}", s));
            }
            Ok(format!("float:{}", s))
        }
        "bool" => {
            pyval_keys(v, &["b"])?;
            let b = v
                .get("b")
                .and_then(json::Json::as_bool)
                .ok_or("pyval bool missing 'b' (bool)")?;
            Ok(leaf_bool(b))
        }
        "none" => {
            pyval_keys(v, &[])?;
            Ok("none".to_string())
        }
        "tuple" => {
            pyval_keys(v, &["xs"])?;
            let xs = v
                .get("xs")
                .and_then(json::Json::as_arr)
                .ok_or("pyval tuple missing 'xs' (array)")?;
            let mut out = String::from("[");
            for (i, x) in xs.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&canonical_pyval(x)?);
            }
            out.push(']');
            Ok(out)
        }
        other => Err(format!("pyval unknown 't': {:?}", other)),
    }
}

/// `content_hash` over the value domain: sha256 of the `pyval` canonical bytes.
pub fn content_hash_pyval(v: &json::Json) -> Result<String, String> {
    canonical_pyval(v).map(|c| sha256_hex(c.as_bytes()))
}

// ---------------------------------------------------------------------------
// Node serialization — `TypeName(field,field,…)` in Python field order.
// ---------------------------------------------------------------------------

/// Write `TypeName(` + comma-joined field reprs + `)`.
fn write_record(tag: &str, fields: &[FieldRepr], out: &mut String) {
    out.push_str(tag);
    out.push('(');
    for (i, f) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        f.write(out);
    }
    out.push(')');
}

/// One field value — a child node, a tuple of fields, or a leaf literal.
enum FieldRepr<'a> {
    Node(&'a Expr),
    Leaf(String),
    /// A tuple field → `[elem,elem,…]` preserving order.
    Tuple(Vec<FieldRepr<'a>>),
}

impl<'a> FieldRepr<'a> {
    fn write(&self, out: &mut String) {
        match self {
            FieldRepr::Node(e) => write_node(e, out),
            FieldRepr::Leaf(s) => out.push_str(s),
            FieldRepr::Tuple(elems) => {
                out.push('[');
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    e.write(out);
                }
                out.push(']');
            }
        }
    }
}

fn write_node(expr: &Expr, out: &mut String) {
    use Expr::*;
    // Each arm lists the Python slot_ast class name + the fields IN DECLARED
    // ORDER. The mapping is pinned by content_hash_conformance.py over the
    // corpus.
    match expr {
        // --- Literals ---
        Num(n) => write_record("Num", &[FieldRepr::Leaf(leaf_num(*n))], out),
        // Python `Num(float:{value!r})` — the repr string travels verbatim.
        NumF(s) => write_record("Num", &[FieldRepr::Leaf(format!("float:{}", s))], out),
        BoolLit(b) => write_record("BoolLit", &[FieldRepr::Leaf(leaf_bool(*b))], out),
        Var(name) => write_record("Var", &[FieldRepr::Leaf(leaf_str(name))], out),

        // --- Arithmetic (Python fields: left, right) ---
        Add(l, r) => bin("Add", l, r, out),
        Sub(l, r) => bin("Sub", l, r, out),
        Mul(l, r) => bin("Mul", l, r, out),
        Div(l, r) => bin("Div", l, r, out),
        Mod(l, r) => bin("Mod", l, r, out),
        MinE(l, r) => bin("MinE", l, r, out),
        MaxE(l, r) => bin("MaxE", l, r, out),
        // unary (Python field: expr)
        Neg(e) => un("Neg", e, out),
        AbsE(e) => un("AbsE", e, out),

        // --- Comparison (left, right) ---
        Lt(l, r) => bin("Lt", l, r, out),
        Lte(l, r) => bin("Lte", l, r, out),
        Gt(l, r) => bin("Gt", l, r, out),
        Gte(l, r) => bin("Gte", l, r, out),
        EqE(l, r) => bin("EqE", l, r, out),

        // --- Boolean ---
        AndE(l, r) => bin("AndE", l, r, out),
        OrE(l, r) => bin("OrE", l, r, out),
        NotE(e) => un("NotE", e, out),
        Reflect(e) => un("Reflect", e, out),
        ReifyExpr(e) => un("ReifyExpr", e, out),

        // --- Conditional / binding ---
        // Python IfE(cond, then_, else_)
        IfE(c, t, e) => write_record(
            "IfE",
            &[FieldRepr::Node(c), FieldRepr::Node(t), FieldRepr::Node(e)],
            out,
        ),
        // Python Let(var, value, body)
        Let(var, value, body) => write_record(
            "Let",
            &[
                FieldRepr::Leaf(leaf_str(var)),
                FieldRepr::Node(value),
                FieldRepr::Node(body),
            ],
            out,
        ),

        // --- Record ---
        // Python MakeRecord(fields: tuple[tuple[str, Expr], …]); each pair is a
        // tuple → `[str:..:k, canon(v)]`.
        MakeRecord(fields) => {
            let pairs: Vec<FieldRepr> = fields
                .iter()
                .map(|(k, v)| {
                    FieldRepr::Tuple(vec![FieldRepr::Leaf(leaf_str(k)), FieldRepr::Node(v)])
                })
                .collect();
            write_record("MakeRecord", &[FieldRepr::Tuple(pairs)], out)
        }
        // Python FieldAccess(record, field)
        FieldAccess(r, f) => write_record(
            "FieldAccess",
            &[FieldRepr::Node(r), FieldRepr::Leaf(leaf_str(f))],
            out,
        ),

        // --- Option ---
        NoneLit => write_record("NoneLit", &[], out),
        SomeE(e) => write_record("SomeE", &[FieldRepr::Node(e)], out), // field: value
        IsNoneE(e) => write_record("IsNoneE", &[FieldRepr::Node(e)], out), // field: opt
        IsSomeE(e) => write_record("IsSomeE", &[FieldRepr::Node(e)], out), // field: opt
        UnwrapSome(e) => write_record("UnwrapSome", &[FieldRepr::Node(e)], out), // field: opt

        // --- Result ---
        OkE(e) => write_record("OkE", &[FieldRepr::Node(e)], out),   // field: value
        ErrE(e) => write_record("ErrE", &[FieldRepr::Node(e)], out), // field: value
        IsOkE(e) => write_record("IsOkE", &[FieldRepr::Node(e)], out), // field: result
        GetOk(e) => write_record("GetOk", &[FieldRepr::Node(e)], out), // field: result

        // --- Residue ρ ---
        ResidueE(e) => write_record("ResidueE", &[FieldRepr::Node(e)], out), // field: payload
        IsResidueE(e) => write_record("IsResidueE", &[FieldRepr::Node(e)], out), // field: expr
        GetResidue(e) => write_record("GetResidue", &[FieldRepr::Node(e)], out), // field: expr

        // --- List ---
        // Rust `EmptyList` is Python class `EmptyListE` (TYPE-NAME crux).
        EmptyList => write_record("EmptyListE", &[], out),
        ListSingleton(e) => write_record("ListSingleton", &[FieldRepr::Node(e)], out), // field: elem
        ListAppend(l, r) => bin("ListAppend", l, r, out),                              // left, right
        ListLen(l) => write_record("ListLen", &[FieldRepr::Node(l)], out),
        ListFirst(l) => write_record("ListFirst", &[FieldRepr::Node(l)], out),
        ListLast(l) => write_record("ListLast", &[FieldRepr::Node(l)], out),
        // Python ListDrop(list_, n) / ListTake(list_, n)
        ListDrop(l, n) => write_record(
            "ListDrop",
            &[FieldRepr::Node(l), FieldRepr::Node(n)],
            out,
        ),
        ListTake(l, n) => write_record(
            "ListTake",
            &[FieldRepr::Node(l), FieldRepr::Node(n)],
            out,
        ),
        // Python ListWindow(list_, k: int)
        ListWindow(l, k) => write_record(
            "ListWindow",
            &[FieldRepr::Node(l), FieldRepr::Leaf(leaf_int(*k as i64))],
            out,
        ),
        ListIndexed(l) => write_record("ListIndexed", &[FieldRepr::Node(l)], out),

        // --- BoundedFold(list_, init, acc_var, item_var, body) ---
        BoundedFold {
            list,
            init,
            acc_var,
            item_var,
            body,
        } => write_record(
            "BoundedFold",
            &[
                FieldRepr::Node(list),
                FieldRepr::Node(init),
                FieldRepr::Leaf(leaf_str(acc_var)),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(body),
            ],
            out,
        ),

        // --- GroupBy(list_, itemVar, keyBody) ---
        GroupBy {
            list,
            item_var,
            key_body,
        } => write_record(
            "GroupBy",
            &[
                FieldRepr::Node(list),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(key_body),
            ],
            out,
        ),
        // --- OrderBy(list_, itemVar, keyBody, descending: bool) ---
        OrderBy {
            list,
            item_var,
            key_body,
            descending,
        } => write_record(
            "OrderBy",
            &[
                FieldRepr::Node(list),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(key_body),
                FieldRepr::Leaf(leaf_bool(*descending)),
            ],
            out,
        ),
        // --- FindFirst(list_, idx_var, item_var, pred, map_) ---
        FindFirst {
            list,
            idx_var,
            item_var,
            pred,
            map_,
        } => write_record(
            "FindFirst",
            &[
                FieldRepr::Node(list),
                FieldRepr::Leaf(leaf_str(idx_var)),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(pred),
                FieldRepr::Node(map_),
            ],
            out,
        ),
        // --- AlwaysUntil(list_, from_t, item_var, pred, stop) ---
        AlwaysUntil {
            list,
            from_t,
            item_var,
            pred,
            stop,
        } => write_record(
            "AlwaysUntil",
            &[
                FieldRepr::Node(list),
                FieldRepr::Node(from_t),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(pred),
                FieldRepr::Node(stop),
            ],
            out,
        ),
        // --- EventuallyAfter(list_, from_t, item_var, pred) ---
        EventuallyAfter {
            list,
            from_t,
            item_var,
            pred,
        } => write_record(
            "EventuallyAfter",
            &[
                FieldRepr::Node(list),
                FieldRepr::Node(from_t),
                FieldRepr::Leaf(leaf_str(item_var)),
                FieldRepr::Node(pred),
            ],
            out,
        ),
        // --- BoundedFix(state0, step_var, step_body, stop_pred, fuel: int) ---
        BoundedFix {
            state0,
            step_var,
            step_body,
            stop_pred,
            fuel,
        } => write_record(
            "BoundedFix",
            &[
                FieldRepr::Node(state0),
                FieldRepr::Leaf(leaf_str(step_var)),
                FieldRepr::Node(step_body),
                FieldRepr::Node(stop_pred),
                FieldRepr::Leaf(leaf_int(*fuel as i64)),
            ],
            out,
        ),

        // --- R1 operators ---
        Glue(s) => write_record("Glue", &[FieldRepr::Node(s)], out), // field: sections
        // Python DischargeProp(residues, edges)
        DischargeProp(res, edges) => write_record(
            "DischargeProp",
            &[FieldRepr::Node(res), FieldRepr::Node(edges)],
            out,
        ),
        UseCountCheck(u) => write_record("UseCountCheck", &[FieldRepr::Node(u)], out), // field: usages

        // --- Call(fn_name: str, args: tuple[Expr, …]) ---
        Call(name, args) => {
            let arg_reprs: Vec<FieldRepr> = args.iter().map(FieldRepr::Node).collect();
            write_record(
                "Call",
                &[FieldRepr::Leaf(leaf_str(name)), FieldRepr::Tuple(arg_reprs)],
                out,
            )
        }

        // --- MatchTag(scrut, universe: tuple[int,…], branches: tuple[(int,Expr),…], default) ---
        MatchTag {
            scrut,
            universe,
            branches,
            default,
        } => {
            let univ: Vec<FieldRepr> = universe
                .iter()
                .map(|u| FieldRepr::Leaf(leaf_int(*u)))
                .collect();
            let brs: Vec<FieldRepr> = branches
                .iter()
                .map(|(code, body)| {
                    FieldRepr::Tuple(vec![FieldRepr::Leaf(leaf_int(*code)), FieldRepr::Node(body)])
                })
                .collect();
            write_record(
                "MatchTag",
                &[
                    FieldRepr::Node(scrut),
                    FieldRepr::Tuple(univ),
                    FieldRepr::Tuple(brs),
                    FieldRepr::Node(default),
                ],
                out,
            )
        }

        // --- Extension-layer string ops (WU-3 60/60, ADR §9.8).
        //     Field order mirrors the Lean ctor (single string leaf for
        //     StrLit; nested expr for the rest). Mirrors slot_ast.py once
        //     these grow there.
        StrLit(s) => write_record("StrLit", &[FieldRepr::Leaf(leaf_str(s))], out),
        StrConcat(a, b) => bin("StrConcat", a, b, out),
        StrLen(a) => un("StrLen", a, out),
        StrEq(a, b) => bin("StrEq", a, b, out),
        IntToStr(a) => un("IntToStr", a, out),
        ContentHash(a) => un("ContentHash", a, out),
        StrCharAt(s, i) => bin("StrCharAt", s, i, out),
        StrCodeAt(s, i) => bin("StrCodeAt", s, i, out),
        StrSubstring(s, i, j) => write_record(
            "StrSubstring",
            &[FieldRepr::Node(s), FieldRepr::Node(i), FieldRepr::Node(j)],
            out,
        ),
        StrToInt(a) => un("StrToInt", a, out),
        StrSplit(s, d) => bin("StrSplit", s, d, out),
    }
}

/// Binary node with Python fields `left, right`.
fn bin(tag: &str, l: &Expr, r: &Expr, out: &mut String) {
    write_record(tag, &[FieldRepr::Node(l), FieldRepr::Node(r)], out);
}

/// Unary node with Python field `expr`.
fn un(tag: &str, e: &Expr, out: &mut String) {
    write_record(tag, &[FieldRepr::Node(e)], out);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Expr::*;

    fn num(n: i64) -> Box<Expr> {
        Box::new(Num(n))
    }

    #[test]
    fn canonical_repr_per_leaf_kind() {
        assert_eq!(canonical_repr(&NumF("6.917529027641082e+18".into())),
                   "Num(float:6.917529027641082e+18)");
        assert_eq!(canonical_repr(&NumF("2.5".into())), "Num(float:2.5)");
        assert_eq!(canonical_repr(&NumF("-0.0".into())), "Num(float:-0.0)");
        assert_eq!(canonical_repr(&Num(7)), "Num(float:7.0)");
        assert_eq!(canonical_repr(&Num(-3)), "Num(float:-3.0)");
        assert_eq!(canonical_repr(&Num(0)), "Num(float:0.0)");
        assert_eq!(canonical_repr(&BoolLit(true)), "BoolLit(bool:True)");
        assert_eq!(canonical_repr(&BoolLit(false)), "BoolLit(bool:False)");
        assert_eq!(canonical_repr(&Var("x".into())), "Var(str:1:x)");
        assert_eq!(canonical_repr(&Var("acc".into())), "Var(str:3:acc)");
        assert_eq!(canonical_repr(&Var("".into())), "Var(str:0:)");
        assert_eq!(canonical_repr(&NoneLit), "NoneLit()");
        assert_eq!(canonical_repr(&EmptyList), "EmptyListE()");
    }

    #[test]
    fn canonical_repr_per_node_kind() {
        assert_eq!(
            canonical_repr(&Add(num(2), num(3))),
            "Add(Num(float:2.0),Num(float:3.0))"
        );
        assert_eq!(
            canonical_repr(&ListWindow(Box::new(EmptyList), 3)),
            "ListWindow(EmptyListE(),int:3)"
        );
        assert_eq!(
            canonical_repr(&MakeRecord(vec![
                ("a".into(), Num(1)),
                ("b".into(), BoolLit(true)),
            ])),
            "MakeRecord([[str:1:a,Num(float:1.0)],[str:1:b,BoolLit(bool:True)]])"
        );
        assert_eq!(
            canonical_repr(&Call("add2".into(), vec![Num(3), Num(4)])),
            "Call(str:4:add2,[Num(float:3.0),Num(float:4.0)])"
        );
        assert_eq!(
            canonical_repr(&MatchTag {
                scrut: num(1),
                universe: vec![1, 2],
                branches: vec![(1, Num(9)), (2, Num(8))],
                default: Box::new(NoneLit),
            }),
            "MatchTag(Num(float:1.0),[int:1,int:2],[[int:1,Num(float:9.0)],[int:2,Num(float:8.0)]],NoneLit())"
        );
        assert_eq!(
            canonical_repr(&BoundedFix {
                state0: num(0),
                step_var: "s".into(),
                step_body: num(1),
                stop_pred: Box::new(BoolLit(true)),
                fuel: 5,
            }),
            "BoundedFix(Num(float:0.0),str:1:s,Num(float:1.0),BoolLit(bool:True),int:5)"
        );
        assert_eq!(
            canonical_repr(&OrderBy {
                list: Box::new(EmptyList),
                item_var: "it".into(),
                key_body: num(1),
                descending: true,
            }),
            "OrderBy(EmptyListE(),str:2:it,Num(float:1.0),bool:True)"
        );
    }

    // Golden (expr → hex q) vectors copied from running the Python authority
    // (`PYTHONPATH=src python3 -c 'from residua.grow.content_store import
    // content_hash; ...'`) — pins the Rust content_hash to the Python's exact
    // bytes end-to-end, independent of the conformance harness.
    #[test]
    fn golden_content_hash_vectors() {
        assert_eq!(
            content_hash(&Num(7)),
            "fb80b1ff7cb5aff3229def061f1d4b0d673220f00f9f0213c2cede449ceb796d"
        );
        assert_eq!(
            content_hash(&Add(num(2), num(3))),
            "499a0f36a86f3990f6627b2a889c9fc9cac977e094b2527d3b5e5b77767024b8"
        );
        assert_eq!(
            content_hash(&Var("x".into())),
            "95b8ed145218e6a2ad3b45d24e68b24904d335f71f3a15cdb47a83c6a006b257"
        );
        assert_eq!(
            content_hash(&MakeRecord(vec![("a".into(), Num(1))])),
            "abac9db490cf1eb9c54e4d6c08cf1f81d5a2e8ad160cfb908c47d634f853baca"
        );
        assert_eq!(
            content_hash(&NoneLit),
            "320c169731c4c7ab445ce6dce346c2228a609644f8d52d63b17663760510de76"
        );
        assert_eq!(
            content_hash(&EmptyList),
            "b74c109c33a9085a6557c09d342786f6a4f8a4c088a7ad6f3533de1c489ad5fc"
        );
    }

    // ------------------------------------------------------------------
    // pyval (value-domain) vectors — expected qs are the Python authority's
    // `content_store.content_hash` over the same Python value. Pins the
    // substrate's value-domain canonical form byte-for-byte.
    // ------------------------------------------------------------------
    fn pyval(s: &str) -> json::Json {
        json::parse(s).unwrap()
    }

    fn pyval_q(s: &str) -> String {
        content_hash_pyval(&json::parse(s).unwrap()).unwrap()
    }

    #[test]
    fn pyval_canonical_bytes() {
        assert_eq!(
            canonical_pyval(&pyval(r#"{"t":"str","s":"codeV2"}"#)).unwrap(),
            "str:6:codeV2"
        );
        assert_eq!(
            canonical_pyval(&pyval(r#"{"t":"int","s":"-7"}"#)).unwrap(),
            "int:-7"
        );
        assert_eq!(
            canonical_pyval(&pyval(r#"{"t":"bool","b":true}"#)).unwrap(),
            "bool:True"
        );
        assert_eq!(canonical_pyval(&pyval(r#"{"t":"none"}"#)).unwrap(), "none");
        assert_eq!(
            canonical_pyval(&pyval(
                r#"{"t":"tuple","xs":[{"t":"str","s":"outer"},{"t":"tuple","xs":[{"t":"str","s":"inner"},{"t":"int","s":"3"}]}]}"#
            ))
            .unwrap(),
            "[str:5:outer,[str:5:inner,int:3]]"
        );
        // str length is codepoint count, not UTF-8 bytes.
        assert_eq!(
            canonical_pyval(&pyval(r#"{"t":"str","s":"unié\n\"q\" \\"}"#)).unwrap(),
            "str:10:unié\n\"q\" \\"
        );
        assert_eq!(canonical_pyval(&pyval(r#"{"t":"tuple","xs":[]}"#)).unwrap(), "[]");
        assert_eq!(canonical_pyval(&pyval(r#"{"t":"str","s":""}"#)).unwrap(), "str:0:");
    }

    #[test]
    fn pyval_golden_qs() {
        // (wire pyval, Python content_hash(<the same Python value>)).
        let cases: &[(&str, &str)] = &[
            (r#"{"t":"str","s":"codeV2"}"#, "e40c456295ece598e9c5cf3fe90a638aa3864ee359ec82a9a19d7829c2a3a29f"),
            (r#"{"t":"tuple","xs":[{"t":"str","s":"codeV2"}]}"#, "4faf9012a76c62f4d3a7e3551fceed08d52d7093ebf7f24169321c4625ca0673"),
            (r#"{"t":"tuple","xs":[{"t":"str","s":"type:TEq"},{"t":"str","s":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"},{"t":"str","s":"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"},{"t":"str","s":"cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"}]}"#, "b4a69c3cc9d237ea68079d11a5a82da90d3261ac4b00076363054061a9d90126"),
            (r#"{"t":"str","s":"unié\n\"q\" \\"}"#, "61bf99e6bd59cdf70a445f207b485a9e70be6c225a067ae557b76f42400ef154"),
            (r#"{"t":"int","s":"-7"}"#, "3972ddcf37baecee993a6ede1aebc61b75041285917c209e2668e4b0f018ba44"),
            (r#"{"t":"int","s":"9223372036854775807"}"#, "9ec754886be1b7bd5e9dc5604bc9ceb33962b98f0b6c63f1caaf740b1c6f8b41"),
            (r#"{"t":"int","s":"-9223372036854775808"}"#, "5200d7b350f092a9f0f17f08b7f2607bffdeae70ce4b87289e4c38e55d129e5c"),
            (r#"{"t":"int","s":"9223372036854775808"}"#, "f0dba082d3ac7f77a6e357709b06f8565fdab08b444050f05fa99e5fa9bad5f0"),
            (r#"{"t":"int","s":"-9223372036854775809"}"#, "b65aa6b5a6976ad3e9b6618a5c0a294e4c9972260f75665142f8d851dde48388"),
            (r#"{"t":"int","s":"123456789012345678901234567890"}"#, "830860c990cf986199fea9a4f5275b1feeaa36304028696b7ab322583736ab93"),
            (r#"{"t":"bool","b":true}"#, "cbc78c2f695cf0a5b3b61d178907a93eceb1a56c58be85283f8ae795e39b4c39"),
            (r#"{"t":"bool","b":false}"#, "96a2745e168e8650026358b4a792a3d061e2bd24c62f0d73d8e290597704088b"),
            (r#"{"t":"none"}"#, "140bedbf9c3f6d56a9846d2ba7088798683f4da0c248231336e6a05679e4fdfe"),
            (r#"{"t":"tuple","xs":[{"t":"str","s":"outer"},{"t":"tuple","xs":[{"t":"str","s":"inner"},{"t":"int","s":"3"}]}]}"#, "74ccb011d7063133b54862d151a84da1b03e624ba42c37ae84ced7460a31e08d"),
            (r#"{"t":"tuple","xs":[]}"#, "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"),
            (r#"{"t":"str","s":""}"#, "8c3bbe56475591ff92c224fd6e3b24cdb01d0d7e84b19d7fb5bc92d9bce75314"),
        ];
        for (wire, expected) in cases {
            assert_eq!(&pyval_q(wire), expected, "wire: {}", wire);
        }
    }

    #[test]
    fn pyval_refuses_bad_shapes() {
        for bad in [
            r#"{"t":"int","s":"007"}"#,
            r#"{"t":"int","s":"-0"}"#,
            r#"{"t":"int","s":"-"}"#,
            r#"{"t":"int","s":""}"#,
            r#"{"t":"int","s":"1.5"}"#,
            r#"{"t":"int","s":"+7"}"#,
            r#"{"t":"int","s":" 7"}"#,
            r#"{"t":"int","s":"1e3"}"#,
            r#"{"t":"int"}"#,
            r#"{"t":"str"}"#,
            r#"{"t":"bool","b":1}"#,
            r#"{"t":"tuple","xs":{}}"#,
            r#"{"t":"float","f":1}"#,
            r#"{"t":"bogus"}"#,
            r#"{"s":"no-t"}"#,
            r#"{"t":"none","extra":1,"and":{"nested":2}}"#, // extra keys refused
        ] {
            assert!(
                canonical_pyval(&json::parse(bad).unwrap()).is_err(),
                "should refuse: {}",
                bad
            );
        }
    }
}
