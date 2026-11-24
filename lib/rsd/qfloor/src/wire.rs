//! The JSON WIRE codec — the byte-shape contract with the differential harness.
//!
//! Decoder: mirrors `_decode_expr` in
//!   tools/mstnf_runtime/slot_eval_exe_conformance.py  (the op-tag + field names)
//! and `_wire_env` (env values are wire-Vals via `_value_verdict`).
//!
//! Encoder: mirrors `_wire_val` / `_expected_output` in the SAME file. The exe
//! output envelope is `{"ok": true, "val": <Val>|null}`; `val: null` is the
//! typed residue (`none`). A decode error is the DISTINCT `{"ok": false,
//! "err": "<msg>"}` envelope.
//!
//! These field names are PINNED by the harness (`_WIRE_SCHEMA`) and the Lean
//! `SlotEval` codec. A drift here is exactly what the fuzzer's `--binary`
//! path catches against `interp.eval_`-wire — faithfulness is SEALED there.

use crate::ast::{Expr, Val};
use crate::json::{self, Json};

// ===========================================================================
// Expr decode  (wire-JSON Expr  →  Expr)  — inverse of _decode_expr.
// ===========================================================================

/// MAX_DEPTH — the wire→AST decoder's recursion bound, the SAME constant as
/// the JSON parser's (`json::MAX_DEPTH`, one named constant so the two bounds
/// cannot drift). `decode_expr` recurses once per Expr nesting level; deeper
/// wire input gets the NAMED `[evalr_decode_depth_exceeded]` error envelope
/// instead of a native stack overflow. Defense in depth: every payload that
/// arrives through `run_str` is already bounded by the parser, but the decoder
/// is `pub` (tests / FFI may hand it a constructed `Json`), so it enforces the
/// bound itself rather than trusting its caller.
pub const MAX_DEPTH: usize = json::MAX_DEPTH;

pub fn decode_expr(j: &Json) -> Result<Expr, String> {
    decode_expr_at(j, 0)
}

fn decode_expr_at(j: &Json, depth: usize) -> Result<Expr, String> {
    if depth > MAX_DEPTH {
        return Err(format!(
            "[evalr_decode_depth_exceeded] wire Expr nesting deeper than MAX_DEPTH={}",
            MAX_DEPTH
        ));
    }
    let op = j
        .get("op")
        .and_then(Json::as_str)
        .ok_or("expr missing string 'op'")?;

    // helpers (each child decodes at depth + 1 — the bound above is the gate)
    let sub = |key: &str| -> Result<Box<Expr>, String> {
        let v = j.get(key).ok_or_else(|| format!("op {:?} missing field {:?}", op, key))?;
        Ok(Box::new(decode_expr_at(v, depth + 1)?))
    };
    let s = |key: &str| -> Result<String, String> {
        j.get(key)
            .and_then(Json::as_str)
            .map(|x| x.to_string())
            .ok_or_else(|| format!("op {:?} missing string field {:?}", op, key))
    };

    let bin = |l: &str, r: &str| -> Result<(Box<Expr>, Box<Expr>), String> {
        Ok((
            Box::new(decode_expr_at(
                j.get(l).ok_or_else(|| format!("op {:?} missing {:?}", op, l))?,
                depth + 1,
            )?),
            Box::new(decode_expr_at(
                j.get(r).ok_or_else(|| format!("op {:?} missing {:?}", op, r))?,
                depth + 1,
            )?),
        ))
    };

    let e = match op {
        // literals
        "num" => {
            let n = j.get("n").ok_or("num.n missing")?;
            if let Some(i) = n.as_int() {
                Expr::Num(i)
            } else if let Some(s) = n.as_str() {
                // frozen-substrate-repair: [wire_num_float_repr_aliases_int]
                // Refuse only the EXACT alias class: `s` is the canonical
                // "<n>.0" rendering of an integer n within +-2^53 — the only
                // strings whose NumF shares q with Num(n) while reflect
                // distinguishes them. Checked FIRST inside the now-larger
                // refused class below — it keeps its more specific diagnostic.
                if let Some(t) = s.strip_suffix(".0") {
                    let digits = t.strip_prefix('-').unwrap_or(t);
                    let canonical = !digits.is_empty()
                        && (digits == "0" || !digits.starts_with('0'))
                        && t != "-0"
                        && digits.bytes().all(|b| b.is_ascii_digit());
                    let in_range = t
                        .parse::<i64>()
                        .map(|n| n.unsigned_abs() <= (1u64 << 53) && n.to_string() == t)
                        .unwrap_or(false);
                    if canonical && in_range {
                        return Err(format!(
                            "[wire_num_float_repr_aliases_int] num.n {:?} is an integral float repr; send it as a JSON integer",
                            s
                        ));
                    }
                }
                // frozen-substrate-repair: [wire_num_string_n]
                // ANY other string `n` is refused at decode — float repr or
                // not. The core is exact-int: a string n is never a legal wire
                // Num (send it as a JSON integer). `Expr::NumF` stays in the
                // AST and in content_hash canonicalisation for the q identity
                // of old bytes, but is now unreachable from the wire.
                return Err(format!(
                    "[wire_num_string_n] num.n {:?} is a string; send n as a JSON integer (exact-int core)",
                    s
                ));
            } else {
                return Err("num.n not an int or float repr (integer-core)".to_string());
            }
        }
        "boollit" => Expr::BoolLit(j.get("b").and_then(Json::as_bool).ok_or("boollit.b not bool")?),
        "var" => Expr::Var(s("x")?),

        // arithmetic / comparison / boolean — fields "a","b".
        "add" => { let (a, b) = bin("a", "b")?; Expr::Add(a, b) }
        "sub" => { let (a, b) = bin("a", "b")?; Expr::Sub(a, b) }
        "mul" => { let (a, b) = bin("a", "b")?; Expr::Mul(a, b) }
        "div" => { let (a, b) = bin("a", "b")?; Expr::Div(a, b) }
        "mod" => { let (a, b) = bin("a", "b")?; Expr::Mod(a, b) }
        "minE" => { let (a, b) = bin("a", "b")?; Expr::MinE(a, b) }
        "maxE" => { let (a, b) = bin("a", "b")?; Expr::MaxE(a, b) }
        "lt" => { let (a, b) = bin("a", "b")?; Expr::Lt(a, b) }
        "lte" => { let (a, b) = bin("a", "b")?; Expr::Lte(a, b) }
        "gt" => { let (a, b) = bin("a", "b")?; Expr::Gt(a, b) }
        "gte" => { let (a, b) = bin("a", "b")?; Expr::Gte(a, b) }
        "eqE" => { let (a, b) = bin("a", "b")?; Expr::EqE(a, b) }
        "andE" => { let (a, b) = bin("a", "b")?; Expr::AndE(a, b) }
        "orE" => { let (a, b) = bin("a", "b")?; Expr::OrE(a, b) }
        "neg" => Expr::Neg(sub("a")?),
        "absE" => Expr::AbsE(sub("a")?),
        "notE" => Expr::NotE(sub("a")?),

        // conditional / let
        "ifE" => Expr::IfE(sub("c")?, sub("t")?, sub("e")?),
        "letE" => Expr::Let(s("x")?, sub("e")?, sub("b")?),

        // list fragment
        "emptyList" => Expr::EmptyList,
        "listSingleton" => Expr::ListSingleton(sub("e")?),
        "listAppend" => { let (l, r) = bin("l", "r")?; Expr::ListAppend(l, r) }
        "listLen" => Expr::ListLen(sub("l")?),
        "listFirst" => Expr::ListFirst(sub("l")?),
        "listLast" => Expr::ListLast(sub("l")?),
        "listDrop" => { let (l, n) = bin("l", "n")?; Expr::ListDrop(l, n) }
        "listTake" => { let (l, n) = bin("l", "n")?; Expr::ListTake(l, n) }
        "listWindow" => {
            let k = j
                .get("k")
                .and_then(Json::as_int)
                .ok_or("listWindow.k not an int")?;
            if k < 0 {
                return Err("listWindow.k must be a Nat".to_string());
            }
            Expr::ListWindow(sub("l")?, k as usize)
        }
        "listIndexed" => Expr::ListIndexed(sub("l")?),

        // Option fragment
        "noneLit" => Expr::NoneLit,
        "someE" => Expr::SomeE(sub("e")?),
        "isNoneE" => Expr::IsNoneE(sub("e")?),
        "isSomeE" => Expr::IsSomeE(sub("e")?),
        "unwrapSome" => Expr::UnwrapSome(sub("e")?),

        // Result fragment
        "okE" => Expr::OkE(sub("e")?),
        "errE" => Expr::ErrE(sub("e")?),
        "isOkE" => Expr::IsOkE(sub("e")?),
        "getOk" => Expr::GetOk(sub("e")?),

        // Residue ρ
        "residueE" => Expr::ResidueE(sub("e")?),
        "isResidueE" => Expr::IsResidueE(sub("e")?),
        "getResidue" => Expr::GetResidue(sub("e")?),

        // record fragment
        "makeRecord" => {
            let flds = j
                .get("flds")
                .and_then(Json::as_arr)
                .ok_or("makeRecord.flds not an array")?;
            let mut fields = Vec::with_capacity(flds.len());
            for pair in flds {
                let arr = pair.as_arr().ok_or("makeRecord field not a [name, expr] pair")?;
                if arr.len() != 2 {
                    return Err("makeRecord field pair must have length 2".to_string());
                }
                let name = arr[0].as_str().ok_or("makeRecord field name not a string")?;
                let ve = decode_expr_at(&arr[1], depth + 1)?;
                fields.push((name.to_string(), ve));
            }
            Expr::MakeRecord(fields)
        }
        "fieldAccess" => Expr::FieldAccess(sub("r")?, s("f")?),

        // bounded fold — fields lst/init/av/iv/body.
        "boundedFold" => Expr::BoundedFold {
            list: Box::new(decode_expr_at(j.get("lst").ok_or("boundedFold missing lst")?, depth + 1)?),
            init: Box::new(decode_expr_at(j.get("init").ok_or("boundedFold missing init")?, depth + 1)?),
            acc_var: s("av")?,
            item_var: s("iv")?,
            body: Box::new(decode_expr_at(j.get("body").ok_or("boundedFold missing body")?, depth + 1)?),
        },

        // --- E1.12 GroupBy — fields list/itemVar/keyBody (_wire_expr). ---
        "groupBy" => Expr::GroupBy {
            list: Box::new(decode_expr_at(j.get("list").ok_or("groupBy missing list")?, depth + 1)?),
            item_var: s("itemVar")?,
            key_body: Box::new(decode_expr_at(j.get("keyBody").ok_or("groupBy missing keyBody")?, depth + 1)?),
        },
        // --- E1.13 OrderBy — fields list/itemVar/keyBody/descending. ---
        "orderBy" => Expr::OrderBy {
            list: Box::new(decode_expr_at(j.get("list").ok_or("orderBy missing list")?, depth + 1)?),
            item_var: s("itemVar")?,
            key_body: Box::new(decode_expr_at(j.get("keyBody").ok_or("orderBy missing keyBody")?, depth + 1)?),
            descending: j
                .get("descending")
                .and_then(Json::as_bool)
                .ok_or("orderBy.descending not bool")?,
        },
        // --- E1.8 FindFirst — fields lst/iv(idx)/it(item)/pred/mp(map). ---
        "findFirst" => Expr::FindFirst {
            list: Box::new(decode_expr_at(j.get("lst").ok_or("findFirst missing lst")?, depth + 1)?),
            idx_var: s("iv")?,
            item_var: s("it")?,
            pred: Box::new(decode_expr_at(j.get("pred").ok_or("findFirst missing pred")?, depth + 1)?),
            map_: Box::new(decode_expr_at(j.get("mp").ok_or("findFirst missing mp")?, depth + 1)?),
        },
        // --- E1.8 AlwaysUntil — fields lst/ft/it/pred/stop. ---
        "alwaysUntil" => Expr::AlwaysUntil {
            list: Box::new(decode_expr_at(j.get("lst").ok_or("alwaysUntil missing lst")?, depth + 1)?),
            from_t: Box::new(decode_expr_at(j.get("ft").ok_or("alwaysUntil missing ft")?, depth + 1)?),
            item_var: s("it")?,
            pred: Box::new(decode_expr_at(j.get("pred").ok_or("alwaysUntil missing pred")?, depth + 1)?),
            stop: Box::new(decode_expr_at(j.get("stop").ok_or("alwaysUntil missing stop")?, depth + 1)?),
        },
        // --- E1.8 EventuallyAfter — fields lst/ft/it/pred. ---
        "eventuallyAfter" => Expr::EventuallyAfter {
            list: Box::new(decode_expr_at(j.get("lst").ok_or("eventuallyAfter missing lst")?, depth + 1)?),
            from_t: Box::new(decode_expr_at(j.get("ft").ok_or("eventuallyAfter missing ft")?, depth + 1)?),
            item_var: s("it")?,
            pred: Box::new(decode_expr_at(j.get("pred").ok_or("eventuallyAfter missing pred")?, depth + 1)?),
        },
        // --- E1.10 BoundedFix — fields state0/stepVar/stepBody/stopPred/fuel. ---
        "boundedFix" => {
            let bf_fuel = j
                .get("fuel")
                .and_then(Json::as_int)
                .ok_or("boundedFix.fuel not an int")?;
            if bf_fuel < 0 {
                return Err("boundedFix.fuel must be a Nat".to_string());
            }
            Expr::BoundedFix {
                state0: Box::new(decode_expr_at(j.get("state0").ok_or("boundedFix missing state0")?, depth + 1)?),
                step_var: s("stepVar")?,
                step_body: Box::new(
                    decode_expr_at(j.get("stepBody").ok_or("boundedFix missing stepBody")?, depth + 1)?,
                ),
                stop_pred: Box::new(
                    decode_expr_at(j.get("stopPred").ok_or("boundedFix missing stopPred")?, depth + 1)?,
                ),
                fuel: bf_fuel as u64,
            }
        }
        // --- E1.16 Glue — field sections. ---
        "glue" => Expr::Glue(sub("sections")?),
        // --- E1.17 DischargeProp — fields residues/edges. ---
        "dischargeProp" => {
            let (res, edg) = bin("residues", "edges")?;
            Expr::DischargeProp(res, edg)
        }
        // --- E1.18 UseCountCheck — field usages. ---
        "useCountCheck" => Expr::UseCountCheck(sub("usages")?),
        // --- E1.9 Call — fields name/args. (programs table arrives separately
        //     via run_payload's "programs" key, not on the Expr node.) ---
        "call" => {
            let args_j = j
                .get("args")
                .and_then(Json::as_arr)
                .ok_or("call.args not an array")?;
            let mut args = Vec::with_capacity(args_j.len());
            for a in args_j {
                args.push(decode_expr_at(a, depth + 1)?);
            }
            Expr::Call(s("name")?, args)
        }

        // --- E1.19 MatchTag — fields scrut/universe/branches/default.
        //     universe = flat int array; branches = array of [code, body]
        //     pairs. Mirrors _wire_expr/_decode_expr in
        //     slot_eval_exe_conformance.py (cc's exprToJson, 93296f6). ---
        "matchTag" => {
            let univ_j = j
                .get("universe")
                .and_then(Json::as_arr)
                .ok_or("matchTag.universe not an array")?;
            let mut universe = Vec::with_capacity(univ_j.len());
            for u in univ_j {
                universe.push(u.as_int().ok_or("matchTag.universe element not an int")?);
            }
            let branches_j = j
                .get("branches")
                .and_then(Json::as_arr)
                .ok_or("matchTag.branches not an array")?;
            let mut branches = Vec::with_capacity(branches_j.len());
            for pair in branches_j {
                let arr = pair
                    .as_arr()
                    .ok_or("matchTag branch not a [code, body] pair")?;
                if arr.len() != 2 {
                    return Err("matchTag branch pair must have length 2".to_string());
                }
                let code = arr[0].as_int().ok_or("matchTag branch code not an int")?;
                branches.push((code, decode_expr_at(&arr[1], depth + 1)?));
            }
            Expr::MatchTag {
                scrut: sub("scrut")?,
                universe,
                branches,
                default: sub("default")?,
            }
        }

        // --- Extension-layer string ops (WU-3 60/60, ADR §9.8).
        //     Field "s" carries the literal; binary ops use "a"/"b"; unary uses "a".
        //     closes [per_platform_interp_strops_MISSING].
        "strLit" => Expr::StrLit(s("s")?),
        "strConcat" => { let (a, b) = bin("a", "b")?; Expr::StrConcat(a, b) }
        "strLen" => Expr::StrLen(sub("a")?),
        "strEq" => { let (a, b) = bin("a", "b")?; Expr::StrEq(a, b) }
        "intToStr" => Expr::IntToStr(sub("a")?),
        "contentHash" => Expr::ContentHash(sub("a")?),
        "reflect" => Expr::Reflect(sub("e")?),
        "reifyExpr" => Expr::ReifyExpr(sub("e")?),
        // slice 0 parse-supporting ops — closes
        // [extension_strops_insufficient_for_parse]. Index unit is Unicode
        // CODE POINT (pinned in residues/catalog.json); the eval arms below
        // use s.chars().nth(i) / s.chars().skip(i).take(j-i), NOT byte indexing.
        "strCharAt" => { let (a, b) = bin("a", "b")?; Expr::StrCharAt(a, b) }
        // strCodeAt: the Unicode code point (Int) of the char at code-point
        // index i — same "a"/"b" binary shape + same code-point index unit as
        // strCharAt; OOB → None residue (ADR_CODEPOINT_PRIMITIVE).
        "strCodeAt" => { let (a, b) = bin("a", "b")?; Expr::StrCodeAt(a, b) }
        "strSubstring" => {
            let a = sub("a")?;
            let b = sub("b")?;
            let c = sub("c")?;
            Expr::StrSubstring(a, b, c)
        }
        // Capability A parse pair (unary "a"; binary "a"/"b" — the D2b convention).
        "strToInt" => Expr::StrToInt(sub("a")?),
        "strSplit" => { let (a, b) = bin("a", "b")?; Expr::StrSplit(a, b) }

        // The full 60-ctor set has explicit decode arms above. A genuinely
        // unrecognised / malformed op string decode-fails LOUD (the distinct
        // `ok:false` envelope) rather than silently mis-evaluating.
        other => {
            return Err(format!(
                "evalR: unrecognised op {:?} (not a slot AST constructor)",
                other
            ))
        }
    };
    Ok(e)
}

// ===========================================================================
// Val encode  (Val  →  wire-JSON Val)  — mirror of _wire_val.
// ===========================================================================

pub fn encode_val(v: &Val) -> Json {
    match v {
        Val::Int(n) => json::obj(vec![("tag", Json::Str("int".into())), ("n", Json::Int(*n))]),
        Val::Bool(b) => json::obj(vec![("tag", Json::Str("bool".into())), ("b", Json::Bool(*b))]),
        Val::List(xs) => json::obj(vec![
            ("tag", Json::Str("list".into())),
            ("xs", Json::Arr(xs.iter().map(encode_val).collect())),
        ]),
        // opt: {"tag":"opt","v": null|<Val>}  (none = null, some = inner Val)
        Val::Opt(None) => json::obj(vec![("tag", Json::Str("opt".into())), ("v", Json::Null)]),
        Val::Opt(Some(inner)) => json::obj(vec![
            ("tag", Json::Str("opt".into())),
            ("v", encode_val(inner)),
        ]),
        // record: {"tag":"record","kvs":[[k,<Val>],…]}
        Val::Record(kvs) => json::obj(vec![
            ("tag", Json::Str("record".into())),
            (
                "kvs",
                Json::Arr(
                    kvs.iter()
                        .map(|(k, vv)| Json::Arr(vec![Json::Str(k.clone()), encode_val(vv)]))
                        .collect(),
                ),
            ),
        ]),
        Val::Ok(inner) => {
            json::obj(vec![("tag", Json::Str("ok".into())), ("v", encode_val(inner))])
        }
        Val::Err(inner) => {
            json::obj(vec![("tag", Json::Str("err".into())), ("v", encode_val(inner))])
        }
        Val::Residue(inner) => json::obj(vec![
            ("tag", Json::Str("residue".into())),
            ("v", encode_val(inner)),
        ]),
        // Extension-layer string value (WU-3 60/60, ADR §9.8).
        Val::Str(s) => json::obj(vec![
            ("tag", Json::Str("str".into())),
            ("s", Json::Str(s.s.clone())),
        ]),
    }
}

/// The exe output envelope for a successful evaluation. `None` = typed residue
/// (`val: null`), mirroring `_expected_output`.
pub fn output_envelope(result: Option<&Val>) -> Json {
    let val = match result {
        Some(v) => encode_val(v),
        None => Json::Null,
    };
    json::obj(vec![("ok", Json::Bool(true)), ("val", val)])
}

/// The decode-error envelope — DISTINCT from a typed residue. `{"ok": false,
/// "err": "<msg>"}` (mirrors the harness doc: `ok:false` is a decode error,
/// `val:null` is `evalL`'s `none`). The fuzzer's well-typed inputs never hit
/// this; it exists so a malformed wire is reported, not silently turned into
/// a residue (§12).
pub fn error_envelope(msg: &str) -> Json {
    json::obj(vec![
        ("ok", Json::Bool(false)),
        ("err", Json::Str(msg.to_string())),
    ])
}

// ===========================================================================
// Env decode  (wire-JSON env  →  Env)  — mirror of _wire_env / valFromJson.
// Env wire shape: [[name, <valJson>], …]  (value via the Val codec).
// ===========================================================================

// frozen-substrate-repair: [effect_wire_malformed]
/// Engine-neutral wire-error repr — the `unknown … <repr>` diagnostics carry a
/// QUOTED, ASCII-ONLY rendering of the offending tag/mode. This is NOT Rust
/// `{:?}` Debug: `char::escape_debug` consults a Unicode printability table
/// that is rustc-version-dependent and cannot be mirrored on the JS/BEAM
/// engines (the #8213 retro-audit measured exactly that emulation drift:
/// NUL `\0`, CRLF sliding through grapheme iteration, U+0085/U+00A0/U+0301/
/// U+200D/U+2028 left literal). The contract here is per-CODEPOINT and
/// table-free — identical on every engine: `"` `\` `\n` `\r` `\t` take the C
/// escapes, every codepoint <0x20 or >=0x7F renders `\u{<lowercase hex>}`,
/// printable ASCII stays literal, wrapped in `"`. ASCII-only output means the
/// JSON encoders downstream cannot diverge. evalgleam's `wire_escape_str`
/// (run_plan.gleam) is the twin implementation.
pub fn escape_wire_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || (c as u32) >= 0x7f => {
                out.push_str(&format!("\\u{{{:x}}}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn decode_val(j: &Json) -> Result<Val, String> {
    let tag = j
        .get("tag")
        .and_then(Json::as_str)
        .ok_or("val missing string 'tag'")?;
    let v = match tag {
        "int" => Val::Int(j.get("n").and_then(Json::as_int).ok_or("int.n not int")?),
        "bool" => Val::Bool(j.get("b").and_then(Json::as_bool).ok_or("bool.b not bool")?),
        "list" => {
            let xs = j.get("xs").and_then(Json::as_arr).ok_or("list.xs not array")?;
            Val::list(xs.iter().map(decode_val).collect::<Result<_, _>>()?)
        }
        "opt" => match j.get("v") {
            Some(Json::Null) | None => Val::Opt(None),
            Some(inner) => Val::Opt(Some(Box::new(decode_val(inner)?))),
        },
        "record" => {
            let kvs = j.get("kvs").and_then(Json::as_arr).ok_or("record.kvs not array")?;
            let mut out = Vec::with_capacity(kvs.len());
            for pair in kvs {
                let arr = pair.as_arr().ok_or("record kv not a [k, val] pair")?;
                if arr.len() != 2 {
                    return Err("record kv pair must have length 2".to_string());
                }
                let k = arr[0].as_str().ok_or("record key not a string")?;
                out.push((k.to_string(), decode_val(&arr[1])?));
            }
            Val::Record(out)
        }
        "ok" => Val::Ok(Box::new(decode_val(j.get("v").ok_or("ok.v missing")?)?)),
        "err" => Val::Err(Box::new(decode_val(j.get("v").ok_or("err.v missing")?)?)),
        "residue" => Val::Residue(Box::new(decode_val(j.get("v").ok_or("residue.v missing")?)?)),
        "str" => Val::str(
            j.get("s")
                .and_then(Json::as_str)
                .ok_or("str.s not a string")?
                .to_string(),
        ),
        other => return Err(format!("unknown Val tag {}", escape_wire_str(other))),
    };
    Ok(v)
}

/// Decode the Programs table wire form (mirror of `_wire_programs`):
/// `[[name, [params…], bodyJson], …]` → `Vec<(name, (params, body))>`.
pub fn decode_programs(j: &Json) -> Result<crate::ast::Programs, String> {
    let arr = j.as_arr().ok_or("programs not an array")?;
    let mut out = Vec::with_capacity(arr.len());
    for entry in arr {
        let e = entry.as_arr().ok_or("program entry not a [name, params, body] triple")?;
        if e.len() != 3 {
            return Err("program entry must have length 3".to_string());
        }
        let name = e[0].as_str().ok_or("program name not a string")?;
        let params_arr = e[1].as_arr().ok_or("program params not an array")?;
        let mut params = Vec::with_capacity(params_arr.len());
        for p in params_arr {
            params.push(p.as_str().ok_or("program param not a string")?.to_string());
        }
        let body = decode_expr(&e[2])?;
        out.push((name.to_string(), (params, body)));
    }
    Ok(out)
}

pub fn decode_env(j: &Json) -> Result<Vec<(String, Val)>, String> {
    let arr = j.as_arr().ok_or("env not an array")?;
    let mut out = Vec::with_capacity(arr.len());
    // The harness pushes [[name, val], …]; later bindings should shadow
    // earlier ones via front-lookup, so we keep input order and rely on
    // eval's `lookup` (first match wins) — but the env codec lists each name
    // once, so order is immaterial here. We preserve it for fidelity.
    for pair in arr {
        let p = pair.as_arr().ok_or("env entry not a [name, val] pair")?;
        if p.len() != 2 {
            return Err("env entry pair must have length 2".to_string());
        }
        let name = p[0].as_str().ok_or("env name not a string")?;
        out.push((name.to_string(), decode_val(&p[1])?));
    }
    Ok(out)
}
