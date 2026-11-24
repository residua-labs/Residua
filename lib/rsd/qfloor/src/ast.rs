//! `Expr` and `Val` — Rust mirrors of `tools/mstspec/ir/slot/slot_ast.py`
//! (the `Expr` ctors + the `Val` tagged union) and the Lean
//! `MSTNFSlotSemanticsCoreMWE` `inductive Expr` / `inductive Val`.
//!
//! INTEGER-CORE ([E1_float_OPEN]): every number is an `i64`. The wire codec
//! and the differential fuzzer both assert `Num.value.is_integer()`, so a
//! float never reaches `evalR`. We use `i64` (not bignum) because the
//! fuzzer's operands are small (`-9..=9`) and arithmetic stays well within
//! range; a wider integer is a later brick if the fuzzer's domain grows.
//!
//! Faithfulness is SEALED by the differential fuzzer (evalR-wire ==
//! interp.eval_-wire), not by these type definitions — they are only the
//! transcription surface.

use std::rc::Rc;

/// Shared string value with a cached ASCII flag. `ascii = s.is_ascii()`
/// computed ONCE at construction (`Val::str`) so the string-index ops can
/// take the O(1) byte-indexing path without re-scanning the whole string.
/// `PartialEq` compares both fields; `ascii` is a pure function of `s`, so
/// equality is still by content.
#[derive(Debug, Clone, PartialEq)]
pub struct StrVal {
    pub s: String,
    pub ascii: bool,
}

/// Slot core values — mirrors the Lean `Val` (int/bool/list/opt/record/ok/err/residue).
///
/// `Residue` is a FIRST-CLASS value (a named ρ), distinct from `None`
/// (the typed residue meaning "no value could be produced"). The evaluator
/// returns `Option<Val>`; `None` is the typed residue, `Some(Val::Residue _)`
/// is a legitimate terminal value.
///
/// Sharing: `List` and `Str` are `Rc`-shared so `Var` lookup `.cloned()` is
/// an O(1) refcount bump instead of a deep copy (the reader's per-char
/// `substring` over a 47KB source was the quadratic hot path). Mutating ops
/// go through `Rc::make_mut` — uniquely-owned values mutate in place, shared
/// ones copy — so observable bytes are unchanged.
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Int(i64),
    Bool(bool),
    List(Rc<Vec<Val>>),
    /// Option: `None` inner = Lean `.opt none`; `Some` inner = `.opt (some x)`.
    Opt(Option<Box<Val>>),
    /// Record: ordered (field-name, value) pairs, dedup'd last-write-wins
    /// preserving first-insertion position (matches `insertField`).
    Record(Vec<(String, Val)>),
    Ok(Box<Val>),
    Err(Box<Val>),
    Residue(Box<Val>),
    /// String value — produced by Lean `evalLF` extension-layer string ops
    /// (`strLit` / `strConcat` / `intToStr`). Slot core has no strings; this
    /// variant exists only because the EXTENSION layer (WU-3 60/60) carries
    /// `Lean Expr.strLit / strConcat / strLen / strEq / intToStr`.
    Str(Rc<StrVal>),
}

impl Val {
    /// The only `Str` constructor: computes the cached ASCII flag once.
    #[inline]
    pub fn str(s: impl Into<String>) -> Val {
        let s = s.into();
        Val::Str(Rc::new(StrVal {
            ascii: s.is_ascii(),
            s,
        }))
    }

    /// The `List` constructor (Rc-wraps the vec).
    #[inline]
    pub fn list(xs: Vec<Val>) -> Val {
        Val::List(Rc::new(xs))
    }
}

/// The well-typed-core slot expression language. Constructor set + field
/// order mirror `slot_ast.py` and the Lean `inductive Expr`.
///
/// Scope note: this is the WELL-TYPED CORE the differential fuzzer
/// generates (see `slot_differential_fuzz.py`'s imports). The remaining
/// full-set ctors (groupBy/orderBy/glue/dischargeProp/useCountCheck/
/// findFirst/alwaysUntil/eventuallyAfter/boundedFix/call/listWindow/
/// listIndexed/listTake) are transcribed here too where cheap, and the
/// genuinely-deferred ones are listed as TODO in `eval.rs`. The fuzzer's
/// generated nodes are the seal target; extra ctors are decode-ready but
/// not all evaluated yet (each is explicitly marked).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // --- Literals ---
    Num(i64),
    /// A `Num` leaf whose Python-side value is a FLOAT that the integer-core
    /// `i64` cannot carry (non-integral, or integral-but-past the IEEE-exact
    /// `float:{n}.0` domain). The payload is Python's `repr(value)` verbatim —
    /// the substrate validates it as a float repr at decode but never
    /// re-derives CPython formatting. Hash-only: eval reduces it to the typed
    /// residue (the `[E1_float_OPEN]` boundary), same as a non-core literal.
    NumF(String),
    BoolLit(bool),
    Var(String),

    // --- Arithmetic ---
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    AbsE(Box<Expr>),
    MinE(Box<Expr>, Box<Expr>),
    MaxE(Box<Expr>, Box<Expr>),

    // --- Comparison ---
    Lt(Box<Expr>, Box<Expr>),
    Lte(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Gte(Box<Expr>, Box<Expr>),
    EqE(Box<Expr>, Box<Expr>),

    // --- Boolean ---
    AndE(Box<Expr>, Box<Expr>),
    OrE(Box<Expr>, Box<Expr>),
    NotE(Box<Expr>),

    // --- Conditional / binding ---
    IfE(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),

    // --- Record ---
    MakeRecord(Vec<(String, Expr)>),
    FieldAccess(Box<Expr>, String),

    // --- Option ---
    NoneLit,
    SomeE(Box<Expr>),
    IsNoneE(Box<Expr>),
    IsSomeE(Box<Expr>),
    UnwrapSome(Box<Expr>),

    // --- Result ---
    OkE(Box<Expr>),
    ErrE(Box<Expr>),
    IsOkE(Box<Expr>),
    GetOk(Box<Expr>),

    // --- Residue ρ (E1.15) ---
    ResidueE(Box<Expr>),
    IsResidueE(Box<Expr>),
    GetResidue(Box<Expr>),

    // --- List ---
    EmptyList,
    ListSingleton(Box<Expr>),
    ListAppend(Box<Expr>, Box<Expr>),
    ListLen(Box<Expr>),
    ListFirst(Box<Expr>),
    ListLast(Box<Expr>),
    ListDrop(Box<Expr>, Box<Expr>),
    ListTake(Box<Expr>, Box<Expr>),
    ListWindow(Box<Expr>, usize),
    ListIndexed(Box<Expr>),

    // --- Bounded fold (the looping node the fuzzer emits) ---
    BoundedFold {
        list: Box<Expr>,
        init: Box<Expr>,
        acc_var: String,
        item_var: String,
        body: Box<Expr>,
    },

    // --- E1.12 GroupBy — quotient q as first-class (evalLF .groupBy). ---
    GroupBy {
        list: Box<Expr>,
        item_var: String,
        key_body: Box<Expr>,
    },
    // --- E1.13 OrderBy — total stable sort by int key (evalLF .orderBy). ---
    OrderBy {
        list: Box<Expr>,
        item_var: String,
        key_body: Box<Expr>,
        descending: bool,
    },
    // --- E1.8 FindFirst — fold returning Option (evalLF .findFirst). ---
    // `idx_var` is dead (host binds only item_var) but carried for fidelity.
    FindFirst {
        list: Box<Expr>,
        idx_var: String,
        item_var: String,
        pred: Box<Expr>,
        map_: Box<Expr>,
    },
    // --- E1.8 AlwaysUntil — SAFETY temporal quantifier (evalLF .alwaysUntil). ---
    AlwaysUntil {
        list: Box<Expr>,
        from_t: Box<Expr>,
        item_var: String,
        pred: Box<Expr>,
        stop: Box<Expr>,
    },
    // --- E1.8 EventuallyAfter — LIVENESS temporal quantifier (evalLF .eventuallyAfter). ---
    EventuallyAfter {
        list: Box<Expr>,
        from_t: Box<Expr>,
        item_var: String,
        pred: Box<Expr>,
    },
    // --- E1.10 BoundedFix — bounded fixpoint iteration (evalLF .boundedFix). ---
    BoundedFix {
        state0: Box<Expr>,
        step_var: String,
        step_body: Box<Expr>,
        stop_pred: Box<Expr>,
        fuel: u64,
    },

    // --- R1 operators (specific input shapes) ---
    // E1.16 Glue — sheaf gluing on records (evalLF .glue).
    Glue(Box<Expr>),
    // E1.17 DischargeProp — RDC discharge-propagation (evalLF .dischargeProp).
    DischargeProp(Box<Expr>, Box<Expr>),
    // E1.18 UseCountCheck — substructural use-count tally (evalLF .useCountCheck).
    UseCountCheck(Box<Expr>),

    // --- E1.9 Call — named application against the Programs table (evalLF .call). ---
    Call(String, Vec<Expr>),

    // --- Extension-layer string ops (WU-3 60/60, ADR §9.8).
    // Slot core has no strings; these live ONLY on the Lean evalLF Expr +
    // extracted-Scheme layer + the per-platform wire codecs (this file).
    // closes [per_platform_interp_strops_MISSING].
    StrLit(String),
    StrConcat(Box<Expr>, Box<Expr>),
    StrLen(Box<Expr>),
    StrEq(Box<Expr>, Box<Expr>),
    IntToStr(Box<Expr>),
    /// G3b: `(content-hash e)` — reify Val → content_hash → Str (64 hex).
    ContentHash(Box<Expr>),
    /// `reflect`: Expr → Val (the AST-as-data encoding; ADR reflect-Expr #1448, Conflux P1).
    /// The argument is NOT evaluated — its STRUCTURE is reflected to a canonical tagged
    /// record. `content_hash(reflect(e))` = on-core compound `content_addr` (B3 Q1).
    Reflect(Box<Expr>),
    /// `reifyExpr`: evaluate the argument to a reflection-record Val, decode it back to an
    /// Expr (the inverse of reflect), and evaluate THAT. Residue if the Val ∉ range(reflect).
    ReifyExpr(Box<Expr>),
    // --- slice 0 parse-supporting ops ([extension_strops_insufficient_for_parse]).
    // Required to express _tokenize (and any parser) as an extension-layer
    // belief. Index unit is **Unicode CODE POINT** (Unicode scalar), pinned
    // here so cross-platform parity (Python s[i] / Rust s.chars().nth(i) /
    // Gleam JS codePointAt-iter / Erlang unicode:characters_to_list) byte-equiv
    // on non-ASCII. Documented as a permanent boundary in residues/catalog.json
    // (see [str_index_out_of_bounds] meaning, references ADR §9.9).
    StrCharAt(Box<Expr>, Box<Expr>),
    StrSubstring(Box<Expr>, Box<Expr>, Box<Expr>),
    // StrCodeAt: the Unicode CODE POINT (scalar value, `char as u32`) of the
    // character at code-point index i — the on-core `ord` the canonical-bytes /
    // event-admit / name-grammar consumers each hit for want of a char→int
    // (ADR_CODEPOINT_PRIMITIVE). Index unit is the SAME Unicode code point as
    // StrCharAt (s.chars().nth(i)); OUT OF RANGE (i<0 or i>=len) is the None
    // residue, mirroring StrCharAt's [str_index_out_of_bounds] discipline
    // exactly. Total. Binary ("a"/"b"). NO chr inverse (no consumer needs it).
    StrCodeAt(Box<Expr>, Box<Expr>),

    // --- Capability A (TWS wire-field parsing as beliefs): the parse pair. ---
    // StrToInt: the INVERSE of IntToStr — Lean String.toInt? discipline (optional
    // single leading '-', then 1+ ASCII digits; anything else is the None residue).
    // StrSplit: split on a NON-EMPTY delimiter, keeping empty fields (the shared
    // splitOn convention); an empty delimiter is the None residue.
    StrToInt(Box<Expr>),
    StrSplit(Box<Expr>, Box<Expr>),

    // --- E1.19 MatchTag — closed-tag exhaustive int dispatch (evalLF .matchTag). ---
    // `universe` is admission-only (NOT consulted at runtime); runtime is pure
    // first-match on `branches` (int code → body) with `default` fall-through.
    // Non-int scrut ⇒ residue (host SlotError("[E1.19_scrut_not_int]")).
    MatchTag {
        scrut: Box<Expr>,
        universe: Vec<i64>,
        branches: Vec<(i64, Expr)>,
        default: Box<Expr>,
    },
}

/// E1.9 (#1045): a `Programs` table maps program names to `(param-names,
/// body-Expr)` pairs. `Call` resolves names via this table. Mirrors the Lean
/// `abbrev Programs := List (String × (List String × Expr))` and the host's
/// `progs` dict. Recursion is fuel-bounded (see `eval.rs`).
pub type Programs = Vec<(String, (Vec<String>, Expr))>;
