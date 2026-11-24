//! A minimal, dependency-free JSON value + parser + serializer.
//!
//! WHY hand-written (not serde): the crate must build OFFLINE in the gate /
//! sandbox (no crates.io fetch). The JSON surface we need is small and fixed
//! (objects, arrays, strings, ints, bools, null) — the slot wire never carries
//! floats (integer-core) and never needs fancy escaping beyond the basics.
//!
//! The fuzzer compares the binary's stdout AFTER `json.loads` (see
//! `run_exe` in slot_eval_exe_conformance.py: `return json.loads(out)`), so
//! byte-for-byte key ORDER does NOT matter — structural JSON equality does.
//! That means our serializer is free to emit a canonical key order; what must
//! match exactly are the field NAMES and the value SHAPES.

use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// Integer-core: the slot wire only ever carries integer numbers.
    Int(i64),
    Str(String),
    Arr(Vec<Json>),
    /// Object preserving INSERTION order (needed when we read wire `makeRecord`
    /// field lists as arrays — but objects themselves we read order-agnostically).
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get<'a>(&'a self, key: &str) -> Option<&'a Json> {
        match self {
            Json::Obj(kvs) => kvs.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        if let Json::Str(s) = self {
            Some(s)
        } else {
            None
        }
    }
    pub fn as_int(&self) -> Option<i64> {
        if let Json::Int(n) = self {
            Some(*n)
        } else {
            None
        }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Json::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }
    pub fn as_arr(&self) -> Option<&Vec<Json>> {
        if let Json::Arr(a) = self {
            Some(a)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Serialize — canonical, compact (no spaces). Key order is fixed at call sites.
// ---------------------------------------------------------------------------

pub fn to_string(j: &Json) -> String {
    let mut s = String::new();
    write_json(j, &mut s);
    s
}

fn write_json(j: &Json, out: &mut String) {
    match j {
        Json::Null => out.push_str("null"),
        Json::Bool(true) => out.push_str("true"),
        Json::Bool(false) => out.push_str("false"),
        Json::Int(n) => out.push_str(&n.to_string()),
        Json::Str(s) => write_str(s, out),
        Json::Arr(a) => {
            out.push('[');
            for (i, e) in a.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_json(e, out);
            }
            out.push(']');
        }
        Json::Obj(kvs) => {
            out.push('{');
            for (i, (k, v)) in kvs.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_str(k, out);
                out.push(':');
                write_json(v, out);
            }
            out.push('}');
        }
    }
}

fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

// ---------------------------------------------------------------------------
// Parse — a small recursive-descent parser over &[u8].
// ---------------------------------------------------------------------------

/// MAX_DEPTH — the maximum container ([ / {) nesting the parser (and the wire
/// Expr decoder, which reuses this constant) will recurse into. A deeper input
/// gets the NAMED error envelope `[evalr_decode_depth_exceeded]` instead of
/// overflowing the native stack (SIGABRT) — the contract is a named {ok:false}
/// answer, NEVER a crash and NEVER silent truncation. Because the recursive
/// evaluator only ever sees exprs decoded through this bound, it also bounds
/// eval's recursion on wire-supplied input.
///
/// WHY 256: far deeper than any legal slot wire (corpus/fixture exprs nest a
/// few dozen levels at most), and CALIBRATED to the worst build profile —
/// debug-build parse+decode+eval frames measure ~16 KiB/level, so 256 levels
/// cost ~4 MiB, a 2x margin inside the 8 MiB main-thread stack the binary
/// runs on. (512 was measured BORDERLINE in debug: ~8 MiB, i.e. a depth-legal
/// input could still SIGABRT — exactly the bug this bound exists to kill.)
pub const MAX_DEPTH: usize = 512;

pub fn parse(s: &str) -> Result<Json, String> {
    let mut p = Parser {
        b: s.as_bytes(),
        i: 0,
        depth: 0,
    };
    p.ws();
    let v = p.value()?;
    p.ws();
    if p.i != p.b.len() {
        return Err(format!("trailing input at byte {}", p.i));
    }
    Ok(v)
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
    /// Current container nesting depth — checked against MAX_DEPTH on every
    /// object/array entry so deep input fails LOUD with a named error.
    depth: usize,
}

impl<'a> Parser<'a> {
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    /// Enter one container level; the NAMED depth error past MAX_DEPTH.
    fn enter(&mut self) -> Result<(), String> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(format!(
                "[evalr_decode_depth_exceeded] JSON nesting deeper than MAX_DEPTH={} at byte {}",
                MAX_DEPTH, self.i
            ));
        }
        Ok(())
    }

    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        match self.peek() {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b't') | Some(b'f') => self.boolean(),
            Some(b'n') => self.null(),
            Some(c) if c == b'-' || c.is_ascii_digit() => self.number(),
            other => Err(format!("unexpected byte {:?} at {}", other, self.i)),
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.enter()?; // depth-bound BEFORE recursing (MAX_DEPTH, named error)
        self.i += 1; // {
        let mut kvs = Vec::new();
        self.ws();
        if self.peek() == Some(b'}') {
            self.i += 1;
            self.depth -= 1;
            return Ok(Json::Obj(kvs));
        }
        loop {
            self.ws();
            let k = self.string()?;
            self.ws();
            if self.peek() != Some(b':') {
                return Err(format!("expected ':' at {}", self.i));
            }
            self.i += 1;
            let v = self.value()?;
            kvs.push((k, v));
            self.ws();
            match self.peek() {
                Some(b',') => {
                    self.i += 1;
                    continue;
                }
                Some(b'}') => {
                    self.i += 1;
                    break;
                }
                other => return Err(format!("expected ',' or '}}' at {}, got {:?}", self.i, other)),
            }
        }
        self.depth -= 1;
        Ok(Json::Obj(kvs))
    }

    fn array(&mut self) -> Result<Json, String> {
        self.enter()?; // depth-bound BEFORE recursing (MAX_DEPTH, named error)
        self.i += 1; // [
        let mut a = Vec::new();
        self.ws();
        if self.peek() == Some(b']') {
            self.i += 1;
            self.depth -= 1;
            return Ok(Json::Arr(a));
        }
        loop {
            let v = self.value()?;
            a.push(v);
            self.ws();
            match self.peek() {
                Some(b',') => {
                    self.i += 1;
                    continue;
                }
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                other => return Err(format!("expected ',' or ']' at {}, got {:?}", self.i, other)),
            }
        }
        self.depth -= 1;
        Ok(Json::Arr(a))
    }

    fn string(&mut self) -> Result<String, String> {
        if self.peek() != Some(b'"') {
            return Err(format!("expected '\"' at {}", self.i));
        }
        self.i += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err("unterminated string".to_string()),
                Some(b'"') => {
                    self.i += 1;
                    break;
                }
                Some(b'\\') => {
                    self.i += 1;
                    match self.peek() {
                        Some(b'"') => out.push('"'),
                        Some(b'\\') => out.push('\\'),
                        Some(b'/') => out.push('/'),
                        Some(b'n') => out.push('\n'),
                        Some(b't') => out.push('\t'),
                        Some(b'r') => out.push('\r'),
                        Some(b'b') => out.push('\u{0008}'),
                        Some(b'f') => out.push('\u{000C}'),
                        Some(b'u') => {
                            let hex = self
                                .b
                                .get(self.i + 1..self.i + 5)
                                .ok_or("truncated \\u escape")?;
                            let code = u32::from_str_radix(
                                std::str::from_utf8(hex).map_err(|_| "bad \\u hex")?,
                                16,
                            )
                            .map_err(|_| "bad \\u hex")?;
                            // frozen-substrate-repair: [evalgleam_js_json_surrogate_divergence]
                            // Surrogate-pair joining per RFC 8259 — canonical
                            // wire spells astral chars as \uD800-\uDBFF +
                            // \uDC00-\uDFFF. Same arm + same refusal texts as
                            // evalgleam_ffi.erl's parse_string.
                            if (0xD800..=0xDBFF).contains(&code) {
                                let lo_hex = self
                                    .b
                                    .get(self.i + 5..self.i + 11)
                                    .filter(|w| w.starts_with(b"\\u"));
                                let lo = lo_hex
                                    .and_then(|w| std::str::from_utf8(&w[2..]).ok())
                                    .and_then(|h| u32::from_str_radix(h, 16).ok())
                                    .filter(|c| (0xDC00..=0xDFFF).contains(c))
                                    .ok_or("high surrogate not followed by low surrogate")?;
                                let joined =
                                    0x10000 + ((code - 0xD800) << 10) + (lo - 0xDC00);
                                out.push(char::from_u32(joined).ok_or("bad \\u codepoint")?);
                                self.i += 10;
                            } else if (0xDC00..=0xDFFF).contains(&code) {
                                return Err("lone low surrogate".to_string());
                            } else {
                                out.push(char::from_u32(code).ok_or("bad \\u codepoint")?);
                                self.i += 4;
                            }
                        }
                        other => return Err(format!("bad escape {:?}", other)),
                    }
                    self.i += 1;
                }
                Some(_) => {
                    // Copy a full UTF-8 scalar (the slot wire is ASCII keys, but be safe).
                    let start = self.i;
                    self.i += 1;
                    while self.i < self.b.len() && (self.b[self.i] & 0xC0) == 0x80 {
                        self.i += 1;
                    }
                    out.push_str(
                        std::str::from_utf8(&self.b[start..self.i]).map_err(|_| "bad utf8")?,
                    );
                }
            }
        }
        Ok(out)
    }

    fn number(&mut self) -> Result<Json, String> {
        // Integer-core: parse an optional '-' then digits. Reject a decimal
        // point loudly (the wire must never carry a float — E1_float_OPEN).
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            self.i += 1;
        }
        if self.peek() == Some(b'.') || self.peek() == Some(b'e') || self.peek() == Some(b'E') {
            return Err(format!(
                "non-integer number at {} (integer-core / E1_float_OPEN)",
                start
            ));
        }
        let text = std::str::from_utf8(&self.b[start..self.i]).map_err(|_| "bad number utf8")?;
        text.parse::<i64>()
            .map(Json::Int)
            .map_err(|e| format!("bad int {:?}: {}", text, e))
    }

    fn boolean(&mut self) -> Result<Json, String> {
        if self.b[self.i..].starts_with(b"true") {
            self.i += 4;
            Ok(Json::Bool(true))
        } else if self.b[self.i..].starts_with(b"false") {
            self.i += 5;
            Ok(Json::Bool(false))
        } else {
            Err(format!("bad literal at {}", self.i))
        }
    }

    fn null(&mut self) -> Result<Json, String> {
        if self.b[self.i..].starts_with(b"null") {
            self.i += 4;
            Ok(Json::Null)
        } else {
            Err(format!("bad literal at {}", self.i))
        }
    }
}

/// Convenience: build an ordered object from pairs (call-site fixes key order).
pub fn obj(pairs: Vec<(&str, Json)>) -> Json {
    Json::Obj(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

// A BTreeMap-based structural-equality helper is NOT needed: derive(PartialEq)
// on Json is order-sensitive for Obj, but the fuzzer parses our output with
// json.loads and compares dicts (order-insensitive). To make our own tests
// order-insensitive too, normalize before comparing.
pub fn normalize(j: &Json) -> Json {
    match j {
        Json::Obj(kvs) => {
            let mut m: BTreeMap<String, Json> = BTreeMap::new();
            for (k, v) in kvs {
                m.insert(k.clone(), normalize(v));
            }
            Json::Obj(m.into_iter().collect())
        }
        Json::Arr(a) => Json::Arr(a.iter().map(normalize).collect()),
        other => other.clone(),
    }
}
