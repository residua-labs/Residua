/-
Parse the landed `encExpr` / `encLevel` grammar back into `Expr Nat`.

The bytes are the translator's `type_text` / `body_text`. This is the inverse
of `Rcic.LeanImport.encExpr`, used by the slice-2 measurement driver. It is
not a second encoding.
-/
import rcic.RcicLeanImport
import rcic.RcicLeanImportQ

namespace Rcic.LeanImport.Slice2

open Rcic.Declarative

def readNat : List Char → Option (Nat × List Char)
  | [] => none
  | c :: cs =>
    if !c.isDigit then none
    else
      let rec go (n : Nat) : List Char → Nat × List Char
        | [] => (n, [])
        | d :: ds =>
          if d.isDigit then go (n * 10 + (d.toNat - '0'.toNat)) ds
          else (n, d :: ds)
      some (go (c.toNat - '0'.toNat) cs)

mutual

def parseLevel (fuel : Nat) (cs : List Char) : Option (Level × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | 'Z' :: rest => some (.zero, rest)
    | 'S' :: '(' :: rest =>
      match parseLevel fuel rest with
      | some (l, ')' :: rest) => some (.succ l, rest)
      | _ => none
    | 'M' :: '(' :: rest =>
      match parseLevel fuel rest with
      | some (a, ',' :: rest) =>
        match parseLevel fuel rest with
        | some (b, ')' :: rest) => some (.max a b, rest)
        | _ => none
      | _ => none
    | 'I' :: '(' :: rest =>
      match parseLevel fuel rest with
      | some (a, ',' :: rest) =>
        match parseLevel fuel rest with
        | some (b, ')' :: rest) => some (.imax a b, rest)
        | _ => none
      | _ => none
    | 'P' :: '(' :: rest =>
      match readNat rest with
      | some (n, ')' :: rest) => some (.param n, rest)
      | _ => none
    | _ => none

def parseLevels (fuel : Nat) (cs : List Char) : Option (List Level × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | ')' :: _ => some ([], cs)
    | _ =>
      match parseLevel fuel cs with
      | some (l, ';' :: rest) =>
        match parseLevels fuel rest with
        | some (ls, rest) => some (l :: ls, rest)
        | none => none
      | _ => none

def parseExprGo (fuel : Nat) (cs : List Char) : Option (Expr Nat × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | 'B' :: '(' :: rest =>
      match readNat rest with
      | some (n, ')' :: rest) => some (.bvar n, rest)
      | _ => none
    | 'U' :: '(' :: rest =>
      match parseLevel fuel rest with
      | some (l, ')' :: rest) => some (.sort l, rest)
      | _ => none
    | 'C' :: '(' :: rest =>
      match readNat rest with
      | some (r, ',' :: rest) =>
        match parseLevels fuel rest with
        | some (ls, ')' :: rest) => some (.const r ls, rest)
        | _ => none
      | _ => none
    | 'T' :: '(' :: rest =>
      match readNat rest with
      | some (n, ')' :: rest) => some (.lit n, rest)
      | _ => none
    | 'A' :: '(' :: rest =>
      match parseExprGo fuel rest with
      | some (a, ',' :: rest) =>
        match parseExprGo fuel rest with
        | some (b, ')' :: rest) => some (.app a b, rest)
        | _ => none
      | _ => none
    | 'L' :: '(' :: rest =>
      match parseExprGo fuel rest with
      | some (a, ',' :: rest) =>
        match parseExprGo fuel rest with
        | some (b, ')' :: rest) => some (.lam a b, rest)
        | _ => none
      | _ => none
    | 'P' :: '(' :: rest =>
      match parseExprGo fuel rest with
      | some (a, ',' :: rest) =>
        match parseExprGo fuel rest with
        | some (b, ')' :: rest) => some (.pi a b, rest)
        | _ => none
      | _ => none
    | 'E' :: '(' :: rest =>
      match parseExprGo fuel rest with
      | some (a, ',' :: rest) =>
        match parseExprGo fuel rest with
        | some (v, ',' :: rest) =>
          match parseExprGo fuel rest with
          | some (b, ')' :: rest) => some (.letE a v b, rest)
          | _ => none
        | _ => none
      | _ => none
    | _ => none

end

def parseExpr (s : String) : Except String (Expr Nat) :=
  let cs := s.toList
  match parseExprGo (cs.length + 1) cs with
  | some (e, []) => .ok e
  | some (_, rest) => .error s!"trailing {rest.length}"
  | none => .error "parse"

theorem slice2_parse_sort_zero :
    parseExpr "U(Z)" = Except.ok (.sort .zero) := by
  rfl

theorem slice2_parse_const_nolevel :
    parseExpr "C(0,)" = Except.ok (.const 0 []) := by
  rfl

theorem slice2_parse_app :
    parseExpr (encExpr (.app (.const 0 []) (.lit 1))) =
      Except.ok (.app (.const 0 []) (.lit 1)) := by
  rfl

end Rcic.LeanImport.Slice2
