/-!
# Bootstrap 1a — μRIR (ADR_BOOTSTRAP_PLAN_V0_1 r4.1/r4.2, r5-thin)

Typed de Bruijn deep embedding. `BootExpr Σ Γ τ`:
  Σ = program signature table (call by index, ruling r4.3; names live in the manifest)
  Γ = typing context (List BootTy), var = Fin index into Γ
  τ = result type

BootTy (r4.1): i64 bool str bytes list pair sum record option residue.
str ≠ bytes (r5-thin): str carries code-point laws, bytes feeds the encoder;
ContentHash eats Bytes ONLY.

Working set = census-30 ∪ encoder ops (ADR 裁定 1, r4 working set):
Sub/Neg/Mul/checked Div-Mod, Pair/match, Bytes pack/len/concat/slice,
ContentHash, ResidueE/GetResidue. fold/fix keep the host law shapes
(fix returns {converged, state, steps} — census: converged 扰动 5/9 红).

0 sorry, 0 axiom. closure_claim = 0.
-/

namespace Residua.Bootstrap.IR

/-- r4.1 BootTy. -/
inductive BootTy where
  | i64 | bool | str | bytes
  | list   (t : BootTy)
  | pair   (a b : BootTy)
  | sum    (ts : List BootTy)
  | record (fs : List (String × BootTy))
  | option (t : BootTy)
  | residue (t : BootTy)

abbrev Ctx := List BootTy

/-- Signature table: (parameter types, return type) per program. Call is by
    index (ruling r4.3); the manifest carries names. -/
abbrev SigTable := List (List BootTy × BootTy)

/-- fix result shape (host law, census-pinned): {converged, state, steps}. -/
def fixResultTy (s : BootTy) : BootTy :=
  .record [("converged", .bool), ("state", s), ("steps", .i64)]

mutual

/-- μRIR expressions. De Bruijn: `var i : BootExpr Σ Γ (Γ.get i)`.
    Binder conventions:
      letE   : value bound at index 0 of the body context
      foldE  : body context = elem :: acc :: Γ (var 0 = element, var 1 = acc)
      fixE   : stop/step context = state :: Γ
      matchE : each branch context = summand :: Γ  -/
inductive BootExpr : SigTable → Ctx → BootTy → Type where
  -- literals / variables / binding / control
  | litI  : Int → BootExpr S G .i64
  | litB  : Bool → BootExpr S G .bool
  | litS  : String → BootExpr S G .str
  | var   : (i : Fin G.length) → BootExpr S G (G.get i)
  | letE  : BootExpr S G a → BootExpr S (a :: G) b → BootExpr S G b
  | ifE   : BootExpr S G .bool → BootExpr S G t → BootExpr S G t → BootExpr S G t
  -- i64 arithmetic (law A lives in Semantics)
  | add   : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .i64
  | sub   : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .i64
  | mul   : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .i64
  | neg   : BootExpr S G .i64 → BootExpr S G .i64
  | divE  : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .i64
  | modE  : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .i64
  -- comparison / bool (comparisons return bool CONSTRUCTOR — law A)
  | lt    : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .bool
  | gt    : BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .bool
  | eqE   : BootExpr S G t → BootExpr S G t → BootExpr S G .bool
  | andE  : BootExpr S G .bool → BootExpr S G .bool → BootExpr S G .bool
  | orE   : BootExpr S G .bool → BootExpr S G .bool → BootExpr S G .bool
  | notE  : BootExpr S G .bool → BootExpr S G .bool
  -- str (code-point laws)
  | strLen       : BootExpr S G .str → BootExpr S G .i64
  | strSplit     : BootExpr S G .str → BootExpr S G .str → BootExpr S G (.list .str)
  | strSubstring : BootExpr S G .str → BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .str
  | strToInt     : BootExpr S G .str → BootExpr S G .i64
  -- list
  | emptyList     : BootExpr S G (.list t)
  | listSingleton : BootExpr S G t → BootExpr S G (.list t)
  | listLen       : BootExpr S G (.list t) → BootExpr S G .i64
  | listFirst     : BootExpr S G (.list t) → BootExpr S G (.option t)
  | listAppend    : BootExpr S G (.list t) → BootExpr S G (.list t) → BootExpr S G (.list t)
  | listDrop      : BootExpr S G .i64 → BootExpr S G (.list t) → BootExpr S G (.list t)
  -- pair
  | pairE : BootExpr S G a → BootExpr S G b → BootExpr S G (.pair a b)
  | fstE  : BootExpr S G (.pair a b) → BootExpr S G a
  | sndE  : BootExpr S G (.pair a b) → BootExpr S G b
  -- sum / match
  | inj    : (i : Fin ts.length) → BootExpr S G (ts.get i) → BootExpr S G (.sum ts)
  | matchE : BootExpr S G (.sum ts) → Branches S G ts r → BootExpr S G r
  -- record
  | recNil  : BootExpr S G (.record [])
  | recCons : (name : String) → BootExpr S G t → BootExpr S G (.record fs) →
              BootExpr S G (.record ((name, t) :: fs))
  | field   : BootExpr S G (.record fs) → (i : Fin fs.length) →
              BootExpr S G (fs.get i).2
  -- option
  | someE      : BootExpr S G t → BootExpr S G (.option t)
  | noneE      : BootExpr S G (.option t)
  | isSomeE    : BootExpr S G (.option t) → BootExpr S G .bool
  | unwrapSome : BootExpr S G (.option t) → BootExpr S G t
  -- first-class residue (typed: residue t = ok t | res code)
  | okE        : BootExpr S G t → BootExpr S G (.residue t)
  | residueE   : Int → BootExpr S G (.residue t)
  | isResidueE : BootExpr S G (.residue t) → BootExpr S G .bool
  | getResidue : BootExpr S G (.residue t) → BootExpr S G .i64
  | getOk      : BootExpr S G (.residue t) → BootExpr S G t
  -- bytes (r5-thin mandatory ctor list; ContentHash eats Bytes ONLY)
  | packBytes   : BootExpr S G (.list .i64) → BootExpr S G .bytes
  | bytesLen    : BootExpr S G .bytes → BootExpr S G .i64
  | bytesConcat : BootExpr S G .bytes → BootExpr S G .bytes → BootExpr S G .bytes
  | bytesSlice  : BootExpr S G .bytes → BootExpr S G .i64 → BootExpr S G .i64 → BootExpr S G .bytes
  | contentHash : BootExpr S G .bytes → BootExpr S G .bytes
  -- fold / fix (host law shapes) / call
  | foldE : BootExpr S G (.list a) → BootExpr S G b →
            BootExpr S (a :: b :: G) b → BootExpr S G b
  | fixE  : BootExpr S (s :: G) .bool → BootExpr S (s :: G) s →
            BootExpr S G s → BootExpr S G .i64 →
            BootExpr S G (fixResultTy s)
  | call  : (f : Fin S.length) → Args S G (S.get f).1 → BootExpr S G (S.get f).2

/-- Argument vectors for call, typed against the callee's parameter list. -/
inductive Args : SigTable → Ctx → List BootTy → Type where
  | nil  : Args S G []
  | cons : BootExpr S G t → Args S G ts → Args S G (t :: ts)

/-- Per-summand match branches; branch i binds the summand value at index 0. -/
inductive Branches : SigTable → Ctx → List BootTy → BootTy → Type where
  | nil  : Branches S G [] r
  | cons : BootExpr S (t :: G) r → Branches S G ts r → Branches S G (t :: ts) r

end

/-- A program table: for each signature, a body typed in its parameter context. -/
inductive Programs : SigTable → SigTable → Type where
  | nil  : Programs S []
  | cons : BootExpr S sig.1 sig.2 → Programs S rest → Programs S (sig :: rest)

end Residua.Bootstrap.IR
