import rcic.RcicLeanImportQ

/-!
# Agent proof fabric — `stmt_q` / `body_q` / `goal_q` as a composition over the import encoding

Plan #7929 P1.1: the fabric and the import lane use **one** encoding definition. The definition is the
import lane's (#7927, `RcicLeanImport` / `RcicLeanImportQ`): the translation `trExpr` (metadata, binder
names, binder info and `letE` nonDep erased; level parameters by position; fvar / mvar / proj / string
literals / `Quot` refused by named residue), the tagged grammar `encExprParts`, and the digests
`Rcic.LeanImport.stmtQ` / `bodyQ`. This module defines no expression grammar and no digest of its own.

`trExpr` takes the constant-reference table `resolve : Name → Option Nat` as a parameter, and
`Rcic.LeanImport.stmtQ` hashes the level-parameter *names*. A fact index over a whole environment needs
two things that #7927 leaves to the caller, so they are supplied here by composition:

1. **A per-declaration reference table.** The references of a term, in first-occurrence order
   (`refsOf`), resolved by #7927's own `indexOfName`. This does not depend on which other declarations
   are indexed, so a declaration's `stmt_q` does not move when another declaration is added. The names
   in that order are hashed beside #7927's digest (`fabricQ`), so two statements of the same shape over
   different constants stay distinct. Constants are identified by name (a named limit: no δ, and a
   renamed constant changes the hash).
2. **Positional level-parameter names.** `Rcic.LeanImport.stmtQ` hashes the parameter names it is given.
   It is given `posParams k` (`u0 … u(k-1)`), so only the number of level parameters enters `stmt_q`.

`stmt_q = sha256Hex ("fabric.stmt|" ++ Rcic.LeanImport.stmtQ (posParams k) t ++ "|" ++ refs)`, with `t`
the image of `trExpr` under the table of item 1. `body_q` is the same over `Rcic.LeanImport.bodyQ`.
`goal_q = stmt_q`.

Proved here for terms of every depth (not one binder):
- `stmtQ_relabel`: invariant under renaming every binder name, changing every binder info and every
  `letE` nonDep flag (α-equivalence in the de Bruijn representation);
- `stmtQ_renameLevels`: invariant under any injective renaming of level parameters;
- `stmtQ_eq_iff_parts`: `stmt_q` is the hash of exactly #7927's digest and the reference names.

`closure_claim = 0`.
-/

namespace Rcic.Fabric.Q

open Rcic.LeanImport

/-! ## 1. The reference table -/

/-- Append `n` unless it is already present. -/
def addRef (acc : List Lean.Name) (n : Lean.Name) : List Lean.Name :=
  if acc.contains n then acc else acc ++ [n]

/-- The constants of a term in first-occurrence order (pre-order, left to right), after `acc`. -/
def refsAcc : Lean.Expr → List Lean.Name → List Lean.Name
  | .const n _, acc => addRef acc n
  | .app f x, acc => refsAcc x (refsAcc f acc)
  | .lam _ t b _, acc => refsAcc b (refsAcc t acc)
  | .forallE _ t b _, acc => refsAcc b (refsAcc t acc)
  | .letE _ t v b _, acc => refsAcc b (refsAcc v (refsAcc t acc))
  | .mdata _ e, acc => refsAcc e acc
  | .proj _ _ e, acc => refsAcc e acc
  | _, acc => acc

def refsOf (e : Lean.Expr) : List Lean.Name := refsAcc e []

/-- The per-declaration table, resolved by #7927's `indexOfName`. -/
def localResolve (refs : List Lean.Name) : Lean.Name → Option Nat := indexOfName refs

/-- Length-prefixed names, so that no name can run into the next. -/
def encRefs : List Lean.Name → String
  | [] => ""
  | n :: ns => toString n.toString.length ++ ":" ++ n.toString ++ encRefs ns

/-- `u0 … u(k-1)`. -/
def posParams (k : Nat) : List Lean.Name :=
  (List.range k).map fun i => Lean.Name.mkSimple ("u" ++ toString i)

/-! ## 2. The composed digests -/

def fabricQ (tag inner : String) (refs : List Lean.Name) : String :=
  Residua.SHA256.sha256Hex ("fabric." ++ tag ++ "|" ++ inner ++ "|" ++ encRefs refs)

/-- `stmt_q` of a declaration type `t` under level parameters `ps`, with translation fuel `fuel`. -/
def stmtQ (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) : Except String String :=
  let refs := refsOf t
  match trExpr fuel ps (localResolve refs) t with
  | .error e => .error e
  | .ok t' => .ok (fabricQ "stmt" (Rcic.LeanImport.stmtQ (posParams ps.length) t') refs)

/-- `body_q` of a declaration value `v`. -/
def bodyQ (fuel : Nat) (ps : List Lean.Name) (v : Lean.Expr) : Except String String :=
  let refs := refsOf v
  match trExpr fuel ps (localResolve refs) v with
  | .error e => .error e
  | .ok v' => .ok (fabricQ "body" (Rcic.LeanImport.bodyQ (some v')) refs)

/-- A goal is a statement. -/
def goalQ (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) : Except String String :=
  stmtQ fuel ps t

theorem goalQ_eq_stmtQ (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) :
    goalQ fuel ps t = stmtQ fuel ps t := rfl

theorem stmtQ_eq_iff_parts (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) (t' : RCExpr)
    (h : trExpr fuel ps (localResolve (refsOf t)) t = .ok t') :
    stmtQ fuel ps t =
      .ok (fabricQ "stmt" (Rcic.LeanImport.stmtQ (posParams ps.length) t') (refsOf t)) := by
  simp only [stmtQ, h]

/-- A refusal of the import translation is a refusal of `stmt_q`, with the same residue. -/
theorem stmtQ_refused (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) (r : String)
    (h : trExpr fuel ps (localResolve (refsOf t)) t = .error r) : stmtQ fuel ps t = .error r := by
  simp only [stmtQ, h]

/-! ## 3. α-invariance at every depth -/

/-- Rename every binder name (`f`), change every binder info (`g`) and every `letE` nonDep flag (`k`). -/
def relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo) (k : Bool → Bool) :
    Lean.Expr → Lean.Expr
  | .app a b => .app (relabel f g k a) (relabel f g k b)
  | .lam n t b bi => .lam (f n) (relabel f g k t) (relabel f g k b) (g bi)
  | .forallE n t b bi => .forallE (f n) (relabel f g k t) (relabel f g k b) (g bi)
  | .letE n t v b nd => .letE (f n) (relabel f g k t) (relabel f g k v) (relabel f g k b) (k nd)
  | .mdata d e => .mdata d (relabel f g k e)
  | .proj s i e => .proj s i (relabel f g k e)
  | e => e

theorem refsAcc_relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo)
    (k : Bool → Bool) : ∀ (e : Lean.Expr) (acc : List Lean.Name),
    refsAcc (relabel f g k e) acc = refsAcc e acc
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app a b, acc => by
      simp only [relabel, refsAcc, refsAcc_relabel f g k a, refsAcc_relabel f g k b]
  | .lam _ t b _, acc => by
      simp only [relabel, refsAcc, refsAcc_relabel f g k t, refsAcc_relabel f g k b]
  | .forallE _ t b _, acc => by
      simp only [relabel, refsAcc, refsAcc_relabel f g k t, refsAcc_relabel f g k b]
  | .letE _ t v b _, acc => by
      simp only [relabel, refsAcc, refsAcc_relabel f g k t, refsAcc_relabel f g k v,
        refsAcc_relabel f g k b]
  | .mdata _ e, acc => by simp only [relabel, refsAcc, refsAcc_relabel f g k e]
  | .proj _ _ e, acc => by simp only [relabel, refsAcc, refsAcc_relabel f g k e]

theorem refsOf_relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo)
    (k : Bool → Bool) (e : Lean.Expr) : refsOf (relabel f g k e) = refsOf e :=
  refsAcc_relabel f g k e []

/-- #7927's translation does not see binder names, binder info or nonDep flags, at any depth. -/
theorem trExpr_relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo)
    (k : Bool → Bool) (ps : List Lean.Name) (r : Lean.Name → Option Nat) :
    ∀ (n : Nat) (e : Lean.Expr), trExpr n ps r (relabel f g k e) = trExpr n ps r e
  | 0, _ => rfl
  | n + 1, .bvar _ => rfl
  | n + 1, .fvar _ => rfl
  | n + 1, .mvar _ => rfl
  | n + 1, .sort _ => rfl
  | n + 1, .const _ _ => rfl
  | n + 1, .lit _ => rfl
  | n + 1, .app a b => by
      simp only [relabel, trExpr, trExpr_relabel f g k ps r n a, trExpr_relabel f g k ps r n b]
  | n + 1, .lam _ t b _ => by
      simp only [relabel, trExpr, trExpr_relabel f g k ps r n t, trExpr_relabel f g k ps r n b]
  | n + 1, .forallE _ t b _ => by
      simp only [relabel, trExpr, trExpr_relabel f g k ps r n t, trExpr_relabel f g k ps r n b]
  | n + 1, .letE _ t v b _ => by
      simp only [relabel, trExpr, trExpr_relabel f g k ps r n t, trExpr_relabel f g k ps r n v,
        trExpr_relabel f g k ps r n b]
  | n + 1, .mdata _ e => by simp only [relabel, trExpr, trExpr_relabel f g k ps r n e]
  | n + 1, .proj _ _ _ => rfl

/-- **α-invariance of `stmt_q`**, for terms of any depth. -/
theorem stmtQ_relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo)
    (k : Bool → Bool) (fuel : Nat) (ps : List Lean.Name) (t : Lean.Expr) :
    stmtQ fuel ps (relabel f g k t) = stmtQ fuel ps t := by
  simp only [stmtQ, refsOf_relabel, trExpr_relabel]

theorem bodyQ_relabel (f : Lean.Name → Lean.Name) (g : Lean.BinderInfo → Lean.BinderInfo)
    (k : Bool → Bool) (fuel : Nat) (ps : List Lean.Name) (v : Lean.Expr) :
    bodyQ fuel ps (relabel f g k v) = bodyQ fuel ps v := by
  simp only [bodyQ, refsOf_relabel, trExpr_relabel]

/-! ## 4. Level-parameter renaming at every depth -/

def renameLevel (σ : Lean.Name → Lean.Name) : Lean.Level → Lean.Level
  | .zero => .zero
  | .succ l => .succ (renameLevel σ l)
  | .max a b => .max (renameLevel σ a) (renameLevel σ b)
  | .imax a b => .imax (renameLevel σ a) (renameLevel σ b)
  | .param n => .param (σ n)
  | .mvar m => .mvar m

def renameLevels (σ : Lean.Name → Lean.Name) : Lean.Expr → Lean.Expr
  | .sort u => .sort (renameLevel σ u)
  | .const n us => .const n (us.map (renameLevel σ))
  | .app a b => .app (renameLevels σ a) (renameLevels σ b)
  | .lam n t b bi => .lam n (renameLevels σ t) (renameLevels σ b) bi
  | .forallE n t b bi => .forallE n (renameLevels σ t) (renameLevels σ b) bi
  | .letE n t v b nd => .letE n (renameLevels σ t) (renameLevels σ v) (renameLevels σ b) nd
  | .mdata d e => .mdata d (renameLevels σ e)
  | .proj s i e => .proj s i (renameLevels σ e)
  | e => e

/-- `σ` is injective, stated on `==` (the equality `indexOfName` uses). -/
def BeqInjective (σ : Lean.Name → Lean.Name) : Prop := ∀ a b, (σ a == σ b) = (a == b)

theorem indexOfName_map (σ : Lean.Name → Lean.Name) (hσ : BeqInjective σ) (m : Lean.Name) :
    ∀ ps : List Lean.Name, indexOfName (ps.map σ) (σ m) = indexOfName ps m
  | [] => rfl
  | p :: ps => by
      simp only [List.map_cons, indexOfName, hσ p m, indexOfName_map σ hσ m ps]

theorem trLevel_rename (σ : Lean.Name → Lean.Name) (hσ : BeqInjective σ) (ps : List Lean.Name) :
    ∀ u : Lean.Level, trLevel (ps.map σ) (renameLevel σ u) = trLevel ps u
  | .zero => rfl
  | .succ u => by simp only [renameLevel, trLevel, trLevel_rename σ hσ ps u]
  | .max a b => by simp only [renameLevel, trLevel, trLevel_rename σ hσ ps a, trLevel_rename σ hσ ps b]
  | .imax a b => by
      simp only [renameLevel, trLevel, trLevel_rename σ hσ ps a, trLevel_rename σ hσ ps b]
  | .param n => by simp only [renameLevel, trLevel, indexOfName_map σ hσ n ps]
  | .mvar _ => rfl

theorem trLevels_rename (σ : Lean.Name → Lean.Name) (hσ : BeqInjective σ) (ps : List Lean.Name) :
    ∀ us : List Lean.Level, trLevels (ps.map σ) (us.map (renameLevel σ)) = trLevels ps us
  | [] => rfl
  | u :: us => by
      simp only [List.map_cons, trLevels, trLevel_rename σ hσ ps u, trLevels_rename σ hσ ps us]

theorem refsAcc_renameLevels (σ : Lean.Name → Lean.Name) :
    ∀ (e : Lean.Expr) (acc : List Lean.Name), refsAcc (renameLevels σ e) acc = refsAcc e acc
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app a b, acc => by
      simp only [renameLevels, refsAcc, refsAcc_renameLevels σ a, refsAcc_renameLevels σ b]
  | .lam _ t b _, acc => by
      simp only [renameLevels, refsAcc, refsAcc_renameLevels σ t, refsAcc_renameLevels σ b]
  | .forallE _ t b _, acc => by
      simp only [renameLevels, refsAcc, refsAcc_renameLevels σ t, refsAcc_renameLevels σ b]
  | .letE _ t v b _, acc => by
      simp only [renameLevels, refsAcc, refsAcc_renameLevels σ t, refsAcc_renameLevels σ v,
        refsAcc_renameLevels σ b]
  | .mdata _ e, acc => by simp only [renameLevels, refsAcc, refsAcc_renameLevels σ e]
  | .proj _ _ e, acc => by simp only [renameLevels, refsAcc, refsAcc_renameLevels σ e]

theorem trExpr_renameLevels (σ : Lean.Name → Lean.Name) (hσ : BeqInjective σ)
    (ps : List Lean.Name) (r : Lean.Name → Option Nat) :
    ∀ (n : Nat) (e : Lean.Expr), trExpr n (ps.map σ) r (renameLevels σ e) = trExpr n ps r e
  | 0, _ => rfl
  | n + 1, .bvar _ => rfl
  | n + 1, .fvar _ => rfl
  | n + 1, .mvar _ => rfl
  | n + 1, .sort u => by simp only [renameLevels, trExpr, trLevel_rename σ hσ ps u]
  | n + 1, .const c us => by simp only [renameLevels, trExpr, trLevels_rename σ hσ ps us]
  | n + 1, .lit _ => rfl
  | n + 1, .app a b => by
      simp only [renameLevels, trExpr, trExpr_renameLevels σ hσ ps r n a,
        trExpr_renameLevels σ hσ ps r n b]
  | n + 1, .lam _ t b _ => by
      simp only [renameLevels, trExpr, trExpr_renameLevels σ hσ ps r n t,
        trExpr_renameLevels σ hσ ps r n b]
  | n + 1, .forallE _ t b _ => by
      simp only [renameLevels, trExpr, trExpr_renameLevels σ hσ ps r n t,
        trExpr_renameLevels σ hσ ps r n b]
  | n + 1, .letE _ t v b _ => by
      simp only [renameLevels, trExpr, trExpr_renameLevels σ hσ ps r n t,
        trExpr_renameLevels σ hσ ps r n v, trExpr_renameLevels σ hσ ps r n b]
  | n + 1, .mdata _ e => by simp only [renameLevels, trExpr, trExpr_renameLevels σ hσ ps r n e]
  | n + 1, .proj _ _ _ => rfl

/-- **Level-renaming invariance of `stmt_q`**: renaming the level parameters injectively (in the
    parameter list and everywhere in the term) does not change `stmt_q`. -/
theorem stmtQ_renameLevels (σ : Lean.Name → Lean.Name) (hσ : BeqInjective σ) (fuel : Nat)
    (ps : List Lean.Name) (t : Lean.Expr) :
    stmtQ fuel (ps.map σ) (renameLevels σ t) = stmtQ fuel ps t := by
  simp only [stmtQ, refsOf, refsAcc_renameLevels, trExpr_renameLevels σ hσ, List.length_map]

/-! ## 5. Distinctness the composition adds -/

/-- Two statements whose #7927 digests agree but whose constants differ are kept apart, unless the
    two reference encodings collide in the hash: equal `stmt_q` gives equal hashed strings. -/
theorem stmtQ_hash_input (fuel : Nat) (ps ps' : List Lean.Name) (t u : Lean.Expr) (t' u' : RCExpr)
    (ht : trExpr fuel ps (localResolve (refsOf t)) t = .ok t')
    (hu : trExpr fuel ps' (localResolve (refsOf u)) u = .ok u') :
    stmtQ fuel ps t = stmtQ fuel ps' u ↔
      fabricQ "stmt" (Rcic.LeanImport.stmtQ (posParams ps.length) t') (refsOf t) =
        fabricQ "stmt" (Rcic.LeanImport.stmtQ (posParams ps'.length) u') (refsOf u) := by
  simp only [stmtQ, ht, hu, Except.ok.injEq]

end Rcic.Fabric.Q
