import rcic.RcicAnnAlg

/-!
# M1-d — the relation's ambient definitions (split out by M1-d (iv))

Context well-formedness on the copy, the weakening specs (`insertAtA`,
`WkSpecA`, `wkExprA`/`wkCtxA`, `WkOkA`: the Kripke worlds), level heights
(`ht`, `lvlIdx`) and stuckness (`StuckA`), exactly as M1-d (i) defined them in
`RcicAnnLR`. Split into their own leaf so that the operations layer
(`RcicAnnCtxMorph`, `RcicAnnWkOps`, `RcicAnnWeaken`) can stand BELOW typed
head reduction (`RcicAnnTyRed`), which the relation now reads.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) context well-formedness on the copy -/

inductive CtxWfA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : LCtxA → Type
  | nil : CtxWfA E I n []
  | assumption {Γ : LCtxA} {A : ExprA} {u : Level}
      (hΓ : CtxWfA E I n Γ) (hA : HasTyA E I n Γ A (.sort u)) :
      CtxWfA E I n (.assumption A :: Γ)
  | letBinding {Γ : LCtxA} {A v : ExprA} {u : Level}
      (hΓ : CtxWfA E I n Γ) (hA : HasTyA E I n Γ A (.sort u)) (hv : HasTyA E I n Γ v A) :
      CtxWfA E I n (.letBinding A v :: Γ)

/-! ## (1) weakenings, L-RING's `WkSpec` on the copy -/

def liftDeclA (k : Nat) : LocalDeclA → LocalDeclA
  | .assumption A => .assumption (liftA k 1 A)
  | .letBinding A v => .letBinding (liftA k 1 A) (liftA k 1 v)

def insertAtA (d : LocalDeclA) : Nat → LCtxA → LCtxA
  | 0, Γ => d :: Γ
  | _ + 1, [] => [d]
  | c + 1, x :: Γ => liftDeclA c x :: insertAtA d c Γ

/-- the list of insertions, outermost last. -/
abbrev WkSpecA := List (LocalDeclA × Nat)

def wkExprA : WkSpecA → ExprA → ExprA
  | [], e => e
  | (_, c) :: ρ, e => wkExprA ρ (liftA c 1 e)

def wkDeclA : WkSpecA → LocalDeclA → LocalDeclA
  | [], x => x
  | (_, c) :: ρ, x => wkDeclA ρ (liftDeclA c x)

def wkCtxA : WkSpecA → LCtxA → LCtxA
  | [], Γ => Γ
  | (d, c) :: ρ, Γ => wkCtxA ρ (insertAtA d c Γ)

def WkSpecA.ok : WkSpecA → LCtxA → Prop
  | [], _ => True
  | (d, c) :: ρ, Γ => c ≤ Γ.length ∧ WkSpecA.ok ρ (insertAtA d c Γ)

def WkSpecA.ub : WkSpecA → WkSpecA
  | [] => []
  | (d, c) :: ρ => (d, c + 1) :: WkSpecA.ub ρ

def WkSpecA.comp : WkSpecA → WkSpecA → WkSpecA
  | [], σ => σ
  | (d, c) :: ρ, σ => (d, c) :: WkSpecA.comp ρ σ

/-- Kripke worlds: well-formed extensions. -/
def WkOkA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ : WkSpecA) (Γ : LCtxA) : Prop :=
  WkSpecA.ok ρ Γ ∧ Nonempty (CtxWfA E I n (wkCtxA ρ Γ))

/-! ## (2) heights and shapes -/

/-- height of a level under a TOTAL valuation. -/
def ht (ρ₀ : Nat → Nat) (l : Level) : Nat :=
  (eval (fun i => some (ρ₀ i)) l).getD 0

theorem ht_of_eqN {ρ₀ : Nat → Nat} {l l' : Level} (h : eqN l l') : ht ρ₀ l = ht ρ₀ l' := by
  unfold ht; rw [h]


/-- a SHAPE head: a sort, a pi, or — M2-f (3) — an inductive family of `E` (its
    applications have the `fam` clause, L-RING C3–C7); everything else weak-head
    normal is STUCK. Reads `E` since M2-f (3). -/
def isShapeHeadA (E : ResolvedEnvA) : ExprA → Prop
  | .sort _ => True
  | .pi _ _ _ _ => True
  | .const r _ => ∃ m, E.members r = some m ∧ m.mclass = .inductiveM
  | _ => False

/-- weak-head normal for `hStepFnA`, and headed by neither a sort nor a pi nor a
    family of `E`: variables, non-family constants (axioms, constructors, stuck
    recursors) and their spines. -/
def StuckA (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (N : ExprA) : Prop :=
  hStepFnA E I.fn Γ N = none ∧ ¬ isShapeHeadA E (appsSpineA N).1

theorem stuckA_not_sort {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {l : Level}
    (h : StuckA E I Γ (.sort l)) : False := h.2 (by simp [appsSpineA, isShapeHeadA])

theorem stuckA_not_pi {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {D C : ExprA} {u v : Level}
    (h : StuckA E I Γ (.pi D u C v)) : False := h.2 (by simp [appsSpineA, isShapeHeadA])

/-- a stuck type is not headed by a family of `E`. -/
theorem stuckA_not_fam {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {N : ExprA}
    (h : StuckA E I Γ N) {r : Nat} {ls : List Level} (hh : (appsSpineA N).1 = .const r ls)
    {m : CheckedMemberA} (hm : E.members r = some m) (hind : m.mclass = .inductiveM) : False :=
  h.2 (by rw [hh]; exact ⟨m, hm, hind⟩)

/-- a non-family constant head is not a shape head. -/
theorem not_isShapeHeadA_const {E : ResolvedEnvA} {r : Nat} {ls : List Level} {m : CheckedMemberA}
    (hm : E.members r = some m) (hni : m.mclass ≠ .inductiveM) :
    ¬ isShapeHeadA E (.const r ls) := fun ⟨m', hm', hind'⟩ => by
  rw [hm] at hm'
  injection hm' with hm'
  subst hm'
  exact hni hind'

/-! M1-d (vi), R-PropOutOfTower: the ELEMENTS of `sort l` are related as types at
    the height `ht l` of the sort itself when it is a Type-level sort; the
    elements of a `Prop`-level sort (`isZero l`) are related level-free, with no
    structure (`TyKA.sortP`). The former `lvlIdx` (`k − 1` for `Prop`) is struck:
    M2-e (0) measured that a Type-level pi with a propositional domain lives at
    its sort's height while the proposition's structure lived at the moving top,
    and the two never met. -/

/-- a normal form whose term relation is the typed-and-convertible triple: a
    proposition, or a type headed by neither a sort nor a pi. `StuckA` and the
    prop clause's data both land here; `EqKA.stuck` relates two such normal
    forms by conversion alone, at every height. -/
def TripleLikeA (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (N : ExprA) : Prop :=
  hStepFnA E I.fn Γ N = none ∧ (IsPropTy E I Γ N ∨ ¬ isShapeHeadA E (appsSpineA N).1)

theorem tripleLikeA_of_stuck {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {N : ExprA}
    (h : StuckA E I Γ N) : TripleLikeA E I Γ N := ⟨h.1, Or.inr h.2⟩

theorem tripleLikeA_of_prop {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {N : ExprA}
    (hn : hStepFnA E I.fn Γ N = none) (hP : IsPropTy E I Γ N) : TripleLikeA E I Γ N :=
  ⟨hn, Or.inl hP⟩

theorem tripleLikeA_not_sort {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {l : Level}
    (h : TripleLikeA E I Γ (.sort l)) : False :=
  h.2.elim (fun hP => not_isPropTy_sort _ _ _ _ hP) (fun hs => hs (by simp [appsSpineA, isShapeHeadA]))

/-- a triple-like pi is a proposition (a pi is shape-headed). -/
theorem tripleLikeA_pi_isProp {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {D C : ExprA}
    {u v : Level} (h : TripleLikeA E I Γ (.pi D u C v)) : IsPropTy E I Γ (.pi D u C v) :=
  h.2.elim id (fun hs => (hs (by simp [appsSpineA, isShapeHeadA])).elim)

end Rcic.Declarative.Ann
