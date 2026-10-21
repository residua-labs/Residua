import rcic.RcicTypedRowsWf

/-!
# ds-refute — a Π-injectivity counterexample candidate (S0, plain typed system)

The construction of `research/rcic/ds-refute/S0_SEARCH.md` §3, in Lean (self-contained:
only `RcicTypedRowsWf` / `RcicDeclarative`).

A Prop family `P` (`sort 0`) with two nullary constructors `true` (ref 1), `false`
(ref 2), and a recursor member at ref 3 with the **large** motive `M : P → Sort 3`
(constant `M := λ _. sort 2`). The ι-reducts are the *free* minor terms:
`rec M m₁ m₂ true ≡ m₁`, `rec M m₁ m₂ false ≡ m₂`.

`irr` on the major (`true ≡ false`, both `: P : sort 0`) + `app`-congruence gives
`rec M m₁ m₂ true ≡ rec M m₁ m₂ false`; `β`/`tyConv` reindex both ι steps to `sort 2`;
`trans`/`symm` glue `m₁ ≡ m₂`. With `m₁ = Π(sort 0). sort 1`, `m₂ = Π(sort 1). sort 0`
(both `: sort 2`):

  `TyConvT (Π(sort 0). sort 1) (Π(sort 1). sort 0)`,

the domains `sort 0` and `sort 1` being non-convertible. This is the Loop-clique
escaping shape (§2): the reduct's domain is a *free* minor, not the recursive call.

Refuted (S0_SEARCH §4.1): `TypedRowsWf` at this environment — `piRow` yields
`TyConvT (sort 0) (sort 1)`, `sortRow` yields `eqN 0 1`, contradiction (R-arity
conjunction shape). Axiom-free (`#print axioms` clean).
-/

namespace Rcic.Declarative

/-! ## a self-contained two-constructor Prop and its large-motive recursor -/

abbrev L1 : Level := .succ .zero
abbrev L2 : Level := .succ (.succ .zero)
abbrev L3 : Level := .succ (.succ (.succ .zero))

def bP : Expr Nat := .const 0 []
def bTrue : Expr Nat := .const 1 []
def bFalse : Expr Nat := .const 2 []

def bFamMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def bTrueMember : CheckedMember := ⟨.constructorM, 0, bP, none⟩
def bFalseMember : CheckedMember := ⟨.constructorM, 0, bP, none⟩

/-- `(M : P → Sort 3) → M true → M false → (p : P) → M p`. -/
def bRecType : Expr Nat :=
  .pi (.pi bP (.sort L3))
    (.pi (.app (.bvar 0) bTrue)
      (.pi (.app (.bvar 1) bFalse)
        (.pi bP (.app (.bvar 3) (.bvar 0)))))

def bRecMember : CheckedMember := ⟨.recursorM, 0, bRecType, none⟩

def bPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 bFamMember) 1 bTrueMember) 2 bFalseMember

def bEnv : ResolvedEnv := extendEnv bPrefix 3 bRecMember

/-- the constant motive `λ (_ : P). sort 2` (`: P → Sort 3`). -/
def bMotive : Expr Nat := .lam bP (.sort L2)

/-- `Π (sort 0). sort 1` — a type of sort 2 (domain `sort 0`). -/
def bMinorA : Expr Nat := .pi (.sort .zero) (.sort L1)

/-- `Π (sort 1). sort 0` — a type of sort 2 (domain `sort 1`). -/
def bMinorB : Expr Nat := .pi (.sort L1) (.sort .zero)

def bRecDoms : List (Expr Nat) :=
  [.pi bP (.sort L3), .app (.bvar 0) bTrue, .app (.bvar 1) bFalse, bP]

/-- witness for `true` (ctorIdx `0`, minor `bMinorA`). -/
def wTrue : IotaWitness bEnv where
  recRef := 3
  ctorRef := 1
  ls := []
  lsC := []
  recMember := bRecMember
  ctorMember := bTrueMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [bMotive, bMinorA, bMinorB]
  fields := []
  ctorParams := []
  kinds := []
  minor := bMinorA
  hlen := rfl
  familyRef := 0
  famMember := bFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := []
  ctorResult := bP
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := bRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := bP
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- witness for `false` (ctorIdx `1`, minor `bMinorB`). -/
def wFalse : IotaWitness bEnv where
  recRef := 3
  ctorRef := 2
  ls := []
  lsC := []
  recMember := bRecMember
  ctorMember := bFalseMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [bMotive, bMinorA, bMinorB]
  fields := []
  ctorParams := []
  kinds := []
  minor := bMinorB
  hlen := rfl
  familyRef := 0
  famMember := bFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := []
  ctorResult := bP
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := bRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := bP
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `0 ≠ₙ 1` (self-contained; `eval` at the empty valuation is `some 0` vs `some 1`). -/
theorem bEqN_zero_one_false : ¬ eqN .zero L1 := by
  intro h
  have hv : (some 0 : Option Nat) = some 1 := h (fun _ => none)
  exact Nat.noConfusion (Option.some.inj hv)

/-! ## the conversion `bMinorA ≡ bMinorB` at `sort 2` -/

section Conv

variable {n : Nat}

/-- `imax 1 2 =ₙ 2`. -/
theorem bImax12 : eqN (.imax L1 L2) L2 := by intro _ρ; rfl
/-- `imax 2 1 =ₙ 2`. -/
theorem bImax21 : eqN (.imax L2 L1) L2 := by intro _ρ; rfl

def hP : HasTyT bEnv n [] bP (.sort .zero) := .const [] 0 [] bFamMember rfl rfl (by rfl)
def hTrue : HasTyT bEnv n [] bTrue bP := .const [] 1 [] bTrueMember rfl rfl (by rfl)
def hFalse : HasTyT bEnv n [] bFalse bP := .const [] 2 [] bFalseMember rfl rfl (by rfl)
def hRecC : HasTyT bEnv n [] (.const 3 []) bRecType := .const [] 3 [] bRecMember rfl rfl (by rfl)

/-- `λ (_ : P). sort 2 : P → Sort 3`. -/
def hMotive : HasTyT bEnv n [] bMotive (.pi bP (.sort L3)) :=
  .lam [] bP .zero (.sort L2) (.sort L3) hP (.sort [.assumption bP] L2)

/-! ### `bMinorA : app bMotive bTrue` (and `bMinorB : app bMotive bFalse`) -/

def hSortA : HasTyT bEnv n [] bMinorA (.sort (.imax L1 L2)) :=
  .pi [] (.sort .zero) L1 (.sort L1) L2 (.sort [] .zero) (.sort [.assumption (.sort .zero)] L1)
def hMinorA2 : HasTyT bEnv n [] bMinorA (.sort L2) :=
  .conv [] bMinorA (.sort (.imax L1 L2)) (.sort L2) (.succ (.imax L1 L2)) hSortA
    (.sorts [] (.imax L1 L2) L2 bImax12)
def hBetaA : ConvT bEnv n [] (.app bMotive bTrue) (.sort L2) (.sort L3) :=
  .beta [] bP (.sort L2) bTrue (.sort L3) .zero hP (.sort [.assumption bP] L2) hTrue
def hMA : HasTyT bEnv n [] bMinorA (.app bMotive bTrue) :=
  .conv [] bMinorA (.sort L2) (.app bMotive bTrue) L3 hMinorA2
    (.symm [] (.app bMotive bTrue) (.sort L2) (.sort L3) hBetaA)

def hSortB : HasTyT bEnv n [] bMinorB (.sort (.imax L2 L1)) :=
  .pi [] (.sort L1) L2 (.sort .zero) L1 (.sort [] L1) (.sort [.assumption (.sort L1)] .zero)
def hMinorB2 : HasTyT bEnv n [] bMinorB (.sort L2) :=
  .conv [] bMinorB (.sort (.imax L2 L1)) (.sort L2) (.succ (.imax L2 L1)) hSortB
    (.sorts [] (.imax L2 L1) L2 bImax21)
def hBetaB : ConvT bEnv n [] (.app bMotive bFalse) (.sort L2) (.sort L3) :=
  .beta [] bP (.sort L2) bFalse (.sort L3) .zero hP (.sort [.assumption bP] L2) hFalse
def hMB : HasTyT bEnv n [] bMinorB (.app bMotive bFalse) :=
  .conv [] bMinorB (.sort L2) (.app bMotive bFalse) L3 hMinorB2
    (.symm [] (.app bMotive bFalse) (.sort L2) (.sort L3) hBetaB)

/-! ### the recursor application `g := rec M m₁ m₂` -/

def g : Expr Nat := .app (.app (.app (.const 3 []) bMotive) bMinorA) bMinorB

def hG0 := HasTyT.app (E := bEnv) (n := n) [] (.const 3 []) bMotive _ _ hRecC hMotive
def hG1 := HasTyT.app (E := bEnv) (n := n) [] (.app (.const 3 []) bMotive) bMinorA _ _ hG0 hMA
def hG2 : HasTyT bEnv n [] g (.pi bP (.app bMotive (.bvar 0))) :=
  HasTyT.app (E := bEnv) (n := n) [] (.app (.app (.const 3 []) bMotive) bMinorA) bMinorB _ _ hG1 hMB

def hGTrue : HasTyT bEnv n [] (.app g bTrue) (.app bMotive bTrue) :=
  HasTyT.app (E := bEnv) (n := n) [] g bTrue _ _ hG2 hTrue
def hGFalse : HasTyT bEnv n [] (.app g bFalse) (.app bMotive bFalse) :=
  HasTyT.app (E := bEnv) (n := n) [] g bFalse _ _ hG2 hFalse

/-! ### the steps: `irr` + `app`-congruence + two `iota`s -/

def hIrr : ConvT bEnv n [] bTrue bFalse bP := .irr [] bP bTrue bFalse hP hTrue hFalse

def hAp : ConvT bEnv n [] (.app g bTrue) (.app g bFalse) (.app bMotive bTrue) :=
  .app [] g g bTrue bFalse bP (.app bMotive (.bvar 0))
    (.refl [] g (.pi bP (.app bMotive (.bvar 0))) hG2) hIrr

def hIotaTrue : ConvT bEnv n [] (.app g bTrue) bMinorA (.app bMotive bTrue) :=
  .iota [] (.app g bTrue) bMinorA (.app bMotive bTrue) (DerivedIota.of wTrue) hGTrue hMA
def hIotaFalse : ConvT bEnv n [] (.app g bFalse) bMinorB (.app bMotive bFalse) :=
  .iota [] (.app g bFalse) bMinorB (.app bMotive bFalse) (DerivedIota.of wFalse) hGFalse hMB

/-- reindex the three steps to `sort 2`. -/
def hAp_r : ConvT bEnv n [] (.app g bTrue) (.app g bFalse) (.sort L2) :=
  .tyConv [] (.app g bTrue) (.app g bFalse) (.app bMotive bTrue) (.sort L2) L3 hAp hBetaA
def hIotaTrue_r : ConvT bEnv n [] (.app g bTrue) bMinorA (.sort L2) :=
  .tyConv [] (.app g bTrue) bMinorA (.app bMotive bTrue) (.sort L2) L3 hIotaTrue hBetaA
def hIotaFalse_r : ConvT bEnv n [] (.app g bFalse) bMinorB (.sort L2) :=
  .tyConv [] (.app g bFalse) bMinorB (.app bMotive bFalse) (.sort L2) L3 hIotaFalse hBetaB

/-- `Π(sort 0). sort 1 ≡ Π(sort 1). sort 0` at `sort 2`. -/
def bConv : ConvT bEnv n [] bMinorA bMinorB (.sort L2) :=
  .trans [] bMinorA (.app g bTrue) bMinorB (.sort L2)
    (.symm [] (.app g bTrue) bMinorA (.sort L2) hIotaTrue_r)
    (.trans [] (.app g bTrue) (.app g bFalse) bMinorB (.sort L2) hAp_r hIotaFalse_r)

/-- the type-level conversion. -/
def bTyConv : TyConvT bEnv n [] bMinorA bMinorB := TyConvT.of [] bMinorA bMinorB L2 bConv

end Conv

/-- **Π-injectivity fails at `bEnv`.** `TypedRowsWf`'s `piRow` reads `bTyConv` and
    returns `TyConvT (sort 0) (sort 1)`; its `sortRow` turns that into `eqN 0 1`. -/
theorem bEnv_typedRowsWf_false {n : Nat} (R : TypedRowsWf bEnv n) : False := by
  obtain ⟨hd⟩ := (R.piRow CtxWfT.nil bTyConv).1
  exact bEqN_zero_one_false (R.sortRow CtxWfT.nil hd)

#print axioms bEnv_typedRowsWf_false

end Rcic.Declarative
