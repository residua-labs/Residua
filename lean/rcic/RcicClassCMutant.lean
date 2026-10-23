import rcic.RcicTypedRowsWf
import rcic.RcicInductivePolicy

/-!
# cc-classc tooth — one elimination more, and the rows fail

The adversarial boundary, kernel-checked. Over a NON-admitted environment, a two-constructor
`Prop` `BP` (`tt ff : BP`) carries a recursor `rec.{u}` into every `Sort u`, i.e. the `AnySort`
policy that 05 §10 refuses (`multipleProp`). `ConvT` is defined over any environment, so its
derivations exist there:

* `mutCollapse`: for any closed sort `T = Sort k` and any `p q : T`, `p ≡ q : T`. The chain is
  `p ≡ι rec M p q tt ≡(irr tt ≡ ff) rec M p q ff ≡ι q`, with the constant motive `M := λ _. T`.
* collapse at `Sort 1`: `Π (x : Sort 0), Sort 0 ≡ Sort 0`. So the family `J : Π (x : Sort 0),
  Sort 0` is itself typed at `Sort 0` (`mutJProp`).
* collapse at `Sort 0`: `J BP ≡ J`, two applications of one family with argument lists of lengths 1
  and 0.
* `mutant_not_typedRowsWf`: famAppRow's `xs.length = xs'.length` clause refutes `TypedRowsWf`.

`mutant_selection_refused` is the admission rule that blocks it: `EliminationSelection` never gives
a two-constructor `Prop` `AnySort` (`anySort_iff`). This is Lean's rule, not a narrowing. So the
rows sit exactly at 05 §10's boundary: class (c) is what that rule lets through, and A1 of
`research/rcic/classc/CLASSC_CEX.md` is this file. `closure_claim = 0`.
-/

namespace Rcic.Syn.ClassC.Mutant

open Rcic.Declarative

/-! ## §1 the mutant environment (not admitted) -/

def bpFam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def bpTt : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩
def bpFf : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩
/-- `Π (M : BP → Sort u) (a : M tt) (b : M ff) (t : BP), M t` — the refused `AnySort` recursor. -/
def bpRecTy : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0)))
    (.pi (.app (.bvar 0) (.const 1 []))
      (.pi (.app (.bvar 1) (.const 2 []))
        (.pi (.const 0 []) (.app (.bvar 3) (.bvar 0)))))
def bpRec : CheckedMember := ⟨.recursorM, 1, bpRecTy, none⟩
/-- an unrelated one-index family `J : Π (x : Sort 0), Sort 0`. -/
def jFam : CheckedMember := ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩

def mutEnv : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv (extendEnv (extendEnv emptyEnv 0 bpFam) 1 bpTt) 2 bpFf)
    3 bpRec) 4 jFam

/-- the refused policy: a two-constructor `Prop` never selects `AnySort`. -/
theorem mutant_selection_refused (safe : Prop) :
    ¬ EliminationSelection .zero 2 safe .anySort := by
  intro h
  rcases (EliminationSelection.anySort_iff .zero 2 safe).mp h with ht | ⟨_, hk | ⟨hk, _⟩⟩
  · exact absurd (ht (fun _ => 0)) (by decide)
  · cases hk
  · cases hk

/-! ## §2 the ι witnesses at `tt` and `ff` -/

def bpW (ctorIdx : Nat) (hidx : ctorIdx < 2) (k : Level) (M p q : Expr Nat) :
    IotaWitness mutEnv where
  recRef := 3
  ctorRef := 1 + ctorIdx
  ls := [k]
  lsC := []
  recMember := bpRec
  ctorMember := ⟨.constructorM, 0, .const 0 [], none⟩
  hrec := rfl
  hctor := by
    rcases ctorIdx with _ | _ | c
    · rfl
    · rfl
    · exact (Nat.not_lt_zero c (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hidx))).elim
  hrecK := rfl
  hctorK := rfl
  preMajor := [M, p, q]
  fields := []
  ctorParams := []
  kinds := []
  minor := [M, p, q][1 + ctorIdx]'(Nat.add_lt_add_left hidx 1)
  hlen := rfl
  familyRef := 0
  famMember := bpFam
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := ctorIdx
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := hidx
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := by
    show [M, p, q][1 + ctorIdx]? = _
    exact List.getElem?_eq_getElem (l := [M, p, q]) (Nat.add_lt_add_left hidx 1)
  ctorDoms := []
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 0 []) (.sort (.param 0)), .app (.bvar 0) (.const 1 []),
    .app (.bvar 1) (.const 2 []), .const 0 []]
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 0 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-! ## §3 the collapse at a closed sort -/

section collapse

variable (k : Level) (p q : Expr Nat)

/-- the constant motive `λ (_ : BP). Sort k`. -/
def motK : Expr Nat := .lam (.const 0 []) (.sort k)

def recCallK (t : Expr Nat) : Expr Nat :=
  foldApps (.const 3 [.succ k]) [motK k, p, q, t]

def hBP : HasTyT mutEnv 0 [] (.const 0 []) (.sort .zero) := .const _ 0 [] bpFam rfl rfl rfl
def hTt : HasTyT mutEnv 0 [] (.const 1 []) (.const 0 []) := .const _ 1 [] bpTt rfl rfl rfl
def hFf : HasTyT mutEnv 0 [] (.const 2 []) (.const 0 []) := .const _ 2 [] bpFf rfl rfl rfl

def hMot : HasTyT mutEnv 0 [] (motK k) (.pi (.const 0 []) (.sort (.succ k))) :=
  .lam _ _ .zero _ _ hBP (.sort _ k)

/-- `(λ _. Sort k) t ≡ Sort k`. -/
def betaK {t : Expr Nat} (ht : HasTyT mutEnv 0 [] t (.const 0 [])) :
    ConvT mutEnv 0 [] (.app (motK k) t) (.sort k) (.sort (.succ k)) :=
  .beta _ (.const 0 []) (.sort k) t (.sort (.succ k)) .zero hBP (.sort _ k) ht

variable {k p q}

def hRec0 (hk : levelsBounded 0 [.succ k] = true) :
    HasTyT mutEnv 0 [] (.const 3 [.succ k]) (instantiateLevels [.succ k] bpRecTy) :=
  .const _ 3 [.succ k] bpRec rfl rfl hk

/-- `rec M p q : Π (t : BP), M t`. -/
def hRecPQ (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k)) :
    HasTyT mutEnv 0 [] (foldApps (.const 3 [.succ k]) [motK k, p, q])
      (.pi (.const 0 []) (.app (motK k) (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _ (hRec0 hk) (hMot k))
      (.conv _ _ _ _ _ hp (.symm _ _ _ _ (betaK k hTt))))
    (.conv _ _ _ _ _ hq (.symm _ _ _ _ (betaK k hFf)))

def hRecAt (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k))
    {t : Expr Nat} (ht : HasTyT mutEnv 0 [] t (.const 0 [])) :
    HasTyT mutEnv 0 [] (recCallK k p q t) (.app (motK k) t) :=
  .app _ _ _ _ _ (hRecPQ hk hp hq) ht

/-- ι at `tt`: `rec M p q tt ≡ p`. -/
def iotaTt (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k)) :
    ConvT mutEnv 0 [] (recCallK k p q (.const 1 [])) p (.app (motK k) (.const 1 [])) :=
  .iota _ _ _ _ (.of (bpW 0 (by decide) (.succ k) (motK k) p q)) (hRecAt hk hp hq hTt)
    (.conv _ _ _ _ _ hp (.symm _ _ _ _ (betaK k hTt)))

/-- ι at `ff`: `rec M p q ff ≡ q`. -/
def iotaFf (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k)) :
    ConvT mutEnv 0 [] (recCallK k p q (.const 2 [])) q (.app (motK k) (.const 2 [])) :=
  .iota _ _ _ _ (.of (bpW 1 (by decide) (.succ k) (motK k) p q)) (hRecAt hk hp hq hFf)
    (.conv _ _ _ _ _ hq (.symm _ _ _ _ (betaK k hFf)))

/-- `irr tt ≡ ff : BP` under `app`: `rec M p q tt ≡ rec M p q ff`. -/
def congTtFf (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k)) :
    ConvT mutEnv 0 [] (recCallK k p q (.const 1 [])) (recCallK k p q (.const 2 []))
      (.app (motK k) (.const 1 [])) :=
  .app _ _ _ _ _ _ _ (.refl _ _ _ (hRecPQ hk hp hq)) (.irr _ _ _ _ hBP hTt hFf)

/-- `M ff ≡ M tt : Sort (k+1)`. -/
def motFfTt : ConvT mutEnv 0 [] (.app (motK k) (.const 2 [])) (.app (motK k) (.const 1 []))
    (.sort (.succ k)) :=
  .trans _ _ _ _ _ (betaK k hFf) (.symm _ _ _ _ (betaK k hTt))

/-- **the collapse**: any two inhabitants of a closed sort are convertible. -/
def mutCollapse (hk : levelsBounded 0 [.succ k] = true) (hp : HasTyT mutEnv 0 [] p (.sort k))
    (hq : HasTyT mutEnv 0 [] q (.sort k)) :
    ConvT mutEnv 0 [] p q (.sort k) :=
  .tyConv _ _ _ _ _ (.succ k)
    (.trans _ _ _ _ _ (.symm _ _ _ _ (iotaTt hk hp hq))
      (.trans _ _ _ _ _ (congTtFf hk hp hq)
        (.tyConv _ _ _ _ _ (.succ k) (iotaFf hk hp hq) motFfTt)))
    (betaK k hTt)

end collapse

/-! ## §4 from the collapse to a famAppRow failure -/

def piS0S0 : Expr Nat := .pi (.sort .zero) (.sort .zero)

theorem eqN_imax_one_one : eqN (.imax (.succ .zero) (.succ .zero)) (.succ .zero) := fun _ => rfl

def hPiS0S0 : HasTyT mutEnv 0 [] piS0S0 (.sort (.succ .zero)) :=
  .conv _ _ _ _ _
    (.pi _ _ _ _ _ (.sort _ _) (.sort _ _))
    (.sorts _ _ _ eqN_imax_one_one)

/-- `Π (x : Sort 0), Sort 0 ≡ Sort 0 : Sort 1`. -/
def collapseS1 : ConvT mutEnv 0 [] piS0S0 (.sort .zero) (.sort (.succ .zero)) :=
  mutCollapse rfl hPiS0S0 (.sort _ _)

/-- the family `J` typed at `Sort 0`. -/
def mutJProp : HasTyT mutEnv 0 [] (.const 4 []) (.sort .zero) :=
  .conv _ _ _ _ _ (.const _ 4 [] jFam rfl rfl rfl) collapseS1

def hJBP : HasTyT mutEnv 0 [] (.app (.const 4 []) (.const 0 [])) (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 4 [] jFam rfl rfl rfl) hBP

/-- `J BP ≡ J : Sort 0`. -/
def collapseJ : ConvT mutEnv 0 [] (.app (.const 4 []) (.const 0 [])) (.const 4 []) (.sort .zero) :=
  mutCollapse rfl hJBP mutJProp

/-- **The rows fail one elimination past 05 §10.** -/
theorem mutant_not_typedRowsWf : ¬ TypedRowsWf mutEnv 0 := by
  intro hR
  have h := hR.famAppRow (Γ := []) .nil (r := 4) (m := jFam) (ls := []) (ls' := [])
    (xs := [.const 0 []]) (xs' := []) rfl rfl hJBP (.of _ _ _ _ collapseJ)
  exact absurd h.2.1 (by decide)

end Rcic.Syn.ClassC.Mutant

#print axioms Rcic.Syn.ClassC.Mutant.mutant_selection_refused
#print axioms Rcic.Syn.ClassC.Mutant.mutCollapse
#print axioms Rcic.Syn.ClassC.Mutant.mutant_not_typedRowsWf
