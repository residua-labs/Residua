import rcic.RcicF8StructPiRequests
import rcic.RcicF8EvPar

/-!
SP-1: the two staged P requests feed the single owner-side structPi producer.
Their answers and support contracts are explicit inputs. Neither P nor U/X
is supplied here. Source is the original PEqT.pi leaf; output is the canonical
structural pi step, NOT asserted equal to that original peq proof object.
closure_claim=0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.SP1
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B A' B' T : Expr Nat}

/-- Re-index the ORIGINAL right endpoint lazily via the original left inversion
chain. No generated typing is admitted as a literal. -/
def payload (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v)) :
    StructPiPayload p.removed Γ A B A' B' T where
  u := p.leftView.u
  v := p.leftView.v
  hA := p.leftView.hA
  hc := dom
  hB := p.leftView.hB
  hcB := cod
  hrt := .rety p.rightOriginal (.symm p.leftView.hc)
  idx := p.leftView.hc

theorem payload_strict (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (hdom : Supported dom.leaves (domainRequest p).leaves)
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v))
    (hcod : Supported cod.leaves (codomainRequest p dom).leaves)
    (x : Jd E n) (hx : x ∈ (payload p dom cod).leaves) :
    SubOf x (.pr p.source) := by
  simp only [StructPiPayload.leaves, payload, EvTy.leaves, EvTc.leaves] at hx
  rcases List.mem_append.mp hx with hx | hi
  · rcases List.mem_append.mp hx with hx | hrt
    · rcases List.mem_append.mp hx with hx | hc
      · rcases List.mem_append.mp hx with hx | hb
        · rcases List.mem_append.mp hx with ha | hd
          · apply p.leftView_strict x
            simp only [EvInvPi.leaves, List.mem_append]
            exact .inl (.inl ha)
          · exact supported_strict hdom (domainRequest_strict p) x hd
        · apply p.leftView_strict x
          simp only [EvInvPi.leaves, List.mem_append]
          exact .inl (.inr hb)
      · exact supported_strict hcod (codomainRequest_strict p dom hdom) x hc
    · rcases List.mem_append.mp hrt with hr | hi
      · have he : x = .ty p.rightTy := List.mem_singleton.mp hr
        subst x; exact .child p.right_child
      · apply p.leftView_strict x
        simp only [EvInvPi.leaves, List.mem_append]
        exact .inr hi
  · apply p.leftView_strict x
    simp only [EvInvPi.leaves, List.mem_append]
    exact .inr hi

def emitted (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v)) :
    EvPar p.removed Γ (.pi A B) (.pi A' B') T :=
  .structPi (payload p dom cod)

theorem emitted_exact (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v))
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (emitted p dom cod).val hcl hinst =
      structPiStep (p.leftView.hA.val hcl hinst) (dom.val hcl hinst)
        (p.leftView.hB.val hcl hinst) (cod.val hcl hinst)
        (hasTyT_of_tyConvT p.rightTy (p.leftView.hc.val hcl hinst).symmT)
        (p.leftView.hc.val hcl hinst) := rfl

/-- Canonical producer proof object is intentionally NOT the original PEq leaf. -/
theorem emitted_not_input (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v))
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (emitted p dom cod).val hcl hinst ≠ p.source := by
  intro h
  cases h

/-- Current Occ counts ParRedT/raw-PEq positions, not hidden future J translations.
    The canonical pi arm emits no such position; component replies remain data. -/
def emittedTile (hW : EnvWfT E) (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v)) :
    DTile p.removed where
  X := p.removed
  step := (emitted p dom cod).val (envClosed_of_envWfT hW) (envWfT_subst_inst hW)
  status := fun o _ => nomatch o
  om2 := fun o _ => nomatch o

theorem emittedTile_exact (hW : EnvWfT E) (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v)) :
    (emittedTile hW p dom cod).step =
      (emitted p dom cod).val (envClosed_of_envWfT hW) (envWfT_subst_inst hW) := rfl

theorem emitted_edge (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (hdom : Supported dom.leaves (domainRequest p).leaves)
    (cod : EvCv p.removed (.assumption A :: Γ) B B' (.sort p.leftView.v))
    (hcod : Supported cod.leaves (codomainRequest p dom).leaves)
    (Z : List (Jd E n)) :
    OM3_edge (p.removed ++ Z) ((emitted p dom cod).leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun x hx => ⟨_, .head _, payload_strict p dom hdom cod hcod x hx⟩)

/-- The binder contexts are constructed from the ORIGINAL endpoint inversions. -/
def leftContext (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (p : Input E n Γ A B A' B' T) : CtxWfT E n (.assumption A :: Γ) :=
  .assumption Γ A p.leftView.u hΓ
    (p.leftView.hA.val (envClosed_of_envWfT hW) (envWfT_subst_inst hW))

def rightContext (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (p : Input E n Γ A B A' B' T) : CtxWfT E n (.assumption A' :: Γ) :=
  .assumption Γ A' p.rightView.u hΓ
    (p.rightView.hA.val (envClosed_of_envWfT hW) (envWfT_subst_inst hW))

/-- Staged consumer of the NAMED P suppliers; neither is an instance or default. -/
def withP (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) (p : Input E n Γ A B A' B' T)
    (P : PAtSort p.removed) (PB : PAtBinder p.removed) : DTile p.removed :=
  let dom := P hW hΓ (domainRequest p)
  emittedTile hW p dom
    (PB hW (leftContext hW hΓ p) (rightContext hW hΓ p) (codomainRequest p dom))

theorem withP_edge (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (p : Input E n Γ A B A' B' T)
    (P : PAtSort p.removed) (hP : PAtSortContract P)
    (PB : PAtBinder p.removed) (hPB : PAtBinderContract PB)
    (Z : List (Jd E n)) :
    let dom := P hW hΓ (domainRequest p)
    let cod := PB hW (leftContext hW hΓ p) (rightContext hW hΓ p) (codomainRequest p dom)
    OM3_edge (p.removed ++ Z) ((emitted p dom cod).leaves ++ Z) :=
  emitted_edge p _ (hP hW hΓ _) _ (hPB hW _ _ _) Z

end Rcic.Declarative.F8Measure.SP1

#print axioms Rcic.Declarative.F8Measure.SP1.payload
#print axioms Rcic.Declarative.F8Measure.SP1.payload_strict
#print axioms Rcic.Declarative.F8Measure.SP1.emitted
#print axioms Rcic.Declarative.F8Measure.SP1.emitted_exact
#print axioms Rcic.Declarative.F8Measure.SP1.emitted_not_input
#print axioms Rcic.Declarative.F8Measure.SP1.emittedTile
#print axioms Rcic.Declarative.F8Measure.SP1.emittedTile_exact
#print axioms Rcic.Declarative.F8Measure.SP1.emitted_edge
#print axioms Rcic.Declarative.F8Measure.SP1.leftContext
#print axioms Rcic.Declarative.F8Measure.SP1.rightContext
#print axioms Rcic.Declarative.F8Measure.SP1.withP
#print axioms Rcic.Declarative.F8Measure.SP1.withP_edge
