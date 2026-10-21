import rcic.RcicF8StructPiExtract

/-! SP-1 actual leaf entry; the named SortUnique premise is not an instance.
The structural case preserves the exact input proof object and both endpoint
fields. No theorem in this module claims the whole ParRedT Pi inversion.
closure_claim = 0. -/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.SP1
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B A' B' T : Expr Nat}

/-- Only the raw proof-root alternative needs sort separation. -/
def inputOfLeaf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ)
    (leaf : PEqLeafT E n Γ (.pi A B) (.pi A' B') T) :
    Input E n Γ A B A' B' T := by
  rcases leaf with ⟨raw, hL, hR⟩
  cases raw with
  | pi _ _ _ _ _ hd hb => exact ⟨hd, hb, hL, hR⟩
  | proof _ _ _ P Q hP hQ hp hq =>
      exact False.elim (piProofRoot_false hW su hΓ hP hp)

theorem inputOfLeaf_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ)
    (leaf : PEqLeafT E n Γ (.pi A B) (.pi A' B') T) :
    (inputOfLeaf hW su hΓ leaf).source =
      ParRedT.peq Γ (.pi A B) (.pi A' B') T leaf := by
  rcases leaf with ⟨raw, hL, hR⟩
  cases raw with
  | pi _ _ _ _ _ hd hb => rfl
  | proof _ _ _ P Q hP hQ hp hq =>
      exact False.elim (piProofRoot_false hW su hΓ hP hp)

theorem Input.original_typings_exact (p : Input E n Γ A B A' B' T)
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    p.leftOriginal.val hcl hinst = p.leftTy ∧
      p.rightOriginal.val hcl hinst = p.rightTy := ⟨rfl, rfl⟩

/-- The result stays tied to the raw LEFT binder, while the stored right
seed stays tied to the original RIGHT binder until the domain reply arrives. -/
theorem codomain_indices_exact (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u)) :
    (codomainRequest p dom).raw = p.codRaw ∧
    (codomainRequest p dom).domain = dom ∧
    (codomainRequest p dom).right = p.rightView.hB := ⟨rfl, rfl, rfl⟩

/-- Binder materialization does not normalize/reindex the right body's sort. -/
theorem codomain_materializes_left (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (codomainRequest p dom).rightAligned hcl hinst =
      hasTyTConvAssump hcl (dom.val hcl hinst) (p.rightView.hB.val hcl hinst) := rfl

end Rcic.Declarative.F8Measure.SP1

#print axioms Rcic.Declarative.F8Measure.SP1.inputOfLeaf
#print axioms Rcic.Declarative.F8Measure.SP1.inputOfLeaf_exact
#print axioms Rcic.Declarative.F8Measure.SP1.Input.original_typings_exact
#print axioms Rcic.Declarative.F8Measure.SP1.codomain_indices_exact
#print axioms Rcic.Declarative.F8Measure.SP1.codomain_materializes_left
