import rcic.RcicAnnSortUniq

/-!
# M2-g′ (e) — row (3) without `hw`

`famAppConvInjA` asks that the family's declared sort be Type-level (`hz`).
`famAppConvInjA_prop` asks that the conversion's sort be `Prop`-level (`hw`).
Neither fact is an assumption here. A full application of the family is typed at
`sort (instLevel ls u₀)`, read off the conversion's left end and the family's
stored type by walking the spine (`famSpine_canonA`, `famApp_declaredSortA`). A
shorter application would convert a pi to that sort, which `tyConvA_pi_sort_false`
refutes. Sort uniqueness (`sortUniqA`) identifies the conversion's sort with the
declared one, so `isZero` of the declared sort is `hw` (`famApp_propLevel_of_declared`).
The case split is only the assembly (`famAppConvInjA_any`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the declared type, from the left end and the stored type -/

section Declared
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a typing of a constant-headed spine at a large type converts from `applyTelA` of the
    member's instantiated type. One more argument than the telescope is a sort converting
    to a pi (`tyConvA_pi_sort_false`); each pi crossed is Type-level (`codom_typeLevel`),
    so `tyConvA_pi_inj` moves the instance onto the stored codomain. -/
theorem famSpine_canonA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {r : Nat} {m : CheckedMemberA} {ls : List Level} {u₀ : Level}
    (hm : E.members r = some m) (hsh : piBodyA m.mtypeA = .sort u₀) (xs : List ExprA) :
    ∀ {T : ExprA}, HasTyA E I n Γ (foldAppsA (.const r ls) xs) T → LargeA E I n Γ T →
      ∃ R, applyTelA xs (instantiateLevelsA ls m.mtypeA) = some R ∧
        Nonempty (TyConvA E I n Γ R T) := by
  refine snocInduction
    (P := fun xs => ∀ {T : ExprA}, HasTyA E I n Γ (foldAppsA (.const r ls) xs) T →
      LargeA E I n Γ T →
      ∃ R, applyTelA xs (instantiateLevelsA ls m.mtypeA) = some R ∧
        Nonempty (TyConvA E I n Γ R T)) ?nil ?snoc xs
  · intro T hT _
    obtain ⟨m', hm', ⟨t⟩⟩ := hasTyA_const_gen hT
    rw [hm] at hm'
    cases hm'
    exact ⟨instantiateLevelsA ls m.mtypeA, rfl, ⟨t⟩⟩
  · intro ys x ih T hT hL
    rw [foldAppsA_snoc] at hT
    obtain ⟨A, u, B, v, _, ⟨hf⟩, ⟨hx⟩, ⟨hB⟩, _, ⟨t1⟩⟩ := hasTyA_app_gen hT
    have hz : isZero v = false :=
      codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB hx ⟨t1⟩ hL
    obtain ⟨R, hTel, ⟨tR⟩⟩ := ih hf (Or.inr ⟨A, u, B, v, hz, ⟨.refl _ _⟩⟩)
    have hbody : piBodyA (instantiateLevelsA ls m.mtypeA) = .sort (instLevel ls u₀) :=
      piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
    rcases applyTelA_sortBody ys (instantiateLevelsA ls m.mtypeA) hbody hTel with
      ⟨_, hsort⟩ | ⟨_, D, uD, C, vD, hpi⟩
    · subst hsort
      exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ tR.symm).elim
    · subst hpi
      obtain ⟨_, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz tR.symm
      obtain ⟨tc⟩ := hcod x hx
      exact ⟨instantiate0A x C, applyTelA_snoc ys (instantiateLevelsA ls m.mtypeA) hTel,
        ⟨.trans _ _ _ _ tc.symm t1⟩⟩

/-- THE DECLARED TYPE OF A FULL APPLICATION. The conversion types its left end at `sort w`.
    The spine walk converts that from `applyTelA` of the stored type; on a sort-bodied
    telescope the result is `sort (instLevel ls u₀)` exactly when every argument is
    consumed, and a pi otherwise, which does not convert to the sort. -/
theorem famApp_declaredSortA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA} {u₀ w : Level}
    (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    Nonempty (HasTyA E I n Γ (foldAppsA (.const r ls) xs) (.sort (instLevel ls u₀))) := by
  have hLeft : HasTyA E I n Γ (foldAppsA (.const r ls) xs) (.sort w) :=
    convA_hasTy_left hE hI hR hIS hΓ h
  obtain ⟨R, hTel, ⟨tR⟩⟩ := famSpine_canonA hE hI hIS hEN hNC hR hS hρ hΓ hm hsh xs hLeft
    (Or.inl ⟨w, ⟨.refl _ _⟩⟩)
  have hbody : piBodyA (instantiateLevelsA ls m.mtypeA) = .sort (instLevel ls u₀) :=
    piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
  rcases applyTelA_sortBody xs (instantiateLevelsA ls m.mtypeA) hbody hTel with
    ⟨_, hsort⟩ | ⟨_, _, _, _, _, hpi⟩
  · subst hsort
    exact ⟨hasTyA_of_tyConvA hLeft tR.symm⟩
  · subst hpi
    exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ tR).elim

/-- `hw`, DERIVED. The application is typed at both sorts, so they are `=ₙ`
    (`sortUniqA`); `isZero` agrees. -/
theorem famApp_propLevel_of_declared (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA} {u₀ w : Level}
    (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w))
    (hz : isZero (instLevel ls u₀) = true) : isZero w = true := by
  obtain ⟨hDecl⟩ := famApp_declaredSortA hE hI hIS hEN hNC hR hS hρ hΓ hm hsh h
  have hLeft : HasTyA E I n Γ (foldAppsA (.const r ls) xs) (.sort w) :=
    convA_hasTy_left hE hI hR hIS hΓ h
  exact (isZero_eqN (sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hDecl hLeft)).symm.trans hz

end Declared

/-! ## (2) assembly: the row, with neither `hz` nor `hw` -/

section Row3Any
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- ROW (3) AT EITHER LEVEL. The hypotheses are `famAppConvInjA`'s, minus `hz`.
    `isZero (instLevel ls u₀) = false` is `famAppConvInjA`; `= true` is `hw`, derived, and
    then `famAppConvInjA_prop`. -/
theorem famAppConvInjA_any (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA}
    {u₀ w : Level} (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs xs' := by
  cases hz : isZero (instLevel ls u₀) with
  | false => exact famAppConvInjA hE hI hIS hEN hNC hR hS hρ hΓ hm hind hsh hz h
  | true =>
      exact famAppConvInjA_prop hE hI hIS hEN hNC hR hS hρ hΓ hm hind
        (famApp_propLevel_of_declared hE hI hIS hEN hNC hR hS hρ hΓ hm hsh h hz) h

/-- `famAppConvInjA`'s hypothesis list, minus `hz`, calls the row. -/
example (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA}
    {u₀ w : Level} (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs xs' :=
  famAppConvInjA_any hE hI hIS hEN hNC hR hS hρ hΓ hm hind hsh h

end Row3Any

section Row3AnyRec
variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- ROW (3) at either level, at the concrete ι: `famAppConvInjA_any` with `EnvSemA` from
    the environment's well-formedness, as `famAppConvInjA_rec` supplies it. -/
theorem famAppConvInjA_any_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hS : SmallIndexProfileA E) (hPE : PropElimStructA E) {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA} {u₀ w : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ) (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvA E (iotaIfaceA E) n Γ (foldAppsA (.const r ls) xs)
      (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA ls m.mtypeA) xs xs' :=
  famAppConvInjA_any (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (envWfA_normCtorType hW)
    (envWfA_normClosed hW) (iotaFnA_recHead E)
    (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ hΓ hm hind hsh h

end Row3AnyRec

#print axioms famSpine_canonA
#print axioms famApp_declaredSortA
#print axioms famApp_propLevel_of_declared
#print axioms famAppConvInjA_any
#print axioms famAppConvInjA_any_rec

end Rcic.Declarative.Ann
