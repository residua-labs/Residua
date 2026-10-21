import rcic.RcicAnnViewTy
import rcic.RcicAnnEnvBridgeGroup

/-!
# Arc D — the semantic-prefix settlement

`CtorTyOfViewA` and `RecTyOfViewsA` stay as `#6165` measured them. They are not proved here.
`ctorTyOfViewSemA_holds` and `recTyOfViewsSemA_holds` prove the semantic-prefix statements:
the same quantifiers and premises, plus the base's `EnvSemA` at `iotaIfaceA E`, `PosValA`,
and agreement with the conclusion's interface.

The mirror walk's `eqN l' up` is sort uniqueness. Both sort typings, and the context that
carries them, move from the conclusion's interface onto `iotaIfaceA E` by `hasTyIfaceA` and
`ctxWfIfaceA`. `sortUniqA` then runs at `iotaFnA_lift hE`, `iotaFnA_subst hE` and
`iotaFnA_recHead E`. The walkers are `#6165`'s, with that uniqueness as a premise
(`ctorViewA_hasTy_ofUniq`, `groupRecTypeA_hasTy_ofUniq`). The public conditional theorems
still ask for `EnvSemA` at the conclusion's interface; there is no transport of `EnvSemA`
along agreement, so these holds do not call them.

The four closed rows feed the holds to `envBridgeSem`. They are not proofs of the original
universal contract.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- a context moves with the typings it stores. Not mutual with `hasTyIfaceA`: that transport
    is already defined. -/
def ctxWfIfaceA {E : ResolvedEnvA} {n : Nat} {I J : IotaIfaceA}
    (hag : IfaceAgreeA E I J) : {Γ : LCtxA} → CtxWfA E I n Γ → CtxWfA E J n Γ
  | _, .nil => .nil
  | _, .assumption hΓ hA => .assumption (ctxWfIfaceA hag hΓ) (hasTyIfaceA hag hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (ctxWfIfaceA hag hΓ) (hasTyIfaceA hag hA) (hasTyIfaceA hag hv)

/-- sort uniqueness at the conclusion's interface, paid at the base's own ι. -/
theorem viewTySortUniq_iota {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hN : EnvNormClosedA E) (hNC : EnvNormCtorTypeA E)
    (hSem : EnvSemA E (iotaIfaceA E) n ρ₀)
    (hρ : PosValA ρ₀)
    (hag : IfaceAgreeA E (iotaIfaceA E) I) : ViewTySortUniqA E I n := by
  intro Γ X a b hΓ ha hb
  exact sortUniqA hE (iotaFnA_lift hE hN) (iotaFnA_subst hE hN) hNC hN (iotaFnA_recHead E) hSem hρ
    (ctxWfIfaceA (IfaceAgreeA.symm hag) hΓ)
    (hasTyIfaceA (IfaceAgreeA.symm hag) ha)
    (hasTyIfaceA (IfaceAgreeA.symm hag) hb)

/-- (T1) at the base's own ι. Not a proof of `CtorTyOfViewA`. -/
theorem ctorTyOfViewSemA_holds : CtorTyOfViewSemA := by
  intro E I f fm cm u hE hEx hN hNC _hEL _hELf hIl hIS _hIL hR hRx hfr _hcls hFam fv v ρ₀ hρ hSem hag
  exact ctorViewA_hasTy_ofUniq (E := E) (I := I) (f := f) (fm := fm) (cm := cm) (fv := fv)
    v hFam hfr hE hEx hIl hIS hR hRx (viewTySortUniq_iota hE hN hNC hSem hρ hag)

/-- (T2) at the base's own ι. The intermediate `extendEnvA` recursor-head premise is the
    contract's; the walker does not read it. Not a proof of `RecTyOfViewsA`. -/
theorem recTyOfViewsSemA_holds : RecTyOfViewsSemA := by
  intro E I f fm u fv cs elim hE hG hN hNC _hEL _hELg hIl hIS _hIL hR _hRx hRG hfresh _hcls hFam ρ₀ hρ
    hSem hag
  exact groupRecTypeA_hasTy_ofUniq (E := E) (I := I) (f := f) (fm := fm) (fv := fv)
    (cs := cs) (elim := elim) hFam hfresh hE hG hIl hIS hR hRG
    (viewTySortUniq_iota hE hN hNC hSem hρ hag)

/-- every in-scope `EnvWfT` environment is the erasure of one the copy admits, from the
    semantic prefix. No (T1) or (T2) hypothesis. -/
theorem annEnvA_of_envWfT_semPrefix {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ AnnEnvA EA ∧ EnvNormEraseA EA := by
  obtain ⟨EA, hE, hsm, hpo, hnf, hn, hWA⟩ :=
    envBridgeSem ctorTyOfViewSemA_holds recTyOfViewsSemA_holds hW hP
  exact ⟨EA, hE, ⟨hWA _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩, hn⟩

/-- ROW 1 over `EnvWfT` in the copy's scope, from the semantic prefix. -/
theorem sortConvCharT_semPrefix {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level}
    {T : Expr Nat} (h : ConvT E n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact sortConvCharT' C hn hΓ h

/-- ROW 2 over `EnvWfT` in the copy's scope, from the semantic prefix. -/
theorem piConvInjT_semPrefix {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' T : Expr Nat} (h : ConvT E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact piConvInjT' C hn hΓ h

/-- ROW 3 over `EnvWfT` in the copy's scope, from the semantic prefix. -/
theorem famAppConvInjT_semPrefix {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat}
    {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (h : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧ ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  rw [members_eraseEnv] at hm
  cases hmA : EA.members r with
  | none => rw [hmA] at hm; exact Option.noConfusion hm
  | some mA =>
      rw [hmA] at hm
      cases hm
      obtain ⟨hWA⟩ := C.wf
      obtain ⟨u₀, hsh⟩ := envWfA_famShape hWA r mA hmA hind
      exact famAppConvInjT_any' C hn hΓ hmA hind hsh h

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.ctorTyOfViewSemA_holds
#print axioms Rcic.Declarative.Ann.recTyOfViewsSemA_holds
#print axioms Rcic.Declarative.Ann.annEnvA_of_envWfT_semPrefix
#print axioms Rcic.Declarative.Ann.sortConvCharT_semPrefix
#print axioms Rcic.Declarative.Ann.piConvInjT_semPrefix
#print axioms Rcic.Declarative.Ann.famAppConvInjT_semPrefix
