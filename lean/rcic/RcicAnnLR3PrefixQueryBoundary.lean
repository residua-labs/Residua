import rcic.RcicAnnLR3ReflInferenceBoundary

/-!
# A generated constructor-application query need not live in its admission prefix

The stored `Eq.refl` telescope is typed in `EqLargeFixture.prefixEnv`.
This does not put an arbitrary declarative application's *chosen* Pi carrier
there.  The witness below keeps the subject `reflAt parameter` and its final
type `domain` fixed.  Its final application uses a domain `S` obtained by an
actual computation of the later Eq recursor, with result `Prop`.

Thus the application arm's Pi query is genuinely full-environment data: its
right Pi contains reference 65, which has no typing in the prefix.  This is a
boundary for restriction of the generated query verbatim, not a refutation
of conservativity between prefix-language endpoints, of another derivation,
or of every combined descent order.  `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.PrefixQuery

open Rcic.Declarative EqLargeFixture

private def applyHere {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) := by
  have hp := hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface hΓ hf).2
  exact .app Γ f a D C u v v hp.2
    (hasTyA_inst0 closed liftIface (iotaRecHeadTypedA_of (iotaFnA_recHead env))
      substIface hΓ hp.2 ha hp.1) hf ha

private def applyPrefix {Γ : LCtxA} (hΓ : CtxWfA prefixEnv noIotaA 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA prefixEnv noIotaA 0 Γ f (.pi D u C v))
    (ha : HasTyA prefixEnv noIotaA 0 Γ a D) :
    HasTyA prefixEnv noIotaA 0 Γ (.app f a) (instantiate0A a C) := by
  have hE := envWfA_closed prefixWf
  have hp := hasTyA_pi_parts
    (hasTyA_regular hE noIotaA_lift (noIotaA_recHead prefixEnv) noIotaA_subst hΓ hf).2
  exact .app Γ f a D C u v v hp.2
    (hasTyA_inst0 hE noIotaA_lift
      (iotaRecHeadTypedA_of (noIotaA_recHead prefixEnv)) noIotaA_subst hΓ hp.2 ha hp.1)
    hf ha

private def eqTypedPrefix {Γ : LCtxA} (hΓ : CtxWfA prefixEnv noIotaA 0 Γ)
    {a b : ExprA} (ha : HasTyA prefixEnv noIotaA 0 Γ a (.sort .zero))
    (hb : HasTyA prefixEnv noIotaA 0 Γ b (.sort .zero)) :
    HasTyA prefixEnv noIotaA 0 Γ (eqAt a b) (.sort .zero) :=
  applyPrefix hΓ (applyPrefix hΓ
    (applyPrefix hΓ (famConstTyped rfl) (.sort Γ .zero)) ha) hb

/-- The same context is well formed already in the admission prefix. -/
def prefixContextWfA3 : CtxWfA prefixEnv noIotaA 0 context :=
  .assumption .nil (eqTypedPrefix .nil parameterTyped parameterTyped)

/-- A closed, genuine use of the recursor added after the constructor prefix. -/
abbrev sortCallA3 : ExprA :=
  foldAppsA (.const 65 [two])
    [.sort .zero, parameter, motive, .sort .zero, parameter, reflAt parameter]

/-- Its conversion is a real old-interface iota step; the minor is `Prop`. -/
theorem sortCallConversionA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (ConvA env (iotaIfaceA env) 0 Γ sortCallA3 (.sort .zero) (.sort one)) := by
  obtain ⟨hr⟩ := recConstTyped Γ
  have h0 := applyHere hΓ hr (.sort Γ .zero)
  have h1 := applyHere hΓ h0 parameterTyped
  have h2 := applyHere hΓ h1 (motiveTyped hΓ)
  have hp := reflTyped hΓ (parameterTyped (E := env) (I := iotaIfaceA env)
    (n := 0) (Γ := Γ))
  have hc := motiveTypeConv hΓ parameterTyped hp
  have hm := hasTyA_of_tyConvA (.sort Γ .zero) hc.symm
  have h3 := applyHere hΓ h2 hm
  have h4 := applyHere hΓ h3 parameterTyped
  have h5 := applyHere hΓ h4 hp
  have ht := hasTyA_of_tyConvA h5 hc
  have hi : (iotaIfaceA env).rel env Γ sortCallA3 (.sort .zero) :=
    ⟨by decide, rfl⟩
  exact ⟨.iota Γ _ _ _ hi ht (.sort Γ .zero)⟩

theorem sortCallTypedA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ sortCallA3 (.sort one)) := by
  obtain ⟨hc⟩ := sortCallConversionA3 hΓ
  exact ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface hΓ hc⟩

theorem sortCallTypeConversionA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (TyConvA env (iotaIfaceA env) 0 Γ sortCallA3 (.sort .zero)) := by
  obtain ⟨hc⟩ := sortCallConversionA3 hΓ
  have ht := convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface hΓ hc
  exact ⟨.of Γ _ _ one one one ht (eqNA_refl _) (.sort Γ .zero) (eqNA_refl _) hc⟩

abbrev partialSubjectA3 : ExprA := .app (.const 64 []) (.sort .zero)
abbrev storedPartialPiA3 : ExprA :=
  .pi (.sort .zero) one (eqAt (.bvar 0) (.bvar 0)) .zero
abbrev chosenPartialPiA3 : ExprA :=
  .pi sortCallA3 one (eqAt (.bvar 0) (.bvar 0)) .zero

private def prefixPartialSubjectTyped {Γ : LCtxA}
    (hΓ : CtxWfA prefixEnv noIotaA 0 Γ) :
    HasTyA prefixEnv noIotaA 0 Γ partialSubjectA3 storedPartialPiA3 := by
  have hT : HasTyA prefixEnv noIotaA 0 [] reflTy (.sort reflSort) :=
    hasTyA_env_iface fam_in_prefix (fun _ _ => rfl) reflTyTyped
  have hTc := hasTyClosedWeakenA (envWfA_closed prefixWf) noIotaA_lift
    (fun _ => rfl) (fun _ => rfl) Γ hT
  have hc : HasTyA prefixEnv noIotaA 0 Γ (.const 64 []) reflTy :=
    .const Γ 64 [] reflMember reflSort rfl rfl rfl hTc
  exact applyPrefix hΓ hc (.sort Γ .zero)

/-- The canonical final typing itself does have a prefix derivation. Hence
the boundary below is specifically about preserving the generated query. -/
def canonicalReflPrefixTypedA3 :
    HasTyA prefixEnv noIotaA 0 context (reflAt parameter) domain :=
  applyPrefix prefixContextWfA3 (prefixPartialSubjectTyped prefixContextWfA3) parameterTyped

def partialSubjectTypedA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ partialSubjectA3 storedPartialPiA3 :=
  applyHere hΓ (reflConstTyped Γ) (.sort Γ .zero)

private def storedBodyTyped {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 (.assumption (.sort .zero) :: Γ)
      (eqAt (.bvar 0) (.bvar 0)) (.sort .zero) :=
  eqTyped (.assumption hΓ (.sort Γ .zero))
    (.bvar _ 0 (.sort .zero) one rfl (.sort _ .zero))
    (.bvar _ 0 (.sort .zero) one rfl (.sort _ .zero))

/-- Both the chosen Pi and its body are positively typed. -/
theorem chosenPartialPiTypedA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ chosenPartialPiA3
      (.sort (.imax one .zero))) := by
  obtain ⟨hS⟩ := sortCallTypedA3 hΓ
  have hΓ' : CtxWfA env (iotaIfaceA env) 0 (.assumption sortCallA3 :: Γ) :=
    .assumption hΓ hS
  obtain ⟨hS'⟩ := sortCallTypedA3 hΓ'
  have hx : HasTyA env (iotaIfaceA env) 0 (.assumption sortCallA3 :: Γ)
      (.bvar 0) sortCallA3 := .bvar _ 0 sortCallA3 one rfl hS'
  obtain ⟨hC⟩ := sortCallTypeConversionA3 hΓ'
  have hx' := hasTyA_of_tyConvA hx hC
  exact ⟨.pi Γ sortCallA3 one _ .zero hS (eqTyped hΓ' hx' hx')⟩

/-- This is the Pi-conversion query consumed by the old uniqueness app arm. -/
theorem chosenPartialPiConversionA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (TyConvA env (iotaIfaceA env) 0 Γ
      storedPartialPiA3 chosenPartialPiA3) := by
  obtain ⟨hC⟩ := sortCallConversionA3 hΓ
  obtain ⟨hP⟩ := chosenPartialPiTypedA3 hΓ
  have hP₀ : HasTyA env (iotaIfaceA env) 0 Γ storedPartialPiA3
      (.sort (.imax one .zero)) :=
    .pi Γ (.sort .zero) one _ .zero (.sort Γ .zero) (storedBodyTyped hΓ)
  have hpi : ConvA env (iotaIfaceA env) 0 Γ storedPartialPiA3 chosenPartialPiA3
      (.sort (.imax one .zero)) :=
    .pi Γ (.sort .zero) sortCallA3 _ _ one one .zero .zero
      (eqNA_refl _) (eqNA_refl _) (.symm Γ _ _ _ hC)
      (.refl _ _ _ (storedBodyTyped hΓ)) hP
  exact ⟨.of Γ _ _ (.imax one .zero) (.imax one .zero) (.imax one .zero)
    hP₀ (eqNA_refl _) hP (eqNA_refl _) hpi⟩

/-- The final application uses that query as its actual carrier. Its subject
and final type are precisely the canonical fixed-subject agreement instance. -/
theorem reflApplicationWithLaterPiA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    ∃ (hf : HasTyA env (iotaIfaceA env) 0 Γ partialSubjectA3 chosenPartialPiA3)
      (ha : HasTyA env (iotaIfaceA env) 0 Γ parameter sortCallA3),
      Nonempty (HasTyA env (iotaIfaceA env) 0 Γ (reflAt parameter) domain) := by
  obtain ⟨hpi⟩ := chosenPartialPiConversionA3 hΓ
  obtain ⟨hS⟩ := sortCallTypeConversionA3 hΓ
  have hf := hasTyA_of_tyConvA (partialSubjectTypedA3 hΓ) hpi
  have ha := hasTyA_of_tyConvA
    (parameterTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := Γ)) hS.symm
  exact ⟨hf, ha, ⟨applyHere hΓ hf ha⟩⟩

private theorem sortCallNoPrefixSupport : ¬ ConstsInA (domA prefixEnv) sortCallA3 := by
  intro h
  obtain ⟨m, hm⟩ := (constsInA_foldAppsA_inv (.const 65 [two])
    [.sort .zero, parameter, motive, .sort .zero, parameter, reflAt parameter] h).1
  change (none : Option CheckedMemberA) = some m at hm
  cases hm

/-- The type-conversion closure preserves environment membership support,
including its untyped reflexivity arm. No row or semantic environment is used. -/
theorem tyConvMemberSupportIffA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A B : ExprA} (hc : TyConvA E I n Γ A B) :
    ConstsInA (domA E) A ↔ ConstsInA (domA E) B := by
  induction hc with
  | refl => exact Iff.rfl
  | of A B l l' u hA hlu hB hl'u h =>
      exact ⟨fun _ => hasTyA_constsIn hB, fun _ => hasTyA_constsIn hA⟩
  | trans A B C h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Reference 65 is absent from the constructor's actual admission prefix. -/
theorem sortCallNoPrefixTypingA3 {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {T : ExprA} :
    ¬ Nonempty (HasTyA prefixEnv I n Γ sortCallA3 T) := by
  rintro ⟨ht⟩
  exact sortCallNoPrefixSupport (hasTyA_constsIn ht)

/-- The generated Pi cannot be used as a typed input to rows in the prefix. -/
theorem chosenPartialPiNoPrefixTypingA3 {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T : ExprA} :
    ¬ Nonempty (HasTyA prefixEnv I n Γ chosenPartialPiA3 T) := by
  rintro ⟨ht⟩
  exact sortCallNoPrefixTypingA3 ⟨(hasTyA_pi_parts ht).1⟩

/-- Even the generated conversion query, with its endpoints unchanged,
cannot be moved to the constructor prefix. -/
theorem chosenPartialPiNoPrefixConversionA3 {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    ¬ Nonempty (TyConvA prefixEnv I n Γ storedPartialPiA3 chosenPartialPiA3) := by
  rintro ⟨hc⟩
  have hS : ConstsInA (domA prefixEnv) storedPartialPiA3 :=
    hasTyA_constsIn
      (hasTyA_regular (envWfA_closed prefixWf) noIotaA_lift
        (noIotaA_recHead prefixEnv) noIotaA_subst .nil (prefixPartialSubjectTyped .nil)).2
  exact sortCallNoPrefixSupport ((tyConvMemberSupportIffA3 hc).mp hS).1

/-- The prefix, full environment, context, conversion, and actual application
premises are all supplied. This records only the failure of verbatim query
restriction; it does not claim the complete D-no alternative. -/
theorem inhabitedPrefixQueryBoundaryA3 :
    Nonempty (EnvWfA noIotaA prefixEnv) ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    PrefixA prefixEnv env ∧
    Nonempty (CtxWfA prefixEnv noIotaA 0 context) ∧
    Nonempty (HasTyA prefixEnv noIotaA 0 context (reflAt parameter) domain) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (TyConvA env (iotaIfaceA env) 0 context
      storedPartialPiA3 chosenPartialPiA3) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context partialSubjectA3 chosenPartialPiA3) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context parameter sortCallA3) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (reflAt parameter) domain) ∧
    (∀ I n Γ T, ¬ Nonempty (HasTyA prefixEnv I n Γ chosenPartialPiA3 T)) ∧
    (∀ I n Γ, ¬ Nonempty (TyConvA prefixEnv I n Γ
      storedPartialPiA3 chosenPartialPiA3)) := by
  obtain ⟨hf, ha, ht⟩ := reflApplicationWithLaterPiA3 contextWf
  exact ⟨⟨prefixWf⟩, wf, prefix_in_env, ⟨prefixContextWfA3⟩,
    ⟨canonicalReflPrefixTypedA3⟩, ⟨contextWf⟩,
    chosenPartialPiConversionA3 contextWf, ⟨hf⟩, ⟨ha⟩, ht,
    (fun _ _ _ _ => chosenPartialPiNoPrefixTypingA3),
    fun _ _ _ => chosenPartialPiNoPrefixConversionA3⟩

#print axioms prefixContextWfA3
#print axioms sortCallA3
#print axioms sortCallConversionA3
#print axioms sortCallTypedA3
#print axioms sortCallTypeConversionA3
#print axioms partialSubjectA3
#print axioms storedPartialPiA3
#print axioms chosenPartialPiA3
#print axioms canonicalReflPrefixTypedA3
#print axioms partialSubjectTypedA3
#print axioms chosenPartialPiTypedA3
#print axioms chosenPartialPiConversionA3
#print axioms reflApplicationWithLaterPiA3
#print axioms tyConvMemberSupportIffA3
#print axioms sortCallNoPrefixTypingA3
#print axioms chosenPartialPiNoPrefixTypingA3
#print axioms chosenPartialPiNoPrefixConversionA3
#print axioms inhabitedPrefixQueryBoundaryA3

end Rcic.Declarative.Ann.LR3.PrefixQuery
