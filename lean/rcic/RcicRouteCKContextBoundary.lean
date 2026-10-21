import rcic.RcicAnnEqLargeFixture
import rcic.RcicSynInlineRefute
import rcic.RcicSynSortRow
import rcic.RcicSynFamRigid

/-!
# Route C: the erased K guard retains its context

The same two source indices have different canonical erased images in a
let context and an assumption context. Both contexts are inhabited and
well formed in the actual Eq environment. This rules out an EXACT guard
factoring through source expressions alone. It does not rule out a
context-aware or certificate-bearing head relation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.RouteCKContext

open Rcic.Declarative Rcic.Syn
open EqLargeFixture

abbrev baseLet : LCtxA := [.letBinding (.sort .zero) parameter]
abbrev baseAssumption : LCtxA := [.assumption (.sort .zero)]
abbrev proofDomain : ExprA := eqAt parameter (.bvar 0)
abbrev letContext : LCtxA := .assumption proofDomain :: baseLet
abbrev assumptionContext : LCtxA := .assumption proofDomain :: baseAssumption

def baseLetWf : CtxWfA env (iotaIfaceA env) 0 baseLet :=
  .letBinding .nil (.sort [] .zero) parameterTyped

def baseAssumptionWf : CtxWfA env (iotaIfaceA env) 0 baseAssumption :=
  .assumption .nil (.sort [] .zero)

def baseIndexTyped {Γ : LCtxA}
    (h : lookupTypeA Γ 0 = some (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ (.bvar 0) (.sort .zero) :=
  .bvar Γ 0 (.sort .zero) one h (.sort Γ .zero)

def letContextWf : CtxWfA env (iotaIfaceA env) 0 letContext :=
  .assumption baseLetWf (eqTyped baseLetWf parameterTyped (baseIndexTyped rfl))

def assumptionContextWf : CtxWfA env (iotaIfaceA env) 0 assumptionContext :=
  .assumption baseAssumptionWf
    (eqTyped baseAssumptionWf parameterTyped (baseIndexTyped rfl))

def indexTyped {Γ : LCtxA} (h : lookupTypeA Γ 1 = some (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ (.bvar 1) (.sort .zero) :=
  .bvar Γ 1 (.sort .zero) one h (.sort Γ .zero)

def proofTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    (hx : lookupTypeA Γ 1 = some (.sort .zero))
    (hp : lookupTypeA Γ 0 = some (eqAt parameter (.bvar 1))) :
    HasTyA env (iotaIfaceA env) 0 Γ (.bvar 0) (eqAt parameter (.bvar 1)) :=
  .bvar Γ 0 _ .zero hp (eqTyped hΓ parameterTyped (indexTyped hx))

/-- The index conversion supplied by the actual local definition. -/
def letIndexConversion :
    ConvA env (iotaIfaceA env) 0 letContext (.bvar 1) parameter (.sort .zero) :=
  .zetaLocal letContext 1 (.sort .zero) parameter rfl rfl parameterTyped

private def applyA {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) := by
  have parts := hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface hΓ hf).2
  exact .app Γ f a D C u v v parts.2
    (hasTyA_inst0 closed liftIface (iotaRecHeadTypedA_of (iotaFnA_recHead env))
      substIface hΓ parts.2 ha parts.1) hf ha

/-- The source call is identical in the two contexts. -/
abbrev contextCall : ExprA :=
  foldAppsA (.const 65 [two]) [.sort .zero, parameter, motive, result, .bvar 1, .bvar 0]

theorem contextCallTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    (hx : lookupTypeA Γ 1 = some (.sort .zero))
    (hp : lookupTypeA Γ 0 = some (eqAt parameter (.bvar 1))) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ contextCall (.sort one)) := by
  obtain ⟨hr⟩ := recConstTyped Γ
  have h0 := applyA hΓ hr (.sort Γ .zero)
  have h1 := applyA hΓ h0 parameterTyped
  have h2 := applyA hΓ h1 (motiveTyped hΓ)
  have hm := hasTyA_of_tyConvA
    (resultTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := Γ))
    (motiveTypeConv hΓ parameterTyped (reflTyped hΓ parameterTyped)).symm
  have h3 := applyA hΓ h2 hm
  have h4 := applyA hΓ h3 (indexTyped hx)
  have h5 := applyA hΓ h4 (proofTyped hΓ hx hp)
  exact ⟨hasTyA_of_tyConvA h5
    (motiveTypeConv hΓ (indexTyped hx) (proofTyped hΓ hx hp))⟩


/-- The actual local-zeta guard also gives family-type conversion. -/
def letFamilyConversion :
    TyConvA env (iotaIfaceA env) 0 letContext
      (eqAt parameter (.bvar 1)) (eqAt parameter parameter) := by
  have hf := applyA letContextWf
    (applyA letContextWf (famConstTyped (E := env) (I := iotaIfaceA env)
      (n := 0) (Γ := letContext) rfl) (.sort letContext .zero)) parameterTyped
  exact .of letContext _ _ .zero .zero .zero
    (eqTyped letContextWf parameterTyped (indexTyped rfl)) (eqNA_refl _)
    (eqTyped letContextWf parameterTyped parameterTyped) (eqNA_refl _)
    (.app letContext _ _ (.bvar 1) parameter (.sort .zero) (.sort .zero) one one
      (.refl letContext _ _ hf) letIndexConversion (.sort _ .zero)
      (eqTyped letContextWf parameterTyped parameterTyped))

def letCanonicalTyped :
    HasTyA env (iotaIfaceA env) 0 letContext (reflAt parameter)
      (eqAt parameter (.bvar 1)) :=
  hasTyA_of_tyConvA (reflTyped letContextWf parameterTyped) letFamilyConversion.symm

/-- Proof irrelevance applies at the actual local index, with the canonical
proof transported through the independently supplied family conversion. -/
def letMajorIrrelevance :
    ConvA env (iotaIfaceA env) 0 letContext (.bvar 0) (reflAt parameter)
      (eqAt parameter (.bvar 1)) :=
  .irr letContext _ _ _
    (eqTyped letContextWf parameterTyped (indexTyped rfl))
    (proofTyped letContextWf rfl rfl) letCanonicalTyped

abbrev contextPrefix : ExprA :=
  foldAppsA (.const 65 [two]) [.sort .zero, parameter, motive, result, .bvar 1]

theorem contextPrefixTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    (hx : lookupTypeA Γ 1 = some (.sort .zero)) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ contextPrefix
      (.pi (eqAt parameter (.bvar 1)) .zero (motiveAt (.bvar 2) (.bvar 0)) two)) := by
  obtain ⟨hr⟩ := recConstTyped Γ
  have h0 := applyA hΓ hr (.sort Γ .zero)
  have h1 := applyA hΓ h0 parameterTyped
  have h2 := applyA hΓ h1 (motiveTyped hΓ)
  have hm := hasTyA_of_tyConvA
    (resultTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := Γ))
    (motiveTypeConv hΓ parameterTyped (reflTyped hΓ parameterTyped)).symm
  have h3 := applyA hΓ h2 hm
  exact ⟨applyA hΓ h3 (indexTyped hx)⟩

/-- The existing annotated conversion derives the context-sensitive K
conclusion using local zeta, irrelevance, application congruence and old iota. -/
theorem letCallConversion :
    Nonempty (ConvA env (iotaIfaceA env) 0 letContext contextCall result (.sort one)) := by
  obtain ⟨hf⟩ := contextPrefixTyped letContextWf rfl
  have hp := proofTyped letContextWf rfl rfl
  have hr := letCanonicalTyped
  have tcp := motiveTypeConv letContextWf (indexTyped rfl) hp
  have tcr := motiveTypeConv letContextWf (indexTyped rfl) hr
  have hfr := applyA letContextWf hf hr
  have hfrP := hasTyA_of_tyConvA hfr (.trans letContext _ _ _ tcr tcp.symm)
  have hbody := (hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface letContextWf hf).2).2
  have hc := ConvA.app letContext contextPrefix contextPrefix (.bvar 0) (reflAt parameter)
    (eqAt parameter (.bvar 1)) (motiveAt (.bvar 2) (.bvar 0)) .zero two
    (.refl letContext _ _ hf) letMajorIrrelevance hbody hfrP
  have hc' := convA_of_tyConvA hc tcp
  have hι : (iotaIfaceA env).rel env letContext
      (.app contextPrefix (reflAt parameter)) result :=
    ⟨by decide, by decide⟩
  exact ⟨.trans letContext _ _ _ _ hc'
    (.iota letContext _ _ _ hι (hasTyA_of_tyConvA hfr tcr) resultTyped)⟩

/-- Both contexts admit the same closed values for their declarations. -/
theorem closedValues :
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] parameter (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter)
      (instantiate0A parameter proofDomain)) :=
  ⟨⟨parameterTyped⟩, ⟨reflTyped .nil parameterTyped⟩⟩

abbrev parameterT : Expr Nat := erase parameter
abbrev parameterE : ETm := .pi (.sort .zero) (.bvar 0)

/-- Enriched typing of the same closed proposition at any context. -/
def parameterP (Γ : LCtx) : TyP eqEnvT 0 Γ parameterT (.sort .zero) :=
  .conv _ _ _ _ (.sort (.imax one .zero)) (.sort .zero) (.succ (.imax one .zero))
    (.pi _ _ _ (.sort .zero) one (.bvar 0) .zero
      (.sort _ _ _ _ _ (eqN_refl _))
      (.bvar _ _ _ 0 (.sort .zero) one rfl (.sort _ _ _ _ _ (eqN_refl _))))
    (.sorts _ _ _ (.imax one .zero) .zero (fun _ => rfl)
      (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (fun _ => rfl)))

theorem parameterP_eps (Γ : LCtx) (ρ : List Disp) :
    (parameterP Γ).eps id ρ = parameterE := rfl

/-- The enriched Eq family head, with its declared telescope. -/
def familyTypeP (Γ : LCtx) :
    TyP eqEnvT 0 Γ eqFamT.mtype (.sort (.imax two (.imax one (.imax one one)))) :=
  .pi _ _ _ (.sort one) two _ _
    (.sort _ _ _ _ _ (eqN_refl _))
    (.pi _ _ _ (.bvar 0) one _ _
      (.bvar _ _ _ 0 (.sort one) two rfl (.sort _ _ _ _ _ (eqN_refl _)))
      (.pi _ _ _ (.bvar 1) one (.sort .zero) one
        (.bvar _ _ _ 1 (.sort one) two rfl (.sort _ _ _ _ _ (eqN_refl _)))
        (.sort _ _ _ _ _ (eqN_refl _))))

def familyP (Γ : LCtx) : TyP eqEnvT 0 Γ (.const 63 []) eqFamT.mtype :=
  .const _ _ _ 63 [] [] eqFamT _ rfl rfl rfl trivial (familyTypeP Γ)

/-- Family formation is typed independently of any semantic environment. -/
def eqP {Γ : LCtx} {b : Expr Nat}
    (hb : TyP eqEnvT 0 Γ b (.sort .zero)) :
    TyP eqEnvT 0 Γ (foldApps (.const 63 []) [.sort .zero, parameterT, b]) (.sort .zero) :=
  .app _ _ _ _ b (.sort .zero) (.sort .zero) one
    (.app _ _ _ _ parameterT (.sort .zero) (.pi (.sort .zero) (.sort .zero))
      (.imax one one)
      (.app _ _ _ _ (.sort .zero) (.sort one)
        (.pi (.bvar 0) (.pi (.bvar 1) (.sort .zero))) (.imax one (.imax one one))
        (familyP Γ) (.sort _ _ _ _ _ (eqN_refl _))
        (.pi _ _ _ (.sort .zero) one (.pi (.sort .zero) (.sort .zero)) (.imax one one)
          (.sort _ _ _ _ _ (eqN_refl _))
          (.pi _ _ _ (.sort .zero) one (.sort .zero) one
            (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (eqN_refl _)))))
      (parameterP Γ)
      (.pi _ _ _ (.sort .zero) one (.sort .zero) one
        (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (eqN_refl _))))
    hb (.sort _ _ _ _ _ (eqN_refl _))

def baseLetP : CtxP eqEnvT 0 (eraseCtx baseLet) :=
  .letBinding _ _ [] (.sort .zero) one parameterT (.nil _ _)
    (.sort _ _ _ _ _ (eqN_refl _)) (parameterP [])

def baseAssumptionP : CtxP eqEnvT 0 (eraseCtx baseAssumption) :=
  .assumption _ _ [] (.sort .zero) one (.nil _ _)
    (.sort _ _ _ _ _ (eqN_refl _))

def letContextP : CtxP eqEnvT 0 (eraseCtx letContext) :=
  .assumption _ _ _ _ .zero baseLetP
    (eqP (.bvar _ _ _ 0 (.sort .zero) one rfl (.sort _ _ _ _ _ (eqN_refl _))))

def assumptionContextP : CtxP eqEnvT 0 (eraseCtx assumptionContext) :=
  .assumption _ _ _ _ .zero baseAssumptionP
    (eqP (.bvar _ _ _ 0 (.sort .zero) one rfl (.sort _ _ _ _ _ (eqN_refl _))))

def letIndexP : TyP eqEnvT 0 (eraseCtx letContext) (.bvar 1) (.sort .zero) :=
  .bvar _ _ _ 1 (.sort .zero) one rfl (.sort _ _ _ _ _ (eqN_refl _))

def assumptionIndexP :
    TyP eqEnvT 0 (eraseCtx assumptionContext) (.bvar 1) (.sort .zero) :=
  .bvar _ _ _ 1 (.sort .zero) one rfl (.sort _ _ _ _ _ (eqN_refl _))

theorem letDisplay : letContextP.disp id = [.drop, .inline parameterE] := rfl
theorem assumptionDisplay : assumptionContextP.disp id = [.drop, .keep] := rfl
theorem letIndexEps : letIndexP.eps id (letContextP.disp id) = parameterE := rfl
theorem assumptionIndexEps :
    assumptionIndexP.eps id (assumptionContextP.disp id) = .bvar 0 := rfl

def letErasedGuard (tbl : List CRule) : Prop :=
  ConvMod (EStep tbl) LvlEq
    ((parameterP (eraseCtx letContext)).eps id (letContextP.disp id))
    (letIndexP.eps id (letContextP.disp id))

def assumptionErasedGuard (tbl : List CRule) : Prop :=
  ConvMod (EStep tbl) LvlEq
    ((parameterP (eraseCtx assumptionContext)).eps id (assumptionContextP.disp id))
    (assumptionIndexP.eps id (assumptionContextP.disp id))

theorem letErasedGuard_holds (tbl : List CRule) : letErasedGuard tbl :=
  .refl parameterE

/-- A Pi head and a free variable cannot join in a well-formed erased table. -/
theorem not_convMod_pi_bvar {tbl : List CRule} (hW : TableWF tbl)
    (A B : ETm) (i : Nat) :
    ¬ ConvMod (EStep tbl) LvlEq (.pi A B) (.bvar i) := by
  intro hc
  obtain ⟨u, v, hu, hq, hv⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr)
      (confluent_eStep_wf hW) hc
  obtain ⟨A', B', rfl, _, _⟩ := rstar_eStep_pi_inv hu
  have hv' := rstar_bvar_eq hv
  subst hv'
  cases hq

theorem assumptionErasedGuard_fails {tbl : List CRule} (hW : TableWF tbl) :
    ¬ assumptionErasedGuard tbl :=
  not_convMod_pi_bvar hW (.sort .zero) (.bvar 0) 0

/-- Exactness at both admitted contexts; this is a factorization demand, not
a soundness claim about arbitrary annotated conversion. -/
def ExactContextFreeGuard (tbl : List CRule) (accepts : Prop) : Prop :=
  (accepts ↔ letErasedGuard tbl) ∧ (accepts ↔ assumptionErasedGuard tbl)

theorem exactContextFreeGuard_false {tbl : List CRule} (hW : TableWF tbl)
    (accepts : Prop) : ¬ ExactContextFreeGuard tbl accepts := by
  rintro ⟨hl, ha⟩
  exact assumptionErasedGuard_fails hW (ha.mp (hl.mpr (letErasedGuard_holds tbl)))

/-- The existing interface sees the same source call in both contexts. -/
theorem no_exact_source_iota_guard {tbl : List CRule} (hW : TableWF tbl)
    (I : IotaIfaceA) :
    ¬ ExactContextFreeGuard tbl (I.fn contextCall = some result) :=
  exactContextFreeGuard_false hW _

theorem inhabited_context_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 letContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 assumptionContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 letContext contextCall (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext contextCall (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] parameter (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter)
      (instantiate0A parameter proofDomain)) ∧
    TableWF [] ∧ letErasedGuard [] ∧ ¬ assumptionErasedGuard [] ∧
    (∀ I : IotaIfaceA, ¬ ExactContextFreeGuard [] (I.fn contextCall = some result)) :=
  ⟨erase_env, wf, ⟨letContextWf⟩, ⟨assumptionContextWf⟩,
    contextCallTyped letContextWf rfl rfl,
    contextCallTyped assumptionContextWf rfl rfl, closedValues.1, closedValues.2,
    emptyTable_wf, letErasedGuard_holds [], assumptionErasedGuard_fails emptyTable_wf,
    no_exact_source_iota_guard emptyTable_wf⟩

/-- A concrete closing substitution, shared by both contexts. -/
def closeSubstitution : SubstA
  | 0 => reflAt parameter
  | _ + 1 => parameter

def letClosingSubstitution :
    SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution letContext where
  ty := by
    intro i A h
    cases i with
    | zero =>
        cases h
        exact reflTyped .nil parameterTyped
    | succ i =>
        cases i with
        | zero =>
            cases h
            exact parameterTyped
        | succ i =>
            simp [lookupTypeA, letContext, baseLet, List.get?] at h
  val := by
    intro i A v hT hV
    cases i with
    | zero => cases hV
    | succ i =>
        cases i with
        | zero =>
            cases hT
            cases hV
            exact .refl [] parameter (.sort .zero) parameterTyped
        | succ i =>
            simp [lookupTypeA, letContext, baseLet, List.get?] at hT

def assumptionClosingSubstitution :
    SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext where
  ty := by
    intro i A h
    cases i with
    | zero =>
        cases h
        exact reflTyped .nil parameterTyped
    | succ i =>
        cases i with
        | zero =>
            cases h
            exact parameterTyped
        | succ i =>
            simp [lookupTypeA, assumptionContext, baseAssumption, List.get?] at h
  val := by
    intro i A v _ hV
    cases i with
    | zero => cases hV
    | succ i =>
        cases i with
        | zero => cases hV
        | succ i =>
            simp [lookupValueA, assumptionContext, baseAssumption, List.get?] at hV

theorem closed_context_guard_boundary :
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution letContext) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 letContext contextCall result (.sort one)) ∧
    (∀ (tbl : List CRule), TableWF tbl →
      letErasedGuard tbl ∧ ¬ assumptionErasedGuard tbl ∧
      ∀ I : IotaIfaceA, ¬ ExactContextFreeGuard tbl (I.fn contextCall = some result)) :=
  ⟨⟨letClosingSubstitution⟩, ⟨assumptionClosingSubstitution⟩, letCallConversion,
    fun tbl hW => ⟨letErasedGuard_holds tbl, assumptionErasedGuard_fails hW,
      no_exact_source_iota_guard hW⟩⟩

/-- The enclosing head strategy cannot recover the missing index context:
all prefixes are below the major, and the proof major is an assumption in
both contexts. This holds for every raw iota function. -/
theorem headStep_sameContexts (I : IotaIfaceA) :
    hStepFnA env I.fn letContext contextCall =
      hStepFnA env I.fn assumptionContext contextCall := by
  have hbelow : BelowMajorA env contextPrefix := by
    intro r ls m hsp hm _
    have hsp' : ExprA.const 65 [two] = .const r ls := hsp
    cases hsp'
    cases hm
    decide
  have hf := hStepFnA_ctx_below env I.fn letContext assumptionContext
    contextPrefix ⟨65, [two], rfl⟩ hbelow
  change hStepFnA env I.fn letContext (.app contextPrefix (.bvar 0)) =
    hStepFnA env I.fn assumptionContext (.app contextPrefix (.bvar 0))
  rw [hStepFnA_app_nonlam env I.fn letContext (.bvar 0)
      (foldAppsA_const_not_lam 65 [two] _),
    hStepFnA_app_nonlam env I.fn assumptionContext (.bvar 0)
      (foldAppsA_const_not_lam 65 [two] _), hf]
  cases hStepFnA env I.fn assumptionContext contextPrefix <;> rfl

theorem iotaRel_sameContexts (I : IotaIfaceA) :
    I.rel env letContext contextCall result ↔
      I.rel env assumptionContext contextCall result := by
  simp only [IotaIfaceA.rel, headStep_sameContexts]

/-- Exact use of the preferred erased guard at these two calls cannot be
realized even by the full graph-plus-head-step relation of the old interface. -/
theorem no_exact_context_iota_relation {tbl : List CRule} (hW : TableWF tbl)
    (I : IotaIfaceA) :
    ¬ ((I.rel env letContext contextCall result ↔ letErasedGuard tbl) ∧
      (I.rel env assumptionContext contextCall result ↔ assumptionErasedGuard tbl)) := by
  rintro ⟨hl, ha⟩
  have hlet := hl.mpr (letErasedGuard_holds tbl)
  exact assumptionErasedGuard_fails hW (ha.mp ((iotaRel_sameContexts I).mp hlet))


/-- All premises of the full graph boundary are supplied in the same admitted
Eq environment, including actual typed substitutions into the empty context. -/
theorem inhabited_full_graph_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 letContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 assumptionContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 letContext contextCall (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext contextCall (.sort one)) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution letContext) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 letContext contextCall result (.sort one)) ∧
    TableWF [] ∧ letErasedGuard [] ∧ ¬ assumptionErasedGuard [] ∧
    (∀ I : IotaIfaceA,
      ¬ ((I.rel env letContext contextCall result ↔ letErasedGuard []) ∧
        (I.rel env assumptionContext contextCall result ↔ assumptionErasedGuard []))) :=
  ⟨erase_env, wf, ⟨letContextWf⟩, ⟨assumptionContextWf⟩,
    contextCallTyped letContextWf rfl rfl,
    contextCallTyped assumptionContextWf rfl rfl,
    ⟨letClosingSubstitution⟩, ⟨assumptionClosingSubstitution⟩, letCallConversion,
    emptyTable_wf, letErasedGuard_holds [], assumptionErasedGuard_fails emptyTable_wf,
    no_exact_context_iota_relation emptyTable_wf⟩

end Rcic.Declarative.Ann.RouteCKContext
