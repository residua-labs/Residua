import rcic.RcicAnnViewTy
import rcic.RcicAnnEnvBridge
import rcic.RcicPinEqEraseWf

/-!
# An inhabited indexed `Eq` test for the existing annotated relation

This file constructs the actual family/refl/AnySort group at references 63--65.
Its erasure is `eqEnvT`.  The recursor's typing is supplied by the existing
view builder over the empty base; no semantic clause for the resulting `Eq`
environment is assumed to admit the group.

The test below concerns the existing head step and existing `EnvSemA` only.
It does not rule out a different guarded relation or a different head step.
-/

namespace Rcic.Declarative.Ann.EqLargeFixture

open Rcic.Declarative

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one
abbrev params : List (ExprA × Level) := [(.sort one, two), (.bvar 0, one)]
abbrev indices : List (ExprA × Level) := [(.bvar 1, one)]
abbrev famTy : ExprA := (piTelA (params ++ indices) (.sort .zero) one).1
abbrev famSort : Level := (piTelA (params ++ indices) (.sort .zero) one).2
abbrev reflTy : ExprA := ctorTypeA 63 [] .zero params [] [.bvar 0]
abbrev reflSort : Level := .imax two (.imax one .zero)
abbrev recTy : ExprA := recTypeA 63 [] params indices .zero (.param 0) [(64, [], [.bvar 0])]

def fam : CheckedMemberA := ⟨.inductiveM, 0, famTy, none, 2, none⟩
def reflMember : CheckedMemberA := ⟨.constructorM, 0, reflTy, none, 0, some reflTy⟩
def recMember : CheckedMemberA := ⟨.recursorM, 1, recTy, none, 0, none⟩
def famEnv : ResolvedEnvA := extendEnvA emptyEnvA 63 fam
def prefixEnv : ResolvedEnvA := extendEnvA famEnv 64 reflMember
def env : ResolvedEnvA := extendEnvA prefixEnv 65 recMember

theorem erase_env : eraseEnv env = eqEnvT := by
  simp only [env, prefixEnv, famEnv, eraseEnv_extend, eraseEnv_empty]
  rfl

private def applyTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA E I n Γ f (.pi D u C v)) (ha : HasTyA E I n Γ a D) :
    HasTyA E I n Γ (.app f a) (instantiate0A a C) := by
  have parts := hasTyA_pi_parts (hasTyA_regular hE hI hR hIS hΓ hf).2
  exact .app Γ f a D C u v v parts.2
    (hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ parts.2 ha parts.1) hf ha

private def applyNoIota {E : ResolvedEnvA} {n : Nat} (hE : EnvClosedA E)
    {Γ : LCtxA} (hΓ : CtxWfA E noIotaA n Γ) {f a D C : ExprA} {u v : Level}
    (hf : HasTyA E noIotaA n Γ f (.pi D u C v)) (ha : HasTyA E noIotaA n Γ a D) :
    HasTyA E noIotaA n Γ (.app f a) (instantiate0A a C) :=
  applyTyped hE noIotaA_lift (noIotaA_recHead E) noIotaA_subst hΓ hf ha

private def sortVar {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (i : Nat) (h : lookupTypeA Γ i = some (.sort one)) :
    HasTyA E I n Γ (.bvar i) (.sort one) :=
  .bvar Γ i (.sort one) two h (.sort Γ one)

def famTyTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ famTy (.sort famSort) :=
  .pi Γ (.sort one) two _ _ (.sort Γ one)
    (.pi _ (.bvar 0) one _ _ (sortVar 0 rfl)
      (.pi _ (.bvar 1) one (.sort .zero) one (sortVar 1 rfl) (.sort _ .zero)))

def famView : FamViewA fam where
  params := params
  indices := indices
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def famWf : EnvWfA noIotaA famEnv :=
  .group emptyEnvA 63 fam famSort .empty rfl rfl (fun _ => rfl)
    famTyTyped rfl famView [] rfl

def famConstTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (hm : E.members 63 = some fam) : HasTyA E I n Γ (.const 63 []) famTy :=
  .const Γ 63 [] fam famSort hm rfl rfl famTyTyped

private abbrev paramCtx : LCtxA := [.assumption (.bvar 0), .assumption (.sort one)]

private def paramCtxWf {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    CtxWfA E I n paramCtx :=
  .assumption (.assumption .nil (.sort [] one)) (sortVar 0 rfl)

private def paramValue {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    HasTyA E I n paramCtx (.bvar 0) (.bvar 1) :=
  .bvar _ 0 (.bvar 1) one rfl (sortVar 1 rfl)

def reflTyTyped : HasTyA famEnv noIotaA 0 [] reflTy (.sort reflSort) := by
  have hE := envWfA_closed famWf
  have h0 := famConstTyped (E := famEnv) (I := noIotaA) (n := 0) (Γ := paramCtx) rfl
  have h1 := applyNoIota hE paramCtxWf h0 (sortVar 1 rfl)
  have h2 := applyNoIota hE paramCtxWf h1 paramValue
  have h3 := applyNoIota hE paramCtxWf h2 paramValue
  exact .pi [] (.sort one) two _ _ (.sort [] one)
    (.pi _ (.bvar 0) one _ .zero (sortVar 0 rfl) h3)

def reflView (I : IotaIfaceA) (hT : HasTyA famEnv I 0 [] reflTy (.sort reflSort)) :
    CtorViewA emptyEnvA I 63 fam famView reflMember where
  mirrors := params
  fields := []
  res := [.bvar 0]
  stored := rfl
  mirrorsConv := .cons [] _ _ _ _ _ _ (.refl [] _) (eqNA_refl _)
    (.cons _ _ _ _ _ [] [] (.refl _ _) (eqNA_refl _) (.nil _))
  typed := .nil _ 0 [.bvar 0]
    (.cons _ _ _ _ (.bvar 0) [] paramValue (.nil .zero))
  univ := fun _ _ h => False.elim (List.not_mem_nil _ h)
  univI := fun _ _ _ _ h => False.elim (List.not_mem_nil _ h)
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => False.elim (List.not_mem_nil _ h))
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨reflSort, ⟨hT⟩⟩

def reflGroup (I : IotaIfaceA) (hT : HasTyA famEnv I 0 [] reflTy (.sort reflSort)) :
    GroupCtorA I emptyEnvA 63 fam famView where
  ref := 64
  member := reflMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := reflSort
  hT := hT
  hlvl := rfl
  view := reflView I hT
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def prefixWf : EnvWfA noIotaA prefixEnv :=
  .group emptyEnvA 63 fam famSort .empty rfl rfl (fun _ => rfl)
    famTyTyped rfl famView [reflGroup noIotaA reflTyTyped] ⟨rfl, rfl⟩

theorem recTyTypedNoIota : ∃ w, Nonempty (HasTyA prefixEnv noIotaA 1 [] recTy (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := [reflGroup noIotaA reflTyTyped]) (elim := .anySort)
    famTyTyped ⟨rfl, rfl⟩ emptyEnvA_closed (envWfA_closed prefixWf)
    (fun _ _ h => Option.noConfusion h) (fun _ _ h => Option.noConfusion h)
    noIotaA_lift noIotaA_subst (noIotaA_recHead emptyEnvA) (noIotaA_recHead prefixEnv)
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one

theorem prefix_noRec : NoRecA prefixEnv := by
  intro r m hm
  by_cases h64 : r = 64
  · subst r
    cases hm
    intro h
    cases h
  · by_cases h63 : r = 63
    · subst r
      cases hm
      intro h
      cases h
    · simp [prefixEnv, famEnv, extendEnvA, emptyEnvA, h64, h63] at hm

theorem prefix_in_env : PrefixA prefixEnv env := prefixA_extend _ _ _ rfl
theorem fam_in_prefix : PrefixA famEnv prefixEnv := prefixA_extend _ _ _ rfl

theorem prefix_iface : IfaceAgreeA prefixEnv noIotaA (iotaIfaceA env) := by
  have h0 : IfaceAgreeA prefixEnv noIotaA (iotaIfaceA prefixEnv) := by
    intro e _
    cases h : iotaFnA prefixEnv e with
    | none => exact h.symm
    | some e' =>
        obtain ⟨r, ls, m, _, hm, hc, _⟩ := iotaFnA_recHead prefixEnv e e' h
        exact False.elim (prefix_noRec r m hm hc)
  exact h0.trans (ifaceAgreeA_prefix prefixWf prefix_in_env)

def reflTyTypedConcrete : HasTyA famEnv (iotaIfaceA env) 0 [] reflTy (.sort reflSort) :=
  hasTyIfaceA (prefix_iface.prefix fam_in_prefix) reflTyTyped

/-- Admission is inhabited without extracting a witness from `Prop` into `Type`. -/
theorem wf : Nonempty (EnvWfA (iotaIfaceA env) env) := by
  obtain ⟨w, ⟨hT⟩⟩ := recTyTypedNoIota
  let cs := [reflGroup (iotaIfaceA env) reflTyTypedConcrete]
  let rc : GroupRecA (iotaIfaceA env) emptyEnvA 63 fam famView cs :=
    { member := recMember
      hcls := rfl
      hnobody := rfl
      hnp := rfl
      elim := .anySort
      harity := rfl
      stored := rfl
      hclT := fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))
      u := w
      hT := hasTyIfaceA prefix_iface hT
      hlvl := rfl }
  exact ⟨.groupRec emptyEnvA 63 fam famSort .empty rfl rfl (fun _ => rfl)
    famTyTyped rfl famView cs ⟨rfl, rfl⟩ rfl rc rfl⟩

theorem closed : EnvClosedA env := wf.elim envWfA_closed
theorem normClosed : EnvNormClosedA env := wf.elim envWfA_normClosed
theorem normCtorType : EnvNormCtorTypeA env := wf.elim envWfA_normCtorType
theorem liftIface : IotaLiftA (iotaIfaceA env) := iotaFnA_lift closed normClosed
theorem substIface : IotaSubstA (iotaIfaceA env) := iotaFnA_subst closed normClosed

private def applyConcrete {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) :=
  applyTyped closed liftIface (iotaFnA_recHead env) substIface hΓ hf ha

/-- The equality parameters are `Prop` and this closed proposition. -/
abbrev parameter : ExprA := .pi (.sort .zero) one (.bvar 0) .zero
/-- A Type-level pi, with strictly positive codomain annotation. -/
abbrev result : ExprA := .pi (.sort .zero) one (.sort .zero) one
abbrev eqAt (a b : ExprA) : ExprA := foldAppsA (.const 63 []) [.sort .zero, a, b]
abbrev reflAt (a : ExprA) : ExprA := foldAppsA (.const 64 []) [.sort .zero, a]
abbrev domain : ExprA := eqAt parameter parameter
abbrev context : LCtxA := [.assumption domain]

def parameterTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ parameter (.sort .zero) :=
  hasTyA_sortEqN (.pi Γ (.sort .zero) one (.bvar 0) .zero (.sort Γ .zero)
    (.bvar _ 0 (.sort .zero) one rfl (.sort _ .zero))) (fun _ => rfl)

def resultTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ result (.sort one) :=
  hasTyA_sortEqN (.pi Γ (.sort .zero) one (.sort .zero) one
    (.sort Γ .zero) (.sort _ .zero)) (fun _ => rfl)

def eqTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a b : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hb : HasTyA env (iotaIfaceA env) 0 Γ b (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ (eqAt a b) (.sort .zero) :=
  applyConcrete hΓ (applyConcrete hΓ
    (applyConcrete hΓ (famConstTyped rfl) (.sort Γ .zero)) ha) hb

def contextWf : CtxWfA env (iotaIfaceA env) 0 context :=
  .assumption .nil (eqTyped .nil parameterTyped parameterTyped)

def majorTyped : HasTyA env (iotaIfaceA env) 0 context (.bvar 0) domain :=
  .bvar context 0 domain .zero rfl (eqTyped contextWf parameterTyped parameterTyped)

def reflConstTyped (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ (.const 64 []) reflTy := by
  have hT := hasTyA_env_iface (prefixA_trans fam_in_prefix prefix_in_env)
    (prefix_iface.prefix fam_in_prefix) reflTyTyped
  exact .const Γ 64 [] reflMember reflSort rfl rfl rfl
    (hasTyClosedWeakenA closed liftIface (fun _ => rfl) (fun _ => rfl) Γ hT)

def reflTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ (reflAt a) (eqAt a a) :=
  applyConcrete hΓ (applyConcrete hΓ (reflConstTyped Γ) (.sort Γ .zero)) ha

abbrev motiveTail (a : ExprA) : ExprA :=
  .pi (eqAt parameter a) .zero (.sort two) (.succ two)
abbrev motiveBody : ExprA := .lam (eqAt parameter (.bvar 0)) .zero (.sort one)
abbrev motive : ExprA := .lam (.sort .zero) one motiveBody
abbrev motiveTy : ExprA :=
  .pi (.sort .zero) one (motiveTail (.bvar 0)) (.imax .zero (.succ two))
abbrev motiveAt (a p : ExprA) : ExprA := .app (.app motive a) p

private def propVar {Γ : LCtxA} : HasTyA env (iotaIfaceA env) 0
    (.assumption (.sort .zero) :: Γ) (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) one rfl (.sort _ .zero)

private def tailLamTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ
      (.lam (eqAt parameter a) .zero (.sort one)) (motiveTail a) :=
  .lam Γ (eqAt parameter a) .zero (.sort one) (.sort two) (.succ two)
    (eqTyped hΓ parameterTyped ha) (.sort _ two) (.sort _ one)

def motiveTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ motive motiveTy :=
  .lam Γ (.sort .zero) one motiveBody (motiveTail (.bvar 0))
    (.imax .zero (.succ two)) (.sort Γ .zero)
    (.pi _ (eqAt parameter (.bvar 0)) .zero (.sort two) (.succ two)
      (eqTyped (.assumption hΓ (.sort Γ .zero)) parameterTyped propVar) (.sort _ two))
    (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar)

def motiveAtTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    HasTyA env (iotaIfaceA env) 0 Γ (motiveAt a p) (.sort two) :=
  applyConcrete hΓ (applyConcrete hΓ (motiveTyped hΓ) ha) hp

def motiveBeta {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    ConvA env (iotaIfaceA env) 0 Γ (motiveAt a p) (.sort one) (.sort two) := by
  have hfirst : ConvA env (iotaIfaceA env) 0 Γ (.app motive a)
      (.lam (eqAt parameter a) .zero (.sort one)) (motiveTail a) :=
    .beta Γ (.sort .zero) one motiveBody a (motiveTail (.bvar 0)) (.sort Γ .zero)
      (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar) ha (tailLamTyped hΓ ha)
  have hc : ConvA env (iotaIfaceA env) 0 Γ (motiveAt a p)
      (.app (.lam (eqAt parameter a) .zero (.sort one)) p) (.sort two) :=
    .app Γ (.app motive a) (.lam (eqAt parameter a) .zero (.sort one)) p p
      (eqAt parameter a) (.sort two) .zero (.succ two) hfirst (.refl Γ p _ hp)
      (.sort _ two) (applyConcrete hΓ (tailLamTyped hΓ ha) hp)
  exact .trans Γ _ _ _ _ hc
    (.beta Γ (eqAt parameter a) .zero (.sort one) p (.sort two)
      (eqTyped hΓ parameterTyped ha) (.sort _ one) hp (.sort Γ one))

def motiveTypeConv {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    TyConvA env (iotaIfaceA env) 0 Γ (motiveAt a p) (.sort one) :=
  .of Γ _ _ two two two (motiveAtTyped hΓ ha hp) (eqNA_refl _)
    (.sort Γ one) (eqNA_refl _) (motiveBeta hΓ ha hp)

theorem recConstTyped (Γ : LCtxA) : Nonempty
    (HasTyA env (iotaIfaceA env) 0 Γ (.const 65 [two]) (instantiateLevelsA [two] recTy)) := by
  obtain ⟨w, ⟨hT⟩⟩ := recTyTypedNoIota
  have h0 := hasTyA_instLevels (envWfA_levels prefixWf) noIotaA_levels
    (n := 0) (ls := [two]) rfl rfl hT
  have h1 := hasTyA_env_iface prefix_in_env prefix_iface h0
  have h2 := hasTyClosedWeakenA closed liftIface
    (fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide)))
    (fun _ => rfl) Γ h1
  exact ⟨.const Γ 65 [two] recMember (instLevel [two] w) rfl rfl rfl h2⟩

abbrev pre : List ExprA := [.sort .zero, parameter, motive, result, parameter]
abbrev recPrefix : ExprA := foldAppsA (.const 65 [two]) pre
abbrev call (p : ExprA) : ExprA := .app recPrefix p

theorem prefixTyped : Nonempty (HasTyA env (iotaIfaceA env) 0 context recPrefix
    (.pi domain .zero (motiveAt parameter (.bvar 0)) two)) := by
  obtain ⟨hr⟩ := recConstTyped context
  have h0 := applyConcrete contextWf hr (.sort context .zero)
  have h1 := applyConcrete contextWf h0 parameterTyped
  have h2 := applyConcrete contextWf h1 (motiveTyped contextWf)
  have hm := hasTyA_of_tyConvA (resultTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := context))
    (motiveTypeConv contextWf parameterTyped (reflTyped contextWf parameterTyped)).symm
  have h3 := applyConcrete contextWf h2 hm
  exact ⟨applyConcrete contextWf h3 parameterTyped⟩

/-- Proof irrelevance aligns the same-index neutral proof with `refl`; actual ι then returns the minor. -/
theorem conversion : Nonempty (ConvA env (iotaIfaceA env) 0 context
    (call (.bvar 0)) result (.sort one)) := by
  obtain ⟨hf⟩ := prefixTyped
  have hp := majorTyped
  have hr := reflTyped contextWf (parameterTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := context))
  have tcp := motiveTypeConv contextWf parameterTyped hp
  have tcr := motiveTypeConv contextWf parameterTyped hr
  have hfr := applyConcrete contextWf hf hr
  have hfrP := hasTyA_of_tyConvA hfr (.trans context _ _ _ tcr tcp.symm)
  have hirr : ConvA env (iotaIfaceA env) 0 context (.bvar 0) (reflAt parameter) domain :=
    .irr context domain (.bvar 0) (reflAt parameter)
      (eqTyped contextWf parameterTyped parameterTyped) hp hr
  have hbody := (hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface contextWf hf).2).2
  have hc := ConvA.app context recPrefix recPrefix (.bvar 0) (reflAt parameter) domain
    (motiveAt parameter (.bvar 0)) .zero two (.refl context _ _ hf) hirr hbody hfrP
  have hc' := convA_of_tyConvA hc tcp
  have hι : (iotaIfaceA env).rel env context (call (reflAt parameter)) result :=
    ⟨by decide, by decide⟩
  exact ⟨.trans context _ _ _ _ hc'
    (.iota context _ _ _ hι (hasTyA_of_tyConvA hfr tcr) resultTyped)⟩

theorem callStuck : StuckA env (iotaIfaceA env) context (call (.bvar 0)) := by
  have hn := neutKA_bvar closed liftIface (iotaConstHeadA_of_recHead (iotaFnA_recHead env))
    (Γ := context) (i := 0) rfl
  exact neutKA_stuck (neutKA_recApp closed liftIface (r := 65) (m := recMember)
    rfl rfl (ls := [two]) (pre := pre) (N := .bvar 0) rfl
    (.inl ⟨neutKA_stuckTm hn, by decide, by decide⟩))

/-- The old semantic target cannot supply this admitted indexed large eliminator. -/
theorem envSem_false {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀) :
    ¬ EnvSemA env (iotaIfaceA env) 0 ρ₀ := by
  intro hS
  obtain ⟨hc⟩ := conversion
  obtain ⟨k, hk⟩ := fund_tyEq closed liftIface substIface normCtorType normClosed
    (iotaFnA_recHead env) hS hρ contextWf hc
  have heq := hk k (Nat.le_refl k)
  rw [LREqA_eq] at heq
  have ht := convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc
  exact eqKA_tripleLike_typi_false (D := .sort .zero) (u := one)
    (C := .sort .zero) (v := one) rfl (whTyA_of_hasTy ht)
    (tripleLikeA_of_stuck callStuck) heq

/-- All hypotheses of the concrete failure instance are supplied, including a
closed inhabitant of the context's equality domain and both Type-level endpoints. -/
theorem inhabited_boundary :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call (.bvar 0)) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context result (.sort one)) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 context (call (.bvar 0)) result (.sort one)) ∧
    isZero one = false ∧
    StuckA env (iotaIfaceA env) context (call (.bvar 0)) ∧
    ¬ EnvSemA env (iotaIfaceA env) 0 (fun _ => 1) := by
  obtain ⟨hc⟩ := conversion
  exact ⟨erase_env, wf, ⟨contextWf⟩, ⟨reflTyped .nil parameterTyped⟩,
    ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc⟩,
    ⟨resultTyped⟩, ⟨hc⟩, rfl, callStuck, envSem_false posValA_one⟩

#print axioms erase_env
#print axioms wf
#print axioms contextWf
#print axioms conversion
#print axioms callStuck
#print axioms envSem_false
#print axioms inhabited_boundary

end Rcic.Declarative.Ann.EqLargeFixture
