import rcic.RcicNativeTypedModelCovVHeadActions

/-!
# Finite value actions with actual spine fields

The spine clause retains a native reduction to the observed head and the
actions of its actual arguments.  Its compact recursion is strictly finite.
The constructor-demand theorem below aligns all demand vectors by native
determinism, so they describe one constructor spine and one field list.

These are compositional lemmas for an observation induction, not an assumed
general observation supplier.  No native normalization theorem is postulated.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovVAudit

/-- A heterogeneous pointwise relation, with the native arguments first. -/
inductive CovWListRealizes (R : CptT → Expr Nat → Prop) :
    List (Expr Nat) → List CptT → Prop
  | nil : CovWListRealizes R [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {u : CptT} {us : List CptT}
      (head : R u x) (tail : CovWListRealizes R xs us) :
      CovWListRealizes R (x :: xs) (u :: us)

theorem CovWListRealizes.length_eq {R : CptT → Expr Nat → Prop} :
    ∀ {xs : List (Expr Nat)} {us : List CptT},
      CovWListRealizes R xs us → xs.length = us.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CovWListRealizes.length_eq h]

theorem CovWListRealizes.getD {R : CptT → Expr Nat → Prop} :
    ∀ {xs : List (Expr Nat)} {us : List CptT},
      CovWListRealizes R xs us →
      ∀ i (hi : i < us.length), R us[i] (xs.getD i (.bvar 0))
  | _, _, .nil, _, hi => by cases hi
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ h, i + 1, hi =>
      CovWListRealizes.getD h i (Nat.lt_of_succ_lt_succ hi)

theorem CovWListRealizes.of_getD {R : CptT → Expr Nat → Prop} :
    ∀ {xs : List (Expr Nat)} {us : List CptT},
      xs.length = us.length →
      (∀ i (hi : i < us.length), R us[i] (xs.getD i (.bvar 0))) →
      CovWListRealizes R xs us
  | [], [], _, _ => .nil
  | _ :: _, [], hlen, _ => by cases hlen
  | [], _ :: _, hlen, _ => by cases hlen
  | x :: xs, u :: us, hlen, h =>
      .cons (h 0 (by simp))
        (CovWListRealizes.of_getD (Nat.succ.inj hlen)
          (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

theorem CovWListRealizes.append {R : CptT → Expr Nat → Prop} :
    ∀ {xs ys : List (Expr Nat)} {us vs : List CptT},
      CovWListRealizes R xs us → CovWListRealizes R ys vs →
      CovWListRealizes R (xs ++ ys) (us ++ vs)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hxs, h => .cons hx (CovWListRealizes.append hxs h)

theorem CovWListRealizes.append_right {R : CptT → Expr Nat → Prop} :
    ∀ {xs ys : List (Expr Nat)} {us vs : List CptT},
      xs.length = us.length → CovWListRealizes R (xs ++ ys) (us ++ vs) →
      CovWListRealizes R ys vs
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, hlen, .cons _ h =>
      CovWListRealizes.append_right (Nat.succ.inj hlen) h
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _ => by cases hlen

/-- Every compact demanded of a field refers to that same native field. -/
inductive CovWListDemands (R : CptT → Expr Nat → Prop) :
    List (Expr Nat) → List (List CptT) → Prop
  | nil : CovWListDemands R [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)}
      {us : List CptT} {uss : List (List CptT)}
      (head : ∀ u ∈ us, R u x) (tail : CovWListDemands R xs uss) :
      CovWListDemands R (x :: xs) (us :: uss)

theorem CovWListDemands.length_eq {R : CptT → Expr Nat → Prop} :
    ∀ {xs : List (Expr Nat)} {uss : List (List CptT)},
      CovWListDemands R xs uss → xs.length = uss.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CovWListDemands.length_eq h]

theorem CovWListDemands.append_inv {R : CptT → Expr Nat → Prop} :
    ∀ {xs ys : List (Expr Nat)} {uss vss : List (List CptT)},
      xs.length = uss.length → CovWListDemands R (xs ++ ys) (uss ++ vss) →
      CovWListDemands R xs uss ∧ CovWListDemands R ys vss
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | _ :: _, _, _ :: _, _, hlen, .cons hx hxs =>
      let h := CovWListDemands.append_inv (Nat.succ.inj hlen) hxs
      ⟨.cons hx h.1, h.2⟩
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _ => by cases hlen

/-- The final argument is recovered by structural demand-list induction. -/
theorem CovWListDemands.snoc_inv {R : CptT → Expr Nat → Prop}
    (uss : List (List CptT)) {xs : List (Expr Nat)} {last : List CptT}
    (h : CovWListDemands R xs (uss ++ [last])) :
    ∃ (pre : List (Expr Nat)) (x : Expr Nat),
      xs = pre ++ [x] ∧ CovWListDemands R pre uss ∧ ∀ u ∈ last, R u x := by
  induction uss generalizing xs with
  | nil =>
      cases h with
      | cons hx htail =>
          cases htail
          exact ⟨[], _, rfl, .nil, hx⟩
  | cons us uss ih =>
      cases h with
      | cons hx htail =>
          obtain ⟨pre, x, rfl, hp, hl⟩ := ih htail
          exact ⟨_ :: pre, x, rfl, .cons hx hp, hl⟩

/-- The per-field demand encoding is inverted for any native interpretation. -/
theorem covW_fields_of_demand_vectors {R : CptT → Expr Nat → Prop} :
    ∀ {fields : List (Expr Nat)} {uss : List (List CptT)},
      fields.length = uss.length →
      (∀ vec ∈ fieldDemandVectorsT uss, CovWListRealizes R fields vec) →
      CovWListDemands R fields uss
  | [], [], _, _ => .nil
  | _ :: _, [], hlen, _ => by cases hlen
  | [], _ :: _, hlen, _ => by cases hlen
  | x :: xs, us :: uss, hlen, hvec =>
      .cons
        (fun u hu => by
          have hmem : u :: List.replicate uss.length .bot ∈
              fieldDemandVectorsT (us :: uss) :=
            List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨u, hu, rfl⟩))
          have h := hvec _ hmem
          cases h with
          | cons hx _ => exact hx)
        (covW_fields_of_demand_vectors (Nat.succ.inj hlen) (fun vec hv => by
          have hmem : .bot :: vec ∈ fieldDemandVectorsT (us :: uss) :=
            List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨vec, hv, rfl⟩))
          have h := hvec _ hmem
          cases h with
          | cons _ hxs => exact hxs))

/-- The recursive spine arguments are genuine subcompacts.  Native arguments
and native reduction derivations are never used as recursion measures. -/
def CovWValueAction (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e : Expr Nat) : Prop :=
  match c with
  | .bot => True
  | .lam rows => CovVNativeHead E n Γ e ∧
      ∀ s ∈ rows, ∀ a : Expr Nat,
        (∀ u ∈ s.1, CovWValueAction E n Γ u a) →
        CovWValueAction E n Γ s.2 (.app e a)
  | .spine r us => ∃ (ls : List Level) (xs : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
      (∀ args : List (Expr Nat),
        NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args)) ∧
      xs.length = us.length ∧
      ∀ i (hi : i < us.length),
        CovWValueAction E n Γ us[i] (xs.getD i (.bvar 0))
  | .prop => ∃ l : Level, sortCode l = .prop ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .sort => ∃ l : Level, sortCode l = .sort ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .pi _ _ => ∃ D B : Expr Nat,
      RedR (WhStepCK2 E n) Γ e (.pi D B)
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  · have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    have hu := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have hd := sizeOfT_fst_lt s
    omega
  · have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    have ho := sizeOfT_snd_lt s
    omega
  · have hu := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›)
    omega

theorem covW_value_action_spine_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {us : List CptT} {e : Expr Nat} :
    CovWValueAction E n Γ (.spine r us) e ↔
      ∃ (ls : List Level) (xs : List (Expr Nat)),
        RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
        (∀ args : List (Expr Nat),
          NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args)) ∧
        CovWListRealizes (CovWValueAction E n Γ) xs us := by
  rw [CovWValueAction]
  constructor
  · rintro ⟨ls, xs, hr, hn, hlen, hx⟩
    exact ⟨ls, xs, hr, hn, CovWListRealizes.of_getD hlen hx⟩
  · rintro ⟨ls, xs, hr, hn, hx⟩
    exact ⟨ls, xs, hr, hn, hx.length_eq, hx.getD⟩

theorem covW_value_action_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e : Expr Nat} (h : CovWValueAction E n Γ c e)
    (hc : c ≠ .bot) : CovVNativeHead E n Γ e := by
  cases c with
  | bot => exact (hc rfl).elim
  | lam rows => rw [CovWValueAction] at h; exact h.1
  | spine r us =>
      obtain ⟨ls, xs, hr, hn, _⟩ := covW_value_action_spine_iff.mp h
      exact ⟨_, hr, hn xs⟩
  | prop =>
      rw [CovWValueAction] at h
      obtain ⟨l, _, hr⟩ := h
      exact ⟨_, hr, normalR_sortCK2 Γ l⟩
  | sort =>
      rw [CovWValueAction] at h
      obtain ⟨l, _, hr⟩ := h
      exact ⟨_, hr, normalR_sortCK2 Γ l⟩
  | pi a rows =>
      rw [CovWValueAction] at h
      obtain ⟨D, B, hr⟩ := h
      exact ⟨_, hr, normalR_piCK2 Γ D B⟩

theorem covW_value_action_backward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (c : CptT) {e e' : Expr Nat} (hr : RedR (WhStepCK2 E n) Γ e e')
    (h : CovWValueAction E n Γ c e') : CovWValueAction E n Γ c e := by
  cases hc : c with
  | bot => rw [CovWValueAction]; trivial
  | lam rows =>
      simp only [hc, CovWValueAction] at h ⊢
      refine ⟨covV_native_head_backward hr h.1, ?_⟩
      intro s hs a ha
      exact covW_value_action_backward s.2
        (redR_appHead (readbackLaws_whStepCK2 E n) hr) (h.2 s hs a ha)
  | spine r us =>
      simp only [hc] at h ⊢
      obtain ⟨ls, xs, hh, hn, hx⟩ := covW_value_action_spine_iff.mp h
      exact covW_value_action_spine_iff.mpr ⟨ls, xs, redR_trans hr hh, hn, hx⟩
  | prop =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨l, hl, hh⟩ := h
      exact ⟨l, hl, redR_trans hr hh⟩
  | sort =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨l, hl, hh⟩ := h
      exact ⟨l, hl, redR_trans hr hh⟩
  | pi a rows =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨D, B, hh⟩ := h
      exact ⟨D, B, redR_trans hr hh⟩
termination_by sizeOf c
decreasing_by
  simp_wf
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := sizeOfT_snd_lt s
  simp only [hc, CptT.lam.sizeOf_spec]
  omega

theorem covW_value_action_lambda {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b : Expr Nat} {rows : List (List CptT × CptT)}
    (hb : ∀ s ∈ rows, ∀ a : Expr Nat,
      (∀ u ∈ s.1, CovWValueAction E n Γ u a) →
      CovWValueAction E n Γ s.2 (instantiate0 a b)) :
    CovWValueAction E n Γ (.lam rows) (.lam A b) := by
  rw [CovWValueAction]
  refine ⟨⟨_, .refl _, normalR_lamCK2 Γ A b⟩, ?_⟩
  intro s hs a ha
  exact covW_value_action_backward s.2 (redR_single (.ctx (.beta A b a)))
    (hb s hs a ha)

theorem covW_value_action_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {rows : List (List CptT × CptT)} {s : List CptT × CptT}
    (hf : CovWValueAction E n Γ (.lam rows) f) (hs : s ∈ rows)
    (ha : ∀ u ∈ s.1, CovWValueAction E n Γ u a) :
    CovWValueAction E n Γ s.2 (.app f a) := by
  rw [CovWValueAction] at hf
  exact hf.2 s hs a ha

theorem covW_value_action_app_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {r : Nat} {us : List CptT} {u : CptT}
    (hf : CovWValueAction E n Γ (.spine r us) f)
    (ha : CovWValueAction E n Γ u a) :
    CovWValueAction E n Γ (.spine r (us ++ [u])) (.app f a) := by
  obtain ⟨ls, xs, hr, hn, hx⟩ := covW_value_action_spine_iff.mp hf
  apply covW_value_action_spine_iff.mpr
  refine ⟨ls, xs ++ [a], ?_, hn, hx.append (.cons ha .nil)⟩
  rw [foldApps_snoc]
  exact redR_appHead (readbackLaws_whStepCK2 E n) hr

/-- Actual declared rigid heads supply the stronger spine clause directly. -/
theorem covW_value_action_rigid_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : RigidConst E r) (ls : List Level) :
    CovWValueAction E n Γ (.spine r []) (.const r ls) := by
  obtain ⟨hb, hnr⟩ := hr m hm
  have hb' : m.body = none := by
    rcases hb with hb | hc
    · exact hb
    · exact ctorNoBody_of_envWfT hW r m hm hc
  exact covW_value_action_spine_iff.mpr
    ⟨ls, [], .refl _, fun xs => covV_body_free_spine_normal hm hb' hnr ls xs, .nil⟩

/-- Native determinism aligns every demand vector with the same normal spine. -/
theorem covW_normal_reduct_unique {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e N₁ N₂ : Expr Nat}
    (h₁ : RedR (WhStepCK2 E n) Γ e N₁)
    (h₂ : RedR (WhStepCK2 E n) Γ e N₂)
    (hn₁ : NormalR (WhStepCK2 E n) Γ N₁)
    (hn₂ : NormalR (WhStepCK2 E n) Γ N₂) : N₁ = N₂ := by
  induction h₁ generalizing N₂ with
  | refl => exact (redR_of_normal hn₁ h₂).symm
  | step hs _ ih =>
      cases h₂ with
      | refl => exact (hn₂ _ hs).elim
      | step ht hr =>
          have he := detR_whStepCK2 hW Γ hs ht
          cases he
          exact ih hr hn₁ hn₂

/-- A realized constructor demand has one actual normal constructor spine.
All its demanded fields are realized by that spine's actual fields. -/
theorem covW_ctor_demand_actual_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e : Expr Nat} {r nparams : Nat}
    {uss : List (List CptT)}
    (hdem : ∀ c ∈ ctorDemandT r nparams uss, CovWValueAction E n Γ c e) :
    ∃ (ls : List Level) (params fields : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) (params ++ fields)) ∧
      NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) (params ++ fields)) ∧
      params.length = nparams ∧ fields.length = uss.length ∧
      CovWListDemands (CovWValueAction E n Γ) fields uss := by
  have hb := hdem _ (List.mem_cons_self _ _)
  obtain ⟨ls, xs, hr, hn, hx⟩ := covW_value_action_spine_iff.mp hb
  have hlen : xs.length = nparams + uss.length := by
    simpa only [List.length_append, List.length_replicate] using hx.length_eq
  have hle : nparams ≤ xs.length := by omega
  have hp : (xs.take nparams).length = nparams := by
    simp only [List.length_take, Nat.min_eq_left hle]
  have hf : (xs.drop nparams).length = uss.length := by
    rw [List.length_drop, hlen]
    omega
  refine ⟨ls, xs.take nparams, xs.drop nparams, ?_, ?_, hp, hf, ?_⟩
  · simpa only [List.take_append_drop] using hr
  · simpa only [List.take_append_drop] using hn xs
  · apply covW_fields_of_demand_vectors hf
    intro vec hvec
    have hm : .spine r (List.replicate nparams .bot ++ vec) ∈
        ctorDemandT r nparams uss :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vec, hvec, rfl⟩)
    obtain ⟨ls', ys, hr', hn', hy⟩ := covW_value_action_spine_iff.mp (hdem _ hm)
    have he := covW_normal_reduct_unique hW hr hr' (hn xs) (hn' ys)
    have hxy : xs = ys := (foldApps_const_inj he).2
    rw [← hxy] at hy
    have hy' : CovWListRealizes (CovWValueAction E n Γ)
        (xs.take nparams ++ xs.drop nparams) (List.replicate nparams .bot ++ vec) := by
      simpa only [List.take_append_drop] using hy
    exact CovWListRealizes.append_right (by simpa using hp) hy'

/-- The recursor's stored major-domain head identifies its family across
the legacy and schema witness formats. -/
theorem covW_legacy_schema_family_eq {E : ResolvedEnv}
    (v : IotaWitness E) (w : IotaWitnessS E) (hr : v.recRef = w.recRef) :
    v.famMember = w.famMember := by
  have hvr := v.hrec
  rw [hr] at hvr
  have hrec : v.recMember = w.recMember :=
    Option.some.inj (hvr.symm.trans w.hrec)
  have hpv := v.hpeelRec
  have hpw := w.hpeelRec
  rw [v.hnmin] at hpv
  rw [w.hnmin, ← hrec] at hpw
  have hdoms : v.recDoms = w.recDoms :=
    congrArg Prod.fst (Option.some.inj (hpv.symm.trans hpw))
  have hidx : v.nparams + 1 + v.nMinors + v.nindices =
      w.nparams + 1 + w.nMinors + w.nindices := by
    have hv := v.hnmin
    have hw := w.hnmin
    rw [← hrec] at hw
    omega
  have hmaj := v.hmajorTy
  rw [hidx, hdoms] at hmaj
  have he := Option.some.inj (hmaj.symm.trans w.hmajorTy)
  have href : v.familyRef = w.familyRef :=
    (Expr.const.inj (foldApps_const_inj he).1).1
  have hmem := v.hfam
  rw [href] at hmem
  exact Option.some.inj (hmem.symm.trans w.hfam)

/-- Non-proposition recursion cannot enter either native non-strict K class. -/
theorem covW_nonprop_no_native_k {E : ResolvedEnv} (w : IotaWitnessS E)
    (hn : ¬ PropFamilyS w) :
    (¬ KFreeRec E w.recRef) ∧ (¬ KProjRec E w.recRef) := by
  constructor
  · rintro ⟨v, hr, hv⟩
    apply hn
    have hp : piBody v.famMember.mtype = .sort .zero := hv.2.2
    rw [covW_legacy_schema_family_eq v w hr] at hp
    exact hp
  · rintro ⟨v, hr, hv⟩
    apply hn
    have hp : piBody v.famMember.mtype = .sort .zero := hv.2.2.1
    rw [covW_legacy_schema_family_eq v w hr] at hp
    exact hp

/-- An admitted schema is instantiated at actual native lists, with its
universe arity and both argument counts retained explicitly. -/
def covW_iota_action_instance {E : ResolvedEnv} (w : IotaWitnessS E)
    (ls lsC : List Level) (pre params fields : List (Expr Nat))
    (hls : ls.length = w.recMember.arity)
    (hpre : pre.length = w.preMajor.length)
    (hparams : params.length = w.nparams)
    (hfields : fields.length = w.fields.length) : IotaWitnessS E :=
  { w with
    ls := ls
    lsC := lsC
    preMajor := pre
    fields := fields
    ctorParams := params
    hctorParams := hparams
    hnpar := by simpa only [hfields] using w.hnpar
    hpre := hpre.trans w.hpre
    hpeel := by simpa only [hfields] using w.hpeel
    hlsLen := hls
    hschema := by simpa only [hfields] using w.hschema
    hstable := by
      intro E' hE'
      simpa only [hfields] using w.hstable E' hE'
    hschemaScope := by simpa only [hfields] using w.hschemaScope }

theorem covW_redR_recMajor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {m : CheckedMember} {ls : List Level} {pre : List (Expr Nat)}
    {x x' : Expr Nat} (hm : E.members r = some m)
    (hrec : m.mclass = .recursorM)
    (hlen : pre.length + 1 = piCount m.mtype)
    (hnK : ¬ KFreeRec E r) (hnP : ¬ KProjRec E r)
    (hr : RedR (WhStepCK2 E n) Γ x x') :
    RedR (WhStepCK2 E n) Γ (recCall (.const r ls) pre x)
      (recCall (.const r ls) pre x') := by
  induction hr with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.recMajor hm hrec hlen hnK hnP hs) ih

/-- The ordinary recursor case uses the actual major's normal fields and
an actual schema-iota step. Its remaining action premise is exactly the
schema-observation induction hypothesis at those fields. -/
theorem covW_value_action_recursor_call {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) (w : IotaWitnessS E) (ls : List Level)
    (hls : ls.length = w.recMember.arity) (hnp : ¬ PropFamilyS w)
    {pre : List (Expr Nat)} {major : Expr Nat} {uss : List (List CptT)} {c : CptT}
    (hpre : pre.length = w.preMajor.length) (hflds : uss.length = w.fields.length)
    (hmaj : ∀ d ∈ ctorDemandT w.ctorRef w.nparams uss,
      CovWValueAction E n Γ d major)
    (hschema : ∀ fields : List (Expr Nat), fields.length = w.fields.length →
      CovWListDemands (CovWValueAction E n Γ) fields uss →
      CovWValueAction E n Γ c
        (instPrefix (pre ++ fields) (instantiateLevels ls w.schema))) :
    CovWValueAction E n Γ c (recCall (.const w.recRef ls) pre major) := by
  obtain ⟨lsC, params, fields, hr, _, hp, hf, hfields⟩ :=
    covW_ctor_demand_actual_fields hW hmaj
  have hflen : fields.length = w.fields.length := hf.trans hflds
  let w' := covW_iota_action_instance w ls lsC pre params fields hls hpre hp hflen
  have hi : WhStepCK2 E n Γ (iotaLhsOfS w') (iotaRhsOfS w') :=
    .ctx (.iota (.ofUS w'))
  change WhStepCK2 E n Γ
    (recCall (.const w.recRef ls) pre
      (foldApps (.const w.ctorRef lsC) (params ++ fields)))
    (instPrefix (pre ++ fields) (instantiateLevels ls w.schema)) at hi
  have hn := covW_nonprop_no_native_k w hnp
  have hlen : pre.length + 1 = piCount w.recMember.mtype := by
    rw [hpre, w.hpre]
    exact w.hnmin
  have hmajor := covW_redR_recMajor (ls := ls) w.hrec w.hrecK hlen hn.1 hn.2 hr
  exact covW_value_action_backward c (redR_trans hmajor (redR_single hi))
    (hschema fields hflen hfields)

/-- Currying discharges proper prefixes separately from the final action. -/
theorem covW_value_action_curry {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (uss : List (List CptT)) (c : CptT) (f : Expr Nat)
    (hp : ∀ args : List (Expr Nat), args.length < uss.length →
      CovVNativeHead E n Γ (foldApps f args))
    (hout : ∀ args : List (Expr Nat),
      CovWListDemands (CovWValueAction E n Γ) args uss →
      CovWValueAction E n Γ c (foldApps f args)) :
    CovWValueAction E n Γ (curryStepT uss c) f := by
  induction uss generalizing f with
  | nil => exact hout [] .nil
  | cons us uss ih =>
      rw [curryStepT, CovWValueAction]
      refine ⟨hp [] (by simp), ?_⟩
      intro s hs a ha
      have he : s = (us, curryStepT uss c) := List.mem_singleton.mp hs
      subst s
      apply ih (.app f a)
      · intro args hlen
        exact hp (a :: args)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hlen)
      · intro args hargs
        exact hout (a :: args) (.cons ha hargs)

/-- The complete non-proposition recursor table is supplied from the
schema induction hypothesis. Correct recursor universe arity is explicit;
no matching-head or normal-reduct supplier is assumed. -/
theorem covW_value_action_recursor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) (w : IotaWitnessS E) (ls : List Level)
    (hls : ls.length = w.recMember.arity) (hnp : ¬ PropFamilyS w)
    {us_pre us_fields : List (List CptT)} {c : CptT}
    (hpre : us_pre.length = w.preMajor.length)
    (hflds : us_fields.length = w.fields.length)
    (hschema : ∀ pre fields : List (Expr Nat),
      CovWListDemands (CovWValueAction E n Γ) pre us_pre →
      CovWListDemands (CovWValueAction E n Γ) fields us_fields →
      CovWValueAction E n Γ c
        (instPrefix (pre ++ fields) (instantiateLevels ls w.schema))) :
    CovWValueAction E n Γ
      (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
      (.const w.recRef ls) := by
  apply covW_value_action_curry
  · intro args hlen
    have htotal : (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]).length =
        piCount w.recMember.mtype := by
      simp only [List.length_append, List.length_singleton]
      rw [hpre, w.hpre]
      exact w.hnmin
    exact ⟨_, .refl _, normalR_recPrefixCK2 hW w.hrec w.hrecK Γ ls args
      (by rw [← htotal]; omega)⟩
  · intro args hargs
    obtain ⟨pre, major, rfl, hps, hm⟩ := CovWListDemands.snoc_inv us_pre hargs
    have hcall := covW_value_action_recursor_call (c := c)
      hW w ls hls hnp (hps.length_eq.trans hpre) hflds hm
      (fun fields _ hfs => hschema pre fields hps hfs)
    simpa only [recCall_eq_app, foldApps_snoc] using hcall

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_VALUE_ACTIONS_ROOTS
#print axioms CovWListRealizes
#print axioms CovWListRealizes.length_eq
#print axioms CovWListRealizes.getD
#print axioms CovWListRealizes.of_getD
#print axioms CovWListRealizes.append
#print axioms CovWListRealizes.append_right
#print axioms CovWListDemands
#print axioms CovWListDemands.length_eq
#print axioms CovWListDemands.append_inv
#print axioms CovWListDemands.snoc_inv
#print axioms covW_fields_of_demand_vectors
#print axioms CovWValueAction
#print axioms covW_value_action_spine_iff
#print axioms covW_value_action_head
#print axioms covW_value_action_backward
#print axioms covW_value_action_lambda
#print axioms covW_value_action_app
#print axioms covW_value_action_app_spine
#print axioms covW_value_action_rigid_const
#print axioms covW_normal_reduct_unique
#print axioms covW_ctor_demand_actual_fields
#print axioms covW_legacy_schema_family_eq
#print axioms covW_nonprop_no_native_k
#print axioms covW_iota_action_instance
#print axioms covW_redR_recMajor
#print axioms covW_value_action_recursor_call
#print axioms covW_value_action_curry
#print axioms covW_value_action_recursor
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_VALUE_ACTIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
