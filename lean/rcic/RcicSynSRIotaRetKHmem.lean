import rcic.RcicSynTableKCompat
import rcic.RcicSynStepFieldsDeltaIota

namespace Rcic.Syn

open Rcic.Declarative

/-! # Row 6 at `tableOfK` — the `hmem` closer

`RcicSynSRIotaRetK` (glm-sr3-iotaretk) re-told `IotaRetainedSimulation` for the
K-rule: at a gated singleton-`Prop` large-eliminating group `iotaRulesKOf` emits
the nullary `[iotaKRule rr nargs' nparams' nindices' nfields']` instead of the
ctor-major rules, so the simulation's `croot` is `CRoot.bare`-shaped — and the
sole table-dependent input was `IotaBareRoot.hmem`, the bare rule's membership
in the table.

This module discharges `hmem` at `tableOfK hW` by `EnvWfT` induction
(`iotaRulesKOf_sub_tableOfK`): every recursor-class member `rr` of `E` is
installed by exactly one `.group` node, whose `iotaRulesKOf` emission is a
sublist of `tableOfK hW` — estar's `mem_tableOfK_*`-style membership fact,
packaged **existentially at the node's own `(f, fm, ctors)`**. Composed with
`bare_mem_iotaRulesKOf`/`iotaKRuleOf_spec`, the retained simulation's root
becomes an `RStep` receipt (`IotaKHeadStep`): `iotaKRule.nargs = fun _ => 0`,
so `CRoot.bare` fires at the bare `const rr ls` head and `rStep_appN_head`
carries the step through the erased application spine — exactly the endpoint
shape `iota_erasure_from_answers` consumes as one `EStep` (`ConvMod.fwd (.inl _)`).

The sole remaining table-dependent datum is the `iotaKRuleOf` emission spec
**at the found node's `(f, fm, ctors)`** — the named inhabited boundary
("the gate case at `rr`'s own group"): the caller's `IotaWitness` must identify
its `familyRef`/constructor list with the node's `f'`/`ctors'` (membership
gives only `rr = rr'`). That bridge is `iotaRetainedRStep_tableOfK`'s
∃-interface; the `matchL`/`beta`/`matchR` legs are unchanged from the
ctor-major telling. -/

/-! ### §1 The membership discharge: `EnvWfT` induction -/

/-- An `iotaKRuleOf` emission is a member of `iotaRulesKOf` (the gated
    branch's singleton output). -/
theorem iotaKRuleOf_mem_iotaRulesKOf {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : iotaKRuleOf f fm ctors rr rm = some ρ) :
    ρ ∈ iotaRulesKOf f fm ctors rr rm := by
  unfold iotaRulesKOf
  rw [h]
  exact List.mem_singleton_self _

/-- A member lookup at a `GroupMembersT` chain's end descends to the chain's
    base when the ref was not installed by the chain. -/
theorem groupMembersT_lookup_outside {S E₀ E' : ResolvedEnv}
    {l : List (Nat × CheckedMember)} (g : GroupMembersT S E₀ l E')
    {r : Nat} {m : CheckedMember} (hres : E'.members r = some m)
    (hnot : ∀ p ∈ l, p.1 ≠ r) :
    E₀.members r = some m := by
  induction g with
  | nil E => exact hres
  | cons E r₀ m₀ rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      have hmid : (extendEnv E r₀ m₀).members r = some m :=
        ih hres fun p hp => hnot p (List.mem_cons_of_mem _ hp)
      have hne : r ≠ r₀ := fun h =>
        (hnot ⟨r₀, m₀⟩ (List.mem_cons_self _ _)) h.symm
      rwa [members_extend_ne E m₀ hne] at hmid

/-- `hmem` discharged, ∃-packaged at the node's own data: every
    recursor-class member `rr` of `E` is installed by some `.group` node of
    `hW`, and that node's `iotaRulesKOf` emission is a sublist of
    `tableOfK hW`. The returned `(f, fm, ctors)` are the node's — the
    inhabited boundary for callers is the `iotaKRuleOf` spec at THIS data. -/
theorem iotaRulesKOf_sub_tableOfK {E : ResolvedEnv} :
    (hW : EnvWfT E) → {rr : Nat} → {rm : CheckedMember} →
    E.members rr = some rm → rm.mclass = .recursorM →
    ∃ (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember)),
      ∀ ρ, ρ ∈ iotaRulesKOf f fm ctors rr rm → ρ ∈ tableOfK hW := by
  intro hW
  induction hW with
  | empty => intro rr rm hres _; cases hres
  | «axiom» E r A u hE _ _ _ _ ih =>
      intro rr rm hres hrec
      rw [tableOfK_axiom]
      by_cases hrr : rr = r
      · subst hrr
        rw [members_extend_self] at hres
        obtain rfl := (Option.some.inj hres).symm
        exact MemberClass.noConfusion hrec
      · rw [members_extend_ne _ _ hrr] at hres
        exact ih hres hrec
  | definition E r A v u hE _ _ _ _ _ _ _ ih =>
      intro rr rm hres hrec
      rw [tableOfK_definition]
      by_cases hrr : rr = r
      · subst hrr
        rw [members_extend_self] at hres
        obtain rfl := (Option.some.inj hres).symm
        exact MemberClass.noConfusion hrec
      · rw [members_extend_ne _ _ hrr] at hres
        obtain ⟨f, fm, ctors, hsub⟩ := ih hres hrec
        exact ⟨f, fm, ctors, fun ρ hρ => List.mem_cons_of_mem _ (hsub ρ hρ)⟩
  | «thm» E r A p hE _ _ _ _ _ _ _ ih =>
      intro rr rm hres hrec
      rw [tableOfK_thm]
      by_cases hrr : rr = r
      · subst hrr
        rw [members_extend_self] at hres
        obtain rfl := (Option.some.inj hres).symm
        exact MemberClass.noConfusion hrec
      · rw [members_extend_ne _ _ hrr] at hres
        exact ih hres hrec
  | «opaque» E r A v u hE _ _ _ _ _ _ _ ih =>
      intro rr rm hres hrec
      rw [tableOfK_opaque]
      by_cases hrr : rr = r
      · subst hrr
        rw [members_extend_self] at hres
        obtain rfl := (Option.some.inj hres).symm
        exact MemberClass.noConfusion hrec
      · rw [members_extend_ne _ _ hrr] at hres
        exact ih hres hrec
  | group E₀' f' fm' ctors' rr' rm' E' hE' hfam' hctors' hrec' hmem' ih =>
      intro rr rm hres hrec
      rw [tableOfK_group]
      by_cases hrr : rr ∈ (((f', fm') :: ctors' ++ [(rr', rm')]).map Prod.fst)
      · rcases List.mem_map.mp hrr with ⟨⟨pa, pb⟩, hp, hpa⟩
        have hpa' : pa = rr := hpa
        have hpm : E'.members pa = some pb := groupMembersT_lookup hmem' hp
        rw [hpa'] at hpm
        have hpb : pb = rm := Option.some.inj (hpm.symm.trans hres)
        rcases List.mem_cons.mp hp with hph | hpt
        · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp hph
          rw [hpb] at hfam'
          exact MemberClass.noConfusion (hfam'.symm.trans hrec)
        · rcases List.mem_append.mp hpt with hpc | hpr
          · have hcm := hctors' ⟨pa, pb⟩ hpc
            rw [hpb] at hcm
            exact MemberClass.noConfusion (hcm.symm.trans hrec)
          · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp (List.mem_singleton.mp hpr)
            subst hpa'
            subst hpb
            exact ⟨f', fm', ctors', fun ρ hρ => List.mem_append_left _ hρ⟩
      · have hnot : ∀ p ∈ (f', fm') :: ctors' ++ [(rr', rm')], p.1 ≠ rr :=
          fun p hp heq => hrr (List.mem_map.mpr ⟨p, hp, heq⟩)
        have h0 : E₀'.members rr = some rm :=
          groupMembersT_lookup_outside hmem' hres hnot
        obtain ⟨f, fm, ctors, hsub⟩ := ih h0 hrec
        exact ⟨f, fm, ctors, fun ρ hρ => List.mem_append_right _ (hsub ρ hρ)⟩

/-! ### §2 The K-side root receipt and `RStep` simulation -/

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- `IotaBareRoot` lifted to `RStep`: `CRoot.bare` fires at the rule's
    `nargs`-prefix `args`; `rStep_appN_head` then carries the step through the
    rest of the erased application spine. For `iotaKRule` (`nargs = fun _ => 0`)
    `args` is forced `[]` — the rule fires at the bare `const rr ls` head and
    the whole erased redex spine rides along. -/
structure IotaKHeadStep (tbl : List CRule) (el erhs : ETm) : Type where
  rule : CRule
  hmem : rule ∈ tbl
  hbare : rule.major = none
  ls : List Level
  args : List ETm
  spine : List ETm
  hlen : args.length = rule.nargs ls
  hel : el = ETm.appN (.const rule.head ls) (args ++ spine)
  herhs : erhs = ETm.appN (rule.rhs ls []) (args ++ spine)

/-- The receipt is an `RStep`: bare root step at the `args`-prefix, congruence
    through `spine`. -/
theorem IotaKHeadStep.toRStep {tbl : List CRule} {el erhs : ETm}
    (k : IotaKHeadStep tbl el erhs) : RStep tbl el erhs := by
  obtain ⟨rule, hmem, hbare, ls, args, spine, hlen, hel, herhs⟩ := k
  cases hel
  cases herhs
  rw [ETm.appN_append, ETm.appN_append]
  exact rStep_appN_head (.cr (.bare hmem hbare ls args hlen)) spine

/-- `IotaBareRoot.hmem` discharged, as a `Prop`-valued ∃ at the found node's
    own `(f, fm, ctors)`: whatever `iotaKRuleOf` emits at the node is in
    `tableOfK hW`. (`∀ ρr, spec → ρr ∈ tableOfK hW` is `Prop`; the
    `IotaKHeadStep`/`IotaRetainedRStep` receipts are `Type` and are built by
    the plain functions below.) -/
theorem iotaKRuleOf_mem_tableOfK {E : ResolvedEnv} (hW : EnvWfT E)
    {rr : Nat} {rm : CheckedMember}
    (hres : E.members rr = some rm) (hrec : rm.mclass = .recursorM) :
    ∃ (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember)),
      ∀ {ρr : CRule}, iotaKRuleOf f fm ctors rr rm = some ρr →
        ρr ∈ tableOfK hW := by
  obtain ⟨f', fm', ctors', hsub⟩ := iotaRulesKOf_sub_tableOfK hW hres hrec
  exact ⟨f', fm', ctors', fun {ρr} h => hsub ρr (iotaKRuleOf_mem_iotaRulesKOf h)⟩

/-- The K rule's `IotaKHeadStep` at `args = []` (`iotaKRule.nargs = fun _ => 0`
    — bare `const rr ls` head firing, spine riding through `appN`). -/
def iotaKHeadStep_iotaKRule {tbl : List CRule}
    {rr nargs nparams nindices nfields : Nat}
    (ls : List Level) (spine : List ETm)
    (hmem : iotaKRule rr nargs nparams nindices nfields ∈ tbl) :
    IotaKHeadStep tbl (ETm.appN (.const rr ls) spine)
      (ETm.appN ((iotaKRule rr nargs nparams nindices nfields).rhs ls []) spine) :=
  ⟨iotaKRule rr nargs nparams nindices nfields, hmem, rfl, ls, [], spine,
    rfl, rfl, rfl⟩

/-- `IotaRetainedSimulation` re-told for `tableOfK`: the rule-root leg is an
    `RStep` receipt (`IotaKHeadStep.toRStep`), since `iotaKRule`'s bare firing
    at `const rr ls` plus `appN`-congruence is `RStep`, not `CRoot`, at the
    erased redex. `iota_erasure_from_answers` consumes either shape — a `CRoot`
    is wrapped `ConvMod.fwd (.inl (.cr _))`; an `RStep` goes `.inl` directly. -/
structure IotaRetainedRStep (tbl : List CRule) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Type where
  el : ETm
  erhs : ETm
  er : ETm
  matchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el
  kstep : RStep tbl el erhs
  beta : RStar (RStep tbl) erhs er
  matchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)

/-- `RcicSynP2Iota.iota_erasure_from_answers` at an `RStep` root: identical
    chain, `.inl hstep` instead of `.inl (.cr _)`. -/
theorem iota_erasure_from_answers_rstep {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {σ : Level → Level} {ρ : List Disp} {el erhs er : ETm}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (qCLL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hlhs.eps σ ρ))
    (qCLR : ConvMod (EStep tbl) LvlEq (hrhs.eps σ ρ) (dr.eps σ ρ))
    (_qPL : PBit σ ρ hlhs hlhs.reg.2) (_qPR : PBit σ ρ hrhs hlhs.reg.2)
    (hmatchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el)
    (hstep : RStep tbl el erhs)
    (hbeta : RStar (RStep tbl) erhs er)
    (hmatchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) := by
  have hchain : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) :=
    qCLL.trans (hmatchL.trans
      ((ConvMod.fwd (.inl hstep)).trans
        ((convMod_of_rstar_estep hbeta).trans (hmatchR.trans qCLR))))
  simpa [ES, CvP.dl, CvP.dr] using hchain

/-- `StepSuppliers.es_iota_retained` closed under `IotaRetainedRStep`:
    `qPL`/`qPR` via `Issues.occ_pb` at the `regOcc` path, `qCLL`/`qCLR` via
    `iota_issued_cl_left`/`iota_issued_cl_right` — `StepIH` discharges all
    four; only the simulation witnesses are premises. -/
theorem iota_retained_caseStep_of_rstep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (_hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (ksim : IotaRetainedRStep tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  intro hq ih
  have qPL : PBit σ ρ hlhs hlhs.reg.2 :=
    iota_issued_pb_hlhs_of_reg_occ Aw tbl w hlhs hrhs dl dr S σ ρ pReg regOcc hq ih
  have qPR : PBit σ ρ hrhs hlhs.reg.2 :=
    iota_issued_pb_hrhs_of_reg_occ Aw tbl w hlhs hrhs dl dr S σ ρ pReg regOcc hq ih
  have qCLL : CL tbl σ ρ dl hlhs :=
    iota_issued_cl_left Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  have qCLR : CL tbl σ ρ hrhs dr :=
    iota_issued_cl_right Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  exact iota_erasure_from_answers_rstep w hlhs hrhs dl dr qCLL qCLR qPL qPR
    ksim.matchL ksim.kstep ksim.beta ksim.matchR

/-- `es_iota_retained` under `IotaRetainedRStep` — the K-side `StepSuppliers`
    row. -/
theorem es_iota_retained_field_of_rstep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (ksim : IotaRetainedRStep tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  iota_retained_caseStep_of_rstep Aw tbl w hlhs hrhs dl dr S σ ρ hrel pReg regOcc ksim

/-- Same-endpoints form (`dl = hlhs`, `dr = hrhs`): `pReg`/`regOcc` are still
    required for `qPL`/`qPR` — only the simulation witnesses differ. -/
theorem es_iota_retained_field_same_endpoints_of_rstep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (ksim : IotaRetainedRStep tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  iota_retained_caseStep_of_rstep Aw tbl w hlhs hrhs dl dr S σ ρ hrel pReg regOcc ksim

/-! ### §3 `hmem` composed: `IotaRetainedRStep` at `tableOfK hW` -/

/-- The composed receipt: at a bare K rule already known in the table
    (`hmem`, typically from `iotaKRuleOf_mem_tableOfK` + `iotaKRuleOf_spec`),
    the erased head shape + `matchL`/`beta`/`matchR` legs give
    `IotaRetainedRStep`. -/
def iotaRetainedRStep_iotaKRule {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {σ : Level → Level} {ρ : List Disp}
    {rr nargs nparams nindices nfields : Nat}
    (ls : List Level) (spine : List ETm) (er : ETm)
    (matchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ)
      (ETm.appN (.const rr ls) spine))
    (hmem : iotaKRule rr nargs nparams nindices nfields ∈ tbl)
    (beta : RStar (RStep tbl)
      (ETm.appN ((iotaKRule rr nargs nparams nindices nfields).rhs ls []) spine) er)
    (matchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    IotaRetainedRStep tbl hlhs hrhs σ ρ :=
  ⟨ETm.appN (.const rr ls) spine,
   ETm.appN ((iotaKRule rr nargs nparams nindices nfields).rhs ls []) spine,
   er, matchL, (iotaKHeadStep_iotaKRule ls spine hmem).toRStep, beta, matchR⟩

/-- **Row 6 at `tableOfK hW` — `hmem` discharged.** `es_iota_retained` at
    `tableOfK hW` from the erased head shape + `matchL`/`beta`/`matchR` legs;
    the only table-dependent residual is the ∃-packaged `iotaKRuleOf` spec at
    the found node's `(f, fm, ctors)` — the inhabited boundary "the gate case
    at `rr`'s own group" (caller's `IotaWitness` must identify
    `familyRef`/`ctors` with the node's `f'`/`ctors'`; membership alone fixes
    only `rr`). When that bridge is inhabited — e.g. a witness built from the
    same group — this is a `CaseStep` with no K-side premise. -/
theorem es_iota_retained_field_tableOfK
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hW : EnvWfT E)
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    {rr : Nat} {rm : CheckedMember}
    (hres : E.members rr = some rm) (hrec : rm.mclass = .recursorM)
    (ls : List Level) (spine : List ETm) (er : ETm)
    (matchL : ConvMod (EStep (tableOfK hW)) LvlEq (hlhs.eps σ ρ)
      (ETm.appN (.const rr ls) spine))
    (beta : ∀ (nargs nparams nindices nfields : Nat),
      RStar (RStep (tableOfK hW))
        (ETm.appN ((iotaKRule rr nargs nparams nindices nfields).rhs ls []) spine) er)
    (matchR : ConvMod (EStep (tableOfK hW)) LvlEq er (hrhs.eps σ ρ)) :
    ∃ (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember)),
      ∀ {ρr : CRule}, iotaKRuleOf f fm ctors rr rm = some ρr →
        CaseStep Aw (tableOfK hW)
          (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  obtain ⟨f', fm', ctors', hnode⟩ := iotaKRuleOf_mem_tableOfK hW hres hrec
  refine ⟨f', fm', ctors', ?_⟩
  intro ρr hgate
  obtain ⟨cr', cm', _, _, hρ⟩ := iotaKRuleOf_spec hgate
  subst hρ
  exact es_iota_retained_field_of_rstep Aw (tableOfK hW) w hlhs hrhs dl dr S σ ρ
    hrel pReg regOcc
    (iotaRetainedRStep_iotaKRule ls spine er matchL (hnode hgate)
      (beta (iotaKNargs fm' rm) (iotaKNparams fm' rm) (iotaNindices rm)
        (iotaKNfields fm' cm' rm))
      matchR)

end Rcic.Syn
