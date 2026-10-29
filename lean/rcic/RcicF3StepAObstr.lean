import rcic.RcicF3TierGroup
import rcic.RcicF3KTWFixtureA
import rcic.RcicF3DIota
import rcic.RcicF3GroupSound

/-!
# `StepAG` from the obstruction side: the exact content as two named cells

`StepAG P K` (`RcicF3TierGroup`) owes the fold's group step
(`GroupStepAt`: `GInv` transfer) at every group with a `PendA`
(function-recursive) node.  This module measures what that debt IS, on
the same pattern as `StepW`'s (`RcicF3StepWMin`): no producer is attempted
(glm-rk03 owns that lane); instead the arm is reduced to its exact
named cells, the cells are instantiated at the on-tree fixture `wEnv`,
and the decidable half is packaged as a checked side condition.

## The decomposition (measured on `devin/f3-tiergroup`)

`gInv_group_ofAt` (`RcicF3MainG`) consumes the direct-fields row
`hrfN : ∀ i, RecFieldsDirect …` in exactly two places:

1. `hclsF` → `famLim_fix` → the family fixed point `hfix` → `GroupFaith`
   → family/constructor member soundness.  At a `PendA` group the row
   fails at the Π-recursive field, and with it the raw-role fixed point.
   The KT lane's replacement (`famKT_fix`, `#8055`) is delivered under the
   semantic `hN` (`w_nonIR` at the fixture) — leaving ONE pure-model cell:
   the faithful raw-role family table agrees with `famKT`
   (`FamFixW` below; equivalently `famLim ≈ famKT`, the lfp-agreement
   bridge `FamKTBridge`; `famFixW_of_bridge`).
2. the `RecStepCtx`/`hrf` premises of the recursor package
   (`MemberSound` at the recursor + `IotaAt` there).  Membership is
   delivered at the KT table (`recVal_mem_rec_KTA`; `w_recVal_mem`
   consumes the same `FamFixW` cell).  ι is NOT delivered for class A —
   but it collapses: an `IotaWitness` bears `analyzeFields = some`, and a
   Π-recursive field admits no analysis (`supField_noKind` by `rfl`), so
   **ι at `wEnv`'s recursor is vacuous, unconditionally**
   (`iotaAt_wEnv_vacuous`).  Generically the residue is the
   witness-local cell `WitDirect` (`iota_at_of_witDirect`), which the
   decidable check `CtorWitOK` certifies.

So the A debt is: `FamFixA` (pure model, per group) + `WitDirect`
(witness-shape, decidable-checkable; empty at `wEnv`).  Nothing else:
the family/constructor soundness and the membership are composition
once the cells hold.

Named residues: `[rcic-f3-stepa-famfix]` (the `famLim ≈ famKT` bridge,
stated as `FamKTBridge`), `[rcic-f3-stepa-witness-shapes]` (a
`CtorWitOK` refusal: a constructor whose fields both bear an `FnRec`
shape and an `analyzeFields` classification).

Axioms of every sealed declaration ⊆ {`propext`, `Quot.sound`}.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAObstr

open Rcic.Declarative Rcic.Model.PS Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup

/-! ## §1 the ι cell: witness shapes are direct -/

/-- **The witness-shape cell at a group**: the group's field analysis
assigns no function-recursive shape at any constructor — this is
`iota_at_D`'s `NoFunRec` premise weakened to the constructor list, which
by `iota_align` covers every ι witness's own constructor.  It is the
CHECKED side condition: a finite scan over the group's finitely many
constructors and their finite `shapesAt` lists against decidable
`FieldShape` equality (refused by name: the failing constructor and
shape). -/
def WitDirect {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ (j : Fin node.a.constructors.length) (s : FieldShape), s ∈ node.h14.shapesAt j →
    s = .nonrecursive ∨ s = .recursive 0

/-- **The checked condition, named for refusal**: `CtorWitOK` is `WitDirect`
under the group's own data — decidable at the group (finite lists,`FieldShape` equality), refused by constructor index and shape when it
fails (named residue `[rcic-f3-stepa-witness-shapes]`). -/
def CtorWitOK {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop := WitDirect node

/-- **ι at a `PendA` group's recursor from the witness-shape cell**: the
`iota_at_gen_pt` pattern with the direct-fields row derived AT THE
WITNESS'S OWN CONSTRUCTOR — the witness's `analyzeFields` certificate
plus `recFieldsDirect_of_analyzeFields` plus the cell's shape fact.  The
row is owed nowhere else: a constructor with no witness never reaches
the kernel lemma. -/
theorem iota_at_of_witDirect (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E E' Efin : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m)
    (hrm : E'.members rr = some rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (hop : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none)
    (hWit : WitDirect node)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    (hpf : ∀ (E'' : ResolvedEnv), (∀ r m, E''.members r = some m → Efin.members r = some m) →
      ∀ (w : IotaWitness E''), w.recRef = rr → ∀ (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
        (ρ : Nat → PSet.{4}) (hl : HasTyT E'' n Γ (iotaLhsOf w) T), HSoundT (mkM P μ) σ hl →
        (∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop), Good (mkM P μ) N Lv ∧ LOKt σ N K hl) →
        Fits (mkM P μ) σ Γ ρ → UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length, w.ctorIdx = i.val → w.recMember = rm →
        w.ctorMember = node.a.constructors[i.val] → w.fields.length = (node.a.constructorViews i).fields.length →
        ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (((∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
        IotaAgree (mkM P μ) σ ρ node.a w i)) ∨
        ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨hnp, hnM, _, hfr⟩ := iota_align node.a w hwr hm
  have hjk : w.ctorIdx < node.a.constructors.length := by have := w.hidx; omega
  let j : Fin node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = node.a.family.ref + 1 + j.val := by rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := node.a.constructorsPresent j
    have h3 := hsubF _ _ (node.sub _ _ (members_extend_preserved node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  -- the direct-fields row at the witness's own constructor
  have hrf : RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length
      (node.a.constructorViews j).fields 0 := by
    have hst := (node.a.constructorViews j).storedType
    have hcpl := (node.a.constructorViews j).parameterCount
    have hctm : w.ctorMember.mtype = policyPi ((node.a.constructorViews j).parameters ++
        (node.a.constructorViews j).fields)
        (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
          (policyParameterLocals (node.a.constructorViews j).parameters.length
            (node.a.constructorViews j).fields.length ++
            (node.a.constructorViews j).resultIndices)) := by rw [hcm]; exact hst
    have hnpar := w.hnpar
    rw [hctm, PSet.piCount_policyPi, PSet.piCount_foldApps _ (fun _ _ h => Expr.noConfusion h),
      List.length_append] at hnpar
    have hpeel := w.hpeel
    rw [hctm, show w.nparams + w.fields.length = ((node.a.constructorViews j).parameters ++
      (node.a.constructorViews j).fields).length by rw [List.length_append]; omega,
      PSet.peelPis_policyPi] at hpeel
    have hdoms : w.ctorDoms = (node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields :=
      (congrArg Prod.fst (Option.some.inj hpeel)).symm
    have hkinds := w.hkinds
    rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
    exact recFieldsDirect_of_analyzeFields hFF hop _ _ (node.h14.analyzed j) (hWit j) hkinds
  have huni : evalTotal (σOf (w.ls.map (evalTotal σ))) node.a.family.resultLevel = 0 ↔
      evalTotal (σOf (w.lsC.map (evalTotal σ))) node.a.family.resultLevel = 0 := by
    rcases selection_uniform node.a with hp | ht
    · exact ⟨fun _ => hp _, fun _ => hp _⟩
    · exact ⟨fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _)),
        fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _))⟩
  have hctor0 := hG.ctor j (w.lsC.map (evalTotal σ))
  rw [nfOf_famDataOf] at hctor0
  have e : w.ctorRef = f + 1 + j.val := by rw [hcref, node.fam]
  have hctor : Equiv (μ w.ctorRef (w.lsC.map (evalTotal σ)))
      (piLam (mkM P μ) (σOf (w.lsC.map (evalTotal σ))) (ctorEnd (mkM P μ) (σOf (w.lsC.map (evalTotal σ)))
        (famDataOf node.a) j.val (node.a.constructorViews j).fields.length) (fun _ => pempty)
        (node.a.constructors[j.val]).mtype) := by rw [e]; exact hctor0
  exact iota_group W4 node.a w hwr hm σ ρ (hG.recur _) (groupFaith_famAt P hG _) j rfl hcm hctor huni
    hrf (hlvC j)
    (fun h0 hpol => by
      rcases hpf E'' hsub w hwr σ n Γ T ρ hl il hN hfit (selection_prop node.a _ h0 hpol).1 hpol j rfl hm hcm
          (witness_fields_length node.a w hwr hm j hcm) with
        ⟨h1, ⟨h2, h3, h4⟩ | hag⟩ | hemp
      · refine Or.inl ⟨h1, Or.inl ⟨h2, h3, h4 _ fun v hv => ?_⟩⟩
        obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
        exact hls l hl'
      · exact Or.inl ⟨h1, Or.inr hag⟩
      · exact Or.inr (hemp _))
    (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr

/-! ## §2 the ι cell is EMPTY at the `wEnv` fixture -/

/-- **No ι witness at `W`'s recursor in any sub-environment of any
extension** — `wIotaWitness_nokind` lifted from the extension form to
the `IotaAt` shape.  A sub-environment `E''` identifies its members
with `wEnv`'s through the common extension `Efin`; the witness's own
`hfam`/`hctor`/`hrec` force exactly the refs the case split reads.
A witness at `6` pins its family to `W` at `4`, its constructor to `sup`
at `5`, whose peeled domains are `[wFieldA, wFieldF]` — but `hkinds`
demands an analysis of exactly that list, and `supFields_noKind` is
`none`. -/
theorem noWitness_wEnv : ∀ (Efin : ResolvedEnv),
    (∀ r m, wEnv.members r = some m → Efin.members r = some m) →
    ∀ (E'' : ResolvedEnv), (∀ r m, E''.members r = some m → Efin.members r = some m) →
      ∀ w : IotaWitness E'', w.recRef = 6 → False := by
  intro Efin hsubW E'' hsub w hwr
  have hm : w.recMember = wRecMember := by
    have h1 := hsub _ _ w.hrec
    rw [hwr] at h1
    have h2 : Efin.members 6 = some wRecMember :=
      hsubW 6 wRecMember (by rw [wEnv_members]; simp)
    exact (Option.some.inj (h2.symm.trans h1)).symm
  -- the Efin-mediated identification: a ref the witness carries in E''
  -- agrees with wEnv's member there
  have hidFam : ∀ (k : Nat) (hk : w.familyRef = k) (m : CheckedMember)
      (hm' : wEnv.members k = some m), w.famMember = m := by
    intro k hk m hm'
    have h1 := hsub _ _ w.hfam
    rw [hk] at h1
    exact (Option.some.inj ((hsubW k m hm').symm.trans h1)).symm
  have hidCtor : ∀ (k : Nat) (hk : w.ctorRef = k) (m : CheckedMember)
      (hm' : wEnv.members k = some m), w.ctorMember = m := by
    intro k hk m hm'
    have h1 := hsub _ _ w.hctor
    rw [hk] at h1
    exact (Option.some.inj ((hsubW k m hm').symm.trans h1)).symm
  have hrecIdx := w.hrecIdx
  rw [hwr] at hrecIdx
  have hidx := w.hidx
  have hctorIdx := w.hctorIdx
  have hfamK := w.hfamK
  have hnM : 1 ≤ w.nMinors := by omega
  have hfle : w.familyRef ≤ 4 := by omega
  by_cases hf4 : w.familyRef = 4
  · have hfm := hidFam 4 hf4 wFamMember (by rw [wEnv_members]; simp)
    have hk0 : w.ctorIdx = 0 := by omega
    have hc5 : w.ctorRef = 5 := by omega
    have hcm := hidCtor 5 hc5 wSupMember (by rw [wEnv_members]; simp)
    have hnidx := w.hnidx
    rw [hfm] at hnidx
    have hpc0 : piCount wFamMember.mtype = 0 := rfl
    rw [hpc0] at hnidx
    have hnp : w.nparams = 0 := by omega
    have hlen2 : w.nparams + w.fields.length = 2 := by rw [w.hnpar, hcm]; rfl
    have hpeel := w.hpeel
    rw [hlen2, hcm] at hpeel
    have hpeel' : (some ([wFieldA, wFieldF], Expr.const 4 []) : Option (List (Expr Nat) × Expr Nat)) =
        some (w.ctorDoms, w.ctorResult) := hpeel
    have hdoms : [wFieldA, wFieldF] = w.ctorDoms := (Prod.mk.inj (Option.some.inj hpeel')).1
    have hkinds := w.hkinds
    rw [hf4, ← hdoms, hnp] at hkinds
    exact absurd hkinds (by rw [List.drop_zero, supFields_noKind]; exact fun h => Option.noConfusion h)
  · by_cases hf3 : w.familyRef = 3
    · have hfm := hidFam 3 hf3 natRecMemberU (by rw [wEnv_members]; simp)
      rw [hfm] at hfamK
      exact absurd hfamK (by decide)
    · by_cases hf2 : w.familyRef = 2
      · have hfm := hidFam 2 hf2 natSuccMember (by rw [wEnv_members]; simp)
        rw [hfm] at hfamK
        exact absurd hfamK (by decide)
      · by_cases hf1 : w.familyRef = 1
        · have hfm := hidFam 1 hf1 natZeroMember (by rw [wEnv_members]; simp)
          rw [hfm] at hfamK
          exact absurd hfamK (by decide)
        · have hf0 : w.familyRef = 0 := by omega
          have hfm := hidFam 0 hf0 natFamMember (by rw [wEnv_members]; simp)
          have hnidx := w.hnidx
          rw [hfm] at hnidx
          have hpc0 : piCount natFamMember.mtype = 0 := rfl
          rw [hpc0] at hnidx
          have hnM5 : w.nMinors = 5 := by omega
          have hcnt : w.nparams + 1 + w.nMinors + w.nindices + 1 = 7 := by omega
          have hpeelRec := w.hpeelRec
          rw [hm, hcnt] at hpeelRec
          have hnone : peelPis 7 wRecMember.mtype = none := rfl
          rw [hnone] at hpeelRec
          exact Option.noConfusion hpeelRec

/-- **ι at `W`'s recursor is vacuous, unconditionally**: no witness exists
at `6` in any sub-environment of any extension, so the `IotaAt`
quantifier is empty.  The ι half of the A debt at `wEnv` is EMPTY. -/
theorem iotaAt_wEnv_vacuous (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (Efin : ResolvedEnv) (hsubF : ∀ r m, wEnv.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin 6 := by
  intro E'' hsub w hwr
  exact (noWitness_wEnv Efin hsubF E'' hsub w hwr).elim

/-! ## §3 the family fixed-point cell -/

/-- **The `FamFixA` cell at `W`**: at every table faithful to `wEnv`'s
roles, the family's entry is the KT least fixed point.  This is the
single input `w_recVal_mem` lacks; equivalently (by `memberValR`) the
bridge `famLim ≈ famKT`. -/
def FamFixW (P : Premises4) : Prop :=
  ∀ (ctx : Nat → Role), (∀ r, Dom wEnv r → ctx r = envCtx wEnvWfT r) →
    ∀ μ : Nat → List Nat → PSet.{4}, FaithfulR P μ ctx wEnv →
      ∀ vs, Equiv (μ 4 vs) (famKT P μ (famDataOf wGroupAdmitted) vs)

/-- **The pure-model bridge (named residue `[rcic-f3-stepa-famfix]`)**:
the iterates limit and the KT lfp agree at `W`'s family data, at every
table.  Two least-fixed-point constructions of the same monotone
operator — the producer lane's target; refuting it blocks the KT route
(not kernel soundness: it is a model-construction identity, not an
admitted-environment fact). -/
def FamKTBridge (P : Premises4) : Prop :=
  ∀ (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
    Equiv (famLim P μ (famDataOf wGroupAdmitted) vs) (famKT P μ (famDataOf wGroupAdmitted) vs)

/-- The cell follows from the bridge: faithfulness forces the family's
entry to `famLim` (`memberValR` at the family role, read by `rfl` from
`envCtx`), the bridge carries it to `famKT`. -/
theorem famFixW_of_bridge (P : Premises4) (h : FamKTBridge P) : FamFixW P := by
  intro ctx hctx μ hF vs
  have h4 : wEnv.members 4 = some wFamMember := by rw [wEnv_members]; simp
  have he : envCtx wEnvWfT 4 = .fam (famDataOf wGroupAdmitted) := rfl
  have hfamR : Equiv (μ 4 vs) (memberValR P μ (ctx 4) wFamMember vs) := hF 4 wFamMember h4 vs
  rw [hctx 4 (dom_of_members h4), he] at hfamR
  have hfamL : Equiv (μ 4 vs) (famLim P μ (famDataOf wGroupAdmitted) vs) := hfamR
  exact hfamL.trans (h μ vs)

/-! ## §4 the A-twin group step: the arm from the cells -/

/-- What the group step has established when it reaches the recursor — the A
twin of `RecStepCtx`: the three direct-row fields (`cls`, `rfd`, `shapes`)
are REPLACED by nothing (the family fixed point arrives as the cell
`hfixA`, and the package builds ι itself from `WitDirect` or vacuity). -/
structure RecStepCtxA (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (fm : CheckedMember) (node : RecNode E E' f rr rm)
    (μ : Nat → List Nat → PSet.{4}) : Prop where
  faith : GroupFaith P μ fm node
  lim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs)
  scope : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n
  facts : TypeFacts E'
  pfree : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
    occursConst (famDataOf node.a).fref e = false
  rmem : E'.members rr = some rm
  rbody : rm.body = none
  lvC : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

/-- **The A-twin of `gInv_group_ofAt`**: the group step consumes the famfix cell
`hfixA` (the direct row's only structural use was `hclsF → famLim_fix →
`hfix`, replaced) and the A-package (the recursor's soundness and ι —
membership at the KT table, ι by `WitDirect` or vacuity).  Everything else
is the landed proof verbatim: the constructor walk, `field_small_gen`, the
recursor dispatch — no syntactic row is owed anywhere. -/
theorem gInv_group_ofAt_A (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hfixA : ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)))
    (hWR : WalkRec hmem)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB1 : (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
      vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d))
    (hWB : WalkB2 K hmem)
    (hpkgA : ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      RecStepCtxA P K fm node μ → RecPkgAt P μ K Efin E' rr rm)
    (IH : GInvAt P K Efin hE) :
    GInvAt P K Efin (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  intro hsubFin ctx hctx μ hF
  obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtx hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr (envCtx hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtx_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : FaithfulR P μ ctx E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH (fun r m h => hsubFin r m (hsubE r m h)) ctx hctxE μ hFE
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := PSet.groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  -- the family's entry is its limit, a fixed point of its value
  have hLimμ : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
    have h := hF f fm hf' vs
    rw [hctxG f (dom_of_members hf'), groupRoles_at_f] at h
    rw [node.fam]
    exact h
  have hpfF : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have := groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at this
    unfold Dom at this
    rw [hf0] at this
    exact absurd this (by decide)
  -- the A cell: the fixed point arrives directly (KT lfp + bridge at the fixture)
  have hfix : ∀ vs, Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) :=
    hfixA node μ
  have hG := groupFaith_of P hmem hL hrr node hF hctxG hTF hfix
  have hfmS : MemberSound P μ K f fm :=
    fam_member_sound P (famDataOf node.a) hG.fam hG.famTy (hTF f fm hf').1 (hTF f fm hf').2.1 hbf
  have hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true := fun i => by
    have h := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at h
    exact h
  -- the constructor scope at the table
  have hES_S : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
    intro σ n
    refine envSound_of P (Efin := Efin) (fun r m h => hsubFin r m (hSsub r m h)) ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.2 r m h hk
  -- the recursor's package (its soundness and ι), from the class's step
  have hrb : rm.body = none :=
    hbody _ _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hP := hpkgA node μ ⟨hG, hLimμ, hES_S, hTF, hpfF, hr', hrb, hlvC⟩ hsubFin
  have hIrr := hP.2
  have hrmS := hP.1
  -- every recursor of the extended environment
  have hIall : ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
    intro r m h hk
    rcases group_member_cases hmem hL hrr node h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact IHμ.2 r m h1 hk
    · rw [hfam] at hk; cases hk
    · exact hIrr
    · rw [(node.a.constructorViews i).hasClass] at hk; cases hk
  -- the constructors, along the walk
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → Ew.members r = none →
      FieldUniverseAdmitted cv →
      AgreeAt node.a.family.parameters.length Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh h07 hagc hB2w hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' := fun r' m' h =>
      hsubw r' m' (members_extend_preserved hfresh r' m' h)
    -- the member is one of the group's constructors
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
      rcases group_member_cases hmem hL hrr node (groupMembersT_installed hmem hin) with
        h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h1
      · rcases List.mem_cons.mp hin with h2 | h2
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; rw [hfam] at hkC; cases hkC
        · rcases List.mem_append.mp h2 with h3 | h3
          · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
            rw [hL] at hr
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
            have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
            exact ⟨⟨i, hi'⟩, rfl, Option.some.inj ((groupMembersT_installed hmem hin).symm.trans
              (node_ctor_member node ⟨i, hi'⟩))⟩
          · rw [List.mem_singleton] at h3
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3; rw [hrec] at hkC; cases hkC
      · rw [hfam] at hkC; cases hkC
      · rw [hrec] at hkC; cases hkC
      · exact h1
    obtain ⟨i, rfl, rfl⟩ := hctor
    -- the constructor's own view agrees with the recursor's
    have hstO := cv.storedType
    have hstR := (node.a.constructorViews i).storedType
    have hspl := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
      (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (hstO.symm.trans hstR)
    have hcat := hspl.1
    have href : famO.ref = node.a.family.ref := foldApps_const_head hspl.2
    have hfamO : famO.member = fm := by
      have h1 := famO.present
      rw [href, node.fam] at h1
      exact Option.some.inj ((hEw f _ h1).symm.trans hf')
    have hlvO : famO.resultLevel = node.a.family.resultLevel := by
      have e1 := famO.storedType
      have e2 := node.a.family.storedType
      rw [hfamO] at e1
      rw [hfmm] at e2
      have := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) (e1.symm.trans e2)).2
      injection this
    have harO : famO.member.arity = node.a.family.member.arity := by rw [hfamO, hfmm]
    refine ctor_member_sound P (famDataOf node.a) i.val (node.a.constructorViews i).parameters
      (node.a.constructorViews i).fields (node.a.constructorViews i).resultIndices (famDataOf_ctor node.a i)
      (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
      (hTF _ _ (node_ctor_member node i)).1 (hTF _ _ (node_ctor_member node i)).2.1
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) (fun vs => hG.ctor i vs) ?_ ?_ ?_
    · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
      rfl
    · intro vs _
      have h := hG.fam vs
      rw [hG.famTy] at h
      show Equiv (μ node.a.family.ref vs) _
      rw [node.fam]
      exact h
    · intro vs hvl hbd zs hz
      obtain ⟨u, d, hd⟩ := hB1 node i vs (hvl.trans (node.a.constructorViews i).arity) hbd
      have hsd := hsound_ty (P.good _ rfl) (hES_S (σOf vs) _) d hd
      have := tel_end_type' _ _ d (node.a.constructorViews i).storedType hsd ρ0 zs trivial hz
      have e : (List.range vs.length).map Level.param = policyFamilyLevels node.a.family := by
        rw [hvl, (node.a.constructorViews i).arity]; rfl
      rw [e]
      exact this
    · intro vs hvl hbd h0 ps xs hps hxs
      have hvlO : vs.length = famO.member.arity := by rw [harO, ← (node.a.constructorViews i).arity]; exact hvl
      have hB2v := hB2w vs hvlO hbd
      have hD : RefsIn (Dom Ew) (cv.parameters ++ cv.fields) := fun e he r hr => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
        obtain ⟨d, _⟩ := hB2v ⟨k, hk⟩
        exact hasTyT_denRefs d r hr
      have hES_w : EnvSound (mkM P μ) (σOf vs) K Ew famO.member.arity :=
        envSound_of P (Efin := Efin) (fun r m h => hsubFin r m (hEw r m h)) hAw
          (fun r m h hk => hIall r m (hEw r m h) hk) _ _
      have h0O : evalTotal (σOf vs) famO.resultLevel ≠ 0 := by rw [hlvO]; exact h0
      -- the level bound on the recursor view's fields: own fields by the own admission, positions the own
      -- view reads as parameters by the level agreement and the recursor's admission
      have hlevF : ∀ (j : Fin (node.a.constructorViews i).fields.length)
          (hk : (node.a.constructorViews i).parameters.length + j.val < (cv.parameters ++ cv.fields).length),
          evalTotal (σOf vs) (cv.domainsTyped.levels ⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩) ≤
            evalTotal (σOf vs) node.a.family.resultLevel := by
        intro j hk
        have hlenN : (node.a.constructorViews i).parameters.length = node.a.family.parameters.length :=
          (node.a.constructorViews i).parameterCount
        rcases Nat.lt_or_ge ((node.a.constructorViews i).parameters.length + j.val) cv.parameters.length with
          hpar | hfld
        · rcases hagc _ hk (by omega) hpar with hp | hle
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
        · have hj : (kk : Nat) → kk = (node.a.constructorViews i).parameters.length + j.val →
              kk - cv.parameters.length < cv.fields.length := fun kk hkk => by
            simp only [List.length_append] at hk; omega
          let j' : Fin cv.fields.length :=
            ⟨(node.a.constructorViews i).parameters.length + j.val - cv.parameters.length, hj _ rfl⟩
          have hfi : (⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩ :
              Fin (cv.parameters ++ cv.fields).length) = cv.fieldIndex j' :=
            Fin.ext (by
              show (node.a.constructorViews i).parameters.length + j.val =
                cv.parameters.length + ((node.a.constructorViews i).parameters.length + j.val - cv.parameters.length)
              omega)
          rw [hfi]
          rcases h07 j' with hp | ⟨_, hle⟩
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
      exact field_small_gen P μ μ K (Epre := Ew) famO.member.arity (cv.parameters ++ cv.fields)
        (node.a.constructorViews i).parameters (node.a.constructorViews i).fields hcat.symm
        cv.domainsTyped.levels node.a.family.resultLevel vs hES_w hB2v (fun _ _ _ => rfl) hD h0 hlevF ps xs hps hxs
  have hAll : AllSound P μ K E' := by
    refine walk_sound P μ K ((f, fm) :: ctors ++ [(rr, rm)]) (AgreeAt node.a.family.parameters.length) ?_ ?_ hfmS hrmS
      hcS hmem (fun _ h => h) (fun _ _ h => h) hWR (hAg node) hWB IHμ.1
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; subst h; rw [hrec] at hk; cases hk
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · subst h; rw [hfam] at hk; cases hk
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; exact h
  exact ⟨hAll, hIall⟩

/-! ## §5 the checked side condition (part (b)) -/

/-- **The A arm is sound given exactly the two named cells + the KT package.**
The `GroupStepAt` antecedents (walk agreement, `BoundG`, `BoundDG`) are the fold's
own inputs — `WalkRec` is derived, the bounds feed `BoundG`'s own structure;
nothing syntactic survives. -/
theorem stepAAt_of_A (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hfixA : ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)))
    (hpkgA : ∀ (Efin : ResolvedEnv) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      RecStepCtxA P K fm node μ → RecPkgAt P μ K Efin E' rr rm) :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun hAg hB _ IH => gInv_of_gInvAt (fun Efin =>
    gInv_group_ofAt_A P K Efin hE hfam hctors hrec hmem hfixA (walkRec_of_group hmem) hAg hB.2.1 hB.2.2.1
      (fun node μ => hpkgA Efin node μ) (gInvAt_of_gInv IH))

/-- **`StepAG` from the cells** — the (b) answer at tier granularity. The two
cells: the famfix cell (named residue `[rcic-f3-stepa-famfix]`; `FamKTBridge`
+ `famKT_fix` + `famVal_tables` instantiate it at the `wEnv` fixture) and the
KT package (the recursor's membership at the KT table — the producer lane's
delivery; ι by `iota_at_of_witDirect` under `CtorWitOK`, or by vacuity as at
`wEnv`). Refuting the famfix cell blocks the KT route to `StepAG` and
nothing else; it is a model-construction identity, not a kernel-soundness
fact. -/
theorem stepAG_of_cells (P : Premises4) (K : Nat → Nat)
    (hfixA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)))
    (hpkgA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (fm : CheckedMember)
      (Efin : ResolvedEnv) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      RecStepCtxA P K fm node μ → RecPkgAt P μ K Efin E' rr rm) :
    StepAG P K :=
  fun {E E' f rr fm rm ctors} hE hfam hctors hrec hmem _ hAg hB hBDG IH =>
    stepAAt_of_A P K hE hfam hctors hrec hmem hfixA
      (fun (Efin : ResolvedEnv) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) =>
        hpkgA fm Efin node μ) hAg hB hBDG IH

end Rcic.F3.StepAObstr
