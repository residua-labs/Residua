import rcic.RcicAnnDeltaEnvA
import rcic.RcicAnnIotaCorrUA
import rcic.RcicAnnIotaCorrN
import rcic.RcicAnnIotaCorrD

/-! # Route C, class (b), the union correspondence at `drEnvA` — R-NoFunRec-4d-ii

`drEnvA` (`RcicAnnDeltaEnvA`) is the annotated twin of `drEnv` — `Id`, `F`, the `.drecD`
constructor `mk` and `F.rec`.  The union ι-correspondence there cannot reuse the strict
route: `¬ EnvNormEraseA drEnvA` (`dr_not_envNormEraseA`), so `iotaAnnotatesUA_of_envWfA` /
`iotaErasesTUA_of_envWfA` are unavailable by design.  This module supplies the δ-aware
composition:

1. **The erased-side census.**  At `drEnv`, ref/class pinning collapses every
   `IotaWitnessS`/`IotaWitnessN`/`IotaWitness` to the `mk` constructor: `nparams = 0`,
   `nindices = 0`, `nMinors = 1`, `ctorIdx = 0`, `ctorDoms = [Id F]` (stored) or `[F]`
   (normalized), `shapes = [.recursive 0]` by `fieldShapesFuel` agreement with `wDrMkD`.
2. **`EnvCorrEraseCert drEnv` is vacuous** — `analyzeField 1 (Id F) = none` (the spine
   head is `const 0`, not the family), so no legacy `IotaWitness` exists.
3. **`iotaWitnessSAnnB drEnv` is vacuously false** — `noTransparentB` rejects `Id F`
   (`Id` is a transparent `definitionM`), killing `directFragCheck`; the `annB` arm of
   `hsel` is vacuous.  The `dArm` arm carries `NormCorrD`, discharged pointwise from the
   `drCtorMemberAD` view evidence (`drCtorMemberAD_shapes`, `telWhnfDom_drMk`).
4. **`iotaAnnotatesUADU_of_envWfA`** — `iotaAnnotatesUA_of_envWfA` mirrored: `.ofU`
   upgrades through the (vacuous) erase certificate, `.ofUS` rides
   `iotaAnnotatesADU_of_envWfA` directly.
5. **`pinDr_iotaErasesTUA`** — `iotaFnA` steps land `.ofUS`: `derivedIotaN_of_iotaFnA`
   hands an `IotaWitnessN` (normed reads); `iotaWitnessS_of_witnessN_dr` repins it on the
   stored side reusing `wDrMkD`'s static shape/schema/fuel evidence, and the δ-arm's
   decided rhs agreement (`iotaWitnessSAnnDArm_parts`) closes `iotaRhsOfS = iotaRhsOfN`.
6. **`pinDr_iotaCorrTUA : IotaCorrTUA drEnvA`** — class (b) composed at the union face.

`closure_claim = 0`. -/

namespace Rcic.Declarative.Ann
open Rcic.Declarative

/-! ## (1) the erased-side census -/

/-- `IotaWitnessS` at `drEnv`: the constructor is `mk` at ref `2` — the only
    `.constructorM` member. -/
theorem drWS_ctor (w : IotaWitnessS drEnv) :
    w.ctorRef = 2 ∧ w.ctorMember = drMkMember := by
  rcases drEnv_members w.hctor with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)

/-- the family is `F` at ref `1` — the only `.inductiveM` member. -/
theorem drWS_fam (w : IotaWitnessS drEnv) :
    w.familyRef = 1 ∧ w.famMember = drFamMember := by
  rcases drEnv_members w.hfam with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)

/-- the recursor is `F.rec` at ref `3` — the only `.recursorM` member. -/
theorem drWS_rec (w : IotaWitnessS drEnv) :
    w.recRef = 3 ∧ w.recMember = drRecMember := by
  rcases drEnv_members w.hrec with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩

/-- `F`'s `piCount = 0` forces `nparams = nindices = 0`; the layout equations then force
    `nMinors = 1`, `ctorIdx = 0`. -/
theorem drWS_counts (w : IotaWitnessS drEnv) :
    w.nparams = 0 ∧ w.nindices = 0 ∧ w.nMinors = 1 ∧ w.ctorIdx = 0 := by
  obtain ⟨hcr, _⟩ := drWS_ctor w
  obtain ⟨hfr, hfm⟩ := drWS_fam w
  obtain ⟨hrr, _⟩ := drWS_rec w
  have h0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx
    rw [hfm] at h
    exact h
  have hnp : w.nparams = 0 := (Nat.add_eq_zero_iff.mp h0).1
  have hni : w.nindices = 0 := (Nat.add_eq_zero_iff.mp h0).2
  have hc : 2 = 1 + 1 + w.ctorIdx := by
    have h := w.hctorIdx
    rw [hcr, hfr] at h
    exact h
  have hr : 3 = 1 + 1 + w.nMinors := by
    have h := w.hrecIdx
    rw [hrr, hfr] at h
    exact h
  exact ⟨hnp, hni, by omega, by omega⟩

/-- the peeled telescope: `peelPis` on the stored `Π (x : Id F), F` gives `[Id F]` and
    `F`; `hnpar` then forces `fields.length = 1`. -/
theorem drWS_tel (w : IotaWitnessS drEnv) :
    w.ctorDoms = [drField] ∧ w.ctorResult = .const 1 [] ∧ w.fields.length = 1 := by
  obtain ⟨_, hcm⟩ := drWS_ctor w
  obtain ⟨hnp, _, _, _⟩ := drWS_counts w
  have hfl : w.fields.length = 1 := by
    have h := w.hnpar
    rw [hcm, hnp] at h
    have hp : piCount drMkMember.mtype = 1 := rfl
    rw [hp, Nat.zero_add] at h
    exact h
  have hcd : w.ctorDoms = [drField] ∧ w.ctorResult = .const 1 [] := by
    have h := w.hpeel
    rw [hcm, hnp, hfl] at h
    have hp : peelPis (0 + 1) drMkMember.mtype = some ([drField], .const 1 []) := rfl
    rw [hp] at h
    exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,
      (congrArg Prod.snd (Option.some.inj h)).symm⟩
  exact ⟨hcd.1, hcd.2, hfl⟩

/-- `fieldShapesFuel` succeeds at `w.fuel` (the witness) and at `8` (`wDrMkD`); agreement
    pins the shapes to `[.recursive 0]`. -/
theorem drWS_shapes (w : IotaWitnessS drEnv) : w.shapes = [.recursive 0] := by
  obtain ⟨hfr, hfm⟩ := drWS_fam w
  obtain ⟨hnp, hni, _, _⟩ := drWS_counts w
  obtain ⟨hd, _, _⟩ := drWS_tel w
  have h := w.hshapes
  rw [hfr, hfm, hnp, hni, hd, List.drop_zero] at h
  exact fieldShapesFuel_agree drEnv h wDrMkD.hshapes

/-- `IotaWitnessN` at `drEnvA`: same census, ann-side member table. -/
theorem drWN_ctor (w : IotaWitnessN drEnvA) :
    w.ctorRef = 2 ∧ w.ctorMember = drCtorMemberAD := by
  rcases drEnvA_mem w.hctor with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)

theorem drWN_fam (w : IotaWitnessN drEnvA) :
    w.familyRef = 1 ∧ w.famMember = drFamMember := by
  have h : drEnv.members w.familyRef = some w.famMember := drEnvA_members _ ▸ w.hfam
  rcases drEnv_members h with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hfamK
    rw [hm] at hx
    exact absurd hx (by decide)

theorem drWN_rec (w : IotaWitnessN drEnvA) :
    w.recRef = 3 ∧ w.recMember = drRecMember := by
  have h : drEnv.members w.recRef = some w.recMember := drEnvA_members _ ▸ w.hrec
  rcases drEnv_members h with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hrecK
    rw [hm] at hx
    exact absurd hx (by decide)
  · exact ⟨hr, hm⟩

theorem drWN_counts (w : IotaWitnessN drEnvA) :
    w.nparams = 0 ∧ w.nindices = 0 ∧ w.nMinors = 1 ∧ w.ctorIdx = 0 := by
  obtain ⟨hcr, _⟩ := drWN_ctor w
  obtain ⟨hfr, hfm⟩ := drWN_fam w
  obtain ⟨hrr, _⟩ := drWN_rec w
  have h0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx
    rw [hfm] at h
    exact h
  have hnp : w.nparams = 0 := (Nat.add_eq_zero_iff.mp h0).1
  have hni : w.nindices = 0 := (Nat.add_eq_zero_iff.mp h0).2
  have hc : 2 = 1 + 1 + w.ctorIdx := by
    have h := w.hctorIdx
    rw [hcr, hfr] at h
    exact h
  have hr : 3 = 1 + 1 + w.nMinors := by
    have h := w.hrecIdx
    rw [hrr, hfr] at h
    exact h
  exact ⟨hnp, hni, by omega, by omega⟩

/-- the NORMED peel at the twin: `peelPis` on `Π (x : F), F` gives `[F]`/`F`, so
    `ctorDoms = [.const 1 []]` and `fields.length = 1`; `analyzeFields` then reads
    `kinds = [.directRec]`, `ctorParams = []`, `ctorAfterParams` the normed body. -/
theorem drWN_tel (w : IotaWitnessN drEnvA) :
    w.ctorDoms = [.const 1 []] ∧ w.ctorResult = .const 1 [] ∧ w.fields.length = 1 ∧
      w.kinds = [.directRec] ∧ w.ctorParams = [] ∧ w.ctorAfterParams =
        instantiateLevels w.ls (memberNormTy w.ctorMember) := by
  obtain ⟨_, hcm⟩ := drWN_ctor w
  obtain ⟨hnp, _, _, _⟩ := drWN_counts w
  have hfl : w.fields.length = 1 := by
    have h := w.hnpar
    rw [hcm, hnp] at h
    have hp : piCount (memberNormTy drCtorMemberAD) = 1 := rfl
    rw [hp, Nat.zero_add] at h
    exact h
  have hcd : w.ctorDoms = [.const 1 []] ∧ w.ctorResult = .const 1 [] := by
    have h := w.hpeel
    rw [hcm, hnp, hfl] at h
    have hp : peelPis (0 + 1) (memberNormTy drCtorMemberAD) =
        some ([.const 1 []], .const 1 []) := rfl
    rw [hp] at h
    exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,
      (congrArg Prod.snd (Option.some.inj h)).symm⟩
  have hk : w.kinds = [.directRec] := by
    obtain ⟨hfr2, _⟩ := drWN_fam w
    have h := w.hkinds
    rw [hnp, hcd.1, List.drop_zero, hfr2] at h
    exact (Option.some.inj h).symm
  have hcp : w.ctorParams = [] := by
    have h := w.hctorParams
    rw [hnp] at h
    exact List.length_eq_zero.mp h
  have hca : w.ctorAfterParams =
      instantiateLevels w.ls (memberNormTy w.ctorMember) := by
    have h := w.hctorAfter
    rw [hcm, hnp, List.take_zero] at h
    have hj := Option.some.inj h
    rw [hcm]
    exact hj.symm
  exact ⟨hcd.1, hcd.2, hfl, hk, hcp, hca⟩

/-! ## (2) the erased-side certificates -/

/-- `EnvCorrEraseCert drEnv` holds VACUOUSLY: `analyzeField` refuses `Id F` (its spine
    head is `const 0` — the `.drecD` shadowing that hides the family from the stored
    read), so no legacy `IotaWitness` exists at `mk`, the only constructor. -/
theorem drEnvCorrEraseCert : EnvCorrEraseCert drEnv := by
  intro w
  rcases drEnv_members w.hctor with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)
  · rcases drEnv_members w.hfam with ⟨hfr, hfm⟩ | ⟨hfr, hfm⟩ | ⟨hfr, hfm⟩ | ⟨hfr, hfm⟩
    · have hx := w.hfamK
      rw [hfm] at hx
      exact absurd hx (by decide)
    · have h0 : w.nparams + w.nindices = 0 := by
        have h := w.hnidx
        rw [hfm] at h
        exact h
      have hnp : w.nparams = 0 := (Nat.add_eq_zero_iff.mp h0).1
      have hfl : w.fields.length = 1 := by
        have h := w.hnpar
        rw [hm, hnp] at h
        have hp : piCount drMkMember.mtype = 1 := rfl
        rw [hp, Nat.zero_add] at h
        exact h
      have hpeel := w.hpeel
      rw [hm, hnp, hfl] at hpeel
      have hp : peelPis (0 + 1) drMkMember.mtype = some ([drField], .const 1 []) := rfl
      rw [hp] at hpeel
      have hd : w.ctorDoms = [drField] := by
        exact (congrArg Prod.fst (Option.some.inj hpeel)).symm
      have hk := w.hkinds
      rw [hd, hnp, List.drop_zero, hfr] at hk
      rw [show analyzeFields 1 [drField] = none from rfl] at hk
      exact Option.noConfusion hk
    · have hx := w.hfamK
      rw [hfm] at hx
      exact absurd hx (by decide)
    · have hx := w.hfamK
      rw [hfm] at hx
      exact absurd hx (by decide)
  · have hx := w.hctorK
    rw [hm] at hx
    exact absurd hx (by decide)

/-- `iotaWitnessSAnnB` is false at EVERY `drEnv` witness: `directFragCheck` opens with
    `noTransparentB` on `Id F`, and `Id` is a transparent `definitionM` — the stored
    domain is exactly where the δ-rewrite lives.  The strict recognizer's `annB` arm is
    vacuous here by design. -/
theorem dr_annB_false (w : IotaWitnessS drEnv) :
    iotaWitnessSAnnB drEnv w = false := by
  obtain ⟨_, _⟩ := drWS_ctor w
  obtain ⟨hfr, hfm⟩ := drWS_fam w
  obtain ⟨hnp, hni, _, _⟩ := drWS_counts w
  obtain ⟨hd, _, _⟩ := drWS_tel w
  unfold iotaWitnessSAnnB
  rw [hfr, hfm, hnp, hni, hd, List.drop_zero]
  rfl

/-! ## (3) the `.drecD` selector -/

/-- `NormCorrD` at `drEnvA`, per-witness: the three conjuncts read off `drCtorMemberAD`'s
    `CtorViewA`-side evidence — `piCount`/`ctorShapesA` on the normed type by `rfl`, and
    the erased `applyTel` landing `telWhnfDom`-normalized (`telWhnfDom_drMk`). -/
theorem drNormCorrD (w : IotaWitnessS drEnv) : NormCorrD drEnvA w := by
  obtain ⟨hcr, hcm0⟩ := drWS_ctor w
  obtain ⟨hfr, hfm⟩ := drWS_fam w
  obtain ⟨hnp, hni, _, _⟩ := drWS_counts w
  obtain ⟨hd, _, hfl⟩ := drWS_tel w
  have hs := drWS_shapes w
  intro cm hcm hcls
  rw [hcr] at hcm
  rw [show drEnvA.members 2 = some drCtorMemberAD from rfl] at hcm
  cases hcm
  refine ⟨?_, ?_, ?_⟩
  · rw [hnp, hfl]
    rfl
  · rw [hfr, hnp, hs]
    exact drCtorMemberAD_shapes
  · intro args hargs
    rw [hnp, List.take_zero] at hargs
    obtain rfl : args = [] := by
      rcases args with _ | ⟨a, as⟩
      · rfl
      · simp at hargs
    refine ⟨instantiateLevelsA (w.ls.take w.ctorMember.arity)
        (memberNormTyA drCtorMemberAD), rfl, ?_⟩
    intro T₀ hT₀
    rw [hnp, List.take_zero, hcm0] at hT₀
    rw [show drMkMember.arity = 0 from rfl, List.take_zero,
      instantiateLevels_nil, applyTel_nil] at hT₀
    obtain rfl := Option.some.inj hT₀
    rw [hd, hnp, List.drop_zero]
    have he : erase (instantiateLevelsA (w.ls.take w.ctorMember.arity)
        (memberNormTyA drCtorMemberAD)) = .pi (.const 1 []) (.const 1 []) := by
      rw [hcm0]
      rw [show drMkMember.arity = 0 from rfl, List.take_zero, instantiateLevelsA_nil]
      rfl
    rw [he]
    exact telWhnfDom_drMk.symm

/-- the per-witness selector: `annB` is vacuous (the stored domain carries `Id`), `dArm`
    gets `drNormCorrD`. -/
theorem drHsel : ∀ w : IotaWitnessS drEnv,
    (iotaWitnessSAnnB drEnv w = true →
      ∀ cm, drEnvA.members w.ctorRef = some cm → cm.mclass = .constructorM →
        ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) ∧
    (iotaWitnessSAnnDArm drEnv w = true → NormCorrD drEnvA w) :=
  fun w =>
    ⟨fun hb _ _ _ _ _ => absurd hb (by rw [dr_annB_false w]; exact Bool.false_ne_true),
     fun _ => drNormCorrD w⟩

/-! ## (4) the union composition -/

/-- `iotaAnnotatesUA_of_envWfA` mirrored at the δ-union: `.ofU` upgrades through the
    erase certificate; `.ofUS` is already `DerivedIotaT` and rides
    `iotaAnnotatesADU_of_envWfA` under the per-witness `.drecD` selector. -/
theorem iotaAnnotatesUADU_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA)
    (hsel : ∀ w : IotaWitnessS (eraseEnv EA),
      (iotaWitnessSAnnB (eraseEnv EA) w = true →
        ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
          ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) ∧
      (iotaWitnessSAnnDArm (eraseEnv EA) w = true → NormCorrD EA w))
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hC : EnvCorrAnnDU (eraseEnv EA)) :
    IotaAnnotatesUA EA := by
  intro e rhs hu
  obtain u | t := derivedIotaU_elim hu
  · obtain ⟨t⟩ := derivedIotaT_of_derivedIota hCe u
    exact iotaAnnotatesADU_of_envWfA hW hsel hC e rhs t
  · exact iotaAnnotatesADU_of_envWfA hW hsel hC e rhs t

/-- annotation at the union face at `drEnvA`: the typed landing composed under the
    `.drecD` selector and the δ-union certificate. -/
theorem pinDr_iotaAnnotatesUA : IotaAnnotatesUA drEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := drRecTyAt0
  exact iotaAnnotatesUADU_of_envWfA (drEnvWfA w hT0) (drEnvA_erase.symm ▸ drHsel)
    (drEnvA_erase.symm ▸ drEnvCorrEraseCert) (drEnvA_erase.symm ▸ envCorrAnnDU_drEnv)

/-- annotation at the typed root at `drEnvA`, standalone. -/
theorem pinDr_iotaAnnotatesA : IotaAnnotatesA drEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := drRecTyAt0
  exact iotaAnnotatesADU_of_envWfA (drEnvWfA w hT0) (drEnvA_erase.symm ▸ drHsel)
    (drEnvA_erase.symm ▸ envCorrAnnDU_drEnv)

/-! ## (5) the N→S witness bridge and the union erase face -/

/-- an `IotaWitnessN` at the twin repinned on the STORED side: every structural field
    transfers verbatim; the stored-read fields (`ctorMember`, `ctorDoms`, `ctorResult`,
    `hnpar`, `hpeel`, `hctorClosed`) come from `drMkMember`; the shape/schema/fuel
    evidence is `wDrMkD`'s — the census pins `wN`'s counts to the same scrutinee. -/
def iotaWitnessS_of_witnessN_dr (wN : IotaWitnessN drEnvA) : IotaWitnessS drEnv where
  recRef := wN.recRef
  ctorRef := wN.ctorRef
  ls := wN.ls
  lsC := wN.lsC
  recMember := wN.recMember
  ctorMember := drMkMember
  hrec := by
    obtain ⟨hrr, hrm⟩ := drWN_rec wN
    rw [hrr, hrm]
    exact wDrMkD.hrec
  hctor := by
    rw [(drWN_ctor wN).1]
    exact wDrMkD.hctor
  hrecK := wN.hrecK
  hctorK := rfl
  preMajor := wN.preMajor
  fields := wN.fields
  ctorParams := wN.ctorParams
  familyRef := wN.familyRef
  famMember := wN.famMember
  hfam := by
    obtain ⟨hfr, hfm⟩ := drWN_fam wN
    rw [hfr, hfm]
    exact wDrMkD.hfam
  hfamK := wN.hfamK
  nparams := wN.nparams
  nindices := wN.nindices
  nMinors := wN.nMinors
  ctorIdx := wN.ctorIdx
  hctorParams := wN.hctorParams
  hnpar := by
    obtain ⟨hnp, _, _, _⟩ := drWN_counts wN
    obtain ⟨_, _, hfl, _, _, _⟩ := drWN_tel wN
    rw [hnp, hfl]
    rfl
  hnidx := wN.hnidx
  hnmin := wN.hnmin
  hidx := wN.hidx
  hctorIdx := wN.hctorIdx
  hrecIdx := wN.hrecIdx
  hpre := wN.hpre
  ctorDoms := [drField]
  ctorResult := .const 1 []
  hpeel := by
    obtain ⟨hnp, _, _, _⟩ := drWN_counts wN
    obtain ⟨_, _, hfl, _, _, _⟩ := drWN_tel wN
    rw [hnp, hfl]
    rfl
  hfamApp := by
    rw [(drWN_fam wN).1]
    rfl
  recDoms := wN.recDoms
  recBody := wN.recBody
  hpeelRec := wN.hpeelRec
  hrecBody := wN.hrecBody
  hmajorTy := wN.hmajorTy
  hrecClosed := wN.hrecClosed
  hctorClosed := rfl
  hlsLen := wN.hlsLen
  fuel := wDrMkD.fuel
  shapes := wDrMkD.shapes
  hshapes := by
    obtain ⟨hfr, hfm⟩ := drWN_fam wN
    obtain ⟨hnp, hni, _, _⟩ := drWN_counts wN
    rw [hfr, hfm, hnp, hni, List.drop_zero]
    exact wDrMkD.hshapes
  schema := wDrMkD.schema
  hschema := by
    obtain ⟨hrr, hrm⟩ := drWN_rec wN
    obtain ⟨hnp, hni, hnM, hci⟩ := drWN_counts wN
    obtain ⟨_, _, hfl, _, _, _⟩ := drWN_tel wN
    rw [hrr, hrm, hnp, hni, hnM, hci, hfl]
    exact wDrMkD.hschema
  hstable := by
    intro E' hsub
    obtain ⟨hrr, hrm⟩ := drWN_rec wN
    obtain ⟨hfr, hfm⟩ := drWN_fam wN
    obtain ⟨hnp, hni, hnM, hci⟩ := drWN_counts wN
    obtain ⟨_, _, hfl, _, _, _⟩ := drWN_tel wN
    rw [hrr, hrm, hfr, hfm, hnp, hni, hnM, hci, hfl, List.drop_zero]
    exact wDrMkD.hstable E' hsub
  hschemaScope := by
    obtain ⟨hnp, hni, hnM, _⟩ := drWN_counts wN
    obtain ⟨_, _, hfl, _, _, _⟩ := drWN_tel wN
    rw [hnp, hni, hnM, hfl]
    exact wDrMkD.hschemaScope

/-- the lhs endpoints agree definitionally — the two lhs builders are the same spine
    expression at the shared fields. -/
theorem dr_lhs_bridge (wN : IotaWitnessN drEnvA) :
    iotaLhsOfS (iotaWitnessS_of_witnessN_dr wN) = iotaLhsOfN wN := rfl

/-- the rhs bridge: `iotaRhsOfS` at the stored witness, through the δ-arm's decided
    rhs agreement, lands the same `foldApps minor (rhsArgs ...)` the normed witness
    carries — `rhsArgs` at `.directRec` and `rhsArgsS` at `.recursive 0` both emit
    `recCallField` on the normalized telescope `Π (x : F), F`. -/
theorem dr_rhs_bridge (wN : IotaWitnessN drEnvA) :
    iotaRhsOfS (iotaWitnessS_of_witnessN_dr wN) = iotaRhsOfN wN := by
  have hdu := envCorrAnnDU_drEnv (iotaWitnessS_of_witnessN_dr wN)
  unfold iotaWitnessSAnnDB at hdu
  rw [Bool.or_eq_true] at hdu
  obtain hd | hd := hdu
  · rw [dr_annB_false (iotaWitnessS_of_witnessN_dr wN)] at hd
    exact Bool.noConfusion hd
  obtain ⟨hfrag, ctorAfter, minor', happ, hwalk, hpm, hrhs⟩ :=
    iotaWitnessSAnnDArm_parts hd
  obtain ⟨hcr, hcm⟩ := drWN_ctor wN
  obtain ⟨hrr, hrm⟩ := drWN_rec wN
  obtain ⟨hfr, hfm⟩ := drWN_fam wN
  obtain ⟨hnp, hni, hnM, hci⟩ := drWN_counts wN
  obtain ⟨hdm, hcr2, hfl, hk, hcp, hca⟩ := drWN_tel wN
  have happ' : applyTel (wN.preMajor.take wN.nparams)
      (instantiateLevels (wN.ls.take drMkMember.arity) drMkMember.mtype) =
      some ctorAfter := happ
  have hpm' : wN.preMajor[wN.nparams + 1 + wN.ctorIdx]? = some minor' := hpm
  have hrhs' : iotaRhsOfS (iotaWitnessS_of_witnessN_dr wN) = foldApps minor'
      (rhsArgsS (.const wN.recRef wN.ls) wN.preMajor wN.nparams wN.nMinors
        wN.fields wDrMkD.shapes
        (telWhnfDom drEnv (domsFuelBound ([drField].drop wN.nparams)) ctorAfter)) :=
    hrhs
  have hca0 : ctorAfter = drMkMember.mtype := by
    rw [hnp, List.take_zero] at happ'
    rw [show drMkMember.arity = 0 from rfl, List.take_zero,
      instantiateLevels_nil, applyTel_nil] at happ'
    exact (Option.some.inj happ').symm
  have hmn : minor' = wN.minor := by
    have h := wN.hminor
    rw [hnp, hci] at h hpm'
    exact (Option.some.inj (h.symm.trans hpm')).symm
  rw [hrhs', hmn]
  unfold iotaRhsOfN
  rw [hca0, hnp, List.drop_zero, telWhnfDom_drMk]
  obtain ⟨f, hff⟩ := List.length_eq_one.mp hfl
  rw [hrr, hnM, hff, hk, hca, hcm]
  rw [show instantiateLevels wN.ls (memberNormTy drCtorMemberAD) =
      .pi (.const 1 []) (.const 1 []) from rfl]
  rfl

/-- the union erase face at `drEnvA`: an `iotaFnA` copy lands `.ofUS` — the normalized
    witness repins on the stored side and the δ-arm's rhs agreement closes the
    endpoints. -/
theorem pinDr_iotaErasesTUA : IotaErasesTUA drEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := drRecTyAt0
  intro e e' h
  obtain ⟨d⟩ := derivedIotaN_of_iotaFnA (drEnvWfA w hT0) drNoFunA h
  obtain ⟨wN, hl, hr⟩ := derivedIotaN_unpack d
  refine ⟨?_⟩
  rw [hl, hr]
  rw [← dr_lhs_bridge wN, ← dr_rhs_bridge wN, drEnvA_erase]
  exact .ofUS (iotaWitnessS_of_witnessN_dr wN)

/-- the union ι-correspondence at `drEnvA` — class (b) composed to the annotated
    supply: both faces at once, through the δ-aware paths. -/
theorem pinDr_iotaCorrTUA : IotaCorrTUA drEnvA :=
  ⟨pinDr_iotaAnnotatesUA, pinDr_iotaErasesTUA⟩

#print axioms pinDr_iotaCorrTUA
#print axioms pinDr_iotaErasesTUA
#print axioms pinDr_iotaAnnotatesUA
#print axioms dr_rhs_bridge
#print axioms iotaWitnessS_of_witnessN_dr
#print axioms drEnvCorrEraseCert

end Rcic.Declarative.Ann
