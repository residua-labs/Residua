import rcic.RcicAnnIotaCorrF
import rcic.RcicAnnAccCorrPin

/-!
# R-NoFunRec S6-5, pinAcc row — the annotation side at a frec environment

The named obstruction and the frec-aware repair, both on the landed Acc
fixture (`RcicAnnAccFrecPin`/`RcicAnnAccCorrPin`):

* `wPinAccS` — the canonical `IotaWitnessS` over `eraseEnv pinAccEnvA`:
  recursor `12`, constructor `11`, family `10`, shapes
  `[.nonrecursive, .recursive 2]`, schema `paSchema`.
* `pin_iotaWitnessSAnnB_wPinAccS`,
  `not_envCorrAnnCert_pinAcc` — the landed DIRECT-fragment recognizer refuses
  this witness: `directFragOne`'s `noInner` clause
  (`piCount T = 0 ∨ ¬ properShapeB (piTailOf T)`) is `false` on the `.frec`
  domain `Π (y:S0), R y x → AccT y`, whose Π-tail `AccT y` is a proper family
  application.  `EnvCorrAnnCert (eraseEnv pinAccEnvA)` is therefore refuted —
  the honest name of the obstruction, inhabited.
* `pinAcc_envCorrAnnCertF` — the frec-aware certificate DOES hold on the same
  environment: `iotaWitnessSAnnBF` decides the `fieldShapesE`/`shapes`
  agreement the annotation direction actually owes, and the erased-side
  analysis returns `[.nonrecursive, .recursive 2]` on `intro`'s domains.
* `pinAcc_envCorrEraseCert` — the erasure certificate is VACUOUS here:
  `analyzeField` returns `none` on the `.frec` domain (`occursConst` sees the
  family inside a Π it cannot classify), so `IotaWitness` — whose `hkinds`
  needs `analyzeFields = some _` — has no inhabitant at the only constructor
  of the environment.
* `pinAcc_iotaAnnotatesUA`, `pinAcc_iotaCorrTUA` — class (a) composed to the
  annotated supply: the full union correspondence on `pinAccEnvA`.

Nothing landed is touched; all names are new.  `closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

/-! ## (1) the canonical `IotaWitnessS` at `AccT.rec`/`intro` -/

/-- the recursor's peeled domains: `[motive, minor, index x, major AccT x]`. -/
abbrev paRecDoms : List (Expr Nat) :=
  [paMotTy, paMinorTy, .sort .zero, .app (.const 10 []) (.bvar 0)]

/-- The shape-based ι witness at the Acc group: recursor `12`, constructor
    `11`, family `10`, no parameters, one index, one minor, fields the two
    context binders `[x, g]` (`fieldBvars 2`), shapes
    `[.nonrecursive, .recursive 2]`, schema `paSchema` — the indexed-Acc
    reduct `minor x g (λ y h, rec M minor y (g y h))` admission derives. -/
def wPinAccS : IotaWitnessS (eraseEnv pinAccEnvA) where
  recRef := 12
  ctorRef := 11
  ls := [.param 0]
  lsC := []
  recMember := paRecT
  ctorMember := paIntroT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := preMajorBvars 0 1 1 2
  fields := fieldBvars 2
  ctorParams := []
  familyRef := 10
  famMember := paFamT
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.sort .zero, paFieldDom]
  ctorResult := .app (.const 10 []) (.bvar 1)
  hpeel := rfl
  hfamApp := rfl
  recDoms := paRecDoms
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 24
  shapes := [.nonrecursive, .recursive 2]
  hshapes := rfl
  schema := paSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem9 : (eraseEnv pinAccEnvA).members 9 = some paRelT := rfl
    have hmem10 : (eraseEnv pinAccEnvA).members 10 = some paFamT := rfl
    have hmem11 : (eraseEnv pinAccEnvA).members 11 = some paIntroT := rfl
    have hmem12 : (eraseEnv pinAccEnvA).members 12 = some paRecT := rfl
    show iotaWitnessStableB (eraseEnv pinAccEnvA) 24 [.sort .zero, paFieldDom]
      (fieldBvars 2)
      (lift 0 5 (ctorFieldTelRaw 0 [.sort .zero, paFieldDom]
        (.app (.const 10 []) (.bvar 1)))) = true
    simp [iotaWitnessStableB, paFieldDom, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem9, hmem10, hmem11, hmem12, paRelT, paFamT, paIntroT,
      paRecT, transparent, instantiateLevels]
    exact ⟨Or.inl rfl, Or.inl rfl⟩)
  hschemaScope := rfl

/-! ## (2) the named obstruction: `directFragCheck` refuses the `.frec` domain -/

/-- THE OBSTRUCTION, INHABITED: `wPinAccS` is a well-formed `IotaWitnessS` of
    the well-formed erased environment, and the landed annotation recognizer
    refuses it — `directFragOne`'s last conjunct asks that a Π-domain's tail
    NOT be a proper family application (`piCount T = 0 ∨
    ¬ properShapeB (piTailOf T)`), which fails at
    `Π (y:S0), R y x → AccT y` whose tail `AccT y` is exactly that.  This is
    the frec counterpart of `pin_iotaWitnessSAnnB_wDrMkS`: not δ-opacity
    (`drFamEnv`) but inner recursion (`R-NoFunRec`). -/
theorem pin_iotaWitnessSAnnB_wPinAccS :
    iotaWitnessSAnnB (eraseEnv pinAccEnvA) wPinAccS = false := rfl

/-- `EnvCorrAnnCert` is refuted at `eraseEnv pinAccEnvA` — the named
    obstruction at class (a). -/
theorem not_envCorrAnnCert_pinAcc :
    ¬ EnvCorrAnnCert (eraseEnv pinAccEnvA) := by
  intro h
  have h' := h wPinAccS
  rw [pin_iotaWitnessSAnnB_wPinAccS] at h'
  exact Bool.noConfusion h'

/-- the frec-aware recognizer accepts the same witness: the decided
    `fieldShapesE` agreement holds (`fieldShapesE` reads
    `[.nonrecursive, .recursive 2]` on `intro`'s domains), and the
    `applyTel`/`fieldsTelS`/schema-`rhsArgsS` conjuncts compute through. -/
theorem pin_iotaWitnessSAnnBF_wPinAccS :
    iotaWitnessSAnnBF (eraseEnv pinAccEnvA) wPinAccS = true := rfl

/-! ## (3) the erased environment's member census -/

/-- `eraseEnv pinAccEnvA`'s members are exactly the axiom `R` at `9` and the
    erased group at `10`–`12`. -/
theorem pinAcc_erase_mem {r : Nat} {m : CheckedMember}
    (h : (eraseEnv pinAccEnvA).members r = some m) :
    (r = 9 ∧ m = paRelT) ∨ (r = 10 ∧ m = paFamT) ∨
      (r = 11 ∧ m = paIntroT) ∨ (r = 12 ∧ m = paRecT) := by
  match r with
  | 9 =>
      left
      rw [show (eraseEnv pinAccEnvA).members 9 = some paRelT from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 10 =>
      right; left
      rw [show (eraseEnv pinAccEnvA).members 10 = some paFamT from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 11 =>
      right; right; left
      rw [show (eraseEnv pinAccEnvA).members 11 = some paIntroT from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 12 =>
      right; right; right
      rw [show (eraseEnv pinAccEnvA).members 12 = some paRecT from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | r + 13 =>
      rw [show (eraseEnv pinAccEnvA).members (r + 13) = none from rfl] at h
      exact Option.noConfusion h
  | 0 =>
      rw [show (eraseEnv pinAccEnvA).members 0 = none from rfl] at h
      exact Option.noConfusion h
  | 1 =>
      rw [show (eraseEnv pinAccEnvA).members 1 = none from rfl] at h
      exact Option.noConfusion h
  | 2 =>
      rw [show (eraseEnv pinAccEnvA).members 2 = none from rfl] at h
      exact Option.noConfusion h
  | 3 =>
      rw [show (eraseEnv pinAccEnvA).members 3 = none from rfl] at h
      exact Option.noConfusion h
  | 4 =>
      rw [show (eraseEnv pinAccEnvA).members 4 = none from rfl] at h
      exact Option.noConfusion h
  | 5 =>
      rw [show (eraseEnv pinAccEnvA).members 5 = none from rfl] at h
      exact Option.noConfusion h
  | 6 =>
      rw [show (eraseEnv pinAccEnvA).members 6 = none from rfl] at h
      exact Option.noConfusion h
  | 7 =>
      rw [show (eraseEnv pinAccEnvA).members 7 = none from rfl] at h
      exact Option.noConfusion h
  | 8 =>
      rw [show (eraseEnv pinAccEnvA).members 8 = none from rfl] at h
      exact Option.noConfusion h

/-! ## (4) census corollaries: refs pinned by member class -/

/-- the only `.inductiveM` member of the erased environment is `AccT` at `10`. -/
theorem pinAcc_fam_ref {r : Nat} {m : CheckedMember}
    (h : (eraseEnv pinAccEnvA).members r = some m)
    (hk : m.mclass = MemberClass.inductiveM) : r = 10 ∧ m = paFamT := by
  rcases pinAcc_erase_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

/-- the only `.constructorM` member is `intro` at `11`. -/
theorem pinAcc_ctor_ref {r : Nat} {m : CheckedMember}
    (h : (eraseEnv pinAccEnvA).members r = some m)
    (hk : m.mclass = MemberClass.constructorM) : r = 11 ∧ m = paIntroT := by
  rcases pinAcc_erase_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact ⟨rfl, rfl⟩
  · exact absurd hk (by decide)

/-- the only `.recursorM` member is `AccT.rec` at `12`. -/
theorem pinAcc_rec_ref {r : Nat} {m : CheckedMember}
    (h : (eraseEnv pinAccEnvA).members r = some m)
    (hk : m.mclass = MemberClass.recursorM) : r = 12 ∧ m = paRecT := by
  rcases pinAcc_erase_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact ⟨rfl, rfl⟩

/-! ## (5) `EnvCorrEraseCert` — vacuous: no legacy `IotaWitness` exists

Every `IotaWitness` over `eraseEnv pinAccEnvA` must name the unique inductive
`10`/constructor `11`/`recursor `12` triple, peel `intro`'s two domains, and
ask `analyzeFields` for kinds — which returns `none` on the `.frec` domain
`Π (y:S0), R y x → AccT y` at either legal `nparams` (`nparams + nindices = 1`
bounds it by `1`). -/

theorem pinAcc_envCorrEraseCert : EnvCorrEraseCert (eraseEnv pinAccEnvA) := by
  intro w
  obtain ⟨hfr, hfm⟩ := pinAcc_fam_ref w.hfam w.hfamK
  obtain ⟨hcr, hcm⟩ := pinAcc_ctor_ref w.hctor w.hctorK
  have hnidx := w.hnidx
  rw [hfm] at hnidx
  rw [show piCount paFamT.mtype = 1 from rfl] at hnidx
  have hnpar := w.hnpar
  rw [hcm] at hnpar
  rw [show piCount paIntroT.mtype = 2 from rfl] at hnpar
  have hpeel := w.hpeel
  rw [hcm, hnpar] at hpeel
  rw [show peelPis 2 paIntroT.mtype =
    some ([.sort .zero, paFieldDom], .app (.const 10 []) (.bvar 1)) from rfl]
    at hpeel
  obtain ⟨hdoms, _⟩ := Prod.mk.inj (Option.some.inj hpeel)
  have hkinds := w.hkinds
  rw [hfr, ← hdoms] at hkinds
  have hnp : w.nparams ≤ 1 := by omega
  rcases Nat.lt_or_ge w.nparams 1 with h0 | h1
  · have hnp0 : w.nparams = 0 := by omega
    rw [hnp0, List.drop_zero] at hkinds
    rw [show analyzeFields 10 [.sort .zero, paFieldDom] = none from rfl] at hkinds
    exact Option.noConfusion hkinds
  · have hnp1 : w.nparams = 1 := by omega
    rw [hnp1, show ([.sort .zero, paFieldDom] : List (Expr Nat)).drop 1 =
      [paFieldDom] from rfl] at hkinds
    rw [show analyzeFields 10 [paFieldDom] = none from rfl] at hkinds
    exact Option.noConfusion hkinds

/-! ## (6) `EnvCorrAnnCertF` — the universal discharge -/

/-- the canonical fuel read of the marker-substituted field domain, at ANY
    sufficient fuel (the fuel-`24` `paFieldDomM_canon` generalized; the domain
    is whnf-stable so only `piCount + 2 = 4` is needed). -/
theorem paFieldDomM_canonF {fuel : Nat} (hf : 4 ≤ fuel) :
    piTelescopeFuel (eraseEnv pinAccEnvA) fuel paFieldDomM =
      some ((piTelE paFieldDomM).1, (piTelE paFieldDomM).2) := by
  rw [piTelE_piDomsOf paFieldDomM]
  exact piTelescopeFuel_of_tailStable paFieldDomM rfl rfl hf

/-- `paSupplies` at an arbitrary fuel ≥ `4`: the two-field walk is identical
    (the only fuel-dependent premise is `hcanon`). -/
theorem pinAccSuppliesF (X : List (Expr Nat)) (ls : List Level) {fuel : Nat}
    (hf : 4 ≤ fuel) :
    WalkSuppliesC (eraseEnv pinAccEnvA) fuel X ls 0 1 [.bvar 1, .bvar 0]
      [.nonrecursive, .recursive 2]
      (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1)))) := by
  refine WalkSuppliesC.supNonrec 1 [.bvar 0] [.recursive 2] (.sort .zero)
    (.pi paFieldDom (.app (.const 10 []) (.bvar 1))) ?_
  show WalkSuppliesC (eraseEnv pinAccEnvA) fuel X ls 0 1 [.bvar 0]
      [.recursive 2]
      (.pi paFieldDomM (.app (.const 10 []) (.bvar 2)))
  refine WalkSuppliesC.supFrec 0 [] [] paFieldDomM
    (.app (.const 10 []) (.bvar 2)) 1 (paFieldDomM_canonF hf) rfl
    (paFieldDomM_hARtel X ls) (paFieldDomM_hidx X ls)
    (WalkSuppliesC.supNil [] _ rfl)

/-- Every `IotaWitnessS` over the erased pinAcc environment passes the
    frec-aware recognizer.  The member census pins the group
    (`familyRef = 10`, `ctorRef = 11`, `recRef = 12`), `hrecIdx`/`hctorIdx`
    pin `nMinors = 1`/`ctorIdx = 0`, `hpeel` pins the constructor domains and
    result, `hmajorTy` kills `nparams = 1` (its `bvar 2` index variable does
    not match the stored `bvar 0`), `hshapes` + fuel-agreement pin
    `w.shapes = [.nonrecursive, .recursive 2]`, and the fieldAnalyze inversion
    gives `w.fuel ≥ 5` — enough for `hcanon`.  The free data (`fields`,
    `preMajor`, `ls`, `fuel`, `schema`) survives symbolically:
    `fieldsTelS`/`rhsArgsS` only inspect the field POSITIONS. -/
theorem pinAcc_envCorrAnnCertF : EnvCorrAnnCertF (eraseEnv pinAccEnvA) := by
  intro w
  obtain ⟨hfr, hfm⟩ := pinAcc_fam_ref w.hfam w.hfamK
  obtain ⟨hcr, hcm⟩ := pinAcc_ctor_ref w.hctor w.hctorK
  obtain ⟨hrr, hrm⟩ := pinAcc_rec_ref w.hrec w.hrecK
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hfr, hrr] at h; omega
  have hci : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hfr, hcr] at h; omega
  have hnidx := w.hnidx
  rw [hfm, show piCount paFamT.mtype = 1 from rfl] at hnidx
  have hnpar := w.hnpar
  rw [hcm, show piCount paIntroT.mtype = 2 from rfl] at hnpar
  have hpeel := w.hpeel
  rw [hcm, hnpar] at hpeel
  rw [show peelPis 2 paIntroT.mtype =
    some ([.sort .zero, paFieldDom], .app (.const 10 []) (.bvar 1)) from rfl]
    at hpeel
  obtain ⟨hdoms, hres⟩ := Prod.mk.inj (Option.some.inj hpeel)
  have hpeelR := w.hpeelRec
  rw [hrm] at hpeelR
  have hcnt4 : w.nparams + 1 + w.nMinors + w.nindices + 1 = 4 := by omega
  rw [hcnt4, show peelPis 4 paRecT.mtype = some (paRecDoms,
    .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) from rfl] at hpeelR
  obtain ⟨hrd, _⟩ := Prod.mk.inj (Option.some.inj hpeelR)
  have hnp : w.nparams = 0 := by
    by_cases h0 : w.nparams = 0
    · exact h0
    · have hnp1 : w.nparams = 1 := by omega
      have hni0 : w.nindices = 0 := by omega
      have hm := w.hmajorTy
      rw [hfr, hfm, ← hrd, hnp1, hni0, hnM] at hm
      rw [show paRecDoms[1 + 1 + 1 + 0]? = some (.app (.const 10 []) (.bvar 0))
        from rfl] at hm
      rw [show ((List.range 1).reverse.map
            (fun i => Expr.bvar (i + 0 + 1 + 1)) ++
            (List.range 0).reverse.map (fun i => Expr.bvar i) :
            List (Expr Nat)) = [.bvar 2] from rfl] at hm
      rw [show (foldApps (.const 10
            ((List.range paFamT.arity).map Level.param)) [.bvar 2] :
            Expr Nat) = .app (.const 10 []) (.bvar 2) from rfl] at hm
      exact absurd hm (by decide)
  have hni : w.nindices = 1 := by omega
  have hfl : w.fields.length = 2 := by omega
  have hsh := w.hshapes
  rw [hfr, hfm, hnp, hni, ← hdoms, List.drop_zero] at hsh
  have h24 : fieldShapesFuel (eraseEnv pinAccEnvA) 24 10 paFamT.arity 0 1 0
      [.sort .zero, paFieldDom] = some [.nonrecursive, .recursive 2] := rfl
  have hshapes : w.shapes = [.nonrecursive, .recursive 2] :=
    fieldShapesFuel_agree _ hsh h24
  -- fuel bound: the `.recursive 2` verdict ran `piTelescopeFuel` at `w.fuel - 1`
  rw [hshapes] at hsh
  have hfa1 : ∃ idxR, fieldAnalyze (eraseEnv pinAccEnvA) w.fuel 10
      paFamT.arity 0 1 1 paFieldDom = .permitted (.recursive 2) idxR := by
    unfold fieldShapesFuel at hsh
    cases hfa0 : fieldAnalyze (eraseEnv pinAccEnvA) w.fuel 10 paFamT.arity 0 1
        0 (.sort .zero) with
    | permitted s0 idx0 =>
        rw [hfa0] at hsh
        simp only [Option.map_eq_some'] at hsh
        obtain ⟨ss1, hrest, heq⟩ := hsh
        obtain ⟨rfl, hss1⟩ := List.cons.inj heq
        rw [hss1] at hrest
        unfold fieldShapesFuel at hrest
        cases hfa1 : fieldAnalyze (eraseEnv pinAccEnvA) w.fuel 10 paFamT.arity
            0 1 1 paFieldDom with
        | permitted s1 idx1 =>
            rw [hfa1] at hrest
            simp only [Option.map_eq_some'] at hrest
            obtain ⟨ss0, hrest0, heq1⟩ := hrest
            obtain rfl := (List.cons.inj heq1).1
            exact ⟨idx1, rfl⟩
        | refused r => rw [hfa1] at hrest; exact Option.noConfusion hrest
        | unresolved => rw [hfa1] at hrest; exact Option.noConfusion hrest
    | refused r => rw [hfa0] at hsh; exact Option.noConfusion hsh
    | unresolved => rw [hfa0] at hsh; exact Option.noConfusion hsh
  obtain ⟨idxR, hfa1'⟩ := hfa1
  obtain ⟨doms2, _body2, hpt, hlen2, -, -⟩ := fieldAnalyze_recursive_out hfa1'
  have hfuel : 5 ≤ w.fuel := by
    have hlow := piTelescopeFuel_some_lower (eraseEnv pinAccEnvA) (w.fuel - 1) hpt
    omega
  -- destructure the free list data
  obtain ⟨f0, f1, hfe⟩ : ∃ a b, w.fields = [a, b] := by
    match w.fields, hfl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨p0, p1, p2, hpm⟩ : ∃ a b c, w.preMajor = [a, b, c] := by
    have hl : w.preMajor.length = 3 := by
      have h := w.hpre; rw [hnp, hnM, hni] at h; omega
    match w.preMajor, hl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨l, hls⟩ : ∃ a, w.ls = [a] := by
    have h := w.hlsLen; rw [hrm] at h
    have h1 : w.ls.length = 1 := by
      have : paRecT.arity = 1 := rfl; omega
    match w.ls, h1 with
    | [a], _ => exact ⟨a, rfl⟩
  -- the supplies at w.fuel
  have hsup : WalkSuppliesC (eraseEnv pinAccEnvA) w.fuel
      (w.preMajor ++ w.fields) w.ls w.nparams w.nMinors
      (fieldBvars w.fields.length) w.shapes
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) := by
    rw [hnp, hnM, hfl, hni, hshapes, ← hdoms, ← hres]
    show WalkSuppliesC (eraseEnv pinAccEnvA) w.fuel (w.preMajor ++ w.fields)
        w.ls 0 1 [.bvar 1, .bvar 0] [.nonrecursive, .recursive 2]
        (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1))))
    exact pinAccSuppliesF _ _ (by omega)
  -- the recognizer
  unfold iotaWitnessSAnnBF
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [hfr, hnp, ← hdoms, List.drop_zero, hshapes]
    exact decide_eq_true_iff.mpr rfl
  · rw [hnp, hci, hcm, hls]
    rw [show w.preMajor.take 0 = ([] : List (Expr Nat)) from List.take_zero _]
    rw [show [l].take paIntroT.arity = ([] : List Level) from rfl]
    rw [show applyTel []
        (instantiateLevels [] paIntroT.mtype) =
        some (instantiateLevels [] paIntroT.mtype) from rfl]
    rw [hfe, hshapes, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rfl
    · have hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some p1 := by
        rw [hnp, hci, hpm]; rfl
      rw [show w.preMajor[0 + 1 + 0]? = some p1 by rw [hpm]; rfl]
      rw [decide_eq_true_iff]
      have hctorAfter : ctorAfterFieldTel w =
          instantiateLevels [] paIntroT.mtype := by
        rw [ctorAfterFieldTel_eq_ctorFieldTelInst]
        show instPrefix (w.preMajor.take w.nparams)
            (instantiateLevels (w.ls.take w.ctorMember.arity)
              (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = _
        rw [hnp, hcm, hls, ← hdoms, ← hres]
        rfl
      have heq := iotaRhsOfS_eq_rhsArgsS_ctorAfter paEnvWfT_erase w hsup hm
      rw [hctorAfter] at heq
      rw [hrr, hls, hpm, hnp, hnM, hfe, hshapes] at heq
      rw [hrr, hpm, hnM]
      exact heq

/-! ## (7) class (a) composed: the full correspondence on `pinAccEnvA` -/

/-- `IotaAnnotatesUA` at `pinAccEnvA`: the annotation direction of the union
    ι-correspondence, through the frec-aware certificate. -/
theorem pinAcc_iotaAnnotatesUA : IotaAnnotatesUA pinAccEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinAccRecTyAt0
  exact iotaAnnotatesUA_of_envWfAF (pinAccWfA w hT0) pinAcc_normErase
    pinAcc_envCorrEraseCert pinAcc_envCorrAnnCertF

/-- THE CLASS-(a) PAYOFF, ANNOTATION SIDE INCLUDED: `IotaCorrTUA pinAccEnvA` —
    both directions of the union ι-correspondence at the indexed-Acc frec
    environment.  `eraseT` is `pinAcc_iotaErasesTUA`'s route through
    `iotaErasesTUA_frecR`; `ann` is the new frec-aware path — the strict
    `EnvCorrAnnCert` remains refuted (`not_envCorrAnnCert_pinAcc`), by design. -/
theorem pinAcc_iotaCorrTUA : IotaCorrTUA pinAccEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinAccRecTyAt0
  exact iotaCorrTUA_frecRA (pinAccWfA w hT0) pinAcc_normErase paEnvWfT_erase 24
    pinAcc_envCorrEraseCert pinAcc_envCorrAnnCertF (fun _ _ _ _ _ => pinAcc_gates)

#print axioms pinAcc_envCorrEraseCert
#print axioms pinAcc_envCorrAnnCertF
#print axioms pinAcc_iotaAnnotatesUA
#print axioms pinAcc_iotaCorrTUA

end Rcic.Declarative.Ann
