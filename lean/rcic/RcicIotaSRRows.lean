import rcic.RcicIotaSRRowsCtor
import rcic.RcicAnnSemPrefixRows
import rcic.RcicDerivedIotaU

/-!
# DT-019 / IA-024 S1 — typed ι subject reduction at `EnvWfT`, modulo the rows

`iotaPreserveT_rows`: for `DerivedIotaT` evidence (the typed root's shape-based
ι relation), under `EnvWfT E` and the three typed chain rows `TypedRowsWf E n`
— no certificate — the reduct is typed at the redex's own type. The premise
shares DT-010/DT-011's `TypedRowsWf` wall (`step_srT_rows`,
`RcicDT1011Rows.lean`); it is NOT literally their premise set: those also take
`hiota : IotaSRTN E n`, a front over the LEGACY `DerivedIota`, which this
theorem (over `DerivedIotaT`) does not discharge. `iotaPreserveTT_noCert` is the `InScope` corollary
(`typedRowsWf_of_envWfT_semPrefix` supplies the rows): `iotaPreserveTT`'s
signature with `CorrCertsBelow` dropped.

The proof never enters the annotated copy. It reads admission's typed ι
equation (`IotaEquationTypedT`, a field of every `EnvWfT` group, connected to the
witness by package B, gate-free here), instantiates it at the redex's universes
and arguments (package A), and aligns the result with the redex's type through
the Π row (spine inversion) and ROW 3 (`famAppRow`) — the constructor side of
`RcicIotaSRRowsCtor`. Shape-agnostic: `.frec`, `.drecD`, the recognizer's fuel —
none enters.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) the instantiation computations -/

theorem bvars_map_instantiateLevels (L : List Level) (f : Nat → Nat) (l : List Nat) :
    (l.map (fun i => (Expr.bvar (f i) : Expr Nat))).map (instantiateLevels L) =
      l.map (fun i => (Expr.bvar (f i) : Expr Nat)) := by
  rw [List.map_map]; rfl

theorem policyLocals_eq_shifted (q : Nat) :
    policyLocals q = (List.range q).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat)) := rfl

theorem fieldBvars_eq_shifted (q : Nat) :
    fieldBvars q = (List.range q).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat)) := rfl

theorem outerDom_reverse (l : List (Expr Nat)) (k : Nat) (hk : k < l.length) :
    outerDom l.reverse k = l[k] := by
  have := outerDom_take_reverse l l.length k (Nat.le_refl _) hk
  rwa [List.take_length] at this

theorem instLvlsCtx_assumptionCtx (L : List Level) (l : List (Expr Nat)) :
    instLvlsCtx L (assumptionCtx l) = assumptionCtx (l.map (instantiateLevels L)) := by
  simp only [instLvlsCtx, assumptionCtx, List.map_map, List.map_reverse]; rfl

/-- the recursor's innermost body instantiated at the whole spine: the motive applied to
    the redex's indices and the major. -/
theorem instPrefix_recBody (pre : List (Expr Nat)) (major : Expr Nat) (np k q : Nat)
    (hlen : pre.length = np + 1 + k + q) (M : Expr Nat) (hM : pre[np]? = some M) (L : List Level) :
    instPrefix (pre ++ [major]) (instantiateLevels L (policyRecBody k q)) =
      foldApps M (pre.drop (np + 1 + k) ++ [major]) := by
  simp only [policyRecBody]
  rw [foldApps_instantiateLevels, List.map_append, bvars_map_instantiateLevels L (fun i => i + 1)]
  simp only [List.map_cons, List.map_nil, instantiateLevels]
  rw [instPrefix_foldApps, List.map_append, List.map_cons, List.map_nil]
  have hlen' : (pre ++ [major]).length = pre.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [instPrefix_bvar_lt (args := pre ++ [major]) (j := k + q + 1) (a := M)
    (by rw [hlen', hlen]; omega)
    (by rw [hlen', hlen, show np + 1 + k + q + 1 - 1 - (k + q + 1) = np by omega,
      List.getElem?_append_left (by rw [hlen]; omega), hM])]
  rw [instPrefix_bvar_lt (args := pre ++ [major]) (j := 0) (a := major)
    (by rw [hlen']; omega)
    (by rw [hlen', Nat.add_sub_cancel, Nat.sub_zero, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]; rfl)]
  rw [instPrefix_shiftedSpine (pre ++ [major]) q 1 (np + 1 + k) (by rw [hlen', hlen])]
  rw [List.drop_append_of_le_length (by rw [hlen]; omega)]
  rw [List.take_left' (by rw [List.length_drop, hlen]; try omega)]

/-- the recursor's major domain instantiated at the pre-major spine: the family at the
    redex's parameters and indices. -/
theorem instPrefix_majorDom {E : ResolvedEnv} (pre : List (Expr Nat)) (fam : PolicyFamilyView E)
    (k : Nat) (L : List Level)
    (hlen : pre.length = fam.parameters.length + 1 + k + fam.indices.length) :
    instPrefix pre (instantiateLevels L (policyMajorDom fam k)) =
      foldApps (.const fam.ref ((policyFamilyLevels fam).map (instLevel L)))
        (pre.take fam.parameters.length ++ pre.drop (fam.parameters.length + 1 + k)) := by
  simp only [policyMajorDom]
  rw [instPrefix_famApp pre fam.parameters.length (k + 1 + fam.indices.length) fam.ref
    (policyFamilyLevels fam) L (policyLocals fam.indices.length) (by rw [hlen]; omega)]
  congr 2
  rw [policyLocals_eq_shifted]
  have hm : ((List.range fam.indices.length).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat))).map
      (fun x => instPrefix pre (instantiateLevels L x)) =
      ((List.range fam.indices.length).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat))).map
        (instPrefix pre) := by
    rw [List.map_map, List.map_map]; rfl
  rw [hm, instPrefix_shiftedSpine pre fam.indices.length 0 (fam.parameters.length + 1 + k)
    (by rw [hlen]; omega)]
  rw [List.take_of_length_le (by rw [List.length_drop, hlen]; omega)]

/-- the family applied to all the locals, instantiated: the family at the arguments. -/
theorem instPrefix_Iapp (args : List (Expr Nat)) (r : Nat) (lvls L : List Level) {c : Nat}
    (hlen : args.length = c) :
    instPrefix args (instantiateLevels L (foldApps (.const r lvls) (policyLocals c))) =
      foldApps (.const r (lvls.map (instLevel L))) args := by
  rw [foldApps_instantiateLevels, instPrefix_foldApps]
  simp only [instantiateLevels, instPrefix_const]
  congr 1
  rw [policyLocals_eq_shifted, bvars_map_instantiateLevels L (fun i => i + 0)]
  rw [instPrefix_shiftedSpine args c 0 0 (by omega)]
  simp only [List.drop_zero]
  exact List.take_of_length_le (Nat.le_of_eq hlen)

/-- the policy motive type, instantiated at the recursor-side parameters: a telescope over
    the (instantiated) index domains and the family application, ending in the motive sort. -/
theorem instPrefix_motiveType {E : ResolvedEnv} (p : List (Expr Nat)) (fam : PolicyFamilyView E)
    (policy : EliminationPolicy) (L : List Level) :
    instPrefix p (instantiateLevels L (policyMotiveType fam policy)) =
      policyPi (instDomsK 0 p ((fam.indices ++
        [foldApps (.const fam.ref (policyFamilyLevels fam))
          (policyLocals (fam.parameters.length + fam.indices.length))]).map (instantiateLevels L)))
        (.sort (instLevel L (policyMotiveLevel fam.member.arity policy))) := by
  simp only [policyMotiveType]
  change instPrefix p (instantiateLevels L (policyPi fam.indices (policyPi
    [foldApps (.const fam.ref (policyFamilyLevels fam))
      (policyLocals (fam.parameters.length + fam.indices.length))]
    (.sort (policyMotiveLevel fam.member.arity policy))))) = _
  rw [← policyPi_append, instantiateLevels_policyPi, instPrefix_policyPi, instantiateLevels_sort',
    instTelK_sort]

/-- the equation's type, instantiated at the redex (parameters, then the middle binders
    the lift skipped, then the fields): the motive at the instantiated result indices and
    the recursor-side constructor application. -/
theorem instPrefix_eqTy (p mid fs : List (Expr Nat)) (ctorRef : Nat) (lvls L : List Level)
    (np k q fl : Nat) (res : List (Expr Nat))
    (hp : p.length = np) (hmid : mid.length = 1 + k + q) (hfs : fs.length = fl)
    (M : Expr Nat) (hM : mid[0]? = some M) :
    instPrefix (p ++ mid ++ fs) (instantiateLevels L (iotaLhsType ctorRef lvls np k q fl res)) =
      foldApps M (res.map (fun r => instPrefix (p ++ fs) (instantiateLevels L r)) ++
        [foldApps (.const ctorRef (lvls.map (instLevel L))) (p ++ fs)]) := by
  simp only [iotaLhsType]
  rw [foldApps_instantiateLevels, List.map_append, List.map_cons, List.map_nil]
  simp only [instantiateLevels]
  rw [instPrefix_foldApps, List.map_append, List.map_cons, List.map_nil]
  have hσ : (p ++ mid ++ fs).length = np + (1 + k + q) + fl := by
    simp only [List.length_append, hp, hmid, hfs]
  -- the motive
  rw [instPrefix_bvar_lt (args := p ++ mid ++ fs) (j := fl + q + k) (a := M)
    (by rw [hσ]; omega)
    (by rw [hσ, show np + (1 + k + q) + fl - 1 - (fl + q + k) = np by omega,
      List.getElem?_append_left (by simp only [List.length_append, hp, hmid]; omega),
      List.getElem?_append_right (by rw [hp]; exact Nat.le_refl _), hp, Nat.sub_self, hM])]
  -- the result indices
  have hidx : ((res.map (fun r => lift fl (1 + k + q) r)).map (instantiateLevels L)).map
      (instPrefix (p ++ mid ++ fs)) =
      res.map (fun r => instPrefix (p ++ fs) (instantiateLevels L r)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro r _
    show instPrefix (p ++ mid ++ fs) (instantiateLevels L (lift fl (1 + k + q) r)) = _
    rw [← lift_instantiateLevels, ← hfs, ← hmid, instPrefix_lift_mid]
  rw [hidx]
  -- the constructor application
  congr 2
  rw [instPrefix_famApp (p ++ mid ++ fs) np (fl + q + k + 1) ctorRef lvls L (fieldBvars fl)
    (by rw [hσ]; omega)]
  rw [List.append_assoc, List.take_left' hp, ← List.append_assoc]
  congr 1
  rw [fieldBvars_eq_shifted]
  have hm : ((List.range fl).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat))).map
      (fun x => instPrefix (p ++ mid ++ fs) (instantiateLevels L x)) =
      ((List.range fl).reverse.map (fun i => (Expr.bvar (i + 0) : Expr Nat))).map
        (instPrefix (p ++ mid ++ fs)) := by
    rw [List.map_map, List.map_map]; rfl
  rw [hm, instPrefix_shiftedSpine (p ++ mid ++ fs) fl 0 (np + (1 + k + q)) (by rw [hσ]; omega)]
  rw [List.drop_append_of_le_length (by simp only [List.length_append, hp, hmid]; exact Nat.le_refl _)]
  rw [List.drop_of_length_le (by simp only [List.length_append, hp, hmid]; exact Nat.le_refl _),
    List.nil_append, List.take_of_length_le (Nat.le_of_eq hfs)]

/-! ## (2) the theorem -/

set_option maxHeartbeats 2000000 in
/-- **DT-019 / IA-024 at `EnvWfT`, modulo the rows.** ι subject reduction for the typed
    root's shape-based evidence: under a well-formed environment and the three typed
    chain rows — DT-010/DT-011's `TypedRowsWf` wall, not their legacy `IotaSRTN` front —
    the reduct is typed at the redex's own type. No certificate: the reduct is admission's own typed equation, instantiated. -/
theorem iotaPreserveT_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  cases hd with
  | of w =>
  have c : RecursorCellHT E w.recRef w.recMember := envWfT_cellHT hW w.hrec w.hrecK
  obtain ⟨hfam, hfamM, hnp, hni, hnm⟩ :=
    IotaWitnessS.recData_admitted c.cell.adm c.cell.sub w rfl rfl
  obtain ⟨hrecDoms, hrecBody⟩ := w.recDoms_eq c.cell.adm hnp hni hnm
  have hminors : c.cell.adm.minorTypes.length = w.nMinors := by rw [c.cell.adm.minorCount, hnm]
  have hrecLen : w.recDoms.length = w.nparams + 1 + w.nMinors + w.nindices + 1 :=
    peelPis_length _ _ w.hpeelRec
  have hpre := w.hpre
  have hplen : (recP w).length = w.nparams := recP_length w
  -- (1) the lhs spine
  have hrecPi : instantiateLevels w.ls w.recMember.mtype =
      policyPi (w.recDoms.map (instantiateLevels w.ls)) (instantiateLevels w.ls w.recBody) := by
    rw [policyPi_of_peelPis _ _ w.hpeelRec, instantiateLevels_policyPi]
  have hlhs' : HasTyT E n Γ (foldApps (.const w.recRef w.ls) (w.preMajor ++ [majorW w])) T := hlhs
  obtain ⟨hlsLen, hwf, preArgs, convL⟩ := hasTyT_spineInv_rows hW hrows.piRow hΓ w.hrec hrecPi
    (w.preMajor ++ [majorW w])
    (by simp only [List.length_map, List.length_append, List.length_cons, List.length_nil, hrecLen, hpre])
    hlhs'
  have preArgsP : ArgsAt E n Γ w.ls w.recDoms w.preMajor := by
    intro k x d hx hd
    have hk : k < w.preMajor.length := (List.getElem?_eq_some_iff.mp hx).1
    have := preArgs k x (instantiateLevels w.ls d) (by rw [List.getElem?_append_left hk]; exact hx)
      (by rw [List.getElem?_map, hd]; rfl)
    rw [List.take_append_of_le_length (Nat.le_of_lt hk)] at this
    exact this
  have pTyped : ∀ k x d, w.preMajor[k]? = some x → k < w.nparams →
      c.cell.adm.family.parameters[k]? = some d →
      HasTyT E n Γ x (instPrefix (w.preMajor.take k) (instantiateLevels w.ls d)) := by
    intro k x d hx hk hd
    apply preArgsP k x d hx
    rw [hrecDoms, policyRecDoms_getElem?_param _ _ _ k (by rw [← hnp]; exact hk)]
    exact hd
  -- the major
  have hmajorDom : w.recDoms[w.preMajor.length]? =
      some (policyMajorDom c.cell.adm.family c.cell.adm.minorTypes.length) := by
    rw [hrecDoms, hpre, hnp, hni, ← hminors]
    exact policyRecDoms_getElem?_major _ _ _
  have hmajorTy_eq : instPrefix w.preMajor (instantiateLevels w.ls
      (policyMajorDom c.cell.adm.family c.cell.adm.minorTypes.length)) = majorTyW w := by
    rw [instPrefix_majorDom _ _ _ _ (by rw [hpre, hnp, hni, hminors])]
    simp only [majorTyW, famL1, recP, recIdx, hfam, hfamM, hnp, hminors, policyFamilyLevels]
  have hmajor : HasTyT E n Γ (majorW w) (majorTyW w) := by
    have h := preArgs w.preMajor.length (majorW w) _
      (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
      (by rw [List.getElem?_map, hmajorDom]; rfl)
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, hmajorTy_eq] at h
    exact h
  have hAM : ∃ u, Nonempty (HasTyT E n Γ (majorTyW w) (.sort u)) := by
    have hT0 := hasTyTExt c.cell.env_extends c.hT
    have hT1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hwf hlsLen hT0
    rw [instLvlsCtx_nil, hrecPi] at hT1
    obtain ⟨hdoms, _⟩ := hasTyT_policyPi_inv _ hT1
    have hlt : w.preMajor.length < (w.recDoms.map (instantiateLevels w.ls)).length := by
      simp only [List.length_map, hrecLen, hpre]; omega
    obtain ⟨v, ⟨hv⟩⟩ := hdoms w.preMajor.length hlt
    rw [List.append_nil] at hv
    have hv' := hasTyT_relocateN (Γ := Γ) hv
    have hd' : (w.recDoms.map (instantiateLevels w.ls))[w.preMajor.length]'hlt =
        instantiateLevels w.ls (policyMajorDom c.cell.adm.family c.cell.adm.minorTypes.length) := by
      rw [List.getElem_map]
      have := hmajorDom
      rw [List.getElem?_eq_getElem (by simp only [List.length_map] at hlt; exact hlt)] at this
      rw [Option.some.inj this]
    rw [hd'] at hv'
    refine ⟨v, ⟨?_⟩⟩
    have h := hasTyT_instPrefix_of_envWfT hW
      (ΔT := ((w.recDoms.map (instantiateLevels w.ls)).take w.preMajor.length).reverse)
      (args := w.preMajor)
      (by simp only [List.length_reverse, List.length_take, List.length_map, hrecLen, hpre]; omega)
      hv' (argsAt_pkgA (by rw [hrecLen, hpre]; omega) preArgsP)
    rw [instPrefix_sort, hmajorTy_eq] at h
    exact h
  -- (2) the constructor side
  obtain ⟨cs⟩ := ctorSide hW hrows hΓ w c hlsLen hwf hmajor hAM pTyped
  have hcm := c.cell.ctorMember_eq w hfam cs.i cs.hi
  obtain ⟨hdoms, _⟩ := c.cell.ctorData_eq w cs.i hcm
  have hfl : w.fields.length = (c.cell.adm.constructorViews cs.i).fields.length := by
    have h1 := peelPis_length _ _ w.hpeel
    rw [hdoms, List.length_append, (c.cell.adm.constructorViews cs.i).parameterCount, ← hnp] at h1
    omega
  have hq : (c.cell.adm.constructorViews cs.i).resultIndices.length = w.nindices := by
    rw [(c.cell.adm.constructorViews cs.i).indexCount, hni]
  -- (3) the admission equation at the witness
  obtain ⟨hgF, hgT⟩ := c.ctorFields_closed cs.i
  obtain ⟨doms, hd, ⟨hEq⟩⟩ := iotaWitnessS_rhs_typed_closed w c.cell cs.i cs.hi hgF hgT
  have hdoms_eq : doms = w.recDoms.dropLast ++
      liftFields (1 + c.cell.adm.constructors.length + c.cell.adm.family.indices.length)
        (c.cell.adm.constructorViews cs.i).fields 0 := by
    have hpc : piCount w.recMember.mtype = w.nparams + 1 + w.nMinors + w.nindices + 1 := w.hnmin.symm
    simp only [equationDoms, hpc, w.hpeelRec] at hd
    exact (Option.some.inj hd).symm
  -- (4) transport the equation to the redex
  have hEq1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hwf hlsLen hEq
  rw [instLvlsCtx_assumptionCtx] at hEq1
  have hEq2 := hasTyT_relocateN (Γ := Γ) hEq1
  have hmidlen : (w.preMajor.drop w.nparams).length =
      1 + c.cell.adm.constructors.length + c.cell.adm.family.indices.length := by
    rw [List.length_drop, hpre, ← hnm, ← hni]; omega
  have hsplit : w.preMajor = recP w ++ w.preMajor.drop w.nparams := (List.take_append_drop _ _).symm
  have hdomslen : doms.length = w.preMajor.length + w.fields.length := by
    rw [hdoms_eq, List.length_append, List.length_dropLast, hrecLen, liftFields_length, hpre, hfl]
    omega
  have σArgs : ArgsAt E n Γ w.ls doms (w.preMajor ++ w.fields) := by
    intro k x d hx hd
    by_cases hkp : k < w.preMajor.length
    · have hdk : doms[k]? = w.recDoms[k]? := by
        rw [hdoms_eq, List.getElem?_append_left (by rw [List.length_dropLast, hrecLen]; omega),
          List.getElem?_dropLast, if_pos (by rw [hrecLen]; omega)]
      rw [List.getElem?_append_left hkp] at hx
      rw [List.take_append_of_le_length (Nat.le_of_lt hkp)]
      exact preArgsP k x d hx (by rw [← hdk]; exact hd)
    · have hkf : w.preMajor.length ≤ k := Nat.le_of_not_lt hkp
      have hk : k < (w.preMajor ++ w.fields).length := (List.getElem?_eq_some_iff.mp hx).1
      have hj : k - w.preMajor.length < w.fields.length := by
        simp only [List.length_append] at hk; omega
      have hjc : k - w.preMajor.length < (c.cell.adm.constructorViews cs.i).fields.length := by
        rw [← hfl]; exact hj
      have hlenDL : w.recDoms.dropLast.length = w.preMajor.length := by
        rw [List.length_dropLast, hrecLen, hpre]; omega
      rw [hdoms_eq, List.getElem?_append_right (by rw [hlenDL]; exact hkf), liftFields_getElem?,
        hlenDL, Nat.zero_add, List.getElem?_eq_getElem hjc] at hd
      simp only [Option.map_some', Option.some.injEq] at hd
      subst hd
      rw [List.getElem?_append_right hkf] at hx
      have hfs := cs.fsTyped (k - w.preMajor.length) x
        ((c.cell.adm.constructorViews cs.i).fields[k - w.preMajor.length]) hx
        (List.getElem?_eq_getElem hjc)
      rw [← lift_instantiateLevels]
      have htake : (w.preMajor ++ w.fields).take k =
          recP w ++ w.preMajor.drop w.nparams ++ w.fields.take (k - w.preMajor.length) := by
        conv => lhs; rw [show k = w.preMajor.length + (k - w.preMajor.length) by omega]
        rw [take_append_add, ← hsplit]
      have hlm := instPrefix_lift_mid (recP w) (w.preMajor.drop w.nparams)
        (w.fields.take (k - w.preMajor.length))
        (instantiateLevels w.ls ((c.cell.adm.constructorViews cs.i).fields[k - w.preMajor.length]))
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), hmidlen] at hlm
      rw [htake, hlm]
      exact hfs
  have hrhs := hasTyT_instPrefix_of_envWfT hW (ΔT := (doms.map (instantiateLevels w.ls)).reverse)
    (args := w.preMajor ++ w.fields)
    (by rw [List.length_reverse, List.length_map, hdomslen, List.length_append])
    hEq2 (by
      rw [show (doms.map (instantiateLevels w.ls)).reverse =
          ((doms.map (instantiateLevels w.ls)).take (w.preMajor ++ w.fields).length).reverse by
        rw [List.take_of_length_le (by rw [List.length_map, hdomslen, List.length_append]; exact Nat.le_refl _)]]
      exact argsAt_pkgA (by rw [hdomslen, List.length_append]; exact Nat.le_refl _) σArgs)
  -- (5) the right-hand side's type, computed
  obtain ⟨M, hM⟩ : ∃ M, w.preMajor[w.nparams]? = some M :=
    ⟨_, List.getElem?_eq_getElem (by rw [hpre]; omega)⟩
  have hM' : (w.preMajor.drop w.nparams)[0]? = some M := by rw [List.getElem?_drop, Nat.add_zero]; exact hM
  have hctorRef : c.cell.adm.family.ref + 1 + cs.i.val = w.ctorRef := by
    rw [cs.hi, w.hctorIdx, hfam]
  have hR : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls (iotaEquationType c.cell.adm cs.i)) =
      foldApps M ((c.cell.adm.constructorViews cs.i).resultIndices.map
        (fun r => instPrefix (recP w ++ w.fields) (instantiateLevels w.ls r)) ++
        [foldApps (.const w.ctorRef (famL1 w)) (recP w ++ w.fields)]) := by
    rw [hsplit, iotaEquationType, hctorRef, instPrefix_eqTy (recP w) (w.preMajor.drop w.nparams) w.fields
      _ _ _ _ _ _ _ _ (by rw [hplen, hnp]) hmidlen hfl M hM']
    simp only [famL1, hfamM, policyFamilyLevels]
  rw [hR] at hrhs
  -- (6) the left-hand side's type, computed
  have hL : instPrefix (w.preMajor ++ [majorW w]) (instantiateLevels w.ls w.recBody) =
      foldApps M (recIdx w ++ [majorW w]) := by
    rw [hrecBody, hminors, ← hni]
    exact instPrefix_recBody w.preMajor (majorW w) w.nparams w.nMinors w.nindices hpre M hM w.ls
  rw [hL] at convL
  -- (7) the motive's type
  have hmot := preArgsP w.nparams M (policyMotiveType c.cell.adm.family c.cell.adm.policy) hM
    (by rw [hrecDoms, hnp]; exact policyRecDoms_getElem?_motive _ _ _)
  rw [instPrefix_motiveType] at hmot
  -- (8) the motive application
  have hIapp : instPrefix (w.preMajor.take w.nparams ++ recIdx w) (instantiateLevels w.ls
      (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
        (policyLocals (c.cell.adm.family.parameters.length + c.cell.adm.family.indices.length)))) =
      majorTyW w := by
    rw [instPrefix_Iapp _ _ _ _ (by have := w.hpre; rw [List.length_append, List.length_take, recIdx_length, hnp, hni]; omega)]
    simp only [majorTyW, famL1, recP, hfam, hfamM, policyFamilyLevels]
  have hidxlen : (recIdx w).length = c.cell.adm.family.indices.length := by rw [recIdx_length, hni]
  obtain ⟨hc⟩ := convT_foldApps_args' _ (recIdx w ++ [majorW w])
    ((c.cell.adm.constructorViews cs.i).resultIndices.map
        (fun r => instPrefix (recP w ++ w.fields) (instantiateLevels w.ls r)) ++
        [foldApps (.const w.ctorRef (famL1 w)) (recP w ++ w.fields)])
    (by simp only [List.length_append, List.length_cons, List.length_nil, instDomsK_length, List.length_map, hidxlen])
    (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, hq, recIdx_length])
    M M _ ⟨.refl _ _ _ hmot⟩ (by
      intro i x x' d hx hx' hd
      rw [instDomsK_getElem?, Nat.zero_add, List.getElem?_map] at hd
      by_cases hi : i < (recIdx w).length
      · -- an index
        rw [List.getElem?_append_left hi] at hx
        rw [List.getElem?_append_left (by rw [List.length_map, hq, ← recIdx_length]; exact hi), List.getElem?_map] at hx'
        rw [List.getElem?_append_left (by rw [← hidxlen]; exact hi)] at hd
        cases hr : (c.cell.adm.constructorViews cs.i).resultIndices[i]? with
        | none => rw [hr] at hx'; cases hx'
        | some r =>
            rw [hr] at hx'
            simp only [Option.map_some', Option.some.injEq] at hx'
            subst hx'
            cases hdi : c.cell.adm.family.indices[i]? with
            | none => rw [hdi] at hd; cases hd
            | some d0 =>
                rw [hdi] at hd
                simp only [Option.map_some', Option.some.injEq] at hd
                subst hd
                rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
                have hpa := instPrefix_append_instTelK ((recIdx w).take i)
                  (List.take w.nparams w.preMajor) (instantiateLevels w.ls d0)
                rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hpa
                rw [← hpa]
                exact cs.idxConv i x r d0 hx hr hdi
      · -- the major
        have hieq : i = (recIdx w).length := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp only [List.length_append, List.length_cons, List.length_nil] at this; omega
        subst hieq
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rw [List.getElem?_append_right (by rw [List.length_map, hq, ← recIdx_length]; exact Nat.le_refl _),
          List.length_map, hq, ← recIdx_length, Nat.sub_self] at hx'
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx'
        subst hx'
        rw [List.getElem?_append_right (by rw [← hidxlen]; exact Nat.le_refl _), hidxlen, Nat.sub_self] at hd
        simp only [List.getElem?_cons_zero, Option.map_some', Option.some.injEq] at hd
        subst hd
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        have hpa := instPrefix_append_instTelK (recIdx w) (List.take w.nparams w.preMajor)
          (instantiateLevels w.ls (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
            (policyLocals (c.cell.adm.family.parameters.length + c.cell.adm.family.indices.length))))
        rw [hidxlen] at hpa
        rw [← hpa, hIapp]
        exact ⟨cs.majorConv⟩)
  rw [instPrefix_sort] at hc
  exact ⟨hasTyT_of_tyConv (hasTyT_of_tyConv hrhs (TyConvT.symmT (.of _ _ _ _ hc))) convL⟩

/-- **the `InScope` corollary**: `iotaPreserveTT`'s signature with `CorrCertsBelow` DROPPED —
    the bridge's scope supplies the rows (`typedRowsWf_of_envWfT_semPrefix`), nothing else is
    needed. -/
theorem iotaPreserveTT_noCert {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW (Ann.typedRowsWf_of_envWfT_semPrefix hW hP n) hΓ hd hlhs

/-- the union-evidence cover at `InScope`: the legacy arm rides `iotaPreserveT`, the typed-root
    arm the certificate-free theorem. -/
theorem iotaPreserveU_noCert {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  match hd with
  | .ofU w => iotaPreserveT hW hP hΓ (.of w) hlhs
  | .ofUS w => iotaPreserveTT_noCert hW hP hΓ (.of w) hlhs

end Rcic.Declarative

#print axioms Rcic.Declarative.iotaPreserveT_rows
#print axioms Rcic.Declarative.iotaPreserveTT_noCert
#print axioms Rcic.Declarative.iotaPreserveU_noCert
