import rcic.RcicIota

namespace Rcic.Declarative

theorem exprClosedAt_instantiateLevels (ls : List Level) :
    ∀ c e, exprClosedAt c (instantiateLevels ls e) = exprClosedAt c e := by
  intro c e
  induction e generalizing c with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f a ihf iha =>
      simp only [instantiateLevels, exprClosedAt, ihf c, iha c]
  | lam A B ihA ihB =>
      simp only [instantiateLevels, exprClosedAt, ihA c, ihB (c + 1)]
  | pi A B ihA ihB =>
      simp only [instantiateLevels, exprClosedAt, ihA c, ihB (c + 1)]
  | letE A v B ihA ihv ihB =>
      simp only [instantiateLevels, exprClosedAt, ihA c, ihv c, ihB (c + 1)]

theorem instantiate_eq_of_exprClosedAt_le {c j : Nat} {e : Expr Nat}
    (h : exprClosedAt c e = true) (hcj : c ≤ j) (v : Expr Nat) :
    instantiate j v e = e := by
  induction e generalizing c j v with
  | bvar i =>
      simp only [exprClosedAt] at h
      have hi : i < c := of_decide_eq_true h
      simp only [instantiate]
      rw [if_neg (by omega), if_neg (by omega)]
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f a ihf iha =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [instantiate, ihf h.1 hcj v, iha h.2 hcj v]
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [instantiate, ihA h.1 hcj v,
        ihB h.2 (Nat.succ_le_succ hcj) (lift 0 1 v)]
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [instantiate, ihA h.1 hcj v,
        ihB h.2 (Nat.succ_le_succ hcj) (lift 0 1 v)]
  | letE A value B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      obtain ⟨⟨hA, hv⟩, hB⟩ := h
      simp only [instantiate, ihA hA hcj v, ihv hv hcj v,
        ihB hB (Nat.succ_le_succ hcj) (lift 0 1 v)]

private theorem instPrefix_map_lift_core (args : List (Expr Nat))
    (c : Nat) (e : Expr Nat) :
    instPrefix (args.map (lift c 1)) (lift (args.length + c) 1 e) =
      lift c 1 (instPrefix args e) := by
  induction args generalizing c e with
  | nil =>
      simp only [List.map_nil, List.length_nil, Nat.zero_add, instPrefix]
  | cons a as ih =>
      simp only [List.map_cons, List.length_map, instPrefix, List.length_cons]
      have hperm := lift_lift_permute as.length 1 c 0 (Nat.zero_le c) a
      have hstep :
          instantiate as.length (lift 0 as.length (lift c 1 a))
              (lift (as.length + 1 + c) 1 e) =
            lift (as.length + c) 1
              (instantiate as.length (lift 0 as.length a) e) := by
        rw [lift_instantiate_low 1 (as.length + c) as.length
          (lift 0 as.length a) (by omega) e]
        rw [← hperm]
        congr 2 <;> omega
      rw [hstep, ih]

theorem instPrefix_map_lift_of_closed (args : List (Expr Nat))
    (c : Nat) (e : Expr Nat) (h : exprClosedAt args.length e = true) :
    instPrefix (args.map (lift c 1)) e = lift c 1 (instPrefix args e) := by
  have hfix : lift (args.length + c) 1 e = e :=
    lift_eq_of_exprClosedAt_le h (by omega)
  simpa only [hfix] using instPrefix_map_lift_core args c e

private theorem instPrefix_map_instantiate_core (args : List (Expr Nat))
    (j : Nat) (v e : Expr Nat) :
    instPrefix (args.map (instantiate j v))
        (instantiate (args.length + j) (lift 0 args.length v) e) =
      instantiate j v (instPrefix args e) := by
  induction args generalizing j v e with
  | nil =>
      simp only [List.map_nil, List.length_nil, Nat.zero_add, lift_zero, instPrefix]
  | cons a as ih =>
      simp only [List.map_cons, List.length_map, instPrefix, List.length_cons]
      have ha := lift_instantiate_high as.length 0 j v (Nat.zero_le j) a
      have hv := lift_lift_merge 1 as.length 0 as.length
        (Nat.zero_le as.length) (Nat.le_refl as.length) v
      have hcomm := instantiate_instantiate as.length (as.length + j)
        (lift 0 as.length a) (lift 0 as.length v) (by omega) e
      have hstep :
          instantiate as.length (lift 0 as.length (instantiate j v a))
              (instantiate (as.length + 1 + j)
                (lift 0 (as.length + 1) v) e) =
            instantiate (as.length + j) (lift 0 as.length v)
              (instantiate as.length (lift 0 as.length a) e) := by
        rw [ha]
        rw [hv] at hcomm
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomm.symm
      rw [hstep, ih]

theorem instPrefix_map_instantiate_of_closed (args : List (Expr Nat))
    (j : Nat) (v e : Expr Nat) (h : exprClosedAt args.length e = true) :
    instPrefix (args.map (instantiate j v)) e =
      instantiate j v (instPrefix args e) := by
  have hfix : instantiate (args.length + j) (lift 0 args.length v) e = e :=
    instantiate_eq_of_exprClosedAt_le h (by omega) (lift 0 args.length v)
  simpa only [hfix] using instPrefix_map_instantiate_core args j v e

/-- `instantiateLevels` commutes with `instPrefix` UNCONDITIONALLY: it never
    reads or writes a `bvar` (`lift_instantiateLevels`,
    `instantiateLevels_instantiate`), so no `exprClosedAt` side condition —
    unlike the `lift` / `instantiate` siblings above. Moved here from
    `RcicIotaShapeAdapter` (it belongs with its transport family; the
    fully-qualified name is unchanged). -/
theorem instPrefix_instLs (lvls : List Level) (xs : List (Expr Nat)) (e : Expr Nat) :
    instantiateLevels lvls (instPrefix xs e) =
      instPrefix (xs.map (instantiateLevels lvls)) (instantiateLevels lvls e) := by
  induction xs generalizing e with
  | nil => simp [instPrefix]
  | cons a as ih =>
      simp only [instPrefix_cons, List.map_cons, List.length_map, ih]
      rw [instantiateLevels_instantiate, lift_instantiateLevels]

def liftWitnessS (c : Nat) {E : ResolvedEnv} (w : IotaWitnessS E) :
    IotaWitnessS E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (lift c 1)
  fields := w.fields.map (lift c 1)
  ctorParams := w.ctorParams.map (lift c 1)
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by simpa only [List.length_map] using w.hctorParams
  hnpar := by simpa only [List.length_map] using w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by simpa only [List.length_map] using w.hpre
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by simpa only [List.length_map] using w.hpeel
  hfamApp := w.hfamApp
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  fuel := w.fuel
  shapes := w.shapes
  hshapes := w.hshapes
  schema := w.schema
  hschema := by simpa only [List.length_map] using w.hschema
  hstable := by
    intro E' hext
    simpa only [List.length_map] using w.hstable E' hext
  hschemaScope := by simpa only [List.length_map] using w.hschemaScope

def instWitnessS (j : Nat) (v : Expr Nat) {E : ResolvedEnv}
    (w : IotaWitnessS E) : IotaWitnessS E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (instantiate j v)
  fields := w.fields.map (instantiate j v)
  ctorParams := w.ctorParams.map (instantiate j v)
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by simpa only [List.length_map] using w.hctorParams
  hnpar := by simpa only [List.length_map] using w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by simpa only [List.length_map] using w.hpre
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by simpa only [List.length_map] using w.hpeel
  hfamApp := w.hfamApp
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  fuel := w.fuel
  shapes := w.shapes
  hshapes := w.hshapes
  schema := w.schema
  hschema := by simpa only [List.length_map] using w.hschema
  hstable := by
    intro E' hext
    simpa only [List.length_map] using w.hstable E' hext
  hschemaScope := by simpa only [List.length_map] using w.hschemaScope

def extWitnessS {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitnessS E) : IotaWitnessS E' where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := hext w.recRef w.recMember w.hrec
  hctor := hext w.ctorRef w.ctorMember w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor
  fields := w.fields
  ctorParams := w.ctorParams
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := hext w.familyRef w.famMember w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := w.hctorParams
  hnpar := w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := w.hpre
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := w.hpeel
  hfamApp := w.hfamApp
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  fuel := w.fuel
  shapes := w.shapes
  hshapes := (w.hstable E' hext).1
  schema := w.schema
  hschema := (w.hstable E' hext).2
  hstable := by
    intro E'' hext'
    exact w.hstable E'' (fun r m h => hext' r m (hext r m h))
  hschemaScope := w.hschemaScope

theorem iotaLhsOfS_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitnessS E) :
    iotaLhsOfS (liftWitnessS c w) = lift c 1 (iotaLhsOfS w) := by
  simp only [iotaLhsOfS, liftWitnessS, recCall_lift, foldApps_lift, lift,
    List.map_append]

theorem iotaRhsOfS_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitnessS E) :
    iotaRhsOfS (liftWitnessS c w) = lift c 1 (iotaRhsOfS w) := by
  have hscope : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels]
    simpa only [List.length_append, w.hpre] using w.hschemaScope
  simpa only [iotaRhsOfS, liftWitnessS, List.map_append] using
    instPrefix_map_lift_of_closed (w.preMajor ++ w.fields) c
      (instantiateLevels w.ls w.schema) hscope

def iotaLiftT {E : ResolvedEnv} :
    ∀ lhs rhs, DerivedIotaT E lhs rhs → ∀ c,
      DerivedIotaT E (lift c 1 lhs) (lift c 1 rhs) := by
  intro lhs rhs h c
  cases h with
  | of w =>
      rw [← iotaLhsOfS_lift c w, ← iotaRhsOfS_lift c w]
      exact .of (liftWitnessS c w)

theorem iotaLhsOfS_instantiate {E : ResolvedEnv} (j : Nat) (v : Expr Nat)
    (w : IotaWitnessS E) :
    iotaLhsOfS (instWitnessS j v w) = instantiate j v (iotaLhsOfS w) := by
  simp only [iotaLhsOfS, instWitnessS, recCall_instantiate,
    foldApps_instantiate, instantiate, List.map_append]

theorem iotaRhsOfS_instantiate {E : ResolvedEnv} (j : Nat) (v : Expr Nat)
    (w : IotaWitnessS E) :
    iotaRhsOfS (instWitnessS j v w) = instantiate j v (iotaRhsOfS w) := by
  have hscope : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels]
    simpa only [List.length_append, w.hpre] using w.hschemaScope
  simpa only [iotaRhsOfS, instWitnessS, List.map_append] using
    instPrefix_map_instantiate_of_closed (w.preMajor ++ w.fields) j v
      (instantiateLevels w.ls w.schema) hscope

def iotaSubstT {E : ResolvedEnv} :
    ∀ lhs rhs, DerivedIotaT E lhs rhs → ∀ v c,
      DerivedIotaT E (instantiate c v lhs) (instantiate c v rhs) := by
  intro lhs rhs h v c
  cases h with
  | of w =>
      rw [← iotaLhsOfS_instantiate c v w, ← iotaRhsOfS_instantiate c v w]
      exact .of (instWitnessS c v w)

theorem iotaLhsOfS_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitnessS E) :
    iotaLhsOfS (extWitnessS hext w) = iotaLhsOfS w := rfl

theorem iotaRhsOfS_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitnessS E) :
    iotaRhsOfS (extWitnessS hext w) = iotaRhsOfS w := rfl

def derivedIotaTExt {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {lhs rhs : Expr Nat} :
    DerivedIotaT E lhs rhs → DerivedIotaT E' lhs rhs
  | .of w => by
      rw [← iotaLhsOfS_ext hext w, ← iotaRhsOfS_ext hext w]
      exact .of (extWitnessS hext w)

def derivedIotaT_unpack {E : ResolvedEnv} {lhs rhs : Expr Nat} :
    DerivedIotaT E lhs rhs →
    Σ' (w : IotaWitnessS E), (lhs = iotaLhsOfS w) ×' (rhs = iotaRhsOfS w)
  | .of w => ⟨w, rfl, rfl⟩

end Rcic.Declarative
