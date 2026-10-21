import rcic.RcicIotaShape
import rcic.RcicTypedEnv

/-!
# R-TypedLevels — level instantiation on the TYPED judgment

The T-side twin of `RcicAnnLevels`' sealed `hasTyA_instLevels` /
`convA_instLevels`: a derivation at universe arity `a` instantiated at a
level-bounded list `ls` of length `a` is a derivation at arity `n`.

    HasTyT E a Γ e A  →  HasTyT E n (instLvlsCtx ls Γ)
        (instantiateLevels ls e) (instantiateLevels ls A)

and the same for `ConvT`. Every rule is re-applied under instantiation;
the `const` / `delta` / `consts` rules compose the instantiations on the
member's level-bounded type and body (`EnvLevelsT`, via
`instantiateLevels_compose`); the `sorts` rule carries `=ₙ` through
`eqN_instLevel`; the `iota` rule — where the A-side consumed the oracle
commutation `IotaLevelsA` — is the NEW work. `ConvT.iota` carries the
LEGACY `DerivedIota` over `IotaWitness` (the §20.6 witness), so the
transport needs a witness map (`lvlsWitness`, the level-twin of
`RcicIota.instWitness`) and the lhs/rhs equations
(`iotaLhsOf_instLevels` / `iotaRhsOf_instLevels` /
`derivedIota_instLevels`); the shape-witness twin
(`lvlsWitnessS` / `iotaLhsOfS_instLevels` / `iotaRhsOfS_instLevels` /
`derivedIotaT_instLevels` for `DerivedIotaT`) is proved beside it for the
typed-ι consumers. The lhs needs nothing new; the rhs composes
`instantiateLevels ls ∘ instantiateLevels w.ls` on the stored data —
the S-witness's `schema`, and the legacy witness's `hctorAfter` view
`instantiateLevels w.ls ctorMember.mtype` — each level-bounded at
`w.ls.length = recMember.arity`; both bounds ride in `IotaLevelsT`.

## The env hypotheses

* `EnvLevelsT E` — members' `mtype`/`body` level-bounded at their arity.
  `EnvWfT` discharges it (`envWfT_levels` below): singleton members are
  arity-0 with `hlvl*` premises, group members carry `hlvlB`.
* `IotaLevelsT E` — the stored data the transports re-instantiate at the
  redex's universes, level-bounded at the recursor's arity
  `w.ls.length`: conjunct one is every shape witness's `schema` (its
  level content is `canonRecLevels recMember.arity` (bounded
  unconditionally) plus the constructor field telescope
  `ctorFieldTelRaw nparams ctorDoms ctorResult` that `hpeel` peels off
  `ctorMember.mtype` — bounded at `ctorMember.arity` under `EnvLevelsT`);
  conjunct two is every legacy witness's `ctorMember.mtype` (bounded at
  `ctorMember.arity` under `EnvLevelsT`). On group-built envs
  (`EnvWfT` → `groupArityCoherent` at admission) `ctorMember.arity =
  famMember.arity ≤ recMember.arity`, so both are bounded there;
  neither witness records arity coherence, so the bounds ride as a
  hypothesis here — the discharge obligation for `EnvWfT` envs is
  exactly `ctorMember.arity ≤ recMember.arity`.
-/

namespace Rcic.Declarative

/-! ## (1) the level algebra, T-side

The A-side proves these in `Rcic.Declarative.Ann` on the SAME `Level` /
`levelBounded` / `levelsBounded` / `instLevel` / `eqN` / `eqNList` carrier
— the level type is shared, so the proofs port verbatim. -/

theorem levelsBounded_getElem {n : Nat} :
    (ls : List Level) → levelsBounded n ls = true → (i : Nat) →
    (hi : i < ls.length) → levelBounded n ls[i] = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, h, 0, _ => boolAnd_left h
  | _ :: t, h, i + 1, hi =>
      levelsBounded_getElem t (boolAnd_right h) i (Nat.lt_of_succ_lt_succ hi)

theorem levelBounded_instLevel {n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) :
    (l : Level) → levelBounded ls.length l = true →
    levelBounded n (instLevel ls l) = true
  | .zero, _ => rfl
  | .succ l, h => by
      simp only [instLevel_succ]; exact levelBounded_instLevel hls l h
  | .max a b, h => by
      simp only [instLevel_max]
      show (levelBounded n (instLevel ls a) && levelBounded n (instLevel ls b)) = true
      rw [levelBounded_instLevel hls a (boolAnd_left h),
        levelBounded_instLevel hls b (boolAnd_right h)]
      rfl
  | .imax a b, h => by
      simp only [instLevel_imax]
      show (levelBounded n (instLevel ls a) && levelBounded n (instLevel ls b)) = true
      rw [levelBounded_instLevel hls a (boolAnd_left h),
        levelBounded_instLevel hls b (boolAnd_right h)]
      rfl
  | .param i, h => by
      have hi : i < ls.length := of_decide_eq_true h
      rw [instLevel_param, List.getElem?_eq_getElem hi]
      exact levelsBounded_getElem ls hls i hi

theorem levelsBounded_map_instLevel {n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) :
    (ns : List Level) → levelsBounded ls.length ns = true →
    levelsBounded n (ns.map (instLevel ls)) = true
  | [], _ => rfl
  | l :: t, h => by
      show (levelBounded n (instLevel ls l) && levelsBounded n (t.map (instLevel ls))) = true
      rw [levelBounded_instLevel hls l (boolAnd_left h),
        levelsBounded_map_instLevel hls t (boolAnd_right h)]
      rfl

theorem eqN_instLevel {l l' : Level} (h : eqN l l') (ls : List Level) :
    eqN (instLevel ls l) (instLevel ls l') := fun ρ => by
  rw [eval_instLevel, eval_instLevel]; exact h _

theorem eqNList_map_instLevel (ls : List Level) :
    (ns ns' : List Level) → eqNList ns ns' →
    eqNList (ns.map (instLevel ls)) (ns'.map (instLevel ls))
  | [], [], _ => trivial
  | _ :: _, [], h => h.elim
  | [], _ :: _, h => h.elim
  | _l :: t, _l' :: t', h =>
      ⟨eqN_instLevel h.1 ls, eqNList_map_instLevel ls t t' h.2⟩

/-- the literal expansion is level-free (`litZero`/`litSucc` carry `[]`). -/
theorem instantiateLevels_natExpand (ls : List Level) :
    (t : Nat) → instantiateLevels ls (natExpand t) = natExpand t
  | 0 => rfl
  | t + 1 => by
      simp only [natExpand, litSucc, instantiateLevels,
        instantiateLevels_natExpand ls t, List.map_nil]

/-! ## (2) contexts -/

def instLvlsDecl (ls : List Level) : LocalDecl → LocalDecl
  | .assumption a => .assumption (instantiateLevels ls a)
  | .letBinding a v => .letBinding (instantiateLevels ls a) (instantiateLevels ls v)

def instLvlsCtx (ls : List Level) (Γ : LCtx) : LCtx := Γ.map (instLvlsDecl ls)

theorem instLvlsCtx_cons (ls : List Level) (d : LocalDecl) (Γ : LCtx) :
    instLvlsCtx ls (d :: Γ) = instLvlsDecl ls d :: instLvlsCtx ls Γ := rfl

theorem lookupType_instLvlsCtx (ls : List Level) (Γ : LCtx) (i : Nat) :
    lookupType (instLvlsCtx ls Γ) i =
      (lookupType Γ i).map (instantiateLevels ls) := by
  unfold lookupType instLvlsCtx
  rw [List.get?_map]
  cases Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a =>
          simp only [Option.map, instLvlsDecl, lift_instantiateLevels]
      | letBinding a v =>
          simp only [Option.map, instLvlsDecl, lift_instantiateLevels]

theorem lookupValue_instLvlsCtx (ls : List Level) (Γ : LCtx) (i : Nat) :
    lookupValue (instLvlsCtx ls Γ) i =
      (lookupValue Γ i).map (instantiateLevels ls) := by
  unfold lookupValue instLvlsCtx
  rw [List.get?_map]
  cases Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp only [Option.map, instLvlsDecl]
      | letBinding a v =>
          simp only [Option.map, instLvlsDecl, lift_instantiateLevels]

/-! ## (3) the env hypotheses -/

/-- members' types and bodies are level-bounded by their arity — the
    T-side twin of `EnvLevelsA`. `EnvWfT` discharges it
    (`envWfT_levels`). -/
def EnvLevelsT (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m →
    exprLevelsBounded m.arity m.mtype = true ∧
    (∀ b, m.body = some b → exprLevelsBounded m.arity b = true)

/-- the ι side of the level-instantiation hypothesis, the T-side twin of
    `IotaLevelsA` ("the ι oracle commutes with level instantiation"). What
    the transports actually consume: (1) the shape witness's stored schema
    — `iotaOpenRhs`'s output at the canonical context — level-bounded at
    the recursor's arity `w.ls.length` (`hlsLen`); (2) the legacy
    witness's stored constructor type, read at `instantiateLevels w.ls` in
    `hctorAfter` — level-bounded at the same `w.ls.length`. See the file
    header for why these ride as a hypothesis and what discharges them. -/
def IotaLevelsT (E : ResolvedEnv) : Prop :=
  (∀ (w : IotaWitnessS E), exprLevelsBounded w.ls.length w.schema = true) ∧
  (∀ (w : IotaWitness E),
    exprLevelsBounded w.ls.length w.ctorMember.mtype = true)

/-! ## (4) the iota witness under level instantiation

`lvlsWitnessS` maps the redex's level vectors (`ls`, `lsC`) and its
term-side lists (`preMajor`, `fields`, `ctorParams`); everything pinned to
`E`-computed data — `ctorDoms` / `ctorResult` / `recDoms` / `recBody` /
`shapes` / `schema` — stays verbatim, exactly as `liftWitnessS` /
`instWitnessS` keep them. -/

def lvlsWitnessS (lvls : List Level) {E : ResolvedEnv}
    (w : IotaWitnessS E) : IotaWitnessS E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls.map (instLevel lvls)
  lsC := w.lsC.map (instLevel lvls)
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (instantiateLevels lvls)
  fields := w.fields.map (instantiateLevels lvls)
  ctorParams := w.ctorParams.map (instantiateLevels lvls)
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
  hlsLen := by simpa only [List.length_map] using w.hlsLen
  fuel := w.fuel
  shapes := w.shapes
  hshapes := w.hshapes
  schema := w.schema
  hschema := by simpa only [List.length_map] using w.hschema
  hstable := by
    intro E' hext
    simpa only [List.length_map] using w.hstable E' hext
  hschemaScope := by simpa only [List.length_map] using w.hschemaScope

theorem recCall_instLevels (lvls : List Level) (rec : Expr Nat)
    (preMajor : List (Expr Nat)) (major : Expr Nat) :
    instantiateLevels lvls (recCall rec preMajor major) =
      recCall (instantiateLevels lvls rec)
        (preMajor.map (instantiateLevels lvls))
        (instantiateLevels lvls major) := by
  simp only [recCall, foldApps_instantiateLevels, List.map_append,
    List.map_cons, List.map_nil]

theorem iotaLhsOfS_instLevels {E : ResolvedEnv} (lvls : List Level)
    (w : IotaWitnessS E) :
    iotaLhsOfS (lvlsWitnessS lvls w) = instantiateLevels lvls (iotaLhsOfS w) := by
  simp only [iotaLhsOfS, lvlsWitnessS, recCall_instLevels,
    foldApps_instantiateLevels, instantiateLevels, List.map_append]

/-- THE RHS EQUATION — the only place `IotaLevelsT` is consumed:
    `instPrefix` commutes unconditionally (`instPrefix_instLs`), then the
    two level substitutions compose on the schema's bound
    (`instantiateLevels_compose`). -/
theorem iotaRhsOfS_instLevels {E : ResolvedEnv} (hIL : IotaLevelsT E)
    (lvls : List Level) (w : IotaWitnessS E) :
    iotaRhsOfS (lvlsWitnessS lvls w) = instantiateLevels lvls (iotaRhsOfS w) := by
  simp only [iotaRhsOfS, lvlsWitnessS]
  rw [← List.map_append, instPrefix_instLs,
    instantiateLevels_compose lvls w.ls w.schema (hIL.1 w)]

/-- level-instantiation transport of the derived-ι relation: the T-side
    counterpart of the `IotaLevelsA` oracle commutation, proved, not
    hypothesized — at the schema-bound cost `IotaLevelsT`. -/
def derivedIotaT_instLevels {E : ResolvedEnv} (hIL : IotaLevelsT E)
    {lhs rhs : Expr Nat} (h : DerivedIotaT E lhs rhs) (lvls : List Level) :
    DerivedIotaT E (instantiateLevels lvls lhs) (instantiateLevels lvls rhs) := by
  cases h with
  | of w =>
      rw [← iotaLhsOfS_instLevels lvls w, ← iotaRhsOfS_instLevels hIL lvls w]
      exact .of (lvlsWitnessS lvls w)

/-! ## (4b) the LEGACY `IotaWitness` under level instantiation

`ConvT.iota`'s payload is `DerivedIota` over the §20.6 `IotaWitness` — the
level twin of `RcicIota.instWitness` (the `instantiate` map the raw side's
`iotaSubst` rides). `lvlsWitness` maps the level vectors (`ls`, `lsC`)
and the term-side lists (`preMajor`, `fields`, `ctorParams`, `minor`,
`ctorAfterParams`); everything pinned to `E`-computed declaration data —
`recMember`/`ctorMember`/`famMember`, `kinds`, `ctorDoms`, `ctorResult`,
`recDoms`, `recBody` — stays verbatim, exactly as `instWitness` keeps it.
The one proof field that reads stored data through the redex's universes
is `hctorAfter` (`applyTel` at `instantiateLevels w.ls ctorMember.mtype`);
moving the map across it needs `instantiateLevels_compose` at the bound
`hbound` — `IotaLevelsT`'s second conjunct supplies it where the map is
applied (`derivedIota_instLevels`). Unlike the `instantiate` twin, NO
`isPiTel`/`directRecConstHead`/`resultConstHead` guards are needed:
`instantiateLevels` preserves the head constructor at every node, so the
recognizer fields transport by the unconditional `*_instantiateLevels`
equalities of `RcicLevelCalc`. -/

def lvlsWitness (lvls : List Level) {E : ResolvedEnv}
    (w : IotaWitness E)
    (hbound : exprLevelsBounded w.ls.length w.ctorMember.mtype = true) :
    IotaWitness E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls.map (instLevel lvls)
  lsC := w.lsC.map (instLevel lvls)
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (instantiateLevels lvls)
  fields := w.fields.map (instantiateLevels lvls)
  ctorParams := w.ctorParams.map (instantiateLevels lvls)
  kinds := w.kinds
  minor := instantiateLevels lvls w.minor
  hlen := by simpa only [List.length_map] using w.hlen
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
  hminor := by rw [List.getElem?_map, w.hminor]; rfl
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by simpa only [List.length_map] using w.hpeel
  hfamApp := w.hfamApp
  hkinds := w.hkinds
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := by simpa only [List.length_map] using w.hlsLen
  ctorAfterParams := instantiateLevels lvls w.ctorAfterParams
  hctorAfter := by
    have htake : (w.preMajor.map (instantiateLevels lvls)).take w.nparams =
        (w.preMajor.take w.nparams).map (instantiateLevels lvls) :=
      (List.map_take (instantiateLevels lvls) w.preMajor w.nparams).symm
    rw [htake]
    have hcomp : instantiateLevels (w.ls.map (instLevel lvls))
        w.ctorMember.mtype =
        instantiateLevels lvls (instantiateLevels w.ls w.ctorMember.mtype) :=
      (instantiateLevels_compose lvls w.ls w.ctorMember.mtype hbound).symm
    rw [hcomp, applyTel_instantiateLevels, w.hctorAfter]; rfl
  hctorTel := by
    rw [isPiTel_instantiateLevels]; exact w.hctorTel
  hfamTel := by
    rw [directRecConstHead_instantiateLevels]; exact w.hfamTel
  hresTel := by
    rw [resultConstHead_instantiateLevels]; exact w.hresTel

theorem recPrefix_instLevels (lvls : List Level) (pre : List (Expr Nat))
    (nparams nMinors : Nat) :
    recPrefix (pre.map (instantiateLevels lvls)) nparams nMinors =
      (recPrefix pre nparams nMinors).map (instantiateLevels lvls) :=
  (List.map_take (instantiateLevels lvls) pre (nparams + 1 + nMinors)).symm

theorem recCallField_instLevels (lvls : List Level) (rec : Expr Nat)
    (pre : List (Expr Nat)) (nparams nMinors : Nat) (f A : Expr Nat) :
    instantiateLevels lvls (recCallField rec pre nparams nMinors f A) =
      recCallField (instantiateLevels lvls rec)
        (pre.map (instantiateLevels lvls)) nparams nMinors
        (instantiateLevels lvls f) (instantiateLevels lvls A) := by
  simp only [recCallField, foldApps_instantiateLevels, List.map_append,
    List.map_cons, List.map_nil, recPrefix_instLevels,
    familyIdx_instantiateLevels]

theorem rhsArgs_instLevels (lvls : List Level) (nparams nMinors : Nat)
    (rec : Expr Nat) (preMajor : List (Expr Nat)) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (T : Expr Nat) →
    (rhsArgs rec preMajor nparams nMinors fs ks T).map
        (instantiateLevels lvls) =
      rhsArgs (instantiateLevels lvls rec)
        (preMajor.map (instantiateLevels lvls)) nparams nMinors
        (fs.map (instantiateLevels lvls)) ks (instantiateLevels lvls T)
  | [], _, _ => by simp only [rhsArgs, List.map_nil]
  | f :: fs, [], T => by
      simp only [rhsArgs, List.map_cons]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs [] T)
  | f :: fs, .plain :: ks, .pi _ B => by
      simp only [rhsArgs, List.map_cons]
      rw [← instantiateLevels_instantiate0,
        rhsArgs_instLevels lvls nparams nMinors rec preMajor fs ks
          (instantiate0 f B)]
  | f :: fs, .directRec :: ks, .pi A B => by
      simp only [rhsArgs, List.map_cons]
      rw [recCallField_instLevels, ← instantiateLevels_instantiate0,
        rhsArgs_instLevels lvls nparams nMinors rec preMajor fs ks
          (instantiate0 f B)]
  | _ :: fs, _ :: ks, .bvar _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .sort _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .const _ _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .app _ _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .lam _ _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .letE _ _ _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)
  | _ :: fs, _ :: ks, .lit _ => by
      simp only [rhsArgs, List.map_cons, instantiateLevels]
      exact congrArg _ (rhsArgs_instLevels lvls nparams nMinors rec
        preMajor fs ks _)

theorem ctorMajor_instLevels {E : ResolvedEnv} (lvls : List Level)
    (w : IotaWitness E)
    (hbound : exprLevelsBounded w.ls.length w.ctorMember.mtype = true) :
    ctorMajor (lvlsWitness lvls w hbound) =
      instantiateLevels lvls (ctorMajor w) := by
  change foldApps (.const w.ctorRef (w.lsC.map (instLevel lvls)))
      (w.ctorParams.map (instantiateLevels lvls) ++
        w.fields.map (instantiateLevels lvls)) =
    instantiateLevels lvls (foldApps (.const w.ctorRef w.lsC)
      (w.ctorParams ++ w.fields))
  rw [foldApps_instantiateLevels, List.map_append]
  rfl

theorem iotaLhsOf_instLevels {E : ResolvedEnv} (lvls : List Level)
    (w : IotaWitness E)
    (hbound : exprLevelsBounded w.ls.length w.ctorMember.mtype = true) :
    iotaLhsOf (lvlsWitness lvls w hbound) =
      instantiateLevels lvls (iotaLhsOf w) := by
  unfold iotaLhsOf
  rw [recCall_instLevels, ctorMajor_instLevels]
  simp only [lvlsWitness, instantiateLevels]

theorem iotaRhsOf_instLevels {E : ResolvedEnv} (lvls : List Level)
    (w : IotaWitness E)
    (hbound : exprLevelsBounded w.ls.length w.ctorMember.mtype = true) :
    iotaRhsOf (lvlsWitness lvls w hbound) =
      instantiateLevels lvls (iotaRhsOf w) := by
  simp only [iotaRhsOf, lvlsWitness, foldApps_instantiateLevels]
  rw [rhsArgs_instLevels lvls w.nparams w.nMinors (.const w.recRef w.ls)
    w.preMajor w.fields w.kinds w.ctorAfterParams]
  rfl

/-- level-instantiation transport of the LEGACY derived-ι relation —
    what `ConvT.iota` actually carries. -/
def derivedIota_instLevels {E : ResolvedEnv} (hIL : IotaLevelsT E)
    {lhs rhs : Expr Nat} (h : DerivedIota E lhs rhs) (lvls : List Level) :
    DerivedIota E (instantiateLevels lvls lhs) (instantiateLevels lvls rhs) := by
  cases h with
  | of w =>
      rw [← iotaLhsOf_instLevels lvls w (hIL.2 w),
        ← iotaRhsOf_instLevels lvls w (hIL.2 w)]
      exact .of (lvlsWitness lvls w (hIL.2 w))

/-! ## (5) the judgments under level instantiation -/

section Inst
variable {E : ResolvedEnv}

theorem instLvlsCtx_lookupType {ls : List Level} {Γ : LCtx} {i : Nat}
    {A : Expr Nat} (h : lookupType Γ i = some A) :
    lookupType (instLvlsCtx ls Γ) i = some (instantiateLevels ls A) := by
  rw [lookupType_instLvlsCtx, h]; rfl

theorem instLvlsCtx_lookupValue {ls : List Level} {Γ : LCtx} {i : Nat}
    {v : Expr Nat} (h : lookupValue Γ i = some v) :
    lookupValue (instLvlsCtx ls Γ) i = some (instantiateLevels ls v) := by
  rw [lookupValue_instLvlsCtx, h]; rfl

/-- the member's type, instantiated twice, instantiated once. -/
theorem instLevels_mtype (hEL : EnvLevelsT E) {r : Nat} {m : CheckedMember}
    (hres : E.members r = some m) {ms : List Level}
    (hlen : ms.length = m.arity) (ls : List Level) :
    instantiateLevels ls (instantiateLevels ms m.mtype) =
      instantiateLevels (ms.map (instLevel ls)) m.mtype :=
  instantiateLevels_compose ls ms m.mtype (by rw [hlen]; exact (hEL r m hres).1)

theorem instLevels_mbody (hEL : EnvLevelsT E) {r : Nat} {m : CheckedMember}
    {b : Expr Nat} (hres : E.members r = some m) (hb : m.body = some b)
    {ms : List Level} (hlen : ms.length = m.arity) (ls : List Level) :
    instantiateLevels ls (instantiateLevels ms b) =
      instantiateLevels (ms.map (instLevel ls)) b :=
  instantiateLevels_compose ls ms b (by rw [hlen]; exact (hEL r m hres).2 b hb)

theorem length_map_arity {ms : List Level} {m : CheckedMember}
    (hlen : ms.length = m.arity) (f : Level → Level) :
    (ms.map f).length = m.arity := by
  rw [List.length_map]; exact hlen

theorem levelsBounded_inst {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    {ms : List Level} (hwf : levelsBounded a ms = true) :
    levelsBounded n (ms.map (instLevel ls)) = true :=
  levelsBounded_map_instLevel hls ms (by rw [hlen]; exact hwf)

mutual

/-- THE T-SIDE INSTANCE-TYPING TRANSPORT: a derivation at universe arity
    `a` instantiated at a bounded level list `ls` of length `a` is a
    derivation at arity `n`. -/
def hasTyT_instLevels (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E a Γ e A →
    HasTyT E n (instLvlsCtx ls Γ) (instantiateLevels ls e)
      (instantiateLevels ls A)
  | _, _, _, .sort Γ l => .sort (instLvlsCtx ls Γ) (instLevel ls l)
  | _, _, _, .bvar Γ i A h =>
      .bvar (instLvlsCtx ls Γ) i (instantiateLevels ls A)
        (instLvlsCtx_lookupType h)
  | _, _, _, .const Γ r ms m hres hlen' hwf => by
      show HasTyT E n (instLvlsCtx ls Γ) (.const r (ms.map (instLevel ls)))
        (instantiateLevels ls (instantiateLevels ms m.mtype))
      rw [instLevels_mtype hEL hres hlen' ls]
      exact .const _ r _ m hres (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf)
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi (instLvlsCtx ls Γ) (instantiateLevels ls A) (instLevel ls u)
        (instantiateLevels ls B) (instLevel ls v)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam (instLvlsCtx ls Γ) (instantiateLevels ls A) (instLevel ls u)
        (instantiateLevels ls body) (instantiateLevels ls B)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hbody)
  | _, _, _, .app Γ f a A B hf ha => by
      show HasTyT E n (instLvlsCtx ls Γ)
        (.app (instantiateLevels ls f) (instantiateLevels ls a))
        (instantiateLevels ls (instantiate0 a B))
      rw [instantiateLevels_instantiate0]
      exact .app _ _ _ _ _
        (hasTyT_instLevels hEL hIL hls hlen hf)
        (hasTyT_instLevels hEL hIL hls hlen ha)
  | _, _, _, .letE Γ A u value B body hA hv hb => by
      show HasTyT E n (instLvlsCtx ls Γ)
        (.letE (instantiateLevels ls A) (instantiateLevels ls value)
          (instantiateLevels ls body))
        (instantiateLevels ls (instantiate0 value B))
      rw [instantiateLevels_instantiate0]
      exact .letE _ _ (instLevel ls u) _ _ _
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hv)
        (hasTyT_instLevels hEL hIL hls hlen hb)
  | _, _, _, .lit Γ t T hexp => by
      have h' := hasTyT_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevels_natExpand] at h'
      exact .lit _ t _ h'
  | _, _, _, .conv Γ e A B u h hc =>
      .conv (instLvlsCtx ls Γ) _ _ _ (instLevel ls u)
        (hasTyT_instLevels hEL hIL hls hlen h)
        (convT_instLevels hEL hIL hls hlen hc)
termination_by _ _ _ h => sizeOf h
decreasing_by all_goals (simp; omega)

/-- conversion at a fixed type under level instantiation. -/
def convT_instLevels (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtx} → {x y A : Expr Nat} → ConvT E a Γ x y A →
    ConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls x)
      (instantiateLevels ls y) (instantiateLevels ls A)
  | _, _, _, _, .refl Γ x A h =>
      .refl _ _ _ (hasTyT_instLevels hEL hIL hls hlen h)
  | _, _, _, _, .symm Γ x y A h =>
      .symm _ _ _ _ (convT_instLevels hEL hIL hls hlen h)
  | _, _, _, _, .trans Γ x y z A h1 h2 =>
      .trans _ _ (instantiateLevels ls y) _ _
        (convT_instLevels hEL hIL hls hlen h1)
        (convT_instLevels hEL hIL hls hlen h2)
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.app (.lam (instantiateLevels ls A) (instantiateLevels ls body))
          (instantiateLevels ls arg))
        (instantiateLevels ls (instantiate0 arg body))
        (instantiateLevels ls (instantiate0 arg B))
      rw [instantiateLevels_instantiate0, instantiateLevels_instantiate0]
      exact .beta _ _ _ _ _ (instLevel ls u)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hbody)
        (hasTyT_instLevels hEL hIL hls hlen harg)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.letE (instantiateLevels ls A) (instantiateLevels ls value)
          (instantiateLevels ls body))
        (instantiateLevels ls (instantiate0 value body))
        (instantiateLevels ls (instantiate0 value B))
      rw [instantiateLevels_instantiate0, instantiateLevels_instantiate0]
      exact .zeta _ _ _ _ _ (instLevel ls u)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hv)
        (hasTyT_instLevels hEL hIL hls hlen hb)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal _ i _ _ (instLvlsCtx_lookupValue hval)
        (instLvlsCtx_lookupType hty)
        (hasTyT_instLevels hEL hIL hls hlen hv)
  | _, _, _, _, .delta Γ r ms m b hres hbody htr hlen' hwf hb => by
      have hb' := hasTyT_instLevels hEL hIL hls hlen hb
      rw [instLevels_mtype hEL hres hlen' ls,
        instLevels_mbody hEL hres hbody hlen' ls] at hb'
      show ConvT E n (instLvlsCtx ls Γ) (.const r (ms.map (instLevel ls)))
        (instantiateLevels ls (instantiateLevels ms b))
        (instantiateLevels ls (instantiateLevels ms m.mtype))
      rw [instLevels_mtype hEL hres hlen' ls,
        instLevels_mbody hEL hres hbody hlen' ls]
      exact .delta _ r _ m b hres hbody htr (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf) hb'
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota _ _ _ _ (derivedIota_instLevels hIL h ls)
        (hasTyT_instLevels hEL hIL hls hlen hlhs)
        (hasTyT_instLevels hEL hIL hls hlen hrhs)
  | _, _, _, _, .lit Γ t _ T (.of _) hexp => by
      have h' := hasTyT_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevels_natExpand] at h'
      show ConvT E n (instLvlsCtx ls Γ) (.lit t)
        (instantiateLevels ls (natExpand t)) (instantiateLevels ls T)
      rw [instantiateLevels_natExpand]
      exact .lit _ t _ _ (.of t) h'
  | _, _, _, _, .app Γ f g x y A B h1 h2 => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.app (instantiateLevels ls f) (instantiateLevels ls x))
        (.app (instantiateLevels ls g) (instantiateLevels ls y))
        (instantiateLevels ls (instantiate0 x B))
      rw [instantiateLevels_instantiate0]
      exact .app _ _ _ _ _ _ _
        (convT_instLevels hEL hIL hls hlen h1)
        (convT_instLevels hEL hIL hls hlen h2)
  | _, _, _, _, .lam Γ A A' b b' B u hA hb =>
      .lam _ _ _ _ _ (instantiateLevels ls B) (instLevel ls u)
        (convT_instLevels hEL hIL hls hlen hA)
        (convT_instLevels hEL hIL hls hlen hb)
  | _, _, _, _, .pi Γ A A' B B' u v hA hB =>
      .pi _ _ _ _ _ (instLevel ls u) (instLevel ls v)
        (convT_instLevels hEL hIL hls hlen hA)
        (convT_instLevels hEL hIL hls hlen hB)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.letE (instantiateLevels ls A) (instantiateLevels ls v)
          (instantiateLevels ls b))
        (.letE (instantiateLevels ls A') (instantiateLevels ls v')
          (instantiateLevels ls b'))
        (instantiateLevels ls (instantiate0 v B))
      rw [instantiateLevels_instantiate0]
      exact .letE _ _ _ _ _ _ _ (instantiateLevels ls B) (instLevel ls u)
        (convT_instLevels hEL hIL hls hlen hA)
        (convT_instLevels hEL hIL hls hlen hv)
        (convT_instLevels hEL hIL hls hlen hb)
  | _, _, _, _, .sorts Γ l₁ l₂ h =>
      .sorts _ (instLevel ls l₁) (instLevel ls l₂) (eqN_instLevel h ls)
  | _, _, _, _, .consts Γ r ms ms' m hres hlen' hwf hwf' h => by
      show ConvT E n (instLvlsCtx ls Γ) (.const r (ms.map (instLevel ls)))
        (.const r (ms'.map (instLevel ls)))
        (instantiateLevels ls (instantiateLevels ms m.mtype))
      rw [instLevels_mtype hEL hres hlen' ls]
      exact .consts _ r _ _ m hres (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf) (levelsBounded_inst hls hlen hwf')
        (eqNList_map_instLevel ls ms ms' h)
  | _, _, _, _, .eta Γ f A B h => by
      have h' := hasTyT_instLevels hEL hIL hls hlen h
      have h'' : instantiateLevels ls (.lam A (.app (lift 0 1 f) (.bvar 0))) =
          .lam (instantiateLevels ls A)
            (.app (lift 0 1 (instantiateLevels ls f)) (.bvar 0)) := by
        simp only [instantiateLevels, lift_instantiateLevels]
      rw [h'']
      exact .eta _ _ _ _ h'
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr _ _ _ _ (hasTyT_instLevels hEL hIL hls hlen hP)
        (hasTyT_instLevels hEL hIL hls hlen hp)
        (hasTyT_instLevels hEL hIL hls hlen hq)
  | _, _, _, _, .tyConv Γ x y A A' u h hA =>
      .tyConv _ _ _ _ _ (instLevel ls u)
        (convT_instLevels hEL hIL hls hlen h)
        (convT_instLevels hEL hIL hls hlen hA)
termination_by _ _ _ _ h => sizeOf h
decreasing_by all_goals (simp; try omega)

end

end Inst

/-! ## (6) `EnvWfT` discharges `EnvLevelsT`

Every `EnvWfT` member carries its level bound: singletons are arity-0
with `hlvl`/`hlvlv`/`hlvlp` premises; group members carry `hlvlB` and
`hnobody`. The fold over `GroupMembersT` reads each admitted node — the
T-side counterpart of `RcicAnnEnvWf`'s `envWfA_levels`. -/

theorem groupMembersT_levels {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') : EnvLevelsT E → EnvLevelsT E' := by
  induction hmem with
  | nil E => exact id
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro hbase
      exact ih (fun r'' m'' hm'' => by
        by_cases hrr : r'' = r
        · rw [hrr, members_extend_eq] at hm''
          cases hm''
          exact ⟨hlvlB, fun b hb => by rw [hnobody] at hb; cases hb⟩
        · rw [members_extend_ne E r m r'' hrr] at hm''
          exact hbase r'' m'' hm'')

/-- `EnvWfT` supplies `EnvLevelsT`: every member's `mtype`/`body`
    level-bounded at its arity. -/
def envWfT_levels : {E : ResolvedEnv} → EnvWfT E → EnvLevelsT E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiom E r A u hE hfresh hA hcl hlvl =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨hlvl, fun _ hb => Option.noConfusion hb⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_levels hE r' m' hm'
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlv⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_levels hE r' m' hm'
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlp⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_levels hE r' m' hm'
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlv⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_levels hE r' m' hm'
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem =>
      groupMembersT_levels hmem (envWfT_levels hE)

/-! ## (7) `EnvWfT` discharges `IotaLevelsT`

The discharge obligation named in §(3)'s header: on a `group`-built
environment the arity coherence check `groupArityCoherent` — carried by
`GroupMembersT.cons`'s `harities` premise — pins a constructor member's
universe arity to its family's `nU` and a recursor member's to `nU` or
`nU + 1`. At an `IotaWitness`/`IotaWitnessS` the member's own `mtype`
computes `memberFamRef` to the witness's `familyRef`
(`piResult_of_peelPis`/`piLastDom_of_peelPis` + `spineHeadRef` lemmas),
so `ctorMember.arity = famMember.arity ≤ recMember.arity`. The route is
the T-side counterpart of `RcicEnv`'s `envWf_decl_checks` /
`envWf_group_arity` / `witness_ctorArity` segment — here through
`envWfT_declArities`.

With the arity window, BOTH conjuncts close:

* `∀ w : IotaWitness E, exprLevelsBounded w.ls.length w.ctorMember.mtype`
  — `EnvLevelsT` bounds `mtype` at `ctorMember.arity`; monotone up to
  `recMember.arity = w.ls.length`.
* `∀ w : IotaWitnessS E, exprLevelsBounded w.ls.length w.schema` — the
  schema is `iotaOpenRhs`'s output at the CANONICAL context, and every
  node it can emit is level-free or drawn from a bounded source: the
  recursor head carries `canonRecLevels recMember.arity` (bounded at
  that arity by `levelsBounded_canonRecLevels`), the `preMajor`/`field`
  argument lists are all `.bvar`s, the walked telescope is the lifted
  `ctorFieldTelRaw` of the peeled constructor type (bounded at
  `ctorMember.arity`, monotone up), and `whnfFuel`'s δ-unfolds read
  `transparentBody`, whose stored bodies of an `EnvWfT` env are
  level-free (`envWfT_body_lvl0`). The boundedness is propagated
  structurally: `whnfFuel_bounded` → `piTelescopeFuel_bounded` →
  `funRecArg_bounded` → `iotaArgs_bounded` → `iotaOpenRhs_bounded`. -/

/-- `levelBounded`/`levelsBounded`/`exprLevelsBounded` are antitone in
    the bound: widening the allowed parameter indices preserves
    boundedness. -/
theorem levelBounded_mono {a b : Nat} (hab : a ≤ b) :
    (l : Level) → levelBounded a l = true → levelBounded b l = true
  | .zero, _ => rfl
  | .succ l, h => levelBounded_mono hab l h
  | .max x y, h =>
      Bool.and_eq_true _ _ ▸
        ⟨levelBounded_mono hab x (boolAnd_left h),
          levelBounded_mono hab y (boolAnd_right h)⟩
  | .imax x y, h =>
      Bool.and_eq_true _ _ ▸
        ⟨levelBounded_mono hab x (boolAnd_left h),
          levelBounded_mono hab y (boolAnd_right h)⟩
  | .param i, h => by
      show decide (i < b) = true
      exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hab)

theorem levelsBounded_mono {a b : Nat} (hab : a ≤ b) :
    (ls : List Level) → levelsBounded a ls = true →
      levelsBounded b ls = true
  | [], _ => rfl
  | l :: t, h =>
      Bool.and_eq_true _ _ ▸
        ⟨levelBounded_mono hab l (boolAnd_left h),
          levelsBounded_mono hab t (boolAnd_right h)⟩

theorem exprLevelsBounded_mono {a b : Nat} (hab : a ≤ b) :
    (e : Expr Nat) → exprLevelsBounded a e = true →
      exprLevelsBounded b e = true
  | .bvar _, _ => rfl
  | .sort l, h => levelBounded_mono hab l h
  | .const _ ms, h => levelsBounded_mono hab ms h
  | .app f x, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_mono hab f (boolAnd_left h),
          exprLevelsBounded_mono hab x (boolAnd_right h)⟩
  | .lam A B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_mono hab A (boolAnd_left h),
          exprLevelsBounded_mono hab B (boolAnd_right h)⟩
  | .pi A B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_mono hab A (boolAnd_left h),
          exprLevelsBounded_mono hab B (boolAnd_right h)⟩
  | .letE A v B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨Bool.and_eq_true _ _ ▸
          ⟨exprLevelsBounded_mono hab A (boolAnd_left (boolAnd_left h)),
            exprLevelsBounded_mono hab v
              (boolAnd_right (boolAnd_left h))⟩,
          exprLevelsBounded_mono hab B (boolAnd_right h)⟩
  | .lit _, _ => rfl

/-- `lift` does not touch level parameters: boundedness is exactly
    preserved. -/
theorem exprLevelsBounded_lift (k c n : Nat) :
    (e : Expr Nat) →
      exprLevelsBounded k (lift c n e) = exprLevelsBounded k e
  | .bvar i => by
      simp only [lift]
      split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [lift, exprLevelsBounded, exprLevelsBounded_lift k c n f,
        exprLevelsBounded_lift k c n x]
  | .lam A B => by
      simp only [lift, exprLevelsBounded, exprLevelsBounded_lift k c n A,
        exprLevelsBounded_lift k (c + 1) n B]
  | .pi A B => by
      simp only [lift, exprLevelsBounded, exprLevelsBounded_lift k c n A,
        exprLevelsBounded_lift k (c + 1) n B]
  | .letE A v B => by
      simp only [lift, exprLevelsBounded, exprLevelsBounded_lift k c n A,
        exprLevelsBounded_lift k c n v,
        exprLevelsBounded_lift k (c + 1) n B]
  | .lit _ => rfl

/-- `instantiate` preserves boundedness when the replacement is bounded
    (under a binder the replacement is lifted, which is level-inert). -/
theorem exprLevelsBounded_instantiate {k : Nat} {v : Expr Nat}
    (hv : exprLevelsBounded k v = true) (j : Nat) :
    (e : Expr Nat) → exprLevelsBounded k e = true →
      exprLevelsBounded k (instantiate j v e) = true
  | .bvar i, _ => by
      simp only [instantiate]
      split
      · exact hv
      · split <;> rfl
  | .sort _, h => h
  | .const _ _, h => h
  | .lit _, h => h
  | .app f x, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_instantiate hv j f (boolAnd_left h),
          exprLevelsBounded_instantiate hv j x (boolAnd_right h)⟩
  | .lam A B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_instantiate hv j A (boolAnd_left h),
          exprLevelsBounded_instantiate
            (by rw [exprLevelsBounded_lift]; exact hv) (j + 1) B
            (boolAnd_right h)⟩
  | .pi A B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨exprLevelsBounded_instantiate hv j A (boolAnd_left h),
          exprLevelsBounded_instantiate
            (by rw [exprLevelsBounded_lift]; exact hv) (j + 1) B
            (boolAnd_right h)⟩
  | .letE A v' B, h =>
      Bool.and_eq_true _ _ ▸
        ⟨Bool.and_eq_true _ _ ▸
          ⟨exprLevelsBounded_instantiate hv j A
            (boolAnd_left (boolAnd_left h)),
            exprLevelsBounded_instantiate hv j v'
              (boolAnd_right (boolAnd_left h))⟩,
          exprLevelsBounded_instantiate
            (by rw [exprLevelsBounded_lift]; exact hv) (j + 1) B
            (boolAnd_right h)⟩

theorem exprLevelsBounded_instantiate0 {k : Nat} {v e : Expr Nat}
    (hv : exprLevelsBounded k v = true) (he : exprLevelsBounded k e = true) :
    exprLevelsBounded k (instantiate0 v e) = true :=
  exprLevelsBounded_instantiate hv 0 e he

/-- `foldApps` builds a bounded application spine from a bounded head and
    bounded arguments. -/
theorem exprLevelsBounded_foldApps {k : Nat} :
    (f : Expr Nat) → (xs : List (Expr Nat)) →
    exprLevelsBounded k f = true →
    (∀ x ∈ xs, exprLevelsBounded k x = true) →
      exprLevelsBounded k (foldApps f xs) = true
  | _, [], hf, _ => hf
  | f, x :: xs, hf, hxs =>
      exprLevelsBounded_foldApps (.app f x) xs
        (Bool.and_eq_true _ _ ▸ ⟨hf, hxs x (List.mem_cons_self x xs)⟩)
        (fun y hy => hxs y (List.mem_cons_of_mem x hy))

/-- The converse direction: a bounded spine has a bounded head and
    bounded arguments. -/
theorem appsSpine_bounded {k : Nat} :
    (e : Expr Nat) → exprLevelsBounded k e = true →
      exprLevelsBounded k (appsSpine e).1 = true ∧
        ∀ x ∈ (appsSpine e).2, exprLevelsBounded k x = true
  | .bvar _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .sort _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .const _ _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .lam _ _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .pi _ _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .letE _ _ _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .lit _, h => ⟨h, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | .app f x, h => by
      have ⟨hhead, hargs⟩ := appsSpine_bounded f (boolAnd_left h)
      show exprLevelsBounded k (appsSpine f).1 = true ∧
        ∀ y ∈ (appsSpine f).2 ++ [x], exprLevelsBounded k y = true
      exact ⟨hhead, fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact hargs y hy
        · rcases List.mem_singleton.mp hy with rfl
          exact boolAnd_right h⟩

/-- `peelPis` decomposes a bounded Π-telescope into bounded domains and
    a bounded result. -/
theorem peelPis_bounded {k : Nat} :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → exprLevelsBounded k T = true →
      (∀ d ∈ ds, exprLevelsBounded k d = true) ∧
        exprLevelsBounded k r = true
  | 0, _, _, _, h, hb => by
      simp only [peelPis] at h
      injection h with h'
      injection h' with hds hr
      subst hds
      subst hr
      exact ⟨fun _ hd => absurd hd (List.not_mem_nil _), hb⟩
  | _ + 1, .pi A B, _, _, h, hb => by
      simp only [peelPis] at h
      cases hp : peelPis _ B with
      | none => rw [hp] at h; exact Option.noConfusion h
      | some pr =>
          rw [hp] at h
          cases pr with
          | mk ds' r' =>
              injection h with hpair
              injection hpair with hds hr
              subst hds
              subst hr
              have ⟨hds2, hr2⟩ :=
                peelPis_bounded _ B hp (boolAnd_right hb)
              exact ⟨fun d hd => by
                rcases List.mem_cons.mp hd with rfl | hd
                · exact boolAnd_left hb
                · exact hds2 d hd, hr2⟩
  | _ + 1, .bvar _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .sort _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .const _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .app _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lam _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .letE _ _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lit _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h

/-- A `foldr .pi` telescope is bounded from bounded domains and a bounded
    result — the shape `ctorFieldTelRaw` builds. -/
theorem exprLevelsBounded_foldr_pi {k : Nat} {r : Expr Nat}
    (hr : exprLevelsBounded k r = true) :
    (ds : List (Expr Nat)) → (∀ d ∈ ds, exprLevelsBounded k d = true) →
      exprLevelsBounded k (ds.foldr Expr.pi r) = true
  | [], _ => hr
  | d :: ds, hd =>
      Bool.and_eq_true _ _ ▸
        ⟨hd d (List.mem_cons_self d ds),
          exprLevelsBounded_foldr_pi hr ds
            (fun d' hd' => hd d' (List.mem_cons_of_mem d hd'))⟩

theorem ctorFieldTelRaw_bounded {k nparams : Nat}
    {ctorDoms : List (Expr Nat)} {ctorResult : Expr Nat}
    (hds : ∀ d ∈ ctorDoms, exprLevelsBounded k d = true)
    (hr : exprLevelsBounded k ctorResult = true) :
    exprLevelsBounded k (ctorFieldTelRaw nparams ctorDoms ctorResult) = true :=
  exprLevelsBounded_foldr_pi hr (ctorDoms.drop nparams)
    (fun d hd => hds d (List.mem_of_mem_drop hd))

/-- `lamTelescope` is bounded from bounded domains and a bounded body. -/
theorem lamTelescope_bounded {k : Nat} {e : Expr Nat}
    (he : exprLevelsBounded k e = true) :
    (ds : List (Expr Nat)) → (∀ d ∈ ds, exprLevelsBounded k d = true) →
      exprLevelsBounded k (lamTelescope ds e) = true
  | [], _ => he
  | d :: ds, hd =>
      Bool.and_eq_true _ _ ▸
        ⟨hd d (List.mem_cons_self d ds),
          lamTelescope_bounded he ds
            (fun d' hd' => hd d' (List.mem_cons_of_mem d hd'))⟩

theorem levelsBounded_of_forall {k : Nat} :
    (ls : List Level) → (∀ l ∈ ls, levelBounded k l = true) →
      levelsBounded k ls = true
  | [], _ => rfl
  | l :: t, h =>
      Bool.and_eq_true _ _ ▸
        ⟨h l (List.mem_cons_self l t),
          levelsBounded_of_forall t
            (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))⟩

/-- The canonical universe vector `[param 0, …, param (a-1)]` is bounded
    at `a` unconditionally. -/
theorem levelsBounded_canonRecLevels (a : Nat) :
    levelsBounded a (canonRecLevels a) = true := by
  apply levelsBounded_of_forall
  intro l hl
  simp only [canonRecLevels, List.mem_map, List.mem_range] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact decide_eq_true hi

/-- Every argument the schema's `preMajor` produces is a bare bound
    variable — level-free unconditionally. -/
theorem preMajorBvars_bounded {k nparams nMinors nindices nfields : Nat} :
    ∀ x ∈ preMajorBvars nparams nMinors nindices nfields,
      exprLevelsBounded k x = true := by
  intro x hx
  simp only [preMajorBvars, List.mem_map, List.mem_reverse,
    List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rfl

theorem fieldBvars_bounded {k nfields : Nat} :
    ∀ x ∈ fieldBvars nfields, exprLevelsBounded k x = true := by
  intro x hx
  simp only [fieldBvars, List.mem_map, List.mem_reverse,
    List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rfl

/-! ### Stored bodies are level-free

`GroupMembersT` members carry `hnobody`; the four singletons hardwire
`arity := 0` with `hlvl*` premises. So every stored body of an `EnvWfT`
env is `exprLevelsBounded 0` — `transparentBody`'s δ-unfolds at `ls`
are the identity (`instantiateLevels_take` + `instantiateLevels_nil`). -/

theorem groupMembersT_body_lvl0 {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') :
    (∀ r m b, E.members r = some m → m.body = some b →
      exprLevelsBounded 0 b = true) →
    ∀ r m b, E'.members r = some m → m.body = some b →
      exprLevelsBounded 0 b = true := by
  induction hmem with
  | nil E => exact id
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro hbase
      exact ih (fun r'' m'' b hm'' hb => by
        by_cases hrr : r'' = r
        · rw [hrr, members_extend_eq] at hm''
          cases hm''
          rw [hnobody] at hb
          exact Option.noConfusion hb
        · rw [members_extend_ne E r m r'' hrr] at hm''
          exact hbase r'' m'' b hm'' hb)

/-- `EnvWfT` supplies level-free stored bodies. -/
def envWfT_body_lvl0 : {E : ResolvedEnv} → EnvWfT E →
    ∀ r m b, E.members r = some m → m.body = some b →
      exprLevelsBounded 0 b = true
  | _, .empty => fun _ _ _ h _ => Option.noConfusion h
  | _, .axiom E r A u hE hfresh hA hcl hlvl =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact Option.noConfusion hb
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_body_lvl0 hE r' m' b hm' hb
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          injection hb with hbv
          subst hbv
          exact hlvlv
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_body_lvl0 hE r' m' b hm' hb
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          injection hb with hbp
          subst hbp
          exact hlvlp
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_body_lvl0 hE r' m' b hm' hb
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          injection hb with hbv
          subst hbv
          exact hlvlv
        · rw [members_extend_ne E r _ r' hrr] at hm'
          exact envWfT_body_lvl0 hE r' m' b hm' hb
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem =>
      groupMembersT_body_lvl0 hmem (envWfT_body_lvl0 hE)

/-- `transparentBody`'s supply from `envWfT_body_lvl0`, at any ambient
    bound `k`. -/
theorem transparentBody_lvl0 {k : Nat} {E : ResolvedEnv}
    (hbody : ∀ r m b, E.members r = some m → m.body = some b →
      exprLevelsBounded 0 b = true) :
    ∀ {r : Nat} {ls : List Level} {e : Expr Nat},
      transparentBody E r ls = some e → exprLevelsBounded k e = true := by
  intro r ls e h
  unfold transparentBody at h
  split at h
  · rename_i m hm
    split at h
    · rename_i htr
      split at h
      · rename_i b hb
        injection h with h'
        subst h'
        have h0 := hbody _ _ _ hm hb
        rw [instantiateLevels_take 0 ls b h0, List.take_zero,
          instantiateLevels_nil]
        exact exprLevelsBounded_mono (Nat.zero_le k) b h0
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-! ### Boundedness through the schema's fuelled recognizers

`whnfFuel` is head-β, ζ, and transparent δ: each rewrite step builds a
`foldApps` of an `instantiate0` body or a `transparentBody` result over
the same spine, so boundedness of the output follows from boundedness of
the input plus the `transparentBody` supply. `piTelescopeFuel` peels
whnf-normal Πs; `funRecArg`/`iotaArgs`/`iotaOpenRhs` assemble their
outputs exclusively from bounded pieces. -/

theorem whnfFuel_bounded {k : Nat} {E : ResolvedEnv}
    (hsup : ∀ r ls b, transparentBody E r ls = some b →
      exprLevelsBounded k b = true) :
    (fuel : Nat) → {e e' : Expr Nat} → whnfFuel E fuel e = some e' →
      exprLevelsBounded k e = true → exprLevelsBounded k e' = true
  | 0, _, _, h, _ => Option.noConfusion h
  | fuel + 1, e, e', h, hb => by
      simp only [whnfFuel] at h
      split at h
      · rename_i A b a args hsp
        have ⟨hhead, hargs⟩ := appsSpine_bounded e hb
        rw [hsp] at hhead hargs
        apply whnfFuel_bounded hsup fuel h
        apply exprLevelsBounded_foldApps
        · exact exprLevelsBounded_instantiate0
            (hargs a (List.mem_cons_self a args)) (boolAnd_right hhead)
        · intro y hy
          exact hargs y (List.mem_cons_of_mem a hy)
      · rename_i A v b args hsp
        have ⟨hhead, hargs⟩ := appsSpine_bounded e hb
        rw [hsp] at hhead hargs
        apply whnfFuel_bounded hsup fuel h
        apply exprLevelsBounded_foldApps
        · exact exprLevelsBounded_instantiate0
            (boolAnd_right (boolAnd_left hhead))
            (boolAnd_right hhead)
        · exact hargs
      · rename_i r ls args hsp
        have ⟨hhead, hargs⟩ := appsSpine_bounded e hb
        rw [hsp] at hhead hargs
        split at h
        · rename_i body htb
          apply whnfFuel_bounded hsup fuel h
          apply exprLevelsBounded_foldApps
          · exact hsup r ls body htb
          · exact hargs
        · injection h with h'
          subst h'
          exact hb
      · injection h with h'
        subst h'
        exact hb

theorem piTelescopeFuel_bounded {k : Nat} {E : ResolvedEnv}
    (hsup : ∀ r ls b, transparentBody E r ls = some b →
      exprLevelsBounded k b = true) :
    (fuel : Nat) → (e : Expr Nat) → {ds : List (Expr Nat)} →
    {body : Expr Nat} →
    piTelescopeFuel E fuel e = some (ds, body) →
    exprLevelsBounded k e = true →
      (∀ d ∈ ds, exprLevelsBounded k d = true) ∧
        exprLevelsBounded k body = true
  | 0, _, _, _, h, _ => by
      simp only [piTelescopeFuel] at h; exact Option.noConfusion h
  | fuel + 1, e, ds, body, h, hb => by
      simp only [piTelescopeFuel] at h
      split at h
      · exact Option.noConfusion h
      · rename_i A B hw
        have hwb := whnfFuel_bounded hsup fuel hw hb
        split at h
        · exact Option.noConfusion h
        · rename_i ds' b' hpt
          have ⟨hds2, hb2⟩ :=
            piTelescopeFuel_bounded hsup fuel B hpt (boolAnd_right hwb)
          injection h with hpair
          injection hpair with hds hbdy
          subst hds
          subst hbdy
          exact ⟨fun d hd => by
            rcases List.mem_cons.mp hd with rfl | hd
            · exact boolAnd_left hwb
            · exact hds2 d hd, hb2⟩
      · rename_i w hw
        have hwb := whnfFuel_bounded hsup fuel hw hb
        injection h with hpair
        injection hpair with hds hbdy
        subst hds
        subst hbdy
        exact ⟨fun _ hd => absurd hd (List.not_mem_nil _), hwb⟩

theorem funRecArg_bounded {k : Nat} {E : ResolvedEnv} {fuel nparams nMinors
    inner : Nat} {rec : Expr Nat} {preMajor : List (Expr Nat)}
    {f A call : Expr Nat}
    (hsup : ∀ r ls b, transparentBody E r ls = some b →
      exprLevelsBounded k b = true)
    (hrec : exprLevelsBounded k rec = true)
    (hpre : ∀ x ∈ preMajor, exprLevelsBounded k x = true)
    (hf : exprLevelsBounded k f = true)
    (hA : exprLevelsBounded k A = true)
    (h : funRecArg E fuel rec preMajor nparams nMinors f A inner =
      some call) :
    exprLevelsBounded k call = true := by
  simp only [funRecArg] at h
  split at h
  · exact Option.noConfusion h
  · rename_i doms famApp hpt
    split at h
    · rename_i hlen
      injection h with hcall
      subst hcall
      obtain ⟨hds, hfam⟩ := piTelescopeFuel_bounded hsup fuel A hpt hA
      apply lamTelescope_bounded
      · apply exprLevelsBounded_foldApps _ _ hrec
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp only [recPrefix] at hy
            rw [exprLevelsBounded_lift]
            exact hpre y (List.mem_of_mem_take hy)
          · simp only [familyIdx] at hx
            obtain ⟨_, hargs⟩ := appsSpine_bounded famApp hfam
            exact hargs x (List.mem_of_mem_drop hx)
        · rcases List.mem_singleton.mp hx with rfl
          apply exprLevelsBounded_foldApps
          · rw [exprLevelsBounded_lift]; exact hf
          · intro y hy
            rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
            rfl
      · exact hds
    · exact Option.noConfusion h

theorem iotaArgs_bounded {k : Nat} {E : ResolvedEnv} {fuel nparams nMinors
    : Nat} {rec : Expr Nat} {preMajor : List (Expr Nat)}
    (hsup : ∀ r ls b, transparentBody E r ls = some b →
      exprLevelsBounded k b = true)
    (hrec : exprLevelsBounded k rec = true)
    (hpre : ∀ x ∈ preMajor, exprLevelsBounded k x = true) :
    (shapes : List FieldShape) → (fs : List (Expr Nat)) →
    (T : Expr Nat) → {args : List (Expr Nat)} →
    iotaArgs E fuel rec preMajor nparams nMinors shapes fs T =
      some args →
    (∀ f ∈ fs, exprLevelsBounded k f = true) →
    exprLevelsBounded k T = true →
    ∀ a ∈ args, exprLevelsBounded k a = true := by
  intro shapes
  induction shapes with
  | nil =>
      intro fs T args h _ _
      cases fs with
      | nil =>
          simp only [iotaArgs] at h
          injection h with h'
          subst h'
          exact fun _ ha => absurd ha (List.not_mem_nil _)
      | cons f fs =>
          simp only [iotaArgs] at h
          exact Option.noConfusion h
  | cons s ss ih =>
      intro fs T args h hfs hT
      cases fs with
      | nil =>
          cases s with
          | nonrecursive =>
              cases T <;> simp only [iotaArgs] at h <;>
                exact Option.noConfusion h
          | recursive inner =>
              cases inner <;> cases T <;> simp only [iotaArgs] at h <;>
                exact Option.noConfusion h
      | cons f fs =>
          have hfb := hfs f (List.mem_cons_self f fs)
          have hfs' : ∀ f' ∈ fs, exprLevelsBounded k f' = true :=
            fun f' hf' => hfs f' (List.mem_cons_of_mem f hf')
          cases s with
          | nonrecursive =>
              cases T with
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _
                  | letE _ _ _ | lit _ =>
                  simp only [iotaArgs] at h
                  exact Option.noConfusion h
              | pi A B =>
                  simp only [iotaArgs] at h
                  obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some.mp h
                  intro a ha
                  rcases List.mem_cons.mp ha with rfl | ha
                  · exact hfb
                  · exact ih fs (instantiate0 f B) hrest hfs'
                      (exprLevelsBounded_instantiate0 hfb
                        (boolAnd_right hT)) a ha
          | recursive inner =>
              cases inner with
              | zero =>
                  cases T with
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _
                      | letE _ _ _ | lit _ =>
                      simp only [iotaArgs] at h
                      exact Option.noConfusion h
                  | pi A B =>
                      simp only [iotaArgs] at h
                      cases hpt : piTelescopeFuel E fuel A with
                      | none => rw [hpt] at h; exact Option.noConfusion h
                      | some pr =>
                          rw [hpt] at h
                          cases pr with
                          | mk doms famApp =>
                              cases doms with
                              | nil =>
                                  obtain ⟨rest, hrest, rfl⟩ :=
                                    Option.map_eq_some.mp h
                                  have hfamB :=
                                    (piTelescopeFuel_bounded hsup fuel A hpt
                                      (boolAnd_left hT)).2
                                  intro a ha
                                  rcases List.mem_cons.mp ha with rfl | ha
                                  · exact hfb
                                  · rcases List.mem_cons.mp ha with rfl | ha
                                    · apply exprLevelsBounded_foldApps _ _
                                        hrec
                                      intro x hx
                                      rcases List.mem_append.mp hx with
                                        hx | hx
                                      · rcases List.mem_append.mp hx with
                                          hx | hx
                                        · simp only [recPrefix] at hx
                                          exact hpre x
                                            (List.mem_of_mem_take hx)
                                        · simp only [familyIdx] at hx
                                          obtain ⟨_, hargs⟩ :=
                                            appsSpine_bounded famApp hfamB
                                          exact hargs x
                                            (List.mem_of_mem_drop hx)
                                      · rcases List.mem_singleton.mp hx
                                          with rfl
                                        exact hfb
                                    · exact ih fs (instantiate0 f B) hrest
                                        hfs'
                                        (exprLevelsBounded_instantiate0 hfb
                                          (boolAnd_right hT)) a ha
                              | cons d ds => exact Option.noConfusion h
              | succ inner' =>
                  cases T with
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _
                      | letE _ _ _ | lit _ =>
                      simp only [iotaArgs] at h
                      exact Option.noConfusion h
                  | pi A B =>
                      simp only [iotaArgs] at h
                      cases hfra : funRecArg E fuel rec preMajor
                        nparams nMinors f A (inner' + 1) with
                      | none =>
                          rw [hfra] at h
                          exact Option.noConfusion h
                      | some call =>
                          rw [hfra] at h
                          obtain ⟨rest, hrest, rfl⟩ :=
                            Option.map_eq_some.mp h
                          have hcall :=
                            funRecArg_bounded hsup hrec hpre hfb
                              (boolAnd_left hT) hfra
                          intro a ha
                          rcases List.mem_cons.mp ha with rfl | ha
                          · exact hfb
                          · rcases List.mem_cons.mp ha with rfl | ha
                            · exact hcall
                            · exact ih fs (instantiate0 f B) hrest hfs'
                                (exprLevelsBounded_instantiate0 hfb
                                  (boolAnd_right hT)) a ha

theorem iotaOpenRhs_bounded {k : Nat} {E : ResolvedEnv} {fuel nparams
    nMinors : Nat} {rec minor : Expr Nat} {preMajor : List (Expr Nat)}
    {shapes : List FieldShape} {fs : List (Expr Nat)}
    {tel schema : Expr Nat}
    (hsup : ∀ r ls b, transparentBody E r ls = some b →
      exprLevelsBounded k b = true)
    (hrec : exprLevelsBounded k rec = true)
    (hminor : exprLevelsBounded k minor = true)
    (hpre : ∀ x ∈ preMajor, exprLevelsBounded k x = true)
    (hfs : ∀ f ∈ fs, exprLevelsBounded k f = true)
    (htel : exprLevelsBounded k tel = true)
    (h : iotaOpenRhs E fuel rec minor preMajor nparams nMinors shapes fs
      tel = some schema) :
    exprLevelsBounded k schema = true := by
  simp only [iotaOpenRhs] at h
  obtain ⟨args, hargs, rfl⟩ := Option.map_eq_some.mp h
  exact exprLevelsBounded_foldApps minor args hminor
    (iotaArgs_bounded hsup hrec hpre shapes fs tel hargs hfs htel)

/-! ### Arity coherence out of `EnvWfT`

`envWfT_declArities` is the T-side counterpart of `RcicEnv`'s
`envWf_decl_checks`, pared to the `groupArityCoherent` conjunct: each
member carries its check at the prefix it was admitted over (the four
singletons pass vacuously — `groupArityCoherent` is `true` off the three
group classes, so no class premise is needed here). -/

noncomputable def groupMembersT_declArities {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') :
    (∀ r m, E.members r = some m →
      Σ' (E0 : ResolvedEnv), groupArityCoherent E0 m = true ×'
        (∀ r' m', E0.members r' = some m' → E.members r' = some m')) →
    ∀ r m, E'.members r = some m →
      Σ' (E0 : ResolvedEnv), groupArityCoherent E0 m = true ×'
        (∀ r' m', E0.members r' = some m' → E'.members r' = some m') := by
  induction hmem with
  | nil E => exact id
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro hbase
      exact ih (fun r'' m'' hm'' => by
        by_cases hrr : r'' = r
        · rw [hrr, members_extend_eq] at hm''
          cases hm''
          exact ⟨E, harities, members_extend_preserved hfresh⟩
        · rw [members_extend_ne E r m r'' hrr] at hm''
          obtain ⟨E0, ha, hsub⟩ := hbase r'' m'' hm''
          exact ⟨E0, ha, fun r' m' h0 =>
            members_extend_preserved hfresh r' m' (hsub r' m' h0)⟩)

noncomputable def envWfT_declArities : {E : ResolvedEnv} → EnvWfT E →
    ∀ r m, E.members r = some m →
      Σ' (E0 : ResolvedEnv), groupArityCoherent E0 m = true ×'
        (∀ r' m', E0.members r' = some m' → E.members r' = some m')
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiom E r A u hE hfresh hA hcl hlvl =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨E, rfl, members_extend_preserved hfresh⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          obtain ⟨E0, ha, hsub⟩ := envWfT_declArities hE r' m' hm'
          exact ⟨E0, ha, fun r'' m'' h0 =>
            members_extend_preserved hfresh r'' m'' (hsub r'' m'' h0)⟩
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨E, rfl, members_extend_preserved hfresh⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          obtain ⟨E0, ha, hsub⟩ := envWfT_declArities hE r' m' hm'
          exact ⟨E0, ha, fun r'' m'' h0 =>
            members_extend_preserved hfresh r'' m'' (hsub r'' m'' h0)⟩
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨E, rfl, members_extend_preserved hfresh⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          obtain ⟨E0, ha, hsub⟩ := envWfT_declArities hE r' m' hm'
          exact ⟨E0, ha, fun r'' m'' h0 =>
            members_extend_preserved hfresh r'' m'' (hsub r'' m'' h0)⟩
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · rw [hrr, members_extend_eq] at hm'
          cases hm'
          exact ⟨E, rfl, members_extend_preserved hfresh⟩
        · rw [members_extend_ne E r _ r' hrr] at hm'
          obtain ⟨E0, ha, hsub⟩ := envWfT_declArities hE r' m' hm'
          exact ⟨E0, ha, fun r'' m'' h0 =>
            members_extend_preserved hfresh r'' m'' (hsub r'' m'' h0)⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem =>
      groupMembersT_declArities hmem (envWfT_declArities hE)

/-- `groupArityCoherent` at the FULL environment: the member's stored
    type declares family `f`, the admission-time check pinned that `f`
    was an inductive in the prefix with the 05 §3/§11 arity, and the
    prefix's inclusion into `E` identifies the family with the caller's.
    T-side counterpart of `envWf_group_arity`. -/
noncomputable def envWfT_group_arity {E : ResolvedEnv} (hW : EnvWfT E)
    {r f : Nat} {m fm : CheckedMember}
    (hm : E.members r = some m) (hf : memberFamRef m = some f)
    (hfam : E.members f = some fm) :
    ((m.mclass = .constructorM) → m.arity = fm.arity) ×'
    ((m.mclass = .recursorM) →
      m.arity = fm.arity ∨ m.arity = fm.arity + 1) := by
  obtain ⟨E0, ha, hext⟩ := envWfT_declArities hW r m hm
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
        exact ha'.2
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] at ha'
        exact ha'.2

/-- The S-witness twins of `memberFamRef_ctorMember` /
    `memberFamRef_recMember` (`RcicEnv`): the S witness's members declare
    its own `familyRef`, read off the same `hpeel`/`hfamApp` and
    `hpeelRec`/`hmajorTy` fields. -/
theorem memberFamRef_ctorMemberS {E : ResolvedEnv} (w : IotaWitnessS E) :
    memberFamRef w.ctorMember = some w.familyRef := by
  unfold memberFamRef
  rw [w.hctorK]
  have hpr : piResult w.ctorMember.mtype = w.ctorResult :=
    piResult_of_peelPis (w.nparams + w.fields.length) w.ctorMember.mtype
      w.hpeel w.hnpar
  rw [hpr]
  exact spineHeadRef_of_isFamilyApp w.hfamApp

theorem memberFamRef_recMemberS {E : ResolvedEnv} (w : IotaWitnessS E) :
    memberFamRef w.recMember = some w.familyRef := by
  have hbody0 : piCount w.recBody = 0 := by
    rw [w.hrecBody, foldApps_snoc]
    rfl
  have hld : piLastDom w.recMember.mtype =
      w.recDoms[w.nparams + 1 + w.nMinors + w.nindices]? :=
    piLastDom_of_peelPis (w.nparams + 1 + w.nMinors + w.nindices)
      w.recMember.mtype w.hpeelRec hbody0
  unfold memberFamRef
  rw [w.hrecK, hld, w.hmajorTy]
  exact spineHeadRef_foldApps_const _ _ _

/-- 05 §3 at a legacy `IotaWitness`, discharged from `EnvWfT`. -/
theorem envWfT_ctorArity {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) : w.ctorMember.arity = w.famMember.arity :=
  (envWfT_group_arity hW w.hctor (memberFamRef_ctorMember w)
    w.hfam).1 w.hctorK

/-- 05 §11 at a legacy `IotaWitness`, discharged from `EnvWfT`. -/
theorem envWfT_recArity {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) : w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 :=
  (envWfT_group_arity hW w.hrec (memberFamRef_recMember w)
    w.hfam).2 w.hrecK

/-- 05 §3 at an `IotaWitnessS`, discharged from `EnvWfT`. -/
theorem envWfT_ctorArityS {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) : w.ctorMember.arity = w.famMember.arity :=
  (envWfT_group_arity hW w.hctor (memberFamRef_ctorMemberS w)
    w.hfam).1 w.hctorK

/-- 05 §11 at an `IotaWitnessS`, discharged from `EnvWfT`. -/
theorem envWfT_recArityS {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) : w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 :=
  (envWfT_group_arity hW w.hrec (memberFamRef_recMemberS w)
    w.hfam).2 w.hrecK

/-- THE DISCHARGE: `EnvWfT` entails `IotaLevelsT`. The legacy conjunct is
    `hlvlB` monotone up the 05 §3/§11 arity window; the shape conjunct is
    the same window fed into `iotaOpenRhs_bounded` at the canonical
    context `hschema` computes. -/
theorem iotaLevelsT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    IotaLevelsT E :=
  ⟨fun w => by
      have hEL := envWfT_levels hW
      have hsup : ∀ r ls b, transparentBody E r ls = some b →
          exprLevelsBounded w.recMember.arity b = true :=
        fun _ _ _ htb =>
          transparentBody_lvl0 (envWfT_body_lvl0 hW) htb
      have hle : w.ctorMember.arity ≤ w.recMember.arity := by
        have hctorA := envWfT_ctorArityS hW w
        rcases envWfT_recArityS hW w with h | h <;> omega
      have hbmt : exprLevelsBounded w.recMember.arity
          w.ctorMember.mtype = true :=
        exprLevelsBounded_mono hle _
          (hEL w.ctorRef w.ctorMember w.hctor).1
      obtain ⟨hds, hres⟩ := peelPis_bounded _ _ w.hpeel hbmt
      have htel : exprLevelsBounded w.recMember.arity
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
        rw [exprLevelsBounded_lift]
        exact ctorFieldTelRaw_bounded hds hres
      have hrecB : exprLevelsBounded w.recMember.arity
          (.const w.recRef (canonRecLevels w.recMember.arity)) = true :=
        levelsBounded_canonRecLevels _
      have hminor : exprLevelsBounded w.recMember.arity
          (.bvar (w.fields.length + w.nindices +
            (w.nMinors - 1 - w.ctorIdx))) = true := rfl
      rw [w.hlsLen]
      exact iotaOpenRhs_bounded hsup hrecB hminor
        preMajorBvars_bounded fieldBvars_bounded htel w.hschema,
    fun w => by
      have hEL := envWfT_levels hW
      have hle : w.ctorMember.arity ≤ w.recMember.arity := by
        have hctorA := envWfT_ctorArity hW w
        rcases envWfT_recArity hW w with h | h <;> omega
      have hbmt : exprLevelsBounded w.recMember.arity
          w.ctorMember.mtype = true :=
        exprLevelsBounded_mono hle _
          (hEL w.ctorRef w.ctorMember w.hctor).1
      rw [w.hlsLen]
      exact hbmt⟩

/-- NON-VACUITY: `EnvWfT` is inhabited, and `iotaLevelsT_of_envWfT`
    produces an `IotaLevelsT` for it — one axiom member suffices to
    exercise the singleton readouts (`envWfT_levels`, `envWfT_body_lvl0`,
    `envWfT_declArities`) end-to-end. A group inhabitant (a real
    `IotaWitness`/`IotaWitnessS`) would additionally exercise the arity
    window; no `EnvWfT`-of-a-group fixture exists in the tree yet, so
    the vacuous side of this tooth is noted in the PR rather than
    discharged here. -/
example : IotaLevelsT
    (extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort (.succ .zero), none⟩) :=
  iotaLevelsT_of_envWfT
    (EnvWfT.axiom emptyEnv 0 (.sort (.succ .zero)) (.succ (.succ .zero))
      EnvWfT.empty rfl (HasTyT.sort [] (.succ .zero))
      (fun _ => rfl) rfl)

#print axioms levelsBounded_getElem
#print axioms levelBounded_instLevel
#print axioms levelsBounded_map_instLevel
#print axioms eqN_instLevel
#print axioms eqNList_map_instLevel
#print axioms instantiateLevels_natExpand
#print axioms lookupType_instLvlsCtx
#print axioms lookupValue_instLvlsCtx
#print axioms lvlsWitnessS
#print axioms recCall_instLevels
#print axioms iotaLhsOfS_instLevels
#print axioms iotaRhsOfS_instLevels
#print axioms derivedIotaT_instLevels
#print axioms lvlsWitness
#print axioms recPrefix_instLevels
#print axioms recCallField_instLevels
#print axioms rhsArgs_instLevels
#print axioms ctorMajor_instLevels
#print axioms iotaLhsOf_instLevels
#print axioms iotaRhsOf_instLevels
#print axioms derivedIota_instLevels
#print axioms instLevels_mtype
#print axioms instLevels_mbody
#print axioms levelsBounded_inst
#print axioms hasTyT_instLevels
#print axioms convT_instLevels
#print axioms groupMembersT_levels
#print axioms envWfT_levels
#print axioms levelBounded_mono
#print axioms levelsBounded_mono
#print axioms exprLevelsBounded_mono
#print axioms exprLevelsBounded_lift
#print axioms exprLevelsBounded_instantiate
#print axioms exprLevelsBounded_instantiate0
#print axioms exprLevelsBounded_foldApps
#print axioms appsSpine_bounded
#print axioms peelPis_bounded
#print axioms ctorFieldTelRaw_bounded
#print axioms lamTelescope_bounded
#print axioms levelsBounded_canonRecLevels
#print axioms groupMembersT_body_lvl0
#print axioms envWfT_body_lvl0
#print axioms transparentBody_lvl0
#print axioms whnfFuel_bounded
#print axioms piTelescopeFuel_bounded
#print axioms funRecArg_bounded
#print axioms iotaArgs_bounded
#print axioms iotaOpenRhs_bounded
#print axioms groupMembersT_declArities
#print axioms envWfT_declArities
#print axioms envWfT_group_arity
#print axioms memberFamRef_ctorMemberS
#print axioms memberFamRef_recMemberS
#print axioms envWfT_ctorArity
#print axioms envWfT_recArity
#print axioms envWfT_ctorArityS
#print axioms envWfT_recArityS
#print axioms iotaLevelsT_of_envWfT

end Rcic.Declarative
