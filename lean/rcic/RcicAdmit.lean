/-
RCIC 00 §20.7 ADMISSION BUNDLE — THE DECLARED Bool (segment 6, batch B1).

`recursorGroupAdmitted E r m` is the recursor-add decision: given the
PREFIX environment `E` (family and constructors present, `r` still
fresh), the recursor's own ref `r`, and its checked member `m`, it
decides — from `(E, r, m)` and NOTHING else — whether 05 §11–13's
recursor group is admissible at that ref. No instance argument appears
in it: the only environment read is `E.members`, which is
declaration-time state and not an instance datum, and no `IotaWitness`,
no `ls` and no redex is in scope. That is what keeps the decision
available at recursor-add, and what makes `iotaTyping_of_admitted`
(batch B5) a theorem about EVERY witness rather than a value at one.
A per-witness cert cannot do that job: `iotaTypingCert w` is indexed by
ONE `w` and may be `none`, while `RecursorGroupIdxAdmitted.typing` is a
Π over `E'`, `hext`, `hrec`, `w` and two equations.

THE RE-BASED IDENTITY SPINE (00 §20.7 D1). Every declared conjunct is
evaluated on the FULL recursor prefix

    L    = nparams + 1 + nMinors + nfields        (nfields = kinds.length)
    Sp   = bvarSpine L
    P    = Sp.take nparams
    Mtv  = .bvar (nMinors + nfields)
    RP   = Sp.take (nparams + 1 + nMinors)
    F    = Sp.drop (nparams + 1 + nMinors)
    PF   = P ++ F

and NOT on `bvarSpine (nparams + nfields)`, the base of the superseded
`ctorIdxPosBuild` (DELETED from `RcicIota.lean` by batch B5, with the
reason at the deletion site): that base carries no motive slot and no
minor slots, so `recPrefix` — which conjuncts 6 and 11d read — cannot
be expressed on it at all. `instPrefix (bvarSpine L)` is the identity
on `.bvar j`, `j < L`, so these declared walks are the OPEN form of the
instance walks and the stored positions are literally the same `Nat`s.
`Mtv` is written `.bvar (nMinors + nfields)` rather than as a spine
lookup: the two agree, and the written form carries neither a `getElem`
bound obligation nor a Nat subtraction.

SHAPE RULES in force (00 §20.7 SHAPE RULES):

* (R-a) NO INVERSION LEMMA. `familyRef` and the level vector are READ
  off the last recursor domain by a total `match` (`recGroupHead`); the
  split `(nparams, nindices)` is ENUMERATED over `List.range (pc+1)`
  and each candidate checked against `majorTyExpr`. `majorTyExpr_inj`
  is therefore not on the path.
* (R-b) FAIL CLOSED. Every `none` / non-`const` / non-`pi` branch is
  `false`, never a vacuous `true` — and that includes the enumeration
  itself (c0e). ONE CLASS OF VACUOUS `true` REMAINS AND IS RECORDED AS
  HARMLESS: at `nMinors = 0` the per-constructor `List.all` is vacuous
  and the Bool returns `true` having run no per-constructor conjunct.
  It is sound — `hidx : ctorIdx < nMinors` (`RcicDeclarative.lean:785`)
  makes `IotaWitness` uninhabited there, so `typing` is vacuous too —
  but (R-b) must not be read as stronger than that.
  THREE FALL-THROUGH ARMS THE CONJUNCTS CALL ARE VACUOUSLY `true` AND
  ARE CUT, NOT ABSENT: `recIdxFromSpineWalk`
  (`RcicDeclarative.lean:491`), `directRecFamilySpine` (`:686`) and
  `directRecFamilySpineExact` (`:708`) all end `| _ :: _, _, _ =>
  true` — conjuncts 11a, 8a and 8b. They are UNREACHABLE here, and the
  cut is conjuncts 3 and 5: conjunct 3 forces `kinds.length = nfields`
  and conjunct 5 forces `isPiTel nfields CA_d`, so the kind list, the
  Π-telescope and `F` (length `nfields` by construction) cannot
  desynchronise, which is the only way those arms are reached. By
  contrast `recIdxPosWalk` (`:556`), `idxPosZip` (`:544`) and
  `recIdxTyWalkPos` (`:667`) fall through to `false`, and
  `recIdxPosBuild` (`:577`) to `none`, so those four need no such
  argument. IF CONJUNCT 3 OR 5 IS EVER REORDERED AFTER 8a / 8b / 11a,
  THIS CUT GOES WITH IT.
* (R-c) EVERY `Option` / `match` SCRUTINEE IS A NAMED `def`
  (`recGroupHead`, `E.members`, `peelPis`, `analyzeFields`, `applyTel`,
  `declaredIdxPositions`), so batch B5's theorem fords it with
  `have h : f … = some …` (00 §18.3 rule 2) instead of re-deriving it.
* (R-d) EVERY CONJUNCT IS ON A RAW STORED TYPE. There is no `ls` at
  recursor-add; a conjunct written at a 00 §20.6 view is not merely
  wrong, it is unwritable. The declared→instance view split is carried
  by the TRANSPORT (batches B3 / B4), not by this file.

STOP RULE (head read; 00 §20.7, re-keyed on PURPOSE as D14). No Nat
subtraction whose PURPOSE is to recover a value the signature should
have carried may appear in this file — `pc - 1` for the last-domain
index, `L - 1 - k` for a spine slot. `recGroupHead` therefore RETURNS
`lastDom` itself and matches `piCount m.mtype` as `pc' + 1`, and there
is no second top-level `match peelPis …`. TWO COUNT SUBTRACTIONS ARE
PERMITTED BY NAME and both are exact under a guard tested FIRST:
`nMinors := r - familyRef - 1` after c0c's
`decide (familyRef + 1 ≤ r)`, and `nfields := piCount m_c.mtype -
nparams` after guard 1's `decide (nparams ≤ piCount m_c.mtype)`.
Neither recovers anything a signature could have carried instead, and
batch B5's theorem READS both guards rather than re-deriving them
(00 §18.3 rule 7).

DUPLICATION, RECORDED AT THE SITE (00 §20.7 POSITIVE DELTA). `piResult`
/ `piLastDom` / `spineHeadRef` / `memberFamRef` (`RcicEnv.lean:158`,
`:163`, `:171`, `:184`) already implement "read `familyRef` off the
last recursor domain" as total declaration-level functions.
`recGroupHead` is the same read, but it must return `lsF`, `pc'` and
`lastDom` as well, and this file is DOWNSTREAM of `RcicIota` and does
not import `RcicEnv` — so it cannot CALL `memberFamRef`. This is a
naming duplication forced by the import direction, not a second belief.
Moving those four definitions here and re-exporting them would put a
non-empty diff in `RcicEnv.lean` and forfeit acceptance item A1.

WHAT THIS FILE DOES NOT CLAIM (00 §20.7 R-9). `recursorGroupAdmitted`
CHECKS at recursor-add, as a kernel does; it does not prove that every
honest 05 declaration PASSES admission. That is a different claim and
is out of scope for this segment.

DEFINITIONS ONLY (batch B1). The transport lemmas (σ-0a … σ-11 and
M-L01) land in batch B4 and `iotaTyping_of_admitted` /
`RecursorGroupIdxAdmitted.ofAdmitted` in batch B5, both in this file.
-/
import rcic.RcicIota

namespace Rcic.Declarative

/-- 05 §13: the recursor's LAST Π-domain is the major type
`I params indices`. Read totally; every failure is `none`.

FOUR components, `lastDom` included, so that the top level never
re-peels and never recovers an index by subtraction (00 §20.7 STOP
RULE, head read): `piCount m.mtype` is matched as `pc' + 1`, so the
last domain is `ds[pc']?` — syntactically the same `Nat` index on both
sides of the B5 pinning chain, with `pc - 1` never written. The `Nat`
component returned is `pc'`, not `pc`, for the same reason: the caller
reconstructs `pc := pc' + 1` and the `+ 1` is the evidence that the
telescope has a last domain at all.

`lsF` is the head's universe list. `hmajorTy`
(`RcicDeclarative.lean:813-817`) pins it to the CANONICAL vector
`(List.range famMember.arity).map Level.param`, so `nU := lsF.length`
is the family's arity WHATEVER `E'` supplies at `familyRef` — which is
the family half of 00 §20.7 REF FREEDOM, and is why `nU` is computed
here rather than by an env lookup. -/
def recGroupHead (m : CheckedMember) :
    Option (Nat × List Level × Nat × Expr Nat) :=
  match piCount m.mtype with
  | 0 => none
  | pc' + 1 =>
      match peelPis (pc' + 1) m.mtype with
      | none => none
      | some (ds, _) =>
          match ds[pc']? with
          | none => none
          | some lastDom =>
              match (appsSpine lastDom).1 with
              | .const familyRef lsF =>
                  some (familyRef, lsF, pc', lastDom)
              | _ => none

/-- The declared index POSITIONS, on the re-based identity spine
(00 §20.7 D1): `recIdxPosBuild nparams PF kinds CA F`.

This is `IotaTyping.idxPositions`'s supplier, and it is the ONE object
in the bundle that is never transported: `mapIndexOf`
(`RcicDeclarative.lean:559-565`) is first-occurrence and neither
`instantiate` nor `instantiateLevels` is injective, so a
`recIdxPosBuild_instantiateLevels` is not true and is not attempted.
The positions are `Nat`s, handed to the instance verbatim; conjuncts
11c and 11d are what check them on both sides. -/
def declaredIdxPositions (nparams nMinors nfields : Nat)
    (kinds : List RecKind) (CA : Expr Nat) : Option (List (List Nat)) :=
  let Sp := bvarSpine (nparams + 1 + nMinors + nfields)
  recIdxPosBuild nparams (Sp.take nparams ++ Sp.drop (nparams + 1 + nMinors))
    kinds CA (Sp.drop (nparams + 1 + nMinors))

/-- Same spine as `declaredIdxPositions`, with `idxSrcOf` in place of
`listIndexOf`. This is the compound-provenance producer: on the real
slot-140 `vaPair` it returns `some` where `declaredIdxPositions` returns
`none`.

IDX-R2: conjunct 11b reads THIS supplier, and 11c/11d read
`recIdxSrcWalk` / `recIdxTySrcWalk`. The Bool alone must yield IotaTyping's
INSTANCE-view walks (`iotaTyping_of_admitted`), so the two ambient facts
the transport needs are checked by the Bool itself, at exactly the members
the sources name: conjunct 11e, `srcMembersStableB`, checks closedness (σ
stage) and level-boundedness (L stage). Both hold for every member of a
well-formed environment. Conjunct 11f, the source-guided fuel at 0
(`recIdxSrcFuelWalk0B`), is the raw openness that `IotaTyping.hidxFuel` is
built from (`recIdxSrcFuelWalk_instantiateLevels_of_zero`). Consequence: a
compound index whose `.constNotFam` constant carries a ground universe
level is refused. At level bound 0 `HasTy.const` cannot type that constant
(its fuel premise), so no ι equation over it is typable at 0. -/
def declaredIdxSrc (fam nparams nMinors nfields : Nat)
    (kinds : List RecKind) (CA : Expr Nat) : Option (List (List IdxSrc)) :=
  let Sp := bvarSpine (nparams + 1 + nMinors + nfields)
  recIdxSrcBuild fam nparams
    (Sp.take nparams ++ Sp.drop (nparams + 1 + nMinors))
    kinds CA (Sp.drop (nparams + 1 + nMinors))

/-- The per-`(nparams, nindices, ctorIdx)` conjuncts of 05 recursor-group
admission, in the ORDER 00 §20.7 fixes (`Bool.and` and `List.all`
short-circuit; cheap discriminating tests first):

     0. m_c := E.members (familyRef+1+ctorIdx)          | none => false
     1. nparams ≤ piCount m_c.mtype ;
        nfields := piCount m_c.mtype - nparams
     2. peelPis (nparams+nfields) m_c.mtype = some (ds_c, res_c)
     3. analyzeFields familyRef (ds_c.drop nparams) = some kinds ;
        kinds.length = nfields
     4. applyTel P m_c.mtype = some CA_d
     5. isPiTel nfields CA_d && directRecConstHead kinds CA_d
                              && resultConstHead kinds CA_d
     6. applyTel (RP.take (nparams+1+ctorIdx)) m.mtype
          = some (.pi mdom_d restMin_d)
     7. decide (mdom_d = minorTel Mtv nparams
          (foldApps (.const (familyRef+1+ctorIdx) lsF) P) kinds CA_d)
     8a. directRecFamilySpine      familyRef lsF nparams P kinds CA_d F
     8b. directRecFamilySpineExact familyRef lsF nparams P kinds CA_d F
     9. recCtorParamAlign m.mtype m_c.mtype P
    10. ctorResultParamShape familyRef res_c nU nparams nfields
    11a. recIdxFromSpineWalk nparams nindices PF kinds CA_d F
    11b. declaredIdxSrc … = some src
    11c. recIdxSrcWalk familyRef nparams PF kinds CA_d F src
    11d. recIdxTySrcWalk familyRef E m.mtype m_c.mtype nparams RP PF kinds CA_d F src
    11e. srcMembersStableB E (idxSrcConstsAll src)
    11f. recIdxSrcFuelWalk0B nparams kinds CA_d F src

CONJUNCT 0 IS THE REF-FREEDOM FIX, and it costs ZERO new definitions.
`w.ctorMember` is the one witness datum reaching `IotaTyping` from a
member other than `m` that the head read does not pin (it reaches
`hidxTy`, `hparamAlign` and, through `hpeel` / `hkinds` / `hctorAfter`,
`kinds` / `ctorResult` / `ctorAfterParams`, hence `hminTel`). Looking
the constructor up at `familyRef+1+ctorIdx` for EVERY
`ctorIdx ∈ List.range nMinors` is what lets B5's step 7 force
`w.ctorMember = m_c` by `Option.some.inj` off `hctor` and `hctorIdx`.
A separate `groupCtorsPresent` conjunct — the one an earlier draft
numbered c0d — is DROPPED: conjunct 0 already refuses whenever any
group ref is undefined, and a separate conjunct would only refuse
EARLIER. The letters at the top level are KEPT as c0a / c0b / c0c /
c0e so that the drop stays visible instead of being closed over by a
renumbering.

Guard 1's subtraction is written only AFTER `nparams ≤ piCount
m_c.mtype` has been tested, so it is not truncating; it is the second
of the two subtractions 00 §20.7's STOP RULE (head read) permits by
name.

Conjunct 8a is BLIND to the level list (its `.directRec` arm is
`| .const r _ => decide (r = fam)`, `RcicDeclarative.lean:681-685`);
conjunct 8b READS it (`:701-707`). That asymmetry is exactly why the
level-arity gate of 00 §20.7 bites at 8b and not at 8a.

The recursor's own ref is `_r`, underscored deliberately: no conjunct
here reads it (conjunct 0 looks up `familyRef+1+ctorIdx`, and `nMinors`
is computed at the top level and passed in), and the binder is kept
only for positional symmetry with `recursorGroupAdmitted E r m`. If a
later conjunct comes to need it, drop the underscore in the same
patch. -/
def recursorGroupAdmittedAt (E : ResolvedEnv) (_r : Nat)
    (m : CheckedMember) (familyRef : Nat) (lsF : List Level)
    (nU nparams nMinors nindices ctorIdx : Nat) : Bool :=
  match E.members (familyRef + 1 + ctorIdx) with          -- conjunct 0
  | none => false
  | some m_c =>
      -- MAY (05 fidelity, NOT load-bearing; 00 §20.7 MAY). Both are
      -- declaration-level 05 §3 / 05 §6 facts that hold on every
      -- carrier; neither is consumed by batch B5's theorem, and either
      -- may be DROPPED — with the drop recorded — if it ever blocks. A
      -- load-bearing conjunct is never weakened in their place. The
      -- third item of that list, `nparams + nindices = piCount
      -- famMember.mtype`, is NOT checked here: it is the witness field
      -- `hnidx` (`RcicDeclarative.lean:783`), so the theorem has it for
      -- free and the Bool need not compute it.
      decide (m_c.mclass = MemberClass.constructorM) &&
      (E.members familyRef).isSome &&
      decide (nparams ≤ piCount m_c.mtype) &&                -- conjunct 1
      (let nfields := piCount m_c.mtype - nparams
       match peelPis (nparams + nfields) m_c.mtype with      -- conjunct 2
       | none => false
       | some (ds_c, res_c) =>
           match analyzeFields familyRef (ds_c.drop nparams) with
           | none => false                                   -- conjunct 3
           | some kinds =>
               decide (kinds.length = nfields) &&
               (let Sp := bvarSpine (nparams + 1 + nMinors + nfields)
                let P := Sp.take nparams
                let RP := Sp.take (nparams + 1 + nMinors)
                let F := Sp.drop (nparams + 1 + nMinors)
                let PF := P ++ F
                let Mtv : Expr Nat := .bvar (nMinors + nfields)
                match applyTel P m_c.mtype with              -- conjunct 4
                | none => false
                | some CA_d =>
                    isPiTel nfields CA_d &&                  -- conjunct 5
                    directRecConstHead kinds CA_d &&
                    resultConstHead kinds CA_d &&
                    (match applyTel (RP.take (nparams + 1 + ctorIdx))
                        m.mtype with                         -- conjunct 6
                     | some (.pi mdom_d _) =>
                         decide (mdom_d =                    -- conjunct 7
                           minorTel Mtv nparams
                             (foldApps
                               (.const (familyRef + 1 + ctorIdx) lsF) P)
                             kinds CA_d)
                     | _ => false) &&
                    directRecFamilySpine familyRef lsF nparams P
                      kinds CA_d F &&                        -- conjunct 8a
                    directRecFamilySpineExact familyRef lsF nparams P
                      kinds CA_d F &&                        -- conjunct 8b
                    recCtorParamAlign m.mtype m_c.mtype P && -- conjunct 9
                    ctorResultParamShape familyRef res_c nU nparams
                      nfields &&                             -- conjunct 10
                    recIdxFromSpineWalk familyRef nparams nindices PF kinds CA_d F &&
                    (match declaredIdxSrc familyRef nparams nMinors nfields
                        kinds CA_d with                      -- conjunct 11b
                     | none => false
                     | some src =>
                         recIdxSrcWalk familyRef nparams PF kinds CA_d F src && -- 11c
                         recIdxTySrcWalk familyRef E m.mtype m_c.mtype nparams RP
                           PF kinds CA_d F src &&                    -- 11d
                         srcMembersStableB E (idxSrcConstsAll src) && -- 11e
                         recIdxSrcFuelWalk0B nparams kinds CA_d F src))) -- 11f

/-- 05 recursor-group admission as a DECLARED `Bool`, decided at
recursor-add from `(E, r, m)` and nothing else (00 §20.7 THE DECLARED
BOOL).

    c0a  decide (lsF = (List.range nU).map Level.param)
    c0b  decide (m.arity = nU) || decide (m.arity = nU + 1)
    c0c  decide (familyRef + 1 ≤ r) ;  nMinors := r - familyRef - 1
    c0e  the enumeration is WITNESSED (fail-closed)
    then the per-candidate `List.all`s over `(nparams, nindices)` and
    the per-constructor `List.all` over `ctorIdx`.

ONE EXPLICIT `decide` PER COMPARISON, house style
(`ctorResultParamShape` writes it that way at
`RcicDeclarative.lean:646-652`). Not because the unparenthesised form
fails to parse — on this project's pinned toolchain
(`leanprover/lean4:v4.14.0`) `=` is `infix:50` and `&&` is `infixl:35`,
so `a + b = pc && decide x` groups as `(a + b = pc) && decide x`, and
it elaborates because `decPropToBool` coerces the `Prop` in `Bool`
position by inserting `decide` — but because that coercion is SILENT,
so which comparisons are decided would stop being readable off the
body.

c0e IS WHAT MAKES THE ENUMERATION FAIL-CLOSED. Without it, if NO
`(nparams, nindices)` candidate satisfies the guard, both `List.all`s
are vacuously `true` and the Bool returns `true` having checked nothing
per-constructor — what (R-b) forbids. It costs batch B5's theorem
nothing: `hnmin` (`RcicDeclarative.lean:784`) plus `hmajorTy` (`:813`)
force the guard at the witness's own split, so `iotaTyping_of_admitted`
reaches the per-conjunct work by instantiating the `all`s and never
consults c0e.

c0a is a LEGIBILITY conjunct, not a soundness one, and is kept on that
ground: `hmajorTy` already makes a declaration whose last-domain head
carried a non-canonical vector UNWITNESSABLE, so omitting c0a would
leave the Bool `true` with no witness to serve. What it buys is that a
reader of this definition alone can see what `nU` is; it costs the
theorem nothing.

c0b is LOAD-BEARING — it is half of the level-arity fix (00 §20.7 THE
LEVEL-ARITY HOLE), the other half being the `IotaWitness` field
`hlsLen` of batch B2. It is exactly the recursor arm of
`groupArityCoherent` (`RcicEnv.lean:220-243`) computed WITHOUT an env
lookup, because `nU` comes from the head read. (`groupArityCoherent`
itself cannot be called: it lives in `RcicEnv`, downstream of this
file.)

The Bool is a SUFFICIENT condition for admission, NOT A REQUIRED ONE
(00 §20.7 D13): `RecursorGroupIdxAdmitted` keeps `typing` as its only
field, so a hand-rolled `typing` still discharges `EnvWf.indMember`'s
`hidxAdm`. "Checks at recursor-add, exactly as a kernel does" is a
statement about THIS Bool, not about the judgment. -/
def recursorGroupAdmitted (E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Bool :=
  match recGroupHead m with
  | none => false
  | some (familyRef, lsF, pc', lastDom) =>
      let pc := pc' + 1
      let nU := lsF.length
      decide (lsF = (List.range nU).map Level.param) &&              -- c0a
      (decide (m.arity = nU) || decide (m.arity = nU + 1)) &&        -- c0b
      decide (familyRef + 1 ≤ r) &&                                 -- c0c
      (let nMinors := r - familyRef - 1
       (List.range (pc + 1)).any (fun np =>                          -- c0e
         (List.range (pc + 1)).any (fun ni =>
           decide (np + 1 + nMinors + ni + 1 = pc) &&
           decide (lastDom = majorTyExpr familyRef lsF np nMinors ni))) &&
       (List.range (pc + 1)).all (fun nparams =>
         (List.range (pc + 1)).all (fun nindices =>
           if decide (nparams + 1 + nMinors + nindices + 1 = pc) &&
              decide (lastDom =
                majorTyExpr familyRef lsF nparams nMinors nindices)
           then (List.range nMinors).all (fun ctorIdx =>
                  recursorGroupAdmittedAt E r m familyRef lsF nU
                    nparams nMinors nindices ctorIdx)
           else true)))

/-! ## 00 §20.7 STAGE σ — the OUTER half of the two-stage transport (B4)

The declared conjuncts above are decided on the RAW stored types and on
the identity spine `Sp = bvarSpine L`; the `IotaTyping` fields read the
00 §20.6 view `instantiateLevels w.ls (stored type)` at the INSTANCE
args `args = recPrefix w.preMajor w.nparams w.nMinors ++ w.fields`. The
transport is two stages, `instantiateLevels` INNER (stage L, batch B3,
`RcicLevelCalc.lean`) and `instPrefix` OUTER (stage σ, this section):

    raw declared Bool at (m.mtype, m_c.mtype, spine slices of Sp)
      │  stage L : X_instantiateLevels   — the TYPES move, the SPINE does not
      ▼
    the same Bool at (instantiateLevels w.ls …, Sp slices)
      │  stage σ : X_instPrefix          — the spine becomes the instance args
      ▼
    the IotaTyping field

σ cannot come first: after σ the subject is `instPrefix args T`, and
pushing `instantiateLevels` through it would need the instance's `args`
to be a map of something the declaration knows, which they are not.

ALL FIFTEEN σ LEMMAS ITERATE ONE INDUCTION on `args`, driven by
`instPrefix`'s own recursion (`RcicIota.lean:3865-3872`): each `cons`
step applies the named sealed `_instantiate` single step at
`j := as.length`, `s := lift 0 as.length a`, feeds the guards forward
with σ-4a/b/c, applies the IH at `as`, and fuses with σ-0b; each `nil`
step closes by σ-0a. No new substitution calculus is introduced here —
every step is an existing sealed lemma of `RcicIota.lean`.

M-L01 (`bvarSpine_instantiateLevels`) is the sixteenth name and is a
stage-L lemma living HERE rather than in `RcicLevelCalc.lean` (00 §20.7
D1): `bvarSpine` is defined at `RcicIota.lean:5420`, `RcicIota` imports
`rcic.RcicLevelCalc`, and `RcicLevelCalc` imports only
`rcic.RcicDeclarative`, so `bvarSpine` is strictly DOWNSTREAM of that
file and is not in scope there. The split is by CONTENT — a lemma goes
beside its subject — not by build convenience.
-/

/-- M-L01 (00 §20.7 STAGE L, sited here by D1). The identity spine is a
FIXED POINT of `instantiateLevels`: `instantiateLevels ls (.bvar i) =
.bvar i` is definitional (`RcicDeclarative.lean:154-155`), so the whole
spine is fixed. This is what makes stage L free of 00 §20.6's
mapped-args hazard — `applyTel_instantiateLevels`
(`RcicLevelCalc.lean:431-434`) exists ONLY in the mapped-args form, and
on this spine the map IS the identity, so the two coincide.

Closed by `exact` and not by `rw` / `simp only`: at `g := id` the
`map_instantiateLevels_bvars` conclusion is about
`fun i => Expr.bvar (id i)`, which is DEFEQ to `Expr.bvar` but is not
the same pattern (00 §20.7, σ-1's TACTIC note, which names this use). -/
theorem bvarSpine_instantiateLevels (lvls : List Level) (n : Nat) :
    (bvarSpine n).map (instantiateLevels lvls) = bvarSpine n :=
  map_instantiateLevels_bvars lvls (fun i => i) (List.range n).reverse

/-- M-L01 on a `take` slice. M-L01 is stated for the WHOLE spine and
every stage-L use is on a SLICE of it (`P`, `RP`), so the glue is a
lemma rather than an assumption. `(Sp.take k)` is NOT `bvarSpine k`
(`bvarSpine n = (List.range n).reverse.map Expr.bvar`, so
`(bvarSpine L).take k = [.bvar (L-1), …, .bvar (L-k)]`), which is why
this goes through `List.map_take` and never by re-reading M-L01 at
`k`. -/
theorem bvarSpine_instantiateLevels_take (lvls : List Level) (n k : Nat) :
    ((bvarSpine n).take k).map (instantiateLevels lvls) = (bvarSpine n).take k := by
  rw [List.map_take, bvarSpine_instantiateLevels]

/-- M-L01 on a `drop` slice (the field slice `F`), by `List.map_drop`.
Sibling of `bvarSpine_instantiateLevels_take`; `PF = P ++ F` then
follows by `List.map_append`. -/
theorem bvarSpine_instantiateLevels_drop (lvls : List Level) (n k : Nat) :
    ((bvarSpine n).drop k).map (instantiateLevels lvls) = (bvarSpine n).drop k := by
  rw [List.map_drop, bvarSpine_instantiateLevels]

/-- σ-0a. The `nil` step of every σ induction. Mirrors
`map_instTel_nil` (`RcicIota.lean:4021-4027`); a second shape is not
invented. -/
theorem map_instPrefix_nil (xs : List (Expr Nat)) :
    xs.map (instPrefix []) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, instPrefix_nil, ih]

/-- σ-0b. The `cons` fusion step of every σ induction: the single
`instantiate` the `_instantiate` lemma produced, followed by the IH's
`instPrefix as`, IS `instPrefix (a :: as)`. Today this fact is INLINED
twice inside `instPrefix_foldApps` (`RcicIota.lean:3905`) and once
inside `instTel_foldApps` (`:4028`); factoring it is why it is written
once here. -/
theorem map_instPrefix_cons (a : Expr Nat) (as : List (Expr Nat))
    (xs : List (Expr Nat)) :
    (xs.map (instantiate as.length (lift 0 as.length a))).map (instPrefix as) =
      xs.map (instPrefix (a :: as)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, instPrefix_cons, ih]

/-- σ-1. `instPrefix args` is the IDENTITY on the identity spine of the
matching length: this is what makes the declared walks the OPEN form of
the instance walks and the stored index positions literally the same
`Nat`s on both sides.

Proved by `exact` on `instPrefix_paramPrefix` (`RcicIota.lean:
4751-4757`) at `nfields := 0`: that lemma concludes about
`(List.range nparams).reverse.map (fun i => Expr.bvar (i + nfields))`,
which at `nfields = 0` is DEFEQ to `bvarSpine nparams` but is NOT the
same pattern, so `rw` / `simp only [instPrefix_paramPrefix]` will not
fire on it (00 §20.7, σ-1's TACTIC). -/
theorem instPrefix_bvarSpine (args : List (Expr Nat)) :
    (bvarSpine args.length).map (instPrefix args) = args :=
  instPrefix_paramPrefix args args.length 0 (Nat.add_zero _).symm
    (List.take_length args)

/-- σ-1 on a `take` slice — the form EVERY conjunct uses (`P`, `RP`).
A PARTIAL slice is not the identity: `(bvarSpine L).take k` is
`[.bvar (L-1), …, .bvar (L-k)]` and its σ-image is `args.take k`. The
length equation is a HYPOTHESIS `hL` rather than a rewrite of the
subject, so the consumer reads `L` (which is what the declared side is
written at) and never has to move `args.length` under the spine. -/
theorem instPrefix_bvarSpine_take (args : List (Expr Nat)) {L : Nat}
    (hL : args.length = L) (k : Nat) :
    ((bvarSpine L).take k).map (instPrefix args) = args.take k := by
  subst hL
  rw [List.map_take, instPrefix_bvarSpine]

/-- σ-1 on a `drop` slice (the field slice `F`), by `List.map_drop`.
Sibling of `instPrefix_bvarSpine_take`.

The THIRD corollary 00 §20.7 offers — the Option-valued
`((bvarSpine L)[k]?).map (instPrefix args) = args[k]?` — is DROPPED
here on that section's own instruction ("It is spare at this head — no
conjunct and no field table row indexes the spine — and is kept only
because the walk proofs may want it; DROP IT if B4 closes without it
rather than seal an unused name"). B4 closes without it: `Mtv` is
written `.bvar (nMinors + nfields)` precisely so that nothing indexes
the spine, and the one place a spine slot is read (σ-11's
`σ Mtv = motive`) goes through `instPrefix_bvar_lt`
(`RcicIota.lean:3933`) directly. -/
theorem instPrefix_bvarSpine_drop (args : List (Expr Nat)) {L : Nat}
    (hL : args.length = L) (k : Nat) :
    ((bvarSpine L).drop k).map (instPrefix args) = args.drop k := by
  subst hL
  rw [List.map_drop, instPrefix_bvarSpine]

/-- σ-2. `applyTel` transports through `instPrefix` on a CLOSED subject.

`hcl` is supplied AT THE 00 §20.6 VIEW, never at the raw stored type:
the composite is `fun j s => instantiate_of_closed _
(instantiateLevels_closed0 w.hctorClosed w.ls) j s`
(`RcicIota.lean:391-393` and `:400-403`), which is why this file needs
no closedness machinery of its own. The raw form of this statement does
not reach any `IotaTyping` field at this head, so it is not offered
(00 §20.7 B4 STOP RULE).

`T` stays PUT across the whole induction — that is exactly what `hcl`
buys: `applyTel_congr_instantiate` (`RcicIota.lean:426`) moves the
subject to `instantiate j s T`, and `hcl` moves it back, so only the
argument list and the result travel. -/
theorem applyTel_instPrefix {T : Expr Nat}
    (hcl : ∀ j s, instantiate j s T = T) :
    (args : List (Expr Nat)) → (xs : List (Expr Nat)) → {U : Expr Nat} →
    applyTel xs T = some U →
    applyTel (xs.map (instPrefix args)) T = some (instPrefix args U)
  | [], xs, U, h => by
      rw [map_instPrefix_nil xs, instPrefix_nil U]
      exact h
  | a :: as, xs, U, h => by
      have hstep := applyTel_congr_instantiate as.length (lift 0 as.length a) xs h
      rw [hcl as.length (lift 0 as.length a)] at hstep
      have ih := applyTel_instPrefix hcl as
        (xs.map (instantiate as.length (lift 0 as.length a))) hstep
      rw [map_instPrefix_cons a as xs, ← instPrefix_cons] at ih
      exact ih

/-- σ-3. `instPrefix` on a Π: the domain takes `instPrefix args`, the
BODY takes `instTel args` (`RcicIota.lean:3981-3986`, the
one-leftover-binder variant), because the body sits under one more
binder than the domain does. The single arithmetic step is
`lift 0 1 (lift 0 as.length a) = lift 0 (as.length + 1) a`,
`lift_lift_merge` (`RcicSubstCalc.lean:60`) — the same idiom already
used at `RcicIota.lean:4383`.

KEPT despite looking removable (00 §20.7): the alternative route
through `applyTel_last_dom` (`RcicIota.lean:4458`) needs a
`peelPis`-prefix truncation at `args.length + 1` from the full-count
peel, and no such lemma exists — the ten `peelPis*` declarations in the
tree are `peelPis`, `_zero`, `_length`, `_piCount`, `_succ`,
`_instantiate_body`, `_instantiate_get`, `_isPiTel`, `_after_applyTel`,
`_instantiateLevels`, and none is a truncation. σ-3 is one lemma; a
truncation lemma plus its consumers is more. -/
theorem instPrefix_pi :
    (args : List (Expr Nat)) → (A B : Expr Nat) →
    instPrefix args (.pi A B) = .pi (instPrefix args A) (instTel args B)
  | [], _, _ => rfl
  | a :: as, A, B => by
      have hmerge : lift 0 1 (lift 0 as.length a) = lift 0 (as.length + 1) a :=
        lift_lift_merge 1 as.length 0 0 (Nat.le_refl 0) (by omega) a
      rw [instPrefix_cons a as (.pi A B)]
      simp only [instantiate]
      rw [hmerge,
        instPrefix_pi as (instantiate as.length (lift 0 as.length a) A)
          (instantiate (as.length + 1) (lift 0 (as.length + 1) a) B),
        instPrefix_cons a as A, instTel_cons a as B]

/-- σ-4a. The `isPiTel` guard travels with the subject, so the walk
lemmas below can feed it forward one `cons` step at a time
(`isPiTel_instantiate`, `RcicIota.lean:556`). -/
theorem isPiTel_instPrefix (n : Nat) :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    isPiTel n T = true → isPiTel n (instPrefix args T) = true
  | [], T, h => by rw [instPrefix_nil T]; exact h
  | a :: as, T, h => by
      rw [instPrefix_cons a as T]
      exact isPiTel_instPrefix n as _
        (isPiTel_instantiate as.length (lift 0 as.length a) n T h)

/-- σ-4b. The `directRecConstHead` guard travels with the subject, under
the `isPiTel` gate that keeps the telescope a Π (M-001;
`directRecConstHead_instantiate`, `RcicIota.lean:638`). -/
theorem directRecConstHead_instPrefix (ks : List RecKind) :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    directRecConstHead ks (instPrefix args T) = true
  | [], T, _, h => by rw [instPrefix_nil T]; exact h
  | a :: as, T, htel, h => by
      rw [instPrefix_cons a as T]
      exact directRecConstHead_instPrefix ks as _
        (isPiTel_instantiate as.length (lift 0 as.length a) ks.length T htel)
        (directRecConstHead_instantiate as.length (lift 0 as.length a) ks T
          htel h)

/-- σ-4c. Sibling of σ-4b for the result head
(`resultConstHead_instantiate`, `RcicIota.lean:719`). The three σ-4
lemmas are what thread σ-11's three guards across its induction. -/
theorem resultConstHead_instPrefix (ks : List RecKind) :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    resultConstHead ks T = true →
    resultConstHead ks (instPrefix args T) = true
  | [], T, _, h => by rw [instPrefix_nil T]; exact h
  | a :: as, T, htel, h => by
      rw [instPrefix_cons a as T]
      exact resultConstHead_instPrefix ks as _
        (isPiTel_instantiate as.length (lift 0 as.length a) ks.length T htel)
        (resultConstHead_instantiate as.length (lift 0 as.length a) ks T
          htel h)

/-- σ-5. Conjunct 11a's walk (`hidxWalk`, `RcicDeclarative.lean:973-974`)
crosses to the instance args. The two guards are the ones
`recIdxFromSpineWalk_instantiate` (`RcicIota.lean:2665-2670`) carries;
they are fed forward one step at a time by σ-4a / σ-4b. -/
theorem recIdxFromSpineWalk_instPrefix (fam nparams nindices : Nat)
    (ks : List RecKind) :
    (args : List (Expr Nat)) → (pf : List (Expr Nat)) → (T : Expr Nat) →
    (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxFromSpineWalk fam nparams nindices pf ks T fs = true →
    recIdxFromSpineWalk fam nparams nindices (pf.map (instPrefix args)) ks
      (instPrefix args T) (fs.map (instPrefix args)) = true
  | [], pf, T, fs, _, _, h => by
      rw [map_instPrefix_nil pf, map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, pf, T, fs, htel, hfam, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hstep := recIdxFromSpineWalk_instantiate fam as.length nparams
        nindices (lift 0 as.length a) pf ks T fs htel hfam h
      have ih := recIdxFromSpineWalk_instPrefix fam nparams nindices ks as
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hfam' hstep
      rw [map_instPrefix_cons a as pf, map_instPrefix_cons a as fs,
        ← instPrefix_cons] at ih
      exact ih

/-- σ-6. Conjunct 11c's walk (`hidxPos`, `RcicDeclarative.lean:975-976`).
`pss` is UNMAPPED in BOTH stages: `idxPosZip`
(`RcicDeclarative.lean:538-544`) CHECKS a stored position against
`paramsFields[i]?` and never recomputes `listIndexOf`, which is the
whole reason the position form exists and why no injectivity of the
substitution is needed anywhere on this route. -/
theorem recIdxPosWalk_instPrefix (nparams : Nat) (ks : List RecKind)
    (pss : List (List Nat)) :
    (args : List (Expr Nat)) → (pf : List (Expr Nat)) → (T : Expr Nat) →
    (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxPosWalk nparams pf ks T fs pss = true →
    recIdxPosWalk nparams (pf.map (instPrefix args)) ks (instPrefix args T)
      (fs.map (instPrefix args)) pss = true
  | [], pf, T, fs, _, _, h => by
      rw [map_instPrefix_nil pf, map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, pf, T, fs, htel, hfam, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hstep := recIdxPosWalk_instantiate as.length nparams
        (lift 0 as.length a) pf ks T fs pss htel hfam h
      have ih := recIdxPosWalk_instPrefix nparams ks pss as
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hfam' hstep
      rw [map_instPrefix_cons a as pf, map_instPrefix_cons a as fs,
        ← instPrefix_cons] at ih
      exact ih

/-- σ-7. Conjunct 11d's walk (`hidxTy`, `RcicDeclarative.lean:979-983`).
ONE σ serves BOTH prefixes: `recIdxTyWalkPos_instantiate`
(`RcicIota.lean:2262-2275`) maps `recPre` AND `paramsFields` under one
substitution and leaves `pss` alone. The two closedness hypotheses are
NOT the walk guards: they are the 00 §20.6 VIEW closedness composite
(`instantiate_of_closed ∘ instantiateLevels_closed0`), the same one
σ-2 and σ-8 read. -/
theorem recIdxTyWalkPos_instPrefix {recType ctorType : Expr Nat}
    (hrecCl : ∀ j s, instantiate j s recType = recType)
    (hctorCl : ∀ j s, instantiate j s ctorType = ctorType)
    (nparams : Nat) (ks : List RecKind) (pss : List (List Nat)) :
    (args : List (Expr Nat)) → (recPre paramsFields : List (Expr Nat)) →
    (T : Expr Nat) → (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxTyWalkPos recType ctorType nparams recPre paramsFields ks T fs pss
      = true →
    recIdxTyWalkPos recType ctorType nparams (recPre.map (instPrefix args))
      (paramsFields.map (instPrefix args)) ks (instPrefix args T)
      (fs.map (instPrefix args)) pss = true
  | [], recPre, paramsFields, T, fs, _, _, h => by
      rw [map_instPrefix_nil recPre, map_instPrefix_nil paramsFields,
        map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, recPre, paramsFields, T, fs, htel, hfam, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hstep := recIdxTyWalkPos_instantiate as.length (lift 0 as.length a)
        recType ctorType (hrecCl as.length (lift 0 as.length a))
        (hctorCl as.length (lift 0 as.length a)) nparams recPre paramsFields
        ks T fs pss htel hfam h
      have ih := recIdxTyWalkPos_instPrefix hrecCl hctorCl nparams ks pss as
        (recPre.map (instantiate as.length (lift 0 as.length a)))
        (paramsFields.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hfam' hstep
      rw [map_instPrefix_cons a as recPre, map_instPrefix_cons a as paramsFields,
        map_instPrefix_cons a as fs, ← instPrefix_cons] at ih
      exact ih

/-- Prefix substitution of one index source's type. One `instantiate`
already returns `some (instantiate j v Ac)` (`idxSrcTy_instantiate`);
this is that equality under `instPrefix`, not a Bool. `s` is not
substituted: it is the stored source. Conjunct 11b stays
`declaredIdxPositions`.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcTy_instPrefix (fam : Nat) (E : ResolvedEnv)
    (ctorType : Expr Nat)
    (hctorCl : ∀ j s, instantiate j s ctorType = ctorType) :
    (args : List (Expr Nat)) → (pf : List (Expr Nat)) → (x : Expr Nat) →
    (s : IdxSrc) → SrcMembersClosed E (idxSrcConsts s) → (Ac : Expr Nat) →
    idxSrcTy fam E ctorType pf x s = some Ac →
    idxSrcTy fam E ctorType (pf.map (instPrefix args)) (instPrefix args x) s =
      some (instPrefix args Ac)
  | [], pf, x, s, _, Ac, h => by
      rw [map_instPrefix_nil pf, instPrefix_nil x, instPrefix_nil Ac]
      exact h
  | a :: as, pf, x, s, hstable, Ac, h => by
      have hstep := idxSrcTy_instantiate fam as.length (lift 0 as.length a) E
        ctorType (hctorCl as.length (lift 0 as.length a)) pf x s hstable Ac h
      have ih := idxSrcTy_instPrefix fam E ctorType hctorCl as
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) x) s hstable
        (instantiate as.length (lift 0 as.length a) Ac) hstep
      rw [map_instPrefix_cons a as pf, ← instPrefix_cons, ← instPrefix_cons] at ih
      exact ih

/-- σ for `recIdxSrcWalk`. `pss` stays put, as in `recIdxPosWalk_instPrefix`:
the source is stored evidence, not recomputed by `idxSrcOf`. -/
theorem recIdxSrcWalk_instPrefix (fam nparams : Nat) (ks : List RecKind)
    (pss : List (List IdxSrc)) :
    (args : List (Expr Nat)) → (pf : List (Expr Nat)) → (T : Expr Nat) →
    (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxSrcWalk fam nparams pf ks T fs pss = true →
    recIdxSrcWalk fam nparams (pf.map (instPrefix args)) ks
      (instPrefix args T) (fs.map (instPrefix args)) pss = true
  | [], pf, T, fs, _, _, h => by
      rw [map_instPrefix_nil pf, map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, pf, T, fs, htel, hfam, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hstep := recIdxSrcWalk_instantiate fam as.length nparams
        (lift 0 as.length a) pf ks T fs pss htel hfam h
      have ih := recIdxSrcWalk_instPrefix fam nparams ks pss as
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hfam' hstep
      rw [map_instPrefix_cons a as pf, map_instPrefix_cons a as fs,
        ← instPrefix_cons] at ih
      exact ih

/-- σ for the index-source fuel walk. The pre-σ source walk supplies the match premise needed when substitution exposes an application. -/
theorem recIdxSrcFuelWalk_instPrefix (fam n nparams : Nat)
    (ks : List RecKind) (pss : List (List IdxSrc)) :
    (args : List (Expr Nat)) → (pf : List (Expr Nat)) → (T : Expr Nat) →
    (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxSrcWalk fam nparams pf ks T fs pss = true →
    recIdxSrcFuelWalk n nparams ks T fs pss →
    recIdxSrcFuelWalk n nparams ks (instPrefix args T)
      (fs.map (instPrefix args)) pss
  | [], _, T, fs, _, _, _, hfuel => by
      rw [map_instPrefix_nil fs, instPrefix_nil T]
      exact hfuel
  | a :: as, pf, T, fs, htel, hfam, hpos, hfuel => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hpos' := recIdxSrcWalk_instantiate fam as.length nparams
        (lift 0 as.length a) pf ks T fs pss htel hfam hpos
      have hfuel' := recIdxSrcFuelWalk_instantiate fam as.length n nparams
        (lift 0 as.length a) pf ks T fs pss htel hfam hpos hfuel
      have ih := recIdxSrcFuelWalk_instPrefix fam n nparams ks pss as
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a)))
        htel' hfam' hpos' hfuel'
      rw [map_instPrefix_cons a as fs, ← instPrefix_cons] at ih
      exact ih

/-- σ for `recIdxTySrcWalk`. Closedness is the 00 §20.6 view composite,
the same one `recIdxTyWalkPos_instPrefix` reads. The alignment inside
the walk is `idxSrcTy`'s type equality, transported by
`idxSrcAlign_instantiate`.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem recIdxTySrcWalk_instPrefix {E : ResolvedEnv}
    {recType ctorType : Expr Nat}
    (hrecCl : ∀ j s, instantiate j s recType = recType)
    (hctorCl : ∀ j s, instantiate j s ctorType = ctorType)
    (fam nparams : Nat) (ks : List RecKind) (pss : List (List IdxSrc))
    (hstable : SrcMembersClosed E (idxSrcConstsAll pss)) :
    (args : List (Expr Nat)) → (recPre pf : List (Expr Nat)) →
    (T : Expr Nat) → (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxTySrcWalk fam E recType ctorType nparams recPre pf ks T fs pss =
      true →
    recIdxTySrcWalk fam E recType ctorType nparams
      (recPre.map (instPrefix args)) (pf.map (instPrefix args)) ks
      (instPrefix args T) (fs.map (instPrefix args)) pss = true
  | [], recPre, pf, T, fs, _, _, h => by
      rw [map_instPrefix_nil recPre, map_instPrefix_nil pf,
        map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, recPre, pf, T, fs, htel, hfam, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hstep := recIdxTySrcWalk_instantiate fam as.length
        (lift 0 as.length a) E recType ctorType
        (hrecCl as.length (lift 0 as.length a))
        (hctorCl as.length (lift 0 as.length a)) nparams recPre pf ks T fs
        pss hstable htel hfam h
      have ih := recIdxTySrcWalk_instPrefix hrecCl hctorCl fam nparams ks
        pss hstable as
        (recPre.map (instantiate as.length (lift 0 as.length a)))
        (pf.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hfam' hstep
      rw [map_instPrefix_cons a as recPre, map_instPrefix_cons a as pf,
        map_instPrefix_cons a as fs, ← instPrefix_cons] at ih
      exact ih

/-- σ-8. Conjunct 9's alignment (`hparamAlign`,
`RcicDeclarative.lean:941-943`). Its hypotheses are CLOSEDNESS, not the
walk guards — `recCtorParamAlign_instantiate`
(`RcicIota.lean:2169-2174`) carries `hrecCl` / `hctorCl` and no
`isPiTel`, so σ-4 does not supply them; they come from the 00 §20.6
view composite, exactly as 00 §20.7's field table says. Both stored
types stay PUT; only the parameter list travels. -/
theorem recCtorParamAlign_instPrefix {recType ctorType : Expr Nat}
    (hrecCl : ∀ j s, instantiate j s recType = recType)
    (hctorCl : ∀ j s, instantiate j s ctorType = ctorType) :
    (args : List (Expr Nat)) → (params : List (Expr Nat)) →
    recCtorParamAlign recType ctorType params = true →
    recCtorParamAlign recType ctorType (params.map (instPrefix args)) = true
  | [], params, h => by
      rw [map_instPrefix_nil params]
      exact h
  | a :: as, params, h => by
      have hstep := recCtorParamAlign_instantiate as.length
        (lift 0 as.length a) recType ctorType
        (hrecCl as.length (lift 0 as.length a))
        (hctorCl as.length (lift 0 as.length a)) params h
      have ih := recCtorParamAlign_instPrefix hrecCl hctorCl as
        (params.map (instantiate as.length (lift 0 as.length a))) hstep
      rw [map_instPrefix_cons a as params] at ih
      exact ih

/-- σ-9. Conjunct 8a's walk (`hfamSpine`,
`RcicDeclarative.lean:934-935`), with the level argument AND the param
argument FREE ON BOTH SIDES: `directRecFamilySpine`
(`RcicDeclarative.lean:675-686`) reads NEITHER — its `.directRec` arm
is `| .const r _ => decide (r = fam)`, so the level list is discarded
and `params` is only carried. That is the same shape M-L05
(`directRecFamilySpine_instantiateLevels`) is stated in, and stating it
this way is what makes a separate `_ls_irrel` lemma unnecessary.

The proof is the standard σ induction at the SAME `ls` / `params`
(`hmap`), followed by one appeal to M-L05 at `lvls := []`, where
`instantiateLevels [] X = X` (`instantiateLevels_nil`,
`RcicLevelCalc.lean:235`) makes that already-sealed lemma deliver
precisely the level/param irrelevance and nothing else. -/
theorem directRecFamilySpine_instPrefix (fam : Nat) (ls ls' : List Level)
    (nparams : Nat) (params params' : List (Expr Nat)) (ks : List RecKind)
    (args : List (Expr Nat)) (T : Expr Nat) (fs : List (Expr Nat))
    (htel : isPiTel ks.length T = true)
    (h : directRecFamilySpine fam ls nparams params ks T fs = true) :
    directRecFamilySpine fam ls' nparams params' ks (instPrefix args T)
      (fs.map (instPrefix args)) = true := by
  have hnilMap : ∀ xs : List (Expr Nat), xs.map (instantiateLevels []) = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ihx =>
        simp only [List.map_cons, instantiateLevels_nil, ihx]
  have hmap : ∀ (args : List (Expr Nat)) (params : List (Expr Nat))
      (T : Expr Nat) (fs : List (Expr Nat)),
      isPiTel ks.length T = true →
      directRecFamilySpine fam ls nparams params ks T fs = true →
      directRecFamilySpine fam ls nparams (params.map (instPrefix args)) ks
        (instPrefix args T) (fs.map (instPrefix args)) = true := by
    intro args0
    induction args0 with
    | nil =>
        intro params0 T0 fs0 _ hd
        rw [map_instPrefix_nil params0, map_instPrefix_nil fs0, instPrefix_nil T0]
        exact hd
    | cons a as ih =>
        intro params0 T0 fs0 htel0 hd
        have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
          ks.length T0 htel0
        have hstep := directRecFamilySpine_instantiate as.length fam ls nparams
          (lift 0 as.length a) params0 ks T0 fs0 htel0 hd
        have ihx := ih (params0.map (instantiate as.length (lift 0 as.length a)))
          (instantiate as.length (lift 0 as.length a) T0)
          (fs0.map (instantiate as.length (lift 0 as.length a))) htel' hstep
        rw [map_instPrefix_cons a as params0, map_instPrefix_cons a as fs0,
          ← instPrefix_cons] at ihx
        exact ihx
  have hmapped := hmap args params T fs htel h
  have hirr := directRecFamilySpine_instantiateLevels [] fam ls ls' nparams
    (params.map (instPrefix args)) params' ks (instPrefix args T)
    (fs.map (instPrefix args)) hmapped
  rw [instantiateLevels_nil, hnilMap (fs.map (instPrefix args))] at hirr
  exact hirr

/-- σ-10. Conjunct 8b's EXACT walk (`hfamSpineExact`,
`RcicDeclarative.lean:958-960`). Unlike σ-9 the level argument is FIXED
— σ does not touch levels — while `params`, `T` and `fs` all move: the
exact walk READS the level list (`decide (lsA = ls)`) and the param
spine (`decide ((appsSpine A).2.take nparams = params)`,
`RcicDeclarative.lean:701-707`). That asymmetry is exactly why the
level-arity gate bites at 8b and not at 8a. -/
theorem directRecFamilySpineExact_instPrefix (fam : Nat) (ls : List Level)
    (nparams : Nat) (ks : List RecKind) :
    (args : List (Expr Nat)) → (params : List (Expr Nat)) → (T : Expr Nat) →
    (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecFamilySpineExact fam ls nparams params ks T fs = true →
    directRecFamilySpineExact fam ls nparams (params.map (instPrefix args)) ks
      (instPrefix args T) (fs.map (instPrefix args)) = true
  | [], params, T, fs, _, h => by
      rw [map_instPrefix_nil params, map_instPrefix_nil fs, instPrefix_nil T]
      exact h
  | a :: as, params, T, fs, htel, h => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hstep := directRecFamilySpineExact_instantiate as.length fam ls
        nparams (lift 0 as.length a) params ks T fs htel h
      have ih := directRecFamilySpineExact_instPrefix fam ls nparams ks as
        (params.map (instantiate as.length (lift 0 as.length a)))
        (instantiate as.length (lift 0 as.length a) T)
        (fs.map (instantiate as.length (lift 0 as.length a))) htel' hstep
      rw [map_instPrefix_cons a as params, map_instPrefix_cons a as fs,
        ← instPrefix_cons] at ih
      exact ih

/-- σ-11. The RHS half of `hminTel` (`RcicDeclarative.lean:984`), the
deepest chain in 00 §20.7's field table: `instPrefix` commutes with the
05 §12 minor telescope. The THREE guards are the ones
`minorTel_instantiate_tel` (`RcicIota.lean:1073-1081`, guards at
`:1076-1078`) carries on `T`, one per `cons` step, threaded across the
induction by σ-4a / σ-4b / σ-4c; without them the statement is not
well-formed, because `minorTel`'s fall-through arm reads `familyIdx`
off a subject a substitution could have changed shape (M-001). The
§20.5 lift-cancellation lemmas live INSIDE that sealed single step; the
iteration inherits them and adds none. -/
theorem minorTel_instPrefix (nparams : Nat) (ks : List RecKind) :
    (args : List (Expr Nat)) → (M ctorAcc T : Expr Nat) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    resultConstHead ks T = true →
    instPrefix args (minorTel M nparams ctorAcc ks T) =
      minorTel (instPrefix args M) nparams (instPrefix args ctorAcc) ks
        (instPrefix args T)
  | [], _, _, _, _, _, _ => rfl
  | a :: as, M, ctorAcc, T, htel, hfam, hres => by
      have htel' := isPiTel_instantiate as.length (lift 0 as.length a)
        ks.length T htel
      have hfam' := directRecConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hfam
      have hres' := resultConstHead_instantiate as.length
        (lift 0 as.length a) ks T htel hres
      rw [instPrefix_cons, minorTel_instantiate_tel as.length
        (lift 0 as.length a) M ctorAcc nparams ks T htel hfam hres]
      exact minorTel_instPrefix nparams ks as
        (instantiate as.length (lift 0 as.length a) M)
        (instantiate as.length (lift 0 as.length a) ctorAcc)
        (instantiate as.length (lift 0 as.length a) T) htel' hfam' hres'


/-! ## 00 §20.7 B5 — THE THEOREM: the declared Bool serves EVERY witness

Stage L (batch B3, `RcicLevelCalc.lean`) and stage σ (batch B4, above)
move a declared `= true` from the RAW stored type on the identity spine
`Sp = bvarSpine L` to the 00 §20.6 view `instantiateLevels w.ls (stored
type)` at the instance args `args = recPrefix w.preMajor w.nparams
w.nMinors ++ w.fields`. Neither is a witness. THIS batch is: it runs the
ten-step PINNING CHAIN of 00 §20.7, discharging every `IotaTyping`
field of an ARBITRARY `IotaWitness E'` of the admitted recursor from
`recursorGroupAdmitted E r m = true`, `hext`, and the witness's own
fields — with NO `EnvWf`, NO `CtxWf`, NO `HasTy` and NO `hcov`.

THE FOUR HEAD-READ FORDING LEMMAS below are what 00 §18.3 rule 2 asks
for: each `Option` / `match` the theorem must pass is discharged by a
NAMED equation (`recGroupHead m = some …`, `E.members … = some …`,
`peelPis … = some …`, `applyTel … = some …`) rather than re-derived
inside the proof, and every impossible arm closes on `Bool.noConfusion`
of a `false = true` the fording produced. `recGroupHead_intro` is the
general introduction form; `recGroupHead_of_witness` is it at a
witness, and is pinning-chain steps 2 and 3 in one line.
`instPrefix_recMotive` is the `σ Mtv = motive` step of the `hminTel`
chain — the ONE place a spine slot is read, and it goes through
`instPrefix_bvar_lt` (`RcicIota.lean:3936`) directly rather than
through a spine `getElem?` corollary, which is why 00 §20.7's σ-1
third corollary was dropped in B4.
-/

/-- Head read of the 05 §13 major type. `majorTyExpr` is a `foldApps`
of a `.const` head over pure `bvar`s, so `appsSpine` returns that head
unchanged (`appsSpine_foldApps`, `RcicIota.lean:3404`, PROMOTED to
`sealedTheorems` by this batch). This is the fact that turns
`hmajorTy`'s stored domain into `recGroupHead`'s `(appsSpine
lastDom).1` match, with no inversion lemma anywhere on the path
(00 §20.7 (R-a): `majorTyExpr_inj` is NOT used). -/
theorem appsSpine_majorTyExpr (familyRef : Nat) (ls : List Level)
    (nparams nMinors nindices : Nat) :
    (appsSpine (majorTyExpr familyRef ls nparams nMinors nindices)).1 =
      Expr.const familyRef ls := by
  rw [majorTyExpr, appsSpine_foldApps]
  rfl

/-- FORDING (00 §18.3 rule 2) for the head read: the four `match`es of
`recGroupHead` discharged by four NAMED equations. Stated generally so
the theorem never re-derives them, and so the `pc' + 1` shape — not
`pc - 1` — is what the caller supplies (00 §20.7 STOP RULE, head
read). -/
theorem recGroupHead_intro (m : CheckedMember) (pc' : Nat)
    (ds : List (Expr Nat)) (body lastDom : Expr Nat) (fam : Nat)
    (ls : List Level)
    (hpc : piCount m.mtype = pc' + 1)
    (hpeel : peelPis (pc' + 1) m.mtype = some (ds, body))
    (hlast : ds[pc']? = some lastDom)
    (hhead : (appsSpine lastDom).1 = Expr.const fam ls) :
    recGroupHead m = some (fam, ls, pc', lastDom) := by
  simp only [recGroupHead, hpc, hpeel, hlast, hhead]

/-- PINNING CHAIN steps 2 and 3 (00 §20.7), in one line. `hnmin`
(`RcicDeclarative.lean:784`) gives the Π-count as `pc' + 1` with
`pc' = nparams + 1 + nMinors + nindices`; `hpeelRec` (`:798-799`) gives
the peel at exactly that count, so `w.recDoms` is determined by
`m.mtype` alone; `hmajorTy` (`:813-817`) gives `ds[pc']?` — the SAME
`Nat` index on both sides, with no subtraction on either — and pins the
head's universe list to 05 §2's CANONICAL vector.

Hence `familyRef = w.familyRef` and `nU := lsF.length =
w.famMember.arity` (`List.length_map` + `List.length_range` at the use
site), WHATEVER `E'` supplies at `familyRef`: that is the family half
of 00 §20.7 REF FREEDOM, and it is why the theorem needs no env lookup
for the family. -/
theorem recGroupHead_of_witness {E : ResolvedEnv} (w : IotaWitness E) :
    recGroupHead w.recMember =
      some (w.familyRef, (List.range w.famMember.arity).map Level.param,
        w.nparams + 1 + w.nMinors + w.nindices,
        majorTyExpr w.familyRef
          ((List.range w.famMember.arity).map Level.param)
          w.nparams w.nMinors w.nindices) := by
  have hmaj : w.recDoms[w.nparams + 1 + w.nMinors + w.nindices]? =
      some (majorTyExpr w.familyRef
        ((List.range w.famMember.arity).map Level.param)
        w.nparams w.nMinors w.nindices) := by
    simpa only [majorTyExpr] using w.hmajorTy
  exact recGroupHead_intro w.recMember (w.nparams + 1 + w.nMinors + w.nindices)
    w.recDoms w.recBody _ w.familyRef _ w.hnmin.symm w.hpeelRec hmaj
    (appsSpine_majorTyExpr _ _ _ _ _)

/-- `σ Mtv = motive`: the motive slot of the instance args is what the
declared `Mtv := .bvar (nMinors + nfields)` instantiates to. The RHS
half of `hminTel` needs exactly this after σ-11 has distributed
`instPrefix` over `minorTel`.

`Mtv` is written as a bare `bvar` and not as a spine lookup precisely
so that this step carries no `getElem` bound obligation on the spine:
the only bound obligation is `nMinors + nfields < args.length`, which
is `hpre` arithmetic, and the slot it names is `args[nparams]?` =
`w.preMajor[w.nparams]?` = `recMotiveOf_spec` (`RcicDeclarative.lean:
889`, PROMOTED to `sealedTheorems` by this batch). No Nat subtraction
is written here either: `instPrefix_bvar_lt`'s own index arithmetic is
discharged by `omega` on an arithmetic goal (00 §18.3 rule 9). -/
theorem instPrefix_recMotive {E : ResolvedEnv} (w : IotaWitness E) :
    instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
        (Expr.bvar (w.nMinors + w.fields.length))
      = recMotiveOf w := by
  have hpreLen : (recPrefix w.preMajor w.nparams w.nMinors).length
      = w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre; omega
  have hlen : (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields).length
      = w.nparams + 1 + w.nMinors + w.fields.length := by
    simp only [List.length_append, hpreLen]
  refine instPrefix_bvar_lt (by rw [hlen]; omega) ?_
  have hidx : (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields).length - 1 -
      (w.nMinors + w.fields.length) = w.nparams := by
    rw [hlen]; omega
  rw [hidx, List.getElem?_append, if_pos (by rw [hpreLen]; omega)]
  simp only [recPrefix]
  rw [List.getElem?_take,
    if_pos (by omega : w.nparams < w.nparams + 1 + w.nMinors)]
  exact recMotiveOf_spec w

/-- 00 §20.7 THE THEOREM. The declared `Bool`, decided at recursor-add
from `(E, r, m)` alone, serves EVERY `IotaWitness` of that recursor in
every extension `E'` of `E`.

`def`, not `theorem`: `IotaTyping` is `Type`-valued
(`RcicDeclarative.lean:916`), 00 §18.3 rule 1. NO `hcov`, NO `EnvWf`,
NO `CtxWf`, NO `HasTy`. Every side condition comes from a witness
field, a Bool conjunct, or the `hlsLen` + c0b arithmetic.

THE PINNING CHAIN, in the order 00 §20.7 fixes it.

1. `m`, `r` — `hm`, `hr`, by `subst`.
2. `recDoms`, `lastDom` — `recGroupHead_of_witness` (`hnmin` +
   `hpeelRec`; `peelPis` is a function).
3. `familyRef`, `lsF`, `nU` — the same lemma's `hmajorTy` half, plus
   `List.length_map` / `List.length_range` for `nU = w.famMember.arity`.
4. `nMinors` — `hrecIdx` (`:787`) gives `w.recRef - w.familyRef - 1 =
   w.nMinors` by `omega` on an arithmetic goal (00 §18.3 rule 9). This
   is one of the TWO Nat subtractions 00 §20.7's STOP RULE permits by
   name, and it is READ here, never re-derived (rule 7).
5. `(nparams, nindices)` — instantiate the two `List.all`s at
   `w.nparams` / `w.nindices` (`List.all_eq_true` + `List.mem_range`,
   the bounds from `hnmin`); the `if`-guard's two conjuncts are `hnmin`
   and step 3's `hmajorTy` AT THE CANONICAL VECTOR, so both close by
   reflexivity and c0e is never consulted.
6. `ctorIdx` — instantiate the inner `List.all` at `w.ctorIdx` (`hidx`,
   `:785`).
7. `w.ctorMember` — THE REF-FREEDOM FIX. Conjunct 0 gives `E.members
   (familyRef+1+ctorIdx) = some m_c`; `hext` lifts it to `E'`;
   `hctor` (`:759`) rewritten by `hctorIdx` (`:786`) gives
   `E'.members (familyRef+1+ctorIdx) = some w.ctorMember`;
   `Option.some.inj` forces `w.ctorMember = m_c`.
8. `kinds`, `ctorDoms`, `ctorResult`, `nfields` — `hnpar` (`:782`)
   fixes `nfields = w.fields.length` (guard 1's subtraction, the SECOND
   permitted one, READ from the guard); `hpeel` (`:792`) and `hkinds`
   (`:795`) then determine all four from the RAW `m_c.mtype`. No level
   step: 00 §20.6's rule is that `peelPis`-valued fields stay RAW.
9. `hnU : w.famMember.arity ≤ w.ls.length` — step 3 gives
   `w.famMember.arity = nU`; c0b gives `m.arity ∈ {nU, nU+1}`;
   `hlsLen` (`:834`, batch B2) gives `w.ls.length = m.arity`. `omega`
   on an arithmetic goal. THIS IS WHAT MAKES M-L15 / M-L16 APPLICABLE,
   i.e. what makes `hfamSpineExact` and `hminTel` reachable at all.
10. `w.ctorAfterParams` — conjunct 4 through stage L
    (`applyTel_instantiateLevels` with `P.map iL = P` by M-L01) then
    stage σ (σ-2 at the 00 §20.6 view, with the CLOSEDNESS COMPOSITE
    `instantiate_of_closed ∘ instantiateLevels_closed0` supplied at the
    VIEW and never at the raw type), against `hctorAfter` (`:829-830`)
    by `Option.some.inj`. Every walk downstream is iterated over BOTH
    stages in that order.

FIELD BY FIELD (00 §20.7's field table). `hmotive` is `recMotiveOf_spec`
— no transport. `mdom` / `restMin` / `hminDom` are `recMinorDom`
(`RcicIota.lean:4535`), which produces all three unconditionally at ANY
`lvls`; conjunct 6 is still needed, but only to IDENTIFY `mdom` for
`hminTel`. `hctorResShape` is conjunct 10 verbatim on the RAW
`w.ctorResult` (`w.hlen` converts `nfields` to `kinds.length`) — no
transport, and no `hnU`, because the field's third argument is
`w.famMember.arity` and `hmajorTy` bridges it to `lsF.length`
unconditionally. `idxPositions` is `declaredIdxPositions`' output
handed over VERBATIM: `recIdxPosBuild` is never transported, because
`mapIndexOf` is first-occurrence and neither substitution is
injective. The remaining seven are M-Lxx then σ-x, exactly as the
field table routes them; `hminTel` is the deepest — conjunct 6 through
stage L, stage σ, `Option.some.inj` and an `Expr.pi` injection on the
LHS, and conjunct 7 through M-L04-at-the-canonical-seed (M-L16, the
`hnU` consumer) then σ-11 with `σ Mtv = motive` on the RHS.

WHAT THIS DOES NOT CLAIM (00 §20.7 R-9 / D13). The Bool is a
SUFFICIENT condition for admission, not a required one, and nothing
here proves that every honest 05 declaration PASSES admission. -/
def iotaTyping_of_admitted {E E' : ResolvedEnv} {r : Nat}
    {m : CheckedMember}
    (hadm : recursorGroupAdmitted E r m = true)
    (hext : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (w : IotaWitness E') (hr : w.recRef = r) (hm : w.recMember = m) :
    IotaTyping E' w := by
  subst hr
  subst hm
  -- ── measurements used throughout ──────────────────────────────────
  have hpreLen : (recPrefix w.preMajor w.nparams w.nMinors).length
      = w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre; omega
  have hargsLen : (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields).length
      = w.nparams + 1 + w.nMinors + w.fields.length := by
    simp only [List.length_append, hpreLen]
  have hcanonLen : ((List.range w.famMember.arity).map Level.param).length
      = w.famMember.arity := by
    rw [List.length_map, List.length_range]
  -- the 00 §20.6 VIEW closedness composite
  have hrecCl : ∀ j s,
      instantiate j s (instantiateLevels w.ls w.recMember.mtype)
        = instantiateLevels w.ls w.recMember.mtype :=
    fun j s => instantiate_of_closed _
      (instantiateLevels_closed0 w.hrecClosed w.ls) j s
  have hctorCl : ∀ j s,
      instantiate j s (instantiateLevels w.ls w.ctorMember.mtype)
        = instantiateLevels w.ls w.ctorMember.mtype :=
    fun j s => instantiate_of_closed _
      (instantiateLevels_closed0 w.hctorClosed w.ls) j s
  -- ── steps 1-6 : head read, nMinors, the split, the constructor ────
  simp only [recursorGroupAdmitted, recGroupHead_of_witness w, hcanonLen]
    at hadm
  have hnm : w.recRef - w.familyRef - 1 = w.nMinors := by
    have := w.hrecIdx; omega
  rw [hnm] at hadm
  have hc0b := boolAnd_right (boolAnd_left (boolAnd_left hadm))
  have hall := boolAnd_right (boolAnd_right hadm)
  have hallP := List.all_eq_true.mp hall w.nparams
    (List.mem_range.mpr (by have := w.hnmin; omega))
  have hallI := List.all_eq_true.mp hallP w.nindices
    (List.mem_range.mpr (by have := w.hnmin; omega))
  rw [if_pos (by simp only [decide_eq_true_eq, Bool.and_eq_true, decide_True,
      and_self] :
    (decide (w.nparams + 1 + w.nMinors + w.nindices + 1
        = w.nparams + 1 + w.nMinors + w.nindices + 1) &&
      decide (majorTyExpr w.familyRef
          ((List.range w.famMember.arity).map Level.param)
          w.nparams w.nMinors w.nindices
        = majorTyExpr w.familyRef
            ((List.range w.famMember.arity).map Level.param)
            w.nparams w.nMinors w.nindices)) = true)] at hallI
  have hAt := List.all_eq_true.mp hallI w.ctorIdx (List.mem_range.mpr w.hidx)
  -- ── step 9 : the level-arity tie (hlsLen + c0b) ───────────────────
  have hc0b' : w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc0b
    exact hc0b
  have hnU : w.famMember.arity ≤ w.ls.length := by
    have h1 := w.hlsLen
    cases hc0b' with
    | inl h => omega
    | inr h => omega
  -- ── step 7 : REF FREEDOM — conjunct 0 forces w.ctorMember ─────────
  cases hmcE : E.members (w.familyRef + 1 + w.ctorIdx) with
  | none =>
      simp only [recursorGroupAdmittedAt, hmcE] at hAt
      exact Bool.noConfusion hAt
  | some m_c =>
      have hmc : w.ctorMember = m_c := by
        have h1 := hext _ _ hmcE
        rw [← w.hctorIdx, w.hctor] at h1
        exact Option.some.inj h1
      subst hmc
      simp only [recursorGroupAdmittedAt, hmcE] at hAt
      -- ── step 8 : nfields / peel / kinds, all RAW ──────────────────
      have hnf : piCount w.ctorMember.mtype - w.nparams = w.fields.length := by
        have := w.hnpar; omega
      rw [hnf] at hAt
      simp only [w.hpeel, w.hkinds] at hAt
      have hg := boolAnd_right (boolAnd_right hAt)
      -- ── conjunct 4 : the declared ctorAfterParams ─────────────────
      cases hCA : applyTel
          ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
            w.nparams) w.ctorMember.mtype with
      | none =>
          simp only [hCA] at hg
          exact Bool.noConfusion hg
      | some CA_d =>
          simp only [hCA] at hg
          have g1 := boolAnd_left (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left (boolAnd_left (boolAnd_left (boolAnd_left
              (boolAnd_left hg))))))))
          have g2 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left (boolAnd_left (boolAnd_left (boolAnd_left
              (boolAnd_left hg))))))))
          have g3 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left (boolAnd_left (boolAnd_left (boolAnd_left hg))))))) 
          have g4 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left (boolAnd_left (boolAnd_left hg)))))) 
          have g5 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left (boolAnd_left hg)))))
          have g6 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left
            (boolAnd_left hg))))
          have g7 := boolAnd_right (boolAnd_left (boolAnd_left (boolAnd_left hg)))
          have g8 := boolAnd_right (boolAnd_left (boolAnd_left hg))
          have g9 := boolAnd_right (boolAnd_left hg)
          have g10 := boolAnd_right hg

          -- ── σ images of the three spine slices (00 §20.7 σ-1) ─────
          have hPsig : (((bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams).map
              (instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)))
              = w.preMajor.take w.nparams := by
            rw [instPrefix_bvarSpine_take _ hargsLen w.nparams,
              List.take_append_of_le_length (by rw [hpreLen]; omega)]
            simp only [recPrefix]
            rw [List.take_take w.nparams (w.nparams + 1 + w.nMinors) w.preMajor,
              (by omega : min w.nparams (w.nparams + 1 + w.nMinors) = w.nparams)]
          have hRPsig : (((bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).take
                (w.nparams + 1 + w.nMinors)).map
              (instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)))
              = recPrefix w.preMajor w.nparams w.nMinors := by
            rw [instPrefix_bvarSpine_take _ hargsLen (w.nparams + 1 + w.nMinors)]
            exact List.take_left' hpreLen
          have hFsig : (((bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)).map
              (instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)))
              = w.fields := by
            rw [instPrefix_bvarSpine_drop _ hargsLen (w.nparams + 1 + w.nMinors)]
            exact List.drop_left' hpreLen
          -- ── step 10 : w.ctorAfterParams IS the transported CA_d ───
          have hCAL := applyTel_instantiateLevels w.ls
            ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
              w.nparams) w.ctorMember.mtype
          rw [bvarSpine_instantiateLevels_take, hCA, Option.map_some'] at hCAL
          have hCAsig := applyTel_instPrefix hctorCl
            (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
            ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
              w.nparams) hCAL
          rw [hPsig] at hCAsig
          have hCAeq : w.ctorAfterParams =
              instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                (instantiateLevels w.ls CA_d) :=
            Option.some.inj (w.hctorAfter.symm.trans hCAsig)
          -- the three guards at the 00 §20.6 view
          have g1L : isPiTel w.kinds.length
              (instantiateLevels w.ls CA_d) = true := by
            rw [w.hlen, isPiTel_instantiateLevels]; exact g1
          have g2L : directRecConstHead w.kinds
              (instantiateLevels w.ls CA_d) = true := by
            rw [directRecConstHead_instantiateLevels]; exact g2
          have g3L : resultConstHead w.kinds
              (instantiateLevels w.ls CA_d) = true := by
            rw [resultConstHead_instantiateLevels]; exact g3
          -- ── hfamSpine : conjunct 8a, M-L05 then σ-9 ───────────────
          have hfamSpine : directRecFamilySpine w.familyRef w.ls w.nparams
              (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams
              w.fields = true := by
            have hL := directRecFamilySpine_instantiateLevels w.ls w.familyRef
              ((List.range w.famMember.arity).map Level.param) w.ls w.nparams
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams)
              w.kinds CA_d
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g5
            rw [bvarSpine_instantiateLevels_drop] at hL
            have hS := directRecFamilySpine_instPrefix w.familyRef w.ls w.ls
              w.nparams
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams) (w.preMajor.take w.nparams) w.kinds
              (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
              (instantiateLevels w.ls CA_d)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g1L hL
            rw [hFsig, ← hCAeq] at hS
            exact hS
          -- ── hfamSpineExact : conjunct 8b, M-L15 then σ-10 ─────────
          have hfamSpineExact : directRecFamilySpineExact w.familyRef
              (w.ls.take w.famMember.arity) w.nparams
              (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams
              w.fields = true := by
            have hL := directRecFamilySpineExact_canonical_take w.ls w.familyRef
              w.famMember.arity w.nparams hnU
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams) w.kinds CA_d
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g6
            rw [bvarSpine_instantiateLevels_take,
              bvarSpine_instantiateLevels_drop] at hL
            have hS := directRecFamilySpineExact_instPrefix w.familyRef
              (w.ls.take w.famMember.arity) w.nparams w.kinds
              (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams) (instantiateLevels w.ls CA_d)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g1L hL
            rw [hPsig, hFsig, ← hCAeq] at hS
            exact hS
          -- ── hparamAlign : conjunct 9, M-L14 then σ-8 ──────────────
          have hparamAlign : recCtorParamAlign
              (instantiateLevels w.ls w.recMember.mtype)
              (instantiateLevels w.ls w.ctorMember.mtype)
              (w.preMajor.take w.nparams) = true := by
            have hL := recCtorParamAlign_instantiateLevels w.ls
              w.recMember.mtype w.ctorMember.mtype
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams) g7
            rw [bvarSpine_instantiateLevels_take] at hL
            have hS := recCtorParamAlign_instPrefix hrecCl hctorCl
              (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams) hL
            rw [hPsig] at hS
            exact hS
          -- ── hidxWalk : conjunct 11a, M-L07 then σ-5 ───────────────
          have hPFL : (((bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).take w.nparams ++
              (bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)).map (instantiateLevels w.ls))
              = (bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).take w.nparams ++
              (bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors) := by
            rw [List.map_append, bvarSpine_instantiateLevels_take,
              bvarSpine_instantiateLevels_drop]
          have hPFsig : (((bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).take w.nparams ++
              (bvarSpine
                (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)).map
              (instPrefix (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)))
              = recParamsFields w := by
            rw [List.map_append, hPsig, hFsig]
            rfl
          have hidxWalk : recIdxFromSpineWalk w.familyRef w.nparams w.nindices
              (recParamsFields w) w.kinds w.ctorAfterParams w.fields = true := by
            have hL := recIdxFromSpineWalk_instantiateLevels w.familyRef w.ls
              w.nparams w.nindices
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams ++
               (bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors))
              w.kinds CA_d
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g9
            rw [hPFL, bvarSpine_instantiateLevels_drop] at hL
            have hS := recIdxFromSpineWalk_instPrefix w.familyRef w.nparams
              w.nindices w.kinds (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).take
                w.nparams ++
               (bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors))
              (instantiateLevels w.ls CA_d)
              ((bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                (w.nparams + 1 + w.nMinors)) g1L g2L hL
            rw [hPFsig, hFsig, ← hCAeq] at hS
            exact hS
          -- ── conjunct 11b : the declared sources ───────────────────
          cases hSrc : declaredIdxSrc w.familyRef w.nparams w.nMinors
              w.fields.length w.kinds CA_d with
          | none =>
              simp only [hSrc] at g10
              exact Bool.noConfusion g10
          | some src =>
              simp only [hSrc] at g10
              have g11c := boolAnd_left (boolAnd_left (boolAnd_left g10))
              have g11d := boolAnd_right (boolAnd_left (boolAnd_left g10))
              have g11e := boolAnd_right (boolAnd_left g10)
              have g11f := boolAnd_right g10
              have hstable := srcMembersStable_hext g11e hext
              -- hidxPos : conjunct 11c, M-L09 then σ-6
              have hidxPosL : recIdxSrcWalk w.familyRef w.nparams
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  w.kinds (instantiateLevels w.ls CA_d)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src = true := by
                have hL := recIdxSrcWalk_instantiateLevels w.ls w.familyRef
                  w.nparams
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  w.kinds CA_d
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src g11c
                rw [hPFL, bvarSpine_instantiateLevels_drop] at hL
                exact hL
              have hidxPos : recIdxSrcWalk w.familyRef w.nparams
                  (recParamsFields w) w.kinds w.ctorAfterParams w.fields src =
                  true := by
                have hS := recIdxSrcWalk_instPrefix w.familyRef w.nparams
                  w.kinds src
                  (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  (instantiateLevels w.ls CA_d)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) g1L g2L hidxPosL
                rw [hPFsig, hFsig, ← hCAeq] at hS
                exact hS
              -- hidxTy : conjunct 11d, hext then M-L12 then σ-7
              have hidxTy : recIdxTySrcWalk w.familyRef E'
                  (instantiateLevels w.ls w.recMember.mtype)
                  (instantiateLevels w.ls w.ctorMember.mtype) w.nparams
                  (recPrefix w.preMajor w.nparams w.nMinors)
                  (recParamsFields w) w.kinds w.ctorAfterParams w.fields src =
                  true := by
                have hExt := recIdxTySrcWalk_hext hext w.familyRef
                  w.recMember.mtype w.ctorMember.mtype w.nparams
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      (w.nparams + 1 + w.nMinors))
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  w.kinds CA_d
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src g11d
                have hL := recIdxTySrcWalk_instantiateLevels w.ls w.familyRef E'
                  w.recMember.mtype w.ctorMember.mtype w.nparams
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      (w.nparams + 1 + w.nMinors))
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  w.kinds CA_d
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src hstable.2 hExt
                rw [bvarSpine_instantiateLevels_take, hPFL,
                  bvarSpine_instantiateLevels_drop] at hL
                have hS := recIdxTySrcWalk_instPrefix hrecCl hctorCl
                  w.familyRef w.nparams w.kinds src hstable.1
                  (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      (w.nparams + 1 + w.nMinors))
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  (instantiateLevels w.ls CA_d)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) g1L g2L hL
                rw [hRPsig, hPFsig, hFsig, ← hCAeq] at hS
                exact hS
              -- hidxFuel : conjunct 11f, fuel-zero to n then σ
              have hidxFuel : ∀ n, rawConstOK n w.ls →
                  recIdxSrcFuelWalk n w.nparams w.kinds w.ctorAfterParams
                    w.fields src := by
                intro n hraw
                have h0 := recIdxSrcFuelWalk0B_sound w.nparams w.kinds CA_d
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src g11f
                have hL := recIdxSrcFuelWalk_instantiateLevels_of_zero n
                  w.nparams w.ls w.kinds CA_d
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) src h0 hraw
                rw [bvarSpine_instantiateLevels_drop] at hL
                have hS := recIdxSrcFuelWalk_instPrefix w.familyRef n w.nparams
                  w.kinds src
                  (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                      w.nparams ++
                   (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors))
                  (instantiateLevels w.ls CA_d)
                  ((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).drop
                      (w.nparams + 1 + w.nMinors)) g1L g2L hidxPosL hL
                rw [hFsig, ← hCAeq] at hS
                exact hS
              -- ── conjuncts 6 and 7 : hminTel, the deepest chain ────
              have hRPtk : (((bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                    (w.nparams + 1 + w.nMinors)).take
                    (w.nparams + 1 + w.ctorIdx))
                  = (bvarSpine
                    (w.nparams + 1 + w.nMinors + w.fields.length)).take
                    (w.nparams + 1 + w.ctorIdx) := by
                rw [List.take_take (w.nparams + 1 + w.ctorIdx)
                  (w.nparams + 1 + w.nMinors)
                  (bvarSpine (w.nparams + 1 + w.nMinors + w.fields.length)),
                  (by have := w.hidx; omega :
                    min (w.nparams + 1 + w.ctorIdx) (w.nparams + 1 + w.nMinors)
                      = w.nparams + 1 + w.ctorIdx)]
              rw [hRPtk] at g4
              cases hU : applyTel ((bvarSpine
                  (w.nparams + 1 + w.nMinors + w.fields.length)).take
                  (w.nparams + 1 + w.ctorIdx)) w.recMember.mtype with
              | none => simp only [hU] at g4; exact Bool.noConfusion g4
              | some U =>
                  simp only [hU] at g4
                  cases U with
                  | bvar _ => exact Bool.noConfusion g4
                  | sort _ => exact Bool.noConfusion g4
                  | const _ _ => exact Bool.noConfusion g4
                  | app _ _ => exact Bool.noConfusion g4
                  | lam _ _ => exact Bool.noConfusion g4
                  | letE _ _ _ => exact Bool.noConfusion g4
                  | lit _ => exact Bool.noConfusion g4
                  | pi mdomD restMinD =>
                      have h7 := of_decide_eq_true g4
                      have ⟨mdom, restMin, hminDom⟩ := recMinorDom w w.ls
                      have h6L := applyTel_instantiateLevels w.ls
                        ((bvarSpine
                          (w.nparams + 1 + w.nMinors + w.fields.length)).take
                          (w.nparams + 1 + w.ctorIdx)) w.recMember.mtype
                      rw [bvarSpine_instantiateLevels_take, hU,
                        Option.map_some'] at h6L
                      have h6S := applyTel_instPrefix hrecCl
                        (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                        ((bvarSpine
                          (w.nparams + 1 + w.nMinors + w.fields.length)).take
                          (w.nparams + 1 + w.ctorIdx)) h6L
                      rw [instPrefix_bvarSpine_take _ hargsLen
                        (w.nparams + 1 + w.ctorIdx),
                        List.take_append_of_le_length
                          (by rw [hpreLen]; have := w.hidx; omega)] at h6S
                      simp only [recPrefix] at h6S
                      rw [List.take_take (w.nparams + 1 + w.ctorIdx)
                          (w.nparams + 1 + w.nMinors) w.preMajor,
                        (by have := w.hidx; omega :
                          min (w.nparams + 1 + w.ctorIdx)
                            (w.nparams + 1 + w.nMinors)
                            = w.nparams + 1 + w.ctorIdx)] at h6S
                      have hpiEq : Expr.pi mdom restMin =
                          instPrefix
                            (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                            (instantiateLevels w.ls (Expr.pi mdomD restMinD)) :=
                        Option.some.inj (hminDom.symm.trans h6S)
                      simp only [instantiateLevels, instPrefix_pi] at hpiEq
                      injection hpiEq with hmd _
                      rw [h7, iotaMdom_canonical_seed w.ls w.famMember.arity
                          w.nparams (w.familyRef + 1 + w.ctorIdx) hnU
                          (Expr.bvar (w.nMinors + w.fields.length))
                          ((bvarSpine
                            (w.nparams + 1 + w.nMinors + w.fields.length)).take
                            w.nparams) w.kinds CA_d,
                        bvarSpine_instantiateLevels_take] at hmd
                      simp only [instantiateLevels] at hmd
                      rw [minorTel_instPrefix w.nparams w.kinds
                          (recPrefix w.preMajor w.nparams w.nMinors ++ w.fields)
                          (Expr.bvar (w.nMinors + w.fields.length))
                          (foldApps (Expr.const (w.familyRef + 1 + w.ctorIdx)
                            (w.ls.take w.famMember.arity))
                            ((bvarSpine
                              (w.nparams + 1 + w.nMinors + w.fields.length)).take
                              w.nparams))
                          (instantiateLevels w.ls CA_d) g1L g2L g3L,
                        instPrefix_recMotive w, instPrefix_foldApps,
                        instPrefix_const, hPsig, ← hCAeq, ← w.hctorIdx] at hmd
                      exact {
                        motive := recMotiveOf w
                        hmotive := recMotiveOf_spec w
                        mdom := mdom
                        restMin := restMin
                        hminDom := hminDom
                        hfamSpine := hfamSpine
                        hparamAlign := hparamAlign
                        hfamSpineExact := hfamSpineExact
                        hctorResShape := by rw [w.hlen]; exact g8
                        idxPositions := src
                        hidxWalk := hidxWalk
                        hidxPos := hidxPos
                        hidxTy := hidxTy
                        hidxFuel := hidxFuel
                        hminTel := by simp only [iotaMdom]; exact hmd }


/-- 00 §20.7's SMART CONSTRUCTOR. `RecursorGroupIdxAdmitted` is NOT
restated and NOT relocated: the structure stays BYTE-IDENTICAL at
`RcicIota.lean`, and this is the intended way to build one.

`def`, not `theorem`, because both `RecursorGroupIdxAdmitted` and
`IotaTyping` are `Type`-valued (00 §18.3 rule 1); the explicit `{_E'}`
binder keeps structure-instance elaboration from having to guess.

WHY THE STRUCTURE IS NOT RESTATED TO CARRY `hadm` (00 §20.7 D13).
Deriving `typing` from a Bool INSIDE the structure would need
`recursorGroupAdmitted` defined before it, i.e. inside `RcicIota.lean`,
which this segment exists to stay out of; and relocating the structure
here would force `import rcic.RcicAdmit` into `RcicEnv.lean`, whose
ZERO-LINE DIFF is acceptance item A1. CONSEQUENCE, stated rather than
discovered: the Bool is a SUFFICIENT condition for admission and NOT A
REQUIRED ONE — a hand-rolled `typing` still discharges
`EnvWf.indMember`'s `hidxAdm`, so "checks at recursor-add, exactly as a
kernel does" is a statement about the BOOL, not about the judgment, and
the DT-018 footprint records a change in how `hidxAdm` CAN BE SUPPLIED,
not in what it MEANS. `RcicEnv.lean:1311`'s `adm.typing hext w.hrec w
rfl rfl` is untouched verbatim, with zero argument-order risk because
the field is not restated. -/
def RecursorGroupIdxAdmitted.ofAdmitted {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (h : recursorGroupAdmitted E r m = true) :
    RecursorGroupIdxAdmitted E r m :=
  { typing := fun {_E'} hext _hrec w hr hm =>
      iotaTyping_of_admitted h hext w hr hm }

end Rcic.Declarative
