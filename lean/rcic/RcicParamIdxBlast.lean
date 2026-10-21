import rcic.RcicParamIdxPins
import rcic.ScmSrcGroupsRec
import rcic.ScmSrcGroupsRecVA
import rcic.RcicIARecUniquePins
import rcic.RcicIARecTyped
import rcic.RcicIndGroupAdmitted
import rcic.RcicIndGroupExclusions
import rcic.RcicPinEqEraseWf
import rcic.RcicPinHEqEraseWf
import rcic.RcicPinLoopEraseWf
import rcic.RcicTypedDeltaRecPins
import rcic.RcicFuelGapPins
import rcic.RcicTypedFunRecPins
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec
import rcic.RcicTypedIdxAdmittedPins

/-!
# R6a blast radius — param-referencing `familyIdx` in the admitted corpus

The `iotaOpenRhs` repair (R6a) changes the emitted iota schema **exactly where a
`.recursive` field's `familyIdx`-retained index argument references a constructor
parameter**: the old `lift 0 C` dropped `fields.length` from the shift, so a param
reference surfaced as a pre-major marker `fl` slots early.  The blast-radius
question — *did any previously admitted environment contain such a reference?* —
is answered here by measuring every `RecursorEliminationAdmitted` record in the
tree, once, at the admission convention (`CtorFieldsPermitted`'s own
`fieldAnalyze` call shape).

`groupParamIdxFree a` re-runs `fieldAnalyze` at fuel 64 — every pinned
`CtorFieldsPermitted`/`FieldPermitted` discharge in the tree uses fuel ≤ 40, and
`fieldAnalyze_mono` transfers a `.permitted` verdict (with its payload) to any
larger bound — and checks each `.recursive` field's retained index arguments for
a `bvar` reaching the parameter block.  A non-`permitted` verdict is reported as
`false` (a measurement flag, not a claim of refusal).

**Result: 44 of 45 carriers pass; `piGroupAdmitted` fails — and `piEnv` is the
R6a fixture itself**, the sole env in the corpus whose `familyIdx` output
contains a constructor-parameter reference (`g P`).  Every pre-existing admitted
env emitted param-free indices, so the lift change is bit-identical on their
schemas (consistent with the green cone rebuild: every pinned
`iotaSchemaAt`/`hstable` literal is unchanged).  The exclusion and uniqueness
fixtures measure `true` for information — they were refused on other grounds
(census, field-kind, recursor identity), not index content.
-/

namespace Rcic.Declarative

/-- `∀ i : Fin n, f i` as one Bool (the `finAllB` pattern). -/
def finAllB (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  (List.range n).all fun j => if hj : j < n then f j hj else false

/-- `bvar k` at internal binder depth `d`, under ambient
`[params(np), fields(j), Tdoms(dj)]`, references a constructor parameter iff
`k ≥ d + dj + j` (`base = dj + j`): `bvar`s below `d + dj` are internal or
telescope-domain refs, `d + dj ≤ k < d + dj + j` are earlier-field refs, and
`d + dj + j ≤ k` reaches the parameter block (or the out-of-context garbage that
a permitted analysis cannot contain). -/
def idxParamFree (base : Nat) : Nat → Expr Nat → Bool
  | d, .bvar k => decide (k < d + base)
  | d, .app f a => idxParamFree base d f && idxParamFree base d a
  | d, .lam A b => idxParamFree base d A && idxParamFree base (d + 1) b
  | d, .pi A B => idxParamFree base d A && idxParamFree base (d + 1) B
  | d, .letE A v b => idxParamFree base d A && idxParamFree base d v &&
      idxParamFree base (d + 1) b
  | _, _ => true

/-- One field at the `CtorFieldsPermitted` convention (`np + j` depth), fuel 64.
`.recursive` shapes must have param-free retained indices; `.nonrecursive`
carries none by construction; anything else is reported `false`. -/
def fieldParamFree (E : ResolvedEnv) (fam nuniv np ni j : Nat)
    (T : Expr Nat) : Bool :=
  match fieldAnalyze E 64 fam nuniv np ni (np + j) T with
  | .permitted (.recursive dj) idxs => idxs.all (idxParamFree (dj + j) 0)
  | .permitted .nonrecursive idxs => idxs.isEmpty
  | _ => false

/-- All fields of one constructor view. -/
def ctorParamFree {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member) : Bool :=
  finAllB c.fields.length fun j hj =>
    fieldParamFree E family.ref family.member.arity
      family.parameters.length family.indices.length j (c.fields.get ⟨j, hj⟩)

/-- All constructors of an admitted recursor group. -/
def groupParamIdxFree {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Bool :=
  finAllB a.constructors.length fun i hi =>
    ctorParamFree (a.constructorViews ⟨i, hi⟩)

/-! ### The measure, per carrier — typed-pin groups -/

theorem blast_nat      : groupParamIdxFree natGroupAdmitted    = true := rfl
theorem blast_false    : groupParamIdxFree falseGroupAdmitted  = true := rfl
theorem blast_true     : groupParamIdxFree trueGroupAdmitted   = true := rfl
theorem blast_struct   : groupParamIdxFree structGroupAdmitted = true := rfl
theorem blast_and      : groupParamIdxFree andGroupAdmitted    = true := rfl
theorem blast_list     : groupParamIdxFree listGroupU          = true := rfl
theorem blast_vec      : groupParamIdxFree vecGroupU           = true := rfl
theorem blast_dr       : groupParamIdxFree drGroupAdmitted     = true := rfl
theorem blast_fg       : groupParamIdxFree Ann.fgGroupAdmitted = true := rfl
theorem blast_w        : groupParamIdxFree wGroupAdmitted      = true := rfl
theorem blast_eq       : groupParamIdxFree eqGroupAdm          = true := rfl
theorem blast_heq      : groupParamIdxFree heqGroupAdm         = true := rfl
theorem blast_pinLoop  : groupParamIdxFree pinLoopGroupAdm     = true := rfl

/-- The R6a fixture is the corpus's sole param-referencing index. -/
theorem blast_pi       : groupParamIdxFree Ann.piGroupAdmitted = false := rfl

/-! ### The scm corpus (`envPre` groups) -/

theorem blast_scmN       : groupParamIdxFree Scm.SrcG.aRecN       = true := rfl
theorem blast_scmBytes   : groupParamIdxFree Scm.SrcG.aRecBytes   = true := rfl
theorem blast_scmRefT    : groupParamIdxFree Scm.SrcG.aRecRefT    = true := rfl
theorem blast_scmDA      : groupParamIdxFree Scm.SrcG.aRecDA      = true := rfl
theorem blast_scmI       : groupParamIdxFree Scm.SrcG.aRecI       = true := rfl
theorem blast_scmBL      : groupParamIdxFree Scm.SrcG.aRecBL      = true := rfl
theorem blast_scmFT      : groupParamIdxFree Scm.SrcG.aRecFT      = true := rfl
theorem blast_scmLt      : groupParamIdxFree Scm.SrcG.aRecLt      = true := rfl
theorem blast_scmBC      : groupParamIdxFree Scm.SrcG.aRecBC      = true := rfl
theorem blast_scmDM10    : groupParamIdxFree Scm.SrcG.aRecDM10    = true := rfl
theorem blast_scmND      : groupParamIdxFree Scm.SrcG.aRecND      = true := rfl
theorem blast_scmNEA     : groupParamIdxFree Scm.SrcG.aRecNEA     = true := rfl
theorem blast_scmIEA     : groupParamIdxFree Scm.SrcG.aRecIEA     = true := rfl
theorem blast_scmSL      : groupParamIdxFree Scm.SrcG.aRecSL      = true := rfl
theorem blast_scmBLL     : groupParamIdxFree Scm.SrcG.aRecBLL     = true := rfl
theorem blast_scmFTL     : groupParamIdxFree Scm.SrcG.aRecFTL     = true := rfl
theorem blast_scmBLC     : groupParamIdxFree Scm.SrcG.aRecBLC     = true := rfl
theorem blast_scmSEA     : groupParamIdxFree Scm.SrcG.aRecSEA     = true := rfl
theorem blast_scmFTE     : groupParamIdxFree Scm.SrcG.aRecFTE     = true := rfl
theorem blast_scmNthB    : groupParamIdxFree Scm.SrcG.aRecNthB    = true := rfl
theorem blast_scmNthF    : groupParamIdxFree Scm.SrcG.aRecNthF    = true := rfl
theorem blast_scmCCT     : groupParamIdxFree Scm.SrcG.aRecCCT     = true := rfl
theorem blast_scmBCT     : groupParamIdxFree Scm.SrcG.aRecBCT     = true := rfl
theorem blast_scmNEL     : groupParamIdxFree Scm.SrcG.aRecNEL     = true := rfl
theorem blast_scmNTB     : groupParamIdxFree Scm.SrcG.aRecNTB     = true := rfl
theorem blast_scmValueAt : groupParamIdxFree Scm.SrcG.aRecValueAt = true := rfl

/-! ### Exclusion / uniqueness fixtures (not `EnvWfT`-admitted; measured for
    information — they fail admission on other grounds, not index content) -/

theorem blast_nelSwapped : groupParamIdxFree aRecNELSwapped  = true := rfl
theorem blast_tooth      : groupParamIdxFree toothAdmGarbage = true := rfl
theorem blast_bad        : groupParamIdxFree badGroupAdmitted = true := rfl
theorem blast_posProp    : groupParamIdxFree PosProp.group   = true := rfl
theorem blast_posList    : groupParamIdxFree PosList.group   = true := rfl

end Rcic.Declarative
