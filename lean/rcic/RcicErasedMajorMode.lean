/-
RcicErasedMajorMode — S3 (W-TABLE-ERASED-MAJOR-ELIM), EM0 slice.
Credit: ChatGPT S3 (#7314), `research/rcic/sortrow/S3_ERASED_MAJOR_ELIM.md` §2–4.

§2 — declaration-side admission mode.  `familyBit` / `resultBit` are the exact
§2 definitions: each is `levelIsZero` of the σ-substituted, `ls`-instantiated
level, so each is a pure `Bool` and `eqN`-invariant.  `wrapperMode` is the mode
computed from the two bits:

    resultBit = true                      → resultErased
    resultBit = false ∧ familyBit = true  → erasedMajor   (relevant-result)
    resultBit = false ∧ familyBit = false → retainedMajor

`LevelHom` is the level substitution σ (`Level → Level`, applied through
`lvlSubst σ` — DT-002's `eval_lvlSubst`); `instLevel ls` is the special case
`lvlSubst (levelParamSubst ls)`.

§3 — mode invariance: `instLevel_args_congr` (no `levelBounded`), the
LevelHom `eqN`-map, `UniformProp`/`UniformType` preservation under any
`lvlSubst σ`, and `familyBit_eqNList` / `resultBit_eqNList` /
`wrapperMode_eqNList` — the mode is a function of the `eqNList` class of
`ls`, never of raw universe syntax.

§4 — static selection.  From the real admission cell
(`envWfT_recursorCell hW w.hrec w.hrecK`) plus `IotaWitness.recData_admitted`,
`familyBit = true` and `resultBit = false` force the `singletonProp`
selection: `constructors.length = 1`, `w.nMinors = 1`, `w.ctorIdx = 0`, and
`w.minor` is `preMajor[nparams + 1]` via `w.hminor`.

Teeth: (a) a `propOnly` admission (`multipleProp` / `hiddenDataProp`) is
refused in this mode — `propOnly` forces `resultBit = true`; (b) a mode
discriminator decided by raw universe syntax is refused by an `eqNList`
pair; (c) a wrong minor index is refused — `w.nMinors = 1` leaves `0` as
the only in-domain index.

Out of scope (S3 §4, EM1–EM3): typed-spine correspondence and the
arbitrary-`iota` erasure simulation — declaration-side mode stability and
the singleton selection only.
-/

import rcic.RcicInductivePolicy
import rcic.RcicIotaLegacyAdm
import rcic.RcicIATypedIota
import rcic.RcicUniverseClass
import rcic.RcicLevelCalc
import rcic.RcicLevelZero
import rcic.RcicLevelDec

namespace Rcic.Declarative

/-! ## §2 bits and mode -/

/-- The level homomorphism `σ : Level → Level`, applied through
`lvlSubst σ`.  `instLevel ls` is `lvlSubst (levelParamSubst ls)`. -/
abbrev LevelHom : Type := Level → Level

/-- §2 `familyBit`: is the family's result level uniformly zero after
`ls`-instantiation and `σ`-substitution? -/
def familyBit {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom) (ls : List Level) :
    Bool :=
  levelIsZero (lvlSubst σ (instLevel ls a.family.resultLevel))

/-- §2 `resultBit`: is the recursor motive level uniformly zero after
`ls`-instantiation and `σ`-substitution? -/
def resultBit {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom) (ls : List Level) :
    Bool :=
  levelIsZero
    (lvlSubst σ (instLevel ls
      (policyMotiveLevel a.family.member.arity a.policy)))

/-- The three modes of §2, computed from `familyBit`/`resultBit`. -/
inductive ErasedMajorMode : Type
  | resultErased : ErasedMajorMode
  | erasedMajor : ErasedMajorMode
  | retainedMajor : ErasedMajorMode
  deriving DecidableEq

/-- §2 `wrapperMode`: `resultBit = true` → result-erased;
`resultBit = false ∧ familyBit = true` → erased-major;
otherwise retained-major. -/
def wrapperMode {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom) (ls : List Level) :
    ErasedMajorMode :=
  if resultBit a σ ls then .resultErased
  else if familyBit a σ ls then .erasedMajor
  else .retainedMajor

/-! ## §3 mode invariance -/

/-- `§3` `LevelHom.levelSub.eqN_map`: any level substitution preserves
`eqN`.  Immediate from `eval_lvlSubst` — evaluation under ρ is evaluation
of the original level under the composed valuation. -/
theorem levelHom_eqN_map (σ : LevelHom) {u v : Level} (h : eqN u v) :
    eqN (lvlSubst σ u) (lvlSubst σ v) := by
  intro ρ
  rw [eval_lvlSubst, eval_lvlSubst]
  exact h _

/-- `evalTotal` commutes with `lvlSubst σ`, mirroring
`evalTotal_instLevel`. -/
theorem evalTotal_lvlSubst (σ : LevelHom) (ν : Nat → Nat) (l : Level) :
    evalTotal ν (lvlSubst σ l) =
      evalTotal (fun i => evalTotal ν (σ (.param i))) l := by
  apply Option.some.inj
  calc
    some (evalTotal ν (lvlSubst σ l)) =
        eval (fun i => some (ν i)) (lvlSubst σ l) := (eval_total ν _).symm
    _ = eval (fun i => eval (fun j => some (ν j)) (σ (.param i))) l :=
      eval_lvlSubst σ _ l
    _ = eval (fun i => some (evalTotal ν (σ (.param i)))) l :=
      eval_congr_val (fun i => eval_total ν (σ (.param i))) l
    _ = some (evalTotal (fun i => evalTotal ν (σ (.param i))) l) :=
      eval_total _ l

/-- §3: any `LevelHom` preserves `UniformProp` (level structure). -/
theorem uniformProp_levelHom (σ : LevelHom) {l : Level} (h : UniformProp l) :
    UniformProp (lvlSubst σ l) := by
  intro ν
  rw [evalTotal_lvlSubst]
  exact h _

/-- §3: any `LevelHom` preserves `UniformType` (level structure). -/
theorem uniformType_levelHom (σ : LevelHom) {l : Level} (h : UniformType l) :
    UniformType (lvlSubst σ l) := by
  intro ν
  rw [evalTotal_lvlSubst]
  exact h _

/-- §3 `instLevel_args_congr`: `eqNList ls ls'` transports `instLevel` —
no `levelBounded` premise.  (Reuses `instLevel_eqNList`.) -/
theorem instLevel_args_congr {ls ls' : List Level} (h : eqNList ls ls')
    (u : Level) : eqN (instLevel ls u) (instLevel ls' u) :=
  instLevel_eqNList h u

/-- `levelIsZero` is `eqN`-invariant (Declarative layer). -/
theorem levelIsZero_eqN_congr {u v : Level} (h : eqN u v) :
    levelIsZero u = levelIsZero v := by
  cases hu : levelIsZero u <;> cases hv : levelIsZero v
  · rfl
  · exact absurd
      ((levelIsZero_iff u).2
        fun ρ => (h ρ).trans ((levelIsZero_iff v).1 hv ρ))
      (by simp [hu])
  · exact absurd
      ((levelIsZero_iff v).2
        fun ρ => (h ρ).symm.trans ((levelIsZero_iff u).1 hu ρ))
      (by simp [hv])
  · rfl

/-- A `UniformType` level is never `levelIsZero` (Declarative layer). -/
theorem levelIsZero_eq_false_of_uniformType {u : Level} (h : UniformType u) :
    levelIsZero u = false := by
  cases hz : levelIsZero u with
  | false => rfl
  | true =>
      exfalso
      have h0 := h (fun _ => 0)
      have hu0 : evalTotal (fun _ => 0) u = 0 := by
        have he : eval (fun i => some ((fun _ : Nat => 0) i)) u = some 0 :=
          (levelIsZero_iff u).1 hz _
        rw [eval_total] at he
        exact Option.some.inj he
      omega

/-- §3 `familyBit_eqNList`: the family bit depends only on the `eqNList`
class of the instantiation. -/
theorem familyBit_eqNList {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom)
    {ls ls' : List Level} (h : eqNList ls ls') :
    familyBit a σ ls = familyBit a σ ls' := by
  unfold familyBit
  exact levelIsZero_eqN_congr (levelHom_eqN_map σ (instLevel_args_congr h _))

/-- §3 `resultBit_eqNList`: the result bit depends only on the `eqNList`
class of the instantiation. -/
theorem resultBit_eqNList {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom)
    {ls ls' : List Level} (h : eqNList ls ls') :
    resultBit a σ ls = resultBit a σ ls' := by
  unfold resultBit
  exact levelIsZero_eqN_congr (levelHom_eqN_map σ (instLevel_args_congr h _))

/-- §3 `wrapperMode_eqNList`: the mode depends only on the `eqNList`
class of the instantiation — mode is semantic, not syntactic. -/
theorem wrapperMode_eqNList {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (σ : LevelHom)
    {ls ls' : List Level} (h : eqNList ls ls') :
    wrapperMode a σ ls = wrapperMode a σ ls' := by
  unfold wrapperMode
  rw [resultBit_eqNList a σ h, familyBit_eqNList a σ h]

/-! ## §4 teeth -/

/-- Tooth (a): a `propOnly` admission (`EliminationSelection.multipleProp` /
`hiddenDataProp` — a Prop-only family with more than one constructor, or a
singleton with unsafe fields) is refused in erased-major mode: `propOnly`
forces `policyMotiveLevel = .zero`, so `resultBit = true`. -/
theorem propOnly_resultBit_true {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (σ : LevelHom) (ls : List Level) (hp : a.policy = .propOnly) :
    resultBit a σ ls = true := by
  simp [resultBit, hp, policyMotiveLevel, instLevel, levelParamSubst,
    lvlSubst, levelIsZero]

/-- Tooth (a), mode level: a `propOnly` admission collapses to
`resultErased`, never `erasedMajor`. -/
theorem propOnly_mode_refused {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (σ : LevelHom) (ls : List Level) (hp : a.policy = .propOnly) :
    wrapperMode a σ ls ≠ .erasedMajor := by
  simp [wrapperMode, propOnly_resultBit_true a σ ls hp]

/-- Mutant discriminator: the raw-syntax zero check `l == .zero` instead
of the semantic `levelIsZero`. -/
def synZeroBit (l : Level) : Bool := decide (l = .zero)

/-- Tooth (b): a mode discriminator decided by raw universe syntax is
refused — the `eqNList` pair `[.zero] ≈ [.max .zero .zero]` flips the
syntactic bit on `instLevel ls (.param 0)` while the semantic bit is
`eqNList`-stable (`familyBit_eqNList` / `wrapperMode_eqNList`). -/
theorem synBit_not_eqNList_invariant :
    ∃ ls ls' : List Level, eqNList ls ls' ∧
      synZeroBit (instLevel ls (.param 0)) ≠
        synZeroBit (instLevel ls' (.param 0)) := by
  refine ⟨[.zero], [.max .zero .zero], ⟨fun ρ => by simp [eval], trivial⟩, ?_⟩
  decide

/-- §1 scope pin: raw `RecKind` is exactly `plain | directRec` — there is
no function-recursive branch to compile. -/
theorem recKind_plain_or_directRec (k : RecKind) :
    k = .plain ∨ k = .directRec := by
  cases k <;> simp

/-! ## §4 static selection -/

/-- §4 static selection: from the real admission cell
(`envWfT_recursorCell hW w.hrec w.hrecK`) and the alignment facts of
`IotaWitness.recData_admitted`, `familyBit = true` + `resultBit = false`
force the `singletonProp` branch — one constructor, one minor,
`ctorIdx = 0`, and `w.minor` read off `preMajor[nparams + 1]` by
`w.hminor`.  Any other in-domain index is refused (`nMinors = 1`). -/
theorem erasedMajor_unique_minor {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) {σ : LevelHom} {ls : List Level}
    (hfam : familyBit (envWfT_recursorCell hW w.hrec w.hrecK).adm σ ls =
      true)
    (hres : resultBit (envWfT_recursorCell hW w.hrec w.hrecK).adm σ ls =
      false) :
    (envWfT_recursorCell hW w.hrec w.hrecK).adm.constructors.length = 1 ∧
      w.nMinors = 1 ∧ w.ctorIdx = 0 ∧
      w.preMajor[w.nparams + 1]? = some w.minor ∧
      ∀ k, k < w.nMinors → k = w.ctorIdx := by
  obtain ⟨_, _, _, _, hnm⟩ :=
    IotaWitness.recData_admitted
      (envWfT_recursorCell hW w.hrec w.hrecK).adm
      (envWfT_recursorCell hW w.hrec w.hrecK).sub w rfl rfl
  -- `resultBit = false` rules out `propOnly` (its motive level is `.zero`).
  have hP :
      (envWfT_recursorCell hW w.hrec w.hrecK).adm.policy = .anySort := by
    cases hp : (envWfT_recursorCell hW w.hrec w.hrecK).adm.policy with
    | anySort => rfl
    | propOnly =>
        simp [resultBit, hp, policyMotiveLevel, instLevel, levelParamSubst,
          lvlSubst, levelIsZero] at hres
  have hsel : EliminationSelection
      (envWfT_recursorCell hW w.hrec w.hrecK).adm.family.resultLevel
      (envWfT_recursorCell hW w.hrec w.hrecK).adm.constructors.length
      (∀ i, PolicyConstructorView.AllFieldsSafe
        ((envWfT_recursorCell hW w.hrec w.hrecK).adm.constructorViews i))
      .anySort :=
    hP ▸ (envWfT_recursorCell hW w.hrec w.hrecK).adm.selected
  rcases (EliminationSelection.anySort_iff _ _ _).mp hsel with
    hUT | ⟨hUP, hks⟩
  · -- `uniformType` contradicts `familyBit = true`: a UniformType level is
    -- never `levelIsZero`, and the class survives `instLevel`/`lvlSubst`.
    exfalso
    unfold familyBit at hfam
    have hUT' := uniformType_levelHom σ (uniformType_instLevel hUT ls)
    rw [levelIsZero_eq_false_of_uniformType hUT'] at hfam
    exact Bool.noConfusion hfam
  · rcases hks with hk0 | ⟨hk1, _⟩
    · -- `emptyProp`: `constructors.length = 0`, but the witness's `hidx`
      -- needs a minor to exist.
      exfalso
      have hn0 : w.nMinors = 0 := hnm.trans hk0
      have hlt := w.hidx
      omega
    · -- `singletonProp`: the unique constructor/minor.
      have hn1 : w.nMinors = 1 := hnm.trans hk1
      have hc0 : w.ctorIdx = 0 := by
        have hlt := w.hidx
        omega
      have hm := w.hminor
      rw [hc0] at hm
      exact ⟨hk1, hn1, hc0, hm, fun k hk => by omega⟩

/-- Tooth (c): a wrong minor index is refused — in erased-major mode the
minor domain is the singleton `k < w.nMinors`, so `k` is forced to
`w.ctorIdx = 0`. -/
theorem erasedMajor_minor_index_unique {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) {σ : LevelHom} {ls : List Level}
    (hfam : familyBit (envWfT_recursorCell hW w.hrec w.hrecK).adm σ ls =
      true)
    (hres : resultBit (envWfT_recursorCell hW w.hrec w.hrecK).adm σ ls =
      false)
    (k : Nat) (hk : k < w.nMinors) : k = w.ctorIdx := by
  obtain ⟨_, _, _, _, huniq⟩ := erasedMajor_unique_minor hW w hfam hres
  exact huniq k hk

end Rcic.Declarative

#print axioms Rcic.Declarative.levelHom_eqN_map
#print axioms Rcic.Declarative.evalTotal_lvlSubst
#print axioms Rcic.Declarative.uniformProp_levelHom
#print axioms Rcic.Declarative.uniformType_levelHom
#print axioms Rcic.Declarative.instLevel_args_congr
#print axioms Rcic.Declarative.levelIsZero_eqN_congr
#print axioms Rcic.Declarative.levelIsZero_eq_false_of_uniformType
#print axioms Rcic.Declarative.familyBit_eqNList
#print axioms Rcic.Declarative.resultBit_eqNList
#print axioms Rcic.Declarative.wrapperMode_eqNList
#print axioms Rcic.Declarative.propOnly_resultBit_true
#print axioms Rcic.Declarative.propOnly_mode_refused
#print axioms Rcic.Declarative.synBit_not_eqNList_invariant
#print axioms Rcic.Declarative.recKind_plain_or_directRec
#print axioms Rcic.Declarative.erasedMajor_unique_minor
#print axioms Rcic.Declarative.erasedMajor_minor_index_unique
