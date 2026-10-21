import rcic.RcicDTMetaTypedEmbed
import rcic.RcicDTMetaTypedEnv
import rcic.RcicTypedGroupPinsVec
import rcic.ScmSrcGroupsEnvWfT

/-!
# EG-006 on the typed root: theorem and opaque rigidity (tymig segment A)

04 §5/§6: "Theorem and opaque bodies are part of checked-group identity even though they are rigid
after admission"; a theorem's or opaque's body "is checked and stored but rigid". GM-THEORY-004
(`docs/rcic/GLOBAL_MUTANT_REGISTRY.md:39`): "Theorem/opaque bodies delta-reduce."

On the typed root the content was already split between two places. The rigidity half is the sealed
`DT015T_rigidity` (`RcicDTMetaTypedEmbed`): a member with `transparent m.mclass = false` has a constant
that takes no `Step`. The checked-and-stored half is the shape of `EnvWfT.thm` / `EnvWfT.opaque`
(`RcicTypedEnv`), which type the body at admission. The only typed pin of `DT015T_rigidity` sits at a
RECURSOR (`pin_DT015T_natU`). This module states the row for its own subject, theorem and opaque
members, and pins it at a real theorem and a real opaque member:

* `envWfT_rigid_hasBody` / `envWfT_rigidBody` — an `EnvWfT` walk: every `theoremM`/`opaqueM`
  member of an `EnvWfT` environment carries a body, typed at its stored type at admission's own
  judgment form (level context `0`, empty context). Group cells cannot contribute such a member: the
  group's members are the family, the constructors and the recursor (`EnvWfT.group`'s class
  premises), read through `groupMembersT_mem_cases`.
* `EG006T_theorem_opaque_rigidity` — the row: such a member's body is checked and stored, the
  δ-lookup `transparentBody` returns `none` at every level list, and its constant takes no `Step`.
  The last conjunct USES the sealed `DT015T_rigidity`; it is not restated.

Pins, both at real fixtures:
* a theorem: slot 153 of `srcEnvG`, `lt010 : Lt 0 10`, through `envWfT_srcEnvG`;
* an opaque: `pinOpqEnvU`, `EnvWfT.opaque` over `natEnvUWfT` with exactly the type and body of
  `pinDefEnvU`'s definition (`Sort 0 : Sort 1` at ref 4). The contrast pin shows the same body as a
  DEFINITION does δ-unfold (`Step.delta`, and the sealed `pin_DT014T_defU`), so rigidity is the class,
  not the body.

Teeth (GM-THEORY-004): `transparentBodyG4` is `transparentBody` read through the mutant
transparency `transparentG4`, under which theorem and opaque members are transparent. At both fixtures
it returns the stored body, so the row's second conjunct is false under the mutant
(`tooth_GM_THEORY_004_opq`, `tooth_GM_THEORY_004_srcThm`). Second instrument: the raw machine
(`kernelStepRaw`, `whnfAt`) leaves both rigid constants in place and unfolds the definition, by
evaluation (`rfl` / kernel `rfl`).

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## (1) the walk: rigid members carry a typed body -/

/-- every `theoremM` / `opaqueM` member of an `EnvWfT` environment has a body. Singleton steps: only
    `EnvWfT.thm` / `EnvWfT.opaque` add such a member, and both store `some _`. Group steps add the
    family, the constructors and the recursor only (`hfam` / `hctors` / `hrec`). -/
theorem envWfT_rigid_hasBody {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ (r : Nat) (m : CheckedMember), E.members r = some m →
      (m.mclass = .theoremM ∨ m.mclass = .opaqueM) → m.body.isSome = true := by
  induction hW with
  | empty =>
      intro r m hm _
      simp [emptyEnv] at hm
  | «axiom» E r₀ A u _ _ _ _ _ ih =>
      intro r m hm hc
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        rcases hc with h | h <;> cases h
      · simp only [extendEnv, if_neg hr] at hm
        exact ih r m hm hc
  | definition E r₀ A v u _ _ _ _ _ _ _ _ ih =>
      intro r m hm hc
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        rcases hc with h | h <;> cases h
      · simp only [extendEnv, if_neg hr] at hm
        exact ih r m hm hc
  | thm E r₀ A p _ _ _ _ _ _ _ _ ih =>
      intro r m hm hc
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        rfl
      · simp only [extendEnv, if_neg hr] at hm
        exact ih r m hm hc
  | «opaque» E r₀ A v u _ _ _ _ _ _ _ _ ih =>
      intro r m hm hc
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        rfl
      · simp only [extendEnv, if_neg hr] at hm
        exact ih r m hm hc
  | group E f fm ctors rr rm E' _ hfam hctors hrec hmem ih =>
      intro r m hm hc
      rcases groupMembersT_mem_cases hmem hm with hin | hbase
      · exfalso
        have hcls : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
            m.mclass = .recursorM := by
          rcases List.mem_cons.mp hin with h | h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact Or.inl hfam
          · rcases List.mem_append.mp h with h | h
            · exact Or.inr (Or.inl (hctors (r, m) h))
            · simp only [List.mem_singleton, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              exact Or.inr (Or.inr hrec)
        rcases hc with h | h <;> rcases hcls with h' | h' | h' <;> rw [h] at h' <;> cases h'
      · exact ih r m hbase hc

/-- the body of a rigid member, with its admission typing: `HasTyT E 0 [] b m.mtype` (the stored
    form `EnvWfT.thm` / `EnvWfT.opaque` checks, read back by the sealed walk `envWfT_bodyTypedRaw`). -/
def envWfT_rigidBody {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hres : E.members r = some m) (hcls : m.mclass = .theoremM ∨ m.mclass = .opaqueM) :
    Σ' b : Expr Nat, (m.body = some b) ×' HasTyT E 0 [] b m.mtype := by
  cases hb : m.body with
  | none =>
      have h := envWfT_rigid_hasBody hW r m hres hcls
      rw [hb] at h
      exact absurd h (by decide)
  | some b => exact ⟨b, rfl, (envWfT_bodyTypedRaw hW r m b hres hb).1⟩

/-- theorem and opaque classes are not transparent. -/
theorem transparent_rigid {c : MemberClass} (hc : c = .theoremM ∨ c = .opaqueM) :
    transparent c = false := by
  rcases hc with rfl | rfl <;> rfl

/-! ## (2) the row -/

/-- EG-006 typed: in an `EnvWfT` environment, a theorem or opaque member's body is checked and
    stored (typed at the member's type at admission's judgment form), the δ-lookup returns no body
    at any level list, and the member's constant takes no one-step reduction. The third conjunct is
    the sealed `DT015T_rigidity`, applied. -/
theorem EG006T_theorem_opaque_rigidity {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hres : E.members r = some m)
    (hcls : m.mclass = .theoremM ∨ m.mclass = .opaqueM) :
    (∃ b, m.body = some b ∧ Nonempty (HasTyT E 0 [] b m.mtype)) ∧
    (∀ ls : List Level, transparentBody E r ls = none) ∧
    (∀ (n : Nat) (Γ : LCtx) (ls : List Level) (e' : Expr Nat),
      Step E n Γ (.const r ls) e' → False) := by
  have htr := transparent_rigid hcls
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb, ht⟩ := envWfT_rigidBody hW hres hcls
    exact ⟨b, hb, ⟨ht⟩⟩
  · intro ls
    simp only [transparentBody, hres, htr]
    rfl
  · intro n Γ ls e' hstep
    exact DT015T_rigidity hres htr hstep

/-! ## (3) pins at real fixtures -/

/-- the opaque fixture: `natEnvU` extended at ref 4 by an OPAQUE member with exactly the type and
    body of `pinDefEnvU`'s definition (`Sort 0 : Sort 1`). -/
def pinOpqEnvU : ResolvedEnv :=
  extendEnv natEnvU 4 ⟨.opaqueM, 0, .sort (.succ .zero), some (.sort .zero)⟩

/-- `EnvWfT pinOpqEnvU` — `EnvWfT.opaque` over `natEnvUWfT`, the same premises
    `pinDefEnvUWfT` hands `EnvWfT.definition`. -/
def pinOpqEnvUWfT : EnvWfT pinOpqEnvU :=
  EnvWfT.opaque natEnvU 4 (.sort (.succ .zero)) (.sort .zero)
    (.succ (.succ .zero)) natEnvUWfT pinDefEnvU_fresh
    (HasTyT.sort [] (.succ .zero)) (HasTyT.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- PIN (EG-006T, opaque): the row consumed at `pinOpqEnvU`'s ref 4. -/
theorem pin_EG006T_opqU :
    (∃ b, (⟨.opaqueM, 0, .sort (.succ .zero), some (.sort .zero)⟩ : CheckedMember).body = some b ∧
      Nonempty (HasTyT pinOpqEnvU 0 [] b (.sort (.succ .zero)))) ∧
    (∀ ls : List Level, transparentBody pinOpqEnvU 4 ls = none) ∧
    (∀ (n : Nat) (Γ : LCtx) (ls : List Level) (e' : Expr Nat),
      Step pinOpqEnvU n Γ (.const 4 ls) e' → False) :=
  EG006T_theorem_opaque_rigidity pinOpqEnvUWfT
    (m := ⟨.opaqueM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl (Or.inr rfl)

/-- PIN (the contrast): the SAME type and body as a DEFINITION at the same ref unfolds — the δ-lookup
    returns the body and `Step.delta` fires — while the opaque member does neither. Rigidity is the
    class, not the body. -/
theorem pin_EG006T_contrast_defU {n : Nat} {Γ : LCtx} :
    transparentBody pinDefEnvU 4 [] = some (.sort .zero) ∧
    Nonempty (Step pinDefEnvU n Γ (.const 4 []) (.sort .zero)) ∧
    transparentBody pinOpqEnvU 4 [] = none :=
  ⟨rfl,
   ⟨Step.delta Γ 4 [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ (.sort .zero)
     rfl rfl rfl⟩,
   rfl⟩

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

-- slot 153 of `srcEnvG` is `lt010 : Lt 0 10`, a theorem (kernel-checked lookup).
kernel_rfl_theorem srcEnvG_slot153 : srcEnvG.members 153 = some mLt010

/-- PIN (EG-006T, theorem): the row consumed at a real theorem of the 168-slot K3c environment,
    through the unconditional `envWfT_srcEnvG`. -/
theorem pin_EG006T_srcThm :
    (∃ b, mLt010.body = some b ∧ Nonempty (HasTyT srcEnvG 0 [] b mLt010.mtype)) ∧
    (∀ ls : List Level, transparentBody srcEnvG 153 ls = none) ∧
    (∀ (n : Nat) (Γ : LCtx) (ls : List Level) (e' : Expr Nat),
      Step srcEnvG n Γ (.const 153 ls) e' → False) :=
  EG006T_theorem_opaque_rigidity envWfT_srcEnvG srcEnvG_slot153 (Or.inl rfl)

end Rcic.Scm.SrcG

namespace Rcic.Declarative

/-! ## (4) GM-THEORY-004: the mutant transparency, and the machine as a second instrument -/

/-- GM-THEORY-004's mutant: theorem and opaque bodies δ-reduce. -/
def transparentG4 : MemberClass → Bool
  | .definitionM => true
  | .theoremM => true
  | .opaqueM => true
  | _ => false

/-- `transparentBody` read through the mutant transparency. -/
def transparentBodyG4 (E : ResolvedEnv) (r : Nat) (ls : List Level) : Option (Expr Nat) :=
  match E.members r with
  | some m =>
      if transparentG4 m.mclass then
        match m.body with
        | some b => some (instantiateLevels ls b)
        | none => none
      else none
  | none => none

/-- TOOTH (GM-THEORY-004, opaque): under the mutant the opaque member's body is returned, so the
    row's δ-lookup conjunct fails at `pinOpqEnvU`; the real lookup returns `none`. -/
theorem tooth_GM_THEORY_004_opq :
    transparentBodyG4 pinOpqEnvU 4 [] = some (.sort .zero) ∧
    transparentBody pinOpqEnvU 4 [] = none ∧
    ¬ (∀ ls : List Level, transparentBodyG4 pinOpqEnvU 4 ls = none) :=
  ⟨rfl, rfl, fun h => Option.noConfusion (h [])⟩

/-- the raw machine's `whnfAt` on the opaque constant at `pinOpqEnvU` — run, not assumed. -/
def pinWhnfOpqState : Rcic.Machine.RawState where
  ambient := ⟨pinOpqEnvU, 0, []⟩
  task := .whnfAt (.sort (.succ .zero)) (.const 4 [])
  budget := 2

/-- the same run on the definition at `pinDefEnvU`. -/
def pinWhnfDefState : Rcic.Machine.RawState where
  ambient := ⟨pinDefEnvU, 0, []⟩
  task := .whnfAt (.sort (.succ .zero)) (.const 4 [])
  budget := 2

/-- SECOND INSTRUMENT: the raw machine leaves the opaque constant in place and unfolds the
    definition with the same body, by evaluation. -/
theorem pin_EG006T_machine_opq_vs_def :
    Rcic.Machine.kernelStepRaw pinWhnfOpqState =
      .result (.accepted (.inferredWhnf (.sort (.succ .zero)) (.const 4 []))) ∧
    Rcic.Machine.kernelStepRaw pinWhnfDefState =
      .result (.accepted (.inferredWhnf (.sort (.succ .zero)) (.sort .zero))) :=
  ⟨rfl, rfl⟩

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

-- the mutant lookup returns slot 153's stored proof term (kernel-checked).
kernel_rfl_theorem srcThm153_G4 :
  transparentBodyG4 srcEnvG 153 [] = mLt010.body.map (instantiateLevels [])

-- the real lookup returns nothing at slot 153 (kernel-checked).
kernel_rfl_theorem srcThm153_real : transparentBody srcEnvG 153 [] = none

/-- TOOTH (GM-THEORY-004, theorem): at `srcEnvG`'s slot 153 the mutant returns the proof body, so the
    row's δ-lookup conjunct fails under it; the real lookup returns `none`. -/
theorem tooth_GM_THEORY_004_srcThm :
    (transparentBodyG4 srcEnvG 153 []).isSome = true ∧
    transparentBody srcEnvG 153 [] = none := by
  refine ⟨?_, srcThm153_real⟩
  rw [srcThm153_G4]
  rfl

/-- the raw machine's `whnfAt` on slot 153's constant. -/
def pinWhnfSrcThmState : Rcic.Machine.RawState where
  ambient := ⟨srcEnvG, 0, []⟩
  task := .whnfAt mLt010.mtype (.const 153 [])
  budget := 2

-- SECOND INSTRUMENT (theorem): the raw machine leaves slot 153's constant in place (kernel-checked
-- run).
kernel_rfl_theorem pin_EG006T_machine_srcThm :
  Rcic.Machine.kernelStepRaw pinWhnfSrcThmState =
    .result (.accepted (.inferredWhnf mLt010.mtype (.const 153 [])))

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.envWfT_rigid_hasBody
#print axioms Rcic.Declarative.envWfT_rigidBody
#print axioms Rcic.Declarative.transparent_rigid
#print axioms Rcic.Declarative.EG006T_theorem_opaque_rigidity
#print axioms Rcic.Declarative.pinOpqEnvUWfT
#print axioms Rcic.Declarative.pin_EG006T_opqU
#print axioms Rcic.Declarative.pin_EG006T_contrast_defU
#print axioms Rcic.Scm.SrcG.srcEnvG_slot153
#print axioms Rcic.Scm.SrcG.pin_EG006T_srcThm
#print axioms Rcic.Declarative.tooth_GM_THEORY_004_opq
#print axioms Rcic.Declarative.pin_EG006T_machine_opq_vs_def
#print axioms Rcic.Scm.SrcG.srcThm153_G4
#print axioms Rcic.Scm.SrcG.srcThm153_real
#print axioms Rcic.Scm.SrcG.tooth_GM_THEORY_004_srcThm
#print axioms Rcic.Scm.SrcG.pin_EG006T_machine_srcThm
