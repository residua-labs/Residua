import rcic.RcicEGTypedRigid
import rcic.RcicDTMetaTypedReg

/-!
# EG-007 typing half: checked bodies exactly bound (typed root)

04 §17 EG-007 "checked bodies exactly bound"; 00 F-04 class Q
(`docs/rcic/00_MASTER_CLOSURE_SPEC.md:3006` — "Q — EG-004, 005, 006, 010,
023 and EG-007's typing half"). The identity half is decided by
`apps/rcic-group-codec/APP.md` (:5, :85: `rcic_group_codec_identity_body`).

Class-Q statement: in an `EnvWfT E`, every member with a stored body is
typed at its member type —
`E.members r = some m → m.body = some b → Nonempty (HasTyT E 0 [] b m.mtype)`.
Definitions AND theorem/opaque in one statement: the sealed walk
`envWfT_bodyTypedRaw` (`RcicDTMetaTypedSR`) already traverses every
`EnvWfT` constructor — group members carry `body = none`, so the body
case is refuted on the group arm. `envWfT_rigidBody` (#6283, the EG-006
module) is that walk's rigid-class specialization; this file reuses the
walk, it does not re-prove it.

Tooth: an `extendEnv` literal whose stored body is not typed at its
member type (`.bvar 0` — DT-023T: untypable at every type in the empty
context) is `¬ EnvWfT`.

Pins at real fixtures: `pinDefEnvU`'s definition (ref 4) and `srcEnvG`'s
slot-153 theorem (`envWfT_srcEnvG`, `Rcic.Scm.SrcG`).

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-- EG-007 typed (F-04 class Q): in an `EnvWfT` environment, every member
    with a stored body is typed at its member type — admission's own
    judgment form (level context `0`, empty context). -/
theorem EG007T_checked_body_typed {E : ResolvedEnv} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hb : m.body = some b) :
    Nonempty (HasTyT E 0 [] b m.mtype) :=
  ⟨(envWfT_bodyTypedRaw hW r m b hres hb).1⟩

/-! ## tooth -/

/-- the tooth environment: `natEnvU` extended at ref 4 by a `definitionM`
    whose stored body `.bvar 0` is not typed at its member type
    (`DT023T_not_everything_typable`: `bvar 0` in the empty context is
    untypable at every type, in every environment). -/
def toothEnvU : ResolvedEnv :=
  extendEnv natEnvU 4 ⟨.definitionM, 0, .sort (.succ .zero), some (.bvar 0)⟩

/-- TOOTH (EG-007T): the malformed member makes the environment
    `¬ EnvWfT` — the well-formedness walk would produce a `bvar 0`
    typing that DT-023T refutes. -/
theorem tooth_EG007T_untyped_body : EnvWfT toothEnvU → False := fun hW =>
  DT023T_not_everything_typable
    ⟨.sort (.succ .zero),
     ⟨(envWfT_bodyTypedRaw hW 4
         ⟨.definitionM, 0, .sort (.succ .zero), some (.bvar 0)⟩ (.bvar 0)
         rfl rfl).1⟩⟩

/-! ## pins at real fixtures -/

/-- PIN (EG-007T, definition): `pinDefEnvU`'s `Sort 0 : Sort 1` definition
    member at ref 4. -/
theorem pin_EG007T_defU :
    Nonempty (HasTyT pinDefEnvU 0 [] (.sort .zero) (.sort (.succ .zero))) :=
  EG007T_checked_body_typed pinDefEnvUWfT (r := 4)
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

/-- PIN (EG-007T, theorem): slot 153 of `srcEnvG` — `lt010`'s stored proof
    body is typed at `Lt 0 10`, through the unconditional
    `envWfT_srcEnvG`. -/
theorem pin_EG007T_srcThm :
    ∃ b, mLt010.body = some b ∧
      Nonempty (HasTyT srcEnvG 0 [] b mLt010.mtype) :=
  ⟨_, rfl, EG007T_checked_body_typed envWfT_srcEnvG srcEnvG_slot153 rfl⟩

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.EG007T_checked_body_typed
#print axioms Rcic.Declarative.tooth_EG007T_untyped_body
#print axioms Rcic.Declarative.pin_EG007T_defU
#print axioms Rcic.Scm.SrcG.pin_EG007T_srcThm
