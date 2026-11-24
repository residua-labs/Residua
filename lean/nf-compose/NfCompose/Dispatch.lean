import NfCompose.Bridge
import NfCompose.Sum
import algorithms.ResiduaConfluxMSTNFComposition

/-!
The existing tagged sum, read at the pinned definition.

`ProfileFamily.compositeProfile` is `StepExecModel.Profile` of `compositeModel`.
`compositeProfile_pinned` is that theorem transported by `profile_to_pinned`.
The hypothesis is agreement of each component's `active` flag with the image
of its `q`. `dispatch_q` and the four siblings are definitional: `toPinned` of
`compositeModel` is `sumModel` of the pinned components.
-/

namespace NfCompose

open MSTNecessityExecModelMWE
open Residua.Conflux.MSTNFComposition
open Residua.RCC.StepExecModel

def componentPinned (F : ProfileFamily) (k : ProfileKind) : ExecModel :=
  toPinned (ProfileFamily.componentModel F k)

theorem composite_active_agrees (F : ProfileFamily)
    (h : ∀ (k : ProfileKind) (c : F.Class k),
      F.active k c = true ↔ ∃ r : F.Raw k, F.q k r = c) :
    ActiveAgrees (ProfileFamily.compositeModel F) := by
  intro c
  rcases c with ⟨k, cls⟩
  constructor
  · intro ha
    rcases (h k cls).mp ha with ⟨r, hr⟩
    exact ⟨⟨k, r⟩, Sigma.ext rfl (heq_of_eq hr)⟩
  · rintro ⟨raw, hr⟩
    rcases raw with ⟨k', r⟩
    have hk : k' = k := congrArg Sigma.fst hr
    cases hk
    exact (h k cls).mpr ⟨r, sigma_eq_snd hr⟩

theorem compositeProfile_pinned (F : ProfileFamily)
    (h : ∀ (k : ProfileKind) (c : F.Class k),
      F.active k c = true ↔ ∃ r : F.Raw k, F.q k r = c) :
    hasMSTNFProfile (toPinned (ProfileFamily.compositeModel F)) :=
  profile_to_pinned (ProfileFamily.compositeProfile F) (composite_active_agrees F h)

theorem dispatch_q (F : ProfileFamily) (raw : (ProfileFamily.compositeModel F).Raw) :
    (toPinned (ProfileFamily.compositeModel F)).q raw =
      (sumModel (componentPinned F)).q raw := rfl

theorem dispatch_evalRaw (F : ProfileFamily) (raw : (ProfileFamily.compositeModel F).Raw) :
    (toPinned (ProfileFamily.compositeModel F)).evalRaw raw =
      (sumModel (componentPinned F)).evalRaw raw := rfl

theorem dispatch_evalClass (F : ProfileFamily) (cls : (ProfileFamily.compositeModel F).Class) :
    (toPinned (ProfileFamily.compositeModel F)).evalClass cls =
      (sumModel (componentPinned F)).evalClass cls := rfl

theorem dispatch_admissible (F : ProfileFamily) (cls : (ProfileFamily.compositeModel F).Class) :
    (toPinned (ProfileFamily.compositeModel F)).admissible cls =
      (sumModel (componentPinned F)).admissible cls := rfl

theorem dispatch_rho (F : ProfileFamily) (cls : (ProfileFamily.compositeModel F).Class) :
    (toPinned (ProfileFamily.compositeModel F)).rho cls =
      (sumModel (componentPinned F)).rho cls := rfl

theorem dispatch_sigma (F : ProfileFamily) (cls : (ProfileFamily.compositeModel F).Class) :
    (toPinned (ProfileFamily.compositeModel F)).sigma cls =
      (sumModel (componentPinned F)).sigma cls := rfl

end NfCompose
