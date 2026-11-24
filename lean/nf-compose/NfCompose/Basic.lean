import MSTNecessityExecModelMWE

/-!
Shared eliminators for the composition proofs.

`hasMSTNFProfile` is the pinned conjunction. `Parts` names its four conjuncts.
`Sigma.ext` / `Sigma.ext_iff` are the prelude extensionality lemmas for the
tagged sum. The `ext` tactic is not used: it can apply `funext`.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

structure Parts (M : ExecModel) where
  qf : quotientFactorization M
  sound : admissibilitySound M
  residue : residueTotality M
  rep : representativePrecision M

def parts {M : ExecModel} (h : hasMSTNFProfile M) : Parts M where
  qf := h.1
  sound := h.2.1
  residue := h.2.2.1
  rep := h.2.2.2

theorem parts_profile {M : ExecModel} (p : Parts M) : hasMSTNFProfile M :=
  ⟨p.qf, p.sound, p.residue, p.rep⟩

theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem sigma_eq_snd {α : Type} {β : α → Type} {i : α} {x y : β i}
    (h : (⟨i, x⟩ : Sigma β) = ⟨i, y⟩) : x = y := by
  have ⟨_, hs⟩ := Sigma.ext_iff.mp h
  exact eq_of_heq hs

theorem option_some_ne_none {α : Type} {a : α} : some a ≠ none := by
  intro h
  cases h

end NfCompose
