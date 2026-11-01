import rcic.RcicF3StepDGCheck
import rcic.RcicF3PropEvalTyped

/-!
# The all-Prop field bound excludes the admitted indexed AccP fixture

`accPIntroSafe` admits its first field because that field is a bare result
index. The field has domain `Sort 0`; it is not a proof field. The final
clause of `BoundG` nevertheless requests a uniformly-Prop typing of every
field of this Prop/anySort group. At this exact admitted fixture that asks
for a bounded typing of `Sort 0` in `Prop`.

The contradiction below uses a concrete sound model of the constructor-free
prefix only. The relation at 9 and the family at 10 are interpreted by
constant-false functions. No soundness of the completed AccP group, no
existence of Premises4, and no imported Acc environment is assumed.

This is a restriction of the soundness tier's bound, not a refutation of
the admitted AccP group or of Lean's singleton-elimination rule. The old
BoundG definition and the existing checked tier are unchanged.

Native verification: ROOT's pinned-toolchain run passed; all five printed
declarations use only propext and Quot.sound. This component has not been
added to an RCC descriptor.
closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.AccBoundScopeAttack

open Rcic.Declarative Rcic.Declarative.Ann Rcic.F3.StepDGCheck

/-- Only the relation and family occur in the exact constructor prefix. -/
theorem prefix_member_cases (r : Nat) (m : CheckedMember)
    (hm : accPFamEnvT.members r = some m) :
    (r = 10 ∧ m = accPFamT) ∨ (r = 9 ∧ m = paRelT) := by
  change (if r = 10 then some accPFamT else
    if r = 9 then some paRelT else none) = some m at hm
  by_cases h10 : r = 10
  · rw [if_pos h10] at hm
    exact Or.inl ⟨h10, (Option.some.inj hm).symm⟩
  · rw [if_neg h10] at hm
    by_cases h9 : r = 9
    · rw [if_pos h9] at hm
      exact Or.inr ⟨h9, (Option.some.inj hm).symm⟩
    · rw [if_neg h9] at hm
      cases hm

def zeroTable : Nat → List Nat → PSet.{4} := fun _ _ => pempty

/-- A concrete model of the prefix: both stored predicates are constantly false.
The temporary table is harmless because both stored types contain only sorts
and Pi binders, with no constant reads. -/
def prefixTable (P : Premises4) : Nat → List Nat → PSet.{4} :=
  fun r vs =>
    if r = 9 then
      piLam (mkM P zeroTable) (σOf vs) (fun _ => tyv pempty) ρ0 paRelT.mtype
    else if r = 10 then
      piLam (mkM P zeroTable) (σOf vs) (fun _ => tyv pempty) ρ0 accPFamT.mtype
    else pempty

theorem relation_value (P : Premises4) (vs : List Nat) :
    prefixTable P 9 vs = piLam (mkM P (prefixTable P)) (σOf vs)
      (fun _ => tyv pempty) ρ0 paRelT.mtype := rfl

theorem family_value (P : Premises4) (vs : List Nat) :
    prefixTable P 10 vs = piLam (mkM P (prefixTable P)) (σOf vs)
      (fun _ => tyv pempty) ρ0 accPFamT.mtype := rfl

theorem relation_sound (P : Premises4) (K : Nat → Nat) :
    MemberSound P (prefixTable P) K 9 paRelT := by
  refine memberSound_piLam (fun _ => rfl) rfl rfl
    (envResp_const (tyv pempty)) (relation_value P) ?_
  intro σ
  change PiGood (mkM P (prefixTable P)) σ (fun _ => tyv pempty) ρ0
    (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)))
  intro x _ y _
  exact tyv_pempty_mem_sort P (prefixTable P) σ (vcons y (vcons x ρ0)) .zero

theorem family_sound (P : Premises4) (K : Nat → Nat) :
    MemberSound P (prefixTable P) K 10 accPFamT := by
  refine memberSound_piLam (fun _ => rfl) rfl rfl
    (envResp_const (tyv pempty)) (family_value P) ?_
  intro σ
  change PiGood (mkM P (prefixTable P)) σ (fun _ => tyv pempty) ρ0
    (.pi (.sort .zero) (.sort .zero))
  intro x _
  exact tyv_pempty_mem_sort P (prefixTable P) σ (vcons x ρ0) .zero

theorem prefix_allSound (P : Premises4) (K : Nat → Nat) :
    AllSound P (prefixTable P) K accPFamEnvT := by
  intro r m hm
  rcases prefix_member_cases r m hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact family_sound P K
  · exact relation_sound P K

theorem prefix_no_constructor (r : Nat) (m : CheckedMember)
    (hm : accPFamEnvT.members r = some m) : m.mclass ≠ .constructorM := by
  rcases prefix_member_cases r m hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · decide
  · decide

/-- The prefix really is sound despite its explicit, interpreted relation axiom.
Its iota obligation is empty because no constructor is installed yet. -/
theorem prefix_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (prefixTable P)) σ K accPFamEnvT n where
  const := fun _ r ls m ρ hres hlen hl _ =>
    (prefix_allSound P K r m hres σ ls ρ hlen hl).1
  delta := fun _ r ls m b ρ hres hbody _ hlen hl _ =>
    (prefix_allSound P K r m hres σ ls ρ hlen hl).2 b hbody
  iota := by
    intro _ _ _ _ _ hι _ _ _ _ _ _ _ _
    cases hι with
    | of w => exact (prefix_no_constructor _ _ w.hctor w.hctorK).elim

/-- The universe of proposition codes is not itself a proposition code. -/
theorem prop_universe_not_prop (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) : tyv (U W4 0) ∉ U W4 0 := by
  intro hx
  have hy : tyv pempty ∈ Ed (mkM P μ) (tyv (U W4 0)) :=
    mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm
      (tyv_pempty_mem_U4 P 0)
  exact tyv_ne_pempty pempty (ed_of_mem_U0 (mkM P μ) hx hy)

/-- A bounded typing of `Sort 0` at a uniformly-Prop sort contradicts any
sound prefix. This uses the existing bounded soundness theorem directly. -/
theorem no_bounded_prop_sort (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K σ : Nat → Nat)
    {E : ResolvedEnv} {n : Nat}
    (hES : EnvSound (mkM P μ) σ K E n)
    (l : Level) (hl : UniformProp l)
    (d : HasTyT E n [] (.sort .zero) (.sort l)) (hd : LOKt σ 4 K d) : False := by
  have hs := sound_ty (P.good _ rfl) hES d hd ρ0 trivial
  change tyv (U W4 0) ∈ Ed (mkM P μ) (tyv (U W4 (evalTotal σ l))) at hs
  rw [hl σ] at hs
  exact prop_universe_not_prop P μ
    (mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)) hs)

/-- Choosing the first field of the actual AccP node exposes the literal
all-Prop obligation. The empty universe vector satisfies every K. -/
theorem boundG_index_obligation (K : Nat → Nat) (hB : BoundG K accPEnvWfT) :
    ∃ l : Level, UniformProp l ∧
      ∃ d : HasTyT accPFamEnvT 0 [] (.sort .zero) (.sort l),
        LOKt (fun _ => 0) 4 K d := by
  have h := hB.2.2.2 accPNode (fun _ => rfl) rfl
    ⟨0, by decide⟩ [] (fun _ hx => nomatch hx) ⟨0, by decide⟩
  change ∃ l : Level, UniformProp l ∧
    ∃ d : HasTyT accPFamEnvT 0 [] (.sort .zero) (.sort l),
      LOKt (fun _ => 0) 4 K d at h
  exact h

/-- The existing BoundG premise is unavailable at this admitted indexed AccP
fixture for every K, relative to the same supplied Premises4. -/
theorem boundG_refuted (P : Premises4) (K : Nat → Nat) :
    ¬ BoundG K accPEnvWfT := by
  intro hB
  obtain ⟨l, hl, d, hd⟩ := boundG_index_obligation K hB
  exact no_bounded_prop_sort P (prefixTable P) K (fun _ => 0)
    (prefix_sound P K (fun _ => 0) 0) l hl d hd

/-- Both the sound-prefix witness and the exact obstruction share P. -/
def Witness (P : Premises4) : Prop :=
  (∀ K σ n, EnvSound (mkM P (prefixTable P)) σ K accPFamEnvT n) ∧
  (∀ K, ¬ BoundG K accPEnvWfT)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨prefix_sound P, boundG_refuted P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.AccBoundScopeAttack

#print axioms Rcic.F3.PSet.AccBoundScopeAttack.prefix_sound
#print axioms Rcic.F3.PSet.AccBoundScopeAttack.boundG_index_obligation
#print axioms Rcic.F3.PSet.AccBoundScopeAttack.boundG_refuted
#print axioms Rcic.F3.PSet.AccBoundScopeAttack.component_witness
#print axioms Rcic.F3.PSet.AccBoundScopeAttack.component_nonrefutable
