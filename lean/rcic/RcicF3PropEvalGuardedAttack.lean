import rcic.RcicF3PropEvalGuarded
import rcic.RcicF3PropEvalUniqueAttack

/-!
# Actual AccR guarded result typing with the extra motive universe

The installed constructor, fitting empty index list, actual typed motive
and produced evaluation pay the guarded bridge. Family arity is zero while
the motive universe is one. The selected proof fibre is inhabited, and
the result is typed at every equivalent proof major in that fibre.
This is a local component witness; universal constructor/index production
and evaluation existence remain open. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalGuardedAttack
open Rcic.Declarative PiIndex PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

noncomputable def target (P : Premises4) (i : Index.{4}) (x : PSet.{4}) : PSet.{4} :=
  PiRawMotiveAny.guarded (ctx P).M (ctx P).σ 1 ((ctx P).M.μ 0 [])
    (ctx P).motive (ctx P).parameters [] (push (ctx P).parameters ρ0) i x

theorem constructor_empty (P : Premises4)
    (j : Fin (ctx P).node.a.constructors.length) (ps xs : List PSet.{4}) :
    Equiv ((ctx P).constructorAt j ps xs) pempty := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  exact (fapps_congr (installed_constructor P) (ps ++ xs)).trans (fapps_pempty _)

theorem indices_fit (P : Premises4)
    (j : Fin (ctx P).node.a.constructors.length) (ps xs : List PSet.{4}) :
    TelFits (ctx P).M (ctx P).σ (ctx P).node.a.family.indices (push ps ρ0)
      ((ctx P).indicesAt j ps xs) := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  exact True.intro

/-- The actual stored constructor enters the family at every equivalent fixed parameter tuple. -/
theorem constructor_mem (P : Premises4)
    (j : Fin (ctx P).node.a.constructors.length) (ps xs : List PSet.{4})
    (hp : LEq ps (ctx P).parameters) :
    (ctx P).constructorAt j ps xs ∈ Ed (ctx P).M
      (fapps ((ctx P).M.μ (ctx P).node.a.family.ref
        ((policyFamilyLevels (ctx P).node.a.family).map (evalTotal (ctx P).σ)))
        (ps ++ (ctx P).indicesAt j ps xs)) := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  let M := (ctx P).M
  have hm : pempty ∈ Ed M (fapps (M.μ 0 []) ps) :=
    mem_congr_right (ed_congr M (fapps_congr_args (M.μ 0 []) hp)).symm
      (major_mem P (installed P) (installed_family P))
  change (ctx P).constructorAt ⟨0, _⟩ ps xs ∈ Ed M (fapps (M.μ 0 []) (ps ++ []))
  rw [List.append_nil]
  exact mem_congr_left (constructor_empty P ⟨0, by change 0 < 1; decide⟩ ps xs).symm hm

/-- The existing canonical evaluation has the actual guarded motive type. -/
theorem canonical_guarded (P : Premises4) :
    PropEvalAttack.canonical P ∈ target P (key [parameter]) pempty := by
  exact ((PropEvalAttack.canonical_spec P).2).mem_guarded (.param 0) rfl
    (motive_mem P (installed P))
    (fun j ps xs _ _ _ => indices_fit P j ps xs)
    (fun j ps xs hp _ _ => constructor_mem P j ps xs hp)
    (fun j ps xs _ _ _ => constructor_empty P j ps xs)

/-- The proof fibre used by the builder is inhabited at the selected full key. -/
theorem source_inhabited (P : Premises4) :
    pempty ∈ proofFibre (ctx P).M ((ctx P).M.μ 0 []) (key [parameter]) :=
  mem_tv.mpr ⟨⟨[parameter], rfl, major_mem P (installed P) (installed_family P)⟩, Equiv.rfl⟩

/-- Proof-major congruence pays the builder's arbitrary proof-fibre member. -/
theorem canonical_at_proof (P : Premises4) (x : PSet.{4})
    (hx : x ∈ proofFibre (ctx P).M ((ctx P).M.μ 0 []) (key [parameter])) :
    PropEvalAttack.canonical P ∈ target P (key [parameter]) x :=
  PropEval.guarded_mem_at_proof (ctx P).M (ctx P).σ 1 ((ctx P).M.μ 0 [])
    (ctx P).motive (ctx P).parameters [] (push (ctx P).parameters ρ0)
    (key [parameter]) x (PropEvalAttack.canonical P) hx (canonical_guarded P)

def Witness (P : Premises4) : Prop :=
  (ctx P).node.a.family.member.arity = 0 ∧ (ctx P).σ 0 = 1 ∧
  pempty ∈ proofFibre (ctx P).M ((ctx P).M.μ 0 []) (key [parameter]) ∧
  PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) ∧
  (∀ x, x ∈ proofFibre (ctx P).M ((ctx P).M.μ 0 []) (key [parameter]) →
    PropEvalAttack.canonical P ∈ target P (key [parameter]) x) ∧
  ¬ Equiv (PropEvalAttack.canonical P) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨rfl, rfl, source_inhabited P, (PropEvalAttack.canonical_spec P).2,
    canonical_at_proof P, (PropEvalAttack.component_witness P).2.2⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalGuardedAttack
