import rcic.RcicF3PiLive
import rcic.RcicF3PiIndependentAttack
/-! Small-value/live-path attacks. Oversized fallback divergence is an
untyped counterexample; the actual Acc presentation helper keeps ordinary
environment soundness and context fitting explicit. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiLiveAttack
open Rcic.Declarative PiSmallCompile

theorem universe_not_small : ¬ Small.{3,4} univIn.{3,4} := by
  exact fun h => mem_irrefl univIn.{3,4} (mem_univIn.mpr h)
def largeDomain : PSet.{4} := singleton univIn.{3,4}
def leafData : PSet.{4} := singleton (tyv pempty)
def largeAssignment : Nat → PSet.{4}
  | 0 => tyv largeDomain
  | _ => tyv leafData

theorem large_domain_invariants : Dich largeDomain ∧ ¬ Small.{3,4} largeDomain := by
  constructor
  · apply Or.inr
    intro h
    have e := (mem_singleton.mp h).symm
    exact not_mem_pempty (mem_congr_right e (mem_univIn.mpr small_pempty))
  · intro h
    exact universe_not_small (small_of_mem_small h (mem_singleton.mpr Equiv.rfl))
/-- An untyped oversized domain refutes unconditional reverse fidelity. -/
theorem fallback_false_positive (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) :
    pempty ∈ Ed (mkM P μ) ((widen (compile P μ σ (fun _ => PUnit.unit)
      [.bvar 0] largeAssignment)).erasedType (mkM P μ) (fun _ => leafData)) ∧
    pempty ∉ Ed (mkM P μ) (den (mkM P μ) σ largeAssignment
      (policyPi [.bvar 0] (.bvar 2))) := by
  let M := mkM P μ
  have eD : Equiv (Ed M (tyv largeDomain)) largeDomain := ed_tyv M large_domain_invariants.1
  have hSmall : ¬ Small.{3,4} (Ed M (tyv largeDomain)) :=
    fun h => large_domain_invariants.2 (Small.congr eD h)
  have eS : rep P (Ed M (tyv largeDomain)) = pempty := by
    unfold rep
    rw [dif_neg hSmall]
  constructor
  · simp only [compile, den, largeAssignment, eS, widen, RecTel.erasedType]
    rw [eS]
    have e0 : Equiv (Ed M (tyv (lift.{3,4} pempty))) pempty :=
      (ed_tyv M (Or.inr (fun h => not_mem_pempty (mem_congr_right lift_pempty_equiv h)))).trans
        lift_pempty_equiv
    have hnone : ∀ a, a ∈ Ed M (tyv (lift.{3,4} pempty)) → False :=
      fun _ ha => not_mem_pempty (mem_congr_right e0 ha)
    let C := fun a => tyv (classFiber (lift.{3,4} pempty)
      (fun _ => Ed M (tyv leafData)) a)
    change pempty ∈ Ed M (piVal M (tyv (lift.{3,4} pempty)) C)
    have hP : PiProp M (tyv (lift.{3,4} pempty)) C := fun a ha => (hnone a ha).elim
    have et := ed_piVal M (tyv (lift.{3,4} pempty)) C
      (fun _ _ h => tyv_congr (classFiber_congr _ _ h))
    rw [cond_pos hP] at et
    exact mem_congr_right et.symm (mem_tv.mpr ⟨fun a ha => (hnone a ha).elim, Equiv.rfl⟩)
  · intro hf
    change pempty ∈ Ed M (piVal M (tyv largeDomain) (fun _ => tyv leafData)) at hf
    have ha : univIn.{3,4} ∈ Ed M (tyv largeDomain) :=
      mem_congr_right eD.symm (mem_singleton.mpr Equiv.rfl)
    have hm := app_mem M (B := fun _ => tyv leafData) (fun _ _ _ => Equiv.rfl) hf ha
    have hz : pempty ∈ leafData := mem_congr_right
      (ed_tyv M (Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm)))
      (mem_congr_left (fapp_pempty _) hm)
    exact tyv_ne_pempty _ (mem_singleton.mp hz).symm
def deadAssignment : Nat → PSet.{4}
  | 0 => tyv largeDomain
  | _ => tyv pempty
/-- A genuine oversized dead branch is retained, rather than refused. -/
theorem oversized_dead_live (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) :
    PiLive.LiveSmall (mkM P μ) σ [.bvar 0, .bvar 2] deadAssignment ∧
    ¬ DomainsSmall (PiSyntaxCompile.compile (mkM P μ) σ (fun _ => PUnit.unit)
      [.bvar 0, .bvar 2] deadAssignment) := by
  let M := mkM P μ
  have e0 : Equiv (Ed M (tyv pempty)) pempty := ed_tyv M (Or.inr not_mem_pempty)
  have hnone : ∀ a b, b ∈ Ed M (den M σ (vcons a deadAssignment) (.bvar 2)) → False :=
    fun _ _ hb => not_mem_pempty (mem_congr_right e0 hb)
  constructor
  · refine ⟨?_, fun a _ => ⟨?_, fun b hb => (hnone a b hb).elim⟩⟩
    · rintro ⟨a, _, b, hb, _⟩
      exact (hnone a b hb).elim
    · rintro ⟨b, hb, _⟩
      exact (hnone a b hb).elim
  · intro h
    exact large_domain_invariants.2 (Small.congr
      (ed_tyv M large_domain_invariants.1) h.1)
/-- An actual erased field enters the small independent signature at every
numeric family reference, including the literal aliases. -/
theorem empty_small (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (σ : Nat → Nat) :
    let X : List Nat → PSet.{4} := fun _ => tyv PiErasureAttack.domain
    let M := mkM P (upd μ f X)
    pempty ∈ Ed M ((widen (PiIndependent.recursiveTel P μ σ
      PiNormalizeAttack.emptyDomains [] PiIndependentAttack.emptyAssignment)).erasedType M
      (fun xs => Ed M (fapps (X []) xs))) := by
  dsimp only
  let X : List Nat → PSet.{4} := fun _ => tyv PiErasureAttack.domain
  let M := mkM P (upd μ f X)
  have hx : pempty ∈ Ed M (den M σ PiIndependentAttack.emptyAssignment
      (PiIndependentAttack.emptyType f)) := by
    change pempty ∈ Ed M (piVal M (tyv PiErasureAttack.domain) (fun _ =>
      piVal M (tyv pempty) (fun _ => (upd μ f X) f [])))
    rw [upd_eq]
    exact (PiErasureAttack.nested_empty_domain.{4,4} M).1
  have hd : ∀ e ∈ PiNormalizeAttack.emptyDomains, occursConst f e = false := by
    simp [PiNormalizeAttack.emptyDomains, occursConst]
  have hm := PiSmallValue.compile_mem P (upd μ f X) σ (PiIndependent.leafArgs P μ σ [])
    (fun xs => Ed M (fapps (X []) xs)) (fun _ => dich_ed M _)
    (.const f []) (fun ρ' => by
      change Equiv (Ed M (X [])) (Ed M ((upd μ f X) f []))
      rw [upd_eq]; exact Equiv.rfl)
    PiNormalizeAttack.emptyDomains PiIndependentAttack.emptyAssignment pempty small_pempty hx
  have he := PiIndependent.smallCompile_free P μ f X (μ f) σ
    (PiIndependent.leafArgs P μ σ []) PiNormalizeAttack.emptyDomains
    PiIndependentAttack.emptyAssignment hd
  rw [PiIndependent.upd_self] at he
  rw [he] at hm
  exact hm
/-- The actual typed Acc field and all hidden presentations enter the small
signature. This remains conditional on ordinary environment soundness and
context fitting, rather than claiming a model of the complete Acc group. -/
theorem acc_small_fields (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ 10 X)) σ K PiSyntaxAttack.env 0)
    (hb : BodiesOK PiSyntaxAttack.env σ K) (ρ : Nat → PSet.{4})
    (hρ : Fits (mkM P (upd μ 10 X)) σ PiSyntaxAttack.ctx ρ) :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    ∀ x, x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((widen (PiIndependent.recursiveTel P μ σ RoleAttacks.accDomains
          [.bvar 1] ρ)).erasedType (mkM P (upd μ 10 X))
          (fun xs => Ed (mkM P (upd μ 10 X)) (fapps (X []) xs))) := by
  have hd : ∀ e ∈ RoleAttacks.accDomains, occursConst 10 e = false := by
    simp [RoleAttacks.accDomains, occursConst]
  have ha : ∀ e ∈ ([.bvar 1] : List (Expr Nat)), occursConst 10 e = false := by
    simp [occursConst]
  have go : ∀ {T : Expr Nat} {l : Level},
      (d : HasTyT PiSyntaxAttack.env 0 PiSyntaxAttack.ctx T (.sort l)) →
      LOKt σ 4 K d → piTelescopeFuel PiSyntaxAttack.env 64 T =
        some (RoleAttacks.accDomains, RoleAttacks.accResult) → ∀ x,
      x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((widen (PiIndependent.recursiveTel P μ σ RoleAttacks.accDomains
          [.bvar 1] ρ)).erasedType (mkM P (upd μ 10 X))
          (fun xs => Ed (mkM P (upd μ 10 X)) (fapps (X []) xs))) := by
    intro T l d hd' hw x hx
    exact PiSmallValue.normalized_mem P μ 10 X σ K hE hb 64 T [] RoleAttacks.accDomains
      [.bvar 1] hw (instOK_of_lokt σ 4 K d hd') hd ha ρ x
      (PiSmallValue.typed_value_small P (upd μ 10 X) σ K hE d hd' ρ hρ hx) hx
  have hf := PiTypedCompileAttack.fieldBound σ K
  obtain ⟨hβ, _, hζ⟩ := PiTypedCompileAttack.presentationBounds σ K
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact go PiSyntaxAttack.fieldTy hf RoleAttacks.accRead
  · exact go PiSyntaxAttack.betaTyped ⟨⟨hβ.1, hβ.2.1⟩, hβ.2.2⟩ RoleAttacks.betaRead
  · exact go PiSyntaxAttack.deltaTyped
      ⟨(fun _ h => False.elim (List.not_mem_nil _ h)), hf⟩ RoleAttacks.deltaRead
  · exact go PiSyntaxAttack.zetaTyped hζ RoleAttacks.zetaRead
end Rcic.F3.PSet.PiLiveAttack
