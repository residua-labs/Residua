import rcic.RcicF3PiValue
import rcic.RcicF3PiIndexAttack
/-! Adversarial constructed-family applications: fitting and invalid arguments,
false fibres, typed hidden Acc fields, depth three and arbitrary references.
The Acc transport retains ordinary environment/body premises. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiValueAttack
open Rcic.Declarative PiIndex PiValue
universe u

def assignment : Nat → PSet.{u} := fun _ => tyv PiPropPrefixAttack.domain

/-- A fitting data argument enters the actual constructed family value. -/
theorem positive (M : Interp.{u}) (σ : Nat → Nat) :
    pempty ∈ Ed M (fapps (value M σ (fun _ => True) [.bvar 0] assignment)
      [PiPropPrefixAttack.datum]) := by
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have hf : TelFits M σ [.bvar 0] assignment [PiPropPrefixAttack.datum] :=
    ⟨mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl), True.intro⟩
  exact (apply_mem_iff M σ _ _ _ _ rfl _).mpr ⟨hf, True.intro, Equiv.rfl⟩
/-- Even the constant-True fibre does not admit an out-of-domain argument. -/
theorem invalid_refused (M : Interp.{u}) (σ : Nat → Nat) (z : PSet.{u}) :
    ¬ z ∈ Ed M (fapps (value M σ (fun _ => True) [.bvar 0] assignment)
      [dataVal 8 []]) := by
  intro hz
  have hf := ((apply_mem_iff M σ (fun _ => True) [.bvar 0] assignment
    [dataVal 8 []] rfl z).mp hz).1
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have he := mem_singleton.mp (mem_congr_right (ed_tyv M hd) hf.1)
  have htags : 8 = 7 := (dataVal_inj rfl he).1
  cases htags
/-- A false fibre stays empty even at fitting arguments. -/
theorem false_refused (M : Interp.{u}) (σ : Nat → Nat) (z : PSet.{u}) :
    ¬ z ∈ Ed M (fapps (value M σ (fun _ => False) [.bvar 0] assignment)
      [PiPropPrefixAttack.datum]) := by
  intro hz
  exact ((apply_mem_iff M σ (fun _ => False) [.bvar 0] assignment
    [PiPropPrefixAttack.datum] rfl z).mp hz).2.1
/-- The actual table derives the complete proof face for every typed Acc
presentation. EnvSound/BodiesOK are explicit; no raw Acc group is asserted. -/
theorem acc_fields (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (hfamily : famDs.length = 1) (σ K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ 10 (table P μ φ famDs))) σ K PiSyntaxAttack.env 0)
    (hb : BodiesOK PiSyntaxAttack.env σ K) (ρ : Nat → PSet.{4}) :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    ∀ x, x ∈ Ed (mkM P (upd μ 10 (table P μ φ famDs)))
      (den (mkM P (upd μ 10 (table P μ φ famDs))) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 (table P μ φ famDs)))
        ((tel (mkM P μ) σ RoleAttacks.accDomains [.bvar 1] ρ).erasedType
          (mkM P (upd μ 10 (table P μ φ famDs)))
          (proofFibre (mkM P (upd μ 10 (table P μ φ famDs))) (table P μ φ famDs []))) := by
  exact PiIndexAttack.acc_fields P μ (table P μ φ famDs) σ K hE hb
    (fun xs hx z hz => complete_empty (mkM P μ) (σOf []) (φ []) famDs ρ0 xs
      (hx.trans hfamily.symm) hz) ρ
/-- Three dependent binder positions retain the complete quotient label. -/
theorem depth_three (M : Interp.{u}) (σ : Nat → Nat) :
    pempty ∈ Ed M (fapps (value M σ
      (fun i => i = key [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum,
        PiPropPrefixAttack.datum]) [.bvar 0, .bvar 1, .bvar 2] assignment)
      [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]) := by
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have hm : PiPropPrefixAttack.datum ∈ Ed M (tyv PiPropPrefixAttack.domain) :=
    mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl)
  have hf : TelFits M σ [.bvar 0, .bvar 1, .bvar 2] assignment
      [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum] :=
    ⟨hm, hm, hm, True.intro⟩
  exact (apply_mem_iff M σ _ _ _ _ rfl _).mpr ⟨hf, rfl, Equiv.rfl⟩

/-- Literal candidate independence at every numeric family reference. -/
theorem relabel (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (φ : Index.{4} → Prop)
    (ρ : Nat → PSet.{4}) :
    value (mkM P (upd μ f X₁)) σ φ [.const (f + 1) []] ρ =
      value (mkM P (upd μ f X₂)) σ φ [.const (f + 1) []] ρ := by
  apply value_free
  intro A hA
  have he := List.mem_singleton.mp hA
  subst A
  have hn : f + 1 ≠ f := by omega
  simp [occursConst, hn]

end Rcic.F3.PSet.PiValueAttack
