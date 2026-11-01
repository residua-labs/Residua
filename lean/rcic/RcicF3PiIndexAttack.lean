import rcic.RcicF3PiIndex
import rcic.RcicF3PiPropPrefixAttack
import rcic.RcicF3PiIndependentAttack
/-! Quotient-label self-attacks: extensional proofs, distinct data, arity,
dependent prefixes, arbitrary labels and complete proof application. Typed
Acc normalization retains explicit environment obligations. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndexAttack
open Rcic.Declarative PiIndex
universe u

/-- Extensional proof aliases share a label without erasing plain data. -/
theorem alias_key :
    key ([PiPropPrefixAttack.alias, PiPropPrefixAttack.datum] : List PSet.{u}) =
      key [pempty, PiPropPrefixAttack.datum] := by
  exact (key_eq_iff _ _).mpr ⟨PiPropPrefixAttack.alias_equiv, Equiv.rfl, True.intro⟩

/-- Proof erasure cannot collapse a retained plain data index. -/
theorem data_key_refused :
    key ([pempty, PiPropPrefixAttack.datum] : List PSet.{u}) ≠ key [pempty, pempty] := by
  intro h
  exact dataVal_ne_pempty 7 [] ((key_eq_iff _ _).mp h).2.1

/-- The quotient also retains arity, including an extra empty proof argument. -/
theorem extra_argument_refused (xs : List PSet.{u}) : key xs ≠ key (pempty :: xs) := by
  intro h
  have hl := LEq.length ((key_eq_iff _ _).mp h)
  simp only [List.length_cons] at hl
  omega

/-- The actual dependent-prefix fixture transports every quotient result label,
while the complete label still distinguishes the plain datum from erasure. -/
theorem dependent_result (M : Interp.{u}) (f : Nat) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) (es : List (Expr Nat)) :
    read (PiPropPrefixAttack.model M f) σ es
      (push [PiPropPrefixAttack.alias, PiPropPrefixAttack.datum] ρ) =
    read (PiPropPrefixAttack.model M f) σ es
      (push [pempty, PiPropPrefixAttack.datum] ρ) ∧
      key ([pempty, PiPropPrefixAttack.datum] : List PSet.{u}) ≠ key [pempty, pempty] := by
  exact ⟨(key_eq_iff _ _).mpr ((PiPropPrefixAttack.dependent_tuple M f σ ρ).2 es),
    data_key_refused⟩


/-- Elementary depth-three readback and independence, for every numerical
family label including literal aliases 1 and 2. -/
theorem triple_labels (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (a b c : PSet.{4}) :
    read (mkM P μ) σ PiIndependentAttack.triArgs (vcons c (vcons b (vcons a ρ))) =
      key [a, b, c] ∧
    tel (mkM P (upd μ f X₁)) σ PiIndependentAttack.triDomains
      PiIndependentAttack.triArgs ρ =
    tel (mkM P (upd μ f X₂)) σ PiIndependentAttack.triDomains
      PiIndependentAttack.triArgs ρ := by
  exact ⟨rfl, rfl⟩

def argType : Expr Nat := policyPi [.bvar 0] (.sort .zero)
def assignment : Nat → PSet.{u} := fun _ => tyv PiPropPrefixAttack.domain
def value (M : Interp.{u}) (σ : Nat → Nat) : PSet.{u} :=
  piLam M σ (fun _ => PiPropPrefixAttack.proofTy) assignment argType

/-- A complete family application inhabits the quotient proof fibre. Its
proof-face premise is derived from application_empty, not supplied as a wall. -/
theorem complete_fibre (M : Interp.{u}) (σ : Nat → Nat) :
    Equiv (proofFibre M (value M σ) (key [PiPropPrefixAttack.datum]))
      (tv True) ∧
    pempty ∈ proofFibre M (value M σ) (key [PiPropPrefixAttack.datum]) := by
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have hg : EnvResp (fun _ : Nat → PSet.{u} => PiPropPrefixAttack.proofTy) :=
    fun _ _ _ => Equiv.rfl
  have hp : ∀ (ρ : Nat → PSet.{u}) z, z ∈ Ed M PiPropPrefixAttack.proofTy →
      Equiv z pempty := fun _ _ h => (mem_tv.mp
        (mem_congr_right (ed_tyv M (dich_tv True)) h)).2
  have hf : TelFits M σ [.bvar 0] assignment [PiPropPrefixAttack.datum] :=
    ⟨mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl), True.intro⟩
  have he := fapps_piLam M σ hg (.sort .zero) [.bvar 0] assignment
    [PiPropPrefixAttack.datum] hf
  have hx := proofFibre_key M (value M σ) [PiPropPrefixAttack.datum]
    (fun ys hys z hz => PiPropField.application_empty M σ _ hg hp [.bvar 0]
      assignment ys hys hz)
  have hEq := hx.trans ((ed_congr M he).trans (ed_tyv M (dich_tv True)))
  exact ⟨hEq, mem_congr_right hEq.symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)⟩

/-- The proof-fibre projection is refused on a data-valued leaf. This pins
why the complete proof face belongs in the comparison theorem. -/
theorem data_fibre_refused (M : Interp.{u}) :
    ¬ Equiv (proofFibre M (tyv PiPropPrefixAttack.domain) (key []))
      (Ed M (tyv PiPropPrefixAttack.domain)) := by
  intro h
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have hz : (PiPropPrefixAttack.datum : PSet.{u}) ∈ Ed M (tyv PiPropPrefixAttack.domain) :=
    mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl)
  exact dataVal_ne_pempty 7 [] (mem_tv.mp (mem_congr_right h.symm hz)).2

/-- Elementary composition at the actual typed Acc field and its beta/delta/let
presentations. Ordinary EnvSound, BodiesOK and the complete proof face remain
explicit; this does not construct the complete raw Acc group model. -/
theorem acc_fields (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ 10 X)) σ K PiSyntaxAttack.env 0)
    (hb : BodiesOK PiSyntaxAttack.env σ K)
    (hX : ∀ xs : List PSet.{4}, xs.length = 1 → ∀ z,
      z ∈ Ed (mkM P (upd μ 10 X)) (fapps (X []) xs) → Equiv z pempty)
    (ρ : Nat → PSet.{4}) :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    ∀ x, x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((tel (mkM P μ) σ RoleAttacks.accDomains [.bvar 1] ρ).erasedType
          (mkM P (upd μ 10 X)) (proofFibre (mkM P (upd μ 10 X)) (X []))) := by
  have hd : ∀ e ∈ RoleAttacks.accDomains, occursConst 10 e = false := by
    simp [RoleAttacks.accDomains, occursConst]
  have ha : ∀ e ∈ ([.bvar 1] : List (Expr Nat)), occursConst 10 e = false := by
    simp [occursConst]
  have go : ∀ T, piTelescopeFuel PiSyntaxAttack.env 64 T =
        some (RoleAttacks.accDomains, RoleAttacks.accResult) →
      InstOK PiSyntaxAttack.env σ K T → ∀ x,
      x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((tel (mkM P μ) σ RoleAttacks.accDomains [.bvar 1] ρ).erasedType
          (mkM P (upd μ 10 X)) (proofFibre (mkM P (upd μ 10 X)) (X []))) := by
    intro T hw hI x hx
    exact normalized_mem P μ 10 X σ K hE hb 64 T [] RoleAttacks.accDomains
      [.bvar 1] hw hI hd ha hX ρ x hx
  have hf := PiTypedCompileAttack.fieldBound σ K
  obtain ⟨hβ, _, hζ⟩ := PiTypedCompileAttack.presentationBounds σ K
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact go _ RoleAttacks.accRead (instOK_of_lokt σ 4 K PiSyntaxAttack.fieldTy hf)
  · exact go _ RoleAttacks.betaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.betaTyped
      ⟨⟨hβ.1, hβ.2.1⟩, hβ.2.2⟩)
  · exact go _ RoleAttacks.deltaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.deltaTyped
      ⟨(fun _ h => False.elim (List.not_mem_nil _ h)), hf⟩)
  · exact go _ RoleAttacks.zetaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.zetaTyped hζ)

end Rcic.F3.PSet.PiIndexAttack
