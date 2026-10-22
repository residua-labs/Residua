import rcic.RcicAnnLR3InductiveCodes

/-!
# Irrelevance throughout the positive relational grammar

An impredicative product at exact level zero has a level-zero codomain.
Induction on its code derivation therefore gives proof irrelevance in
every legal dependent fibre. This supplies the irrelevance port for the
new code system, rather than inheriting a port for the smaller grammar.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveIrrelevance

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

theorem imax_zero_right {u v : Option Nat} (h : imaxLevel u v = some 0) : v = some 0 := by
  cases u <;> cases v <;> simp_all [imaxLevel, eval]
  rename_i a b
  by_cases hb : b = 0
  · exact hb
  · have hle : b ≤ max a b := Nat.le_max_right a b
    rw [h hb] at hle
    exact Nat.eq_zero_of_le_zero hle

theorem code_irrelevant_at_zero {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeI k V R) : k = some 0 →
      ∀ {x y : Value}, Member R x → Member R y → R x y := by
  induction h with
  | old h =>
    intro hk x y hx hy
    cases hk
    exact NeutralCodes.code_prop_irrelevant h hx hy
  | nat hv hr =>
    intro hk
    cases hk
  | @pi kA kB A C V RA R RB hA hB hc hv hr ihA ihB =>
    intro hk x y hx hy
    have hkB : kB = some 0 := imax_zero_right hk
    apply (hr x y).mpr
    intro a b hab
    have ha := left_member (code_laws hA) hab
    have hb := right_member (code_laws hA) hab
    have hxa := ((hr x x).mp hx) a a ha
    have hyb := ((hr y y).mp hy) b b hb
    exact ihB a a ha hkB hxa ((hc a b hab _ _).mpr hyb)

def propIrrelevance : PropIrrelevance legacyUniverseSystem where
  relate := fun h hx hy => code_irrelevant_at_zero h rfl hx hy

/-- The nine previously supplied contracts remain supplied on the
larger code grammar and the same explicit evaluator. -/
theorem inherited_nine_arms (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Ty_conv (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_refl (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_symm (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_trans (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_sorts (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_tyConv (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_irr (FunctionEval.annSemantics legacyUniverseSystem) E I n ∧
    PairedArms.Conv_beta (FunctionEval.annSemantics legacyUniverseSystem) E I n :=
  ⟨PairedArms.ty_sort_supplied _ E I n,
    PairedArms.ty_conv_supplied _ E I n legacyUniverseTransport,
    PairedArms.conv_refl_supplied _ E I n,
    PairedArms.conv_symm_supplied _ E I n,
    PairedArms.conv_trans_supplied _ E I n,
    PairedArms.conv_sorts_supplied _ E I n,
    PairedArms.conv_tyConv_supplied _ E I n legacyUniverseTransport,
    PairedArms.conv_irr_supplied _ E I n propIrrelevance,
    FunctionEval.conv_beta_supplied legacyUniverseSystem E I n⟩

end Rcic.Declarative.Ann.LR3.InductiveIrrelevance
