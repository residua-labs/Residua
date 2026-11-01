import rcic.RcicF3PiTupleExact
/-! Original typed constructor fields preserve their stage bounds under
admitted normalization. The dependent tuple and every local value are
retained. This is a syntax bridge, not universal A production. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiTupleExact
open Rcic.Declarative PiValueRule PiValueExtract
 theorem smallAlong_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n fuel f nu ar : Nat}
    (hE : EnvSound (mkM P μ) σ K E n) (hb : BodiesOK E σ K)
    (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E) (W : PSet.{4}) :
    ∀ {As fs}, Views E fuel f nu ar As fs →
    ∀ {Γ : LCtx} {b : Expr Nat} {l : Level}
      (d : HasTyT E n Γ (policyPi As b) (.sort l)), LOKt σ 4 K d →
      ∀ ρ xs, Fits (mkM P μ) σ Γ ρ → TelFits (mkM P μ) σ As ρ xs →
        (SmallAlong (mkM P μ) σ W
          (fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs ↔
          SmallAlong (mkM P μ) σ W As ρ xs) := by
  intro As fs hv
  induction hv with
  | nil => intro Γ b l d hd ρ xs hρ hx; rfl
  | @cons A a As rest hv ht ih =>
    intro Γ b l d hd ρ xs hρ hx
    obtain ⟨u, v, dA, dB, hdA, hdB⟩ := pi_inv_lokt σ 4 K d hd
    have he : Equiv (den (mkM P μ) σ ρ
        (fieldExpr f ((List.range nu).map Level.param) a))
        (den (mkM P μ) σ ρ A) := by
      cases a with
      | plain B =>
        change Equiv (den (mkM P μ) σ ρ B) (den (mkM P μ) σ ρ A)
        rw [hv.1]
        exact Equiv.rfl
      | recursive ds args =>
        exact PiHereditary.den_piTelescope_typed4 P μ σ K hE hb hR dA hdA hv.1 ρ hρ
    cases xs with
    | nil => exact Iff.rfl
    | cons x xs =>
      have hi := ih dB hdB (vcons x ρ) xs ⟨hρ, hx.1⟩ hx.2
      exact ⟨fun hs => ⟨mem_congr_left (ed_congr (mkM P μ) he) hs.1, hi.mp hs.2⟩,
        fun hs => ⟨mem_congr_left (ed_congr (mkM P μ) he.symm) hs.1, hi.mpr hs.2⟩⟩
/-- Stored prefix soundness and bounds pay both normalizer body conditions.
This wrapper is elementary composition of the normalization bridge. -/
 theorem smallAlong_iff_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n fuel f nu ar : Nat} (hES : EnvSound (mkM P μ) σ K E₁ n)
    {As : List (Expr Nat)} {fs : List FieldSpec} (hv : Views E₁ fuel f nu ar As fs)
    {Γ : LCtx} {b : Expr Nat} {l : Level}
    (d : HasTyT E₁ n Γ (policyPi As b) (.sort l)) (hd : LOKt σ 4 K d)
    (W : PSet.{4}) (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hρ : Fits (mkM P μ) σ Γ ρ) (hx : TelFits (mkM P μ) σ As ρ xs) :
    SmallAlong (mkM P μ) σ W
      (fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs ↔
      SmallAlong (mkM P μ) σ W As ρ xs := by
  exact smallAlong_iff P μ σ K hES
    (bodiesOK_of_envWfT K hW hB hsub hnew σ)
    (PiHereditary.bodiesRegular_of_bound P μ K hW hB hA hI hfin hsub hnew σ)
    W hv d hd ρ xs hρ hx
end Rcic.F3.PSet.PiTupleExact
