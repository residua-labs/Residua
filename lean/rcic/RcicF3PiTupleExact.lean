import rcic.RcicF3PiHereditaryEnv
import rcic.RcicF3PiRawCtor
import rcic.RcicF3DBoundBridge
/-! Bidirectional normalization of whole dependent constructor tuples,
from the original bounded typing. Universal group assembly remains unpaid.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiTupleExact
open Rcic.Declarative PiValueRule PiValueExtract

/-- Every tuple of the extracted constructor fits exactly when it fits the
original constructor. The tuple values and dependent environments are identical. -/
theorem fits_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n fuel f nu ar : Nat}
    (hE : EnvSound (mkM P μ) σ K E n) (hb : BodiesOK E σ K)
    (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E) :
    ∀ {As fs}, Views E fuel f nu ar As fs →
    ∀ {Γ : LCtx} {b : Expr Nat} {l : Level}
      (d : HasTyT E n Γ (policyPi As b) (.sort l)), LOKt σ 4 K d →
      ∀ ρ xs, Fits (mkM P μ) σ Γ ρ →
        (TelFits (mkM P μ) σ (fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs ↔
          TelFits (mkM P μ) σ As ρ xs) := by
  intro As fs hv
  induction hv with
  | nil =>
      intro Γ b l d hd ρ xs hρ
      rfl
  | @cons A a As rest hv ht ih =>
      intro Γ b l d hd ρ xs hρ
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
          change (_ ∧ _) ↔ (_ ∧ _)
          constructor
          · intro hx
            have hraw := mem_congr_right (ed_congr (mkM P μ) he) hx.1
            exact ⟨hraw, (ih dB hdB (vcons x ρ) xs ⟨hρ, hraw⟩).mp hx.2⟩
          · intro hx
            exact ⟨mem_congr_right (ed_congr (mkM P μ) he.symm) hx.1,
              (ih dB hdB (vcons x ρ) xs ⟨hρ, hx.1⟩).mpr hx.2⟩
/-- Ordinary stored body bounds and group-invariant components pay all
normalizer side conditions; there is no additional normalization wall. -/
theorem fits_iff_of_bound (P : Premises4)
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
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    TelFits (mkM P μ) σ (fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs ↔
      TelFits (mkM P μ) σ As ρ xs := by
  exact fits_iff P μ σ K hES
    (bodiesOK_of_envWfT K hW hB hsub hnew σ)
    (PiHereditary.bodiesRegular_of_bound P μ K hW hB hA hI hfin hsub hnew σ)
    hv d hd ρ xs hρ

/-- The positive proof-family predicate obeys an equation with the ORIGINAL
constructor fields. No already-normalized typing or normalized tuple is a premise. -/
theorem predicate_equation (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (raw : Fin cs.length → List (Expr Nat)) {E : ResolvedEnv} {n fuel : Nat}
    (hv : ∀ c, Views E fuel f vs.length famDs.length (raw c) (cs[c]).fields)
    (K : Nat → Nat)
    (hES : EnvSound (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hR : PiHereditary.BodiesRegular (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) K E)
    (ls : Fin cs.length → Level)
    (d : ∀ c, HasTyT E n [] (policyPi (raw c)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) (.sort (ls c)))
    (hd : ∀ c, LOKt (σOf vs) 4 K (d c)) (i : PiIndex.Index.{4}) :
    predicate P μ famDs cs vs i ↔ ∃ (c : Fin cs.length) (xs : List PSet.{4}),
      TelFits (mkM P (upd μ f (PiValue.table P μ
        (predicate P μ famDs cs) famDs))) (σOf vs) (raw c) ρ0 xs ∧
        PiIndex.read (mkM P μ) (σOf vs) (cs[c]).result (push xs ρ0) = i := by
  have he := PiValueRule.predicate_equation P μ f famDs cs vs (fun c => (hv c).clean) i
  have ht := fun c xs => fits_iff P _ (σOf vs) K hES hb hR (hv c) (d c) (hd c) ρ0 xs True.intro
  constructor
  · intro hi
    obtain ⟨c, xs, hx, hres⟩ := he.mp hi
    exact ⟨c, xs, (ht c xs).mp hx, hres⟩
  · rintro ⟨c, xs, hx, hres⟩
    exact he.mpr ⟨c, xs, (ht c xs).mpr hx, hres⟩
/-- Successful executable field admission, parameter-prefix scans and stored
bounded constructor typings produce the raw constructor equation. The body
conditions are derived from the ordinary prefix invariant, not assumed as walls.
This is a proof-family equation, not raw group or recursor soundness. -/
theorem admitted_predicate_equation (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (f : Nat) (famDs : List (Expr Nat))
    (cs : List Constructor) (vs : List Nat) (K : Nat → Nat)
    {E Efin E₁ : ResolvedEnv} (hW : EnvWfT E) (hB : BoundG K hW)
    (hA : AllSound P (upd μ f (PiValue.table P μ (predicate P μ famDs cs) famDs)) K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM →
      IotaAt P (upd μ f (PiValue.table P μ (predicate P μ famDs cs) famDs)) K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n fuel ni : Nat}
    (hES : EnvSound (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) K E₁ n)
    (Ps : List (Expr Nat)) (As : Fin cs.length → List (Expr Nat))
    (fs : Fin cs.length → List FieldSpec) (ss : Fin cs.length → List FieldShape)
    (hP : ∀ A ∈ Ps, occursConst f A = false)
    (ha : ∀ c, fieldShapesFuel E₁ fuel f vs.length Ps.length ni Ps.length (As c) = some (ss c))
    (har : Ps.length + ni = famDs.length)
    (hf : ∀ c, fields E₁ fuel f vs.length Ps.length ni Ps.length (As c) = some (fs c))
    (hc : ∀ c, (cs[c]).fields = Ps.map FieldSpec.plain ++ fs c)
    (ls : Fin cs.length → Level)
    (d : ∀ c, HasTyT E₁ n [] (policyPi (Ps ++ As c)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) (.sort (ls c)))
    (hd : ∀ c, LOKt (σOf vs) 4 K (d c)) (i : PiIndex.Index.{4}) :
    predicate P μ famDs cs vs i ↔ ∃ (c : Fin cs.length) (xs : List PSet.{4}),
      TelFits (mkM P (upd μ f (PiValue.table P μ
        (predicate P μ famDs cs) famDs))) (σOf vs) (Ps ++ As c) ρ0 xs ∧
        PiIndex.read (mkM P μ) (σOf vs) (cs[c]).result (push xs ρ0) = i := by
  have hv : ∀ c, Views E₁ fuel f vs.length famDs.length (Ps ++ As c) (cs[c]).fields := by
    intro c
    obtain ⟨fs', hfs', hv⟩ := fields_of_admitted (As c) Ps.length (ss c) (ha c) (Nat.le_refl _)
    have he : fs' = fs c := Option.some.inj (hfs'.symm.trans (hf c))
    rw [he] at hv
    have hp := PiRawCtor.prefix_views Ps hP hv
    rw [har] at hp
    rw [hc c]
    exact hp
  exact predicate_equation P μ f famDs cs vs (fun c => Ps ++ As c) hv K hES
    (bodiesOK_of_envWfT K hW hB hsub hnew (σOf vs))
    (PiHereditary.bodiesRegular_of_bound P _ K hW hB hA hI hfin hsub hnew (σOf vs))
    ls d hd i
end Rcic.F3.PSet.PiTupleExact
