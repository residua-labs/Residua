import rcic.RcicF8JTransVia

/-!
JT-2 same-output adapters for the original J1/J3/J5a answers, following
ChatGPT's J-totality contract.  The certificate indices are the exact
materialized paths of the returned Valley, with the original literal as
caller.  The adapters add evidence to existing outputs; they do not run a
replacement producer or alter the structural demand domain.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JTotality
variable {E : ResolvedEnv} {n : Nat}

/-- Both step certificates refer to this exact returned Valley and original
literal.  Strict leaf support and answer availability are separate contracts. -/
structure SameOutputStepCertificates (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T)
    (V : Valley R Γ a b T) where
  leftTiles : J3.Certified R [.cv h]
    (V.left.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  rightTiles : J3.Certified R [.cv h]
    (V.right.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))

end Rcic.Declarative.F8Measure.JTotality

namespace Rcic.Declarative.F8Measure.J1
variable {E : ResolvedEnv} {n : Nat} {R X : List (Jd E n)}

/-- Convert the original J1 evidence without changing its indexed lazy star
or any emitted step.  Each tail uses the existing owner certificate for that
exact original producer; `J5a.baseCertificate_exact` identifies its owner tile.
This does not assert equality with the saved tile's status function. -/
def DirectTiles.toCertified {hcl : EnvClosed E} {hinst : EnvMembersSubstStable E}
    {Γ : LCtx} {a b T : Expr Nat} {ss : EvParStar R Γ a b T}
    (tiles : DirectTiles hcl hinst X ss) :
    J3.Certified R X (ss.val hcl hinst) :=
  match tiles with
  | .refl _ => PUnit.unit
  | .tail (s := s) _ _ _ rest =>
      ⟨J5a.baseCertificate hcl hinst X s, DirectTiles.toCertified rest⟩
termination_by structural tiles

/-- The first converted certificate is the existing owner tile for the exact
original emitted step, with the same caller X. -/
theorem DirectTiles.toCertified_tail_exact {hcl : EnvClosed E}
    {hinst : EnvMembersSubstStable E} {Γ : LCtx} {a b c T : Expr Nat}
    {s : EvPar R Γ a b T} {ss : EvParStar R Γ b c T}
    (tile : DTile R) (removed : tile.X = X)
    (exactStep : HEq tile.step (s.val hcl hinst))
    (rest : DirectTiles hcl hinst X ss) :
    ((DirectTiles.tail (s := s) tile removed exactStep rest).toCertified.1).tile =
      s.toDTile hcl hinst X := by
  simp only [DirectTiles.toCertified]
  exact J5a.baseCertificate_exact hcl hinst X s

/-- Certificates for the actual J1 result, retaining its original Valley. -/
def Result.sameOutput {hW : EnvWfT E} {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (out : Result hW R h) :
    JTotality.SameOutputStepCertificates hW R h out.valley where
  leftTiles := out.leftTiles.toCertified
  rightTiles := out.rightTiles.toCertified

end Rcic.Declarative.F8Measure.J1

namespace Rcic.Declarative.F8Measure.J3
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Projection of J3/J5a's certificates at the exact returned Valley. -/
def Result.sameOutput {hW : EnvWfT E} {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (out : Result hW R h) :
    JTotality.SameOutputStepCertificates hW R h out.valley where
  leftTiles := out.leftTiles
  rightTiles := out.rightTiles

end Rcic.Declarative.F8Measure.J3

namespace Rcic.Declarative.F8Measure.JTotality
variable {E : ResolvedEnv} {n : Nat}

/-- The original Via-trans dispatcher, forgetting only the certificate packet
after it has selected its actual returned Valley. -/
def j5aVia (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), JProcViaP R :=
  fun R {_ _ _ _} v h hs =>
    (J5aVia.dispatchVia hW su R v h hs).map (·.valley)

theorem j5aVia_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    JContractViaP (j5aVia hW su) := by
  intro R Γ a b T v h hs V hV
  have hV' : (J5aVia.dispatchVia hW su R v h hs).map (·.valley) = some V := hV
  obtain ⟨out, _, rfl⟩ := Option.map_eq_some'.mp hV'
  exact out.strict

/-- Equality of the complete projected Option output at the genuine Wf
restriction; no target-to-source well-formedness is inferred. -/
theorem j5aVia_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    j5aVia hW su R (.ofWf hΓ) h hs =
      (J5a.dispatchWf hW su R hΓ h hs).map (·.valley) := by
  unfold j5aVia
  rw [J5aVia.dispatchVia_ofWf]

theorem j1Via_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    j1Via hW R (.ofWf hΓ) h hs =
      (J1.dispatchWf hW R hΓ h hs).map (·.valley) := by
  unfold j1Via
  rw [J1.dispatchVia_ofWf]

theorem j3Via_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    j3Via hW R (.ofWf hΓ) h hs =
      (J3.dispatchWf hW R hΓ h hs).map (·.valley) := by
  unfold j3Via
  rw [J3.dispatchVia_ofWf]

end Rcic.Declarative.F8Measure.JTotality
