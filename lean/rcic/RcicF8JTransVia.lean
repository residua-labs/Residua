import rcic.RcicF8DProofVia

/-!
J5a under CtxWfVia.  The independent input grammar is the landed J5a grammar.
The trans case calls the ONE source-premise D object through its retained
weakening interface. DProofVia proves correspondence to the actual target run.
Every source closing step receives a fresh certificate for its exact read step.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J5aVia
open J3
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
variable {Γ : LCtx} {a b c T : Expr Nat}
variable {h₁ : ConvT E n Γ a b T} {h₂ : ConvT E n Γ b c T}

/-- The proof-index property is derived along the recursion, never a caller's
back-transportability premise. -/
structure FragmentResult (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T) where
  result : Result hW R h
  only : J5aProofOnly.valleyPI result.valley

def callD (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfVia E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) :=
  DProofVia.dProc hW su v p₁.result.valley.right p₂.result.valley.left
    p₁.only.2 p₂.only.1

def transValley (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfVia E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) : Valley R Γ a c T :=
  let k := (callD hW su v p₁ p₂).out
  { N := k.1
    left := .trans p₁.result.valley.left (J5a.readOutput k.2.1)
    right := .trans p₂.result.valley.right (J5a.readOutput k.2.2)
    ty₁ := p₁.result.valley.ty₁
    ty₂ := p₂.result.valley.ty₂ }

theorem closing_strict (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfVia E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) :
    ∀ l ∈ (J5a.readOutput (callD hW su v p₁ p₂).out.2.1).leaves ++
      (J5a.readOutput (callD hW su v p₁ p₂).out.2.2).leaves,
      SubOf l (.cv (.trans Γ a b c T h₁ h₂)) := by
  intro l hl
  have hd : l ∈ (callD hW su v p₁ p₂).out.2.1.leaves ++
      (callD hW su v p₁ p₂).out.2.2.leaves := by
    rcases List.mem_append.mp hl with h | h
    · exact List.mem_append.mpr (.inl (J5a.readOutput_leaves _ l h))
    · exact List.mem_append.mpr (.inr (J5a.readOutput_leaves _ l h))
  obtain ⟨k, hk, hs⟩ := (callD hW su v p₁ p₂).sound l hd
  exact subEq_trans_subOf hs (J5a.middle_strict p₁.result p₂.result k hk)

theorem transValley_strict (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfVia E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) :
    ∀ l ∈ (transValley hW su v p₁ p₂).leaves,
      SubOf l (.cv (.trans Γ a b c T h₁ h₂)) := by
  intro l hl
  simp only [transValley, Valley.leaves, EvParStar.leaves, List.mem_append] at hl
  rcases hl with (((hL | hDL) | (hR | hDR)) | hT₁) | hT₂
  · apply J5a.left_child_support p₁.result l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inl hL))
  · exact closing_strict hW su v p₁ p₂ l (List.mem_append.mpr (.inl hDL))
  · apply J5a.right_child_support p₂.result l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inr hR))
  · exact closing_strict hW su v p₁ p₂ l (List.mem_append.mpr (.inr hDR))
  · apply J5a.left_child_support p₁.result l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inr hT₁)
  · apply J5a.right_child_support p₂.result l
    simp only [Valley.leaves, List.mem_append]
    exact .inr hT₂

def transResult (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfVia E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) :
    FragmentResult hW R (.trans Γ a b c T h₁ h₂) where
  result := {
    valley := transValley hW su v p₁ p₂
    leftTiles := J5a.certifiedSplice _ _
      (Certified.recaller (callerOfChild
        (y := .cv (.trans Γ a b c T h₁ h₂)) (.head _)) _ p₁.result.leftTiles)
      (J5a.readOutput_certified (envClosed_of_envWfT hW)
        (envMembersSubstStable_of_envWfT hW) [.cv (.trans Γ a b c T h₁ h₂)]
        (callD hW su v p₁ p₂).out.2.1)
    rightTiles := J5a.certifiedSplice _ _
      (Certified.recaller (callerOfChild
        (y := .cv (.trans Γ a b c T h₁ h₂)) (.tail _ (.head _))) _ p₂.result.rightTiles)
      (J5a.readOutput_certified (envClosed_of_envWfT hW)
        (envMembersSubstStable_of_envWfT hW) [.cv (.trans Γ a b c T h₁ h₂)]
        (callD hW su v p₁ p₂).out.2.2)
    strict := transValley_strict hW su v p₁ p₂ }
  only := by
    have hd := (callD hW su v p₁ p₂).pi
    exact ⟨⟨p₁.only.1, J5aProofOnly.readOutput _ hd.1⟩,
      ⟨p₂.only.2, J5aProofOnly.readOutput _ hd.2⟩⟩

/-- The Via recursion uses exactly the original five-constructor fragment. -/
def build (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (v : CtxWfVia E n Γ) →
    (h : ConvT E n Γ a b T) → J5a.fragment h = true →
    (∃ r ∈ R, SubEq (.cv h) r) → FragmentResult hW R h
  | _, _, _, _, _, .refl _ _ _ ha, _, hs =>
      ⟨reflResult hW ha hs, True.intro, True.intro⟩
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, _, hs =>
      ⟨irrResult hW hP hp hq hs, ⟨True.intro, True.intro⟩, True.intro⟩
  | Γ, _, _, _, v, .symm _ a b T h, hf, hs =>
      let p := build hW su R v h hf
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      ⟨p.result.swap, p.only.2, p.only.1⟩
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hf, hs =>
      let p := build hW su R v h hf
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      ⟨p.result.reindex u hT hs, p.only⟩
  | Γ, _, _, _, v, .trans _ a b c T h₁ h₂, hf, hs =>
      transResult hW su v
        (build hW su R v h₁ (Bool.and_eq_true_iff.mp hf).1
          (certOfChild (y := .cv (.trans Γ a b c T h₁ h₂)) (.head _) hs))
        (build hW su R v h₂ (Bool.and_eq_true_iff.mp hf).2
          (certOfChild (y := .cv (.trans Γ a b c T h₁ h₂)) (.tail _ (.head _)) hs))
  | _, _, _, _, _, .beta .., hf, _ => by cases hf
  | _, _, _, _, _, .zeta .., hf, _ => by cases hf
  | _, _, _, _, _, .zetaLocal .., hf, _ => by cases hf
  | _, _, _, _, _, .delta .., hf, _ => by cases hf
  | _, _, _, _, _, .iota .., hf, _ => by cases hf
  | _, _, _, _, _, .lit .., hf, _ => by cases hf
  | _, _, _, _, _, .app .., hf, _ => by cases hf
  | _, _, _, _, _, .lam .., hf, _ => by cases hf
  | _, _, _, _, _, .pi .., hf, _ => by cases hf
  | _, _, _, _, _, .letE .., hf, _ => by cases hf
  | _, _, _, _, _, .sorts .., hf, _ => by cases hf
  | _, _, _, _, _, .consts .., hf, _ => by cases hf
  | _, _, _, _, _, .eta .., hf, _ => by cases hf

def buildFragment (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hf : J5a.fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) : Result hW R h :=
  (build hW su R v h hf hs).result

theorem transResult_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : FragmentResult hW R h₁)
    (p₂ : FragmentResult hW R h₂) :
    (transResult hW su (.ofWf hΓ) p₁ p₂).result =
      J5a.transResult hW su hΓ p₁.result p₂.result := by
  unfold transResult transValley callD J5a.transResult J5a.transValley J5a.callD
  simp only [DProofVia.dProc_ofWf]

/-- Compatibility is equality of the actual result, including its exact
step-indexed certificate data. -/
theorem build_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → (hf : J5a.fragment h = true) →
    (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (build hW su R (.ofWf hΓ) h hf hs).result =
      J5a.buildFragment hW su R hΓ h hf hs
  | _, _, _, _, _, .refl .., _, _ => rfl
  | _, _, _, _, _, .irr .., _, _ => rfl
  | Γ, _, _, _, hΓ, .symm _ a b T h, hf, hs => by
      change (build hW su R (.ofWf hΓ) h hf _).result.swap = _
      rw [build_ofWf hW su R hΓ h hf]
      rfl
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hf, hs => by
      change (build hW su R (.ofWf hΓ) h hf _).result.reindex u hT hs = _
      rw [build_ofWf hW su R hΓ h hf]
      rfl
  | Γ, _, _, _, hΓ, .trans _ a b c T h₁ h₂, hf, hs => by
      change (transResult hW su (.ofWf hΓ) _ _).result = _
      rw [transResult_ofWf]
      rw [build_ofWf hW su R hΓ h₁, build_ofWf hW su R hΓ h₂]
      rfl
  | _, _, _, _, _, .beta .., hf, _ => by cases hf
  | _, _, _, _, _, .zeta .., hf, _ => by cases hf
  | _, _, _, _, _, .zetaLocal .., hf, _ => by cases hf
  | _, _, _, _, _, .delta .., hf, _ => by cases hf
  | _, _, _, _, _, .iota .., hf, _ => by cases hf
  | _, _, _, _, _, .lit .., hf, _ => by cases hf
  | _, _, _, _, _, .app .., hf, _ => by cases hf
  | _, _, _, _, _, .lam .., hf, _ => by cases hf
  | _, _, _, _, _, .pi .., hf, _ => by cases hf
  | _, _, _, _, _, .letE .., hf, _ => by cases hf
  | _, _, _, _, _, .sorts .., hf, _ => by cases hf
  | _, _, _, _, _, .consts .., hf, _ => by cases hf
  | _, _, _, _, _, .eta .., hf, _ => by cases hf

theorem buildFragment_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hf : J5a.fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    buildFragment hW su R (.ofWf hΓ) h hf hs =
      J5a.buildFragment hW su R hΓ h hf hs :=
  build_ofWf hW su R hΓ h hf hs

def dispatchVia (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option (Result hW R h) :=
  if hf : J5a.fragment h = true then some (buildFragment hW su R v h hf hs) else none

theorem dispatchVia_coverage (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (dispatchVia hW su R v h hs).isSome = J5a.fragment h := by
  cases hf : J5a.fragment h <;> simp [dispatchVia, hf]

theorem dispatchVia_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    dispatchVia hW su R (.ofWf hΓ) h hs = J5a.dispatchWf hW su R hΓ h hs := by
  by_cases hf : J5a.fragment h = true <;>
    simp [dispatchVia, J5a.dispatchWf, hf, buildFragment_ofWf]

theorem buildFragment_only (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hf : J5a.fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    J5aProofOnly.valleyPI (buildFragment hW su R v h hf hs).valley :=
  (build hW su R v h hf hs).only

theorem buildFragment_edge (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hf : J5a.fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (Z : List (Jd E n)) :
    OM3_edge ([.cv h] ++ Z) ((buildFragment hW su R v h hf hs).valley.leaves ++ Z) :=
  J3.result_edge (buildFragment hW su R v h hf hs) Z

end Rcic.Declarative.F8Measure.J5aVia
