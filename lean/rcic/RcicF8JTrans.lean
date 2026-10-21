import rcic.RcicF8JTransport
import rcic.RcicF8DTileStep

/-!
J5a: raw trans consumes the actual landed D at the original middle.
The connector emits existing s.read producers, not an alleged equality to
s.star1. Certificates index the EXISTING materialized stars. No carrier,
measure, D solver, or generated J re-call is added. SortUnique is explicit;
its piRow-free supply is the separate sortRow 4c route, never TypedRowsWf.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J5a
open F8Occurrences J3
variable {E : ResolvedEnv} {n : Nat} {R X : List (Jd E n)}

/-- Certificate of the ACTUAL existing base producer, using its owner tile. -/
def baseCertificate (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} :
    (p : EvPar R Γ a b T) → StepCertificate R X (p.val hcl hinst)
  | .proofIndex p =>
      let t := (EvPar.proofIndex p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩
  | .structPi p =>
      let t := (EvPar.structPi p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩
  | .sortEq p =>
      let t := (EvPar.sortEq p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩
  | .consts p =>
      let t := (EvPar.consts p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩
  | .lit p =>
      let t := (EvPar.lit p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩
  | .refl p =>
      let t := (EvPar.refl p).toDTile hcl hinst X
      ⟨t.status, t.om2⟩

theorem baseCertificate_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (p : EvPar R Γ a b T) :
    (baseCertificate hcl hinst X p).tile = p.toDTile hcl hinst X := by
  cases p <;> rfl

/-- An OUTPUT construction on the existing D spine; every tail is s.read. -/
def readSpine {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → DSpine R Γ T a b → EvParStar R Γ a b T
  | _, _, .refl h => .refl h
  | _, _, .tail s rest => .tail s.read (readSpine rest)

theorem readSpine_leaves {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (s : DSpine R Γ T a b) →
    ∀ l ∈ (readSpine s).leaves, l ∈ s.leaves
  | _, _, .refl _, _, hl => hl
  | _, _, .tail s rest, l, hl => by
      simp only [readSpine, EvParStar.leaves, DSpine.leaves, List.mem_append] at hl ⊢
      rcases hl with h | h
      · exact .inl (s.read_leaves l h)
      · exact .inr (readSpine_leaves rest l h)

def readSpine_certified (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (s : DSpine R Γ T a b) →
    Certified R X ((readSpine s).val hcl hinst)
  | _, _, .refl _ => PUnit.unit
  | _, _, .tail s rest =>
      ⟨baseCertificate hcl hinst X s.read, readSpine_certified hcl hinst X rest⟩

theorem readSpine_tail_exact {Γ : LCtx} {T a b c : Expr Nat}
    (s : DStep R Γ a b T) (rest : DSpine R Γ T b c) :
    readSpine (.tail s rest) = EvParStar.tail s.read (readSpine rest) := rfl

def readOutput {Γ : LCtx} {a b T : Expr Nat} (s : EvParStar R Γ a b T) :
    EvParStar R Γ a b T := readSpine s.spine

theorem readOutput_leaves {Γ : LCtx} {a b T : Expr Nat}
    (s : EvParStar R Γ a b T) : ∀ l ∈ (readOutput s).leaves, l ∈ s.leaves :=
  fun l hl => s.spine_leaves l (readSpine_leaves s.spine l hl)

def readOutput_certified (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (s : EvParStar R Γ a b T) :
    Certified R X ((readOutput s).val hcl hinst) :=
  readSpine_certified hcl hinst X s.spine

/-- Splice certificates on the existing parRedTStar_trans, not a new star. -/
def certifiedSplice {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} →
    (s₁ : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    (s₂ : ParRedTStar (PEqLeafT E n) E n Γ b c T) →
    Certified R X s₁ → Certified R X s₂ →
    Certified R X (parRedTStar_trans s₁ s₂)
  | _, _, _, .refl .., _, _, k₂ => k₂
  | _, _, _, .tail _ rest, s₂, k₁, k₂ =>
      ⟨k₁.1, certifiedSplice rest s₂ k₁.2 k₂⟩

end Rcic.Declarative.F8Measure.J5a

namespace Rcic.Declarative.F8Measure.J5a
open J3
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
variable {Γ : LCtx} {a b c T : Expr Nat}
variable {h₁ : ConvT E n Γ a b T} {h₂ : ConvT E n Γ b c T}

/-- The D request is at the ORIGINAL shared middle b, not at the outer endpoints. -/
def callD (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :=
  dProcWf (R := R) hW su hΓ p₁.valley.right p₂.valley.left

theorem callD_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    callD hW su hΓ p₁ p₂ =
      dProcWf (R := R) hW su hΓ p₁.valley.right p₂.valley.left := rfl

def transValley (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    Valley R Γ a c T :=
  let k := callD hW su hΓ p₁ p₂
  { N := k.1
    left := .trans p₁.valley.left (readOutput k.2.1)
    right := .trans p₂.valley.right (readOutput k.2.2)
    ty₁ := p₁.valley.ty₁
    ty₂ := p₂.valley.ty₂ }

theorem left_child_support {hW : EnvWfT E} (p₁ : Result hW R h₁)
    (l : Jd E n) (hl : l ∈ p₁.valley.leaves) :
    SubOf l (.cv (.trans Γ a b c T h₁ h₂)) :=
  .trans (p₁.strict l hl) (.child (.head _))

theorem right_child_support {hW : EnvWfT E} (p₂ : Result hW R h₂)
    (l : Jd E n) (hl : l ∈ p₂.valley.leaves) :
    SubOf l (.cv (.trans Γ a b c T h₁ h₂)) :=
  .trans (p₂.strict l hl) (.child (.tail _ (.head _)))

theorem middle_strict {hW : EnvWfT E} (p₁ : Result hW R h₁)
    (p₂ : Result hW R h₂) :
    ∀ l ∈ p₁.valley.right.leaves ++ p₂.valley.left.leaves,
      SubOf l (.cv (.trans Γ a b c T h₁ h₂)) := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · apply left_child_support p₁ l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inr h))
  · apply right_child_support p₂ l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inl h))

theorem closing_strict (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    ∀ l ∈ (readOutput (callD hW su hΓ p₁ p₂).2.1).leaves ++
          (readOutput (callD hW su hΓ p₁ p₂).2.2).leaves,
      SubOf l (.cv (.trans Γ a b c T h₁ h₂)) := by
  intro l hl
  have hd : l ∈ (callD hW su hΓ p₁ p₂).2.1.leaves ++
      (callD hW su hΓ p₁ p₂).2.2.leaves := by
    rcases List.mem_append.mp hl with h | h
    · exact List.mem_append.mpr (.inl (readOutput_leaves _ l h))
    · exact List.mem_append.mpr (.inr (readOutput_leaves _ l h))
  obtain ⟨k, hk, hs⟩ := dContractWf hW su R hΓ
    p₁.valley.right p₂.valley.left l hd
  exact subEq_trans_subOf hs (middle_strict p₁ p₂ k hk)

theorem transValley_strict (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    ∀ l ∈ (transValley hW su hΓ p₁ p₂).leaves,
      SubOf l (.cv (.trans Γ a b c T h₁ h₂)) := by
  intro l hl
  simp only [transValley, Valley.leaves, EvParStar.leaves, List.mem_append] at hl
  rcases hl with (((hL | hDL) | (hR | hDR)) | hT₁) | hT₂
  · apply left_child_support p₁ l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inl hL))
  · exact closing_strict hW su hΓ p₁ p₂ l (List.mem_append.mpr (.inl hDL))
  · apply right_child_support p₂ l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inl (.inr hR))
  · exact closing_strict hW su hΓ p₁ p₂ l (List.mem_append.mpr (.inr hDR))
  · apply left_child_support p₁ l
    simp only [Valley.leaves, List.mem_append]
    exact .inl (.inr hT₁)
  · apply right_child_support p₂ l
    simp only [Valley.leaves, List.mem_append]
    exact .inr hT₂

/-- Fully constructed result: original child calls, actual D, actual closing tiles. -/
def transResult (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    Result hW R (.trans Γ a b c T h₁ h₂) where
  valley := transValley hW su hΓ p₁ p₂
  leftTiles := certifiedSplice _ _
    (Certified.recaller (callerOfChild
      (y := .cv (.trans Γ a b c T h₁ h₂)) (.head _)) _ p₁.leftTiles)
    (readOutput_certified (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) [.cv (.trans Γ a b c T h₁ h₂)]
      (callD hW su hΓ p₁ p₂).2.1)
  rightTiles := certifiedSplice _ _
    (Certified.recaller (callerOfChild
      (y := .cv (.trans Γ a b c T h₁ h₂)) (.tail _ (.head _))) _ p₂.rightTiles)
    (readOutput_certified (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) [.cv (.trans Γ a b c T h₁ h₂)]
      (callD hW su hΓ p₁ p₂).2.2)
  strict := transValley_strict hW su hΓ p₁ p₂

theorem transResult_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    (transResult hW su hΓ p₁ p₂).valley = transValley hW su hΓ p₁ p₂ := rfl

theorem transValley_leaves (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (p₁ : Result hW R h₁) (p₂ : Result hW R h₂) :
    (transValley hW su hΓ p₁ p₂).leaves =
      ((p₁.valley.left.leaves ++ (readOutput (callD hW su hΓ p₁ p₂).2.1).leaves) ++
       (p₂.valley.right.leaves ++ (readOutput (callD hW su hΓ p₁ p₂).2.2).leaves) ++
       p₁.valley.ty₁.leaves) ++ p₂.valley.ty₂.leaves := rfl

theorem children_edge (h₁ : ConvT E n Γ a b T) (h₂ : ConvT E n Γ b c T)
    (Z : List (Jd E n)) :
    OM3_edge ([.cv (.trans Γ a b c T h₁ h₂)] ++ Z) ([.cv h₁, .cv h₂] ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun l hl => by
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, .head _, .child (.head _)⟩
    · have heq := List.mem_singleton.mp hl
      subst l
      exact ⟨_, .head _, .child (.tail _ (.head _))⟩)

theorem d_call_edge {hW : EnvWfT E} (p₁ : Result hW R h₁) (p₂ : Result hW R h₂)
    (Z : List (Jd E n)) :
    OM3_edge ([.cv (.trans Γ a b c T h₁ h₂)] ++ Z)
      ((p₁.valley.right.leaves ++ p₂.valley.left.leaves) ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun l hl => ⟨_, .head _, middle_strict p₁ p₂ l hl⟩)

end Rcic.Declarative.F8Measure.J5a

namespace Rcic.Declarative.F8Measure.J5a
open J3
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Independent INPUT grammar. Neither worker success nor a supplied Valley defines it. -/
def fragment : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .refl .. => true
  | _, _, _, _, .irr .. => true
  | _, _, _, _, .symm _ _ _ _ h => fragment h
  | _, _, _, _, .tyConv _ _ _ _ _ _ h _ => fragment h
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂ => fragment h₁ && fragment h₂
  | _, _, _, _, .beta .. => false
  | _, _, _, _, .zeta .. => false
  | _, _, _, _, .zetaLocal .. => false
  | _, _, _, _, .delta .. => false
  | _, _, _, _, .iota .. => false
  | _, _, _, _, .lit .. => false
  | _, _, _, _, .app .. => false
  | _, _, _, _, .lam .. => false
  | _, _, _, _, .pi .. => false
  | _, _, _, _, .letE .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
  | _, _, _, _, .eta .. => false

/-- Total on the independently specified fragment, structurally recursive on h.
The only non-child call is canonical D at the original shared middle. -/
def buildFragment (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → fragment h = true →
    (∃ r ∈ R, SubEq (.cv h) r) → Result hW R h
  | _, _, _, _, _, .refl _ _ _ ha, _, hs => reflResult hW ha hs
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, _, hs => irrResult hW hP hp hq hs
  | Γ, _, _, _, hΓ, .symm _ a b T h, hf, hs =>
      (buildFragment hW su R hΓ h hf
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)).swap
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hf, hs =>
      (buildFragment hW su R hΓ h hf
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)).reindex u hT hs
  | Γ, _, _, _, hΓ, .trans _ a b c T h₁ h₂, hf, hs =>
      transResult hW su hΓ
        (buildFragment hW su R hΓ h₁ (Bool.and_eq_true_iff.mp hf).1
          (certOfChild (y := .cv (.trans Γ a b c T h₁ h₂)) (.head _) hs))
        (buildFragment hW su R hΓ h₂ (Bool.and_eq_true_iff.mp hf).2
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

def dispatchWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option (Result hW R h) :=
  if hf : fragment h = true then some (buildFragment hW su R hΓ h hf hs) else none

theorem dispatchWf_coverage (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (dispatchWf hW su R hΓ h hs).isSome = fragment h := by
  cases hf : fragment h <;> simp [dispatchWf, hf]

theorem buildFragment_strict (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hf : fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    ∀ l ∈ (buildFragment hW su R hΓ h hf hs).valley.leaves, SubOf l (.cv h) :=
  (buildFragment hW su R hΓ h hf hs).strict

theorem buildFragment_edge (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hf : fragment h = true)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (Z : List (Jd E n)) :
    OM3_edge ([.cv h] ++ Z) ((buildFragment hW su R hΓ h hf hs).valley.leaves ++ Z) :=
  J3.result_edge (buildFragment hW su R hΓ h hf hs) Z

end Rcic.Declarative.F8Measure.J5a
