import rcic.RcicF8JTrans

/-!
The syntactic proof-index invariant of the actual J5a recursion.  These are
predicates on the landed carriers; they introduce no reduction producer or D
solver.  In particular the D theorem is about the existing dProcWf, and the J
theorem is about the existing buildFragment.  closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J5aProofOnly

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Only the proof-index owner constructor is allowed at a nonempty step. -/
def parPI : {Γ : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T → Prop
  | _, _, _, _, .proofIndex _ => True
  | _, _, _, _, .structPi _ => False
  | _, _, _, _, .sortEq _ => False
  | _, _, _, _, .consts _ => False
  | _, _, _, _, .lit _ => False
  | _, _, _, _, .refl _ => False

/-- A proof-index owner under the existing lazy step transports. -/
def stepPI : {Γ : LCtx} → {a b T : Expr Nat} → DStep R Γ a b T → Prop
  | _, _, _, _, .base p => parPI p
  | _, _, _, _, .conv s _ => stepPI s
  | _, _, _, _, .wk _ _ s => stepPI s
  | _, _, _, _, .subst0 _ s _ _ => stepPI s
  | _, _, _, _, .substLet _ s _ _ => stepPI s

def spinePI {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → DSpine R Γ T a b → Prop
  | _, _, .refl _ => True
  | _, _, .tail s rest => stepPI s ∧ spinePI rest

/-- The star predicate follows every constructor, including lazy splicing. -/
def starPI : {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T → Prop
  | _, _, _, _, .refl _ => True
  | _, _, _, _, .tail p rest => parPI p ∧ starPI rest
  | _, _, _, _, .conv ss _ => starPI ss
  | _, _, _, _, .wk _ _ ss => starPI ss
  | _, _, _, _, .trans s₁ s₂ => starPI s₁ ∧ starPI s₂
  | _, _, _, _, .subst0 _ ss _ _ => starPI ss
  | _, _, _, _, .substLet _ ss _ _ => starPI ss

def optPI : {Γ : LCtx} → {a b T : Expr Nat} → DOpt R Γ a b T → Prop
  | _, _, _, _, .stay _ => True
  | _, _, _, _, .step s => stepPI s

theorem readConv {Γ : LCtx} {a b T U : Expr Nat}
    (p : EvPar R Γ a b T) (c : EvTc R Γ T U) (hp : parPI p) :
    parPI (p.readConv c) := by
  cases p <;> simp_all only [parPI, EvPar.readConv]

theorem readWk {Γ : LCtx} {a b T : Expr Nat}
    (p : EvPar R Γ a b T) (d : LocalDecl) (k : Nat) (hp : parPI p) :
    parPI (p.readWk d k) := by
  cases p <;> simp_all only [parPI, EvPar.readWk]

/-- Lazy substitution preserves the proof-index owner, as `readWk` does. -/
theorem readSubst0 {Γ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) (hp : parPI p) :
    parPI (p.readSubst0 j hget hv) := by
  cases p with
  | proofIndex _ => exact True.intro
  | structPi _ => simp only [parPI] at hp
  | sortEq _ => simp only [parPI] at hp
  | consts _ => simp only [parPI] at hp
  | lit _ => simp only [parPI] at hp
  | refl _ => simp only [parPI] at hp

theorem readSubstLet {Γ : LCtx} {t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) (hp : parPI p) :
    parPI (p.readSubstLet j hget hv) := by
  cases p with
  | proofIndex _ => exact True.intro
  | structPi _ => simp only [parPI] at hp
  | sortEq _ => simp only [parPI] at hp
  | consts _ => simp only [parPI] at hp
  | lit _ => simp only [parPI] at hp
  | refl _ => simp only [parPI] at hp

theorem read : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    stepPI s → parPI s.read
  | _, _, _, _, .base p, hp => hp
  | _, _, _, _, .conv s c, hs => readConv s.read c (read s hs)
  | _, _, _, _, .wk d k s, hs => readWk s.read d k (read s hs)
  | _, _, _, _, .subst0 j s hget hv, hs => readSubst0 j hget hv s.read (read s hs)
  | _, _, _, _, .substLet j s hget hv, hs => readSubstLet j hget hv s.read (read s hs)

theorem parPI_castR {Γ : LCtx} {a b b' T : Expr Nat}
    (hb : b = b') (p : EvPar R Γ a b T) : parPI (p.castR hb) ↔ parPI p := by
  subst hb
  rfl

theorem readConv_iff {Γ : LCtx} {a b T U : Expr Nat}
    (p : EvPar R Γ a b T) (c : EvTc R Γ T U) :
    parPI (p.readConv c) ↔ parPI p := by
  cases p <;> simp only [EvPar.readConv, parPI]

theorem readWk_iff {Γ : LCtx} {a b T : Expr Nat}
    (p : EvPar R Γ a b T) (d : LocalDecl) (k : Nat) :
    parPI (p.readWk d k) ↔ parPI p := by
  cases p with
  | proofIndex _ => exact Iff.rfl
  | structPi _ => exact Iff.rfl
  | sortEq _ => exact Iff.rfl
  | consts _ => exact Iff.rfl
  | refl _ => exact Iff.rfl
  | lit p =>
      simp only [EvPar.readWk]
      rw [parPI_castR]
      exact Iff.rfl

theorem readSubst0_iff {Γ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) :
    parPI (p.readSubst0 j hget hv) ↔ parPI p := by
  cases p with
  | proofIndex _ => exact Iff.rfl
  | structPi _ => exact Iff.rfl
  | sortEq _ => exact Iff.rfl
  | consts _ => exact Iff.rfl
  | lit _ =>
      simp only [EvPar.readSubst0]
      rw [parPI_castR]
      exact Iff.rfl
  | refl _ => exact Iff.rfl

theorem readSubstLet_iff {Γ : LCtx} {t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) :
    parPI (p.readSubstLet j hget hv) ↔ parPI p := by
  cases p with
  | proofIndex _ => exact Iff.rfl
  | structPi _ => exact Iff.rfl
  | sortEq _ => exact Iff.rfl
  | consts _ => exact Iff.rfl
  | lit _ =>
      simp only [EvPar.readSubstLet]
      rw [parPI_castR]
      exact Iff.rfl
  | refl _ => exact Iff.rfl

/-- Reading reflects the owner constructor as well as preserving it. -/
theorem of_read : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    parPI s.read → stepPI s
  | _, _, _, _, .base _, hp => hp
  | _, _, _, _, .conv s c, hs => of_read s ((readConv_iff s.read c).mp hs)
  | _, _, _, _, .wk d k s, hs => of_read s ((readWk_iff s.read d k).mp hs)
  | _, _, _, _, .subst0 j s hget hv, hs =>
      of_read s ((readSubst0_iff j hget hv s.read).mp hs)
  | _, _, _, _, .substLet j s hget hv, hs =>
      of_read s ((readSubstLet_iff j hget hv s.read).mp hs)

theorem readConv_rightTy {Γ : LCtx} {a b T U : Expr Nat}
    (p : EvPar R Γ a b T) (c : EvTc R Γ T U) (hp : parPI p) :
    (p.readConv c).rightTy = .rety p.rightTy c := by
  cases p <;> simp_all only [parPI, EvPar.readConv, EvPar.rightTy]

theorem readWk_rightTy {Γ : LCtx} {a b T : Expr Nat}
    (p : EvPar R Γ a b T) (d : LocalDecl) (k : Nat) (hp : parPI p) :
    (p.readWk d k).rightTy = .wk d k p.rightTy := by
  cases p <;> simp_all only [parPI, EvPar.readWk, EvPar.rightTy]

theorem readSubst0_rightTy {Γ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) (hp : parPI p) :
    (p.readSubst0 j hget hv).rightTy = .subst0 j p.rightTy hget hv := by
  cases p with
  | proofIndex _ => rfl
  | structPi _ => simp only [parPI] at hp
  | sortEq _ => simp only [parPI] at hp
  | consts _ => simp only [parPI] at hp
  | lit _ => simp only [parPI] at hp
  | refl _ => simp only [parPI] at hp

theorem readSubstLet_rightTy {Γ : LCtx} {t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    {a b T : Expr Nat} (p : EvPar R Γ a b T) (hp : parPI p) :
    (p.readSubstLet j hget hv).rightTy = .substLet j p.rightTy hget hv := by
  cases p with
  | proofIndex _ => rfl
  | structPi _ => simp only [parPI] at hp
  | sortEq _ => simp only [parPI] at hp
  | consts _ => simp only [parPI] at hp
  | lit _ => simp only [parPI] at hp
  | refl _ => simp only [parPI] at hp

/-- Reading a proof-index step preserves its exact endpoint typing field.
The proof-index hypothesis matters: other owners can nest retypings differently. -/
theorem read_rightTy : {Γ : LCtx} → {a b T : Expr Nat} →
    (s : DStep R Γ a b T) → stepPI s → s.read.rightTy = s.rightTy
  | _, _, _, _, .base _, _ => rfl
  | _, _, _, _, .conv s c, hs => by
      simp only [DStep.read, DStep.rightTy,
        readConv_rightTy s.read c (read s hs), read_rightTy s hs]
  | _, _, _, _, .wk d k s, hs => by
      simp only [DStep.read, DStep.rightTy,
        readWk_rightTy s.read d k (read s hs), read_rightTy s hs]
  | _, _, _, _, .subst0 j s hget hv, hs => by
      simp only [DStep.read, DStep.rightTy,
        readSubst0_rightTy j hget hv s.read (read s hs), read_rightTy s hs]
  | _, _, _, _, .substLet j s hget hv, hs => by
      simp only [DStep.read, DStep.rightTy,
        readSubstLet_rightTy j hget hv s.read (read s hs), read_rightTy s hs]

theorem append {Γ : LCtx} {T : Expr Nat} : {a b c : Expr Nat} →
    (s₁ : DSpine R Γ T a b) → (s₂ : DSpine R Γ T b c) →
    spinePI s₁ → spinePI s₂ → spinePI (s₁.append s₂)
  | _, _, _, .refl _, _, _, h₂ => h₂
  | _, _, _, .tail s rest, s₂, h₁, h₂ =>
      ⟨h₁.1, append rest s₂ h₁.2 h₂⟩

theorem spineConv {Γ : LCtx} {T U : Expr Nat} (c : EvTc R Γ T U) :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) →
    spinePI ss → spinePI (ss.conv c)
  | _, _, .refl _, _ => True.intro
  | _, _, .tail s rest, hs => ⟨hs.1, spineConv c rest hs.2⟩

theorem spineWk (d : LocalDecl) (k : Nat) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) →
    spinePI ss → spinePI (ss.wk d k)
  | _, _, .refl _, _ => True.intro
  | _, _, .tail s rest, hs => ⟨hs.1, spineWk d k rest hs.2⟩

theorem spineSubst0 {Γ : LCtx} {T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) →
    spinePI ss → spinePI (ss.subst0 j hget hv)
  | _, _, .refl _, _ => True.intro
  | _, _, .tail _ rest, hs => ⟨hs.1, spineSubst0 j hget hv rest hs.2⟩

theorem spineSubstLet {Γ : LCtx} {T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) →
    spinePI ss → spinePI (ss.substLet j hget hv)
  | _, _, .refl _, _ => True.intro
  | _, _, .tail _ rest, hs => ⟨hs.1, spineSubstLet j hget hv rest hs.2⟩

theorem spine : {Γ : LCtx} → {a b T : Expr Nat} → (ss : EvParStar R Γ a b T) →
    starPI ss → spinePI ss.spine
  | _, _, _, _, .refl _, _ => True.intro
  | _, _, _, _, .tail p rest, hs => ⟨hs.1, spine rest hs.2⟩
  | _, _, _, _, .conv ss c, hs => spineConv c ss.spine (spine ss hs)
  | _, _, _, _, .wk d k ss, hs => spineWk d k ss.spine (spine ss hs)
  | _, _, _, _, .trans s₁ s₂, hs => append s₁.spine s₂.spine
      (spine s₁ hs.1) (spine s₂ hs.2)
  | _, _, _, _, .subst0 j ss hget hv, hs =>
      spineSubst0 j hget hv ss.spine (spine ss hs)
  | _, _, _, _, .substLet j ss hget hv, hs =>
      spineSubstLet j hget hv ss.spine (spine ss hs)

theorem star1 : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    stepPI s → starPI s.star1
  | _, _, _, _, .base p, hp => ⟨hp, True.intro⟩
  | _, _, _, _, .conv s _, hs => star1 s hs
  | _, _, _, _, .wk _ _ s, hs => star1 s hs
  | _, _, _, _, .subst0 _ s _ _, hs => star1 s hs
  | _, _, _, _, .substLet _ s _ _, hs => star1 s hs

theorem toStar {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    (ss : DSpine R Γ T a b) → spinePI ss → starPI ss.toStar
  | _, _, .refl _, _ => True.intro
  | _, _, .tail s rest, hs => ⟨star1 s hs.1, toStar rest hs.2⟩

theorem toSpine : {Γ : LCtx} → {a b T : Expr Nat} → (o : DOpt R Γ a b T) →
    optPI o → spinePI o.toSpine
  | _, _, _, _, .stay _, _ => True.intro
  | _, _, _, _, .step s, hs => ⟨hs, True.intro⟩

theorem readSpine {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    (ss : DSpine R Γ T a b) → spinePI ss → starPI (J5a.readSpine ss)
  | _, _, .refl _, _ => True.intro
  | _, _, .tail s rest, hs => ⟨read s hs.1, readSpine rest hs.2⟩

theorem readOutput {Γ : LCtx} {a b T : Expr Nat}
    (ss : EvParStar R Γ a b T) (hs : starPI ss) : starPI (J5a.readOutput ss) :=
  readSpine ss.spine (spine ss hs)

/-- A preservation property of a landed step diamond, used only to prove
closure of its existing strip/star combinators. -/
def diamondPI (S : DStepDiamondWf R) : Prop :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (s₁ : DStep R Γ a b T) (s₂ : DStep R Γ a c T),
    stepPI s₁ → stepPI s₂ →
    optPI (S hΓ s₁ s₂).left ∧ optPI (S hΓ s₁ s₂).right

theorem evParDiamond (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (p₁ : EvPar R Γ a b T) (p₂ : EvPar R Γ a c T)
    (h₁ : parPI p₁) (_h₂ : parPI p₂) :
    optPI (evParDiamondWf hW su hΓ p₁ p₂).left ∧
      optPI (evParDiamondWf hW su hΓ p₁ p₂).right := by
  cases p₁ <;> simp_all only [parPI, evParDiamondWf, evParDiamondAt, optPI, stepPI, proofIndexJoin]
  exact ⟨True.intro, True.intro⟩

/-- The actual D step call preserves the property; no supplier premise. -/
theorem dStepDiamond (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    diamondPI (dStepDiamondWf (R := R) hW su) := by
  intro Γ a b c T hΓ s₁ s₂ h₁ h₂
  exact evParDiamond hW su hΓ s₁.read s₂.read (read s₁ h₁) (read s₂ h₂)

theorem strip (S : DStepDiamondWf R) (hS : diamondPI S)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {T : Expr Nat} :
    {a b c : Expr Nat} → (s : DStep R Γ a b T) → (ss : DSpine R Γ T a c) →
    stepPI s → spinePI ss →
    spinePI (dStripWf S hΓ s ss).left ∧ spinePI (dStripWf S hΓ s ss).right
  | _, _, _, s, .refl _, hs, _ => ⟨True.intro, hs, True.intro⟩
  | _, _, _, s, .tail t rest, hs, hss => by
      have hJ := hS hΓ s t hs hss.1
      change optPI (S hΓ s t).left ∧ optPI (S hΓ s t).right at hJ
      simp only [dStripWf, dStripAt]
      cases hj : S hΓ s t with
      | mk d o₁ o₂ sound =>
          rw [hj] at hJ
          change optPI o₁ ∧ optPI o₂ at hJ
          cases o₂ with
          | stay h =>
              simpa only [dStripWf, dStripAt, hj] using
                And.intro (append o₁.toSpine rest (toSpine o₁ hJ.1) hss.2) True.intro
          | step u =>
              have hr := strip S hS hΓ u rest hJ.2 hss.2
              simpa only [dStripWf, dStripAt, hj] using
                And.intro
                  (append o₁.toSpine (dStripWf S hΓ u rest).left
                    (toSpine o₁ hJ.1) hr.1) hr.2

theorem star (S : DStepDiamondWf R) (hS : diamondPI S)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {T : Expr Nat} :
    {a b c : Expr Nat} → (ss₁ : DSpine R Γ T a b) → (ss₂ : DSpine R Γ T a c) →
    spinePI ss₁ → spinePI ss₂ →
    spinePI (dStarWf S hΓ ss₁ ss₂).left ∧ spinePI (dStarWf S hΓ ss₁ ss₂).right
  | _, _, _, .refl _, ss₂, _, h₂ => ⟨h₂, True.intro⟩
  | _, _, _, .tail s rest, ss₂, h₁, h₂ => by
      have hJ := strip S hS hΓ s ss₂ h₁.1 h₂
      have hK := star S hS hΓ rest (dStripWf S hΓ s ss₂).left h₁.2 hJ.1
      exact ⟨hK.1, append (dStripWf S hΓ s ss₂).right
        (dStarWf S hΓ rest (dStripWf S hΓ s ss₂).left).right hJ.2 hK.2⟩

theorem dStrip (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s : DStep R Γ a b T) (ss : DSpine R Γ T a c)
    (hs : stepPI s) (hss : spinePI ss) :
    spinePI (dStripWf (dStepDiamondWf hW su) hΓ s ss).left ∧
      spinePI (dStripWf (dStepDiamondWf hW su) hΓ s ss).right :=
  strip _ (dStepDiamond hW su) hΓ s ss hs hss

theorem dStar (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (ss₁ : DSpine R Γ T a b) (ss₂ : DSpine R Γ T a c)
    (h₁ : spinePI ss₁) (h₂ : spinePI ss₂) :
    spinePI (dStarWf (dStepDiamondWf hW su) hΓ ss₁ ss₂).left ∧
      spinePI (dStarWf (dStepDiamondWf hW su) hΓ ss₁ ss₂).right :=
  star _ (dStepDiamond hW su) hΓ ss₁ ss₂ h₁ h₂

/-- Actual H-D outputs on the proof-index fragment have only proof-index steps. -/
theorem dProc (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (ss₁ : EvParStar R Γ a b T) (ss₂ : EvParStar R Γ a c T)
    (h₁ : starPI ss₁) (h₂ : starPI ss₂) :
    starPI (dProcWf hW su hΓ ss₁ ss₂).2.1 ∧
      starPI (dProcWf hW su hΓ ss₁ ss₂).2.2 := by
  have h := dStar hW su hΓ ss₁.spine ss₂.spine (spine ss₁ h₁) (spine ss₂ h₂)
  exact ⟨toStar _ h.1, toStar _ h.2⟩

def valleyPI {Γ : LCtx} {a b T : Expr Nat} (V : Valley R Γ a b T) : Prop :=
  starPI V.left ∧ starPI V.right

theorem transValley (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} {a b c T : Expr Nat}
    {h₁ : ConvT E n Γ a b T} {h₂ : ConvT E n Γ b c T}
    (hΓ : CtxWfT E n Γ) (p₁ : J3.Result hW R h₁) (p₂ : J3.Result hW R h₂)
    (hp₁ : valleyPI p₁.valley) (hp₂ : valleyPI p₂.valley) :
    valleyPI (J5a.transValley hW su hΓ p₁ p₂) := by
  have hd := dProc hW su hΓ p₁.valley.right p₂.valley.left hp₁.2 hp₂.1
  exact ⟨⟨hp₁.1, readOutput _ hd.1⟩, ⟨hp₂.2, readOutput _ hd.2⟩⟩

/-- The invariant is derived by induction on the independent INPUT grammar,
and concerns the actual landed recursion result, not a supplied valley. -/
theorem buildFragment (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → (hf : J5a.fragment h = true) →
    (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    valleyPI (J5a.buildFragment hW su R hΓ h hf hs).valley
  | _, _, _, _, _, .refl _ _ _ _, _, _ => ⟨True.intro, True.intro⟩
  | _, _, _, _, _, .irr _ _ _ _ _ _ _, _, _ =>
      ⟨⟨True.intro, True.intro⟩, True.intro⟩
  | Γ, _, _, _, hΓ, .symm _ a b T h, hf, hs => by
      have ih := buildFragment hW su R hΓ h hf
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      exact ⟨ih.2, ih.1⟩
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hf, hs =>
      buildFragment hW su R hΓ h hf
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
  | Γ, _, _, _, hΓ, .trans _ a b c T h₁ h₂, hf, hs =>
      transValley hW su hΓ _ _
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

end Rcic.Declarative.F8Measure.J5aProofOnly
