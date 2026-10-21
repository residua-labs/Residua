import rcic.RcicF8DTileViaS
import rcic.RcicF8JTransProofOnly

/-!
Weakening correspondence for the ONE source-premise D object.  The relation
below records the complete read producer (including its proposition, chain,
and endpoint typing fields), rather than just its endpoints.  All certificates
are subsequently made from the reconstructed source producers.  No typing or
context well-formedness is transported backwards.  closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure

open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

def Wk.evTy : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a T : Expr Nat} →
    EvTy R Γ a T → EvTy R Δ (ρ.map a) (ρ.map T)
  | _, _, .id _, _, _, h => h
  | _, _, .ins d k ρ, _, _, h => ρ.evTy (.wk d k h)

def Wk.evTc : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {A B : Expr Nat} →
    EvTc R Γ A B → EvTc R Δ (ρ.map A) (ρ.map B)
  | _, _, .id _, _, _, c => c
  | _, _, .ins d k ρ, _, _, c => ρ.evTc (.wk d k c)

def Wk.par : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    EvPar R Γ a b T → EvPar R Δ (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, p => p
  | _, _, .ins d k ρ, _, _, _, p => ρ.par (p.readWk d k)

def Wk.step : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    DStep R Γ a b T → DStep R Δ (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, s => s
  | _, _, .ins d k ρ, _, _, _, s => ρ.step (.wk d k s)

def Wk.spine {Γ Δ : LCtx} (ρ : Wk Γ Δ) {T : Expr Nat} :
    {a b : Expr Nat} → DSpine R Γ T a b →
      DSpine R Δ (ρ.map T) (ρ.map a) (ρ.map b)
  | _, _, .refl h => .refl (ρ.evTy h)
  | _, _, .tail s rest => .tail (ρ.step s) (ρ.spine rest)

/-- The actual forward input transport uses the landed lazy star constructor. -/
def Wk.star : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    EvParStar R Γ a b T → EvParStar R Δ (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, ss => ss
  | _, _, .ins d k ρ, _, _, _, ss => ρ.star (.wk d k ss)

namespace DProofVia
open J5aProofOnly

theorem step_read : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    (s : DStep R Γ a b T) → (ρ.step s).read = ρ.par s.read
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, s => step_read ρ (.wk d k s)

theorem step_rightTy : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    (s : DStep R Γ a b T) → (ρ.step s).rightTy = ρ.evTy s.rightTy
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, s => step_rightTy ρ (.wk d k s)

theorem spine_wk {Γ Δ : LCtx} (d : LocalDecl) (k : Nat)
    (ρ : Wk (insertAt d k Γ) Δ) {T : Expr Nat}
    {a b : Expr Nat} (ss : DSpine R Γ T a b) :
    ρ.spine (ss.wk d k) = (Wk.ins d k ρ).spine ss := by
  induction ss with
  | refl => rfl
  | tail s rest ih => exact congrArg (DSpine.tail (ρ.step (.wk d k s))) ih

theorem star_spine : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    (ss : EvParStar R Γ a b T) → (ρ.star ss).spine = ρ.spine ss.spine
  | _, _, .id Γ, _, _, _, ss => by
      have hid : ∀ {a b T : Expr Nat} (sp : DSpine R Γ T a b),
          sp = (Wk.id Γ).spine sp := by
        intro a b T sp
        induction sp with
        | refl => rfl
        | tail s rest ih => exact congrArg (DSpine.tail s) ih
      exact hid ss.spine
  | _, _, .ins d k ρ, _, _, _, ss => by
      rw [Wk.star, star_spine ρ]
      change ρ.spine (ss.spine.wk d k) = (Wk.ins d k ρ).spine ss.spine
      exact spine_wk d k ρ ss.spine

theorem parPI_push : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    (p : EvPar R Γ a b T) → parPI p → parPI (ρ.par p)
  | _, _, .id _, _, _, _, _, hp => hp
  | _, _, .ins d k ρ, _, _, _, p, hp =>
      parPI_push ρ (p.readWk d k) (readWk p d k hp)

theorem starPI_push : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) → {a b T : Expr Nat} →
    (ss : EvParStar R Γ a b T) → starPI ss → starPI (ρ.star ss)
  | _, _, .id _, _, _, _, _, hs => hs
  | _, _, .ins d k ρ, _, _, _, ss, hs => starPI_push ρ (.wk d k ss) hs

/-- Heterogeneous equality here compares the full payload-bearing producer,
not merely the step's expressions or its materialized reduction endpoints. -/
structure StepReads {Γ Δ : LCtx} (ρ : Wk Γ Δ)
    {a b T A B U : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Δ A B U) : Prop where
  left : ρ.map a = A
  right : ρ.map b = B
  index : ρ.map T = U
  read : HEq t.read (ρ.par s.read)
  typing : HEq t.rightTy (ρ.evTy s.rightTy)

/-- Tail alignment retains every actual emitted read and its terminal typing. -/
inductive Reads {Γ Δ : LCtx} (ρ : Wk Γ Δ) :
    {a b T A B U : Expr Nat} → DSpine R Γ T a b → DSpine R Δ U A B → Type where
  | refl {a T A U : Expr Nat} (h : EvTy R Γ a T) (ht : EvTy R Δ A U)
      (term : ρ.map a = A) (index : ρ.map T = U)
      (typing : HEq ht (ρ.evTy h)) : Reads ρ (.refl h) (.refl ht)
  | tail {a b c T A B C U : Expr Nat}
      (s : DStep R Γ a b T) (t : DStep R Δ A B U)
      (rest : DSpine R Γ T b c) (trest : DSpine R Δ U B C)
      (step : StepReads ρ s t) (more : Reads ρ rest trest) :
      Reads ρ (.tail s rest) (.tail t trest)

theorem Reads.left {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B U : Expr Nat} {s : DSpine R Γ T a b} {t : DSpine R Δ U A B}
    (h : Reads ρ s t) : ρ.map a = A := by
  cases h with
  | refl _ _ e _ _ => exact e
  | tail _ _ _ _ st _ => exact st.left

theorem Reads.right {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B U : Expr Nat} {s : DSpine R Γ T a b} {t : DSpine R Δ U A B}
    (h : Reads ρ s t) : ρ.map b = B := by
  induction h with
  | refl _ _ e _ _ => exact e
  | tail _ _ _ _ _ _ ih => exact ih

theorem Reads.index {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B U : Expr Nat} {s : DSpine R Γ T a b} {t : DSpine R Δ U A B}
    (h : Reads ρ s t) : ρ.map T = U := by
  cases h with
  | refl _ _ _ e _ => exact e
  | tail _ _ _ _ st _ => exact st.index

theorem Reads.typing {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B U : Expr Nat} {s : DSpine R Γ T a b} {t : DSpine R Δ U A B}
    (h : Reads ρ s t) : HEq t.rightTy (ρ.evTy s.rightTy) := by
  induction h with
  | refl _ _ _ _ e => exact e
  | tail _ _ _ _ _ _ ih => exact ih

def Reads.append {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b c T A B C U : Expr Nat}
    {s₁ : DSpine R Γ T a b} {s₂ : DSpine R Γ T b c}
    {t₁ : DSpine R Δ U A B} {t₂ : DSpine R Δ U B C}
    (h₁ : Reads ρ s₁ t₁) (h₂ : Reads ρ s₂ t₂) :
    Reads ρ (s₁.append s₂) (t₁.append t₂) :=
  match b, B, s₁, t₁, h₁ with
  | _, _, .refl _, .refl _, .refl _ _ _ _ _ => h₂
  | _, _, .tail s rest, .tail t trest, .tail _ _ _ _ st more =>
      .tail s t _ _ st (more.append h₂)
termination_by structural h₁

def reads_push {Γ Δ : LCtx} (ρ : Wk Γ Δ) {T : Expr Nat} :
    {a b : Expr Nat} → (s : DSpine R Γ T a b) → Reads ρ s (ρ.spine s)
  | _, _, .refl h => .refl h _ rfl rfl (HEq.rfl)
  | _, _, .tail s rest => .tail s _ rest _
      ⟨rfl, rfl, rfl, heq_of_eq (step_read ρ s), heq_of_eq (step_rightTy ρ s)⟩
      (reads_push ρ rest)

def Reads.castRight {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B B' U : Expr Nat} {s : DSpine R Γ T a b}
    {t : DSpine R Δ U A B} {t' : DSpine R Δ U A B'}
    (h : Reads ρ s t) (endEq : B = B') (e : HEq t t') : Reads ρ s t' := by
  cases endEq
  cases eq_of_heq e
  exact h

theorem StepReads.pi {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b T A B U : Expr Nat} {s : DStep R Γ a b T} {t : DStep R Δ A B U}
    (h : StepReads ρ s t) (hs : stepPI s) : stepPI t := by
  rcases h with ⟨ha, hb, hT, hr, _⟩
  cases ha
  cases hb
  cases hT
  have hp := parPI_push ρ s.read (J5aProofOnly.read s hs)
  rw [← eq_of_heq hr] at hp
  exact of_read t hp

/-- The only new source producer is the same landed proof-index join. -/
def joinRead {Γ : LCtx} {a b c T : Expr Nat}
    (p : EvPar R Γ a b T) (hp : parPI p) (hc : EvTy R Γ c T) : EvPar R Γ b c T := by
  cases p with
  | proofIndex p => exact proofIndexJoin p hc
  | structPi _ => cases hp
  | sortEq _ => cases hp
  | consts _ => cases hp
  | lit _ => cases hp
  | refl _ => cases hp

theorem joinRead_pi {Γ : LCtx} {a b c T : Expr Nat}
    (p : EvPar R Γ a b T) (hp : parPI p) (hc : EvTy R Γ c T) :
    parPI (joinRead p hp hc) := by
  cases p with
  | proofIndex _ => trivial
  | structPi _ => exact False.elim hp
  | sortEq _ => exact False.elim hp
  | consts _ => exact False.elim hp
  | lit _ => exact False.elim hp
  | refl _ => exact False.elim hp

theorem joinRead_rightTy {Γ : LCtx} {a b c T : Expr Nat}
    (p : EvPar R Γ a b T) (hp : parPI p) (hc : EvTy R Γ c T) :
    (joinRead p hp hc).rightTy = hc := by
  cases p with
  | proofIndex _ => rfl
  | structPi _ => exact False.elim hp
  | sortEq _ => exact False.elim hp
  | consts _ => exact False.elim hp
  | lit _ => exact False.elim hp
  | refl _ => exact False.elim hp

theorem joinRead_leaves {Γ : LCtx} {a b c T : Expr Nat}
    (p : EvPar R Γ a b T) (hp : parPI p) (hc : EvTy R Γ c T) :
    ∀ ℓ ∈ (joinRead p hp hc).leaves, ℓ ∈ p.leaves ∨ ℓ ∈ hc.leaves := by
  cases p with
  | proofIndex p => exact proofIndexJoin_leaves p hc
  | structPi _ => cases hp
  | sortEq _ => cases hp
  | consts _ => cases hp
  | lit _ => cases hp
  | refl _ => cases hp

theorem joinRead_readWk {Γ : LCtx} {a b c T : Expr Nat}
    (p : EvPar R Γ a b T) (hp : parPI p) (hc : EvTy R Γ c T)
    (d : LocalDecl) (k : Nat) :
    (joinRead p hp hc).readWk d k =
      joinRead (p.readWk d k) (readWk p d k hp) (.wk d k hc) := by
  cases p with
  | proofIndex _ => rfl
  | structPi _ => exact False.elim hp
  | sortEq _ => exact False.elim hp
  | consts _ => exact False.elim hp
  | lit _ => exact False.elim hp
  | refl _ => exact False.elim hp

theorem joinRead_push : {Γ Δ : LCtx} → (ρ : Wk Γ Δ) →
    {a b c T : Expr Nat} → (p : EvPar R Γ a b T) → (hp : parPI p) →
    (hc : EvTy R Γ c T) →
    ρ.par (joinRead p hp hc) =
      joinRead (ρ.par p) (parPI_push ρ p hp) (ρ.evTy hc)
  | _, _, .id _, _, _, _, _, p, hp, hc => rfl
  | _, _, .ins d k ρ, _, _, _, _, p, hp, hc => by
      change ρ.par ((joinRead p hp hc).readWk d k) = _
      rw [joinRead_readWk]
      exact joinRead_push ρ (p.readWk d k) (readWk p d k hp) (.wk d k hc)

def StepReads.join {Γ Δ : LCtx} {ρ : Wk Γ Δ}
    {a b c T A B C U : Expr Nat}
    {s : DStep R Γ a b T} {t : DStep R Γ a c T}
    {st : DStep R Δ A B U} {tt : DStep R Δ A C U}
    (rs : StepReads ρ s st) (rt : StepReads ρ t tt)
    (hs : stepPI s) (ht : stepPI t) :
    StepReads ρ (.base (joinRead s.read (J5aProofOnly.read s hs) t.rightTy))
      (.base (joinRead st.read (J5aProofOnly.read st (rs.pi hs)) tt.rightTy)) := by
  rcases rs with ⟨ha, hb, hT, hread, hty⟩
  rcases rt with ⟨_, hc, _, _, htty⟩
  cases ha
  cases hb
  cases hc
  cases hT
  have er := eq_of_heq hread
  have et := eq_of_heq htty
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · apply heq_of_eq
    change joinRead st.read _ tt.rightTy = ρ.par (joinRead s.read _ t.rightTy)
    rw [joinRead_push]
    have hj : ∀ (p q : EvPar R Δ (ρ.map a) (ρ.map b) (ρ.map T))
        (hp : parPI p) (hq : parPI q)
        (hc hd : EvTy R Δ (ρ.map c) (ρ.map T)),
        p = q → hc = hd → joinRead p hp hc = joinRead q hq hd := by
      intro p q hp hq hc hd ep ec
      cases ep
      cases ec
      rfl
    exact hj _ _ _ _ _ _ er et
  · simp only [DStep.rightTy, joinRead_rightTy]
    exact heq_of_eq et

theorem star1_spine : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    s.star1.spine = .tail s (.refl s.rightTy)
  | _, _, _, _, .base _ => rfl
  | _, _, _, _, .conv s c => by
      simp only [DStep.star1, EvParStar.spine, star1_spine s,
        DSpine.conv, DStep.rightTy]
  | _, _, _, _, .wk d k s => by
      simp only [DStep.star1, EvParStar.spine, star1_spine s,
        DSpine.wk, DStep.rightTy]
  | _, _, _, _, .subst0 j s hget hv => by
      simp only [DStep.star1, EvParStar.spine, star1_spine s,
        DSpine.subst0, DStep.rightTy]
  | _, _, _, _, .substLet j s hget hv => by
      simp only [DStep.star1, EvParStar.spine, star1_spine s,
        DSpine.substLet, DStep.rightTy]

theorem toStar_spine {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) → ss.toStar.spine = ss
  | _, _, .refl _ => rfl
  | _, _, .tail s rest => by
      simp only [DSpine.toStar, EvParStar.spine, star1_spine s,
        toStar_spine rest, DSpine.append]

/-- The exact landed strip row on proof-index owners.  The equalities concern
the actual emitted producers, including the right endpoint typing field. -/
theorem actual_strip_tailAt {Γ : LCtx} (P : StructPiJoinAt R Γ) {a b c e T : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) (rest : DSpine R Γ T c e)
    (hs : stepPI s) (ht : stepPI t) :
    (dStripAt (dStepDiamondAt P) s (.tail t rest)).d = e ∧
      HEq (dStripAt (dStepDiamondAt P) s (.tail t rest)).left
        (DSpine.tail (.base (joinRead s.read (read s hs) t.rightTy)) rest) ∧
      HEq (dStripAt (dStepDiamondAt P) s (.tail t rest)).right
        (DSpine.refl rest.rightTy) := by
  have core : ∀ (p : EvPar R Γ a b T) (hp : parPI p), s.read = p →
      (dStripAt (dStepDiamondAt P) s (.tail t rest)).d = e ∧
        HEq (dStripAt (dStepDiamondAt P) s (.tail t rest)).left
          (DSpine.tail (.base (joinRead p hp t.rightTy)) rest) ∧
        HEq (dStripAt (dStepDiamondAt P) s (.tail t rest)).right
          (DSpine.refl rest.rightTy) := by
    intro p hp hr
    cases p with
    | proofIndex p =>
        have hd : (dStepDiamondAt P s t).d = c := by
          change (evParDiamondAt P s.read t.read).d = c
          rw [hr]
          rfl
        have hl : HEq (dStepDiamondAt P s t).left
            (DOpt.step (.base (proofIndexJoin p t.read.rightTy))) := by
          change HEq (evParDiamondAt P s.read t.read).left _
          rw [hr]
          exact HEq.rfl
        have hr' : HEq (dStepDiamondAt P s t).right
            (DOpt.stay t.read.rightTy) := by
          change HEq (evParDiamondAt P s.read t.read).right _
          rw [hr]
          exact HEq.rfl
        simp only [dStripAt]
        generalize hj : dStepDiamondAt P s t = J at hd hl hr' ⊢
        rcases J with ⟨d, o₁, o₂, hJ⟩
        change d = c at hd
        cases hd
        cases eq_of_heq hl
        cases eq_of_heq hr'
        simp only [DOpt.toSpine, DSpine.append, joinRead]
        rw [read_rightTy t ht]
        exact ⟨True.intro, HEq.rfl, HEq.rfl⟩
    | structPi _ => exact False.elim hp
    | sortEq _ => exact False.elim hp
    | consts _ => exact False.elim hp
    | lit _ => exact False.elim hp
    | refl _ => exact False.elim hp
  exact core s.read (read s hs) rfl

theorem actual_strip_tail (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c e T : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) (rest : DSpine R Γ T c e)
    (hs : stepPI s) (ht : stepPI t) :
    (dStripWf (dStepDiamondWf hW su) hΓ s (.tail t rest)).d = e ∧
      HEq (dStripWf (dStepDiamondWf hW su) hΓ s (.tail t rest)).left
        (DSpine.tail (.base (joinRead s.read (read s hs) t.rightTy)) rest) ∧
      HEq (dStripWf (dStepDiamondWf hW su) hΓ s (.tail t rest)).right
        (DSpine.refl rest.rightTy) :=
  actual_strip_tailAt (structPiJoinAtWf hW su hΓ) s t rest hs ht

/-- A source join together with a correspondence to one fixed actual target
execution.  The target execution is an index, never a supplied source result. -/
structure Reconstruction {Γ Δ : LCtx} (ρ : Wk Γ Δ)
    {b c T B C U : Expr Nat} {L M : List (Jd E n)}
    (actual : DSpineJoin R Δ B C U M) where
  out : DSpineJoin R Γ b c T L
  pi : spinePI out.left ∧ spinePI out.right
  reads : Reads ρ out.left actual.left × Reads ρ out.right actual.right

/-- Equality of the whole dependent spine join; proof fields are irrelevant. -/
theorem spineJoin_eq {Γ : LCtx} {b c T : Expr Nat} {L : List (Jd E n)}
    {x y : DSpineJoin R Γ b c T L} (hd : x.d = y.d)
    (hl : HEq x.left y.left) (hr : HEq x.right y.right) : x = y := by
  cases x
  cases y
  cases hd
  cases eq_of_heq hl
  cases eq_of_heq hr
  rfl

/-- Reconstruct the two actual strip branches.  There is no recursive strip
solver here: the proof-index row's right optional step is always `stay`. -/
def reconstructStrip (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ Δ : LCtx} (ρ : Wk Γ Δ) (hΔ : CtxWfT E n Δ)
    {a b c T A B C U : Expr Nat}
    (s : DStep R Γ a b T) (ss : DSpine R Γ T a c)
    (st : DStep R Δ A B U) (ts : DSpine R Δ U A C)
    (rs : StepReads ρ s st) (rr : Reads ρ ss ts)
    (hs : stepPI s) (hss : spinePI ss) :
    Reconstruction ρ (b := b) (c := c) (T := T) (L := s.leaves ++ ss.leaves)
      (dStripWf (dStepDiamondWf hW su) hΔ st ts) := by
  let evidence : Reconstruction ρ (b := b) (c := c) (T := T)
      (L := s.leaves ++ ss.leaves) (dStripWf (dStepDiamondWf hW su) hΔ st ts) := by
    cases rr with
    | refl h ht _ _ _ =>
        let out : DSpineJoin R Γ b _ T (s.leaves ++ (DSpine.refl h).leaves) :=
          { d := b
            left := .refl s.rightTy
            right := .tail s (.refl s.rightTy)
            sound := fun ℓ hm => by
              apply dSubEq_of_mem
              simp only [DSpine.leaves, List.mem_append] at hm ⊢
              rcases hm with h | h | h
              · exact .inl (s.rightTy_leaves ℓ h)
              · exact .inl h
              · exact .inl (s.rightTy_leaves ℓ h) }
        have rt : Reads ρ (DSpine.refl s.rightTy) (DSpine.refl st.rightTy) :=
          .refl _ _ rs.right rs.index rs.typing
        exact ⟨out, ⟨True.intro, hs, True.intro⟩,
          rt, .tail s st _ _ rs rt⟩
    | tail t tt rest trest rt more =>
        let j := joinRead s.read (read s hs) t.rightTy
        let out : DSpineJoin R Γ b _ T (s.leaves ++ (DSpine.tail t rest).leaves) :=
          { d := _
            left := .tail (.base j) rest
            right := .refl rest.rightTy
            sound := fun ℓ hm => by
              apply dSubEq_of_mem
              simp only [DSpine.leaves, DStep.leaves, List.mem_append] at hm ⊢
              rcases hm with (hj | hr) | hh
              · rcases joinRead_leaves s.read (read s hs) t.rightTy ℓ hj with hp | ht
                · exact .inl (s.read_leaves ℓ hp)
                · exact .inr (.inl (t.rightTy_leaves ℓ ht))
              · exact .inr (.inr hr)
              · exact .inr (.inr (rest.rightTy_leaves ℓ hh)) }
        have actual := actual_strip_tail hW su hΔ st tt trest (rs.pi hs) (rt.pi hss.1)
        have rl : Reads ρ out.left
            (.tail (.base (joinRead st.read (read st (rs.pi hs)) tt.rightTy)) trest) :=
          .tail _ _ rest trest (rs.join rt hs hss.1) more
        have rr : Reads ρ out.right (.refl trest.rightTy) :=
          .refl _ _ more.right more.index more.typing
        exact ⟨out, ⟨⟨joinRead_pi s.read (read s hs) t.rightTy, hss.2⟩, True.intro⟩,
          rl.castRight actual.1.symm actual.2.1.symm,
          rr.castRight actual.1.symm actual.2.2.symm⟩
  have e : evidence.out = dStripAt (dStepDiamondViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)) s ss := by
    cases rr with
    | refl => rfl
    | tail t tt rest trest rt more =>
        have h := actual_strip_tailAt
          (structPiJoinAtViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)) s t rest hs hss.1
        exact spineJoin_eq h.1.symm h.2.1.symm h.2.2.symm
  exact
    { out := dStripAt (dStepDiamondViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)) s ss
      pi := by rw [← e]; exact evidence.pi
      reads := by rw [← e]; exact evidence.reads }

/-- Composition of already reconstructed source joins; this is only the leaf
and append bookkeeping shared by the two actual star branches. -/
def assemble {Γ : LCtx} {a x b c T : Expr Nat}
    (s : DStep R Γ a x T) (rest : DSpine R Γ T x b) (other : DSpine R Γ T a c)
    (J : DSpineJoin R Γ x c T (s.leaves ++ other.leaves))
    (K : DSpineJoin R Γ b J.d T (rest.leaves ++ J.left.leaves)) :
    DSpineJoin R Γ b c T ((DSpine.tail s rest).leaves ++ other.leaves) :=
  { d := K.d
    left := K.left
    right := J.right.append K.right
    sound := by
      have hK : ∀ m ∈ rest.leaves ++ J.left.leaves,
          ∃ k ∈ (DSpine.tail s rest).leaves ++ other.leaves, SubEq m k := by
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact dSubEq_of_mem (by
            simp only [DSpine.leaves, List.mem_append]; exact .inl (.inr hm))
        · obtain ⟨k, hk, hsub⟩ := J.sound m (List.mem_append.mpr (.inl hm))
          refine ⟨k, ?_, hsub⟩
          simp only [DSpine.leaves, List.mem_append] at hk ⊢
          rcases hk with h | h
          · exact .inl (.inl h)
          · exact .inr h
      intro ℓ hm
      rcases List.mem_append.mp hm with hl | hr
      · exact dCover_trans K.sound hK ℓ (List.mem_append.mpr (.inl hl))
      · rcases List.mem_append.mp (J.right.append_leaves K.right ℓ hr) with hj | hk
        · obtain ⟨k, hmem, hsub⟩ := J.sound ℓ (List.mem_append.mpr (.inr hj))
          refine ⟨k, ?_, hsub⟩
          simp only [DSpine.leaves, List.mem_append] at hmem ⊢
          rcases hmem with h | h
          · exact .inl (.inl h)
          · exact .inr h
        · exact dCover_trans K.sound hK ℓ (List.mem_append.mpr (.inr hk)) }

/-- Follow the actual target star recursion.  Its paired input spine witness
is constructed by forward transport, and each recursive target join is the
one computed by the landed `dStripWf`/`dStarWf`. -/
def reconstructStar (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ Δ : LCtx} (ρ : Wk Γ Δ) (hΔ : CtxWfT E n Δ)
    {a b c T A B C U : Expr Nat}
    (ss₁ : DSpine R Γ T a b) (ss₂ : DSpine R Γ T a c)
    (ts₁ : DSpine R Δ U A B) (ts₂ : DSpine R Δ U A C)
    (r₁ : Reads ρ ss₁ ts₁) (r₂ : Reads ρ ss₂ ts₂)
    (h₁ : spinePI ss₁) (h₂ : spinePI ss₂) :
    Reconstruction ρ (b := b) (c := c) (T := T) (L := ss₁.leaves ++ ss₂.leaves)
      (dStarWf (dStepDiamondWf hW su) hΔ ts₁ ts₂) := by
  let S : DStepDiamondAt R Γ :=
    dStepDiamondViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)
  -- This induction computes only correspondence evidence. Its source index is
  -- always the shared fold; there is no second source-output recursion.
  let rec evidence {a b c T A B C U : Expr Nat}
      (ss₁ : DSpine R Γ T a b) (ss₂ : DSpine R Γ T a c)
      (ts₁ : DSpine R Δ U A B) (ts₂ : DSpine R Δ U A C)
      (r₁ : Reads ρ ss₁ ts₁) (r₂ : Reads ρ ss₂ ts₂)
      (h₁ : spinePI ss₁) (h₂ : spinePI ss₂) :
      PLift (spinePI (dStarAt S ss₁ ss₂).left ∧ spinePI (dStarAt S ss₁ ss₂).right) ×
        (Reads ρ (dStarAt S ss₁ ss₂).left
            (dStarWf (dStepDiamondWf hW su) hΔ ts₁ ts₂).left ×
         Reads ρ (dStarAt S ss₁ ss₂).right
            (dStarWf (dStepDiamondWf hW su) hΔ ts₁ ts₂).right) :=
    match b, B, ss₁, ts₁, r₁ with
    | _, _, .refl h, .refl ht, .refl _ _ _ _ _ =>
        ⟨⟨⟨h₂, True.intro⟩⟩, r₂, .refl _ _ r₂.right r₂.index r₂.typing⟩
    | _, _, .tail s rest, .tail st trest, .tail _ _ _ _ rs more => by
        let J := reconstructStrip hW su ρ hΔ s ss₂ st ts₂ rs r₂ h₁.1 h₂
        let K := evidence rest J.out.left trest
          (dStripWf (dStepDiamondWf hW su) hΔ st ts₂).left
          more J.reads.1 h₁.2 J.pi.1
        exact ⟨⟨⟨K.1.down.1, J5aProofOnly.append _ _ J.pi.2 K.1.down.2⟩⟩,
          K.2.1, J.reads.2.append K.2.2⟩
  termination_by structural r₁
  let proof := evidence ss₁ ss₂ ts₁ ts₂ r₁ r₂ h₁ h₂
  exact { out := dStarAt S ss₁ ss₂, pi := proof.1.down, reads := proof.2 }

def reads_id {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (ss : DSpine R Γ T a b) → Reads (.id Γ) ss ss
  | _, _, .refl h => .refl h h rfl rfl HEq.rfl
  | _, _, .tail s rest =>
      .tail s s rest rest ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩ (reads_id rest)

/-- The target call is always the landed D procedure on the two actual lazy
forward pushes, at the image of their original common source point. -/
def target (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :=
  dProcWf hW su v.wf (v.ρ.star s₁) (v.ρ.star s₂)

structure Result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) where
  out : Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T
  sound : ∀ ℓ ∈ out.2.1.leaves ++ out.2.2.leaves,
    ∃ k ∈ s₁.leaves ++ s₂.leaves, SubEq ℓ k
  pi : starPI out.2.1 ∧ starPI out.2.2
  center : v.ρ.map out.1 = (target hW su v s₁ s₂).1
  reads : Reads v.ρ out.2.1.spine (target hW su v s₁ s₂).2.1.spine ×
    Reads v.ρ out.2.2.spine (target hW su v s₁ s₂).2.2.spine

/-- The retained strip correspondence reconstructs precisely the shared source
fold. Its target is only the index of the correspondence. -/
theorem reconstructStrip_out (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ Δ : LCtx} (ρ : Wk Γ Δ) (hΔ : CtxWfT E n Δ)
    {a b c T A B C U : Expr Nat}
    (s : DStep R Γ a b T) (ss : DSpine R Γ T a c)
    (st : DStep R Δ A B U) (ts : DSpine R Δ U A C)
    (rs : StepReads ρ s st) (rr : Reads ρ ss ts)
    (hs : stepPI s) (hss : spinePI ss) :
    (reconstructStrip hW su ρ hΔ s ss st ts rs rr hs hss).out =
      dStripAt (dStepDiamondViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)) s ss := rfl

/-- Full source output agreement: the evidence induction is indexed by this
shared fold. No centre-only or endpoint-only identification is used. -/
theorem reconstructStar_out (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ Δ : LCtx} (ρ : Wk Γ Δ) (hΔ : CtxWfT E n Δ)
    {a b c T A B C U : Expr Nat}
    (ss₁ : DSpine R Γ T a b) (ss₂ : DSpine R Γ T a c)
    (ts₁ : DSpine R Δ U A B) (ts₂ : DSpine R Δ U A C)
    (r₁ : Reads ρ ss₁ ts₁) (r₂ : Reads ρ ss₂ ts₂)
    (h₁ : spinePI ss₁) (h₂ : spinePI ss₂) :
    (reconstructStar hW su ρ hΔ ss₁ ss₂ ts₁ ts₂ r₁ r₂ h₁ h₂).out =
      dStarAt (dStepDiamondViaS hW su (CtxWfVia.toS ⟨Δ, ρ, hΔ⟩)) ss₁ ss₂ := rfl

def reconstructed (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (h₁ : starPI s₁) (h₂ : starPI s₂) : Result hW su v s₁ s₂ := by
  let t₁ := v.ρ.star s₁
  let t₂ := v.ρ.star s₂
  have r₁ : Reads v.ρ s₁.spine t₁.spine := by
    rw [show t₁.spine = v.ρ.spine s₁.spine from star_spine v.ρ s₁]
    exact reads_push v.ρ s₁.spine
  have r₂ : Reads v.ρ s₂.spine t₂.spine := by
    rw [show t₂.spine = v.ρ.spine s₂.spine from star_spine v.ρ s₂]
    exact reads_push v.ρ s₂.spine
  let J := reconstructStar hW su v.ρ v.wf s₁.spine s₂.spine t₁.spine t₂.spine
    r₁ r₂ (spine s₁ h₁) (spine s₂ h₂)
  have eJ := reconstructStar_out hW su v.ρ v.wf s₁.spine s₂.spine t₁.spine t₂.spine
    r₁ r₂ (spine s₁ h₁) (spine s₂ h₂)
  have output_eq : dProcViaS hW su v.toS s₁ s₂ =
      ⟨J.out.d, J.out.left.toStar, J.out.right.toStar⟩ := by
    simp only [dProcViaS, dProcAt]
    rw [← eJ]
  refine
    { out := dProcViaS hW su v.toS s₁ s₂
      sound := dContractViaS hW su R v.toS s₁ s₂
      pi := ?_
      center := ?_
      reads := ?_ }
  · rw [output_eq]
    exact ⟨toStar J.out.left J.pi.1, toStar J.out.right J.pi.2⟩
  · rw [output_eq]
    exact J.reads.1.right
  · rw [output_eq]
    constructor
    · change Reads v.ρ J.out.left.toStar.spine
        (dStarWf (dStepDiamondWf hW su) v.wf t₁.spine t₂.spine).left.toStar.spine
      rw [toStar_spine, toStar_spine]
      exact J.reads.1
    · change Reads v.ρ J.out.right.toStar.spine
        (dStarWf (dStepDiamondWf hW su) v.wf t₁.spine t₂.spine).right.toStar.spine
      rw [toStar_spine, toStar_spine]
      exact J.reads.2

def landed (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (h₁ : starPI s₁) (h₂ : starPI s₂) : Result hW su (.ofWf hΓ) s₁ s₂ :=
  { out := dProcWf hW su hΓ s₁ s₂
    sound := dContractWf hW su R hΓ s₁ s₂
    pi := J5aProofOnly.dProc hW su hΓ s₁ s₂ h₁ h₂
    center := rfl
    reads := ⟨reads_id _, reads_id _⟩ }

/-- D-Via accepts only the actual source inputs and their derived syntactic
invariant.  No source closure, source well-formedness, or backtransportability
premise is supplied by its caller. -/
def dProc (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (h₁ : starPI s₁) (h₂ : starPI s₂) : Result hW su v s₁ s₂ := by
  cases v with
  | mk Δ ρ hΔ =>
      cases ρ with
      | id => exact landed hW su hΔ s₁ s₂ h₁ h₂
      | ins d k ρ => exact reconstructed hW su ⟨Δ, .ins d k ρ, hΔ⟩ s₁ s₂ h₁ h₂

/-- The landed weakening front is the `ins` specialization of the ONE source
object. The equality includes both complete closing stars. -/
theorem dProc_eq_dProcViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (h₁ : starPI s₁) (h₂ : starPI s₂) :
    (dProc hW su v s₁ s₂ h₁ h₂).out = dProcViaS hW su v.toS s₁ s₂ := by
  cases v with
  | mk Δ ρ hΔ => cases ρ <;> rfl

/-- On a genuinely well-formed source, the twin returns the actual landed D
result, as an equality of the complete payload-bearing output carrier. -/
theorem dProc_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (h₁ : starPI s₁) (h₂ : starPI s₂) :
    (dProc hW su (.ofWf hΓ) s₁ s₂ h₁ h₂).out = dProcWf hW su hΓ s₁ s₂ := rfl

end DProofVia
end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.DProofVia.actual_strip_tailAt
#print axioms Rcic.Declarative.F8Measure.DProofVia.spineJoin_eq
#print axioms Rcic.Declarative.F8Measure.DProofVia.reconstructStrip_out
#print axioms Rcic.Declarative.F8Measure.DProofVia.reconstructStar_out
#print axioms Rcic.Declarative.F8Measure.DProofVia.dProc_eq_dProcViaS
