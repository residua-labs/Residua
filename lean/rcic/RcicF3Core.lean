import rcic.RcicF3Sound

/-!
# F3 S3: the model's obligations and context fitting

`Good M N Lvl`: what the core soundness proof needs from the universe
stages of an interpretation `M`, up to the level bound `N`. `Lvl k S` says
`S` is the element set of a level-`k` type:

- level 0 is exactly the subsets of `{∅}` (propositions, proof-irrelevant);
- every level's element sets are dichotomous;
- `U k` (for `k ≤ N`) consists exactly of the tagged level-`k` element sets,
  and `U k` itself is a level-`(k+1)` element set when `k + 1 ≤ N`;
- positive levels contain every subset of `{∅}`, include lower positive
  levels, and are closed under dependent products.

`Fits Γ ρ`: the environment `ρ` realizes the context `Γ` (each assumption's
value is an element of its type, each let-bound value is its definiens).
Soundness is stated over fitting environments only (F3 plan, D4).
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

structure Good (M : Interp.{T}) (N : Nat) (Lvl : Nat → PSet.{T} → Prop) : Prop where
  congr : ∀ {k : Nat} {S S' : PSet.{T}}, Lvl k S → Equiv S S' → Lvl k S'
  dich : ∀ {k : Nat} {S : PSet.{T}}, Lvl k S → Dich S
  lvl0 : ∀ {S : PSet.{T}}, Lvl 0 S ↔ ∀ y, y ∈ S → Equiv y pempty
  U_iff : ∀ {k : Nat}, k ≤ N → ∀ x, x ∈ M.U k ↔ ∃ S, Lvl k S ∧ Equiv x (tyv S)
  univ : ∀ {k : Nat}, k + 1 ≤ N → Lvl (k + 1) (M.U k)
  prop : ∀ {m : Nat} {S : PSet.{T}}, 1 ≤ m → m ≤ N → (∀ y, y ∈ S → Equiv y pempty) → Lvl m S
  mono : ∀ {k m : Nat} {S : PSet.{T}}, 1 ≤ k → k ≤ m → m ≤ N → Lvl k S → Lvl m S
  pi : ∀ {m : Nat} {A : PSet.{T}} {B : PSet.{T} → PSet.{T}}, 1 ≤ m → m ≤ N → Lvl m A →
    (∀ a a', Equiv a a' → Equiv (B a) (B a')) → (∀ x, x ∈ A → Lvl m (B x)) → Lvl m (piSet A B)

/-- Drop the first binding. -/
def tl (ρ : Nat → PSet.{T}) : Nat → PSet.{T} := fun i => ρ (i + 1)

theorem tl_vcons (x : PSet.{T}) (ρ : Nat → PSet.{T}) : tl (vcons x ρ) = ρ := rfl

/-- The environment realizes the context. -/
def Fits (M : Interp.{T}) (σ : Nat → Nat) : LCtx → (Nat → PSet.{T}) → Prop
  | [], _ => True
  | .assumption A :: Γ, ρ => Fits M σ Γ (tl ρ) ∧ ρ 0 ∈ Ed M (den M σ (tl ρ) A)
  | .letBinding A v :: Γ, ρ => Fits M σ Γ (tl ρ) ∧ ρ 0 ∈ Ed M (den M σ (tl ρ) A) ∧
      Equiv (ρ 0) (den M σ (tl ρ) v)

theorem shiftρ_succ (k : Nat) (ρ : Nat → PSet.{T}) : shiftρ (k + 1) ρ = shiftρ k (tl ρ) := by
  funext i
  show ρ (i + (k + 1)) = ρ (i + k + 1)
  rw [Nat.add_assoc]

theorem den_lift_shift (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (k : Nat)
    (A : Expr Nat) : den M σ ρ (Rcic.Declarative.lift 0 k A) = den M σ (shiftρ k ρ) A := by
  rw [den_lift, liftρ_zero]

/-- The type of a context entry. -/
def declType : LocalDecl → Expr Nat
  | .assumption A => A
  | .letBinding A _ => A

/-- A fitting environment's value at a variable is an element of the entry's
type, read in the tail environment. -/
theorem fits_get (M : Interp.{T}) (σ : Nat → Nat) :
    (Γ : LCtx) → (ρ : Nat → PSet.{T}) → Fits M σ Γ ρ → ∀ (i : Nat) (d : LocalDecl),
      Γ.get? i = some d → ρ i ∈ Ed M (den M σ (shiftρ (i + 1) ρ) (declType d))
  | [], _, _, i, d, h => by simp at h
  | d' :: Γ, ρ, hf, 0, d, h => by
      simp only [List.get?, Option.some.injEq] at h
      subst h
      cases d' with
      | assumption B => exact hf.2
      | letBinding B v => exact hf.2.1
  | d' :: Γ, ρ, hf, i + 1, d, h => by
      have htail : Fits M σ Γ (tl ρ) := by cases d' <;> exact hf.1
      have := fits_get M σ Γ (tl ρ) htail i d (by simpa using h)
      rw [shiftρ_succ]
      exact this

theorem fits_lookupType (M : Interp.{T}) (σ : Nat → Nat) (Γ : LCtx) (ρ : Nat → PSet.{T})
    (hf : Fits M σ Γ ρ) (i : Nat) (A : Expr Nat) (h : lookupType Γ i = some A) :
    ρ i ∈ Ed M (den M σ ρ A) := by
  unfold lookupType at h
  cases hd : Γ.get? i with
  | none => rw [hd] at h; exact Option.noConfusion h
  | some d =>
      rw [hd] at h
      have hm := fits_get M σ Γ ρ hf i d hd
      cases d with
      | assumption B =>
          simp only [Option.some.injEq] at h
          subst h
          rw [den_lift_shift]
          exact hm
      | letBinding B v =>
          simp only [Option.some.injEq] at h
          subst h
          rw [den_lift_shift]
          exact hm

/-- A fitting environment's value at a let-bound variable is its definiens. -/
theorem fits_value_get (M : Interp.{T}) (σ : Nat → Nat) :
    (Γ : LCtx) → (ρ : Nat → PSet.{T}) → Fits M σ Γ ρ → ∀ (i : Nat) (A v : Expr Nat),
      Γ.get? i = some (.letBinding A v) → Equiv (ρ i) (den M σ (shiftρ (i + 1) ρ) v)
  | [], _, _, i, _, _, h => by simp at h
  | d' :: Γ, ρ, hf, 0, A, v, h => by
      simp only [List.get?, Option.some.injEq] at h
      subst h
      exact hf.2.2
  | d' :: Γ, ρ, hf, i + 1, A, v, h => by
      have htail : Fits M σ Γ (tl ρ) := by cases d' <;> exact hf.1
      have := fits_value_get M σ Γ (tl ρ) htail i A v (by simpa using h)
      rw [shiftρ_succ]
      exact this

theorem fits_lookupValue (M : Interp.{T}) (σ : Nat → Nat) (Γ : LCtx) (ρ : Nat → PSet.{T})
    (hf : Fits M σ Γ ρ) (i : Nat) (v : Expr Nat) (h : lookupValue Γ i = some v) :
    Equiv (ρ i) (den M σ ρ v) := by
  unfold lookupValue at h
  cases hd : Γ.get? i with
  | none => rw [hd] at h; exact Option.noConfusion h
  | some d =>
      rw [hd] at h
      cases d with
      | assumption B => exact Option.noConfusion h
      | letBinding B w =>
          simp only [Option.some.injEq] at h
          subst h
          rw [den_lift_shift]
          exact fits_value_get M σ Γ ρ hf i B w hd

/-! ## Levels -/

theorem eval_some (σ : Nat → Nat) : (l : Level) → eval (fun i => some (σ i)) l = some (evalTotal σ l)
  | .zero => rfl
  | .succ l => by simp [eval, evalTotal, eval_some σ l]
  | .max a b => by simp [eval, evalTotal, eval_some σ a, eval_some σ b]
  | .imax a b => by
      simp only [eval, evalTotal, eval_some σ a, eval_some σ b, Option.bind_some]
      by_cases h : evalTotal σ b = 0 <;> simp [h]
  | .param i => rfl

theorem evalTotal_eq_of_eqN (σ : Nat → Nat) {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    evalTotal σ l₁ = evalTotal σ l₂ := by
  have := h (fun i => some (σ i))
  rw [eval_some, eval_some] at this
  exact Option.some.inj this

theorem map_evalTotal_of_eqNList (σ : Nat → Nat) :
    {ls ls' : List Level} → eqNList ls ls' → ls.map (evalTotal σ) = ls'.map (evalTotal σ)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, t⟩ => by
      simp only [List.map_cons, evalTotal_eq_of_eqN σ h, map_evalTotal_of_eqNList σ t]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-! ## Values of the rules -/

theorem tyv_ne_pempty (S : PSet.{T}) : ¬ Equiv (tyv S) pempty := fun h =>
  not_mem_pempty (mem_congr_right h (mem_pair.mpr (Or.inl Equiv.rfl)))

theorem imax_le {a b N : Nat} (ha : a ≤ N) (hb : b ≤ N) : (if b = 0 then 0 else max a b) ≤ N := by
  split
  · exact Nat.zero_le _
  · exact Nat.max_le.mpr ⟨ha, hb⟩

section Rules

variable {M : Interp.{T}} {N : Nat} {Lvl : Nat → PSet.{T} → Prop} (hG : Good M N Lvl)
include hG

theorem U_dich {k : Nat} (hk : k ≤ N) : Dich (M.U k) := Or.inr fun h => by
  obtain ⟨S, _, he⟩ := (hG.U_iff hk pempty).mp h
  exact tyv_ne_pempty S he.symm

theorem ed_sortU {k : Nat} (hk : k ≤ N) : Equiv (Ed M (tyv (M.U k))) (M.U k) :=
  ed_tyv M (U_dich hG hk)

theorem ed_of_lvl {k : Nat} {S x : PSet.{T}} (hS : Lvl k S) (hx : Equiv x (tyv S)) :
    Equiv (Ed M x) S :=
  (ed_congr M hx).trans (ed_tyv M (hG.dich hS))

/-- A universe is an element of the next one. -/
theorem sort_mem {k : Nat} (hk : k + 1 ≤ N) : tyv (M.U k) ∈ Ed M (tyv (M.U (k + 1))) :=
  mem_congr_right (ed_sortU hG hk).symm
    ((hG.U_iff hk _).mpr ⟨M.U k, hG.univ hk, Equiv.rfl⟩)

/-- Product formation: a product of a level-`a` domain and level-`b` fibres
is a level-`imax a b` type. -/
theorem pi_mem {a b : Nat} (ha : a ≤ N) (hb : b ≤ N) {A : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hA : A ∈ M.U a) (hfib : ∀ x, x ∈ Ed M A → B x ∈ M.U b) :
    piVal M A B ∈ M.U (if b = 0 then 0 else max a b) := by
  obtain ⟨SA, hSA, hAe⟩ := (hG.U_iff ha A).mp hA
  have eA : Equiv (Ed M A) SA := ed_of_lvl hG hSA hAe
  have fib : ∀ x, x ∈ Ed M A → ∃ S, Lvl b S ∧ Equiv (Ed M (B x)) S := fun x hx => by
    obtain ⟨S, hS, he⟩ := (hG.U_iff hb _).mp (hfib x hx)
    exact ⟨S, hS, ed_of_lvl hG hS he⟩
  have hBe : ∀ x x', Equiv x x' → Equiv (Ed M (B x)) (Ed M (B x')) := fun x x' h => ed_congr M (hB x x' h)
  have hm : (if b = 0 then 0 else max a b) ≤ N := imax_le ha hb
  refine (hG.U_iff hm _).mpr ⟨_, ?_, Equiv.rfl⟩
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos rfl]
    have hP : PiProp M A B := fun x hx y hy => by
      obtain ⟨S, hS, he⟩ := fib x hx
      exact hG.lvl0.mp hS y (mem_congr_right he hy)
    rw [cond_pos hP]
    exact hG.lvl0.mpr fun y hy => (mem_tv.mp hy).2
  · rw [if_neg hb0]
    have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
    have hm1 : 1 ≤ max a b := Nat.le_trans hb1 (Nat.le_max_right a b)
    have hmN : max a b ≤ N := Nat.max_le.mpr ⟨ha, hb⟩
    cases hd : M.dec (PiProp M A B) with
    | isTrue hP =>
      rw [cond_pos hP]
      exact hG.prop hm1 hmN fun y hy => (mem_tv.mp hy).2
    | isFalse hP =>
      rw [cond_neg hP]
      refine hG.pi hm1 hmN ?_ hBe ?_
      · by_cases ha0 : a = 0
        · subst ha0
          exact hG.congr (hG.prop hm1 hmN fun y hy => hG.lvl0.mp hSA y hy) eA.symm
        · exact hG.congr (hG.mono (Nat.pos_of_ne_zero ha0) (Nat.le_max_left a b) hmN hSA) eA.symm
      · intro x hx
        obtain ⟨S, hS, he⟩ := fib x hx
        exact hG.congr (hG.mono hb1 (Nat.le_max_right a b) hmN hS) he.symm

end Rules

/-- Abstractions land in the product of their body's types. -/
theorem lam_mem (M : Interp.{T}) {A : PSet.{T}} {b B : PSet.{T} → PSet.{T}}
    (hb : ∀ x x', Equiv x x' → Equiv (b x) (b x')) (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hval : ∀ x, x ∈ Ed M A → b x ∈ Ed M (B x)) : lamVal M A b ∈ Ed M (piVal M A B) := by
  haveI := M.dec
  refine mem_congr_right (ed_piVal M A B hB).symm ?_
  by_cases hP : PiProp M A B
  · rw [cond_pos hP]
    have hL : LamProof M A b := fun x hx => hP x hx _ (hval x hx)
    show cond M.dec (LamProof M A b) pempty (mkLam b (Ed M A)) ∈ _
    rw [cond_pos hL]
    exact mem_tv.mpr ⟨fun x hx => mem_congr_left (hL x hx) (hval x hx), Equiv.rfl⟩
  · rw [cond_neg hP]
    have hL : ¬ LamProof M A b := fun hL => hP fun x hx y hy => by
      rcases dich_ed M (B x) with h | h
      · exact h y hy
      · exact (h (mem_congr_left (hL x hx) (hval x hx))).elim
    show cond M.dec (LamProof M A b) pempty (mkLam b (Ed M A)) ∈ _
    rw [cond_neg hL]
    exact mkLam_mem_piSet hb (fun x x' h => ed_congr M (hB x x' h)) hval

theorem fapp_pempty (a : PSet.{T}) : Equiv (fapp pempty a) pempty :=
  ext fun z => ⟨fun hz => by
      obtain ⟨t, ht, _⟩ := mem_sUnion.mp hz
      obtain ⟨u, hu, _⟩ := mem_sUnion.mp (mem_sep_subset ht)
      obtain ⟨w, hw, _⟩ := mem_sUnion.mp hu
      exact (not_mem_pempty hw).elim,
    fun hz => (not_mem_pempty hz).elim⟩

/-- Applications land in the fibre. -/
theorem app_mem (M : Interp.{T}) {A f a : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hf : f ∈ Ed M (piVal M A B)) (ha : a ∈ Ed M A) : fapp f a ∈ Ed M (B a) := by
  haveI := M.dec
  have hf' := mem_congr_right (ed_piVal M A B hB) hf
  by_cases hP : PiProp M A B
  · rw [cond_pos hP] at hf'
    obtain ⟨hφ, hf0⟩ := mem_tv.mp hf'
    exact mem_congr_left ((fapp_pempty a).symm.trans (fapp_congr hf0.symm Equiv.rfl)) (hφ a ha)
  · rw [cond_neg hP] at hf'
    exact fapp_mem_piSet (fun x x' h => ed_congr M (hB x x' h)) hf' ha

/-- β in the model. -/
theorem beta_val (M : Interp.{T}) {A a : PSet.{T}} {b : PSet.{T} → PSet.{T}}
    (hb : ∀ x x', Equiv x x' → Equiv (b x) (b x')) (ha : a ∈ Ed M A) :
    Equiv (fapp (lamVal M A b) a) (b a) := by
  cases hd : M.dec (LamProof M A b) with
  | isTrue hL =>
      show Equiv (fapp (cond M.dec _ _ _) a) _
      rw [cond_pos hL]
      exact (fapp_pempty a).trans (hL a ha).symm
  | isFalse hL =>
      show Equiv (fapp (cond M.dec _ _ _) a) _
      rw [cond_neg hL]
      exact fapp_mkLam hb ha

theorem mem_bigUnion_image {A a b : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (ha : a ∈ A) (hb : b ∈ B a) :
    b ∈ sUnion (sImage B A) := by
  obtain ⟨i, hi⟩ := ha
  exact mem_sUnion.mpr ⟨B (A.Func i), ⟨i, Equiv.refl _⟩, mem_congr_right (hB _ _ hi).symm hb⟩

theorem isFuncOn_of_dep {A f : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (h : isFuncOnDep A B f) :
    isFuncOn A (sUnion (sImage B A)) f := by
  refine ⟨fun a ha => ?_, fun p hp => ?_, h.2.2⟩
  · obtain ⟨b, hb, hab⟩ := h.1 a ha
    exact ⟨b, mem_bigUnion_image hB ha hb, hab⟩
  · obtain ⟨a, ha, b, hb, he⟩ := h.2.1 p hp
    exact ⟨a, ha, b, mem_bigUnion_image hB ha hb, he⟩

/-- η in the model. -/
theorem eta_val (M : Interp.{T}) {A f : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (hf : f ∈ Ed M (piVal M A B)) :
    Equiv (lamVal M A (fun x => fapp f x)) f := by
  have hf' := mem_congr_right (ed_piVal M A B hB) hf
  have hBe : ∀ x x', Equiv x x' → Equiv (Ed M (B x)) (Ed M (B x')) := fun x x' h => ed_congr M (hB x x' h)
  cases hd : M.dec (PiProp M A B) with
  | isTrue hP =>
      rw [cond_pos hP] at hf'
      obtain ⟨_, hf0⟩ := mem_tv.mp hf'
      have hL : LamProof M A (fun x => fapp f x) := fun x _ =>
        (fapp_congr hf0 Equiv.rfl).trans (fapp_pempty x)
      show Equiv (cond M.dec _ _ _) _
      rw [cond_pos hL]
      exact hf0.symm
  | isFalse hP =>
      rw [cond_neg hP] at hf'
      have happ : ∀ x, x ∈ Ed M A → fapp f x ∈ Ed M (B x) := fun x hx => fapp_mem_piSet hBe hf' hx
      have hL : ¬ LamProof M A (fun x => fapp f x) := fun hL => hP fun x hx y hy => by
        rcases dich_ed M (B x) with h | h
        · exact h y hy
        · exact (h (mem_congr_left (hL x hx) (happ x hx))).elim
      show Equiv (cond M.dec _ _ _) _
      rw [cond_neg hL]
      exact mkLam_fapp (isFuncOn_of_dep hBe (isFuncOnDep_of_mem_piSet hBe hf'))

/-- `mkLam` congruence, using the map only on the domain. -/
theorem mkLam_congr_on {g g' : PSet.{T} → PSet.{T}} {A A' : PSet.{T}}
    (hg : ∀ x x', Equiv x x' → Equiv (g x) (g x')) (hA : Equiv A A')
    (hgg : ∀ x, x ∈ A → Equiv (g x) (g' x)) : Equiv (mkLam g A) (mkLam g' A') := by
  have key : ∀ (i : A.Idx) (j : A'.Idx), Equiv (A.Func i) (A'.Func j) →
      Equiv (ordPair (A.Func i) (g (A.Func i))) (ordPair (A'.Func j) (g' (A'.Func j))) := by
    intro i j hij
    have hjA : A'.Func j ∈ A := mem_congr_right hA.symm ⟨j, Equiv.refl _⟩
    exact ordPair_congr hij ((hg _ _ hij).trans (hgg _ hjA))
  apply ext; intro p; constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hA.exists_mem_left i
    exact ⟨j, (key i j hj).symm.trans hi⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hA.exists_mem_right j
    exact ⟨i, (key i j hi).trans hj⟩

theorem mem_piSet_of_dep {A f : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (hfun : isFuncOnDep A B f) : f ∈ piSet A B := by
  have hpow : f ∈ powerset (prod A (sUnion (sImage B A))) := by
    refine mem_powerset.mpr fun p hp => ?_
    obtain ⟨a, ha, b, hb, hpe⟩ := hfun.2.1 p hp
    exact mem_prod.mpr ⟨a, ha, b, mem_bigUnion_image hB ha hb, hpe⟩
  obtain ⟨i, hi⟩ := hpow
  exact mem_sep.mpr ⟨i, isFuncOnDep_equiv Equiv.rfl hB hi.symm hfun, hi⟩

theorem isFuncOnDep_congr_on {A A' f : PSet.{T}} {B B' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hBB : ∀ x, x ∈ A → Equiv (B x) (B' x)) (h : isFuncOnDep A B f) : isFuncOnDep A' B' f := by
  refine ⟨fun a ha => ?_, fun p hp => ?_, h.2.2⟩
  · have ha' := mem_congr_right hA.symm ha
    obtain ⟨b, hb, hab⟩ := h.1 a ha'
    exact ⟨b, mem_congr_right (hBB a ha') hb, hab⟩
  · obtain ⟨a, ha, b, hb, he⟩ := h.2.1 p hp
    exact ⟨a, mem_congr_right hA ha, b, mem_congr_right (hBB a ha) hb, he⟩

theorem piSet_congr_on {A A' : PSet.{T}} {B B' : PSet.{T} → PSet.{T}} (hA : Equiv A A')
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (hBB : ∀ x, x ∈ A → Equiv (B x) (B' x)) : Equiv (piSet A B) (piSet A' B') := by
  have hBB' : ∀ x, x ∈ A' → Equiv (B' x) (B x) := fun x hx => (hBB x (mem_congr_right hA.symm hx)).symm
  exact ext fun f => ⟨fun hf => mem_piSet_of_dep hB' (isFuncOnDep_congr_on hA hB hBB
      (isFuncOnDep_of_mem_piSet hB hf)),
    fun hf => mem_piSet_of_dep hB (isFuncOnDep_congr_on hA.symm hB' hBB'
      (isFuncOnDep_of_mem_piSet hB' hf))⟩

theorem lamVal_congr_on (M : Interp.{T}) {A A' : PSet.{T}} {b b' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hb : ∀ x x', Equiv x x' → Equiv (b x) (b x'))
    (hbb : ∀ x, x ∈ Ed M A → Equiv (b x) (b' x)) : Equiv (lamVal M A b) (lamVal M A' b') := by
  have eA := ed_congr M hA
  refine cond_congr ⟨fun h x hx => ?_, fun h x hx => ?_⟩ Equiv.rfl (mkLam_congr_on hb eA hbb)
  · have hx' := mem_congr_right eA.symm hx
    exact (hbb x hx').symm.trans (h x hx')
  · exact (hbb x hx).trans (h x (mem_congr_right eA hx))

theorem piVal_congr_on (M : Interp.{T}) {A A' : PSet.{T}} {B B' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (hBB : ∀ x, x ∈ Ed M A → Equiv (B x) (B' x)) : Equiv (piVal M A B) (piVal M A' B') := by
  have eA := ed_congr M hA
  have eB : ∀ x, x ∈ Ed M A → Equiv (Ed M (B x)) (Ed M (B' x)) := fun x hx => ed_congr M (hBB x hx)
  refine tyv_congr (cond_congr ?_ ?_ (piSet_congr_on eA (fun x x' h => ed_congr M (hB x x' h))
    (fun x x' h => ed_congr M (hB' x x' h)) eB))
  · constructor
    · intro h x hx y hy
      have hx' := mem_congr_right eA.symm hx
      exact h x hx' y (mem_congr_right (eB x hx').symm hy)
    · intro h x hx y hy
      exact h x (mem_congr_right eA hx) y (mem_congr_right (eB x hx) hy)
  · refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => by
        have hx' := mem_congr_right eA.symm hx
        exact mem_congr_right (eB x hx') (hφ x hx'), hz⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => mem_congr_right (eB x hx).symm (hφ x (mem_congr_right eA hx)), hz⟩

end PSet

end Rcic.F3