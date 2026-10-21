import rcic.RcicAnnSubstCalc
import rcic.RcicAnnCtxMorph
import rcic.RcicAnnWk
import rcic.RcicAnnStep

/-!
# M2-e (1) — parallel substitution on the copy, and its algebra

The fundamental theorem is stated over VALID SUBSTITUTIONS in worlds
(`research/rcic/rows-m1/M2_PLAN.md` §2): a parallel substitution `σ : SubstA`
sends every variable of the source context to a term of the target context, so
the theorem's conclusion lives in the target context and the binder arms extend
`σ` by the related arguments (`SubstA.cons`). The algebra, all by induction on
the expression with the binder case through `SubstA.up`:

* `substA_ext` / `substA_id`     — pointwise-equal substitutions act equally; the identity
* `liftA_substA`                 — `liftA c 1 (substA σ e) = substA (liftA c 1 ∘ σ) e`
* `substA_liftA`                 — `substA σ (liftA c 1 e) = substA (σ ∘ shift at c) e`
* `instantiateA_substA`          — `instantiateA j a (substA σ e) = substA (instantiateA j a ∘ σ) e`
* `substA_substA`                — composition
* `instantiateA_eq_substA`       — a single instantiation is a parallel substitution
* `substA_instantiate0A`         — THE ONE THE `app`/`beta`/`zeta` ARMS CONSUME:
                                   `substA σ (instantiate0A a B) = instantiate0A (substA σ a) (substA σ.up B)`
* `instantiate0A_substA_up`      — `instantiate0A a (substA σ.up B) = substA (σ.cons a) B`
* `wkExprA_substA`               — a world acts on the images
* `substA_closed` / `wkExprA_closed` — a lift-closed term is fixed (member types and bodies
                                   under `EnvClosedA`, `natExpandA`)

No `sorry`, no new axiom; `funext` is not used (everything is `substA_ext`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- a parallel substitution: every variable to a term. -/
abbrev SubstA := Nat → ExprA

namespace SubstA

/-- the identity. -/
def id : SubstA := fun i => .bvar i

/-- under one binder: the bound variable stays, the images move up. -/
def up (σ : SubstA) : SubstA
  | 0 => .bvar 0
  | i + 1 => liftA 0 1 (σ i)

/-- extension by a term for the variable `0`. -/
def cons (a : ExprA) (σ : SubstA) : SubstA
  | 0 => a
  | i + 1 => σ i

/-- precomposition with the shift at cutoff `c` (what `liftA c 1` does to indices). -/
def shiftAt (c : Nat) (σ : SubstA) : SubstA := fun i => if c ≤ i then σ (i + 1) else σ i

/-- the single substitution `instantiateA j a` as a parallel one. -/
def single (j : Nat) (a : ExprA) : SubstA := fun i =>
  if i = j then a else if j < i then .bvar (i - 1) else .bvar i

@[simp] theorem up_zero (σ : SubstA) : σ.up 0 = .bvar 0 := rfl
@[simp] theorem up_succ (σ : SubstA) (i : Nat) : σ.up (i + 1) = liftA 0 1 (σ i) := rfl
@[simp] theorem cons_zero (a : ExprA) (σ : SubstA) : cons a σ 0 = a := rfl
@[simp] theorem cons_succ (a : ExprA) (σ : SubstA) (i : Nat) : cons a σ (i + 1) = σ i := rfl
@[simp] theorem id_apply (i : Nat) : id i = .bvar i := rfl

theorem up_ext {σ τ : SubstA} (h : ∀ i, σ i = τ i) : ∀ i, σ.up i = τ.up i
  | 0 => rfl
  | i + 1 => by simp only [up_succ, h i]

theorem id_up : ∀ i, SubstA.id.up i = SubstA.id i
  | 0 => rfl
  | i + 1 => by rw [up_succ, id_apply, id_apply, liftA_bvar]; simp [shiftIdx]

/-- `shiftAt (c+1)` under a binder is `shiftAt c` lifted. -/
theorem shiftAt_succ_up (c : Nat) (σ : SubstA) :
    ∀ i, shiftAt (c + 1) σ.up i = (shiftAt c σ).up i
  | 0 => by
      show (if c + 1 ≤ 0 then σ.up (0 + 1) else σ.up 0) = ExprA.bvar 0
      rw [if_neg (Nat.not_succ_le_zero c)]; rfl
  | i + 1 => by
      simp only [shiftAt, up_succ, Nat.add_le_add_iff_right]
      by_cases h : c ≤ i <;> simp [h]

/-- `single (j+1)` of the lifted replacement is `single j` lifted. -/
theorem single_up (j : Nat) (a : ExprA) :
    ∀ i, (single j a).up i = single (j + 1) (liftA 0 1 a) i
  | 0 => by
      show ExprA.bvar 0 = (if 0 = j + 1 then liftA 0 1 a else if j + 1 < 0 then ExprA.bvar (0 - 1) else ExprA.bvar 0)
      rw [if_neg (by omega), if_neg (by omega)]
  | i + 1 => by
      simp only [up_succ, single]
      by_cases h1 : i = j
      · subst h1; simp
      · rw [if_neg h1, if_neg (fun h => h1 (Nat.succ.inj h))]
        by_cases h2 : j < i
        · rw [if_pos h2, if_pos (Nat.succ_lt_succ h2), liftA_bvar]
          simp only [shiftIdx, Nat.zero_le, if_true]
          congr 1; omega
        · rw [if_neg h2, if_neg (fun h => h2 (Nat.lt_of_succ_lt_succ h)), liftA_bvar]
          simp only [shiftIdx, Nat.zero_le, if_true]

end SubstA

/-- apply a parallel substitution. -/
def substA (σ : SubstA) : ExprA → ExprA
  | .bvar i => σ i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (substA σ f) (substA σ x)
  | .lam a u b => .lam (substA σ a) u (substA σ.up b)
  | .pi a u b v => .pi (substA σ a) u (substA σ.up b) v
  | .letE a w b => .letE (substA σ a) (substA σ w) (substA σ.up b)
  | .lit t => .lit t

@[simp] theorem substA_bvar (σ : SubstA) (i : Nat) : substA σ (.bvar i) = σ i := rfl
@[simp] theorem substA_sort (σ : SubstA) (l : Level) : substA σ (.sort l) = .sort l := rfl
@[simp] theorem substA_const (σ : SubstA) (r : Nat) (ls : List Level) :
    substA σ (.const r ls) = .const r ls := rfl
@[simp] theorem substA_app (σ : SubstA) (f x : ExprA) :
    substA σ (.app f x) = .app (substA σ f) (substA σ x) := rfl
@[simp] theorem substA_lam (σ : SubstA) (a : ExprA) (u : Level) (b : ExprA) :
    substA σ (.lam a u b) = .lam (substA σ a) u (substA σ.up b) := rfl
@[simp] theorem substA_pi (σ : SubstA) (a : ExprA) (u : Level) (b : ExprA) (v : Level) :
    substA σ (.pi a u b v) = .pi (substA σ a) u (substA σ.up b) v := rfl
@[simp] theorem substA_letE (σ : SubstA) (a w b : ExprA) :
    substA σ (.letE a w b) = .letE (substA σ a) (substA σ w) (substA σ.up b) := rfl
@[simp] theorem substA_lit (σ : SubstA) (t : Nat) : substA σ (.lit t) = .lit t := rfl

/-! ## the algebra -/

theorem substA_ext {σ τ : SubstA} (h : ∀ i, σ i = τ i) : (e : ExprA) → substA σ e = substA τ e
  | .bvar i => h i
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substA, substA_ext h f, substA_ext h x]
  | .lam a _ b => by simp only [substA, substA_ext h a, substA_ext (SubstA.up_ext h) b]
  | .pi a _ b _ => by simp only [substA, substA_ext h a, substA_ext (SubstA.up_ext h) b]
  | .letE a w b => by
      simp only [substA, substA_ext h a, substA_ext h w, substA_ext (SubstA.up_ext h) b]
  | .lit _ => rfl

theorem substA_id : (e : ExprA) → substA SubstA.id e = e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substA, substA_id f, substA_id x]
  | .lam a _ b => by rw [substA, substA_id a, substA_ext SubstA.id_up b, substA_id b]
  | .pi a _ b _ => by rw [substA, substA_id a, substA_ext SubstA.id_up b, substA_id b]
  | .letE a w b => by rw [substA, substA_id a, substA_id w, substA_ext SubstA.id_up b, substA_id b]
  | .lit _ => rfl

/-- lifting the result lifts the images. -/
theorem liftA_substA (c : Nat) (σ : SubstA) :
    (e : ExprA) → liftA c 1 (substA σ e) = substA (fun i => liftA c 1 (σ i)) e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substA, liftA, liftA_substA c σ f, liftA_substA c σ x]
  | .lam a _ b => by
      simp only [substA, liftA, liftA_substA c σ a, liftA_substA (c + 1) σ.up b]
      exact congrArg _ (substA_ext (liftA_up c σ) b)
  | .pi a _ b _ => by
      simp only [substA, liftA, liftA_substA c σ a, liftA_substA (c + 1) σ.up b]
      rw [substA_ext (liftA_up c σ) b]
  | .letE a w b => by
      simp only [substA, liftA, liftA_substA c σ a, liftA_substA c σ w, liftA_substA (c + 1) σ.up b]
      exact congrArg _ (substA_ext (liftA_up c σ) b)
  | .lit _ => rfl
where
  /-- the binder case's pointwise identity. -/
  liftA_up (c : Nat) (σ : SubstA) : ∀ i, liftA (c + 1) 1 (σ.up i) = SubstA.up (fun i => liftA c 1 (σ i)) i
    | 0 => by rw [SubstA.up_zero, liftA_bvar, shiftIdx_succ_zero]; rfl
    | i + 1 => by
        simp only [SubstA.up_succ]
        rw [liftA_liftA_permute 1 1 c 0 (Nat.zero_le c), show 1 + c = c + 1 from Nat.add_comm 1 c]

/-- substituting a lifted term precomposes with the shift. -/
theorem substA_liftA (c : Nat) (σ : SubstA) :
    (e : ExprA) → substA σ (liftA c 1 e) = substA (SubstA.shiftAt c σ) e
  | .bvar i => by
      rw [liftA_bvar]; unfold SubstA.shiftAt shiftIdx
      by_cases h : c ≤ i <;> simp [h]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substA, liftA, substA_liftA c σ f, substA_liftA c σ x]
  | .lam a _ b => by
      simp only [substA, liftA, substA_liftA c σ a, substA_liftA (c + 1) σ.up b]
      exact congrArg _ (substA_ext (SubstA.shiftAt_succ_up c σ) b)
  | .pi a _ b _ => by
      simp only [substA, liftA, substA_liftA c σ a, substA_liftA (c + 1) σ.up b]
      rw [substA_ext (SubstA.shiftAt_succ_up c σ) b]
  | .letE a w b => by
      simp only [substA, liftA, substA_liftA c σ a, substA_liftA c σ w, substA_liftA (c + 1) σ.up b]
      exact congrArg _ (substA_ext (SubstA.shiftAt_succ_up c σ) b)
  | .lit _ => rfl

/-- under a binder, a lifted term is substituted by the unlifted substitution, lifted. -/
theorem substA_up_liftA (σ : SubstA) (e : ExprA) :
    substA σ.up (liftA 0 1 e) = liftA 0 1 (substA σ e) := by
  rw [substA_liftA, liftA_substA]
  exact substA_ext (fun i => by simp [SubstA.shiftAt]) e

/-- `m` binders up. -/
def upNA : Nat → SubstA → SubstA
  | 0, σ => σ
  | m + 1, σ => upNA m σ.up

theorem upNA_succ : (m : Nat) → (σ : SubstA) → upNA (m + 1) σ = (upNA m σ).up
  | 0, _ => rfl
  | m + 1, σ => upNA_succ m σ.up

/-- the variables of the `m` binders stay. -/
theorem upNA_lt : (m : Nat) → (σ : SubstA) → (i : Nat) → i < m → upNA m σ i = .bvar i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, σ, i, h => by
      rw [upNA_succ]
      cases i with
      | zero => rfl
      | succ i =>
          rw [SubstA.up_succ, upNA_lt m σ i (by omega), liftA_bvar]
          simp [shiftIdx]

/-- under `m` binders, a term lifted past them is substituted by the substitution, then lifted. -/
theorem substA_upNA_liftA : (m : Nat) → (σ : SubstA) → (e : ExprA) →
    substA (upNA m σ) (liftA 0 m e) = liftA 0 m (substA σ e)
  | 0, σ, e => by simp only [liftA_zero]; rfl
  | m + 1, σ, e => by
      rw [upNA_succ, ← liftA_liftA_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _) e, substA_up_liftA,
        substA_upNA_liftA m σ e, liftA_liftA_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _)]

/-- substituting a lifted term reads the substitution's tail. -/
theorem substA_liftA_succ (σ : SubstA) (e : ExprA) :
    substA σ (liftA 0 1 e) = substA (fun i => σ (i + 1)) e := by
  rw [substA_liftA]
  exact substA_ext (fun i => by simp [SubstA.shiftAt]) e

/-- substituting a lifted term past an extension reads the substitution extended. -/
theorem substA_cons_liftA (a : ExprA) (σ : SubstA) (e : ExprA) :
    substA (SubstA.cons a σ) (liftA 0 1 e) = substA σ e :=
  substA_liftA_succ (SubstA.cons a σ) e

/-- instantiating the result instantiates the images. -/
theorem instantiateA_substA (j : Nat) (a : ExprA) (σ : SubstA) :
    (e : ExprA) → instantiateA j a (substA σ e) = substA (fun i => instantiateA j a (σ i)) e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [substA, instantiateA, instantiateA_substA j a σ f, instantiateA_substA j a σ x]
  | .lam a' _ b => by
      simp only [substA, instantiateA, instantiateA_substA j a σ a',
        instantiateA_substA (j + 1) (liftA 0 1 a) σ.up b]
      exact congrArg _ (substA_ext (inst_up j a σ) b)
  | .pi a' _ b _ => by
      simp only [substA, instantiateA, instantiateA_substA j a σ a',
        instantiateA_substA (j + 1) (liftA 0 1 a) σ.up b]
      rw [substA_ext (inst_up j a σ) b]
  | .letE a' w b => by
      simp only [substA, instantiateA, instantiateA_substA j a σ a', instantiateA_substA j a σ w,
        instantiateA_substA (j + 1) (liftA 0 1 a) σ.up b]
      exact congrArg _ (substA_ext (inst_up j a σ) b)
  | .lit _ => rfl
where
  inst_up (j : Nat) (a : ExprA) (σ : SubstA) :
      ∀ i, instantiateA (j + 1) (liftA 0 1 a) (σ.up i) = SubstA.up (fun i => instantiateA j a (σ i)) i
    | 0 => by
        show (if 0 = j + 1 then liftA 0 1 a else if j + 1 < 0 then ExprA.bvar (0 - 1) else ExprA.bvar 0)
          = ExprA.bvar 0
        rw [if_neg (by omega), if_neg (by omega)]
    | i + 1 => by
        simp only [SubstA.up_succ]
        rw [liftA_instantiateA_high 1 0 j a (Nat.zero_le j), show 1 + j = j + 1 from Nat.add_comm 1 j]

/-- composition. -/
theorem substA_substA (τ σ : SubstA) :
    (e : ExprA) → substA τ (substA σ e) = substA (fun i => substA τ (σ i)) e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substA, substA_substA τ σ f, substA_substA τ σ x]
  | .lam a _ b => by
      simp only [substA, substA_substA τ σ a, substA_substA τ.up σ.up b]
      exact congrArg _ (substA_ext (comp_up τ σ) b)
  | .pi a _ b _ => by
      simp only [substA, substA_substA τ σ a, substA_substA τ.up σ.up b]
      rw [substA_ext (comp_up τ σ) b]
  | .letE a w b => by
      simp only [substA, substA_substA τ σ a, substA_substA τ σ w, substA_substA τ.up σ.up b]
      exact congrArg _ (substA_ext (comp_up τ σ) b)
  | .lit _ => rfl
where
  comp_up (τ σ : SubstA) : ∀ i, substA τ.up (σ.up i) = SubstA.up (fun i => substA τ (σ i)) i
    | 0 => rfl
    | i + 1 => by simp only [SubstA.up_succ]; exact substA_up_liftA τ (σ i)

/-- a single instantiation is a parallel substitution. -/
theorem instantiateA_eq_substA (j : Nat) (a : ExprA) :
    (e : ExprA) → instantiateA j a e = substA (SubstA.single j a) e
  | .bvar i => by simp only [instantiateA, substA, SubstA.single]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [instantiateA, substA, instantiateA_eq_substA j a f, instantiateA_eq_substA j a x]
  | .lam a' _ b => by
      simp only [instantiateA, substA, instantiateA_eq_substA j a a',
        instantiateA_eq_substA (j + 1) (liftA 0 1 a) b]
      exact congrArg _ (substA_ext (SubstA.single_up j a) b).symm
  | .pi a' _ b _ => by
      simp only [instantiateA, substA, instantiateA_eq_substA j a a',
        instantiateA_eq_substA (j + 1) (liftA 0 1 a) b]
      rw [substA_ext (SubstA.single_up j a) b]
  | .letE a' w b => by
      simp only [instantiateA, substA, instantiateA_eq_substA j a a', instantiateA_eq_substA j a w,
        instantiateA_eq_substA (j + 1) (liftA 0 1 a) b]
      exact congrArg _ (substA_ext (SubstA.single_up j a) b).symm
  | .lit _ => rfl

/-- THE ONE THE ARMS CONSUME: substitution passes through a `0`-instantiation. -/
theorem substA_instantiate0A (σ : SubstA) (a B : ExprA) :
    substA σ (instantiate0A a B) = instantiate0A (substA σ a) (substA σ.up B) := by
  rw [instantiate0A, instantiateA_eq_substA, substA_substA, instantiate0A, instantiateA_substA]
  exact substA_ext (fun i => by
    cases i with
    | zero => simp [SubstA.single, instantiateA]
    | succ i => simp [SubstA.single, instantiateA_liftA_id]) B

/-- instantiating under an extended substitution is substituting the extension. -/
theorem instantiate0A_substA_up (σ : SubstA) (a B : ExprA) :
    instantiate0A a (substA σ.up B) = substA (SubstA.cons a σ) B := by
  rw [instantiate0A, instantiateA_substA]
  exact substA_ext (fun i => by
    cases i with
    | zero => simp [instantiateA]
    | succ i => simp [instantiateA_liftA_id]) B

/-- a world acts on the images. -/
theorem wkExprA_substA : (ρ : WkSpecA) → (σ : SubstA) → (e : ExprA) →
    wkExprA ρ (substA σ e) = substA (fun i => wkExprA ρ (σ i)) e
  | [], _, _ => rfl
  | (_, c) :: ρ, σ, e => by
      simp only [wkExprA]
      rw [liftA_substA, wkExprA_substA ρ]

/-! ## closed terms -/

/-- lift-closed above `c` and the substitution is the identity below `c`: fixed. -/
theorem substA_closed_aux : (e : ExprA) → (c : Nat) → (∀ k, c ≤ k → liftA k 1 e = e) →
    (σ : SubstA) → (∀ i, i < c → σ i = .bvar i) → substA σ e = e
  | .bvar i, c, h, σ, hσ => by
      by_cases hic : i < c
      · exact hσ i hic
      · exfalso
        have := h c (Nat.le_refl c)
        rw [liftA_bvar] at this
        have := ExprA.bvar.inj this
        unfold shiftIdx at this
        rw [if_pos (Nat.le_of_not_lt hic)] at this
        omega
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .app f x, c, h, σ, hσ => by
      have hf : ∀ k, c ≤ k → liftA k 1 f = f := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.app.injEq] at this; exact this.1
      have hx : ∀ k, c ≤ k → liftA k 1 x = x := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.app.injEq] at this; exact this.2
      simp only [substA, substA_closed_aux f c hf σ hσ, substA_closed_aux x c hx σ hσ]
  | .lam a u b, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → liftA k 1 a = a := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.lam.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → liftA k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [liftA, ExprA.lam.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2.2
      simp only [substA, substA_closed_aux a c ha σ hσ,
        substA_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
  | .pi a u b v, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → liftA k 1 a = a := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.pi.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → liftA k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [liftA, ExprA.pi.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2.2.1
      simp only [substA, substA_closed_aux a c ha σ hσ,
        substA_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
  | .letE a w b, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → liftA k 1 a = a := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.letE.injEq] at this; exact this.1
      have hw : ∀ k, c ≤ k → liftA k 1 w = w := fun k hk => by
        have := h k hk; simp only [liftA, ExprA.letE.injEq] at this; exact this.2.1
      have hb : ∀ k, c + 1 ≤ k → liftA k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [liftA, ExprA.letE.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2.2
      simp only [substA, substA_closed_aux a c ha σ hσ, substA_closed_aux w c hw σ hσ,
        substA_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
where
  up_below (c : Nat) (σ : SubstA) (hσ : ∀ i, i < c → σ i = .bvar i) :
      ∀ i, i < c + 1 → σ.up i = .bvar i
    | 0, _ => rfl
    | i + 1, hi => by
        rw [SubstA.up_succ, hσ i (Nat.lt_of_succ_lt_succ hi), liftA_bvar]
        simp [shiftIdx]

/-- a lift-closed term is fixed by every substitution. -/
theorem substA_closed {e : ExprA} (h : ∀ k, liftA k 1 e = e) (σ : SubstA) : substA σ e = e :=
  substA_closed_aux e 0 (fun k _ => h k) σ (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- a lift-closed term is fixed by every world. -/
theorem wkExprA_closed {e : ExprA} (h : ∀ k, liftA k 1 e = e) :
    (ρ : WkSpecA) → wkExprA ρ e = e
  | [] => rfl
  | (_, c) :: ρ => by simp only [wkExprA]; rw [h c]; exact wkExprA_closed h ρ

/-- level instantiation preserves lift-closedness. -/
theorem liftA_instantiateLevelsA_closed {e : ExprA} (h : ∀ k, liftA k 1 e = e) (ls : List Level) :
    ∀ k, liftA k 1 (instantiateLevelsA ls e) = instantiateLevelsA ls e := fun k => by
  rw [← instantiateLevelsA_liftA, h k]

/-- the literal expansion is closed. -/
theorem liftA_natExpandA_closed : (t : Nat) → ∀ k, liftA k 1 (natExpandA t) = natExpandA t
  | 0, _ => rfl
  | t + 1, k => by simp only [natExpandA, litSuccA, liftA, liftA_natExpandA_closed t k]

theorem substA_natExpandA (σ : SubstA) (t : Nat) : substA σ (natExpandA t) = natExpandA t :=
  substA_closed (liftA_natExpandA_closed t) σ

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.substA_instantiate0A
#print axioms Rcic.Declarative.Ann.instantiate0A_substA_up
#print axioms Rcic.Declarative.Ann.wkExprA_substA
#print axioms Rcic.Declarative.Ann.substA_closed
#print axioms Rcic.Declarative.Ann.substA_upNA_liftA
