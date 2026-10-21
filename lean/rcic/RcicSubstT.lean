import rcic.RcicTypedEnvEntry
import rcic.RcicParRedSRTyped
import rcic.RcicTypedInvert
import rcic.RcicDTMetaTypedSR
import rcic.RcicLevelCalc

/-!
# B transport — `substT` algebra on the typed judgment

`RcicTypedSubst` owns the single-variable substitution (`hasTyT_substS`);
segment B's cell theorem needs the PARALLEL form in SYNTAX only: the
constructor's field contexts embed the plain field prefix into the full field
prefix by a renaming σ (`ctorFieldsT` writes `idx.map (substT σ)`), so this
module ports `RcicAnnSubst`'s proven algebra to `substT` — the equations the
renaming bridge (`substT σ e` = an iterated `lift`) and the cell's index
transport consume.

* `SubstT.cons` / `SubstT.shiftAt` / `SubstT.single` / `SubstT.upNT` —
  the auxiliary constructors `substT`'s algebra reads.
* `substT_ext`/`substT_id`, `lift_substT`/`substT_lift`/`substT_up_lift`,
  `substT_substT` (composition), `substT_instantiate0` — the `app`/`ArgsTyT`
  equations; `substT_closed` (lift-closed terms are fixed).
* `instantiate_bvar_lift` — `inst0 (bvar j) (lift (j+1) 1 e) = e`.

The judgment-level counterpart (a `SubstTyT` morphism with
`hasTyT_substT`/`convT_substT` mutuals) was tried and REMOVED: `convT_substT`'s
`.letE` arm is unprovable — `ConvT.letE` carries conversion of the bound value
but not its typing, and constructing the morphism's `val` under the let binder
needs `hasTyT_substT` applied to a produced `HasTyT`, which is not a structural
subterm (termination fails). For segment B's renaming σ the transport instead
goes through `.letE`-safe iterated `hasTyTWeaken`/`convTWeaken`/
`argsTyT_weakenUnderTel` (in `RcicIARecIH`), with this module's algebra
supplying the `substT σ e = lift-chain e` syntactic bridge.
-/

namespace Rcic.Declarative

/-! ## `SubstT` constructors the algebra reads (port of `SubstA`) -/

namespace SubstT

/-- extension by a term for the variable `0`. -/
def cons (a : Expr Nat) (σ : SubstT) : SubstT
  | 0 => a
  | i + 1 => σ i

/-- precomposition with the shift at cutoff `c` (what `lift c 1` does to
    indices). -/
def shiftAt (c : Nat) (σ : SubstT) : SubstT := fun i => if c ≤ i then σ (i + 1) else σ i

/-- the single substitution `instantiate j a` as a parallel one. -/
def single (j : Nat) (a : Expr Nat) : SubstT := fun i =>
  if i = j then a else if j < i then .bvar (i - 1) else .bvar i

@[simp] theorem up_zero (σ : SubstT) : σ.up 0 = .bvar 0 := rfl
@[simp] theorem up_succ (σ : SubstT) (i : Nat) : σ.up (i + 1) = lift 0 1 (σ i) := rfl
@[simp] theorem cons_zero (a : Expr Nat) (σ : SubstT) : cons a σ 0 = a := rfl
@[simp] theorem cons_succ (a : Expr Nat) (σ : SubstT) (i : Nat) : cons a σ (i + 1) = σ i := rfl
@[simp] theorem id_apply (i : Nat) : id i = .bvar i := rfl

theorem up_ext {σ τ : SubstT} (h : ∀ i, σ i = τ i) : ∀ i, σ.up i = τ.up i
  | 0 => rfl
  | i + 1 => by simp only [up_succ, h i]

theorem id_up : ∀ i, SubstT.id.up i = SubstT.id i
  | 0 => rfl
  | i + 1 => by rw [up_succ, id_apply, id_apply, lift]; simp

/-- `shiftAt (c+1)` under a binder is `shiftAt c` lifted. -/
theorem shiftAt_succ_up (c : Nat) (σ : SubstT) :
    ∀ i, shiftAt (c + 1) σ.up i = (shiftAt c σ).up i
  | 0 => by
      show (if c + 1 ≤ 0 then σ.up (0 + 1) else σ.up 0) = Expr.bvar 0
      rw [if_neg (Nat.not_succ_le_zero c)]; rfl
  | i + 1 => by
      simp only [shiftAt, up_succ, Nat.add_le_add_iff_right]
      by_cases h : c ≤ i <;> simp [h]

/-- `single (j+1)` of the lifted replacement is `single j` lifted. -/
theorem single_up (j : Nat) (a : Expr Nat) :
    ∀ i, (single j a).up i = single (j + 1) (lift 0 1 a) i
  | 0 => by
      show Expr.bvar 0 = (if 0 = j + 1 then lift 0 1 a else if j + 1 < 0 then Expr.bvar (0 - 1) else Expr.bvar 0)
      rw [if_neg (by omega), if_neg (by omega)]
  | i + 1 => by
      simp only [up_succ, single]
      by_cases h1 : i = j
      · subst h1; simp [lift]
      · rw [if_neg h1, if_neg (fun h => h1 (Nat.succ.inj h))]
        by_cases h2 : j < i
        · rw [if_pos h2, if_pos (Nat.succ_lt_succ h2), lift]
          simp only [Nat.zero_le, if_true]
          congr 1; omega
        · rw [if_neg h2, if_neg (fun h => h2 (Nat.lt_of_succ_lt_succ h)), lift]
          simp only [Nat.zero_le, if_true]

end SubstT

/-! ## the `substT` algebra -/

theorem substT_ext {σ τ : SubstT} (h : ∀ i, σ i = τ i) : (e : Expr Nat) → substT σ e = substT τ e
  | .bvar i => h i
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substT, substT_ext h f, substT_ext h x]
  | .lam a b => by simp only [substT, substT_ext h a, substT_ext (SubstT.up_ext h) b]
  | .pi a b => by simp only [substT, substT_ext h a, substT_ext (SubstT.up_ext h) b]
  | .letE a w b => by
      simp only [substT, substT_ext h a, substT_ext h w, substT_ext (SubstT.up_ext h) b]
  | .lit _ => rfl

theorem substT_id : (e : Expr Nat) → substT SubstT.id e = e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substT, substT_id f, substT_id x]
  | .lam a b => by rw [substT, substT_id a, substT_ext SubstT.id_up b, substT_id b]
  | .pi a b => by rw [substT, substT_id a, substT_ext SubstT.id_up b, substT_id b]
  | .letE a w b => by rw [substT, substT_id a, substT_id w, substT_ext SubstT.id_up b, substT_id b]
  | .lit _ => rfl

/-- lifting the result lifts the images — the `d = 1` case of
    `RcicTypedScopeCheck.lift_substT`, kept local under this name. -/
theorem lift_substT_one (c : Nat) (σ : SubstT) (e : Expr Nat) :
    lift c 1 (substT σ e) = substT (fun i => lift c 1 (σ i)) e :=
  lift_substT 1 e c σ

/-- substituting a lifted term precomposes with the shift. -/
theorem substT_lift (c : Nat) (σ : SubstT) :
    (e : Expr Nat) → substT σ (lift c 1 e) = substT (SubstT.shiftAt c σ) e
  | .bvar i => by
      show substT σ (if c ≤ i then .bvar (i + 1) else .bvar i) = _
      have hR : substT (SubstT.shiftAt c σ) (.bvar i) =
          (if c ≤ i then σ (i + 1) else σ i) := rfl
      rw [hR]
      by_cases h : c ≤ i <;> simp [h, substT]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substT, lift, substT_lift c σ f, substT_lift c σ x]
  | .lam a b => by
      simp only [substT, lift, substT_lift c σ a, substT_lift (c + 1) σ.up b]
      exact congrArg _ (substT_ext (SubstT.shiftAt_succ_up c σ) b)
  | .pi a b => by
      simp only [substT, lift, substT_lift c σ a, substT_lift (c + 1) σ.up b]
      rw [substT_ext (SubstT.shiftAt_succ_up c σ) b]
  | .letE a w b => by
      simp only [substT, lift, substT_lift c σ a, substT_lift c σ w, substT_lift (c + 1) σ.up b]
      exact congrArg _ (substT_ext (SubstT.shiftAt_succ_up c σ) b)
  | .lit _ => rfl

/-- under a binder, a lifted term is substituted by the unlifted substitution, lifted. -/
theorem substT_up_lift (σ : SubstT) (e : Expr Nat) :
    substT σ.up (lift 0 1 e) = lift 0 1 (substT σ e) := by
  rw [substT_lift, lift_substT_one]
  exact substT_ext (fun i => by simp [SubstT.shiftAt]) e

/-- `m` binders up. -/
def SubstT.upNT : Nat → SubstT → SubstT
  | 0, σ => σ
  | m + 1, σ => SubstT.upNT m σ.up

theorem SubstT.upNT_succ : (m : Nat) → (σ : SubstT) → upNT (m + 1) σ = (upNT m σ).up
  | 0, _ => rfl
  | m + 1, σ => SubstT.upNT_succ m σ.up

/-- the variables of the `m` binders stay. -/
theorem SubstT.upNT_lt : (m : Nat) → (σ : SubstT) → (i : Nat) → i < m → upNT m σ i = .bvar i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, σ, i, h => by
      rw [SubstT.upNT_succ]
      cases i with
      | zero => rfl
      | succ i =>
          rw [SubstT.up_succ, SubstT.upNT_lt m σ i (by omega), lift]
          simp

/-- under `m` binders, a term lifted past them is substituted by the substitution, then lifted. -/
theorem substT_upNT_lift : (m : Nat) → (σ : SubstT) → (e : Expr Nat) →
    substT (SubstT.upNT m σ) (lift 0 m e) = lift 0 m (substT σ e)
  | 0, σ, e => by simp only [lift_zero]; rfl
  | m + 1, σ, e => by
      rw [SubstT.upNT_succ, ← lift_lift_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _) e, substT_up_lift,
        substT_upNT_lift m σ e, lift_lift_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _)]

/-- substituting a lifted term reads the substitution's tail. -/
theorem substT_lift_succ (σ : SubstT) (e : Expr Nat) :
    substT σ (lift 0 1 e) = substT (fun i => σ (i + 1)) e := by
  rw [substT_lift]
  exact substT_ext (fun i => by simp [SubstT.shiftAt]) e

/-- substituting a lifted term past an extension reads the substitution extended. -/
theorem substT_cons_lift (a : Expr Nat) (σ : SubstT) (e : Expr Nat) :
    substT (SubstT.cons a σ) (lift 0 1 e) = substT σ e :=
  substT_lift_succ (SubstT.cons a σ) e

/-- instantiating the result instantiates the images. -/
theorem instantiate_substT (j : Nat) (a : Expr Nat) (σ : SubstT) :
    (e : Expr Nat) → instantiate j a (substT σ e) = substT (fun i => instantiate j a (σ i)) e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [substT, instantiate, instantiate_substT j a σ f, instantiate_substT j a σ x]
  | .lam a' b => by
      simp only [substT, instantiate, instantiate_substT j a σ a',
        instantiate_substT (j + 1) (lift 0 1 a) σ.up b]
      exact congrArg _ (substT_ext (inst_up j a σ) b)
  | .pi a' b => by
      simp only [substT, instantiate, instantiate_substT j a σ a',
        instantiate_substT (j + 1) (lift 0 1 a) σ.up b]
      rw [substT_ext (inst_up j a σ) b]
  | .letE a' w b => by
      simp only [substT, instantiate, instantiate_substT j a σ a', instantiate_substT j a σ w,
        instantiate_substT (j + 1) (lift 0 1 a) σ.up b]
      exact congrArg _ (substT_ext (inst_up j a σ) b)
  | .lit _ => rfl
where
  inst_up (j : Nat) (a : Expr Nat) (σ : SubstT) :
      ∀ i, instantiate (j + 1) (lift 0 1 a) (σ.up i) = SubstT.up (fun i => instantiate j a (σ i)) i
    | 0 => by
        show (if 0 = j + 1 then lift 0 1 a else if j + 1 < 0 then Expr.bvar (0 - 1) else Expr.bvar 0)
          = Expr.bvar 0
        rw [if_neg (by omega), if_neg (by omega)]
    | i + 1 => by
        simp only [SubstT.up_succ]
        rw [lift_instantiate_high 1 0 j a (Nat.zero_le j), show 1 + j = j + 1 from Nat.add_comm 1 j]

/-- composition. -/
theorem substT_substT (τ σ : SubstT) :
    (e : Expr Nat) → substT τ (substT σ e) = substT (fun i => substT τ (σ i)) e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by simp only [substT, substT_substT τ σ f, substT_substT τ σ x]
  | .lam a b => by
      simp only [substT, substT_substT τ σ a, substT_substT τ.up σ.up b]
      exact congrArg _ (substT_ext (comp_up τ σ) b)
  | .pi a b => by
      simp only [substT, substT_substT τ σ a, substT_substT τ.up σ.up b]
      rw [substT_ext (comp_up τ σ) b]
  | .letE a w b => by
      simp only [substT, substT_substT τ σ a, substT_substT τ σ w, substT_substT τ.up σ.up b]
      exact congrArg _ (substT_ext (comp_up τ σ) b)
  | .lit _ => rfl
where
  comp_up (τ σ : SubstT) : ∀ i, substT τ.up (σ.up i) = SubstT.up (fun i => substT τ (σ i)) i
    | 0 => rfl
    | i + 1 => by simp only [SubstT.up_succ]; exact substT_up_lift τ (σ i)

/-- a single instantiation is a parallel substitution. -/
theorem instantiate_eq_substT (j : Nat) (a : Expr Nat) :
    (e : Expr Nat) → instantiate j a e = substT (SubstT.single j a) e
  | .bvar i => by simp only [instantiate, substT, SubstT.single]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [instantiate, substT, instantiate_eq_substT j a f, instantiate_eq_substT j a x]
  | .lam a' b => by
      simp only [instantiate, substT, instantiate_eq_substT j a a',
        instantiate_eq_substT (j + 1) (lift 0 1 a) b]
      exact congrArg _ (substT_ext (SubstT.single_up j a) b).symm
  | .pi a' b => by
      simp only [instantiate, substT, instantiate_eq_substT j a a',
        instantiate_eq_substT (j + 1) (lift 0 1 a) b]
      rw [substT_ext (SubstT.single_up j a) b]
  | .letE a' w b => by
      simp only [instantiate, substT, instantiate_eq_substT j a a', instantiate_eq_substT j a w,
        instantiate_eq_substT (j + 1) (lift 0 1 a) b]
      exact congrArg _ (substT_ext (SubstT.single_up j a) b).symm
  | .lit _ => rfl

/-- THE ONE THE ARMS CONSUME: substitution passes through a `0`-instantiation. -/
theorem substT_instantiate0 (σ : SubstT) (a B : Expr Nat) :
    substT σ (instantiate0 a B) = instantiate0 (substT σ a) (substT σ.up B) := by
  rw [instantiate0, instantiate_eq_substT, substT_substT, instantiate0, instantiate_substT]
  exact substT_ext (fun i => by
    cases i with
    | zero => simp [SubstT.single, instantiate]
    | succ i => simp [SubstT.single, substT, instantiate_lift_id]) B

/-- instantiating under an extended substitution is substituting the extension. -/
theorem instantiate0_substT_up (σ : SubstT) (a B : Expr Nat) :
    instantiate0 a (substT σ.up B) = substT (SubstT.cons a σ) B := by
  rw [instantiate0, instantiate_substT]
  exact substT_ext (fun i => by
    cases i with
    | zero => simp [instantiate]
    | succ i => simp [substT, instantiate_lift_id]) B

/-- a `cons`-of-`id` substitution is the `0`-instantiation. -/
theorem substT_cons_id (a e : Expr Nat) :
    substT (SubstT.cons a SubstT.id) e = instantiate0 a e := by
  rw [instantiate0, instantiate_eq_substT]
  exact substT_ext (fun i => by
    cases i with
    | zero => rfl
    | succ i => simp [SubstT.single]) e

/-- the η-arm's codomain simplification: instantiating a lifted term at the
    variable it just introduced is the identity. -/
theorem instantiate_bvar_lift : (e : Expr Nat) → (j : Nat) →
    instantiate j (.bvar j) (lift (j + 1) 1 e) = e
  | .bvar i, j => by
      rw [lift]
      by_cases hi : j + 1 ≤ i
      · rw [if_pos hi, instantiate, if_neg (by omega : ¬ i + 1 = j),
            if_pos (by omega : j < i + 1)]
        congr 1
      · rw [if_neg hi, instantiate]
        by_cases h2 : i = j
        · subst h2; simp
        · rw [if_neg h2, if_neg (by omega : ¬ j < i)]
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app f x, j => by
      simp only [lift, instantiate, instantiate_bvar_lift f j, instantiate_bvar_lift x j]
  | .lam a b, j => by
      simp only [lift, instantiate]
      rw [instantiate_bvar_lift a j, if_pos (Nat.zero_le j),
        instantiate_bvar_lift b (j + 1)]
  | .pi a b, j => by
      simp only [lift, instantiate]
      rw [instantiate_bvar_lift a j, if_pos (Nat.zero_le j),
        instantiate_bvar_lift b (j + 1)]
  | .letE a w b, j => by
      simp only [lift, instantiate]
      rw [instantiate_bvar_lift a j, instantiate_bvar_lift w j,
        if_pos (Nat.zero_le j), instantiate_bvar_lift b (j + 1)]

theorem instantiate0_bvar0_lift1 (e : Expr Nat) :
    instantiate0 (.bvar 0) (lift 1 1 e) = e := instantiate_bvar_lift e 0

/-! ## closed terms -/

/-- lift-closed above `c` and the substitution is the identity below `c`: fixed. -/
theorem substT_closed_aux : (e : Expr Nat) → (c : Nat) → (∀ k, c ≤ k → lift k 1 e = e) →
    (σ : SubstT) → (∀ i, i < c → σ i = .bvar i) → substT σ e = e
  | .bvar i, c, h, σ, hσ => by
      by_cases hic : i < c
      · exact hσ i hic
      · exfalso
        have h0 := h c (Nat.le_refl c)
        rw [lift, if_pos (Nat.le_of_not_lt hic)] at h0
        injection h0 with h0
        omega
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .app f x, c, h, σ, hσ => by
      have hf : ∀ k, c ≤ k → lift k 1 f = f := fun k hk => by
        have := h k hk; simp only [lift, Expr.app.injEq] at this; exact this.1
      have hx : ∀ k, c ≤ k → lift k 1 x = x := fun k hk => by
        have := h k hk; simp only [lift, Expr.app.injEq] at this; exact this.2
      simp only [substT, substT_closed_aux f c hf σ hσ, substT_closed_aux x c hx σ hσ]
  | .lam a b, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.lam.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [lift, Expr.lam.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2
      simp only [substT, substT_closed_aux a c ha σ hσ,
        substT_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
  | .pi a b, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.pi.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [lift, Expr.pi.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2
      simp only [substT, substT_closed_aux a c ha σ hσ,
        substT_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
  | .letE a w b, c, h, σ, hσ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.letE.injEq] at this; exact this.1
      have hw : ∀ k, c ≤ k → lift k 1 w = w := fun k hk => by
        have := h k hk; simp only [lift, Expr.letE.injEq] at this; exact this.2.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have := h (k - 1) (by omega)
        simp only [lift, Expr.letE.injEq] at this
        rw [show k - 1 + 1 = k by omega] at this; exact this.2.2
      simp only [substT, substT_closed_aux a c ha σ hσ, substT_closed_aux w c hw σ hσ,
        substT_closed_aux b (c + 1) hb σ.up (up_below c σ hσ)]
where
  up_below (c : Nat) (σ : SubstT) (hσ : ∀ i, i < c → σ i = .bvar i) :
      ∀ i, i < c + 1 → σ.up i = .bvar i
    | 0, _ => rfl
    | i + 1, hi => by
        rw [SubstT.up_succ, hσ i (Nat.lt_of_succ_lt_succ hi), lift]
        simp

/-- a lift-closed term is fixed by every substitution. -/
theorem substT_closed {e : Expr Nat} (h : ∀ k, lift k 1 e = e) (σ : SubstT) : substT σ e = e :=
  substT_closed_aux e 0 (fun k _ => h k) σ (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- level instantiation preserves lift-closedness (typed-side alias of
    `instantiateLevels_closed` at unit amount). -/
theorem lift_instantiateLevels_closedT {e : Expr Nat} (h : ∀ k, lift k 1 e = e) (ls : List Level) :
    ∀ k, lift k 1 (instantiateLevels ls e) = instantiateLevels ls e :=
  instantiateLevels_closed h ls

/-- the literal expansion is closed. -/
theorem lift_natExpand_closed : (t : Nat) → ∀ k, lift k 1 (natExpand t) = natExpand t :=
  fun t k => natExpand_lift k 1 t

theorem substT_natExpand (σ : SubstT) (t : Nat) : substT σ (natExpand t) = natExpand t :=
  substT_closed (lift_natExpand_closed t) σ

/-! ## the renaming bridge, generalized to skip-counts

A field list is modelled as `List Nat`: each entry is the number of full-context
binders the field inserts that are absent from the plain context.  `0` = plain
field (`σ.up`, binder kept); `k ≥ 1` = recursive field contributing `k` new
binders (`σ.shift1^k`).  ctor: [0,1,1]; minor: [0,2,2] (drec adds field + IH). -/

/-- `σ.shift1^k`. -/
def shiftN (σ : SubstT) : Nat → SubstT
  | 0 => σ
  | k + 1 => (shiftN σ k).shift1

def ctorSubStep (k : Nat) (σ : SubstT) : SubstT :=
  if k = 0 then σ.up else shiftN σ k

def ctorSub (fs : List Nat) : SubstT := fs.foldl (fun σ k => ctorSubStep k σ) SubstT.id

def ctorVarStep (k : Nat) (F : Nat → Nat) : Nat → Nat :=
  if k = 0 then (fun | 0 => 0 | i + 1 => F i + 1) else (fun i => F i + k)

def ctorVar (fs : List Nat) : Nat → Nat := fs.foldl (fun F k => ctorVarStep k F) id

/-- a field's full-context binder count. -/
def fieldBinders (k : Nat) : Nat := if k = 0 then 1 else k

/-- full-context binders below position of a field — for its inner cutoff base. -/
def binderCount (fs : List Nat) : Nat := (fs.map fieldBinders).sum

theorem ctorVarStep_zero_id : ctorVarStep 0 id = id := by
  funext i; cases i with
  | zero => rfl
  | succ i => rfl

/-- the KEY invariant: an initial `F₀ i = G₀ i + (c ≤ G₀ i ? k₀ : 0)` survives the
    fold with the guard's bound growing by each field's binder count. -/
theorem foldl_ctorVarStep_gen :
    ∀ (fs : List Nat) (F₀ G₀ : Nat → Nat) (c k₀ : Nat),
      (∀ i, F₀ i = G₀ i + (if c ≤ G₀ i then k₀ else 0)) → ∀ (i : Nat),
      (fs.foldl (fun F k => ctorVarStep k F) F₀) i =
        (fs.foldl (fun F k => ctorVarStep k F) G₀) i +
          (if c + binderCount fs ≤ (fs.foldl (fun F k => ctorVarStep k F) G₀) i then k₀ else 0) := by
  intro fs
  induction fs with
  | nil =>
      intro F₀ G₀ c k₀ h i
      simp only [List.foldl_nil, binderCount, List.map_nil, List.sum_nil, Nat.add_zero]
      exact h i
  | cons q rest ih =>
      intro F₀ G₀ c k₀ h i
      simp only [List.foldl_cons, binderCount, List.map_cons, List.sum_cons]
      have h' : ∀ j, ctorVarStep q F₀ j =
          ctorVarStep q G₀ j + (if c + fieldBinders q ≤ ctorVarStep q G₀ j then k₀ else 0) := by
        intro j
        cases q with
        | zero =>
            cases j with
            | zero =>
                show (0 : Nat) = 0 + (if c + fieldBinders 0 ≤ 0 then k₀ else 0)
                rw [show fieldBinders 0 = 1 from rfl, if_neg (by omega), Nat.add_zero]
            | succ j =>
                show F₀ j + 1 = G₀ j + 1 +
                    (if c + fieldBinders 0 ≤ G₀ j + 1 then k₀ else 0)
                rw [show fieldBinders 0 = 1 from rfl, h j]
                by_cases hc : c ≤ G₀ j
                · rw [if_pos hc, if_pos (by omega : c + 1 ≤ G₀ j + 1)]; omega
                · rw [if_neg hc, if_neg (by omega : ¬(c + 1 ≤ G₀ j + 1))]
        | succ q' =>
            show F₀ j + (q' + 1) = G₀ j + (q' + 1) +
                (if c + fieldBinders (q' + 1) ≤ G₀ j + (q' + 1) then k₀ else 0)
            rw [show fieldBinders (q' + 1) = q' + 1 from rfl, h j]
            by_cases hc : c ≤ G₀ j
            · rw [if_pos hc, if_pos (by omega : c + (q' + 1) ≤ G₀ j + (q' + 1))]
              omega
            · rw [if_neg hc, if_neg (by omega : ¬(c + (q' + 1) ≤ G₀ j + (q' + 1)))]
              omega
      rw [ih (ctorVarStep q F₀) (ctorVarStep q G₀) (c + fieldBinders q) k₀ h' i]
      simp only [binderCount, Nat.add_assoc]

/-- corollary: a leading `+k` step contributes `+k` once past its position. -/
theorem foldl_ctorVarStep_shift (fs : List Nat) (k : Nat) (i : Nat) :
    (fs.foldl (fun F k => ctorVarStep k F) (· + k)) i =
      ctorVar fs i + (if binderCount fs ≤ ctorVar fs i then k else 0) := by
  have := foldl_ctorVarStep_gen fs (· + k) id 0 k
    (fun i => by simp [ctorVarStep]) i
  simpa [ctorVar] using this

/-- insertion cutoffs: a skip-`k` field contributes `k` consecutive cutoffs at
    its inner binder count, innermost-first. -/
def insCutoffs : List Nat → List Nat
  | [] => []
  | k :: rest => insCutoffs rest ++ (List.range k).map (· + binderCount rest)

def liftChain (cs : List Nat) (e : Expr Nat) : Expr Nat :=
  cs.foldl (fun e c => lift c 1 e) e

def liftChainStep (i : Nat) (c : Nat) : Nat := if c ≤ i then i + 1 else i

/-- folding `liftChainStep` over `k` consecutive cutoffs `[B..B+k-1]` adds `k`
    to every var at or past `B`. -/
theorem foldl_liftChainStep_consec (k : Nat) :
    ∀ (B i : Nat), ((List.range k).map (· + B)).foldl liftChainStep i =
      i + (if B ≤ i then k else 0) := by
  induction k with
  | zero => intro B i; simp
  | succ k ih =>
      intro B i
      have hcons : (List.range (k + 1)).map (· + B) =
          B :: ((List.range k).map (· + (B + 1))) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq]
        refine ⟨by omega, ?_⟩
        congr 1
        funext x
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        omega
      rw [hcons, List.foldl_cons]
      have hstep : liftChainStep i B = i + (if B ≤ i then 1 else 0) := by
        simp only [liftChainStep]
        by_cases h : B ≤ i <;> simp [h]
      rw [hstep, ih (B + 1)]
      by_cases h : B ≤ i
      · rw [if_pos h, if_pos (by omega : B + 1 ≤ i + 1), if_pos h]; omega
      · rw [if_neg h, if_neg (by omega : ¬(B + 1 ≤ i + 0)), if_neg h]

/-- the chain's var-map equals σ's var-map. -/
theorem liftChainStep_eq_ctorVar (fs : List Nat) (i : Nat) :
    (insCutoffs fs).foldl liftChainStep i = ctorVar fs i := by
  induction fs with
  | nil => rfl
  | cons k rest ih =>
      show ((insCutoffs rest) ++ ((List.range k).map (· + binderCount rest))).foldl liftChainStep i = _
      rw [List.foldl_append, ih]
      cases k with
      | zero =>
          show List.foldl liftChainStep (ctorVar rest i)
              ((List.range 0).map (· + binderCount rest)) = _
          simp only [List.range_zero, List.map_nil, List.foldl_nil]
          show ctorVar rest i = (rest.foldl (fun F k => ctorVarStep k F) (ctorVarStep 0 id)) i
          rw [ctorVarStep_zero_id]
          rfl
      | succ k' =>
          show List.foldl liftChainStep (ctorVar rest i)
              ((List.range (k' + 1)).map (· + binderCount rest)) = _
          rw [foldl_liftChainStep_consec]
          show ctorVar rest i + (if binderCount rest ≤ ctorVar rest i then k' + 1 else 0) =
              (rest.foldl (fun F k => ctorVarStep k F) (ctorVarStep (k' + 1) id)) i
          have hstep : ctorVarStep (k' + 1) id = (· + (k' + 1)) := rfl
          rw [hstep]
          show ctorVar rest i + (if binderCount rest ≤ ctorVar rest i then k' + 1 else 0) =
              (rest.foldl (fun F k => ctorVarStep k F) (· + (k' + 1))) i
          exact (foldl_ctorVarStep_shift rest (k' + 1) i).symm

/-- σ on a bvar is the var-map's bvar, thread through the whole fold. -/
theorem ctorSub_bvar (fs : List Nat) (σ : SubstT) (F : Nat → Nat)
    (h : ∀ i, σ i = .bvar (F i)) :
    ∀ i, (fs.foldl (fun σ k => ctorSubStep k σ) σ) i =
      .bvar ((fs.foldl (fun F k => ctorVarStep k F) F) i) := by
  induction fs generalizing σ F with
  | nil => intro i; exact h i
  | cons k rest ih =>
      intro i
      have h' : ∀ j, ctorSubStep k σ j = .bvar (ctorVarStep k F j) := by
        intro j
        cases k with
        | zero =>
            cases j with
            | zero => rfl
            | succ j =>
                show lift 0 1 (σ j) = .bvar (F j + 1)
                rw [h j]
                simp only [lift]
                rw [if_pos (Nat.zero_le _)]
        | succ k' =>
          have hshift : ∀ m, (shiftN σ m) j = lift 0 m (σ j) := by
            intro m
            induction m with
            | zero => exact (lift_zero_idx 0 (σ j)).symm
            | succ m ihm =>
                show lift 0 1 (shiftN σ m j) = lift 0 (m + 1) (σ j)
                rw [ihm]
                show lift 0 1 (lift 0 m (σ j)) = lift 0 (m + 1) (σ j)
                exact lift_lift_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _) (σ j)
          have h2 : ctorSubStep (k' + 1) σ j = lift 0 (k' + 1) (σ j) := by
            simp only [ctorSubStep]
            rw [if_neg (by omega)]
            exact hshift (k' + 1)
          rw [h2, h j]
          show lift 0 (k' + 1) (.bvar (F j)) = .bvar (F j + (k' + 1))
          simp only [lift]
          rw [if_pos (Nat.zero_le _)]
      exact ih (ctorSubStep k σ) (ctorVarStep k F) h' i

theorem ctorSub_apply (fs : List Nat) (i : Nat) :
    ctorSub fs i = .bvar (ctorVar fs i) :=
  ctorSub_bvar fs SubstT.id id (fun _ => rfl) i

theorem liftChain_bvar (cs : List Nat) (i : Nat) :
    liftChain cs (.bvar i) = .bvar (cs.foldl liftChainStep i) := by
  induction cs generalizing i with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons]
      have h1 : lift c 1 (Expr.bvar i : Expr Nat) = Expr.bvar (liftChainStep i c) := by
        simp only [lift, liftChainStep]
        by_cases h : c ≤ i <;> simp [h]
      rw [h1]
      exact ih (liftChainStep i c)

/-- the renaming σ's action on a bvar equals the insertAt chain's. -/
theorem substT_ctorSub_bvar (fs : List Nat) (i : Nat) :
    substT (ctorSub fs) (.bvar i) = liftChain (insCutoffs fs) (.bvar i) := by
  simp only [substT, ctorSub_apply, liftChain_bvar, liftChainStep_eq_ctorVar]

/-! ## the expression-level bridge -/

/-- a cutoff chain as a substitution. -/
def liftChainSub (cs : List Nat) : SubstT := fun i => .bvar (cs.foldl liftChainStep i)

theorem liftChainStep_succ_map (cs : List Nat) (i : Nat) :
    (cs.map (· + 1)).foldl liftChainStep (i + 1) = cs.foldl liftChainStep i + 1 := by
  induction cs generalizing i with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : liftChainStep (i + 1) (c + 1) = liftChainStep i c + 1 := by
        simp only [liftChainStep]
        by_cases h : c ≤ i
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      rw [hstep]
      exact ih (liftChainStep i c)

theorem liftChainStep_zero_map (cs : List Nat) :
    (cs.map (· + 1)).foldl liftChainStep 0 = 0 := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hz : liftChainStep 0 (c + 1) = 0 := by simp [liftChainStep]
      rw [hz]
      exact ih

/-- the chain-substitution under a binder is the chain of shifted cutoffs. -/
theorem liftChainSub_up (cs : List Nat) :
    (liftChainSub cs).up = liftChainSub (cs.map (· + 1)) := by
  funext i
  cases i with
  | zero =>
      show Expr.bvar 0 = Expr.bvar ((cs.map (· + 1)).foldl liftChainStep 0)
      rw [liftChainStep_zero_map]
  | succ i =>
      show lift 0 1 (liftChainSub cs i) = liftChainSub (cs.map (· + 1)) (i + 1)
      simp only [liftChainSub, lift]
      rw [if_pos (Nat.zero_le _), liftChainStep_succ_map]

/-- `lift` distributes under a binder's cutoff. -/
theorem liftChain_lam (cs : List Nat) (A B : Expr Nat) :
    liftChain cs (.lam A B) = .lam (liftChain cs A) (liftChain (cs.map (· + 1)) B) := by
  induction cs generalizing A B with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons, List.map_cons]
      rw [show lift c 1 (Expr.lam A B) = Expr.lam (lift c 1 A) (lift (c + 1) 1 B) from rfl]
      exact ih (lift c 1 A) (lift (c + 1) 1 B)

theorem liftChain_pi (cs : List Nat) (A B : Expr Nat) :
    liftChain cs (.pi A B) = .pi (liftChain cs A) (liftChain (cs.map (· + 1)) B) := by
  induction cs generalizing A B with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons, List.map_cons]
      rw [show lift c 1 (Expr.pi A B) = Expr.pi (lift c 1 A) (lift (c + 1) 1 B) from rfl]
      exact ih (lift c 1 A) (lift (c + 1) 1 B)

theorem liftChain_letE (cs : List Nat) (A w B : Expr Nat) :
    liftChain cs (.letE A w B) =
      .letE (liftChain cs A) (liftChain cs w) (liftChain (cs.map (· + 1)) B) := by
  induction cs generalizing A w B with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons, List.map_cons]
      rw [show lift c 1 (Expr.letE A w B) =
        Expr.letE (lift c 1 A) (lift c 1 w) (lift (c + 1) 1 B) from rfl]
      exact ih (lift c 1 A) (lift c 1 w) (lift (c + 1) 1 B)

theorem liftChain_app (cs : List Nat) (f x : Expr Nat) :
    liftChain cs (.app f x) = .app (liftChain cs f) (liftChain cs x) := by
  induction cs generalizing f x with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons]
      rw [show lift c 1 (Expr.app f x) = Expr.app (lift c 1 f) (lift c 1 x) from rfl]
      exact ih (lift c 1 f) (lift c 1 x)

theorem liftChain_closed (e : Expr Nat) (h : ∀ k, lift k 1 e = e) :
    ∀ cs, liftChain cs e = e := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      simp only [liftChain, List.foldl_cons]
      rw [h c]
      exact ih

/-- substituting a chain-lift is the chain itself — the expression-level bridge. -/
theorem substT_liftChainSub (cs : List Nat) : (e : Expr Nat) →
    substT (liftChainSub cs) e = liftChain cs e
  | .bvar i => liftChain_bvar cs i |>.symm
  | .sort _ => (liftChain_closed _ (fun _ => rfl) _).symm
  | .const _ _ => (liftChain_closed _ (fun _ => rfl) _).symm
  | .app f x => by
      rw [substT, liftChain_app, substT_liftChainSub cs f, substT_liftChainSub cs x]
  | .lam a b => by
      rw [substT, liftChain_lam, substT_liftChainSub cs a, liftChainSub_up,
        substT_liftChainSub (cs.map (· + 1)) b]
  | .pi a b => by
      rw [substT, liftChain_pi, substT_liftChainSub cs a, liftChainSub_up,
        substT_liftChainSub (cs.map (· + 1)) b]
  | .letE a w b => by
      rw [substT, liftChain_letE, substT_liftChainSub cs a, substT_liftChainSub cs w,
        liftChainSub_up, substT_liftChainSub (cs.map (· + 1)) b]
  | .lit _ => (liftChain_closed _ (fun _ => rfl) _).symm

/-- the ctor renaming is the cutoff chain, pointwise. -/
theorem ctorSub_eq_liftChainSub (fs : List Nat) (i : Nat) :
    ctorSub fs i = liftChainSub (insCutoffs fs) i := by
  rw [ctorSub_apply]
  simp only [liftChainSub, liftChainStep_eq_ctorVar]

/-- THE renaming bridge: the ctor σ acts as the insertAt lift chain. -/
theorem substT_ctorSub (fs : List Nat) (e : Expr Nat) :
    substT (ctorSub fs) e = liftChain (insCutoffs fs) e := by
  rw [funext (ctorSub_eq_liftChainSub fs)]
  exact substT_liftChainSub _ e

/-- the lift chain distributes over concatenated cutoff lists, inner block first. -/
theorem liftChain_append (cs cs' : List Nat) (e : Expr Nat) :
    liftChain (cs ++ cs') e = liftChain cs' (liftChain cs e) := by
  simp only [liftChain, List.foldl_append]

/-- a zero head skip contributes no cutoff — the ctorSub of `0 :: fs` acts as that of `fs`. -/
theorem substT_ctorSub_cons_zero (rest : List Nat) (e : Expr Nat) :
    substT (ctorSub (0 :: rest)) e = substT (ctorSub rest) e := by
  rw [substT_ctorSub, substT_ctorSub]
  congr 1
  simp only [insCutoffs, List.range_zero, List.map_nil, List.append_nil]

/-- a unit head skip appends one cutoff at the tail's binder count — the ctorSub of
    `1 :: fs` acts as `fs`'s chain followed by a lift at the tail depth. -/
theorem substT_ctorSub_cons_one (rest : List Nat) (e : Expr Nat) :
    substT (ctorSub (1 :: rest)) e =
      lift (binderCount rest) 1 (substT (ctorSub rest) e) := by
  rw [substT_ctorSub, substT_ctorSub, show insCutoffs (1 :: rest) =
      insCutoffs rest ++ [binderCount rest] from by
    simp only [insCutoffs, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
      Nat.zero_add]]
  rw [liftChain_append]
  rfl

/-- one skip appended: the `ctorSub` of `xs ++ [k]` is that of `xs` followed by the step. -/
theorem ctorSub_append_one (xs : List Nat) (k : Nat) :
    ctorSub (xs ++ [k]) = ctorSubStep k (ctorSub xs) := by
  simp [ctorSub, List.foldl_append]

/-! ### the constructor field skip map

`ctorFieldsT` gives every field exactly one binder in the constructor telescope: a plain
field steps `σ.up`, a recursive one (`.drec`/`.drecD`) steps `σ.shift1`.  Its skip list is
`fs.map FieldT.ctorSkip`, all entries `≤ 1`, so `binderCount` of a tail is just its length —
the insertion cutoff of a recursive field is the number of fields after it. -/

/-- the ctor field skip count: `σ.up` on plain, `σ.shift1` on recursive. -/
def FieldT.ctorSkip : FieldT → Nat
  | .plain _ _ => 0
  | .drec _ => 1
  | .drecD _ _ => 1

theorem binderCount_map_ctorSkip : (fs : List FieldT) →
    binderCount (fs.map FieldT.ctorSkip) = fs.length
  | [] => rfl
  | f :: fs => by
      simp only [List.map_cons, List.length_cons, binderCount, List.map_cons, List.sum_cons]
      have h1 : fieldBinders f.ctorSkip = 1 := by cases f <;> rfl
      rw [h1, show (List.map fieldBinders (List.map FieldT.ctorSkip fs)).sum =
          binderCount (fs.map FieldT.ctorSkip) from rfl, binderCount_map_ctorSkip fs]
      omega

/-- the recursive fields' insertion cutoffs, innermost first: each recursive field's
    count of fields after it. -/
def ctorInsCutoffs : List FieldT → List Nat
  | .plain _ _ :: fs => ctorInsCutoffs fs
  | .drec _ :: fs => ctorInsCutoffs fs ++ [fs.length]
  | .drecD _ _ :: fs => ctorInsCutoffs fs ++ [fs.length]
  | [] => []

theorem ctorInsCutoffs_length : (fs : List FieldT) →
    (ctorInsCutoffs fs).length = (fs.filter (fun f => f.ctorSkip ≠ 0)).length
  | [] => rfl
  | f :: fs => by
      cases f <;> simp [ctorInsCutoffs, FieldT.ctorSkip, ctorInsCutoffs_length fs]

/-- for the ctor skip map the insertion cutoffs are the fields-after counts, one per
    recursive field, innermost first. -/
theorem insCutoffs_map_ctorSkip : (fs : List FieldT) →
    insCutoffs (fs.map FieldT.ctorSkip) = ctorInsCutoffs fs
  | [] => rfl
  | .plain _ _ :: fs => by
      simp only [List.map_cons, FieldT.ctorSkip, insCutoffs, List.range_zero, List.map_nil,
        List.append_nil, ctorInsCutoffs]
      exact insCutoffs_map_ctorSkip fs
  | .drec _ :: fs => by
      simp only [List.map_cons, FieldT.ctorSkip, insCutoffs, binderCount_map_ctorSkip,
        ctorInsCutoffs, show List.range 1 = [0] from rfl, List.map_nil, Nat.zero_add]
      rw [insCutoffs_map_ctorSkip fs]
  | .drecD _ _ :: fs => by
      simp only [List.map_cons, FieldT.ctorSkip, insCutoffs, binderCount_map_ctorSkip,
        ctorInsCutoffs, show List.range 1 = [0] from rfl, List.map_nil, Nat.zero_add]
      rw [insCutoffs_map_ctorSkip fs]

/-- `plainIdxT` increments by the starting index. -/
theorem plainIdxT_add : (fs : List FieldT) → (j k : Nat) → plainIdxT fs (j + k) = plainIdxT fs j + k
  | [], _, _ => rfl
  | .plain _ _ :: fs, j, k => by
      simp only [plainIdxT]
      rw [show j + k + 1 = j + 1 + k from by omega, plainIdxT_add fs (j + 1) k]
  | .drec _ :: fs, j, k => plainIdxT_add fs j k
  | .drecD _ _ :: fs, j, k => plainIdxT_add fs j k

theorem plainIdxT_cons_plain (D : Expr Nat) (u : Level) (fs : List FieldT) (j : Nat) :
    plainIdxT (.plain D u :: fs) j = plainIdxT fs j + 1 := by
  simp only [plainIdxT]
  rw [plainIdxT_add]

/-- `substT` distributes over an application spine. -/
theorem substT_foldApps (σ : SubstT) (f : Expr Nat) :
    (args : List (Expr Nat)) →
      substT σ (foldApps f args) = foldApps (substT σ f) (args.map (substT σ))
  | [] => rfl
  | x :: xs => substT_foldApps σ (.app f x) xs

/-- the bvar-level fold: a pointwise-bounded cutoff chain adds its length to a
    variable — `liftChainStep` fires at every step. -/
theorem foldl_liftChainStep_add : (cs : List Nat) → (v : Nat) →
    (∀ i (hi : i < cs.length), cs[i] ≤ v + i) →
    cs.foldl liftChainStep v = v + cs.length
  | [], _, _ => rfl
  | c :: cs, v, h => by
      simp only [List.foldl_cons, liftChainStep]
      have hc : c ≤ v := by
        have := h 0 (by simp)
        simp only [List.getElem_cons_zero] at this; omega
      rw [if_pos hc, foldl_liftChainStep_add cs (v + 1) (fun i hi => by
        have := h (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at this; omega)]
      simp only [List.length_cons]; omega

/-- `liftChain` over a pointwise-bounded cutoff list past a `lift 0 m`: each step
    merges by `lift_lift_merge`, accumulating to `lift 0 (m + cs.length)`. The bound
    `cs[i] ≤ m + i` is what the merge's `c' ≤ n + c` premise needs at step `i`. -/
theorem liftChain_lift_zero : (cs : List Nat) → (m : Nat) →
    (∀ i (hi : i < cs.length), cs[i] ≤ m + i) →
    (e : Expr Nat) → liftChain cs (lift 0 m e) = lift 0 (m + cs.length) e
  | [], _, _, _ => rfl
  | c :: cs, m, h, e => by
      show liftChain cs (lift c 1 (lift 0 m e)) = lift 0 (m + (c :: cs).length) e
      rw [lift_lift_merge 1 m 0 c (Nat.zero_le c) (by
        have := h 0 (by simp)
        simp only [List.getElem_cons_zero] at this; omega)]
      rw [liftChain_lift_zero cs (m + 1) (fun i hi => by
        have := h (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at this; omega) e]
      congr 1
      simp only [List.length_cons]; omega

/-- the plain-field count plus the insertion-pair count exhausts the field count —
    the boundary case of `ctorInsCutoffs_le`. -/
theorem plainIdxT_add_ctorInsCutoffs_length : (fs : List FieldT) →
    plainIdxT fs 0 + (ctorInsCutoffs fs).length = fs.length
  | [] => rfl
  | .plain _ _ :: fs => by
      have h := plainIdxT_add_ctorInsCutoffs_length fs
      simp only [ctorInsCutoffs, plainIdxT_cons_plain, List.length_cons]
      omega
  | .drec _ :: fs => by
      have h := plainIdxT_add_ctorInsCutoffs_length fs
      simp only [ctorInsCutoffs, List.length_append, List.length_cons, List.length_nil,
        plainIdxT, List.length_cons]
      omega
  | .drecD _ _ :: fs => by
      have h := plainIdxT_add_ctorInsCutoffs_length fs
      simp only [ctorInsCutoffs, List.length_append, List.length_cons, List.length_nil,
        plainIdxT, List.length_cons]
      omega

/-- each ctor insertion cutoff is bounded by the plain-field count plus its own
    position — the `liftChain_lift_zero` bound at `m = plainIdxT`-based offsets. -/
theorem ctorInsCutoffs_le : (fs : List FieldT) →
    ∀ i (hi : i < (ctorInsCutoffs fs).length),
      (ctorInsCutoffs fs)[i] ≤ plainIdxT fs 0 + i
  | [], _, hi => absurd hi (by simp [ctorInsCutoffs])
  | .plain _ _ :: fs, i, hi => by
      have h := ctorInsCutoffs_le fs i (by simpa [ctorInsCutoffs] using hi)
      simp only [ctorInsCutoffs, plainIdxT_cons_plain]
      omega
  | .drec _ :: fs, i, hi => by
      simp only [ctorInsCutoffs, List.length_append, List.length_cons,
        List.length_nil] at hi
      simp only [ctorInsCutoffs]
      by_cases hlt : i < (ctorInsCutoffs fs).length
      · rw [List.getElem_append_left hlt]
        have h := ctorInsCutoffs_le fs i hlt
        simp only [plainIdxT]; omega
      · have heq : i = (ctorInsCutoffs fs).length := by omega
        subst heq
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero, plainIdxT]
        have h := plainIdxT_add_ctorInsCutoffs_length fs
        omega
  | .drecD _ _ :: fs, i, hi => by
      simp only [ctorInsCutoffs, List.length_append, List.length_cons,
        List.length_nil] at hi
      simp only [ctorInsCutoffs]
      by_cases hlt : i < (ctorInsCutoffs fs).length
      · rw [List.getElem_append_left hlt]
        have h := ctorInsCutoffs_le fs i hlt
        simp only [plainIdxT]; omega
      · have heq : i = (ctorInsCutoffs fs).length := by omega
        subst heq
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero, plainIdxT]
        have h := plainIdxT_add_ctorInsCutoffs_length fs
        omega


/-- `k` consecutive cutoffs `[B..B+k-1]` act as one `lift B k`. -/
theorem liftChain_consec (k B : Nat) (e : Expr Nat) :
    liftChain ((List.range k).map (· + B)) e = lift B k e := by
  induction k generalizing B e with
  | zero => show e = _; rw [lift_zero_idx]
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, liftChain_append, ih,
          Nat.add_comm k B]
      exact lift_lift_merge 1 k B (B + k) (Nat.le_add_right B k)
        (Nat.le_of_eq (Nat.add_comm B k)) e

/-- `k` equal cutoffs `c` act as `lift c k`. -/
theorem liftChain_replicate (k c : Nat) (e : Expr Nat) :
    liftChain (List.replicate k c) e = lift c k e := by
  induction k generalizing e with
  | zero => show e = _; rw [lift_zero_idx]
  | succ k ih =>
      show liftChain (List.replicate k c) (lift c 1 e) = lift c (k + 1) e
      rw [ih]
      have h := lift_lift_merge k 1 c c (Nat.le_refl c) (Nat.le_add_left c 1) e
      rw [Nat.add_comm 1 k] at h; exact h

theorem insCutoffs_cons (k : Nat) (rest : List Nat) :
    insCutoffs (k :: rest) = insCutoffs rest ++ (List.range k).map (· + binderCount rest) := rfl

/-- `ctorSub (k :: skips)` = `lift (binderCount skips) k` after `ctorSub skips` —
    the prepend-a-global-shift step (the `d`-past-parameters layer of the minor's
    context: `d` extra binders below the field telescope, shifted over `ctorSub`). -/
theorem substT_ctorSub_cons (k : Nat) (rest : List Nat) (e : Expr Nat) :
    substT (ctorSub (k :: rest)) e =
      lift (binderCount rest) k (substT (ctorSub rest) e) := by
  rw [substT_ctorSub, insCutoffs_cons, liftChain_append, ← substT_ctorSub,
      liftChain_consec]

/-! ## `instPrefix` as a `SubstT` — the parameter-locals spine -/

/-- `instPrefix args` as a parallel substitution: each `single` composes into the tail's. -/
def instPrefixSubst : List (Expr Nat) → SubstT
  | [] => SubstT.id
  | a :: as => fun i =>
      substT (instPrefixSubst as) (SubstT.single as.length (lift 0 as.length a) i)

/-- `instPrefix` IS `instPrefixSubst` applied. -/
theorem instPrefix_eq_substT : (as : List (Expr Nat)) → (e : Expr Nat) →
    instPrefix as e = substT (instPrefixSubst as) e
  | [], e => (substT_id e).symm
  | a :: as, e => by
      show instPrefix as (instantiate as.length (lift 0 as.length a) e) = _
      rw [instPrefix_eq_substT as, instantiate_eq_substT, substT_substT]
      rfl

/-- the descending parameter spine `[bvar (B+i-1), …, bvar B]` as a list. -/
def descSpine (B i : Nat) : List (Expr Nat) :=
  (List.range i).reverse.map (fun t => .bvar (B + t))

theorem descSpine_length (B i : Nat) : (descSpine B i).length = i := by
  simp [descSpine]

theorem descSpine_succ (B i : Nat) :
    descSpine B (i + 1) = .bvar (B + i) :: descSpine B i := by
  have hrev : (List.range (i + 1)).reverse = i :: (List.range i).reverse := by
    rw [List.range_succ, List.reverse_append]
    rfl
  simp only [descSpine, hrev, List.map_cons]

/-- the spine substitution's pointwise action: below `i` it is `+B`, at and past `i`
    the consumed binders decrement. -/
theorem instPrefixSubst_descSpine : (i : Nat) → (B k : Nat) →
    instPrefixSubst (descSpine B i) k = if k < i then .bvar (B + k) else .bvar (k - i)
  | 0, B, k => by
      show (SubstT.id : SubstT) k = _
      show (Expr.bvar k : Expr Nat) = if k < 0 then .bvar (B + k) else .bvar (k - 0)
      rw [if_neg (Nat.not_lt_zero k), Nat.sub_zero]
  | i + 1, B, k => by
      rw [descSpine_succ]
      show substT (instPrefixSubst (descSpine B i))
          (SubstT.single (descSpine B i).length
            (lift 0 (descSpine B i).length (.bvar (B + i))) k) = _
      rw [descSpine_length]
      have hl : lift 0 i (Expr.bvar (B + i) : Expr Nat) = .bvar (B + i + i) :=
        if_pos (Nat.zero_le _)
      rw [hl]
      show substT (instPrefixSubst (descSpine B i))
          (if k = i then .bvar (B + i + i) else if i < k then .bvar (k - 1)
            else .bvar k) = _
      by_cases hk : k = i
      · rw [if_pos hk]
        show instPrefixSubst (descSpine B i) (B + i + i) = _
        rw [instPrefixSubst_descSpine i B (B + i + i), if_neg (by omega),
          if_pos (by omega : k < i + 1)]
        congr 1; omega
      · by_cases hik : i < k
        · rw [if_neg hk, if_pos hik]
          show instPrefixSubst (descSpine B i) (k - 1) = _
          rw [instPrefixSubst_descSpine i B (k - 1), if_neg (by omega),
            if_neg (by omega : ¬ k < i + 1)]
          congr 1; omega
        · rw [if_neg hk, if_neg hik]
          have hk' : k < i := by omega
          show instPrefixSubst (descSpine B i) k = _
          rw [instPrefixSubst_descSpine i B k, if_pos hk', if_pos (by omega)]

/-- `SubstT.up` preserves below-`c+1` agreement from below-`c`. -/
theorem substT_up_congr (σ τ : SubstT) (c : Nat) (h : ∀ i, i < c → σ i = τ i) :
    ∀ i, i < c + 1 → σ.up i = τ.up i
  | 0, _ => rfl
  | i + 1, hi => by
      rw [SubstT.up_succ, SubstT.up_succ, h i (Nat.lt_of_succ_lt_succ hi)]

/-- two substitutions agreeing below `c` agree on a term whose variables stay below `c`
    (the sibling of `substT_closed_aux`: agreement, not identity). -/
theorem substT_congr_below : (e : Expr Nat) → (c : Nat) →
    (∀ k, c ≤ k → lift k 1 e = e) → (σ τ : SubstT) →
    (∀ i, i < c → σ i = τ i) → substT σ e = substT τ e
  | .bvar i, c, h, σ, τ, hστ => by
      by_cases hic : i < c
      · exact hστ i hic
      · exfalso
        have h0 := h c (Nat.le_refl c)
        rw [lift, if_pos (Nat.le_of_not_lt hic)] at h0
        injection h0 with h0
        omega
  | .sort _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _ => rfl
  | .lit _, _, _, _, _, _ => rfl
  | .app f x, c, h, σ, τ, hστ => by
      have hf : ∀ k, c ≤ k → lift k 1 f = f := fun k hk => by
        have := h k hk; simp only [lift, Expr.app.injEq] at this; exact this.1
      have hx : ∀ k, c ≤ k → lift k 1 x = x := fun k hk => by
        have := h k hk; simp only [lift, Expr.app.injEq] at this; exact this.2
      show Expr.app (substT σ f) (substT σ x) = Expr.app (substT τ f) (substT τ x)
      rw [substT_congr_below f c hf σ τ hστ, substT_congr_below x c hx σ τ hστ]
  | .lam a b, c, h, σ, τ, hστ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.lam.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have h4 := h (k - 1) (by omega)
        simp only [lift, Expr.lam.injEq] at h4
        rw [show k - 1 + 1 = k from by omega] at h4
        exact h4.2
      show Expr.lam (substT σ a) (substT σ.up b) = Expr.lam (substT τ a) (substT τ.up b)
      rw [substT_congr_below a c ha σ τ hστ,
        substT_congr_below b (c + 1) hb σ.up τ.up (substT_up_congr σ τ c hστ)]
  | .pi a b, c, h, σ, τ, hστ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.pi.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have h4 := h (k - 1) (by omega)
        simp only [lift, Expr.pi.injEq] at h4
        rw [show k - 1 + 1 = k from by omega] at h4
        exact h4.2
      show Expr.pi (substT σ a) (substT σ.up b) = Expr.pi (substT τ a) (substT τ.up b)
      rw [substT_congr_below a c ha σ τ hστ,
        substT_congr_below b (c + 1) hb σ.up τ.up (substT_up_congr σ τ c hστ)]
  | .letE a w b, c, h, σ, τ, hστ => by
      have ha : ∀ k, c ≤ k → lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [lift, Expr.letE.injEq] at this; exact this.1
      have hw : ∀ k, c ≤ k → lift k 1 w = w := fun k hk => by
        have := h k hk; simp only [lift, Expr.letE.injEq] at this; exact this.2.1
      have hb : ∀ k, c + 1 ≤ k → lift k 1 b = b := fun k hk => by
        have h4 := h (k - 1) (by omega)
        simp only [lift, Expr.letE.injEq] at h4
        rw [show k - 1 + 1 = k from by omega] at h4
        exact h4.2.2
      show Expr.letE (substT σ a) (substT σ w) (substT σ.up b) =
          Expr.letE (substT τ a) (substT τ w) (substT τ.up b)
      rw [substT_congr_below a c ha σ τ hστ,
        substT_congr_below w c hw σ τ hστ,
        substT_congr_below b (c + 1) hb σ.up τ.up (substT_up_congr σ τ c hστ)]

/-- `lift k 1 e = e` at a larger cutoff, from the smaller one: `e`'s variables stay below
    `i` already. -/
theorem lift_fixed_ge : (e : Expr Nat) → (i k : Nat) → i ≤ k → lift i 1 e = e →
    lift k 1 e = e
  | .bvar v, i, k, hik, h => by
      by_cases hv : v < i
      · rw [lift, if_neg (by omega : ¬ k ≤ v)]
      · rw [lift, if_pos (by omega : i ≤ v)] at h
        simp only [Expr.bvar.injEq] at h; omega
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .app f x, i, k, hik, h => by
      simp only [lift, Expr.app.injEq] at h ⊢
      exact ⟨lift_fixed_ge f i k hik h.1, lift_fixed_ge x i k hik h.2⟩
  | .lam a b, i, k, hik, h => by
      simp only [lift, Expr.lam.injEq] at h ⊢
      exact ⟨lift_fixed_ge a i k hik h.1,
        lift_fixed_ge b (i + 1) (k + 1) (Nat.succ_le_succ hik) h.2⟩
  | .pi a b, i, k, hik, h => by
      simp only [lift, Expr.pi.injEq] at h ⊢
      exact ⟨lift_fixed_ge a i k hik h.1,
        lift_fixed_ge b (i + 1) (k + 1) (Nat.succ_le_succ hik) h.2⟩
  | .letE a w b, i, k, hik, h => by
      simp only [lift, Expr.letE.injEq] at h ⊢
      exact ⟨lift_fixed_ge a i k hik h.1, lift_fixed_ge w i k hik h.2.1,
        lift_fixed_ge b (i + 1) (k + 1) (Nat.succ_le_succ hik) h.2.2⟩

/-- `liftChainStep` folded over `m` zero cutoffs adds `m`. -/
theorem foldl_liftChainStep_replicate : (m : Nat) → (i : Nat) →
    (List.replicate m 0).foldl liftChainStep i = i + m
  | 0, _ => rfl
  | m + 1, i => by
      show (List.replicate m 0).foldl liftChainStep (liftChainStep i 0) = _
      rw [show liftChainStep i 0 = i + 1 from by simp [liftChainStep],
        foldl_liftChainStep_replicate m (i + 1)]
      omega

/-- instantiating by the descending spine `[bvar (B+i-1), …, bvar B]` is `lift 0 B`
    on a term whose variables stay below `i`. -/
theorem instPrefix_descSpine (B i : Nat) (e : Expr Nat) (he : lift i 1 e = e) :
    instPrefix (descSpine B i) e = lift 0 B e := by
  rw [instPrefix_eq_substT]
  have hbound : ∀ k, i ≤ k → lift k 1 e = e := fun k hk => lift_fixed_ge e i k hk he
  have hσ : ∀ k, k < i → instPrefixSubst (descSpine B i) k =
      liftChainSub (List.replicate B 0) k := by
    intro k hk
    rw [instPrefixSubst_descSpine, if_pos hk]
    show (Expr.bvar (B + k) : Expr Nat) =
      Expr.bvar ((List.replicate B 0).foldl liftChainStep k)
    rw [foldl_liftChainStep_replicate]
    congr 1; omega
  rw [substT_congr_below e i hbound _ _ hσ, substT_liftChainSub, liftChain_replicate]

/-- the `k`-offset instantiate-chain: `instTelK 0 = instPrefix`, `instTelK 1 = instTel`;
    the residual-domain form `Is[k]` takes after `args` consume `k..k+|args|-1`. -/
def instTelK : Nat → List (Expr Nat) → Expr Nat → Expr Nat
  | _, [], e => e
  | k, a :: as, e =>
      instTelK k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e)

theorem instTelK_nil (k : Nat) (e : Expr Nat) : instTelK k [] e = e := rfl

theorem instTelK_cons (k : Nat) (a : Expr Nat) (as : List (Expr Nat)) (e : Expr Nat) :
    instTelK k (a :: as) e =
      instTelK k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e) := rfl

/-- `instTelK` as a parallel substitution (mirrors `instPrefixSubst`). -/
def instTelKSubst : Nat → List (Expr Nat) → SubstT
  | _, [] => SubstT.id
  | k, a :: as => fun i =>
      substT (instTelKSubst k as)
        (SubstT.single (k + as.length) (lift 0 (k + as.length) a) i)

/-- `instTelK` IS `instTelKSubst` applied. -/
theorem instTelK_eq_substT : (k : Nat) → (as : List (Expr Nat)) → (e : Expr Nat) →
    instTelK k as e = substT (instTelKSubst k as) e
  | _, [], e => (substT_id e).symm
  | k, a :: as, e => by
      show instTelK k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e) = _
      rw [instTelK_eq_substT k as, instantiate_eq_substT, substT_substT]
      rfl

/-- the offset spine substitution's pointwise action: below `k` untouched, in the arg
    window `k..k+i` it is `+B`, past it the consumed binders decrement. -/
theorem instTelKSubst_descSpine : (i : Nat) → (k B j : Nat) →
    instTelKSubst k (descSpine B i) j =
      if j < k then .bvar j else if j < k + i then .bvar (B + j) else .bvar (j - i)
  | 0, k, B, j => by
      show (SubstT.id : SubstT) j = _
      show (Expr.bvar j : Expr Nat) =
        if j < k then .bvar j else if j < k + 0 then .bvar (B + j) else .bvar (j - 0)
      by_cases h : j < k
      · rw [if_pos h]
      · rw [if_neg h, if_neg (by omega : ¬ j < k + 0), Nat.sub_zero]
  | i + 1, k, B, j => by
      rw [descSpine_succ]
      show substT (instTelKSubst k (descSpine B i))
          (SubstT.single (k + (descSpine B i).length)
            (lift 0 (k + (descSpine B i).length) (.bvar (B + i))) j) = _
      rw [descSpine_length]
      have hl : lift 0 (k + i) (Expr.bvar (B + i) : Expr Nat) = .bvar (B + i + (k + i)) :=
        if_pos (Nat.zero_le _)
      rw [hl]
      show substT (instTelKSubst k (descSpine B i))
          (if j = k + i then .bvar (B + i + (k + i)) else if k + i < j then .bvar (j - 1)
            else .bvar j) = _
      by_cases hjk : j = k + i
      · subst hjk
        rw [if_pos rfl]
        show instTelKSubst k (descSpine B i) (B + i + (k + i)) = _
        rw [instTelKSubst_descSpine i k B (B + i + (k + i))]
        rw [if_neg (by omega : ¬ B + i + (k + i) < k),
          if_neg (by omega : ¬ B + i + (k + i) < k + i),
          if_neg (by omega : ¬ k + i < k),
          if_pos (by omega : k + i < k + (i + 1))]
        congr 1; omega
      · by_cases hlt : k + i < j
        · rw [if_neg hjk, if_pos hlt]
          show instTelKSubst k (descSpine B i) (j - 1) = _
          rw [instTelKSubst_descSpine i k B (j - 1)]
          rw [if_neg (by omega : ¬ j - 1 < k), if_neg (by omega : ¬ j - 1 < k + i),
            if_neg (by omega : ¬ j < k), if_neg (by omega : ¬ j < k + (i + 1))]
          congr 1; omega
        · rw [if_neg hjk, if_neg hlt]
          show instTelKSubst k (descSpine B i) j = _
          rw [instTelKSubst_descSpine i k B j]
          by_cases hjk2 : j < k
          · rw [if_pos hjk2, if_pos hjk2]
          · rw [if_neg hjk2, if_neg hjk2, if_pos (by omega : j < k + i),
              if_pos (by omega : j < k + (i + 1))]

/-- `instTelK` by the descending spine `[bvar (B+i-1), …, bvar B]` is `lift k B` on a
    term whose variables stay below `k + i` (the offset `instPrefix_descSpine`). -/
theorem instTelK_descSpine (k B i : Nat) (e : Expr Nat) (he : lift (k + i) 1 e = e) :
    instTelK k (descSpine B i) e = lift k B e := by
  rw [instTelK_eq_substT]
  have hbound : ∀ m, k + i ≤ m → lift m 1 e = e :=
    fun m hm => lift_fixed_ge e (k + i) m hm he
  have hσ : ∀ j, j < k + i → instTelKSubst k (descSpine B i) j =
      liftChainSub ((List.range B).map (· + k)) j := by
    intro j hj
    rw [instTelKSubst_descSpine]
    show (if j < k then Expr.bvar j else if j < k + i then .bvar (B + j)
        else .bvar (j - i)) =
      Expr.bvar (((List.range B).map (· + k)).foldl liftChainStep j)
    rw [foldl_liftChainStep_consec]
    by_cases hjk : j < k
    · rw [if_pos hjk, if_neg (by omega : ¬ k ≤ j)]
      exact congrArg Expr.bvar (by omega : j = j + 0)
    · rw [if_neg hjk, if_pos hj, if_pos (by omega : k ≤ j)]
      exact congrArg Expr.bvar (Nat.add_comm B j)
  rw [substT_congr_below e (k + i) hbound _ _ hσ, substT_liftChainSub, liftChain_consec]

end Rcic.Declarative
