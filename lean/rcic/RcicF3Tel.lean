import rcic.RcicF3Env
import rcic.RcicF3Table

/-!
# F3 S4b: abstractions over a whole Π telescope

- `piLam M σ g ρ e`: the abstraction over every Π binder of `e`, with value
  `g` (read at the extended environment) at the end; `piLam_mem`: it is an
  element of `e`'s denotation when the end value is (`PiGood`);
- `fapps`: iterated application; `ed_fapps_emptyFam`: applying the empty
  family (end value `tyv ∅`) to any number of arguments up to its arity gives
  a value whose elements set is empty;
- `den_levels_agree`: the denotation of a term with levels bounded by `k`
  reads the level valuation only below `k`;
- `piLam_agree`: the value reads the constant table only at the term's refs.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs)

universe T

namespace PSet

/-- The abstraction over every Π binder of `e`, with end value `g`. -/
def piLam (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T}) :
    (Nat → PSet.{T}) → Expr Nat → PSet.{T}
  | ρ, .pi A B => lamVal M (den M σ ρ A) (fun x => piLam M σ g (vcons x ρ) B)
  | ρ, .bvar i => g ρ
  | ρ, .sort l => g ρ
  | ρ, .const r ls => g ρ
  | ρ, .app f a => g ρ
  | ρ, .lam A b => g ρ
  | ρ, .letE A v b => g ρ
  | ρ, .lit t => g ρ

/-- The end-value obligation along the telescope of `e`. -/
def PiGood (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T}) :
    (Nat → PSet.{T}) → Expr Nat → Prop
  | ρ, .pi A B => ∀ x, x ∈ Ed M (den M σ ρ A) → PiGood M σ g (vcons x ρ) B
  | ρ, .bvar i => g ρ ∈ Ed M (den M σ ρ (.bvar i))
  | ρ, .sort l => g ρ ∈ Ed M (den M σ ρ (.sort l))
  | ρ, .const r ls => g ρ ∈ Ed M (den M σ ρ (.const r ls))
  | ρ, .app f a => g ρ ∈ Ed M (den M σ ρ (.app f a))
  | ρ, .lam A b => g ρ ∈ Ed M (den M σ ρ (.lam A b))
  | ρ, .letE A v b => g ρ ∈ Ed M (den M σ ρ (.letE A v b))
  | ρ, .lit t => g ρ ∈ Ed M (den M σ ρ (.lit t))

/-- `g` respects pointwise-equivalent environments. -/
def EnvResp (g : (Nat → PSet.{T}) → PSet.{T}) : Prop :=
  ∀ ρ ρ' : Nat → PSet.{T}, (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (g ρ) (g ρ')

theorem envResp_const (v : PSet.{T}) : EnvResp (fun _ => v) := fun _ _ _ => Equiv.rfl

theorem piLam_congr (M : Interp.{T}) (σ : Nat → Nat) {g : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) : (e : Expr Nat) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (piLam M σ g ρ e) (piLam M σ g ρ' e)
  | .pi A B, ρ, ρ', h => lamVal_congr M (den_congr M σ A h)
      (fun x x' hx => piLam_congr M σ hg B (vcons_congr hx h))
  | .bvar _, _, _, h => hg _ _ h
  | .sort _, _, _, h => hg _ _ h
  | .const _ _, _, _, h => hg _ _ h
  | .app _ _, _, _, h => hg _ _ h
  | .lam _ _, _, _, h => hg _ _ h
  | .letE _ _ _, _, _, h => hg _ _ h
  | .lit _, _, _, h => hg _ _ h

theorem piLam_mem (M : Interp.{T}) (σ : Nat → Nat) {g : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) : (e : Expr Nat) → ∀ (ρ : Nat → PSet.{T}), PiGood M σ g ρ e →
      piLam M σ g ρ e ∈ Ed M (den M σ ρ e)
  | .pi A B, ρ, h => lam_mem M
      (fun x x' hx => piLam_congr M σ hg B (vcons_congr hx (fun _ => Equiv.rfl)))
      (den_resp M σ ρ B) (fun x hx => piLam_mem M σ hg B (vcons x ρ) (h x hx))
  | .bvar _, _, h => h
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .app _ _, _, h => h
  | .lam _ _, _, h => h
  | .letE _ _ _, _, h => h
  | .lit _, _, h => h

/-- Iterated application. -/
def fapps : PSet.{T} → List PSet.{T} → PSet.{T}
  | F, [] => F
  | F, a :: as => fapps (fapp F a) as

theorem fapps_congr : {F F' : PSet.{T}} → Equiv F F' → (as : List PSet.{T}) →
    Equiv (fapps F as) (fapps F' as)
  | _, _, h, [] => h
  | _, _, h, _ :: as => fapps_congr (fapp_congr h Equiv.rfl) as

theorem fapps_pempty : (as : List PSet.{T}) → Equiv (fapps pempty as) pempty
  | [] => Equiv.rfl
  | a :: as => (fapps_congr (fapp_pempty a) as).trans (fapps_pempty as)

theorem fapp_mkLam_out {g : PSet.{T} → PSet.{T}} {A a : PSet.{T}} (ha : ¬ a ∈ A) :
    Equiv (fapp (mkLam g A) a) pempty := by
  refine ext fun z => ⟨fun hz => ?_, fun hz => (not_mem_pempty hz).elim⟩
  obtain ⟨w, hw, _⟩ := mem_sUnion.mp hz
  obtain ⟨_, hp, _⟩ := mem_sep.mp hw
  obtain ⟨i, hi⟩ := (show ordPair a _ ∈ sImage (fun a => ordPair a (g a)) A from hp)
  exact (ha ⟨i, (ordPair_equiv hi).1⟩).elim

theorem el_pempty : Equiv (El (pempty : PSet.{T})) pempty := by
  refine ext fun z => ⟨fun hz => ?_, fun hz => (not_mem_pempty hz).elim⟩
  obtain ⟨w, hw, _⟩ := mem_sUnion.mp hz
  obtain ⟨_, _, he⟩ := mem_sep.mp hw
  have := mem_sep_subset hw
  obtain ⟨u, hu, _⟩ := mem_sUnion.mp this
  exact (not_mem_pempty hu).elim

theorem ed_pempty (M : Interp.{T}) : Equiv (Ed M pempty) pempty := by
  rw [ed_of_dich M ((dich_congr el_pempty.symm).mp (Or.inl fun _ h => (not_mem_pempty h).elim))]
  exact el_pempty

theorem ed_tyv_empty (M : Interp.{T}) : Equiv (Ed M (tyv pempty)) pempty :=
  ed_tyv M (Or.inl fun _ h => (not_mem_pempty h).elim)

/-- Number of leading Π binders. -/
def piArity : Expr Nat → Nat
  | .pi _ B => piArity B + 1
  | _ => 0

/-- The empty family: applying it to at most its arity many arguments and
reading the element set gives the empty set (when the end is reached the
value is `tyv ∅`; arguments outside a domain give `∅`). -/
theorem ed_fapps_emptyFam (M : Interp.{T}) (σ : Nat → Nat) :
    (e : Expr Nat) → ∀ (ρ : Nat → PSet.{T}) (as : List PSet.{T}), as.length = piArity e →
      Equiv (Ed M (fapps (piLam M σ (fun _ => tyv pempty) ρ e) as)) pempty
  | .pi A B, ρ, [], h => absurd h.symm (Nat.succ_ne_zero _)
  | .pi A B, ρ, a :: as, h => by
      have hl : as.length = piArity B := Nat.succ.inj h
      show Equiv (Ed M (fapps (fapp (lamVal M (den M σ ρ A) _) a) as)) pempty
      cases hd : M.dec (LamProof M (den M σ ρ A) (fun x => piLam M σ (fun _ => tyv pempty) (vcons x ρ) B)) with
      | isTrue hp =>
          have e1 : lamVal M (den M σ ρ A) (fun x => piLam M σ (fun _ => tyv pempty) (vcons x ρ) B) = pempty := by
            unfold lamVal cond; rw [hd]; rfl
          rw [e1]
          exact (ed_congr M ((fapps_congr (fapp_pempty a) as).trans (fapps_pempty as))).trans (ed_pempty M)
      | isFalse hp =>
          have e1 : lamVal M (den M σ ρ A) (fun x => piLam M σ (fun _ => tyv pempty) (vcons x ρ) B) =
              mkLam (fun x => piLam M σ (fun _ => tyv pempty) (vcons x ρ) B) (Ed M (den M σ ρ A)) := by
            unfold lamVal cond; rw [hd]; rfl
          rw [e1]
          cases hm : M.dec (a ∈ Ed M (den M σ ρ A)) with
          | isTrue ha =>
              have e2 := fapp_mkLam (fun x y hxy => piLam_congr M σ (envResp_const (tyv pempty)) B
                (vcons_congr (ρ := ρ) (ρ' := ρ) hxy (fun _ => Equiv.rfl))) ha
              exact (ed_congr M (fapps_congr e2 as)).trans (ed_fapps_emptyFam M σ B (vcons a ρ) as hl)
          | isFalse ha =>
              exact (ed_congr M ((fapps_congr (fapp_mkLam_out ha) as).trans (fapps_pempty as))).trans
                (ed_pempty M)
  | .bvar _, ρ, [], _ => ed_tyv_empty M
  | .sort _, ρ, [], _ => ed_tyv_empty M
  | .const _ _, ρ, [], _ => ed_tyv_empty M
  | .app _ _, ρ, [], _ => ed_tyv_empty M
  | .lam _ _, ρ, [], _ => ed_tyv_empty M
  | .letE _ _ _, ρ, [], _ => ed_tyv_empty M
  | .lit _, ρ, [], _ => ed_tyv_empty M
  | .bvar _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .sort _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .const _ _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .app _ _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .lam _ _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .letE _ _ _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .lit _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)

theorem evalTotal_agree {σ σ' : Nat → Nat} {k : Nat} (h : ∀ i, i < k → σ i = σ' i) :
    (l : Level) → levelBounded k l = true → evalTotal σ l = evalTotal σ' l
  | .zero, _ => rfl
  | .succ l, hb => by simp only [evalTotal, evalTotal_agree h l hb]
  | .max a b, hb => by
      simp only [levelBounded, Bool.and_eq_true] at hb
      simp only [evalTotal, evalTotal_agree h a hb.1, evalTotal_agree h b hb.2]
  | .imax a b, hb => by
      simp only [levelBounded, Bool.and_eq_true] at hb
      simp only [evalTotal, evalTotal_agree h a hb.1, evalTotal_agree h b hb.2]
  | .param i, hb => by
      simp only [levelBounded, decide_eq_true_eq] at hb
      simp only [evalTotal, h i hb]

theorem map_evalTotal_agree {σ σ' : Nat → Nat} {k : Nat} (h : ∀ i, i < k → σ i = σ' i) :
    (ls : List Level) → levelsBounded k ls = true → ls.map (evalTotal σ) = ls.map (evalTotal σ')
  | [], _ => rfl
  | l :: ls, hb => by
      simp only [levelsBounded, Bool.and_eq_true] at hb
      simp only [List.map_cons, evalTotal_agree h l hb.1, map_evalTotal_agree h ls hb.2]

/-- A term whose levels are bounded by `k` reads the level valuation only below `k`. -/
theorem den_levels_agree (M : Interp.{T}) {σ σ' : Nat → Nat} {k : Nat}
    (h : ∀ i, i < k → σ i = σ' i) :
    (e : Expr Nat) → exprLevelsBounded k e = true → ∀ ρ, den M σ ρ e = den M σ' ρ e
  | .bvar _, _, _ => rfl
  | .sort l, hb, _ => by
      show tyv (M.U (evalTotal σ l)) = tyv (M.U (evalTotal σ' l))
      rw [evalTotal_agree h l hb]
  | .const r ls, hb, _ => by
      show M.μ r (ls.map (evalTotal σ)) = M.μ r (ls.map (evalTotal σ'))
      rw [map_evalTotal_agree h ls hb]
  | .lit _, _, _ => rfl
  | .app f a, hb, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      show fapp _ _ = fapp _ _
      rw [den_levels_agree M h f hb.1 ρ, den_levels_agree M h a hb.2 ρ]
  | .lam A b, hb, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      show lamVal _ _ _ = lamVal _ _ _
      rw [den_levels_agree M h A hb.1 ρ]
      have : (fun x => den M σ (vcons x ρ) b) = (fun x => den M σ' (vcons x ρ) b) :=
        funext fun x => den_levels_agree M h b hb.2 _
      rw [this]
  | .pi A B, hb, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      show piVal _ _ _ = piVal _ _ _
      rw [den_levels_agree M h A hb.1 ρ]
      have : (fun x => den M σ (vcons x ρ) B) = (fun x => den M σ' (vcons x ρ) B) :=
        funext fun x => den_levels_agree M h B hb.2 _
      rw [this]
  | .letE A v b, hb, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      show den M σ (vcons (den M σ ρ v) ρ) b = den M σ' (vcons (den M σ' ρ v) ρ) b
      rw [den_levels_agree M h v hb.1.2 ρ]
      exact den_levels_agree M h b hb.2 _

/-- `piLam` reads the constant table only at the term's refs. -/
theorem piLam_agree (M : Interp.{T}) {μ₁ μ₂ : Nat → List Nat → PSet.{T}} (σ : Nat → Nat)
    (g : (Nat → PSet.{T}) → PSet.{T}) :
    (e : Expr Nat) → (∀ r, r ∈ denRefs e → ∀ ls, μ₁ r ls = μ₂ r ls) →
      ∀ ρ, piLam (withμ M μ₁) σ g ρ e = piLam (withμ M μ₂) σ g ρ e
  | .pi A B, h, ρ => by
      show lamVal _ _ _ = lamVal _ _ _
      rw [den_agree M σ A (fun r hr => h r (by simp [denRefs, hr])) ρ]
      have : (fun x => piLam (withμ M μ₁) σ g (vcons x ρ) B) =
          (fun x => piLam (withμ M μ₂) σ g (vcons x ρ) B) :=
        funext fun x => piLam_agree M σ g B (fun r hr => h r (by simp [denRefs, hr])) _
      rw [this]
      rfl
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app _ _, _, _ => rfl
  | .lam _ _, _, _ => rfl
  | .letE _ _ _, _, _ => rfl
  | .lit _, _, _ => rfl

/-- The denotation of an application spine. -/
theorem den_foldApps (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) :
    (f : Expr Nat) → (as : List (Expr Nat)) →
      den M σ ρ (foldApps f as) = fapps (den M σ ρ f) (as.map (den M σ ρ))
  | _, [] => rfl
  | f, a :: as => den_foldApps M σ ρ (.app f a) as

theorem piArity_policyPi : (Ds : List (Expr Nat)) → (b : Expr Nat) →
    piArity (policyPi Ds b) = Ds.length + piArity b
  | [], _ => by simp [policyPi]
  | A :: Ds, b => by
      show piArity (policyPi Ds b) + 1 = _
      rw [piArity_policyPi Ds b]; simp; omega

/-- `PiGood` through a `policyPi` telescope. -/
theorem piGood_policyPi (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T})
    (b : Expr Nat) (hb : ∀ ρ, PiGood M σ g ρ b) :
    (Ds : List (Expr Nat)) → ∀ ρ, PiGood M σ g ρ (policyPi Ds b)
  | [], ρ => hb ρ
  | _ :: Ds, ρ => fun x _ => piGood_policyPi M σ g b hb Ds (vcons x ρ)

end PSet

end Rcic.F3
