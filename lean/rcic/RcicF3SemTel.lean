import rcic.RcicF3Iota
import rcic.RcicTypedLevels

/-!
# F3 S5b-7a: telescopes read semantically

`SemTel M σ ρ T Fs σF ρF`: the domains of `T` are the fields `Fs` under
homomorphic substitutions which, read at `σ` and `ρ` below any further
values, are the fields read at `σF` and `ρF` below the same values.
The constructor telescope after the parameters, as an ι redex reads it,
has this shape (`semTel_instantiateLevels`, `SemTel.applyTel`), and one
instantiation step keeps it (`SemTel.step`). ι for recursive fields with
indices reads the recursive call's indices through it.

Also: `insρ_push`, `instFields_getElem`, and the syntactic facts on closed,
level-bounded family applications the ι proof uses.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

theorem insρ_push (y : PSet.{T}) (ρ : Nat → PSet.{T}) (vs : List PSet.{T}) :
    insρ vs.length y (push vs ρ) = push vs (vcons y ρ) := by
  funext i
  unfold insρ
  by_cases h1 : i = vs.length
  · subst h1
    rw [if_pos rfl]
    have := push_ge vs (vcons y ρ) 0
    rw [Nat.zero_add] at this
    rw [this]
    rfl
  · rw [if_neg h1]
    by_cases h2 : vs.length < i
    · rw [if_pos h2]
      obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 + vs.length := ⟨i - 1 - vs.length, by omega⟩
      rw [show d + 1 + vs.length - 1 = d + vs.length by omega, push_ge, push_ge]
      rfl
    · rw [if_neg h2]
      have hi : i < vs.length := by omega
      rw [push_lt _ _ _ hi, push_lt _ _ _ hi]

theorem instFields_getElem (a : Expr Nat) : (c : Nat) → (Ds : List (Expr Nat)) → (m : Nat) →
    (hm : m < Ds.length) → (hm' : m < (instFields a c Ds).length) →
    (instFields a c Ds)[m] = instantiate (c + m) (liftIter m a) Ds[m]
  | _, _ :: _, 0, _, _ => rfl
  | c, _ :: Ds, m + 1, hm, hm' => by
      have := instFields_getElem (Rcic.Declarative.lift 0 1 a) (c + 1) Ds m (by simpa using hm)
        (by simpa [instFields] using hm')
      simp only [instFields, List.getElem_cons_succ]
      rw [this, show c + 1 + m = c + (m + 1) by omega]
      rfl

theorem instantiateLevels_policyPi (ls : List Level) (b : Expr Nat) : (Ds : List (Expr Nat)) →
    instantiateLevels ls (policyPi Ds b) = policyPi (Ds.map (instantiateLevels ls)) (instantiateLevels ls b)
  | [] => rfl
  | D :: Ds => by
      show Expr.pi _ _ = _
      rw [instantiateLevels_policyPi ls b Ds]
      rfl

/-- The domains of `T` are the fields `Fs`, syntactically under homomorphic
substitutions and semantically below any further values. -/
def SemTel (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (Tl : Expr Nat) (Fs : List (Expr Nat))
    (σF : Nat → Nat) (ρF : Nat → PSet.{T}) : Prop :=
  ∃ (Ds : List (Expr Nat)) (b : Expr Nat), Tl = policyPi Ds b ∧ Ds.length = Fs.length ∧
    ∀ (m : Nat) (h1 : m < Ds.length) (h2 : m < Fs.length), ∃ I, HomSub I ∧ Ds[m] = I Fs[m] ∧
      ∀ (e : Expr Nat) (vs : List PSet.{T}), vs.length = m →
        den M σ (push vs ρ) (I e) = den M σF (push vs ρF) e

/-- A stored telescope at a level instantiation. -/
theorem semTel_instantiateLevels (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (ls : List Level)
    (Ds : List (Expr Nat)) (b : Expr Nat) :
    SemTel M σ ρ (instantiateLevels ls (policyPi Ds b)) Ds
      (fun i => ((ls.map (evalTotal σ))[i]?).getD (σ i)) ρ := by
  refine ⟨Ds.map (instantiateLevels ls), instantiateLevels ls b, instantiateLevels_policyPi ls b Ds,
    List.length_map _ _, fun m h1 h2 => ⟨instantiateLevels ls, homSub_instantiateLevels ls, ?_, ?_⟩⟩
  · simp
  · intro e vs _
    exact den_instantiateLevels M σ e ls

/-- One instantiation step keeps the shape; the field side gains the value. -/
theorem SemTel.step {M : Interp.{T}} {σ : Nat → Nat} {ρ : Nat → PSet.{T}} {A B F : Expr Nat}
    {Fs : List (Expr Nat)} {σF : Nat → Nat} {ρF : Nat → PSet.{T}}
    (h : SemTel M σ ρ (.pi A B) (F :: Fs) σF ρF) (a : Expr Nat) :
    SemTel M σ ρ (instantiate0 a B) Fs σF (vcons (den M σ ρ a) ρF) := by
  obtain ⟨Ds, b, hT, hl, hD⟩ := h
  cases Ds with
  | nil => exact (Nat.succ_ne_zero _ hl.symm).elim
  | cons D Ds =>
      have hT' : Expr.pi A B = Expr.pi D (policyPi Ds b) := hT
      cases hT'
      obtain ⟨b', hb'⟩ := instantiate_policyPi Ds a b 0
      refine ⟨instFields a 0 Ds, b', hb', by rw [instFields_length]; simpa using hl, fun m h1 h2 => ?_⟩
      have h1' : m < Ds.length := by rw [instFields_length] at h1; exact h1
      obtain ⟨I, hI, hIe, hIs⟩ := hD (m + 1) (by simpa using h1') (by simpa using h2)
      refine ⟨instantiate m (liftIter m a) ∘ I, hI.comp (homSub_instantiate _ _), ?_, fun e vs hv => ?_⟩
      · rw [instFields_getElem a 0 Ds m h1' h1, Nat.zero_add]
        simp only [List.getElem_cons_succ] at hIe
        rw [hIe]
        rfl
      · show den M σ (push vs ρ) (instantiate m (liftIter m a) (I e)) = _
        rw [den_instantiate, ← hv, den_liftIter, insρ_push]
        have := hIs e (den M σ ρ a :: vs) (by simp [hv])
        exact this

/-- Applying terms to a telescope keeps the shape of the remaining domains. -/
theorem SemTel.applyTel {M : Interp.{T}} {σ : Nat → Nat} {ρ : Nat → PSet.{T}} :
    (as : List (Expr Nat)) → (Ps Fs : List (Expr Nat)) → as.length = Ps.length →
    (Tl Tl' : Expr Nat) → {σF : Nat → Nat} → {ρF : Nat → PSet.{T}} →
    SemTel M σ ρ Tl (Ps ++ Fs) σF ρF → applyTel as Tl = some Tl' →
    SemTel M σ ρ Tl' Fs σF (push (as.map (den M σ ρ)) ρF)
  | [], [], Fs, _, Tl, Tl', _, _, h, hT => by
      have hT' : Tl = Tl' := Option.some.inj hT
      subst hT'; simpa using h
  | a :: as, P :: Ps, Fs, hl, Tl, Tl', _, _, h, hT => by
      obtain ⟨A, B, hAB, hrest⟩ := applyTel_cons_inv a as hT
      subst hAB
      exact SemTel.applyTel as Ps Fs (Nat.succ.inj hl) _ Tl' (SemTel.step h a) hrest
  | [], _ :: _, _, hl, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], _, hl, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hl).elim

/-- The head domain is the head field, syntactically and semantically. -/
theorem SemTel.head {M : Interp.{T}} {σ : Nat → Nat} {ρ : Nat → PSet.{T}} {A B F : Expr Nat}
    {Fs : List (Expr Nat)} {σF : Nat → Nat} {ρF : Nat → PSet.{T}}
    (h : SemTel M σ ρ (.pi A B) (F :: Fs) σF ρF) :
    ∃ I, HomSub I ∧ A = I F ∧ ∀ e, den M σ ρ (I e) = den M σF ρF e := by
  obtain ⟨Ds, b, hT, hl, hD⟩ := h
  cases Ds with
  | nil => exact (Nat.succ_ne_zero _ hl.symm).elim
  | cons D Ds =>
      have hT' : Expr.pi A B = Expr.pi D (policyPi Ds b) := hT
      cases hT'
      obtain ⟨I, hI, hIe, hIs⟩ := hD 0 (by simp) (by simp)
      exact ⟨I, hI, hIe, fun e => hIs e [] rfl⟩

/-! ### closed, level-bounded family applications -/

theorem lift_foldApps_fixed (c : Nat) : (h : Expr Nat) → (as : List (Expr Nat)) →
    Rcic.Declarative.lift c 1 (foldApps h as) = foldApps h as →
    Rcic.Declarative.lift c 1 h = h ∧ ∀ e, e ∈ as → Rcic.Declarative.lift c 1 e = e
  | _, [], hf => ⟨hf, fun _ he => absurd he (List.not_mem_nil _)⟩
  | h, a :: as, hf => by
      obtain ⟨hha, has⟩ := lift_foldApps_fixed c (.app h a) as hf
      simp only [Rcic.Declarative.lift] at hha
      injection hha with hh ha
      exact ⟨hh, fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact ha
        · exact has e he⟩

theorem lift_policyPi_fixed : (Ds : List (Expr Nat)) → (b : Expr Nat) → (c : Nat) →
    Rcic.Declarative.lift c 1 (policyPi Ds b) = policyPi Ds b →
    ∀ (m : Nat) (hm : m < Ds.length), Rcic.Declarative.lift (c + m) 1 Ds[m] = Ds[m]
  | D :: Ds, b, c, h, m, hm => by
      have h' : Expr.pi (Rcic.Declarative.lift c 1 D) (Rcic.Declarative.lift (c + 1) 1 (policyPi Ds b)) =
          Expr.pi D (policyPi Ds b) := h
      injection h' with hD hB
      cases m with
      | zero => exact hD
      | succ m =>
          have := lift_policyPi_fixed Ds b (c + 1) hB m (by simpa using hm)
          rw [show c + (m + 1) = c + 1 + m by omega]
          exact this

theorem lift_policyPi_append_fixed (Fs : List (Expr Nat)) (b : Expr Nat) : (Ps : List (Expr Nat)) → (c : Nat) →
    Rcic.Declarative.lift c 1 (policyPi (Ps ++ Fs) b) = policyPi (Ps ++ Fs) b →
    ∀ (k : Nat) (hk : k < Fs.length), Rcic.Declarative.lift (c + Ps.length + k) 1 Fs[k] = Fs[k]
  | [], c, h, k, hk => lift_policyPi_fixed Fs b c h k hk
  | P :: Ps, c, h, k, hk => by
      have h' : Expr.pi (Rcic.Declarative.lift c 1 P) (Rcic.Declarative.lift (c + 1) 1 (policyPi (Ps ++ Fs) b)) =
          Expr.pi P (policyPi (Ps ++ Fs) b) := h
      injection h' with _ hB
      have := lift_policyPi_append_fixed Fs b Ps (c + 1) hB k hk
      rw [show c + (P :: Ps).length + k = c + 1 + Ps.length + k by simp only [List.length_cons]; omega]
      exact this

/-- Below `ps` and `ys`, the environment's base is not read. -/
theorem push_push_agree (ys ps : List PSet.{T}) (R R' : Nat → PSet.{T}) (i : Nat)
    (hi : i < ps.length + ys.length) : push ys (push ps R) i = push ys (push ps R') i := by
  by_cases h : i < ys.length
  · rw [push_lt _ _ _ h, push_lt _ _ _ h]
  · obtain ⟨d, rfl⟩ : ∃ d, i = d + ys.length := ⟨i - ys.length, by omega⟩
    rw [push_ge, push_ge, push_lt _ _ _ (by omega), push_lt _ _ _ (by omega)]

theorem levelsBounded_policyPi (k : Nat) : (D : List (Expr Nat)) → (b : Expr Nat) →
    exprLevelsBounded k (policyPi D b) = true → ExprsBounded k D ∧ exprLevelsBounded k b = true
  | [], b, h => ⟨fun _ he => absurd he (List.not_mem_nil _), h⟩
  | A :: D, b, h => by
      have h' : (exprLevelsBounded k A && exprLevelsBounded k (policyPi D b)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hD, hb⟩ := levelsBounded_policyPi k D b h'.2
      refine ⟨fun e he => ?_, hb⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact h'.1
      · exact hD e he

theorem levelsBounded_foldApps (k : Nat) : (f : Expr Nat) → (as : List (Expr Nat)) →
    exprLevelsBounded k (foldApps f as) = true → exprLevelsBounded k f = true ∧ ExprsBounded k as
  | f, [], h => ⟨h, fun _ he => absurd he (List.not_mem_nil _)⟩
  | f, a :: as, h => by
      obtain ⟨hfa, has⟩ := levelsBounded_foldApps k (.app f a) as h
      have hfa' : (exprLevelsBounded k f && exprLevelsBounded k a) = true := hfa
      rw [Bool.and_eq_true] at hfa'
      refine ⟨hfa'.1, fun e he => ?_⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hfa'.2
      · exact has e he

end PSet

end Rcic.F3
