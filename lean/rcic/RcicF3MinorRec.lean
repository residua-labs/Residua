import rcic.RcicF3FamLim
import rcic.RcicF3RecCore

/-!
# F3 S5b-3b: minor premises with recursive fields

- `den_tables`: the denotation respects pointwise-`≈` tables;
- `minor_sem`: the semantic reading of `minorFromTelescope` with
  non-recursive and directly recursive shapes. An element of the derived
  minor type, applied to fitting fields followed after each recursive field
  by an element of the motive at that field's indices and the field, lands
  in the motive at the end's indices and the accumulated constructor value.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

theorem denLit_tables (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} (h : ∀ r ls, Equiv (μ₁ r ls) (μ₂ r ls)) :
    (t : Nat) → Equiv (denLit (mkM P μ₁) t) (denLit (mkM P μ₂) t)
  | 0 => h 1 []
  | t + 1 => fapp_congr (h 2 []) (denLit_tables P h t)

/-- The denotation respects pointwise-`≈` tables. -/
theorem den_tables (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} (h : ∀ r ls, Equiv (μ₁ r ls) (μ₂ r ls))
    (σ : Nat → Nat) : (e : Expr Nat) → ∀ {ρ ρ' : Nat → PSet.{4}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ' e)
  | .bvar i, _, _, hρ => hρ i
  | .sort _, _, _, _ => Equiv.rfl
  | .const r _, _, _, _ => h r _
  | .app f a, _, _, hρ => fapp_congr (den_tables P h σ f hρ) (den_tables P h σ a hρ)
  | .lam A b, _, _, hρ => lamVal_congr (mkM P μ₂) (den_tables P h σ A hρ)
      (fun _ _ hx => den_tables P h σ b (vcons_congr hx hρ))
  | .pi A B, _, _, hρ => piVal_congr (mkM P μ₂) (den_tables P h σ A hρ)
      (fun _ _ hx => den_tables P h σ B (vcons_congr hx hρ))
  | .letE _ v b, _, _, hρ => den_tables P h σ b (vcons_congr (den_tables P h σ v hρ) hρ)
  | .lit t, _, _, _ => denLit_tables P h t

/-! ### syntax -/

theorem appsSpine_lift (c s : Nat) : (e : Expr Nat) →
    appsSpine (Rcic.Declarative.lift c s e) =
      (Rcic.Declarative.lift c s (appsSpine e).1, (appsSpine e).2.map (Rcic.Declarative.lift c s))
  | .app f x => by
      have ih := appsSpine_lift c s f
      show appsSpine (Expr.app (Rcic.Declarative.lift c s f) (Rcic.Declarative.lift c s x)) = _
      simp only [appsSpine, ih, List.map_append, List.map_cons, List.map_nil]
  | .bvar _ => by simp only [Rcic.Declarative.lift]; split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem familyIdx_lift (np c s : Nat) (e : Expr Nat) :
    familyIdx np (Rcic.Declarative.lift c s e) = (familyIdx np e).map (Rcic.Declarative.lift c s) := by
  simp only [familyIdx, appsSpine_lift, List.map_drop]

/-- A field headed by the family. -/
def RecHead (f : Nat) (A : Expr Nat) : Prop :=
  ∃ (ls : List Level) (args : List (Expr Nat)), A = foldApps (.const f ls) args

theorem RecHead.lift {f : Nat} {A : Expr Nat} (h : RecHead f A) (c s : Nat) :
    RecHead f (Rcic.Declarative.lift c s A) := by
  obtain ⟨ls, args, rfl⟩ := h
  exact ⟨ls, args.map (Rcic.Declarative.lift c s), by rw [lift_foldApps]; rfl⟩

/-- The induction hypothesis type of a recursive field headed by an opaque family. -/
theorem funIHType_recHead {E : ResolvedEnv} {fuel np : Nat} {f : Nat} (hop : ∀ ls, transparentBody E f ls = none)
    {A M ih : Expr Nat} (hA : RecHead f A) (h : funIHType E fuel np A M 0 = some ih) :
    ih = foldApps (Rcic.Declarative.lift 0 1 M) ((familyIdx np A).map (Rcic.Declarative.lift 0 1) ++ [.bvar 0]) := by
  obtain ⟨ls, args, rfl⟩ := hA
  have hl : Rcic.Declarative.lift 0 1 (foldApps (.const f ls) args) =
      foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1)) := by rw [lift_foldApps]; rfl
  unfold funIHType at h
  rw [hl] at h
  match fuel, h with
  | 0, h => simp [piTelescopeFuel] at h
  | 1, h => simp [piTelescopeFuel, whnfFuel] at h
  | k + 2, h =>
      have hw : whnfFuel E (k + 1) (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1))) =
          some (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1))) := by
        unfold whnfFuel
        rw [appsSpine_foldApps]
        simp only [appsSpine, List.nil_append, hop]
      have hnp : ∀ (A' B' : Expr Nat), foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1)) ≠ .pi A' B' :=
        foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _
      have hpt : piTelescopeFuel E (k + 2) (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1))) =
          some ([], foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1))) := by
        show (match whnfFuel E (k + 1) _ with
          | none => none
          | some (.pi A B) => _
          | some w => some ([], w)) = _
        rw [hw]
        generalize hfa : foldApps (.const f ls) (args.map (Rcic.Declarative.lift 0 1)) = fa
        rw [hfa] at hnp
        cases fa with
        | pi A' B' => exact absurd rfl (hnp A' B')
        | _ => rfl
      rw [hpt] at h
      simp only [List.length_nil, if_true, Option.some.injEq] at h
      rw [← h, familyIdx_foldApps_const, familyIdx_foldApps_const, lift_zero_idx, policyPi, List.map_drop]
      rfl

/-! ### the semantic minor -/

/-- A minor's arguments: each field, followed for a recursive field by `g` at it. -/
def shArgs (g : PSet.{4} → PSet.{4}) : List FieldShape → List PSet.{4} → List PSet.{4}
  | .recursive _ :: ss, x :: xs => x :: g x :: shArgs g ss xs
  | .nonrecursive :: ss, x :: xs => x :: shArgs g ss xs
  | _, _ => []

/-- `g` at each recursive field lies in the motive at the field's indices and the field. -/
def IHOk (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4}) :
    List FieldShape → List (Expr Nat) → (Nat → PSet.{4}) → List PSet.{4} → Prop
  | s :: ss, A :: Fs, ρ, x :: xs =>
      (s = .recursive 0 → g x ∈ Ed M (fapps mo ((familyIdx np A).map (den M σ ρ) ++ [x]))) ∧
        IHOk M σ np mo g ss Fs (vcons x ρ) xs
  | _, _, _, _ => True

theorem IHOk_liftFields (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4})
    (ys : List PSet.{4}) (R : Nat → PSet.{4}) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → (zs xs : List PSet.{4}) →
    (IHOk M σ np mo g ss (liftFields ys.length Fs zs.length) (push zs (push ys R)) xs ↔
      IHOk M σ np mo g ss Fs (push zs R) xs)
  | [], _, _, _ => Iff.rfl
  | _ :: _, [], _, _ => Iff.rfl
  | _ :: _, _ :: _, _, [] => Iff.rfl
  | s :: ss, A :: Fs, zs, x :: xs => by
      show ((s = .recursive 0 → g x ∈ Ed M (fapps mo ((familyIdx np (Rcic.Declarative.lift zs.length ys.length A)).map
            (den M σ (push zs (push ys R))) ++ [x]))) ∧
          IHOk M σ np mo g ss (liftFields ys.length Fs (zs.length + 1)) (vcons x (push zs (push ys R))) xs) ↔
        ((s = .recursive 0 → g x ∈ Ed M (fapps mo ((familyIdx np A).map (den M σ (push zs R)) ++ [x]))) ∧
          IHOk M σ np mo g ss Fs (vcons x (push zs R)) xs)
      have e1 : (familyIdx np (Rcic.Declarative.lift zs.length ys.length A)).map (den M σ (push zs (push ys R))) =
          (familyIdx np A).map (den M σ (push zs R)) := by
        rw [familyIdx_lift, List.map_map]
        exact List.map_congr_left fun e _ => den_lift_push M σ zs ys R e
      have h1 : vcons x (push zs (push ys R)) = push (zs ++ [x]) (push ys R) := by rw [push_append]; rfl
      have h2 : vcons x (push zs R) = push (zs ++ [x]) R := by rw [push_append]; rfl
      have hl : zs.length + 1 = (zs ++ [x]).length := by simp
      rw [e1, h1, h2, hl, IHOk_liftFields M σ np mo g ys R ss Fs (zs ++ [x]) xs]

theorem liftFields_getElem? (s : Nat) : (Fs : List (Expr Nat)) → (c k : Nat) →
    (liftFields s Fs c)[k]? = Fs[k]?.map (Rcic.Declarative.lift (c + k) s)
  | [], _, _ => by simp [liftFields]
  | A :: Fs, c, 0 => by simp [liftFields]
  | A :: Fs, c, k + 1 => by
      simp only [liftFields, List.getElem?_cons_succ]
      rw [liftFields_getElem? s Fs (c + 1) k, show c + 1 + k = c + (k + 1) by omega]

theorem den_lift01 (M : Interp.{4}) (σ : Nat → Nat) (x : PSet.{4}) (ρ : Nat → PSet.{4}) (e : Expr Nat) :
    den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 e) = den M σ ρ e := den_lift0_push M σ [x] ρ e

theorem den_lift02 (M : Interp.{4}) (σ : Nat → Nat) (x y : PSet.{4}) (ρ : Nat → PSet.{4}) (e : Expr Nat) :
    den M σ (vcons y (vcons x ρ)) (Rcic.Declarative.lift 0 2 e) = den M σ ρ e := den_lift0_push M σ [x, y] ρ e

/-- **The semantic minor.** -/
theorem minor_sem (M : Interp.{4}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat) {f : Nat}
    (hop : ∀ ls, transparentBody E f ls = none) (g : PSet.{4} → PSet.{4}) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → (Tend Mx acc R : Expr Nat) → (ρ : Nat → PSet.{4}) →
    (F : PSet.{4}) → (xs : List PSet.{4}) →
    (∀ (k : Nat) (s : FieldShape) (A : Expr Nat), ss[k]? = some s → Fs[k]? = some A →
      s = .nonrecursive ∨ (s = .recursive 0 ∧ RecHead f A)) →
    ss.length = Fs.length →
    minorFromTelescope E fuel np Mx acc ss (policyPi Fs Tend) = some R →
    F ∈ Ed M (den M σ ρ R) → TelFits M σ Fs ρ xs → IHOk M σ np (den M σ ρ Mx) g ss Fs ρ xs →
    fapps F (shArgs g ss xs) ∈ Ed M (fapp (fapps (den M σ ρ Mx) ((familyIdx np Tend).map (den M σ (push xs ρ))))
      (fapps (den M σ ρ acc) xs))
  | [], [], Tend, Mx, acc, R, ρ, F, [], _, _, hR, hF, _, _ => by
      simp only [policyPi, minorFromTelescope, Option.some.injEq] at hR
      subst hR
      have hF' : F ∈ Ed M (fapp (den M σ ρ (foldApps Mx (familyIdx np Tend))) (den M σ ρ acc)) := hF
      rw [den_foldApps] at hF'
      exact hF'
  | [], _ :: _, _, _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, _, _, _, _, _, _, [], _, _, _, _, hx, _ => hx.elim
  | .nonrecursive :: ss, A :: Fs, Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hR, hF, ⟨hx, hfs⟩, ⟨_, hih⟩ => by
      have hR' : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 1 Mx)
          (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss (policyPi Fs Tend)).map (fun rest => .pi A rest) =
          some R := hR
      obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR'
      have h1 := app_mem M (fun y y' hy => den_congr M σ R' (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
      have ih := minor_sem M σ E fuel np hop g ss Fs Tend _ _ R' (vcons x ρ) (fapp F x) xs
        (fun k s A' h1 h2 => hsh (k + 1) s A' (by simp only [List.getElem?_cons_succ]; exact h1)
          (by simp only [List.getElem?_cons_succ]; exact h2)) (Nat.succ.inj hl) hR'' h1 hfs
        (by rw [den_lift01]; exact hih)
      have e : den M σ (vcons x ρ) (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) = fapp (den M σ ρ acc) x := by
        show fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc)) x = _
        rw [den_lift01]
      rw [den_lift01, e] at ih
      exact ih
  | .recursive inner :: ss, A :: Fs, Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hR, hF, ⟨hx, hfs⟩, ⟨hgx, hih⟩ => by
      rcases hsh 0 (.recursive inner) A List.getElem?_cons_zero List.getElem?_cons_zero with h0 | ⟨h0, hA⟩
      · exact absurd h0 (by intro h; cases h)
      · cases h0
        have hR1 : (match funIHType E fuel np A Mx 0 with
            | none => none
            | some ih => (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
                (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
                (Rcic.Declarative.lift 0 1 (policyPi Fs Tend))).map fun rest => Expr.pi A (.pi ih rest)) = some R := hR
        cases hih' : funIHType E fuel np A Mx 0 with
        | none => rw [hih'] at hR1; cases hR1
        | some ihT =>
            rw [hih'] at hR1
            obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR1
            have hihT := funIHType_recHead hop hA hih'
            have h1 := app_mem M (fun y y' hy => den_congr M σ (.pi ihT R') (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
            have hg : g x ∈ Ed M (den M σ (vcons x ρ) ihT) := by
              rw [hihT, den_foldApps, List.map_append, den_lift01, List.map_map]
              have e : (den M σ (vcons x ρ) ∘ Rcic.Declarative.lift 0 1) = den M σ ρ :=
                funext fun e => den_lift01 M σ x ρ e
              rw [e]
              exact hgx rfl
            have h2 := app_mem M (fun y y' hy => den_congr M σ R' (vcons_congr (ρ := vcons x ρ) (ρ' := vcons x ρ) hy (fun _ => Equiv.rfl))) h1 hg
            rw [lift_policyPi, Nat.zero_add] at hR''
            have hxl : xs.length = Fs.length := hfs.length
            have hfs' : TelFits M σ (liftFields 1 Fs 0) (vcons (g x) (vcons x ρ)) xs :=
              (TelFits_liftFields M σ [g x] (vcons x ρ) Fs [] xs).mpr hfs
            have hih2 : IHOk M σ np (den M σ (vcons (g x) (vcons x ρ)) (Rcic.Declarative.lift 0 2 Mx)) g ss
                (liftFields 1 Fs 0) (vcons (g x) (vcons x ρ)) xs := by
              rw [den_lift02]
              exact (IHOk_liftFields M σ np _ g [g x] (vcons x ρ) ss Fs [] xs).mpr hih
            have ih := minor_sem M σ E fuel np hop g ss (liftFields 1 Fs 0)
              (Rcic.Declarative.lift Fs.length 1 Tend) _ _ R' (vcons (g x) (vcons x ρ)) _ xs
              (fun k s A' h1 h2 => by
                rw [liftFields_getElem?] at h2
                cases hk : Fs[k]? with
                | none => rw [hk] at h2; cases h2
                | some B =>
                    rw [hk] at h2
                    cases h2
                    rcases hsh (k + 1) s B (by simp only [List.getElem?_cons_succ]; exact h1)
                      (by simp only [List.getElem?_cons_succ]; exact hk) with h | ⟨h, hB⟩
                    · exact Or.inl h
                    · exact Or.inr ⟨h, hB.lift _ _⟩)
              (by rw [liftFields_length']; exact Nat.succ.inj hl) hR'' h2 hfs' hih2
            rw [den_lift02, familyIdx_lift, List.map_map, ← hxl] at ih
            have e : (den M σ (push xs (vcons (g x) (vcons x ρ))) ∘ Rcic.Declarative.lift xs.length 1) =
                den M σ (push xs (vcons x ρ)) := funext fun e => den_lift_push M σ xs [g x] (vcons x ρ) e
            have e2 : den M σ (vcons (g x) (vcons x ρ)) (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) =
                fapp (den M σ ρ acc) x := by
              show fapp (den M σ (vcons (g x) (vcons x ρ)) (Rcic.Declarative.lift 0 2 acc)) x = _
              rw [den_lift02]
            rw [e, e2] at ih
            exact ih

end PSet

end Rcic.F3
