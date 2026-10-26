import rcic.RcicF3KTWFixture

/-!
# F3 class A KT-4a: minor semantics for one-binder function-recursive fields

`shArgsA`/`IHOkA` extend routec's `shArgs`/`IHOk` with a λ-IH for
`.recursive 1` fields; `funIHType_fnRecHead` computes the one-binder IH
type for a family-headed codomain under an opaque family head.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- A function-recursive field headed by the family: `Π (y : D'), F args`. -/
def FnRecHead (f : Nat) (A : Expr Nat) : Prop := ∃ D' B, A = .pi D' B ∧ RecHead f B

/-- Minor arguments with the λ-IH for one-binder recursive fields. -/
def shArgsA (M : Interp.{4}) (σ : Nat → Nat) (g : PSet.{4} → PSet.{4}) :
    List FieldShape → List (Expr Nat) → (Nat → PSet.{4}) → List PSet.{4} → List PSet.{4}
  | .recursive 0 :: ss, _ :: Fs, ρ, x :: xs => x :: g x :: shArgsA M σ g ss Fs (vcons x ρ) xs
  | .recursive 1 :: ss, A :: Fs, ρ, x :: xs =>
      x :: lamVal M (den M σ ρ (piDom A)) (fun y => g (fapp x y)) :: shArgsA M σ g ss Fs (vcons x ρ) xs
  | .nonrecursive :: ss, _ :: Fs, ρ, x :: xs => x :: shArgsA M σ g ss Fs (vcons x ρ) xs
  | _, _, _, _ => []

/-- `g` at each recursive field lies in the motive at the field's indices and the field;
for a one-binder recursive field, pointwise at every domain element. -/
def IHOkA (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4}) :
    List FieldShape → List (Expr Nat) → (Nat → PSet.{4}) → List PSet.{4} → Prop
  | s :: ss, A :: Fs, ρ, x :: xs =>
      (s = .recursive 0 → g x ∈ Ed M (fapps mo ((familyIdx np A).map (den M σ ρ) ++ [x]))) ∧
      (s = .recursive 1 → ∀ y, y ∈ Ed M (den M σ ρ (piDom A)) →
          g (fapp x y) ∈ Ed M (fapps mo ((familyIdx np (piCod A)).map (den M σ (vcons y ρ)) ++ [fapp x y]))) ∧
      IHOkA M σ np mo g ss Fs (vcons x ρ) xs
  | _, _, _, _ => True

theorem piDom_lift (c s : Nat) : (A : Expr Nat) →
    piDom (Rcic.Declarative.lift c s A) = Rcic.Declarative.lift c s (piDom A)
  | .bvar i => by
      show piDom (if c ≤ i then Expr.bvar (i + s) else Expr.bvar i) =
        if c ≤ i then Expr.bvar (i + s) else Expr.bvar i
      split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- For a `pi`, `piCod` of the lift lifts the codomain with the binder's extra `+1` cutoff.
(For non-`pi` `A`, `piCod A = A` and the lifted codomain keeps cutoff `c`.) -/
theorem piCod_lift (c s : Nat) (A : Expr Nat) (h : ∃ D B, A = .pi D B) :
    piCod (Rcic.Declarative.lift c s A) = Rcic.Declarative.lift (c + 1) s (piCod A) := by
  obtain ⟨D, B, rfl⟩ := h
  rfl

theorem shArgsA_liftFields (M : Interp.{4}) (σ : Nat → Nat) (g : PSet.{4} → PSet.{4})
    (ys : List PSet.{4}) (R : Nat → PSet.{4}) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → (zs xs : List PSet.{4}) →
    shArgsA M σ g ss (liftFields ys.length Fs zs.length) (push zs (push ys R)) xs =
      shArgsA M σ g ss Fs (push zs R) xs
  | [], _, _, _ => rfl
  | s :: ss, [], zs, xs => by
      cases s with
      | nonrecursive => rfl
      | recursive n =>
          cases n with
          | zero => rfl
          | succ m => cases m with | zero => rfl | succ _ => rfl
  | s :: ss, A :: Fs, zs, [] => by
      cases s with
      | nonrecursive => rfl
      | recursive n =>
          cases n with
          | zero => rfl
          | succ m => cases m with | zero => rfl | succ _ => rfl
  | s :: ss, A :: Fs, zs, x :: xs => by
      have h1 : vcons x (push zs (push ys R)) = push (zs ++ [x]) (push ys R) := by
        rw [push_append]; rfl
      have h2 : vcons x (push zs R) = push (zs ++ [x]) R := by rw [push_append]; rfl
      have hl : zs.length + 1 = (zs ++ [x]).length := by simp
      cases s with
      | nonrecursive =>
          show x :: shArgsA M σ g ss (liftFields ys.length Fs (zs.length + 1))
              (vcons x (push zs (push ys R))) xs =
            x :: shArgsA M σ g ss Fs (vcons x (push zs R)) xs
          rw [h1, h2, hl, shArgsA_liftFields M σ g ys R ss Fs (zs ++ [x]) xs]
      | recursive n =>
          cases n with
          | zero =>
              show x :: g x :: shArgsA M σ g ss (liftFields ys.length Fs (zs.length + 1))
                  (vcons x (push zs (push ys R))) xs =
                x :: g x :: shArgsA M σ g ss Fs (vcons x (push zs R)) xs
              rw [h1, h2, hl, shArgsA_liftFields M σ g ys R ss Fs (zs ++ [x]) xs]
          | succ m =>
              cases m with
              | zero =>
                  show x :: lamVal M (den M σ (push zs (push ys R))
                      (piDom (Rcic.Declarative.lift zs.length ys.length A)))
                      (fun y => g (fapp x y)) ::
                      shArgsA M σ g ss (liftFields ys.length Fs (zs.length + 1))
                      (vcons x (push zs (push ys R))) xs =
                    x :: lamVal M (den M σ (push zs R) (piDom A)) (fun y => g (fapp x y)) ::
                      shArgsA M σ g ss Fs (vcons x (push zs R)) xs
                  rw [piDom_lift, den_lift_push, h1, h2, hl,
                    shArgsA_liftFields M σ g ys R ss Fs (zs ++ [x]) xs]
              | succ m' => rfl

theorem IHOkA_liftFields (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4})
    (g : PSet.{4} → PSet.{4}) (ys : List PSet.{4}) (R : Nat → PSet.{4}) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → (zs xs : List PSet.{4}) →
    (∀ (k : Nat) (A : Expr Nat), ss[k]? = some (.recursive 1) → Fs[k]? = some A →
      ∃ D B : Expr Nat, A = .pi D B) →
    (IHOkA M σ np mo g ss (liftFields ys.length Fs zs.length) (push zs (push ys R)) xs ↔
      IHOkA M σ np mo g ss Fs (push zs R) xs)
  | [], _, _, _, _ => Iff.rfl
  | s :: ss, [], zs, xs, _ => by
      cases s with
      | nonrecursive => exact Iff.rfl
      | recursive n =>
          cases n with
          | zero => exact Iff.rfl
          | succ m => cases m with | zero => exact Iff.rfl | succ _ => exact Iff.rfl
  | s :: ss, A :: Fs, zs, [], _ => by
      cases s with
      | nonrecursive => exact Iff.rfl
      | recursive n =>
          cases n with
          | zero => exact Iff.rfl
          | succ m => cases m with | zero => exact Iff.rfl | succ _ => exact Iff.rfl
  | s :: ss, A :: Fs, zs, x :: xs, hpi => by
      show ((s = .recursive 0 → g x ∈ Ed M (fapps mo
            ((familyIdx np (Rcic.Declarative.lift zs.length ys.length A)).map
              (den M σ (push zs (push ys R))) ++ [x]))) ∧
          (s = .recursive 1 → ∀ y, y ∈ Ed M (den M σ (push zs (push ys R))
            (piDom (Rcic.Declarative.lift zs.length ys.length A))) →
            g (fapp x y) ∈ Ed M (fapps mo
              ((familyIdx np (piCod (Rcic.Declarative.lift zs.length ys.length A))).map
                (den M σ (vcons y (push zs (push ys R)))) ++ [fapp x y]))) ∧
          IHOkA M σ np mo g ss (liftFields ys.length Fs (zs.length + 1))
            (vcons x (push zs (push ys R))) xs) ↔
        ((s = .recursive 0 → g x ∈ Ed M (fapps mo
            ((familyIdx np A).map (den M σ (push zs R)) ++ [x]))) ∧
          (s = .recursive 1 → ∀ y, y ∈ Ed M (den M σ (push zs R) (piDom A)) →
            g (fapp x y) ∈ Ed M (fapps mo
              ((familyIdx np (piCod A)).map (den M σ (vcons y (push zs R))) ++ [fapp x y]))) ∧
          IHOkA M σ np mo g ss Fs (vcons x (push zs R)) xs)
      have e1 : (familyIdx np (Rcic.Declarative.lift zs.length ys.length A)).map
          (den M σ (push zs (push ys R))) =
          (familyIdx np A).map (den M σ (push zs R)) := by
        rw [familyIdx_lift, List.map_map]
        exact List.map_congr_left fun e _ => den_lift_push M σ zs ys R e
      have edom : den M σ (push zs (push ys R))
          (piDom (Rcic.Declarative.lift zs.length ys.length A)) =
          den M σ (push zs R) (piDom A) := by
        rw [piDom_lift]
        exact den_lift_push M σ zs ys R (piDom A)
      have h1 : vcons x (push zs (push ys R)) = push (zs ++ [x]) (push ys R) := by
        rw [push_append]; rfl
      have h2 : vcons x (push zs R) = push (zs ++ [x]) R := by rw [push_append]; rfl
      have hl : zs.length + 1 = (zs ++ [x]).length := by simp
      rw [e1, edom, h1, h2, hl,
        IHOkA_liftFields M σ np mo g ys R ss Fs (zs ++ [x]) xs
          (fun k A' h1 h2 => hpi (k + 1) A'
            (by rwa [List.getElem?_cons_succ]) (by rwa [List.getElem?_cons_succ]))]
      refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
      have ec : ∀ (D B : Expr Nat) (y : PSet.{4}),
          (familyIdx np (piCod (Rcic.Declarative.lift zs.length ys.length (.pi D B)))).map
            (den M σ (vcons y (push zs (push ys R)))) =
          (familyIdx np (piCod (.pi D B))).map (den M σ (vcons y (push zs R))) := by
        intro D B y
        have hA : Rcic.Declarative.lift zs.length ys.length (.pi D B) =
            .pi (Rcic.Declarative.lift zs.length ys.length D)
              (Rcic.Declarative.lift (zs.length + 1) ys.length B) := rfl
        rw [hA]
        show (familyIdx np (Rcic.Declarative.lift (zs.length + 1) ys.length B)).map
            (den M σ (vcons y (push zs (push ys R)))) =
          (familyIdx np B).map (den M σ (vcons y (push zs R)))
        have h1y : vcons y (push zs (push ys R)) = push (zs ++ [y]) (push ys R) := by
          rw [push_append]; rfl
        have h2y : vcons y (push zs R) = push (zs ++ [y]) R := by rw [push_append]; rfl
        have hly : zs.length + 1 = (zs ++ [y]).length := by simp
        rw [h1y, h2y, familyIdx_lift, List.map_map, hly]
        exact List.map_congr_left fun e _ => den_lift_push M σ (zs ++ [y]) ys R e
      constructor
      · intro hh hs
        obtain ⟨D, B, rfl⟩ := hpi 0 A (hs ▸ List.getElem?_cons_zero) List.getElem?_cons_zero
        intro y hy
        rw [← ec D B y]
        exact hh hs y hy
      · intro hh hs
        obtain ⟨D, B, rfl⟩ := hpi 0 A (hs ▸ List.getElem?_cons_zero) List.getElem?_cons_zero
        intro y hy
        rw [ec D B y]
        exact hh hs y hy

/-- The induction hypothesis type of a one-binder function-recursive field headed by an
opaque family: `Π (y : lift 0 1 D'), motive idx (f y)`. -/
theorem funIHType_fnRecHead {E : ResolvedEnv} {fuel np : Nat} {f : Nat} (hop : ∀ ls, transparentBody E f ls = none)
    {D' B M ih : Expr Nat} (hB : RecHead f B) (h : funIHType E fuel np (.pi D' B) M 1 = some ih) :
    ∃ D'' B'', ih = .pi D'' B'' ∧ D'' = Rcic.Declarative.lift 0 1 D' ∧
      B'' = foldApps (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 M))
        ((familyIdx np (Rcic.Declarative.lift 1 1 B)) ++ [.app (.bvar 1) (.bvar 0)]) := by
  obtain ⟨ls, args, rfl⟩ := hB
  have hl : Rcic.Declarative.lift 1 1 (foldApps (.const f ls) args) =
      foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1)) := by rw [lift_foldApps]; rfl
  have hwpi : ∀ k : Nat, whnfFuel E (k + 1)
      (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) =
      some (.pi (Rcic.Declarative.lift 0 1 D')
        (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1)))) := by
    intro k
    have he : Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args)) =
        .pi (Rcic.Declarative.lift 0 1 D')
          (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) :=
      congrArg (fun e => Expr.pi (Rcic.Declarative.lift 0 1 D') e) hl
    rw [he]
    rfl
  unfold funIHType at h
  match fuel, h with
  | 0, h => simp [piTelescopeFuel] at h
  | 1, h => simp [piTelescopeFuel, whnfFuel] at h
  | k + 2, h =>
      cases k with
      | zero =>
          have hwpi1 : whnfFuel E 1
              (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) =
              some (.pi (Rcic.Declarative.lift 0 1 D')
                (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1)))) := hwpi 0
          have hn : piTelescopeFuel E 2
              (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) = none := by
            show (match whnfFuel E 1
                (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) with
              | none => none
              | some (.pi A B) => _
              | some w => some ([], w)) = none
            rw [hwpi1]
            rfl
          rw [hn] at h
          cases h
      | succ j =>
          have hnp : ∀ (A' B' : Expr Nat), foldApps (.const f ls)
              (args.map (Rcic.Declarative.lift 1 1)) ≠ .pi A' B' :=
            foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _
          have hw : whnfFuel E (j + 1)
              (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) =
              some (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) := by
            unfold whnfFuel
            rw [appsSpine_foldApps]
            simp only [appsSpine, List.nil_append, hop]
          have hpt2 : piTelescopeFuel E (j + 2)
              (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) =
              some ([], foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) := by
            show (match whnfFuel E (j + 1) _ with
              | none => none
              | some (.pi A B) => _
              | some w => some ([], w)) = _
            rw [hw]
            generalize hfa : foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1)) = fa
            rw [hfa] at hnp
            cases fa with
            | pi A' B' => exact absurd rfl (hnp A' B')
            | _ => rfl
          have hwpi2 : whnfFuel E (j + 2)
              (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) =
              some (.pi (Rcic.Declarative.lift 0 1 D')
                (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1)))) := hwpi (j + 1)
          have hpt : piTelescopeFuel E (j + 3)
              (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) =
              some ([Rcic.Declarative.lift 0 1 D'],
                foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) := by
            show (match whnfFuel E (j + 2)
                (Rcic.Declarative.lift 0 1 (.pi D' (foldApps (.const f ls) args))) with
              | none => none
              | some (.pi A B) => (match piTelescopeFuel E (j + 2) B with
                  | none => none
                  | some (ds, body) => some (A :: ds, body))
              | some w => some ([], w)) = _
            rw [hwpi2]
            show (match piTelescopeFuel E (j + 2)
                (foldApps (.const f ls) (args.map (Rcic.Declarative.lift 1 1))) with
              | none => none
              | some (ds, body) => some (Rcic.Declarative.lift 0 1 D' :: ds, body)) = _
            rw [hpt2]
          rw [hpt] at h
          simp only [List.length_cons, List.length_nil, Nat.reduceEqDiff, if_true, Option.some.injEq] at h
          rw [← h, hl]
          refine ⟨Rcic.Declarative.lift 0 1 D', _, rfl, rfl, rfl⟩

/-- The semantic minor with λ-IH arguments for one-binder function-recursive fields. -/
theorem minor_semA (M : Interp.{4}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat) {f : Nat}
    (hop : ∀ ls, transparentBody E f ls = none) (g : PSet.{4} → PSet.{4})
    (hg : ∀ x x', Equiv x x' → Equiv (g x) (g x')) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → (Tend Mx acc R : Expr Nat) →
    (ρ : Nat → PSet.{4}) → (F : PSet.{4}) → (xs : List PSet.{4}) →
    (∀ (k : Nat) (s : FieldShape) (A : Expr Nat), ss[k]? = some s → Fs[k]? = some A →
      s = .nonrecursive ∨ (s = .recursive 0 ∧ RecHead f A) ∨ (s = .recursive 1 ∧ FnRecHead f A)) →
    ss.length = Fs.length →
    minorFromTelescope E fuel np Mx acc ss (policyPi Fs Tend) = some R →
    F ∈ Ed M (den M σ ρ R) → TelFits M σ Fs ρ xs →
    IHOkA M σ np (den M σ ρ Mx) g ss Fs ρ xs →
    fapps F (shArgsA M σ g ss Fs ρ xs) ∈ Ed M (fapp (fapps (den M σ ρ Mx)
      ((familyIdx np Tend).map (den M σ (push xs ρ)))) (fapps (den M σ ρ acc) xs))
  | [], [], Tend, Mx, acc, R, ρ, F, [], _, _, hR, hF, _, _ => by
      simp only [policyPi, minorFromTelescope, Option.some.injEq] at hR
      subst hR
      have hF' : F ∈ Ed M (fapp (den M σ ρ (foldApps Mx (familyIdx np Tend))) (den M σ ρ acc)) := hF
      rw [den_foldApps] at hF'
      exact hF'
  | [], _ :: _, _, _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, _, _, _, _, _, _, [], _, _, _, _, hx, _ => hx.elim
  | .nonrecursive :: ss, A :: Fs, Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hR, hF,
      ⟨hx, hfs⟩, ⟨_, _, hih⟩ => by
      have hR' : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 1 Mx)
          (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss (policyPi Fs Tend)).map
          (fun rest => .pi A rest) = some R := hR
      obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR'
      have h1 := app_mem M (fun y y' hy => den_congr M σ R'
          (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
      have ih := minor_semA M σ E fuel np hop g hg ss Fs Tend _ _ R' (vcons x ρ) (fapp F x) xs
        (fun k s A' h1 h2 => hsh (k + 1) s A' (by simp only [List.getElem?_cons_succ]; exact h1)
          (by simp only [List.getElem?_cons_succ]; exact h2)) (Nat.succ.inj hl) hR'' h1 hfs
        (by rw [den_lift01]; exact hih)
      have e : den M σ (vcons x ρ) (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) =
          fapp (den M σ ρ acc) x := by
        show fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc)) x = _
        rw [den_lift01]
      rw [den_lift01, e] at ih
      exact ih
  | .recursive inner :: ss, A :: Fs, Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hR, hF,
      ⟨hx, hfs⟩, ⟨hdir, hfn, hih⟩ => by
      have hpitail : ∀ (k : Nat) (A' : Expr Nat), ss[k]? = some (.recursive 1) →
          Fs[k]? = some A' → ∃ D' B' : Expr Nat, A' = .pi D' B' := fun k A' h1 h2 => by
        rcases hsh (k + 1) (.recursive 1) A' (by rwa [List.getElem?_cons_succ])
            (by rwa [List.getElem?_cons_succ]) with h | ⟨h, -⟩ | ⟨-, hFn⟩
        · exact absurd h (by intro c; cases c)
        · cases h
        · obtain ⟨D, B, hA, -⟩ := hFn
          exact ⟨D, B, hA⟩
      cases inner with
      | zero =>
          rcases hsh 0 (.recursive 0) A List.getElem?_cons_zero List.getElem?_cons_zero
            with h0 | ⟨h0, hA⟩ | ⟨h0, -⟩
          · cases h0
          · cases h0
            have hR1 : (match funIHType E fuel np A Mx 0 with
                | none => none
                | some ih => (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
                    (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
                    (Rcic.Declarative.lift 0 1 (policyPi Fs Tend))).map fun rest =>
                      Expr.pi A (.pi ih rest)) = some R := hR
            cases hih' : funIHType E fuel np A Mx 0 with
            | none => rw [hih'] at hR1; cases hR1
            | some ihT =>
                rw [hih'] at hR1
                obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR1
                have hihT := funIHType_recHead hop hA hih'
                have h1 := app_mem M (fun y y' hy => den_congr M σ (.pi ihT R')
                    (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
                have hg' : g x ∈ Ed M (den M σ (vcons x ρ) ihT) := by
                  rw [hihT, den_foldApps, List.map_append, den_lift01, List.map_map]
                  have e : (den M σ (vcons x ρ) ∘ Rcic.Declarative.lift 0 1) = den M σ ρ :=
                    funext fun e => den_lift01 M σ x ρ e
                  rw [e]
                  exact hdir rfl
                have h2 := app_mem M (fun y y' hy => den_congr M σ R'
                    (vcons_congr (ρ := vcons x ρ) (ρ' := vcons x ρ) hy
                      (fun _ => Equiv.rfl))) h1 hg'
                rw [lift_policyPi, Nat.zero_add] at hR''
                have hxl : xs.length = Fs.length := hfs.length
                have hfs' : TelFits M σ (liftFields 1 Fs 0) (vcons (g x) (vcons x ρ)) xs :=
                  (TelFits_liftFields M σ [g x] (vcons x ρ) Fs [] xs).mpr hfs
                have hih2 : IHOkA M σ np (den M σ (vcons (g x) (vcons x ρ))
                    (Rcic.Declarative.lift 0 2 Mx)) g ss (liftFields 1 Fs 0)
                    (vcons (g x) (vcons x ρ)) xs := by
                  rw [den_lift02]
                  exact (IHOkA_liftFields M σ np _ g [g x] (vcons x ρ) ss Fs [] xs
                    hpitail).mpr hih
                have ih := minor_semA M σ E fuel np hop g hg ss (liftFields 1 Fs 0)
                  (Rcic.Declarative.lift Fs.length 1 Tend) _ _ R' (vcons (g x) (vcons x ρ))
                  _ xs
                  (fun k s A' h1 h2 => by
                    rw [liftFields_getElem?] at h2
                    cases hk : Fs[k]? with
                    | none => rw [hk] at h2; cases h2
                    | some B' =>
                        rw [hk] at h2
                        cases h2
                        rcases hsh (k + 1) s B'
                          (by simp only [List.getElem?_cons_succ]; exact h1)
                          (by simp only [List.getElem?_cons_succ]; exact hk)
                          with h | ⟨h, hB⟩ | ⟨h, hFn⟩
                        · exact Or.inl h
                        · exact Or.inr (Or.inl ⟨h, hB.lift _ _⟩)
                        · obtain ⟨D₁, B₁, hA', hrec⟩ := hFn
                          exact Or.inr (Or.inr ⟨h, _, _, by rw [hA']; rfl, hrec.lift _ _⟩))
                  (by rw [liftFields_length']; exact Nat.succ.inj hl) hR'' h2 hfs' hih2
                rw [den_lift02, familyIdx_lift, List.map_map, ← hxl] at ih
                have e : (den M σ (push xs (vcons (g x) (vcons x ρ))) ∘
                    Rcic.Declarative.lift xs.length 1) =
                    den M σ (push xs (vcons x ρ)) := funext fun e =>
                  den_lift_push M σ xs [g x] (vcons x ρ) e
                have e2 : den M σ (vcons (g x) (vcons x ρ))
                    (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) =
                    fapp (den M σ ρ acc) x := by
                  show fapp (den M σ (vcons (g x) (vcons x ρ))
                    (Rcic.Declarative.lift 0 2 acc)) x = _
                  rw [den_lift02]
                rw [e, e2] at ih
                rw [show shArgsA M σ g ss (liftFields 1 Fs 0) (vcons (g x) (vcons x ρ)) xs =
                    shArgsA M σ g ss Fs (vcons x ρ) xs from
                  shArgsA_liftFields M σ g [g x] (vcons x ρ) ss Fs [] xs] at ih
                exact ih
          · cases h0
      | succ m =>
          cases m with
          | zero =>
              rcases hsh 0 (.recursive 1) A List.getElem?_cons_zero List.getElem?_cons_zero
                with h0 | ⟨h0, -⟩ | ⟨h0, hA⟩
              · cases h0
              · cases h0
              · obtain ⟨D', B, rfl, hB⟩ := hA
                have hR1 : (match funIHType E fuel np (.pi D' B) Mx 1 with
                    | none => none
                    | some ih => (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
                        (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
                        (Rcic.Declarative.lift 0 1 (policyPi Fs Tend))).map fun rest =>
                          Expr.pi (.pi D' B) (.pi ih rest)) = some R := hR
                cases hih' : funIHType E fuel np (.pi D' B) Mx 1 with
                | none => rw [hih'] at hR1; cases hR1
                | some ihT =>
                    rw [hih'] at hR1
                    obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR1
                    obtain ⟨D'', B'', hT, hD, hB''⟩ := funIHType_fnRecHead hop hB hih'
                    have hT' : ihT = .pi (Rcic.Declarative.lift 0 1 D')
                        (foldApps (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 Mx))
                          (familyIdx np (Rcic.Declarative.lift 1 1 B) ++
                            [.app (.bvar 1) (.bvar 0)])) := hT.trans (by rw [hD, hB''])
                    have h1 := app_mem M (fun y y' hy => den_congr M σ (.pi ihT R')
                        (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
                    have ebody : ∀ y : PSet.{4},
                        den M σ (vcons y (vcons x ρ))
                          (foldApps (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 Mx))
                            (familyIdx np (Rcic.Declarative.lift 1 1 B) ++
                              [.app (.bvar 1) (.bvar 0)])) =
                        fapps (den M σ ρ Mx)
                          ((familyIdx np B).map (den M σ (vcons y ρ)) ++ [fapp x y]) := by
                      intro y
                      rw [den_foldApps, List.map_append, den_lift01, den_lift01,
                        familyIdx_lift, List.map_map]
                      have e1 : (den M σ (vcons y (vcons x ρ)) ∘
                          Rcic.Declarative.lift 1 1) = den M σ (vcons y ρ) := funext fun e =>
                        den_lift_push M σ [y] [x] ρ e
                      rw [e1]
                      rfl
                    have hv : lamVal M (den M σ ρ D') (fun y => g (fapp x y)) ∈
                        Ed M (den M σ (vcons x ρ) ihT) := by
                      rw [hT']
                      rw [show den M σ (vcons x ρ)
                          (.pi (Rcic.Declarative.lift 0 1 D')
                            (foldApps (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 Mx))
                              (familyIdx np (Rcic.Declarative.lift 1 1 B) ++
                                [.app (.bvar 1) (.bvar 0)]))) =
                          piVal M (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 D'))
                            (fun y => den M σ (vcons y (vcons x ρ))
                              (foldApps (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 Mx))
                                (familyIdx np (Rcic.Declarative.lift 1 1 B) ++
                                  [.app (.bvar 1) (.bvar 0)]))) from rfl]
                      rw [den_lift01]
                      refine lam_mem M ?_ ?_ ?_
                      · exact fun y y' hy => hg _ _ (fapp_congr Equiv.rfl hy)
                      · exact fun y y' hy => den_congr M σ _ (vcons_congr
                          (ρ := vcons x ρ) (ρ' := vcons x ρ) hy (fun _ => Equiv.rfl))
                      · intro y hy
                        rw [ebody y]
                        exact hfn rfl y hy
                    have h2 := app_mem M (fun y y' hy => den_congr M σ R'
                        (vcons_congr (ρ := vcons x ρ) (ρ' := vcons x ρ) hy
                          (fun _ => Equiv.rfl))) h1 hv
                    rw [lift_policyPi, Nat.zero_add] at hR''
                    have hxl : xs.length = Fs.length := hfs.length
                    have hfs' : TelFits M σ (liftFields 1 Fs 0) (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ)) xs :=
                      (TelFits_liftFields M σ [lamVal M (den M σ ρ D') (fun y => g (fapp x y))] (vcons x ρ) Fs [] xs).mpr hfs
                    have hih2 : IHOkA M σ np (den M σ (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ))
                        (Rcic.Declarative.lift 0 2 Mx)) g ss (liftFields 1 Fs 0)
                        (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ)) xs := by
                      rw [den_lift02]
                      exact (IHOkA_liftFields M σ np _ g [lamVal M (den M σ ρ D') (fun y => g (fapp x y))] (vcons x ρ) ss Fs [] xs
                        hpitail).mpr hih
                    have ih := minor_semA M σ E fuel np hop g hg ss (liftFields 1 Fs 0)
                      (Rcic.Declarative.lift Fs.length 1 Tend) _ _ R' (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ))
                      _ xs
                      (fun k s A' h1 h2 => by
                        rw [liftFields_getElem?] at h2
                        cases hk : Fs[k]? with
                        | none => rw [hk] at h2; cases h2
                        | some B' =>
                            rw [hk] at h2
                            cases h2
                            rcases hsh (k + 1) s B'
                              (by simp only [List.getElem?_cons_succ]; exact h1)
                              (by simp only [List.getElem?_cons_succ]; exact hk)
                              with h | ⟨h, hB⟩ | ⟨h, hFn⟩
                            · exact Or.inl h
                            · exact Or.inr (Or.inl ⟨h, hB.lift _ _⟩)
                            · obtain ⟨D₁, B₁, hA', hrec⟩ := hFn
                              exact Or.inr (Or.inr ⟨h, _, _, by rw [hA']; rfl, hrec.lift _ _⟩))
                      (by rw [liftFields_length']; exact Nat.succ.inj hl) hR'' h2 hfs' hih2
                    rw [den_lift02, familyIdx_lift, List.map_map, ← hxl] at ih
                    have e : (den M σ (push xs (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ))) ∘
                        Rcic.Declarative.lift xs.length 1) =
                        den M σ (push xs (vcons x ρ)) := funext fun e =>
                      den_lift_push M σ xs [lamVal M (den M σ ρ D') (fun y => g (fapp x y))] (vcons x ρ) e
                    have e2 : den M σ (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ))
                        (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) =
                        fapp (den M σ ρ acc) x := by
                      show fapp (den M σ (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ))
                        (Rcic.Declarative.lift 0 2 acc)) x = _
                      rw [den_lift02]
                    rw [e, e2] at ih
                    rw [show shArgsA M σ g ss (liftFields 1 Fs 0) (vcons (lamVal M (den M σ ρ D') (fun y => g (fapp x y))) (vcons x ρ)) xs =
                        shArgsA M σ g ss Fs (vcons x ρ) xs from
                      shArgsA_liftFields M σ g [lamVal M (den M σ ρ D') (fun y => g (fapp x y))] (vcons x ρ) ss Fs [] xs] at ih
                    exact ih
          | succ m' =>
              rcases hsh 0 (.recursive (Nat.succ (Nat.succ m'))) A
                List.getElem?_cons_zero List.getElem?_cons_zero
                with h0 | ⟨h0, -⟩ | ⟨h0, -⟩
              · cases h0
              · cases h0
              · cases h0

/-- Admission-style shapes read off the field kinds. -/
def shapeOfKind : PKind → FieldShape
  | .plain => .nonrecursive
  | .direct => .recursive 0
  | .fn => .recursive 1

/-- The shape list a `FieldsClassA` constructor induces. -/
def shapesOf (f : Nat) (Fs : List (Expr Nat)) : List FieldShape :=
  (kindsOf f Fs).map shapeOfKind

/-- `ihOkF_of_InPhi` for class-A fields: `InPhi` over a candidate set `Z` whose
predicate is the motive condition gives `IHOkA` — the Π-recursive clause is
the `fn` arm: for `y` in the field's denoted domain, `fapp x y` is a `Z`-member
whose result tuple is the codomain's recursor tuple. -/
theorem ihOkA_of_InPhi (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (ps : List PSet.{4}) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4}) (Z : PSet.{4})
    (hZ : ∀ x, x ∈ Z → ∀ idxv : List PSet.{4},
      idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x) (ordPair pempty (tup idxv)) →
      g x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])))
    (hps : ps.length = (famDataOf a).params.length)
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClassA (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
        (famDataOf a).indices.length rest done.length →
      Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
        (kindsOf (famDataOf a).fref rest) xs done.length pre →
      IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
        (shapesOf (famDataOf a).fref rest) rest (push pre (push ps ρ0)) xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls hIn
      cases xs with
      | nil => trivial
      | cons x xs' =>
          exact Nat.noConfusion (Sem.InPhi.length _ _ _ _ _ hIn)
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls hIn
      obtain ⟨hdisj, hcls'⟩ := hcls
      have hf : fieldAt Fs done.length = A := by
        rw [hFs]
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      cases xs with
      | nil =>
          exact Nat.noConfusion (Sem.InPhi.length _ _ _ _ _ hIn)
      | cons x xs' =>
          rcases hdisj with h0 | hdir | hFn
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_free h0] at hIn
            obtain ⟨hx, hin⟩ := hIn
            rw [show shapesOf (famDataOf a).fref (A :: rest') =
                shapeOfKind (kindOf (famDataOf a).fref A) ::
                  shapesOf (famDataOf a).fref rest' from rfl]
            rw [kindOf_free h0]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
              (.nonrecursive :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun ho => ?_, fun ho => ?_, ?_⟩
            · cases ho
            · cases ho
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_directRec hdir] at hIn
            obtain ⟨⟨hxm, hxe⟩, hin⟩ := hIn
            rw [show shapesOf (famDataOf a).fref (A :: rest') =
                shapeOfKind (kindOf (famDataOf a).fref A) ::
                  shapesOf (famDataOf a).fref rest' from rfl]
            rw [kindOf_directRec hdir]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
              (.recursive 0 :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun _ => ?_, fun ho => ?_, ?_⟩
            · obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
              have hrecD : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).recTup
                  done.length pre pempty =
                  recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A := by
                show recTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs
                    done.length pre pempty = _
                unfold recTupF
                rw [hf, kindOf_directRec ⟨idx, hAe, hlen, hfree⟩]
              rw [hrecD] at hxe
              have haf : argsFitF P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A := by
                cases hdec : P.dec (argsFitF P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0)) A) with
                | isTrue h => exact h
                | isFalse hn =>
                    exfalso
                    have hs : recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A =
                        singleton pempty := by unfold recTupAt; rw [cond_neg hn]
                    exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs) (push ps ρ0) x
                      (hxe.trans (by rw [← hs]; exact Equiv.rfl))
              have hre : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x)
                  (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                    (push pre (push ps ρ0)))))) := by
                have hre2 : recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A =
                    ordPair pempty (tup ((familyIdx (famDataOf a).params.length A).map
                      (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))) := by
                  unfold recTupAt; rw [cond_pos haf]
                rw [hAe, familyIdx_directRec] at hre2
                have hse : Equiv (recTupAt P μ (famDataOf a) (σOf vs)
                    (push pre (push ps ρ0)) A)
                    (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                      (push pre (push ps ρ0)))))) := by
                  rw [← hre2, hAe]
                  exact Equiv.rfl
                exact hxe.trans hse
              have hTf : TelFits (mkM P μ) (σOf vs)
                  ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                  ((policyParameterLocals (famDataOf a).params.length done.length ++ idx).map
                    (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)))) := by
                rw [hAe] at haf
                exact (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0)) (famDataOf a).fref
                  (canonL a.family.member.arity) _).mp haf
              have hpsl' : ps.length = (famDataOf a).params.length := hps
              have e := den_recArgs (mkM P μ) (σOf vs) ps pre idx
              rw [hpre] at e
              rw [← hpsl'] at hTf
              rw [e] at hTf
              obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
              obtain ⟨rfl, rfl⟩ := List.append_inj heq
                (by rw [TelFits.length h1]; exact hpsl')
              rw [hAe, familyIdx_directRec]
              exact hZ x hxm (idx.map (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))
                (by rw [List.length_map]; exact hlen) h2 hre
            · cases ho
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
          · simp only [kindsOf, List.map] at hIn
            obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            rw [kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩] at hIn
            obtain ⟨hxp, hin⟩ := hIn
            rw [show shapesOf (famDataOf a).fref (A :: rest') =
                shapeOfKind (kindOf (famDataOf a).fref A) ::
                  shapesOf (famDataOf a).fref rest' from rfl]
            rw [kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
              (.recursive 1 :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun ho => ?_, fun _ y hy => ?_, ?_⟩
            · cases ho
            · rw [hA] at hy ⊢
              have hyD : y ∈ domEF P μ (σOf vs) (push ps ρ0) Fs done.length pre := by
                unfold domEF
                rw [hf, hA]
                exact hy
              cases hdec : P.dec (domEF P μ (σOf vs) (push ps ρ0) Fs done.length pre ∈
                  W4 (evalTotal (σOf vs) (famDataOf a).resLevel)) with
              | isTrue hdW =>
                  have hdom : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).domBig
                      done.length pre =
                      domEF P μ (σOf vs) (push ps ρ0) Fs done.length pre := by
                    show domBigF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs done.length pre = _
                    unfold domBigF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩, cond_pos hdW]
                  have hxp' : x ∈ piSet (domEF P μ (σOf vs) (push ps ρ0) Fs done.length pre)
                      ((semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).fib Z
                        done.length pre) :=
                    mem_congr_right (piSet_congr (by rw [hdom]; exact Equiv.rfl)
                      (fun a a' h => Sem.fib_resp _ _ _ _ h)) hxp
                  have hfy : fapp x y ∈ (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).fib
                      Z done.length pre y :=
                    fapp_mem_piSet (fun a a' h => Sem.fib_resp _ _ _ _ h) hxp' hyD
                  obtain ⟨hzm, hreT, hfx⟩ := mem_sep.mp hfy
                  have hfm : fapp x y ∈ Z := ⟨hzm, hfx⟩
                  have hrecT : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).recTup
                      done.length pre y =
                      recTupAt P μ (famDataOf a) (σOf vs) (vcons y (push pre (push ps ρ0)))
                        (piCod A) := by
                    show recTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs
                        done.length pre y = _
                    unfold recTupF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩, cond_pos hdW]
                  rw [hrecT] at hreT
                  rw [hA] at hreT
                  have haf : argsFitF P μ (famDataOf a) (σOf vs)
                      (vcons y (push pre (push ps ρ0)))
                      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                        (policyParameterLocals (famDataOf a).params.length
                          (done.length + 1) ++ idx)) := by
                    cases hdc : P.dec (argsFitF P μ (famDataOf a) (σOf vs)
                      (vcons y (push pre (push ps ρ0)))
                      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                        (policyParameterLocals (famDataOf a).params.length
                          (done.length + 1) ++ idx))) with
                    | isTrue h => exact h
                    | isFalse hn =>
                        exfalso
                        have hs : recTupAt P μ (famDataOf a) (σOf vs)
                            (vcons y (push pre (push ps ρ0)))
                            (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                              (policyParameterLocals (famDataOf a).params.length
                                (done.length + 1) ++ idx)) = singleton pempty := by
                          unfold recTupAt; rw [cond_neg hn]
                        exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs) (push ps ρ0)
                          (fapp x y) (((resTupF_congr P μ (famDataOf a) (σOf vs)
                            (push ps ρ0) hfx.symm).trans hreT).trans
                            (by rw [← hs]; exact Equiv.rfl))
                  have hre2 : recTupAt P μ (famDataOf a) (σOf vs)
                      (vcons y (push pre (push ps ρ0)))
                      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                        (policyParameterLocals (famDataOf a).params.length
                          (done.length + 1) ++ idx)) =
                      ordPair pempty (tup ((familyIdx (famDataOf a).params.length
                        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                          (policyParameterLocals (famDataOf a).params.length
                            (done.length + 1) ++ idx))).map
                        (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0)))))) := by
                    unfold recTupAt; rw [cond_pos haf]
                  have hre'' : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0)
                      (fapp x y)) (ordPair pempty (tup ((familyIdx (famDataOf a).params.length
                        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                          (policyParameterLocals (famDataOf a).params.length
                            (done.length + 1) ++ idx))).map
                        (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0))))))) := by
                    rw [← hre2]
                    exact (resTupF_congr P μ (famDataOf a) (σOf vs) (push ps ρ0)
                      hfx.symm).trans hreT
                  have hTf : TelFits (mkM P μ) (σOf vs)
                      ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                      ((policyParameterLocals (famDataOf a).params.length (done.length + 1)
                        ++ idx).map
                        (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0))))) :=
                    (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                      (vcons y (push pre (push ps ρ0))) (famDataOf a).fref
                      (canonL a.family.member.arity) _).mp haf
                  have hvey : vcons y (push pre (push ps ρ0)) =
                      push (pre ++ [y]) (push ps ρ0) := by rw [push_append]; rfl
                  have hpsl' : ps.length = (famDataOf a).params.length := hps
                  have hyl : (pre ++ [y]).length = done.length + 1 := by
                    rw [List.length_append, hpre]; rfl
                  have e := den_recArgs (mkM P μ) (σOf vs) ps (pre ++ [y]) idx
                  rw [hyl] at e
                  rw [← hpsl'] at hTf
                  rw [hvey] at hTf
                  rw [e] at hTf
                  obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
                  obtain ⟨rfl, rfl⟩ := List.append_inj heq
                    (by rw [TelFits.length h1]; exact hpsl')
                  rw [← hvey] at h2
                  rw [familyIdx_directRec] at hre''
                  show g (fapp x y) ∈ Ed (mkM P μ) (fapps mo
                    ((familyIdx (famDataOf a).params.length
                      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                        (policyParameterLocals (famDataOf a).params.length
                          (done.length + 1) ++ idx))).map
                      (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0))))
                      ++ [fapp x y]))
                  rw [familyIdx_directRec]
                  exact hZ (fapp x y) hfm _
                    (by rw [List.length_map]; exact hlen) h2 hre''
              | isFalse hdW =>
                  exfalso
                  have hdom : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).domBig
                      done.length pre = singleton pempty := by
                    show domBigF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs done.length pre = _
                    unfold domBigF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩, cond_neg hdW]
                  have hgd := isFuncOnDep_of_mem_piSet
                    (fun a a' h => Sem.fib_resp _ _ _ _ h)
                    (mem_congr_right (piSet_congr (by rw [hdom]; exact Equiv.rfl)
                      (fun a a' h => Sem.fib_resp _ _ _ _ h)) hxp)
                  obtain ⟨b, hb, -⟩ := hgd.1 pempty (mem_singleton.mpr Equiv.rfl)
                  obtain ⟨bi, hreT, -⟩ := mem_sep.mp hb
                  have hrecT : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).recTup
                      done.length pre pempty = singleton pempty := by
                    show recTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs
                        done.length pre pempty = _
                    unfold recTupF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩, cond_neg hdW]
                  exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs) (push ps ρ0) _
                    (hrecT ▸ hreT)
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClassA (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest' (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          FieldsClassA (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
            (famDataOf a).indices.length rest' done'.length →
          Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
            (kindsOf (famDataOf a).fref rest') xs done'.length pre →
          IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
            (shapesOf (famDataOf a).fref rest') rest' (push pre (push ps ρ0)) xs)
        (hin : Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
          (kindsOf (famDataOf a).fref rest') xs' (done.length + 1) (pre ++ [x])) :
        IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo g
          (shapesOf (famDataOf a).fref rest') rest'
          (vcons x (push pre (push ps ρ0))) xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x]) (push ps ρ0) := by
        rw [push_append]; rfl
      rw [hvey]
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        (by rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton, hpre])
        (by rw [List.length_append]; exact hcls')
        (by rw [List.length_append]; exact hin)

/-- Class-A analogue of `RecGroup`: fields in `FieldsClassA`, minors derived with
the kind-read shapes. -/
structure RecGroupA {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Prop where
  bounded : FamBounded (famDataOf a) a.family.member.arity
  famFree : ∀ e, e ∈ a.family.parameters ++ a.family.indices →
    occursConst a.family.ref e = false
  fields : ∀ i : Fin a.constructors.length, FieldsClassA a.family.ref
    a.family.member.arity a.family.parameters.length a.family.indices.length
    (a.constructorViews i).fields 0
  riFree : ∀ (i : Fin a.constructors.length) (e : Expr Nat),
    e ∈ (a.constructorViews i).resultIndices → occursConst a.family.ref e = false
  opq : ∀ ls, transparentBody E a.family.ref ls = none
  shapes : ∀ i : Fin a.constructors.length, ∃ fuel,
    derivedMinor a i fuel (shapesOf a.family.ref (a.constructorViews i).fields) =
      a.minorTypes[i.val]?

/-- The `k`-th field's class disjunction from a `FieldsClassA`. -/
private theorem fieldsClassA_at {f ar np nq : Nat} :
    (Fs : List (Expr Nat)) → (d k : Nat) → FieldsClassA f ar np nq Fs d →
    ∀ A', Fs[k]? = some A' →
      occursConst f A' = false ∨ DirectRec f ar np nq (d + k) A' ∨
        FnRec f ar np nq (d + k) A'
  | [], _, _, _, _, h => by cases h
  | A :: Fs, d, 0, h, _, hA => by
      obtain ⟨hd, -⟩ := h
      rw [List.getElem?_cons_zero] at hA
      obtain rfl := Option.some.inj hA
      exact hd
  | A :: Fs, d, k + 1, h, A', hA => by
      obtain ⟨-, ht⟩ := h
      have := fieldsClassA_at Fs (d + 1) k ht A' (by rw [List.getElem?_cons_succ] at hA; exact hA)
      rwa [Nat.add_right_comm] at this

/-- Constructor-level minor for Π-recursive groups, with `shArgsA`. -/
theorem minor_ok_recA {M : Interp.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (G : RecGroupA a) (vs : List Nat)
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal M W4 (σOf vs) (famDataOf a)))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (M.μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam M (σOf vs) (ctorEnd M (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
          (a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length) (hisl : is.length = a.family.indices.length)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits M (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hisfit : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (j : Nat) (xs : List PSet.{4}) (hcf : CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs)
    (g : PSet.{4} → PSet.{4}) (hg : ∀ x x', Equiv x x' → Equiv (g x) (g x'))
    (hih : IHOkA M (σOf vs) a.family.parameters.length mo g
      (shapesOf a.family.ref (ctorFieldsOf (famDataOf a) j))
      (ctorFieldsOf (famDataOf a) j) (push ps ρ0) xs) :
    fapps (ms.getD j pempty) (shArgsA M (σOf vs) g
      (shapesOf a.family.ref (ctorFieldsOf (famDataOf a) j))
      (ctorFieldsOf (famDataOf a) j) (push ps ρ0) xs) ∈
      Ed M (fapps mo (is ++ [ctorV M (σOf vs) (famDataOf a) j xs])) := by
  obtain ⟨c, hc, hxs, hri⟩ := hcf
  have hjk : j < a.constructors.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    rwa [famDataOf_ctors_length] at this
  let i : Fin a.constructors.length := ⟨j, hjk⟩
  have hc' : c = ((a.constructorViews i).fields, (a.constructorViews i).resultIndices) := by
    have := famDataOf_ctor a i
    rw [hc] at this; exact Option.some.inj this
  subst hc'
  have hcfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews i).fields := ctorFieldsOf_famDataOf a i
  rw [hcfo] at hih ⊢
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hjm : j < ms.length := by rw [hmsl, a.minorCount]; exact hjk
  have hmj := TelFits_get a.minorTypes _ ms hms j (by rw [a.minorCount]; exact hjk)
  obtain ⟨fuel, hdm⟩ := G.shapes i
  have hmt : derivedMinor a i fuel (shapesOf a.family.ref (a.constructorViews i).fields) =
      some (a.minorTypes[j]'(by rw [a.minorCount]; exact hjk)) :=
    hdm.trans (List.getElem?_eq_getElem _)
  have hρpre : push (ms.take j) (vcons mo (push ps ρ0)) = push (mo :: ms.take j) (push ps ρ0) := rfl
  have htl : (mo :: ms.take j).length = 1 + j := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)]; omega
  rw [hρpre] at hmj
  have hxsl : xs.length = (a.constructorViews i).fields.length := hxs.length
  -- the derived minor, read semantically
  unfold derivedMinor at hmt
  dsimp only at hmt
  rw [show ctorFieldTelescope (a.constructorViews i) = policyPi (a.constructorViews i).fields
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)) from rfl, lift_policyPi, Nat.zero_add] at hmt
  have h1 : den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0)) (.bvar j) = mo := by
    show push (mo :: ms.take j) (push ps ρ0) j = mo
    have := push_cons_len_index mo (ms.take j) (push ps ρ0)
    rwa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)] at this
  have hfitL : TelFits M (σOf vs) (liftFields (1 + j) (a.constructorViews i).fields 0)
      (push (mo :: ms.take j) (push ps ρ0)) xs := by
    have := (TelFits_liftFields M (σOf vs) (mo :: ms.take j) (push ps ρ0) (a.constructorViews i).fields [] xs).mpr hxs
    rw [htl] at this; exact this
  -- the shape hypothesis for minor_semA
  have hsh : ∀ (k : Nat) (s : FieldShape) (A : Expr Nat), (shapesOf a.family.ref (a.constructorViews i).fields)[k]? = some s →
      (liftFields (1 + j) (a.constructorViews i).fields 0)[k]? = some A →
      s = .nonrecursive ∨ (s = .recursive 0 ∧ RecHead a.family.ref A) ∨
        (s = .recursive 1 ∧ FnRecHead a.family.ref A) := by
    intro k s A hs hA'
    simp only [shapesOf, kindsOf, List.getElem?_map] at hs
    rw [liftFields_getElem?] at hA'
    cases hAk : (a.constructorViews i).fields[k]? with
    | none =>
        rw [hAk] at hs
        cases hs
    | some A₀ =>
        rw [hAk] at hs hA'
        cases hA'
        cases hs
        obtain h0 | hdr | hfn := fieldsClassA_at (a.constructorViews i).fields 0 k (G.fields i) A₀ hAk
        · rw [kindOf_free h0]
          exact Or.inl rfl
        · obtain ⟨idx, hAe, hlen, hfree⟩ := hdr
          rw [kindOf_directRec ⟨idx, hAe, hlen, hfree⟩]
          refine Or.inr (Or.inl ⟨rfl, ?_⟩)
          exact RecHead.lift (⟨canonL a.family.member.arity,
            policyParameterLocals a.family.parameters.length (0 + k) ++ idx,
            hAe⟩ : RecHead a.family.ref A₀) (0 + k) (1 + j)
        · obtain ⟨D', idx, hAe, hlen, hD'f, hidxf⟩ := hfn
          rw [kindOf_fnRec ⟨D', idx, hAe, hlen, hD'f, hidxf⟩]
          refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          refine ⟨Rcic.Declarative.lift (0 + k) (1 + j) D',
            Rcic.Declarative.lift (0 + k + 1) (1 + j) (foldApps (.const a.family.ref (canonL a.family.member.arity))
              (policyParameterLocals a.family.parameters.length (0 + k + 1) ++ idx)), ?_, ?_⟩
          · rw [hAe]; rfl
          · exact RecHead.lift (⟨canonL a.family.member.arity,
              policyParameterLocals a.family.parameters.length (0 + k + 1) ++ idx,
              rfl⟩ : RecHead a.family.ref _) (0 + k + 1) (1 + j)
  -- the IHOkA lifted over the prefix
  have hpi : ∀ (k : Nat) (A' : Expr Nat), (shapesOf a.family.ref (a.constructorViews i).fields)[k]? =
      some (.recursive 1) → (a.constructorViews i).fields[k]? = some A' →
      ∃ D B, A' = .pi D B := by
    intro k A' hs hA'
    have hs1 : (shapesOf a.family.ref (a.constructorViews i).fields)[k]? =
        ((a.constructorViews i).fields[k]?).map (fun A => shapeOfKind (kindOf a.family.ref A)) := by
      unfold shapesOf kindsOf
      rw [List.getElem?_map, List.getElem?_map, Option.map_map]
      rfl
    rw [hs1, hA'] at hs
    have hs2 : shapeOfKind (kindOf a.family.ref A') = .recursive 1 := Option.some.inj hs
    obtain h0 | hdr | hfn := fieldsClassA_at (a.constructorViews i).fields 0 k (G.fields i) A' hA'
    · rw [kindOf_free h0] at hs2; cases hs2
    · rw [kindOf_directRec hdr] at hs2; cases hs2
    · obtain ⟨D', idx, hAe, _, _, _⟩ := hfn
      exact ⟨D', _, hAe⟩
  have hihL : IHOkA M (σOf vs) a.family.parameters.length
      (den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0)) (.bvar j)) g
      (shapesOf a.family.ref (a.constructorViews i).fields)
      (liftFields (1 + j) (a.constructorViews i).fields 0)
      (push (mo :: ms.take j) (push ps ρ0)) xs := by
    rw [h1]
    have := (IHOkA_liftFields M (σOf vs) a.family.parameters.length mo g (mo :: ms.take j)
      (push ps ρ0) (shapesOf a.family.ref (a.constructorViews i).fields)
      (a.constructorViews i).fields [] xs hpi).mpr hih
    rw [htl] at this; exact this
  have hmem := minor_semA M (σOf vs) E fuel a.family.parameters.length G.opq g hg
    (shapesOf a.family.ref (a.constructorViews i).fields)
    (liftFields (1 + j) (a.constructorViews i).fields 0) _ _ _ _ _ _ xs hsh
    (by rw [shapesOf, kindsOf, List.length_map, List.length_map, liftFields_length'])
    hmt hmj hfitL hihL
  have harg : shArgsA M (σOf vs) g (shapesOf a.family.ref (a.constructorViews i).fields)
      (liftFields (mo :: ms.take j).length (a.constructorViews i).fields 0)
      (push [] (push (mo :: ms.take j) (push ps ρ0))) xs =
      shArgsA M (σOf vs) g (shapesOf a.family.ref (a.constructorViews i).fields)
        (a.constructorViews i).fields (push [] (push ps ρ0)) xs :=
    shArgsA_liftFields M (σOf vs) g (mo :: ms.take j) (push ps ρ0) _ _ [] xs
  rw [show push [] (push (mo :: ms.take j) (push ps ρ0)) = push (mo :: ms.take j) (push ps ρ0) from rfl,
      show push [] (push ps ρ0) = push ps ρ0 from rfl, htl] at harg
  rw [harg] at hmem
  rw [h1] at hmem
  -- the end
  have hidx : (familyIdx a.family.parameters.length (Rcic.Declarative.lift (a.constructorViews i).fields.length (1 + j)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)))).map
      (den M (σOf vs) (push xs (push (mo :: ms.take j) (push ps ρ0)))) =
      (a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0))) := by
    rw [familyIdx_lift, familyIdx_foldApps_const, List.drop_append_of_le_length
      (by rw [length_paramLocals, (a.constructorViews i).parameterCount]; exact Nat.le_refl _),
      List.drop_eq_nil_of_le (by rw [length_paramLocals, (a.constructorViews i).parameterCount]; exact Nat.le_refl _),
      List.nil_append,
      List.map_map, ← hxsl]
    exact List.map_congr_left fun e _ => by
      show den M (σOf vs) _ (Rcic.Declarative.lift xs.length (1 + j) e) = _
      rw [← htl, den_lift_push]
  have h3 : den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0))
      (foldApps (.const (a.family.ref + 1 + j) (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length (1 + j))) =
      fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) ps := by
    rw [den_foldApps]
    have e1 : push (mo :: ms.take j) (push ps ρ0) = push (ps ++ (mo :: ms.take j)) ρ0 :=
      (push_append ps _ ρ0).symm
    rw [e1, ← hpsl, ← htl, den_paramLocals]
    rfl
  rw [hidx, h3, ← fapps_append] at hmem
  have e1 : Equiv (fapps mo ((a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))))
      (fapps mo is) := fapps_congr_args mo hri
  have hV := ctorApp_ctorV a vs hfamμ hctorμ ps mo is hpsl hisl hmo hisfit j hjk xs hxsl _
    (mem_congr_right (ed_congr M (fapp_congr e1 Equiv.rfl)) hmem)
  rw [fapps_append]
  exact mem_congr_right (ed_congr M (fapp_congr e1 hV)) hmem
