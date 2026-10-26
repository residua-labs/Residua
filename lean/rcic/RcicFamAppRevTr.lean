import rcic.RcicFamAppRevTwin
import rcic.RcicParRedDiamond
import rcic.RcicLevelCalc
import rcic.RcicConstsClosedEnvWfT

/-!
# RcicFamAppRevTr — the translation of ANY revealed singleton's environment into its copy-only twin, on terms

The class-B fixture `riEnv` (`RI : Sort 0 → Sort 0`, `mk : Π X, RI X`, AnySort recursor) is carried into its
twins by `RcicClassCAxSpine.tr` (`rec.{l} ↦ recT l := λ M m X h. m X`, `mk ↦ mk₀` at reference `2`). This module
is the same translation for the tier's generic B1 shape (`RcicFamAppRevTwin.RevBase`): a family `F : Π (i : I),
Sort 0` at `f` over a closed index type `I`, its constructor `mk : Π (x : I), F x` at `f + 1`, its AnySort
recursor at `f + 2`. The twin keeps `F` and the constructor's reference (`mk` becomes an axiom at the SAME
reference `f + 1`), so the translation rewrites ONE constant: `rec.{[l]} ↦ recTG f I l := λ (M : Π i, F i → Sort l)
(m : Π x, M x (mk x)) (i : I) (h : F i). m i`. Everything else is the identity; the way back is the identity on terms.

Contents.
* §1 the shape (`motTy`, `minTy`, `recTG`, `recTyG`, the stored members `revCtorM`/`revRecM`) and `tr`.
* §2 `tr` commutes with `lift`, `instantiate`, `instantiateLevels` (the λ-recursor is closed and has the index
  type's level-freeness), `foldApps`, `natExpand`; contexts; `tr` fixes every term whose constants are members of
  an environment without a member at `f + 2` (`tr_id_of_cmc`, `tr_id_of_hasTyT`).
* §3 **the base ι transport**: a ι witness of the environment of interest at a BASE recursor (reference `< f`)
  is a witness of any environment agreeing below `f`, at the translated arguments — `trWitness`, the exact
  shape of the landed `instWitness` (RcicIota): the term fields are mapped, the four shape fields re-established
  from the stored constructor type through the landed producers (`directRecConstHead_applyTel`,
  `resultConstHead_applyTel`), `iotaLhsOf`/`iotaRhsOf` commute (`rhsArgs_tr`). No hypothesis on the base.
* §4 the ι witnesses AT the revealed singleton's recursor have the fixture's shape (`revIota_inv`,
  `RcicClassCAxSpine.riIota_inv` with `I`, `f` free).

closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin

/-! ## §1 the shape and the translation -/

/-- `F i`, under one binder. -/
abbrev famApp0 (f : Nat) : Expr Nat := .app (.const f []) (.bvar 0)

/-- `M i h`, under `[h, i, m, M]`. -/
abbrev recB4 : Expr Nat := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)

section Shape

variable (f : Nat) (I : Expr Nat)

/-- the motive's type at level `l`: `Π (i : I), F i → Sort l`. -/
def motTy (l : Level) : Expr Nat := .pi I (.pi (famApp0 f) (.sort l))

/-- the minor's type under the motive: `Π (x : I), M x (mk x)`. -/
def minTy : Expr Nat := .pi I (.app (.app (.bvar 1) (.bvar 0)) (.app (.const (f + 1) []) (.bvar 0)))

/-- **the λ-recursor**: `λ (M : motTy l) (m : minTy) (i : I) (h : F i). m i`. -/
def recTG (l : Level) : Expr Nat :=
  .lam (motTy f I l) (.lam (minTy f I) (.lam I (.lam (famApp0 f) (.app (.bvar 2) (.bvar 1)))))

/-- the recursor's type at level `l`: `Π (M : motTy l) (m : minTy) (i : I) (h : F i), M i h`. -/
def recTyG (l : Level) : Expr Nat := .pi (motTy f I l) (.pi (minTy f I) (.pi I (.pi (famApp0 f) recB4)))

/-- the STORED recursor type: the motive's sort is the level parameter `0`. -/
def recTyS : Expr Nat := recTyG f I (.param 0)

/-- the constructor member, `mk : Π (x : I), F x`. -/
def revCtorM : CheckedMember := ⟨.constructorM, 0, revCtorTy f I, none⟩

/-- the recursor member, at one level parameter. -/
def revRecM : CheckedMember := ⟨.recursorM, 1, recTyS f I, none⟩

/-- the translation of a constant: `rec.{[l]} ↦ recTG l`, every other constant to itself (a `rec` at a
    level list that is not a singleton is untypable and is left alone). -/
def trC (r : Nat) (ls : List Level) : Expr Nat :=
  if r = f + 2 then (match ls with | [l] => recTG f I l | _ => .const r ls) else .const r ls

/-- **the translation on terms.** -/
def tr : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => trC f I r ls
  | .app a b => .app (tr a) (tr b)
  | .lam a b => .lam (tr a) (tr b)
  | .pi a b => .pi (tr a) (tr b)
  | .letE a v b => .letE (tr a) (tr v) (tr b)
  | .lit t => .lit t

def trDecl : LocalDecl → LocalDecl
  | .assumption a => .assumption (tr f I a)
  | .letBinding a v => .letBinding (tr f I a) (tr f I v)

def trCtx (Γ : LCtx) : LCtx := Γ.map (trDecl f I)

theorem trC_ne {r : Nat} (h : r ≠ f + 2) (ls : List Level) : trC f I r ls = .const r ls := by
  simp [trC, h]

theorem trC_rec (l : Level) : trC f I (f + 2) [l] = recTG f I l := by
  simp [trC]

theorem tr_const_ne {r : Nat} (h : r ≠ f + 2) (ls : List Level) : tr f I (.const r ls) = .const r ls :=
  trC_ne f I h ls

theorem tr_rec (l : Level) : tr f I (.const (f + 2) [l]) = recTG f I l := trC_rec f I l

end Shape

/-! ## §2 commutation -/

section Commute

variable {f : Nat} {I : Expr Nat}

theorem recTG_lift01 (hclI : ∀ k, lift k 1 I = I) (l : Level) : lift 0 1 (recTG f I l) = recTG f I l := by
  simp [recTG, motTy, minTy, lift, hclI]

theorem recTG_lift (hclI : ∀ k, lift k 1 I = I) (l : Level) (c k : Nat) : lift c k (recTG f I l) = recTG f I l :=
  lift_of_closed _ (recTG_lift01 hclI l) c k

theorem recTG_instantiate (hclI : ∀ k, lift k 1 I = I) (l : Level) (j : Nat) (s : Expr Nat) :
    instantiate j s (recTG f I l) = recTG f I l :=
  instantiate_of_closed _ (recTG_lift01 hclI l) j s

theorem trC_lift (hclI : ∀ k, lift k 1 I = I) (r : Nat) (ls : List Level) (c k : Nat) :
    lift c k (trC f I r ls) = trC f I r ls := by
  unfold trC
  split
  · split
    · exact recTG_lift hclI _ c k
    · rfl
  · rfl

theorem trC_instantiate (hclI : ∀ k, lift k 1 I = I) (r : Nat) (ls : List Level) (j : Nat) (s : Expr Nat) :
    instantiate j s (trC f I r ls) = trC f I r ls := by
  unfold trC
  split
  · split
    · exact recTG_instantiate hclI _ j s
    · rfl
  · rfl

theorem tr_lift (hclI : ∀ k, lift k 1 I = I) (k : Nat) :
    (e : Expr Nat) → ∀ c, tr f I (lift c k e) = lift c k (tr f I e)
  | .bvar i, c => by
      by_cases h : c ≤ i <;> simp [lift, tr, h]
  | .sort _, _ => rfl
  | .const r ls, c => by
      simp only [lift, tr]
      exact (trC_lift hclI r ls c k).symm
  | .app a b, c => by simp only [lift, tr, tr_lift hclI k a c, tr_lift hclI k b c]
  | .lam a b, c => by simp only [lift, tr, tr_lift hclI k a c, tr_lift hclI k b (c + 1)]
  | .pi a b, c => by simp only [lift, tr, tr_lift hclI k a c, tr_lift hclI k b (c + 1)]
  | .letE a v b, c => by
      simp only [lift, tr, tr_lift hclI k a c, tr_lift hclI k v c, tr_lift hclI k b (c + 1)]
  | .lit _, _ => rfl

theorem tr_instantiate (hclI : ∀ k, lift k 1 I = I) (s : Expr Nat) :
    (e : Expr Nat) → ∀ j, tr f I (instantiate j s e) = instantiate j (tr f I s) (tr f I e)
  | .bvar i, j => by
      by_cases h1 : i = j
      · simp [instantiate, tr, h1]
      · by_cases h2 : j < i <;> simp [instantiate, tr, h1, h2]
  | .sort _, _ => rfl
  | .const r ls, j => by
      simp only [instantiate, tr]
      exact (trC_instantiate hclI r ls j _).symm
  | .app a b, j => by simp only [instantiate, tr, tr_instantiate hclI s a j, tr_instantiate hclI s b j]
  | .lam a b, j => by
      simp only [instantiate, tr, tr_instantiate hclI s a j, tr_instantiate hclI (lift 0 1 s) b (j + 1),
        tr_lift hclI]
  | .pi a b, j => by
      simp only [instantiate, tr, tr_instantiate hclI s a j, tr_instantiate hclI (lift 0 1 s) b (j + 1),
        tr_lift hclI]
  | .letE a v b, j => by
      simp only [instantiate, tr, tr_instantiate hclI s a j, tr_instantiate hclI s v j,
        tr_instantiate hclI (lift 0 1 s) b (j + 1), tr_lift hclI]
  | .lit _, _ => rfl

theorem tr_instantiate0 (hclI : ∀ k, lift k 1 I = I) (s e : Expr Nat) :
    tr f I (instantiate0 s e) = instantiate0 (tr f I s) (tr f I e) :=
  tr_instantiate hclI s e 0

theorem recTG_instantiateLevels (hlvlI : exprLevelsBounded 0 I = true) (ls : List Level) (l : Level) :
    instantiateLevels ls (recTG f I l) = recTG f I (instLevel ls l) := by
  simp [recTG, motTy, minTy, instantiateLevels, Ann.instantiateLevels_closed ls I hlvlI]

theorem trC_instantiateLevels (hlvlI : exprLevelsBounded 0 I = true) (ls : List Level) (r : Nat) :
    (ms : List Level) → trC f I r (ms.map (instLevel ls)) = instantiateLevels ls (trC f I r ms)
  | [] => by
      unfold trC
      split <;> rfl
  | [l] => by
      unfold trC
      split
      · simp only [List.map_cons, List.map_nil]
        exact (recTG_instantiateLevels hlvlI ls l).symm
      · rfl
  | _ :: _ :: _ => by
      unfold trC
      split <;> rfl

theorem tr_instantiateLevels (hlvlI : exprLevelsBounded 0 I = true) (ls : List Level) :
    (e : Expr Nat) → tr f I (instantiateLevels ls e) = instantiateLevels ls (tr f I e)
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const r ms => by
      simp only [instantiateLevels, tr]
      exact trC_instantiateLevels hlvlI ls r ms
  | .app a b => by
      simp only [instantiateLevels, tr, tr_instantiateLevels hlvlI ls a, tr_instantiateLevels hlvlI ls b]
  | .lam a b => by
      simp only [instantiateLevels, tr, tr_instantiateLevels hlvlI ls a, tr_instantiateLevels hlvlI ls b]
  | .pi a b => by
      simp only [instantiateLevels, tr, tr_instantiateLevels hlvlI ls a, tr_instantiateLevels hlvlI ls b]
  | .letE a v b => by
      simp only [instantiateLevels, tr, tr_instantiateLevels hlvlI ls a, tr_instantiateLevels hlvlI ls v,
        tr_instantiateLevels hlvlI ls b]
  | .lit _ => rfl

theorem tr_natExpand (t : Nat) : tr f I (natExpand t) = natExpand t := by
  induction t with
  | zero =>
      show trC f I 1 [] = .const 1 []
      unfold trC
      split
      · rfl
      · rfl
  | succ t ih =>
      show Expr.app (trC f I 2 []) (tr f I (natExpand t)) = .app (.const 2 []) (natExpand t)
      rw [ih]
      unfold trC
      split
      · rfl
      · rfl

theorem tr_foldApps (g : Expr Nat) (xs : List (Expr Nat)) :
    tr f I (foldApps g xs) = foldApps (tr f I g) (xs.map (tr f I)) := by
  induction xs generalizing g with
  | nil => rfl
  | cons x xs ih => simp only [foldApps, ih, tr, List.map]

theorem lookupType_trCtx (hclI : ∀ k, lift k 1 I = I) (Γ : LCtx) (i : Nat) :
    lookupType (trCtx f I Γ) i = (lookupType Γ i).map (tr f I) := by
  unfold lookupType trCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp [trDecl, tr_lift hclI]
      | letBinding a v => simp [trDecl, tr_lift hclI]

theorem lookupValue_trCtx (hclI : ∀ k, lift k 1 I = I) (Γ : LCtx) (i : Nat) :
    lookupValue (trCtx f I Γ) i = (lookupValue Γ i).map (tr f I) := by
  unfold lookupValue trCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => rfl
      | letBinding a v => simp [trDecl, tr_lift hclI]

/-- `tr` fixes every term whose constants are members of an environment with no member at `f + 2`. -/
theorem tr_id_of_cmc {E : ResolvedEnv} (h2 : E.members (f + 2) = none) :
    ∀ {e : Expr Nat}, ConstsMemberClosed E e → tr f I e = e
  | _, .bvar _ => rfl
  | _, .sort _ => rfl
  | _, .lit _ _ => rfl
  | _, .const r ls m hmem _ => by
      have hne : r ≠ f + 2 := fun h => by rw [h, h2] at hmem; exact Option.noConfusion hmem
      exact tr_const_ne f I hne ls
  | _, .app hf ha => by simp only [tr, tr_id_of_cmc h2 hf, tr_id_of_cmc h2 ha]
  | _, .lam hA hb => by simp only [tr, tr_id_of_cmc h2 hA, tr_id_of_cmc h2 hb]
  | _, .pi hA hb => by simp only [tr, tr_id_of_cmc h2 hA, tr_id_of_cmc h2 hb]
  | _, .letE hA hv hb => by simp only [tr, tr_id_of_cmc h2 hA, tr_id_of_cmc h2 hv, tr_id_of_cmc h2 hb]

/-- `tr` fixes every term whose constants are members of an environment with no member at `f + 2`
    (`ConstsIn` form). -/
theorem tr_id_of_constsIn {E : ResolvedEnv} (h2 : E.members (f + 2) = none) :
    (e : Expr Nat) → ConstsIn E e → tr f I e = e
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit _, _ => rfl
  | .const r ls, ⟨m, hmem⟩ => by
      have hne : r ≠ f + 2 := fun h => by rw [h, h2] at hmem; exact Option.noConfusion hmem
      exact tr_const_ne f I hne ls
  | .app a b, ⟨ha, hb⟩ => by simp only [tr, tr_id_of_constsIn h2 a ha, tr_id_of_constsIn h2 b hb]
  | .lam a b, ⟨ha, hb⟩ => by simp only [tr, tr_id_of_constsIn h2 a ha, tr_id_of_constsIn h2 b hb]
  | .pi a b, ⟨ha, hb⟩ => by simp only [tr, tr_id_of_constsIn h2 a ha, tr_id_of_constsIn h2 b hb]
  | .letE a v b, ⟨ha, hv, hb⟩ => by
      simp only [tr, tr_id_of_constsIn h2 a ha, tr_id_of_constsIn h2 v hv, tr_id_of_constsIn h2 b hb]

/-- `tr` fixes every term typed in an environment with no member at `f + 2`. -/
theorem tr_id_of_hasTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (h2 : E.members (f + 2) = none) (h : HasTyT E n Γ e A) : tr f I e = e :=
  tr_id_of_constsIn h2 e (hasTyT_constsIn h)

/-- a constant that is no member does not occur in a term whose constants are members. -/
theorem occursConst_false_of_constsIn {E : ResolvedEnv} {r : Nat} (hr : E.members r = none) :
    (e : Expr Nat) → ConstsIn E e → occursConst r e = false
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r' _, ⟨m, hmem⟩ => by
      have hne : r' ≠ r := fun h => by rw [h, hr] at hmem; exact Option.noConfusion hmem
      simp [occursConst, hne]
  | .app a b, ⟨ha, hb⟩ => by
      simp only [occursConst, occursConst_false_of_constsIn hr a ha, occursConst_false_of_constsIn hr b hb,
        Bool.or_self]
  | .lam a b, ⟨ha, hb⟩ => by
      simp only [occursConst, occursConst_false_of_constsIn hr a ha, occursConst_false_of_constsIn hr b hb,
        Bool.or_self]
  | .pi a b, ⟨ha, hb⟩ => by
      simp only [occursConst, occursConst_false_of_constsIn hr a ha, occursConst_false_of_constsIn hr b hb,
        Bool.or_self]
  | .letE a v b, ⟨ha, hv, hb⟩ => by
      simp only [occursConst, occursConst_false_of_constsIn hr a ha, occursConst_false_of_constsIn hr v hv,
        occursConst_false_of_constsIn hr b hb, Bool.or_self]
  | .lit 0, ⟨m, hmem⟩ => by
      have hne : r ≠ 1 := fun h => by rw [h, hmem] at hr; exact Option.noConfusion hr
      simp [occursConst, litOccurs, hne]
  | .lit (t + 1), ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ => by
      have hne1 : r ≠ 1 := fun h => by rw [h, hm1] at hr; exact Option.noConfusion hr
      have hne2 : r ≠ 2 := fun h => by rw [h, hm2] at hr; exact Option.noConfusion hr
      simp [occursConst, litOccurs, hne1, hne2]

end Commute

/-! ## §3 the base ι transport -/

section Spine

variable {f : Nat} {I : Expr Nat}

/-- the translation of a non-application is a non-application, so spines translate pointwise. -/
theorem appsSpine_tr : (e : Expr Nat) →
    appsSpine (tr f I e) = (tr f I (appsSpine e).1, (appsSpine e).2.map (tr f I))
  | .app g x => by
      simp only [tr, appsSpine, appsSpine_tr g, List.map_append, List.map_cons, List.map_nil]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const r ls => by
      show appsSpine (trC f I r ls) = (trC f I r ls, [])
      unfold trC
      split
      · split <;> rfl
      · rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem familyIdx_tr (nparams : Nat) (A : Expr Nat) :
    familyIdx nparams (tr f I A) = (familyIdx nparams A).map (tr f I) := by
  simp only [familyIdx, appsSpine_tr, List.map_drop]

theorem recPrefix_tr (pre : List (Expr Nat)) (nparams nMinors : Nat) :
    recPrefix (pre.map (tr f I)) nparams nMinors = (recPrefix pre nparams nMinors).map (tr f I) := by
  simp only [recPrefix, List.map_take]

theorem recCall_tr (rec : Expr Nat) (pre : List (Expr Nat)) (major : Expr Nat) :
    tr f I (recCall rec pre major) = recCall (tr f I rec) (pre.map (tr f I)) (tr f I major) := by
  simp only [recCall, tr_foldApps, List.map_append, List.map_cons, List.map_nil]

theorem recCallField_tr (rec : Expr Nat) (pre : List (Expr Nat)) (nparams nMinors : Nat) (g A : Expr Nat) :
    tr f I (recCallField rec pre nparams nMinors g A) =
      recCallField (tr f I rec) (pre.map (tr f I)) nparams nMinors (tr f I g) (tr f I A) := by
  simp only [recCallField, tr_foldApps, List.map_append, List.map_cons, List.map_nil, recPrefix_tr,
    familyIdx_tr]

/-- a non-Π telescope falls through to the next field, whatever the kind. -/
theorem rhsArgs_notPi (rec : Expr Nat) (pre : List (Expr Nat)) (nparams nMinors : Nat) (g : Expr Nat)
    (fs : List (Expr Nat)) (k : RecKind) (ks : List RecKind) :
    (T : Expr Nat) → (∀ A B, T ≠ .pi A B) →
    rhsArgs rec pre nparams nMinors (g :: fs) (k :: ks) T = g :: rhsArgs rec pre nparams nMinors fs ks T
  | .pi A B, h => absurd rfl (h A B)
  | .bvar _, _ => by cases k <;> rfl
  | .sort _, _ => by cases k <;> rfl
  | .const _ _, _ => by cases k <;> rfl
  | .app _ _, _ => by cases k <;> rfl
  | .lam _ _, _ => by cases k <;> rfl
  | .letE _ _ _, _ => by cases k <;> rfl
  | .lit _, _ => by cases k <;> rfl

theorem trC_not_pi (r : Nat) (ls : List Level) (A B : Expr Nat) : trC f I r ls ≠ .pi A B := by
  unfold trC
  split
  · split <;> exact fun h => Expr.noConfusion h
  · exact fun h => Expr.noConfusion h

/-- `rhsArgs` commutes with `tr`: the telescope's Π-shape is preserved by `tr`, so every arm of the
    definition is hit by the same arm after translation (no bvar-hit, unlike `instantiate`). -/
theorem rhsArgs_tr (hclI : ∀ k, lift k 1 I = I) (nparams nMinors : Nat) (rec : Expr Nat)
    (pre : List (Expr Nat)) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (T : Expr Nat) →
    (rhsArgs rec pre nparams nMinors fs ks T).map (tr f I) =
      rhsArgs (tr f I rec) (pre.map (tr f I)) nparams nMinors (fs.map (tr f I)) ks (tr f I T)
  | [], _, _ => by simp only [rhsArgs, List.map_nil]
  | g :: fs, [], T => by
      simp only [rhsArgs, List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs [] T]
  | g :: fs, .plain :: ks, .pi A B => by
      simp only [rhsArgs, List.map_cons, tr]
      rw [rhsArgs_tr hclI nparams nMinors rec pre fs ks (instantiate0 g B), tr_instantiate0 hclI]
  | g :: fs, .directRec :: ks, .pi A B => by
      simp only [rhsArgs, List.map_cons, tr]
      rw [recCallField_tr, rhsArgs_tr hclI nparams nMinors rec pre fs ks (instantiate0 g B),
        tr_instantiate0 hclI]
  | g :: fs, k :: ks, .bvar i => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.bvar i) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.bvar i), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.bvar i)) (fun _ _ h => Expr.noConfusion h)).symm
  | g :: fs, k :: ks, .sort l => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.sort l) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.sort l), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.sort l)) (fun _ _ h => Expr.noConfusion h)).symm
  | g :: fs, k :: ks, .const r ls => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.const r ls) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.const r ls), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.const r ls)) (trC_not_pi r ls)).symm
  | g :: fs, k :: ks, .app a b => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.app a b) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.app a b), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.app a b)) (fun _ _ h => Expr.noConfusion h)).symm
  | g :: fs, k :: ks, .lam a b => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.lam a b) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.lam a b), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.lam a b)) (fun _ _ h => Expr.noConfusion h)).symm
  | g :: fs, k :: ks, .letE a v b => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.letE a v b) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.letE a v b), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.letE a v b)) (fun _ _ h => Expr.noConfusion h)).symm
  | g :: fs, k :: ks, .lit t => by
      rw [rhsArgs_notPi rec pre nparams nMinors g fs k ks (.lit t) (fun _ _ h => Expr.noConfusion h),
        List.map_cons, rhsArgs_tr hclI nparams nMinors rec pre fs ks (.lit t), List.map_cons]
      exact (rhsArgs_notPi _ _ _ _ _ _ k ks (tr f I (.lit t)) (fun _ _ h => Expr.noConfusion h)).symm

theorem isPiTel_tr : (n : Nat) → (T : Expr Nat) → isPiTel n T = true → isPiTel n (tr f I T) = true
  | 0, _, _ => rfl
  | n + 1, .pi A B, h => by
      simp only [isPiTel, tr] at h ⊢
      exact isPiTel_tr n B h
  | _ + 1, .bvar _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .sort _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .const _ _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .app _ _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .lam _ _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .letE _ _ _, h => by simp only [isPiTel] at h; nomatch h
  | _ + 1, .lit _, h => by simp only [isPiTel] at h; nomatch h

/-- `applyTel` of translated arguments on a translated telescope. -/
theorem applyTel_congr_tr (hclI : ∀ k, lift k 1 I = I) :
    (xs : List (Expr Nat)) → {T U : Expr Nat} → applyTel xs T = some U →
    applyTel (xs.map (tr f I)) (tr f I T) = some (tr f I U)
  | [], T, U, h => by
      simp only [applyTel] at h
      injection h with h
      subst h
      rfl
  | x :: xs, T, U, h => by
      obtain ⟨A, B, hT, h'⟩ := applyTel_cons_inv x xs h
      subst hT
      simp only [List.map_cons, tr, applyTel]
      rw [← tr_instantiate0 hclI]
      exact applyTel_congr_tr hclI xs h'

end Spine

section Witness

variable {f : Nat} {I : Expr Nat} {E G : ResolvedEnv}

/-- the three references of a witness at a recursor below `f` are all below `f`. -/
theorem witness_refs_lt (w : IotaWitness E) (hlt : w.recRef < f) :
    w.ctorRef < f ∧ w.familyRef < f := by
  have h1 := w.hctorIdx
  have h2 := w.hrecIdx
  have h3 := w.hidx
  exact ⟨by omega, by omega⟩

/-- **the base ι transport.** A witness of `E` at a recursor below `f` is a witness of any `G` that agrees
    with `E` below `f`, at the translated term fields: the shape of the landed `instWitness`. The stored
    constructor type is fixed by `tr` (`hfix`), and the two head-shape fields are re-derived from it through
    the landed producers (`directRecConstHead_applyTel`, `resultConstHead_applyTel`). -/
def trWitness (hclI : ∀ k, lift k 1 I = I) (hlvlI : exprLevelsBounded 0 I = true)
    (hagree : ∀ r, r < f → G.members r = E.members r) (w : IotaWitness E) (hlt : w.recRef < f)
    (hfix : tr f I w.ctorMember.mtype = w.ctorMember.mtype) : IotaWitness G where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := by rw [hagree _ hlt]; exact w.hrec
  hctor := by rw [hagree _ (witness_refs_lt w hlt).1]; exact w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (tr f I)
  fields := w.fields.map (tr f I)
  ctorParams := w.ctorParams.map (tr f I)
  kinds := w.kinds
  minor := tr f I w.minor
  hlen := by simp only [List.length_map]; exact w.hlen
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := by rw [hagree _ (witness_refs_lt w hlt).2]; exact w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by simp only [List.length_map]; exact w.hctorParams
  hnpar := by simp only [List.length_map]; exact w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by simp only [List.length_map]; exact w.hpre
  hminor := by rw [List.getElem?_map, w.hminor]; rfl
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by simp only [List.length_map]; exact w.hpeel
  hfamApp := w.hfamApp
  hkinds := w.hkinds
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  ctorAfterParams := tr f I w.ctorAfterParams
  hctorAfter := by
    rw [← List.map_take]
    have happ := applyTel_congr_tr (f := f) hclI (w.preMajor.take w.nparams) w.hctorAfter
    rw [tr_instantiateLevels hlvlI, hfix] at happ
    exact happ
  hctorTel := isPiTel_tr _ _ w.hctorTel
  hfamTel := by
    have happ := applyTel_congr_tr (f := f) hclI (w.preMajor.take w.nparams) w.hctorAfter
    rw [tr_instantiateLevels hlvlI, hfix] at happ
    have hlenP : (w.preMajor.take w.nparams).length = w.nparams := by
      rw [List.length_take, w.hpre]; omega
    have hpeel' : peelPis (w.nparams + w.kinds.length) w.ctorMember.mtype = some (w.ctorDoms, w.ctorResult) := by
      rw [w.hlen]; exact w.hpeel
    have htel : isPiTel (((w.preMajor.take w.nparams).map (tr f I)).length + w.kinds.length)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
      rw [List.length_map, hlenP, isPiTel_instantiateLevels]
      exact peelPis_isPiTel _ _ hpeel'
    have hpref : directRecConstHead
        (List.replicate ((w.preMajor.take w.nparams).map (tr f I)).length RecKind.plain ++ w.kinds)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
      rw [List.length_map, hlenP, directRecConstHead_instantiateLevels]
      exact directRecConstHead_plain_prefix_of_analyzeFields w.familyRef w.nparams w.kinds _ hpeel' w.hkinds
    exact directRecConstHead_applyTel w.kinds _ _ _ happ htel hpref
  hresTel := by
    have happ := applyTel_congr_tr (f := f) hclI (w.preMajor.take w.nparams) w.hctorAfter
    rw [tr_instantiateLevels hlvlI, hfix] at happ
    have hlenP : (w.preMajor.take w.nparams).length = w.nparams := by
      rw [List.length_take, w.hpre]; omega
    have hpeel' : peelPis (List.replicate w.nparams RecKind.plain ++ w.kinds).length w.ctorMember.mtype =
        some (w.ctorDoms, w.ctorResult) := by
      rw [List.length_append, List.length_replicate, w.hlen]; exact w.hpeel
    have htel : isPiTel (((w.preMajor.take w.nparams).map (tr f I)).length + w.kinds.length)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
      rw [List.length_map, hlenP, isPiTel_instantiateLevels]
      have := peelPis_isPiTel _ _ hpeel'
      rwa [List.length_append, List.length_replicate] at this
    have hres : resultConstHead
        (List.replicate ((w.preMajor.take w.nparams).map (tr f I)).length RecKind.plain ++ w.kinds)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
      rw [List.length_map, hlenP, resultConstHead_instantiateLevels]
      exact resultConstHead_of_peelPis _ _ hpeel' (isFamilyApp_spineHeadConst w.hfamApp)
    exact resultConstHead_applyTel w.kinds _ _ _ happ htel hres

theorem ctorMajor_tr (hclI : ∀ k, lift k 1 I = I) (hlvlI : exprLevelsBounded 0 I = true)
    (hagree : ∀ r, r < f → G.members r = E.members r) (w : IotaWitness E) (hlt : w.recRef < f)
    (hfix : tr f I w.ctorMember.mtype = w.ctorMember.mtype) :
    ctorMajor (trWitness hclI hlvlI hagree w hlt hfix) = tr f I (ctorMajor w) := by
  have hne : w.ctorRef ≠ f + 2 := by have := (witness_refs_lt w hlt).1; omega
  show foldApps (.const w.ctorRef w.lsC) (w.ctorParams.map (tr f I) ++ w.fields.map (tr f I)) =
    tr f I (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
  rw [tr_foldApps, tr_const_ne f I hne, List.map_append]

theorem iotaLhsOf_tr (hclI : ∀ k, lift k 1 I = I) (hlvlI : exprLevelsBounded 0 I = true)
    (hagree : ∀ r, r < f → G.members r = E.members r) (w : IotaWitness E) (hlt : w.recRef < f)
    (hfix : tr f I w.ctorMember.mtype = w.ctorMember.mtype) :
    iotaLhsOf (trWitness hclI hlvlI hagree w hlt hfix) = tr f I (iotaLhsOf w) := by
  have hne : w.recRef ≠ f + 2 := by omega
  unfold iotaLhsOf
  rw [recCall_tr, ctorMajor_tr, tr_const_ne f I hne]
  rfl

theorem iotaRhsOf_tr (hclI : ∀ k, lift k 1 I = I) (hlvlI : exprLevelsBounded 0 I = true)
    (hagree : ∀ r, r < f → G.members r = E.members r) (w : IotaWitness E) (hlt : w.recRef < f)
    (hfix : tr f I w.ctorMember.mtype = w.ctorMember.mtype) :
    iotaRhsOf (trWitness hclI hlvlI hagree w hlt hfix) = tr f I (iotaRhsOf w) := by
  have hne : w.recRef ≠ f + 2 := by omega
  show foldApps (tr f I w.minor) (rhsArgs (.const w.recRef w.ls) (w.preMajor.map (tr f I)) w.nparams w.nMinors
      (w.fields.map (tr f I)) w.kinds (tr f I w.ctorAfterParams)) =
    tr f I (foldApps w.minor (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors w.fields w.kinds
      w.ctorAfterParams))
  rw [tr_foldApps, rhsArgs_tr hclI, tr_const_ne f I hne]

/-- **the base ι step, translated**: a derived ι of `E` at a base recursor is a derived ι of `G` at the
    translated redex and reduct. -/
def derivedIota_tr (hclI : ∀ k, lift k 1 I = I) (hlvlI : exprLevelsBounded 0 I = true)
    (hagree : ∀ r, r < f → G.members r = E.members r) (w : IotaWitness E) (hlt : w.recRef < f)
    (hfix : tr f I w.ctorMember.mtype = w.ctorMember.mtype) :
    DerivedIota G (tr f I (iotaLhsOf w)) (tr f I (iotaRhsOf w)) := by
  rw [← iotaLhsOf_tr hclI hlvlI hagree w hlt hfix, ← iotaRhsOf_tr hclI hlvlI hagree w hlt hfix]
  exact .of (trWitness hclI hlvlI hagree w hlt hfix)

end Witness

/-! ## §4 the ι witnesses at the revealed singleton's recursor -/

section Inv

variable {f : Nat} {I : Expr Nat}

theorem piCount_recTyS : piCount (recTyS f I) = 4 := rfl

theorem piCount_revCtorTy : piCount (revCtorTy f I) = 1 := rfl

theorem piCount_revFamTy : piCount (revFamM I).mtype = 1 := rfl

theorem peelPis_recTyS :
    peelPis 4 (recTyS f I) = some ([motTy f I (.param 0), minTy f I, I, famApp0 f], recB4) := rfl

theorem peelPis_revCtorTy : peelPis 1 (revCtorTy f I) = some ([I], famApp0 f) := rfl

theorem analyzeFields_rev (hIfree : occursConst f I = false) : analyzeFields f [I] = some [.plain] := by
  simp [analyzeFields, analyzeField, hIfree]

/-- **every ι witness at the recursor `f + 2` has the fixture's shape**: the recursor at `[l]`, three pre-major
    arguments, the constructor applied to one field, the minor applied to that field. The environment is read
    at `f`, `f + 1`, `f + 2` only. -/
theorem revIota_inv {E : ResolvedEnv} (h0 : E.members f = some (revFamM I)) (h1 : E.members (f + 1) = some (revCtorM f I))
    (h2 : E.members (f + 2) = some (revRecM f I)) (hlvlI : exprLevelsBounded 0 I = true)
    (hIfree : occursConst f I = false) (w : IotaWitness E) (hr : w.recRef = f + 2) :
    ∃ (ls lsC : List Level) (M m X x : Expr Nat), ls.length = 1 ∧
      iotaLhsOf w = foldApps (.const (f + 2) ls) [M, m, X, foldApps (.const (f + 1) lsC) [x]] ∧
      iotaRhsOf w = .app m x := by
  obtain ⟨recRef, ctorRef, ls, lsC, recMember, ctorMember, hrec, hctor, hrecK, hctorK,
    preMajor, fields, ctorParams, kinds, minor, hlen, familyRef, famMember, hfam, hfamK,
    nparams, nindices, nMinors, ctorIdx, hctorParams, hnpar, hnidx, hnmin, hidx, hctorIdx,
    hrecIdx, hpre, hminor, ctorDoms, ctorResult, hpeel, hfamApp, hkinds, recDoms, recBody,
    hpeelRec, hrecBody, hmajorTy, hrecClosed, hctorClosed, hlsLen, ctorAfterParams,
    hctorAfter, hctorTel, hfamTel, hresTel⟩ := w
  simp only at hr
  subst hr
  rw [h2] at hrec
  obtain rfl : revRecM f I = recMember := Option.some.inj hrec
  have p3 : piCount (revRecM f I).mtype = 4 := rfl
  rw [p3] at hnmin
  -- the family is `f` and there is one minor: the other arities contradict the stored recursor type
  have hcases : nMinors = 0 ∨ nMinors = 1 ∨ nMinors = 2 := by omega
  have hnM : nMinors = 1 := by
    rcases hcases with h | h | h
    · exfalso
      subst h
      have hfr : familyRef = f + 1 := by omega
      subst hfr
      rw [h1] at hfam
      obtain rfl : revCtorM f I = famMember := Option.some.inj hfam
      exact MemberClass.noConfusion hfamK
    · exact h
    · exfalso
      subst h
      have hnp : nparams = 0 := by omega
      have hni : nindices = 0 := by omega
      subst hnp hni
      have hP : peelPis (0 + 1 + 2 + 0 + 1) (revRecM f I).mtype =
          some ([motTy f I (.param 0), minTy f I, I, famApp0 f], recB4) := rfl
      rw [hP] at hpeelRec
      obtain ⟨hd, -⟩ := Prod.mk.inj (Option.some.inj hpeelRec)
      subst hd
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.range_zero, List.reverse_nil,
        List.map_nil, List.append_nil, foldApps, Option.some.injEq] at hmajorTy
      exact Expr.noConfusion hmajorTy
  subst hnM
  have hfr : familyRef = f := by omega
  subst familyRef
  rw [h0] at hfam
  obtain rfl : revFamM I = famMember := Option.some.inj hfam
  have hci : ctorIdx = 0 := by omega
  subst hci
  have hcr : ctorRef = f + 1 := by omega
  subst hcr
  rw [h1] at hctor
  obtain rfl : revCtorM f I = ctorMember := Option.some.inj hctor
  have p1 : piCount (revCtorM f I).mtype = 1 := rfl
  have p2 : piCount (revFamM I).mtype = 1 := rfl
  rw [p1] at hnpar
  rw [p2] at hnidx
  have hnp : nparams = 0 := by
    refine Decidable.byContradiction (fun hne => ?_)
    have hn1 : nparams = 1 := by omega
    have hn2 : nindices = 0 := by omega
    subst hn1 hn2
    have hP : peelPis (1 + 1 + 1 + 0 + 1) (revRecM f I).mtype =
        some ([motTy f I (.param 0), minTy f I, I, famApp0 f], recB4) := rfl
    rw [hP] at hpeelRec
    obtain ⟨-, hb⟩ := Prod.mk.inj (Option.some.inj hpeelRec)
    rw [← hb] at hrecBody
    simp [foldApps] at hrecBody
  subst hnp
  have hnI : nindices = 1 := by omega
  subst hnI
  have hfl : fields.length = 1 := by omega
  obtain ⟨x, rfl⟩ := List.length_eq_one.mp hfl
  obtain ⟨M, m, X, rfl⟩ : ∃ M m X, preMajor = [M, m, X] := by
    match preMajor, hpre with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hcp : ctorParams = [] := List.length_eq_zero.mp hctorParams
  subst hcp
  have hq : peelPis (0 + [x].length) (revCtorM f I).mtype = some ([I], famApp0 f) := rfl
  rw [hq] at hpeel
  obtain ⟨hcd, -⟩ := Prod.mk.inj (Option.some.inj hpeel)
  subst hcd
  have ha : analyzeFields f (List.drop 0 [I]) = some [RecKind.plain] := analyzeFields_rev hIfree
  rw [ha] at hkinds
  have hks : kinds = [.plain] := (Option.some.inj hkinds).symm
  subst hks
  have hmin : minor = m := by
    have := hminor
    simp at this
    exact this.symm
  subst hmin
  have hca : ctorAfterParams = instantiateLevels ls (revCtorM f I).mtype := by
    have := hctorAfter
    simp [applyTel] at this
    exact this.symm
  refine ⟨ls, lsC, M, minor, X, x, hlsLen, ?_, ?_⟩
  · simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps]
  · subst hca
    simp [iotaRhsOf, rhsArgs, foldApps, revCtorM, revCtorTy, instantiateLevels]

/-- the ι redex at `f + 2`, as an equation on the endpoints. -/
theorem revIota_inv' {E : ResolvedEnv} (h0 : E.members f = some (revFamM I)) (h1 : E.members (f + 1) = some (revCtorM f I))
    (h2 : E.members (f + 2) = some (revRecM f I)) (hlvlI : exprLevelsBounded 0 I = true)
    (hIfree : occursConst f I = false) {lhs rhs : Expr Nat} (d : DerivedIota E lhs rhs)
    (hr : ∀ w : IotaWitness E, lhs = iotaLhsOf w → rhs = iotaRhsOf w → w.recRef = f + 2) :
    ∃ (ls lsC : List Level) (M m X x : Expr Nat), ls.length = 1 ∧
      lhs = foldApps (.const (f + 2) ls) [M, m, X, foldApps (.const (f + 1) lsC) [x]] ∧
      rhs = .app m x := by
  cases d with
  | of w => exact revIota_inv h0 h1 h2 hlvlI hIfree w (hr w rfl rfl)

end Inv

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.trWitness
#print axioms Rcic.Syn.FamApp.Rev.derivedIota_tr
#print axioms Rcic.Syn.FamApp.Rev.revIota_inv
