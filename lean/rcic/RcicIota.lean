/-
RCIC F-05a: DerivedIota is the 05 §11–12 relation; IotaLift / IotaSubst
are theorems over it (00 §19 O-1).

Criterion for IotaWitness fields: a field stays iff `iotaRhsOf` reads
it or kernel iota checks it. Neither: it leaves the redex and lives
on `IotaTyping` (05 admission; IotaPreserve premise). Recursive-call
indices are `familyIdx` of the ctor telescope instantiated with
`preMajor`, not `idxPositions`.

05 §13 recursor signature is now IotaWitness fields (`hpeelRec` /
`hrecBody`) plus `IotaTyping.hminDom` (`mdom = minorTel`): `rec_I : Π
params motive minors indices (major : I params indices), motive
indices major`, and the selected minor domain is `minorTel` of the
constructor field telescope with IH binders. 0-ary IotaPreserve is
`iotaPreserve_zero`. n-ary: `telArgs_fields` (ctor params then
fields). DirectRec IH is `recCallField` (05 §14 field indices from
`appsSpine A`), so `HasTy f A` types the IH without `Conv A A_syn`.
`familyIdx` instantiate is gated on `directRecConstHead` (M-001:
bvar-hit commute is false). Post-IH instantiate is
`instantiate0_minorTel_directRec`. `applyTel_recPrefix_idx_last` is
05 §13: last-Π after `recPrefix ++ idx` is `I params idx`.
`directRec_eq_family` matches the DirectRec field type to that app.
IH typing when `familyIdx = majors` is `hasTy_recCallField_aligned`.
Arbitrary `familyIdx` is `telArgs_idxGo` /
`hasTy_recCallField_of_align` given `idxTyAlign` (ctor domain =
recursor index domain). n-ary `iotaPreserve_plain` and
`iotaPreserve_nindices_zero` are theorems; `iotaPreserve_of_align`
covers Vec.cons given `recIdxTyWalk`. IotaPreserve is a theorem
(`iotaPreserve`) over `DerivedIota + IotaTyping`; O-2 fires on
DT-010/011. Lit* remain 08. Attempt count: 20.
-/
import rcic.RcicDeclarative
import rcic.RcicLevelCalc
import rcic.RcicSubstCalc

namespace Rcic.Declarative

theorem foldApps_nil (f : Expr Nat) : foldApps f [] = f := rfl

theorem foldApps_cons (f x : Expr Nat) (xs : List (Expr Nat)) :
    foldApps f (x :: xs) = foldApps (.app f x) xs := rfl

theorem foldApps_lift (c a : Nat) (f : Expr Nat) (xs : List (Expr Nat)) :
    lift c a (foldApps f xs) = foldApps (lift c a f) (xs.map (lift c a)) := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps, List.map_nil]
  | cons x xs ih =>
      simp only [foldApps, List.map_cons, lift]
      exact ih (.app f x)

theorem lift_inj (c : Nat) :
    (e1 e2 : Expr Nat) → lift c 1 e1 = lift c 1 e2 → e1 = e2
  | .bvar i, .bvar j, h => by
      simp only [lift] at h
      by_cases hi : c ≤ i
      · rw [if_pos hi] at h
        by_cases hj : c ≤ j
        · rw [if_pos hj] at h
          injection h with hij
          have : i = j := Nat.add_right_cancel hij
          rw [this]
        · rw [if_neg hj] at h
          injection h with hij
          omega
      · rw [if_neg hi] at h
        by_cases hj : c ≤ j
        · rw [if_pos hj] at h
          injection h with hij
          omega
        · rw [if_neg hj] at h
          injection h with hij
          subst hij
          rfl
  | .sort _, .sort _, h => by
      simp only [lift] at h
      injection h with hl
      subst hl
      rfl
  | .const _ _, .const _ _, h => by
      simp only [lift] at h
      injection h with hr hls
      subst hr
      subst hls
      rfl
  | .app f1 x1, .app f2 x2, h => by
      simp only [lift] at h
      injection h with hf hx
      have hf' := lift_inj c f1 f2 hf
      have hx' := lift_inj c x1 x2 hx
      subst hf'
      subst hx'
      rfl
  | .lam A1 b1, .lam A2 b2, h => by
      simp only [lift] at h
      injection h with hA hb
      have hA' := lift_inj c A1 A2 hA
      have hb' := lift_inj (c + 1) b1 b2 hb
      subst hA'
      subst hb'
      rfl
  | .pi A1 B1, .pi A2 B2, h => by
      simp only [lift] at h
      injection h with hA hB
      have hA' := lift_inj c A1 A2 hA
      have hB' := lift_inj (c + 1) B1 B2 hB
      subst hA'
      subst hB'
      rfl
  | .letE A1 v1 b1, .letE A2 v2 b2, h => by
      simp only [lift] at h
      injection h with hA hv hb
      have hA' := lift_inj c A1 A2 hA
      have hv' := lift_inj c v1 v2 hv
      have hb' := lift_inj (c + 1) b1 b2 hb
      subst hA'
      subst hv'
      subst hb'
      rfl
  | .lit _, .lit _, h => by
      simp only [lift] at h
      injection h with ht
      subst ht
      rfl
  | .bvar _, .sort _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .const _ _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .app _ _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .lam _ _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .pi _ _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .letE _ _ _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .bvar _, .lit _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .sort _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .sort _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .sort _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .sort _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .sort _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .sort _, .letE _ _ _, h => by simp only [lift] at h; nomatch h
  | .sort _, .lit _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .const _ _, .sort _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .letE _ _ _, h => by simp only [lift] at h; nomatch h
  | .const _ _, .lit _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .app _ _, .sort _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .letE _ _ _, h => by simp only [lift] at h; nomatch h
  | .app _ _, .lit _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .lam _ _, .sort _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .letE _ _ _, h => by simp only [lift] at h; nomatch h
  | .lam _ _, .lit _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .pi _ _, .sort _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .letE _ _ _, h => by simp only [lift] at h; nomatch h
  | .pi _ _, .lit _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .letE _ _ _, .sort _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .letE _ _ _, .lit _, h => by simp only [lift] at h; nomatch h
  | .lit _, .bvar _, h => by simp only [lift] at h; split at h <;> nomatch h
  | .lit _, .sort _, h => by simp only [lift] at h; nomatch h
  | .lit _, .const _ _, h => by simp only [lift] at h; nomatch h
  | .lit _, .app _ _, h => by simp only [lift] at h; nomatch h
  | .lit _, .lam _ _, h => by simp only [lift] at h; nomatch h
  | .lit _, .pi _ _, h => by simp only [lift] at h; nomatch h
  | .lit _, .letE _ _ _, h => by simp only [lift] at h; nomatch h

theorem foldApps_instantiate (j : Nat) (v : Expr Nat) (f : Expr Nat)
    (xs : List (Expr Nat)) :
    instantiate j v (foldApps f xs) =
      foldApps (instantiate j v f) (xs.map (instantiate j v)) := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps, List.map_nil]
  | cons x xs ih =>
      simp only [foldApps, List.map_cons, instantiate]
      exact ih (.app f x)

theorem foldApps_snoc (f x : Expr Nat) (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) = .app (foldApps f ys) x := by
  induction ys generalizing f with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.cons_append, foldApps]
      exact ih (.app f y)

theorem foldApps_append (f : Expr Nat) (xs ys : List (Expr Nat)) :
    foldApps f (xs ++ ys) = foldApps (foldApps f xs) ys := by
  induction xs generalizing f with
  | nil =>
      simp only [List.nil_append, foldApps]
  | cons x xs ih =>
      simp only [List.cons_append, foldApps]
      exact ih (.app f x)

theorem appsSpine_lift (c a : Nat) :
    (e : Expr Nat) →
    appsSpine (lift c a e) =
      (lift c a (appsSpine e).1, (appsSpine e).2.map (lift c a))
  | .app f x => by
      simp only [lift, appsSpine]
      have ih := appsSpine_lift c a f
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil]
  | .bvar i => by
      simp only [lift, appsSpine, List.map_nil]
      split <;> rfl
  | .sort _ => by simp only [lift, appsSpine, List.map_nil]
  | .const _ _ => by simp only [lift, appsSpine, List.map_nil]
  | .lam _ _ => by simp only [lift, appsSpine, List.map_nil]
  | .pi _ _ => by simp only [lift, appsSpine, List.map_nil]
  | .letE _ _ _ => by simp only [lift, appsSpine, List.map_nil]
  | .lit _ => by simp only [lift, appsSpine, List.map_nil]

/-- Instantiate preserves a const-headed spine (the 05 family-app shape).
A bvar-hit can replace the head, so this is gated on `const`. -/
theorem appsSpine_instantiate_const (j : Nat) (v : Expr Nat)
    (r : Nat) (ls : List Level) :
    (e : Expr Nat) →
    (appsSpine e).1 = .const r ls →
    appsSpine (instantiate j v e) =
      (.const r ls, (appsSpine e).2.map (instantiate j v))
  | .app f x, h => by
      simp only [appsSpine] at h
      simp only [instantiate, appsSpine]
      have ih := appsSpine_instantiate_const j v r ls f h
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil]
  | .const r' ls', h => by
      simp only [appsSpine] at h
      injection h with hr hls
      subst hr
      subst hls
      simp only [instantiate, appsSpine, List.map_nil]
  | .bvar _, h => by simp only [appsSpine] at h; nomatch h
  | .sort _, h => by simp only [appsSpine] at h; nomatch h
  | .lam _ _, h => by simp only [appsSpine] at h; nomatch h
  | .pi _ _, h => by simp only [appsSpine] at h; nomatch h
  | .letE _ _ _, h => by simp only [appsSpine] at h; nomatch h
  | .lit _, h => by simp only [appsSpine] at h; nomatch h

theorem familyIdx_lift (c a nparams : Nat) (A : Expr Nat) :
    familyIdx nparams (lift c a A) =
      (familyIdx nparams A).map (lift c a) := by
  simp only [familyIdx]
  rw [appsSpine_lift]
  exact (List.map_drop (lift c a) (appsSpine A).2 nparams).symm

theorem familyIdx_instantiate_const (j : Nat) (v : Expr Nat)
    (nparams : Nat) {r : Nat} {ls : List Level} {A : Expr Nat}
    (h : (appsSpine A).1 = .const r ls) :
    familyIdx nparams (instantiate j v A) =
      (familyIdx nparams A).map (instantiate j v) := by
  simp only [familyIdx]
  rw [appsSpine_instantiate_const j v r ls A h]
  exact (List.map_drop (instantiate j v) (appsSpine A).2 nparams).symm

theorem recPrefix_lift (c : Nat) (pre : List (Expr Nat))
    (nparams nMinors : Nat) :
    recPrefix (pre.map (lift c 1)) nparams nMinors =
      (recPrefix pre nparams nMinors).map (lift c 1) :=
  (List.map_take (lift c 1) pre (nparams + 1 + nMinors)).symm

theorem recPrefix_instantiate (j : Nat) (v : Expr Nat)
    (pre : List (Expr Nat)) (nparams nMinors : Nat) :
    recPrefix (pre.map (instantiate j v)) nparams nMinors =
      (recPrefix pre nparams nMinors).map (instantiate j v) :=
  (List.map_take (instantiate j v) pre (nparams + 1 + nMinors)).symm

theorem recCallField_lift (c : Nat) (rec : Expr Nat)
    (pre : List (Expr Nat)) (nparams nMinors : Nat) (f A : Expr Nat) :
    lift c 1 (recCallField rec pre nparams nMinors f A) =
      recCallField (lift c 1 rec) (pre.map (lift c 1)) nparams nMinors
        (lift c 1 f) (lift c 1 A) := by
  simp only [recCallField, foldApps_lift, List.map_append, List.map_cons,
    List.map_nil, recPrefix_lift, familyIdx_lift]

theorem recCallField_instantiate (j : Nat) (s rec : Expr Nat)
    (pre : List (Expr Nat)) (nparams nMinors : Nat) (f A : Expr Nat)
    (hsc : spineHeadConst A = true) :
    instantiate j s (recCallField rec pre nparams nMinors f A) =
      recCallField (instantiate j s rec) (pre.map (instantiate j s))
        nparams nMinors (instantiate j s f) (instantiate j s A) := by
  simp only [recCallField, foldApps_instantiate, List.map_append,
    List.map_cons, List.map_nil, recPrefix_instantiate]
  have hidx : (familyIdx nparams A).map (instantiate j s) =
      familyIdx nparams (instantiate j s A) := by
    simp only [spineHeadConst] at hsc
    cases hsp : (appsSpine A).1 with
    | const r ls =>
        exact (familyIdx_instantiate_const j s nparams (by rw [hsp])).symm
    | bvar _ => simp only [hsp] at hsc; nomatch hsc
    | sort _ => simp only [hsp] at hsc; nomatch hsc
    | app _ _ => simp only [hsp] at hsc; nomatch hsc
    | lam _ _ => simp only [hsp] at hsc; nomatch hsc
    | pi _ _ => simp only [hsp] at hsc; nomatch hsc
    | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
    | lit _ => simp only [hsp] at hsc; nomatch hsc
  rw [hidx]

/-- A term with no free bvar ≥ k is unchanged by any lift at cutoff ≥ k. -/
theorem lift_closed_gen (e : Expr Nat) (k : Nat) (h : lift k 1 e = e)
    (c a : Nat) (hc : k ≤ c) : lift c a e = e := by
  induction e generalizing k c a with
  | bvar i =>
      simp only [lift] at h
      split at h
      · injection h with hi
        exact (Nat.ne_of_gt (Nat.lt_succ_self i) hi).elim
      · simp only [lift]
        split
        · have : i < k := by omega
          exact (Nat.not_lt_of_ge (by omega : i ≥ c) (Nat.lt_of_lt_of_le this hc)).elim
        · rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx =>
      simp only [lift] at h
      injection h with hf hx
      simp only [lift, ihf k hf c a hc, ihx k hx c a hc]
  | lam A b ihA ihb =>
      simp only [lift] at h
      injection h with hA hb
      simp only [lift, ihA k hA c a hc, ihb (k+1) hb (c+1) a (Nat.succ_le_succ hc)]
  | pi A b ihA ihb =>
      simp only [lift] at h
      injection h with hA hb
      simp only [lift, ihA k hA c a hc, ihb (k+1) hb (c+1) a (Nat.succ_le_succ hc)]
  | letE A v b ihA ihv ihb =>
      simp only [lift] at h
      injection h with hA hv hb
      simp only [lift, ihA k hA c a hc, ihv k hv c a hc,
        ihb (k+1) hb (c+1) a (Nat.succ_le_succ hc)]
  | lit _ => rfl

theorem lift_of_closed (e : Expr Nat) (h : lift 0 1 e = e) (c a : Nat) :
    lift c a e = e :=
  lift_closed_gen e 0 h c a (Nat.zero_le c)

theorem instantiate_closed_gen (e : Expr Nat) (k : Nat) (h : lift k 1 e = e)
    (j : Nat) (hj : k ≤ j) (s : Expr Nat) : instantiate j s e = e := by
  induction e generalizing k j s with
  | bvar i =>
      simp only [lift] at h
      split at h
      · injection h with hi
        exact (Nat.ne_of_gt (Nat.lt_succ_self i) hi).elim
      · simp only [instantiate]
        have hik : i < k := by omega
        have hne : ¬ i = j := by omega
        have hnlt : ¬ j < i := by omega
        rw [if_neg hne, if_neg hnlt]
  | sort _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx =>
      simp only [lift] at h
      injection h with hf hx
      simp only [instantiate, ihf k hf j hj, ihx k hx j hj]
  | lam A b ihA ihb =>
      simp only [lift] at h
      injection h with hA hb
      simp only [instantiate, ihA k hA j hj,
        ihb (k+1) hb (j+1) (Nat.succ_le_succ hj)]
  | pi A b ihA ihb =>
      simp only [lift] at h
      injection h with hA hb
      simp only [instantiate, ihA k hA j hj,
        ihb (k+1) hb (j+1) (Nat.succ_le_succ hj)]
  | letE A v b ihA ihv ihb =>
      simp only [lift] at h
      injection h with hA hv hb
      simp only [instantiate, ihA k hA j hj, ihv k hv j hj,
        ihb (k+1) hb (j+1) (Nat.succ_le_succ hj)]
  | lit _ => rfl

theorem instantiate_of_closed (e : Expr Nat) (h : lift 0 1 e = e)
    (j : Nat) (s : Expr Nat) : instantiate j s e = e :=
  instantiate_closed_gen e 0 h j (Nat.zero_le j) s

/-- 00 §20.6: a STORED-TYPE VIEW inherits the stored type's closedness,
because `instantiateLevels` neither reads nor writes a `bvar`. This is
the single fact every `_lift` / `_instantiate` transport of a witness
field needs after the views land: the transport's shape is unchanged,
only the closedness it feeds moves from the raw type to its view. -/
theorem instantiateLevels_closed0 {e : Expr Nat} (h : lift 0 1 e = e)
    (ls : List Level) :
    lift 0 1 (instantiateLevels ls e) = instantiateLevels ls e :=
  instantiateLevels_closed (fun c => lift_of_closed e h c 1) ls 0

def applyTel_congr_lift (c amt : Nat) :
    (xs : List (Expr Nat)) → {T U : Expr Nat} →
    applyTel xs T = some U →
    applyTel (xs.map (lift c amt)) (lift c amt T) = some (lift c amt U)
  | [], T, U, h => by
      simp only [applyTel, List.map_nil] at h ⊢
      injection h with hU
      subst hU
      rfl
  | x :: xs, T, U, h => by
      have ⟨A, B, hT, hrest⟩ := applyTel_cons_inv x xs h
      subst hT
      simp only [List.map_cons, lift, applyTel]
      have hinst :
          instantiate0 (lift c amt x) (lift (c + 1) amt B) =
            lift c amt (instantiate0 x B) := by
        simp only [instantiate0]
        exact (lift_instantiate_low amt c 0 x (Nat.zero_le c) B).symm
      rw [hinst]
      exact applyTel_congr_lift c amt xs hrest

def applyTel_congr_instantiate (j : Nat) (v : Expr Nat) :
    (xs : List (Expr Nat)) → {T U : Expr Nat} →
    applyTel xs T = some U →
    applyTel (xs.map (instantiate j v)) (instantiate j v T) =
      some (instantiate j v U)
  | [], T, U, h => by
      simp only [applyTel, List.map_nil] at h ⊢
      injection h with hU
      subst hU
      rfl
  | x :: xs, T, U, h => by
      have ⟨A, B, hT, hrest⟩ := applyTel_cons_inv x xs h
      subst hT
      simp only [List.map_cons, instantiate, applyTel]
      have hinst :
          instantiate0 (instantiate j v x)
              (instantiate (j + 1) (lift 0 1 v) B) =
            instantiate j v (instantiate0 x B) := by
        simp only [instantiate0]
        exact (instantiate_instantiate 0 j x v (Nat.zero_le j) B).symm
      rw [hinst]
      exact applyTel_congr_instantiate j v xs hrest

theorem isPiTel_zero (T : Expr Nat) : isPiTel 0 T = true := rfl

theorem bool_and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b
  · cases h
  · cases h
  · cases h
  · exact ⟨rfl, rfl⟩

def listFindIdx {α} [DecidableEq α] (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (listFindIdx x ys).map (· + 1)

theorem listFindIdx_get {α} [DecidableEq α] {x : α} {xs : List α} {i : Nat}
    (h : listFindIdx x xs = some i) : xs[i]? = some x := by
  induction xs generalizing i with
  | nil =>
      simp only [listFindIdx] at h
      exact Option.noConfusion h
  | cons y ys ih =>
      simp only [listFindIdx] at h
      split at h
      · rename_i heq
        injection h with hi
        subst hi
        subst heq
        simp only [List.getElem?_cons_zero]
      · cases hmap : listFindIdx x ys with
        | none =>
            simp only [hmap, Option.map_none'] at h
            exact Option.noConfusion h
        | some j =>
            simp only [hmap, Option.map_some'] at h
            injection h with hi
            subst hi
            have := ih hmap
            simp only [List.getElem?_cons_succ]
            exact this

theorem listFindIdx_isSome {α} [DecidableEq α] (x : α) :
    (xs : List α) → decide (x ∈ xs) = true →
    (listFindIdx x xs).isSome = true
  | [], h => by
      have hx : x ∈ [] := of_decide_eq_true h
      cases hx
  | y :: ys, h => by
      simp only [listFindIdx]
      split
      · rfl
      · rename_i hne
        have hmem : x ∈ y :: ys := of_decide_eq_true h
        have hys : x ∈ ys := by
          have hor := (List.mem_cons (a := x) (b := y) (l := ys)).mp hmem
          cases hor with
          | inl heq => exact (hne heq).elim
          | inr ht => exact ht
        have hdec : decide (x ∈ ys) = true := decide_eq_true hys
        have ih := listFindIdx_isSome x ys hdec
        cases hfi : listFindIdx x ys with
        | none =>
            simp only [hfi, Option.isSome] at ih
            nomatch ih
        | some _ =>
            simp only [hfi, Option.map_some', Option.isSome]

def memFindIdx {α} [DecidableEq α] (x : α) (xs : List α)
    (h : decide (x ∈ xs) = true) :
    Σ' (i : Nat), xs[i]? = some x :=
  match hfi : listFindIdx x xs with
  | some i => ⟨i, listFindIdx_get hfi⟩
  | none =>
      have hs := listFindIdx_isSome x xs h
      by
        simp only [hfi, Option.isSome] at hs
        nomatch hs

theorem all_mem_map (f : Expr Nat → Expr Nat) :
    (xs ys : List (Expr Nat)) →
    xs.all (fun x => decide (x ∈ ys)) = true →
    (xs.map f).all (fun y => decide (y ∈ ys.map f)) = true
  | [], _, _ => rfl
  | x :: xs, ys, h => by
      simp only [List.all_cons, List.map_cons] at h ⊢
      have ⟨hx, hxs⟩ := bool_and_true h
      have hxmem : x ∈ ys := of_decide_eq_true hx
      have hx' : decide (f x ∈ ys.map f) = true :=
        decide_eq_true (List.mem_map_of_mem f hxmem)
      have hxs' := all_mem_map f xs ys hxs
      simp only [hx', hxs']
      rfl

theorem isPiTel_lift (c a : Nat) :
    (n : Nat) → (T : Expr Nat) →
    isPiTel n T = true → isPiTel n (lift c a T) = true
  | 0, T, _ => rfl
  | n + 1, .pi A B, h => by
      simp only [isPiTel, lift] at h ⊢
      exact isPiTel_lift (c + 1) a n B h
  | n + 1, .bvar _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .sort _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .const _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .app _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lam _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .letE _ _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lit _, h => by simp only [isPiTel] at h; nomatch h

theorem isPiTel_instantiate (j : Nat) (v : Expr Nat) :
    (n : Nat) → (T : Expr Nat) →
    isPiTel n T = true → isPiTel n (instantiate j v T) = true
  | 0, T, _ => rfl
  | n + 1, .pi A B, h => by
      simp only [isPiTel, instantiate] at h ⊢
      exact isPiTel_instantiate (j + 1) (lift 0 1 v) n B h
  | n + 1, .bvar _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .sort _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .const _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .app _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lam _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .letE _ _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lit _, h => by simp only [isPiTel] at h; nomatch h

theorem spineHeadConst_lift (c a : Nat) (A : Expr Nat)
    (h : spineHeadConst A = true) :
    spineHeadConst (lift c a A) = true := by
  simp only [spineHeadConst] at h ⊢
  cases hsp : (appsSpine A).1 with
  | const r ls =>
      have hlift := appsSpine_lift c a A
      rw [hlift, hsp]
      simp only [lift]
  | bvar _ => simp only [hsp] at h; nomatch h
  | sort _ => simp only [hsp] at h; nomatch h
  | app _ _ => simp only [hsp] at h; nomatch h
  | lam _ _ => simp only [hsp] at h; nomatch h
  | pi _ _ => simp only [hsp] at h; nomatch h
  | letE _ _ _ => simp only [hsp] at h; nomatch h
  | lit _ => simp only [hsp] at h; nomatch h

theorem spineHeadConst_instantiate (j : Nat) (v : Expr Nat) (A : Expr Nat)
    (h : spineHeadConst A = true) :
    spineHeadConst (instantiate j v A) = true := by
  simp only [spineHeadConst] at h ⊢
  cases hsp : (appsSpine A).1 with
  | const r ls =>
      have happs := appsSpine_instantiate_const j v r ls A (by rw [hsp])
      rw [happs]
  | bvar _ => simp only [hsp] at h; nomatch h
  | sort _ => simp only [hsp] at h; nomatch h
  | app _ _ => simp only [hsp] at h; nomatch h
  | lam _ _ => simp only [hsp] at h; nomatch h
  | pi _ _ => simp only [hsp] at h; nomatch h
  | letE _ _ _ => simp only [hsp] at h; nomatch h
  | lit _ => simp only [hsp] at h; nomatch h

theorem directRecConstHead_lift (c a : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    directRecConstHead ks T = true →
    directRecConstHead ks (lift c a T) = true
  | [], _, _ => rfl
  | .plain :: ks, .pi A B, h => by
      simp only [directRecConstHead, lift] at h ⊢
      exact directRecConstHead_lift (c + 1) a ks B h
  | .directRec :: ks, .pi A B, h => by
      simp only [directRecConstHead, lift] at h ⊢
      have ⟨hA, hB⟩ := bool_and_true h
      have hA' := spineHeadConst_lift c a A hA
      have hB' := directRecConstHead_lift (c + 1) a ks B hB
      simp only [hA', hB']
      rfl
  | .plain :: ks, .bvar _, _ => by
      simp only [directRecConstHead, lift]; split <;> rfl
  | .plain :: ks, .sort _, _ => rfl
  | .plain :: ks, .const _ _, _ => rfl
  | .plain :: ks, .app _ _, _ => rfl
  | .plain :: ks, .lam _ _, _ => rfl
  | .plain :: ks, .letE _ _ _, _ => rfl
  | .plain :: ks, .lit _, _ => rfl
  | .directRec :: ks, .bvar _, _ => by
      simp only [directRecConstHead, lift]; split <;> rfl
  | .directRec :: ks, .sort _, _ => rfl
  | .directRec :: ks, .const _ _, _ => rfl
  | .directRec :: ks, .app _ _, _ => rfl
  | .directRec :: ks, .lam _ _, _ => rfl
  | .directRec :: ks, .letE _ _ _, _ => rfl
  | .directRec :: ks, .lit _, _ => rfl

/-- Instantiating a bvar into a Π can change `directRecConstHead`'s
catch-all; the `isPiTel` gate keeps the telescope a Π (M-001). -/
theorem directRecConstHead_instantiate (j : Nat) (v : Expr Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    directRecConstHead ks (instantiate j v T) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, htel, h => by
      simp only [isPiTel, List.length_cons, directRecConstHead, instantiate]
        at htel h ⊢
      exact directRecConstHead_instantiate (j + 1) (lift 0 1 v) ks B htel h
  | .directRec :: ks, .pi A B, htel, h => by
      simp only [isPiTel, List.length_cons, directRecConstHead, instantiate]
        at htel h ⊢
      have ⟨hA, hB⟩ := bool_and_true h
      have hA' := spineHeadConst_instantiate j v A hA
      have hB' :=
        directRecConstHead_instantiate (j + 1) (lift 0 1 v) ks B htel hB
      simp only [hA', hB']
      rfl
  | .plain :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

/-- `resultConstHead` transports across `lift`. Sibling of
`directRecConstHead_lift`: same walk, `spineHeadConst_lift` at the
base instead of `rfl` (the base is no longer vacuously `true`). -/
theorem resultConstHead_lift (c a : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    resultConstHead ks T = true →
    resultConstHead ks (lift c a T) = true
  | [], T, h => spineHeadConst_lift c a T h
  | .plain :: ks, .pi A B, h => by
      simp only [resultConstHead, lift] at h ⊢
      exact resultConstHead_lift (c + 1) a ks B h
  | .directRec :: ks, .pi A B, h => by
      simp only [resultConstHead, lift] at h ⊢
      exact resultConstHead_lift (c + 1) a ks B h
  | .plain :: _, .bvar _, h => by nomatch h
  | .plain :: _, .sort l, h => spineHeadConst_lift c a (.sort l) h
  | .plain :: _, .const r ls, h => spineHeadConst_lift c a (.const r ls) h
  | .plain :: _, .app f x, h => spineHeadConst_lift c a (.app f x) h
  | .plain :: _, .lam A B, h => spineHeadConst_lift c a (.lam A B) h
  | .plain :: _, .letE A v B, h => spineHeadConst_lift c a (.letE A v B) h
  | .plain :: _, .lit t, h => spineHeadConst_lift c a (.lit t) h
  | .directRec :: _, .bvar _, h => by nomatch h
  | .directRec :: _, .sort l, h => spineHeadConst_lift c a (.sort l) h
  | .directRec :: _, .const r ls, h => spineHeadConst_lift c a (.const r ls) h
  | .directRec :: _, .app f x, h => spineHeadConst_lift c a (.app f x) h
  | .directRec :: _, .lam A B, h => spineHeadConst_lift c a (.lam A B) h
  | .directRec :: _, .letE A v B, h =>
      spineHeadConst_lift c a (.letE A v B) h
  | .directRec :: _, .lit t, h => spineHeadConst_lift c a (.lit t) h

/-- Instantiating a bvar into a Π can change `resultConstHead`'s
catch-all; the `isPiTel` gate keeps the telescope a Π (M-001).
Sibling of `directRecConstHead_instantiate`. -/
theorem resultConstHead_instantiate (j : Nat) (v : Expr Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    resultConstHead ks T = true →
    resultConstHead ks (instantiate j v T) = true
  | [], T, _, h => spineHeadConst_instantiate j v T h
  | .plain :: ks, .pi A B, htel, h => by
      simp only [isPiTel, List.length_cons, resultConstHead, instantiate]
        at htel h ⊢
      exact resultConstHead_instantiate (j + 1) (lift 0 1 v) ks B htel h
  | .directRec :: ks, .pi A B, htel, h => by
      simp only [isPiTel, List.length_cons, resultConstHead, instantiate]
        at htel h ⊢
      exact resultConstHead_instantiate (j + 1) (lift 0 1 v) ks B htel h
  | .plain :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

theorem kinds_all_plain_nil : kinds_all_plain ([] : List RecKind) = true := rfl

/-- All-plain telescopes have no DirectRec domains. -/
theorem directRecConstHead_of_plain :
    (ks : List RecKind) → (T : Expr Nat) →
    kinds_all_plain ks = true →
    directRecConstHead ks T = true
  | [], _, _ => rfl
  | .plain :: ks, .pi _ B, h => by
      simp only [kinds_all_plain, directRecConstHead] at h ⊢
      exact directRecConstHead_of_plain ks B h
  | .plain :: ks, .bvar _, h => by simp only [directRecConstHead]
  | .plain :: ks, .sort _, h => by simp only [directRecConstHead]
  | .plain :: ks, .const _ _, h => by simp only [directRecConstHead]
  | .plain :: ks, .app _ _, h => by simp only [directRecConstHead]
  | .plain :: ks, .lam _ _, h => by simp only [directRecConstHead]
  | .plain :: ks, .letE _ _ _, h => by simp only [directRecConstHead]
  | .plain :: ks, .lit _, h => by simp only [directRecConstHead]
  | .directRec :: _, _, h => by
      simp only [kinds_all_plain] at h; nomatch h

def applyTel_isPiTel :
    (n : Nat) → (T : Expr Nat) → (xs : List (Expr Nat)) →
    xs.length = n → isPiTel n T = true →
    Σ' (U : Expr Nat), applyTel xs T = some U
  | 0, T, xs, hlen, _ => by
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hx
      exact ⟨T, rfl⟩
  | n + 1, T, xs, hlen, htel => by
      match xs, T with
      | x :: xs, .pi _ B =>
          have hlen' : xs.length = n := by
            simp only [List.length_cons] at hlen
            exact Nat.succ.inj hlen
          simp only [isPiTel, List.length_cons] at htel
          have htel' := isPiTel_instantiate 0 x n B htel
          let ⟨U, hU⟩ := applyTel_isPiTel n (instantiate0 x B) xs hlen' htel'
          exact ⟨U, hU⟩
      | [], _ =>
          simp only [List.length_nil] at hlen
          cases hlen
      | _ :: _, .bvar _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .sort _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .const _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .app _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .lam _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .letE _ _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .lit _ => simp only [isPiTel] at htel; nomatch htel

/-- Applying `n` arguments to a Π-telescope of length `n+1` leaves a Π. -/
def applyTel_drop1_pi :
    (n : Nat) → (T : Expr Nat) → (xs : List (Expr Nat)) →
    xs.length = n → isPiTel (n + 1) T = true →
    {U : Expr Nat} → applyTel xs T = some U →
    Σ' (A B : Expr Nat), U = Expr.pi A B
  | 0, T, xs, hlen, htel, U, happ => by
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hx
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      match T with
      | .pi A B => exact ⟨A, B, rfl⟩
      | .bvar _ => simp only [isPiTel] at htel; nomatch htel
      | .sort _ => simp only [isPiTel] at htel; nomatch htel
      | .const _ _ => simp only [isPiTel] at htel; nomatch htel
      | .app _ _ => simp only [isPiTel] at htel; nomatch htel
      | .lam _ _ => simp only [isPiTel] at htel; nomatch htel
      | .letE _ _ _ => simp only [isPiTel] at htel; nomatch htel
      | .lit _ => simp only [isPiTel] at htel; nomatch htel
  | n + 1, T, xs, hlen, htel, U, happ => by
      match xs, T with
      | x :: xs, .pi _ B =>
          have hlen' : xs.length = n := by
            simp only [List.length_cons] at hlen
            exact Nat.succ.inj hlen
          simp only [isPiTel, List.length_cons] at htel
          have htel' := isPiTel_instantiate 0 x (n + 1) B htel
          have ⟨A, B', hU⟩ :=
            applyTel_drop1_pi n (instantiate0 x B) xs hlen' htel' happ
          exact ⟨A, B', hU⟩
      | [], _ =>
          simp only [List.length_nil] at hlen
          cases hlen
      | _ :: _, .bvar _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .sort _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .const _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .app _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .lam _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .letE _ _ _ => simp only [isPiTel] at htel; nomatch htel
      | _ :: _, .lit _ => simp only [isPiTel] at htel; nomatch htel

/-- Zero-index families: `familyIdx` is `[]`, equal to the major-index spine. -/
theorem familyIdx_eq_majors_of_zero {E : ResolvedEnv} (w : IotaWitness E)
    {A : Expr Nat}
    (hn : w.nindices = 0)
    (hlen : (familyIdx w.nparams A).length = w.nindices) :
    familyIdx w.nparams A =
      w.preMajor.drop (w.nparams + 1 + w.nMinors) := by
  have hf : familyIdx w.nparams A = [] :=
    List.eq_nil_of_length_eq_zero (hlen.trans hn)
  have hdrop : (w.preMajor.drop (w.nparams + 1 + w.nMinors)).length = 0 := by
    simp only [List.length_drop]
    have := w.hpre
    omega
  have hm : w.preMajor.drop (w.nparams + 1 + w.nMinors) = [] :=
    List.eq_nil_of_length_eq_zero hdrop
  rw [hf, hm]

theorem applyTel_snoc (x : Expr Nat) :
    (xs : List (Expr Nat)) → (T : Expr Nat) → {A B : Expr Nat} →
    applyTel xs T = some (.pi A B) →
    applyTel (xs ++ [x]) T = some (instantiate0 x B)
  | [], T, A, B, h => by
      simp only [applyTel, List.nil_append] at h ⊢
      injection h with hT
      subst hT
      rfl
  | y :: ys, T, A, B, h => by
      have ⟨A0, B0, hT, hrest⟩ := applyTel_cons_inv y ys h
      subst hT
      simp only [List.cons_append, applyTel]
      exact applyTel_snoc x ys (instantiate0 y B0) hrest

theorem isPiTel_mono :
    (n : Nat) → (T : Expr Nat) →
    isPiTel (n + 1) T = true → isPiTel n T = true
  | 0, _, _ => rfl
  | n + 1, .pi _ B, h => by
      simp only [isPiTel] at h ⊢
      exact isPiTel_mono n B h
  | n + 1, .bvar _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .sort _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .const _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .app _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lam _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .letE _ _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lit _, h => by simp only [isPiTel] at h; nomatch h

theorem isPiTel_le {n k : Nat} {T : Expr Nat} (h : n ≤ k) :
    isPiTel k T = true → isPiTel n T = true := by
  induction h with
  | refl => intro ht; exact ht
  | step h ih =>
      intro ht
      exact ih (isPiTel_mono _ T ht)

theorem isPiTel_of_applyTel :
    (n k : Nat) → (T : Expr Nat) → (xs : List (Expr Nat)) →
    xs.length = n → isPiTel (n + k) T = true →
    {U : Expr Nat} → applyTel xs T = some U → isPiTel k U = true
  | 0, k, T, xs, hlen, htel, U, h => by
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hx
      simp only [applyTel] at h
      injection h with hU
      subst hU
      have hk : 0 + k = k := Nat.zero_add k
      rw [hk] at htel
      exact htel
  | n + 1, k, T, xs, hlen, htel, U, h => by
      match xs with
      | [] =>
          simp only [List.length_nil] at hlen
          cases hlen
      | x :: xs' =>
          have ⟨A, B, hT, hrest⟩ := applyTel_cons_inv x xs' h
          subst hT
          simp only [List.length_cons] at hlen
          have hlen' : xs'.length = n := Nat.succ.inj hlen
          have hsum : n + 1 + k = n + k + 1 := by omega
          rw [hsum] at htel
          simp only [isPiTel] at htel
          have htel' := isPiTel_instantiate 0 x (n + k) B htel
          exact isPiTel_of_applyTel n k (instantiate0 x B) xs' hlen'
            htel' hrest

/-- Split `applyTel` along `xs ++ ys`. -/
def applyTel_append_split :
    (xs ys : List (Expr Nat)) → {T U : Expr Nat} →
    applyTel (xs ++ ys) T = some U →
    Σ' (T' : Expr Nat),
      (applyTel xs T = some T') ×' (applyTel ys T' = some U)
  | [], ys, T, U, h => ⟨T, rfl, h⟩
  | x :: xs, ys, T, U, h => by
      simp only [List.cons_append] at h
      have ⟨A, B, hT, hrest⟩ := applyTel_cons_inv x (xs ++ ys) h
      subst hT
      simp only [applyTel] at h
      have ⟨T', hxs, hys⟩ := applyTel_append_split xs ys h
      exact ⟨T', hxs, hys⟩

def applyTel_append_of :
    (xs ys : List (Expr Nat)) → {T T' U : Expr Nat} →
    applyTel xs T = some T' → applyTel ys T' = some U →
    applyTel (xs ++ ys) T = some U
  | [], ys, T, T', U, hxs, hys => by
      simp only [applyTel, List.nil_append] at hxs ⊢
      injection hxs with hT
      subst hT
      exact hys
  | x :: xs, ys, T, T', U, hxs, hys => by
      have ⟨A, B, hT, hrest⟩ := applyTel_cons_inv x xs hxs
      subst hT
      simp only [List.cons_append, applyTel]
      exact applyTel_append_of xs ys hrest hys

theorem lift_bvar_lt {R} (c a i : Nat) (h : i < c) :
    lift c a (Expr.bvar i : Expr R) = .bvar i := by
  simp only [lift]
  split
  · omega
  · rfl

theorem minorTel_lift_tel (c nparams : Nat) (M ctorAcc : Expr Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    lift c 1 (minorTel M nparams ctorAcc ks T) =
      minorTel (lift c 1 M) nparams (lift c 1 ctorAcc) ks (lift c 1 T)
  | [], T, _ => by
      simp only [minorTel, lift, foldApps_lift, familyIdx_lift]
  | .plain :: ks, T, htel => by
      cases T with
      | pi A B =>
          have hM : lift (c + 1) 1 (lift 0 1 M) = lift 0 1 (lift c 1 M) := by
            have h := lift_lift_permute 1 1 c 0 (Nat.zero_le c) M
            simp only [Nat.add_comm 1 c] at h
            exact h.symm
          have hC : lift (c + 1) 1 (lift 0 1 ctorAcc) =
              lift 0 1 (lift c 1 ctorAcc) := by
            have h := lift_lift_permute 1 1 c 0 (Nat.zero_le c) ctorAcc
            simp only [Nat.add_comm 1 c] at h
            exact h.symm
          simp only [isPiTel, List.length_cons] at htel
          simp only [minorTel, lift]
          apply congrArg (Expr.pi (lift c 1 A))
          rw [minorTel_lift_tel (c + 1) nparams (lift 0 1 M)
            (.app (lift 0 1 ctorAcc) (.bvar 0)) ks B htel]
          simp only [lift, hM, hC, if_neg (Nat.not_succ_le_zero c)]
      | bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, T, htel => by
      cases T with
      | pi A B =>
          have hC2 : lift (c + 2) 1 (lift 0 2 ctorAcc) =
              lift 0 2 (lift c 1 ctorAcc) := by
            have h := lift_lift_permute 2 1 c 0 (Nat.zero_le c) ctorAcc
            simp only [Nat.add_comm 2 c] at h
            exact h.symm
          have hM2 : lift (c + 2) 1 (lift 0 2 M) = lift 0 2 (lift c 1 M) := by
            have h := lift_lift_permute 2 1 c 0 (Nat.zero_le c) M
            simp only [Nat.add_comm 2 c] at h
            exact h.symm
          have hF1 : lift (c + 1) 1 (lift 0 1
              (foldApps M (familyIdx nparams A))) =
              lift 0 1 (foldApps (lift c 1 M)
                (familyIdx nparams (lift c 1 A))) := by
            have h := lift_lift_permute 1 1 c 0 (Nat.zero_le c)
              (foldApps M (familyIdx nparams A))
            simp only [Nat.add_comm 1 c] at h
            have hFih : lift c 1 (foldApps M (familyIdx nparams A)) =
                foldApps (lift c 1 M) (familyIdx nparams (lift c 1 A)) := by
              rw [foldApps_lift, familyIdx_lift]
            rw [hFih] at h
            exact h.symm
          have hB : lift (c + 2) 1 (lift 0 1 B) =
              lift 0 1 (lift (c + 1) 1 B) := by
            have h := lift_lift_permute 1 1 (c + 1) 0 (Nat.zero_le (c + 1)) B
            simp only [Nat.add_comm 1 (c + 1)] at h
            exact h.symm
          have htelB : isPiTel ks.length (lift 0 1 B) = true := by
            simp only [isPiTel, List.length_cons] at htel
            exact isPiTel_lift 0 1 ks.length B htel
          simp only [minorTel, lift]
          apply congrArg (Expr.pi (lift c 1 A))
          simp only [if_neg (Nat.not_succ_le_zero c), hF1]
          apply congrArg (fun t =>
            Expr.pi (.app (lift 0 1 (foldApps (lift c 1 M)
              (familyIdx nparams (lift c 1 A)))) (.bvar 0)) t)
          rw [minorTel_lift_tel (c + 2) nparams (lift 0 2 M)
            (.app (lift 0 2 ctorAcc) (.bvar 1)) ks (lift 0 1 B) htelB]
          simp only [lift, hM2, hC2, hB,
            if_neg (show ¬ (c + 2 ≤ 1) by omega)]
      | bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel

theorem inst_bvar_zero_succ (j : Nat) (v : Expr Nat) :
    instantiate (j + 1) (lift 0 1 v) (.bvar 0) = .bvar 0 := by
  simp only [instantiate]
  have hne : ¬ (0 = j + 1) := by omega
  have hnlt : ¬ (j + 1 < 0) := Nat.not_lt_zero _
  rw [if_neg hne, if_neg hnlt]

theorem inst_bvar_one_add2 (j : Nat) (v : Expr Nat) :
    instantiate (j + 2) (lift 0 2 v) (.bvar 1) = .bvar 1 := by
  simp only [instantiate]
  have hne : ¬ (1 = j + 2) := by omega
  have hnlt : ¬ (j + 2 < 1) := by omega
  rw [if_neg hne, if_neg hnlt]

theorem minorTel_instantiate_tel (j : Nat) (v : Expr Nat)
    (M ctorAcc : Expr Nat) (nparams : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    resultConstHead ks T = true →
    instantiate j v (minorTel M nparams ctorAcc ks T) =
      minorTel (instantiate j v M) nparams (instantiate j v ctorAcc) ks
        (instantiate j v T)
  | [], T, _, _, hres => by
      have hidx : (familyIdx nparams T).map (instantiate j v) =
          familyIdx nparams (instantiate j v T) := by
        simp only [resultConstHead, spineHeadConst] at hres
        cases hsp : (appsSpine T).1 with
        | const r ls =>
            exact (familyIdx_instantiate_const j v nparams (by rw [hsp])).symm
        | bvar _ => simp only [hsp] at hres; nomatch hres
        | sort _ => simp only [hsp] at hres; nomatch hres
        | app _ _ => simp only [hsp] at hres; nomatch hres
        | lam _ _ => simp only [hsp] at hres; nomatch hres
        | pi _ _ => simp only [hsp] at hres; nomatch hres
        | letE _ _ _ => simp only [hsp] at hres; nomatch hres
        | lit _ => simp only [hsp] at hres; nomatch hres
      simp only [minorTel, instantiate, foldApps_instantiate, hidx]
  | .plain :: ks, T, htel, hfam, hres => by
      cases T with
      | pi A B =>
          have hM : instantiate (j + 1) (lift 0 1 v) (lift 0 1 M) =
              lift 0 1 (instantiate j v M) := by
            have h := lift_instantiate_high 1 0 j v (Nat.zero_le j) M
            simp only [Nat.add_comm 1 j] at h
            exact h.symm
          have hC : instantiate (j + 1) (lift 0 1 v) (lift 0 1 ctorAcc) =
              lift 0 1 (instantiate j v ctorAcc) := by
            have h := lift_instantiate_high 1 0 j v (Nat.zero_le j) ctorAcc
            simp only [Nat.add_comm 1 j] at h
            exact h.symm
          simp only [isPiTel, List.length_cons] at htel
          simp only [directRecConstHead] at hfam
          simp only [resultConstHead] at hres
          simp only [minorTel, instantiate]
          apply congrArg (Expr.pi (instantiate j v A))
          rw [minorTel_instantiate_tel (j + 1) (lift 0 1 v)
            (lift 0 1 M)
            (.app (lift 0 1 ctorAcc) (.bvar 0)) nparams ks B htel hfam hres]
          simp only [instantiate, hM, hC,
            if_neg (show ¬ (0 = j + 1) by omega),
            if_neg (Nat.not_lt_zero (j + 1))]
      | bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, T, htel, hfam, hres => by
      cases T with
      | pi A B =>
          have hC2 : instantiate (j + 2) (lift 0 2 v) (lift 0 2 ctorAcc) =
              lift 0 2 (instantiate j v ctorAcc) := by
            have h := lift_instantiate_high 2 0 j v (Nat.zero_le j) ctorAcc
            simp only [Nat.add_comm 2 j] at h
            exact h.symm
          have hM2 : instantiate (j + 2) (lift 0 2 v) (lift 0 2 M) =
              lift 0 2 (instantiate j v M) := by
            have h := lift_instantiate_high 2 0 j v (Nat.zero_le j) M
            simp only [Nat.add_comm 2 j] at h
            exact h.symm
          simp only [directRecConstHead] at hfam
          have ⟨hscA, hfamB⟩ := bool_and_true hfam
          have hFih : instantiate (j + 1) (lift 0 1 v)
              (lift 0 1 (foldApps M (familyIdx nparams A))) =
              lift 0 1 (foldApps (instantiate j v M)
                (familyIdx nparams (instantiate j v A))) := by
            have h := lift_instantiate_high 1 0 j v (Nat.zero_le j)
              (foldApps M (familyIdx nparams A))
            simp only [Nat.add_comm 1 j] at h
            have hidx :
                (familyIdx nparams A).map (instantiate j v) =
                  familyIdx nparams (instantiate j v A) := by
              simp only [spineHeadConst] at hscA
              cases hsp : (appsSpine A).1 with
              | const r ls =>
                  exact (familyIdx_instantiate_const j v nparams
                    (by rw [hsp])).symm
              | bvar _ => simp only [hsp] at hscA; nomatch hscA
              | sort _ => simp only [hsp] at hscA; nomatch hscA
              | app _ _ => simp only [hsp] at hscA; nomatch hscA
              | lam _ _ => simp only [hsp] at hscA; nomatch hscA
              | pi _ _ => simp only [hsp] at hscA; nomatch hscA
              | letE _ _ _ => simp only [hsp] at hscA; nomatch hscA
              | lit _ => simp only [hsp] at hscA; nomatch hscA
            have hFih' :
                instantiate j v (foldApps M (familyIdx nparams A)) =
                  foldApps (instantiate j v M)
                    (familyIdx nparams (instantiate j v A)) := by
              rw [foldApps_instantiate, hidx]
            rw [hFih'] at h
            exact h.symm
          have hB : instantiate (j + 2) (lift 0 2 v) (lift 0 1 B) =
              lift 0 1 (instantiate (j + 1) (lift 0 1 v) B) := by
            have h := lift_instantiate_high 1 0 (j + 1) (lift 0 1 v)
              (Nat.zero_le (j + 1)) B
            simp only [Nat.add_comm 1 (j + 1)] at h
            have hv00 : lift 0 1 (lift 0 1 v) = lift 0 2 v :=
              lift_lift_merge 1 1 0 0 (Nat.le_refl 0) (by omega) v
            rw [hv00] at h
            exact h.symm
          have htelB : isPiTel ks.length (lift 0 1 B) = true := by
            simp only [isPiTel, List.length_cons] at htel
            exact isPiTel_lift 0 1 ks.length B htel
          have hfamB' : directRecConstHead ks (lift 0 1 B) = true :=
            directRecConstHead_lift 0 1 ks B hfamB
          simp only [resultConstHead] at hres
          have hresB' : resultConstHead ks (lift 0 1 B) = true :=
            resultConstHead_lift 0 1 ks B hres
          simp only [minorTel, instantiate]
          apply congrArg (Expr.pi (instantiate j v A))
          simp only [hFih, if_neg (show ¬ (0 = j + 1) by omega),
            if_neg (Nat.not_lt_zero (j + 1))]
          apply congrArg (fun t =>
            Expr.pi (.app (lift 0 1 (foldApps (instantiate j v M)
              (familyIdx nparams (instantiate j v A)))) (.bvar 0)) t)
          have hv00 : lift 0 1 (lift 0 1 v) = lift 0 2 v :=
            lift_lift_merge 1 1 0 0 (Nat.le_refl 0) (by omega) v
          have hj : j + 1 + 1 = j + 2 := by omega
          rw [hj, hv00]
          rw [minorTel_instantiate_tel (j + 2) (lift 0 2 v)
            (lift 0 2 M)
            (.app (lift 0 2 ctorAcc) (.bvar 1)) nparams ks
            (lift 0 1 B) htelB hfamB' hresB']
          simp only [instantiate, hM2, hC2, hB,
            if_neg (show ¬ (1 = j + 2) by omega),
            if_neg (show ¬ (j + 2 < 1) by omega)]
      | bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel

theorem drop_eq_cons_of_get {α} {xs : List α} {k : Nat} {x : α}
    (h : xs[k]? = some x) : xs.drop k = x :: xs.drop (k + 1) := by
  induction k generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp only [List.getElem?_nil] at h
          exact Option.noConfusion h
      | cons y ys =>
          simp only [List.getElem?_cons_zero] at h
          injection h with hy
          subst hy
          simp only [List.drop_zero, List.drop_succ_cons]
  | succ k ih =>
      cases xs with
      | nil =>
          simp only [List.getElem?_nil] at h
          exact Option.noConfusion h
      | cons y ys =>
          simp only [List.getElem?_cons_succ] at h
          simp only [List.drop_succ_cons]
          exact ih h

theorem foldApps_snoc_ne_const {r : Nat} {ls : List Level}
    (f x : Expr Nat) (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) ≠ .const r ls := by
  induction ys generalizing f with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      exact ih (.app f y) h

theorem recCall_lift (c : Nat) (rec : Expr Nat) (preMajor : List (Expr Nat))
    (major : Expr Nat) :
    lift c 1 (recCall rec preMajor major) =
      recCall (lift c 1 rec) (preMajor.map (lift c 1)) (lift c 1 major) := by
  simp only [recCall, foldApps_lift, List.map_append, List.map_cons, List.map_nil]

theorem recCall_instantiate (j : Nat) (v rec : Expr Nat)
    (preMajor : List (Expr Nat)) (major : Expr Nat) :
    instantiate j v (recCall rec preMajor major) =
      recCall (instantiate j v rec) (preMajor.map (instantiate j v))
        (instantiate j v major) := by
  simp only [recCall, foldApps_instantiate, List.map_append, List.map_cons,
    List.map_nil]

theorem instantiate0_lift (c : Nat) (f B : Expr Nat) :
    instantiate0 (lift c 1 f) (lift (c + 1) 1 B) =
      lift c 1 (instantiate0 f B) :=
  (lift_instantiate_low 1 c 0 f (Nat.zero_le c) B).symm

theorem recIdxFromSpineWalk_lift (fam c nparams nindices : Nat)
    (pf : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    recIdxFromSpineWalk fam nparams nindices pf ks T fs = true →
    recIdxFromSpineWalk fam nparams nindices (pf.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, h => by
      simp only [recIdxFromSpineWalk, List.map_cons, lift] at h ⊢
      rw [instantiate0_lift]
      exact recIdxFromSpineWalk_lift fam c nparams nindices pf ks
        (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [recIdxFromSpineWalk, List.map_cons, lift] at h ⊢
      have ⟨hlenall, hrest⟩ := bool_and_true h
      have ⟨hlen, hall⟩ := bool_and_true hlenall
      have hlen' :
          decide ((familyIdx nparams (lift c 1 A)).length = nindices) =
            true := by
        rw [familyIdx_lift, List.length_map]
        exact hlen
      have hall' : (familyIdx nparams (lift c 1 A)).all
          (fun y => idxFamFree fam (pf.map (lift c 1)) y) = true := by
        rw [familyIdx_lift]
        exact all_idxFamFree_map_lift fam c 1 (familyIdx nparams A) pf hall
      have hrest' := recIdxFromSpineWalk_lift fam c nparams nindices pf ks
        (instantiate0 f B) fs hrest
      rw [instantiate0_lift]
      simp only [hlen', hall', hrest']
      rfl
  | .plain :: ks, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, lift]
  | .directRec :: ks, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, lift]
  | .plain :: _, .bvar _, _, _ => by
      simp only [recIdxFromSpineWalk, lift]; split <;> rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => by
      simp only [recIdxFromSpineWalk, lift]; split <;> rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

theorem directRecFamilySpine_lift (c fam : Nat) (ls : List Level)
    (nparams : Nat) (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    directRecFamilySpine fam ls nparams params ks T fs = true →
    directRecFamilySpine fam ls nparams (params.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, lift] at h ⊢
      rw [instantiate0_lift]
      exact directRecFamilySpine_lift c fam ls nparams params ks
        (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, lift] at h ⊢
      have ⟨hhead, hrest⟩ := bool_and_true h
      rw [appsSpine_lift]
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          simp only [hconst, lift] at hhead ⊢
          rw [hhead, instantiate0_lift]
          exact directRecFamilySpine_lift c fam ls nparams params ks
            (instantiate0 f B) fs hrest
      | bvar _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: ks, .pi _ _, [], _ => by
      simp only [directRecFamilySpine, List.map_nil, lift]
  | .directRec :: ks, .pi _ _, [], _ => by
      simp only [directRecFamilySpine, List.map_nil, lift]
  | .plain :: _, .bvar _, _, _ => by
      simp only [directRecFamilySpine, lift]; split <;> rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => by
      simp only [directRecFamilySpine, lift]; split <;> rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

/-- 00 §20.5: the EXACT walk transports under `lift` (both extra
`decide`s are mapped by `lift` on each side; `List.map_take`
commutes the parameter prefix). -/
theorem directRecFamilySpineExact_lift (c fam : Nat) (ls : List Level)
    (nparams : Nat) (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    directRecFamilySpineExact fam ls nparams params ks T fs = true →
    directRecFamilySpineExact fam ls nparams (params.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpineExact, List.map_cons, lift] at h ⊢
      rw [instantiate0_lift]
      exact directRecFamilySpineExact_lift c fam ls nparams params ks
        (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpineExact, List.map_cons, lift] at h ⊢
      have ⟨hh, hrest⟩ := bool_and_true h
      have ⟨hhead, htake⟩ := bool_and_true hh
      have hte : (appsSpine A).2.take nparams = params :=
        of_decide_eq_true htake
      have htake' :
          decide (((appsSpine A).2.map (lift c 1)).take nparams =
            params.map (lift c 1)) = true := by
        rw [← List.map_take, hte]
        exact decide_eq_true rfl
      rw [appsSpine_lift]
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          simp only [hconst, lift] at hhead ⊢
          rw [hhead, htake', instantiate0_lift]
          exact directRecFamilySpineExact_lift c fam ls nparams params ks
            (instantiate0 f B) fs hrest
      | bvar _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: ks, .pi _ _, [], _ => by
      simp only [directRecFamilySpineExact, List.map_nil, lift]
  | .directRec :: ks, .pi _ _, [], _ => by
      simp only [directRecFamilySpineExact, List.map_nil, lift]
  | .plain :: _, .bvar _, _, _ => by
      simp only [directRecFamilySpineExact, lift]; split <;> rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => by
      simp only [directRecFamilySpineExact, lift]; split <;> rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

theorem listIndexOf_lift (c : Nat) (x : Expr Nat) :
    (xs : List (Expr Nat)) →
    listIndexOf (lift c 1 x) (xs.map (lift c 1)) = listIndexOf x xs
  | [] => rfl
  | y :: ys => by
      simp only [listIndexOf, List.map_cons]
      split
      · rename_i hfeq
        have heq : x = y := lift_inj c x y hfeq
        simp only [heq, ↓reduceIte]
      · rename_i hne
        have hne' : ¬ (x = y) := fun heq => hne (congrArg (lift c 1) heq)
        simp only [hne', ↓reduceIte]
        rw [listIndexOf_lift c x ys]

theorem listIndexOf_get {α} [DecidableEq α] {x : α} {xs : List α} {i : Nat}
    (h : listIndexOf x xs = some i) : xs[i]? = some x := by
  induction xs generalizing i with
  | nil =>
      simp only [listIndexOf] at h
      exact Option.noConfusion h
  | cons y ys ih =>
      simp only [listIndexOf] at h
      split at h
      · rename_i heq
        injection h with hi
        subst hi
        subst heq
        simp only [List.getElem?_cons_zero]
      · cases hmap : listIndexOf x ys with
        | none =>
            simp only [hmap, Option.map_none'] at h
            exact Option.noConfusion h
        | some j =>
            simp only [hmap, Option.map_some'] at h
            injection h with hi
            subst hi
            have := ih hmap
            simp only [List.getElem?_cons_succ]
            exact this

theorem idxTyAlignGo_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (recPre paramsFields : List (Expr Nat)) :
    (pre rest : List (Expr Nat)) →
    idxTyAlignGo recType ctorType recPre paramsFields pre rest = true →
    idxTyAlignGo recType ctorType (recPre.map (lift c 1))
      (paramsFields.map (lift c 1)) (pre.map (lift c 1))
      (rest.map (lift c 1)) = true
  | pre, [], _ => rfl
  | pre, x :: xs, h => by
      simp only [idxTyAlignGo] at h ⊢
      simp only [listIndexOf_lift, List.map_append, List.map_cons,
        List.map_nil]
      cases hfi : listIndexOf x paramsFields with
      | none =>
          simp only [hfi] at h
          nomatch h
      | some i =>
          simp only [hfi] at h ⊢
          cases happR : applyTel (recPre ++ pre) recType with
          | none =>
              simp only [happR] at h
              nomatch h
          | some Ur =>
              simp only [happR] at h
              match Ur with
              | .pi Ar Br =>
                  simp only [hfi, happR] at h
                  cases happC : applyTel (paramsFields.take i) ctorType with
                  | none =>
                      simp only [happC] at h
                      nomatch h
                  | some Uc =>
                      match Uc with
                      | .pi Ac Bc =>
                          simp only [happC] at h
                          have ⟨heq, hrest⟩ := bool_and_true h
                          have hAcAr : Ac = Ar := of_decide_eq_true heq
                          have happR' := applyTel_congr_lift c 1
                            (recPre ++ pre) happR
                          rw [hrecCl, List.map_append] at happR'
                          have happC' := applyTel_congr_lift c 1
                            (paramsFields.take i) happC
                          rw [hctorCl, List.map_take] at happC'
                          simp only [idxTyAlignPosGo, List.map_append,
                            List.map_cons, List.map_nil, lift, happR', happC']
                          have heq' : decide (lift c 1 Ac = lift c 1 Ar) = true := by
                            rw [hAcAr]
                            exact decide_eq_true rfl
                          have ih := idxTyAlignGo_lift c recType ctorType
                            hrecCl hctorCl recPre paramsFields
                            (pre ++ [x]) xs hrest
                          rw [List.map_append, List.map_cons, List.map_nil] at ih
                          rw [heq', ih]
                          rfl
                      | .bvar _ =>
                          simp only [happC] at h; nomatch h
                      | .sort _ =>
                          simp only [happC] at h; nomatch h
                      | .const _ _ =>
                          simp only [happC] at h; nomatch h
                      | .app _ _ =>
                          simp only [happC] at h; nomatch h
                      | .lam _ _ =>
                          simp only [happC] at h; nomatch h
                      | .letE _ _ _ =>
                          simp only [happC] at h; nomatch h
                      | .lit _ =>
                          simp only [happC] at h; nomatch h
              | .bvar _ =>
                  simp only [happR] at h; nomatch h
              | .sort _ =>
                  simp only [happR] at h; nomatch h
              | .const _ _ =>
                  simp only [happR] at h; nomatch h
              | .app _ _ =>
                  simp only [happR] at h; nomatch h
              | .lam _ _ =>
                  simp only [happR] at h; nomatch h
              | .letE _ _ _ =>
                  simp only [happR] at h; nomatch h
              | .lit _ =>
                  simp only [happR] at h; nomatch h

theorem recIdxTyWalk_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (nparams : Nat) (recPre paramsFields : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    recIdxTyWalk recType ctorType nparams recPre paramsFields ks T fs = true →
    recIdxTyWalk recType ctorType nparams
      (recPre.map (lift c 1)) (paramsFields.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, h => by
      simp only [recIdxTyWalk, List.map_cons, lift] at h ⊢
      rw [instantiate0_lift]
      exact recIdxTyWalk_lift c recType ctorType hrecCl hctorCl nparams
        recPre paramsFields ks (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [recIdxTyWalk, List.map_cons, lift] at h ⊢
      have ⟨halign, hrest⟩ := bool_and_true h
      have hfi := familyIdx_lift c 1 nparams A
      have halign' : idxTyAlign recType ctorType
          (recPre.map (lift c 1)) (paramsFields.map (lift c 1))
          (familyIdx nparams (lift c 1 A)) = true := by
        simp only [idxTyAlign, hfi]
        simp only [idxTyAlign] at halign
        exact idxTyAlignGo_lift c recType ctorType hrecCl hctorCl
          recPre paramsFields [] (familyIdx nparams A) halign
      have hrest' := recIdxTyWalk_lift c recType ctorType hrecCl hctorCl
        nparams recPre paramsFields ks (instantiate0 f B) fs hrest
      rw [instantiate0_lift]
      simp only [halign', hrest']
      rfl
  | .plain :: _, .pi _ _, [], _ => by
      simp only [recIdxTyWalk, List.map_nil, lift]
  | .directRec :: _, .pi _ _, [], _ => by
      simp only [recIdxTyWalk, List.map_nil, lift]
  | .plain :: _, .bvar _, _, _ => by
      simp only [recIdxTyWalk, lift]; split <;> rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => by
      simp only [recIdxTyWalk, lift]; split <;> rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

theorem rhsArgs_lift (c nparams nMinors : Nat) (rec : Expr Nat)
    (preMajor : List (Expr Nat)) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (T : Expr Nat) →
    (rhsArgs rec preMajor nparams nMinors fs ks T).map (lift c 1) =
      rhsArgs (lift c 1 rec) (preMajor.map (lift c 1)) nparams nMinors
        (fs.map (lift c 1)) ks (lift c 1 T)
  | [], _, T => by simp only [rhsArgs, List.map_nil]
  | f :: fs, [], T => by
      simp only [rhsArgs, List.map_cons]
      rw [rhsArgs_lift]
  | f :: fs, .plain :: ks, .pi A B => by
      simp only [rhsArgs, List.map_cons, lift]
      rw [instantiate0_lift, rhsArgs_lift]
  | f :: fs, .directRec :: ks, .pi A B => by
      simp only [rhsArgs, List.map_cons, List.map_append, recCallField_lift]
      rw [instantiate0_lift, rhsArgs_lift]
  | f :: fs, .plain :: ks, .bvar _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]
      simp only [lift]; split <;> simp only [rhsArgs]
  | f :: fs, .plain :: ks, .sort _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .plain :: ks, .const _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .plain :: ks, .app _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .plain :: ks, .lam _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .plain :: ks, .letE _ _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .plain :: ks, .lit _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .bvar _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]
      simp only [lift]; split <;> simp only [rhsArgs]
  | f :: fs, .directRec :: ks, .sort _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .const _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .app _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .lam _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .letE _ _ _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]
  | f :: fs, .directRec :: ks, .lit _ => by
      simp only [rhsArgs, List.map_cons]; rw [rhsArgs_lift]; simp only [rhsArgs, lift]

theorem idxPosZip_cons {pf : List (Expr Nat)} {x : Expr Nat}
    {xs : List (Expr Nat)} {i : Nat} {is : List Nat}
    (h : idxPosZip pf (x :: xs) (i :: is) = true) :
    pf[i]? = some x ∧ idxPosZip pf xs is = true := by
  simp only [idxPosZip] at h
  have ⟨heq, hrest⟩ := bool_and_true h
  exact ⟨of_decide_eq_true heq, hrest⟩

theorem idxPosZip_lift (c : Nat) (pf xs : List (Expr Nat)) (pos : List Nat)
    (h : idxPosZip pf xs pos = true) :
    idxPosZip (pf.map (lift c 1)) (xs.map (lift c 1)) pos = true := by
  induction xs generalizing pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons _ _ => simp only [idxPosZip] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil => simp only [idxPosZip] at h; nomatch h
      | cons i is =>
          have ⟨hx, hrest⟩ := idxPosZip_cons h
          have hx' : (pf.map (lift c 1))[i]? = some (lift c 1 x) := by
            rw [List.getElem?_map, hx]; rfl
          have hrest' := ih is hrest
          simp only [idxPosZip, List.map_cons, hx', decide_eq_true rfl, hrest']
          rfl

theorem idxPosZip_instantiate (j : Nat) (s : Expr Nat)
    (pf xs : List (Expr Nat)) (pos : List Nat)
    (h : idxPosZip pf xs pos = true) :
    idxPosZip (pf.map (instantiate j s))
      (xs.map (instantiate j s)) pos = true := by
  induction xs generalizing pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons _ _ => simp only [idxPosZip] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil => simp only [idxPosZip] at h; nomatch h
      | cons i is =>
          have ⟨hx, hrest⟩ := idxPosZip_cons h
          have hx' : (pf.map (instantiate j s))[i]? =
              some (instantiate j s x) := by
            rw [List.getElem?_map, hx]; rfl
          have hrest' := ih is hrest
          simp only [idxPosZip, List.map_cons, hx', decide_eq_true rfl, hrest']
          rfl

theorem recIdxPosWalk_lift (c nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxPosWalk nparams pf ks T fs pss = true) :
    recIdxPosWalk nparams (pf.map (lift c 1)) ks (lift c 1 T)
      (fs.map (lift c 1)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxPosWalk, List.map_nil]
          | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxPosWalk, List.map_cons, lift]
                            at h ⊢
                          rw [instantiate0_lift]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxPosWalk] at h; nomatch h
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      simp only [recIdxPosWalk, List.map_cons, lift]
                        at h ⊢
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      have hzip' : idxPosZip (pf.map (lift c 1))
                          (familyIdx nparams (lift c 1 A)) pos = true := by
                        rw [hfi]
                        exact idxPosZip_lift c pf (familyIdx nparams A)
                          pos hzip
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [instantiate0_lift]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h

theorem recIdxPosWalk_instantiate (j nparams : Nat) (s : Expr Nat)
    (pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List Nat))
    (htel : isPiTel ks.length T = true)
    (hfam : directRecConstHead ks T = true)
    (h : recIdxPosWalk nparams pf ks T fs pss = true) :
    recIdxPosWalk nparams (pf.map (instantiate j s)) ks
      (instantiate j s T) (fs.map (instantiate j s)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxPosWalk, List.map_nil]
          | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [isPiTel, List.length_cons, recIdxPosWalk,
                            List.map_cons, instantiate, directRecConstHead]
                            at htel hfam h ⊢
                          have htel' :=
                            isPiTel_instantiate 0 f ks.length B htel
                          have hfam' :=
                            directRecConstHead_instantiate 0 f ks B htel hfam
                          have ih' :=
                            ih (instantiate0 f B) fs pss htel' hfam' h
                          have heq : instantiate j s (instantiate0 f B) =
                              instantiate0 (instantiate j s f)
                                (instantiate (j + 1) (lift 0 1 s) B) := by
                            simp only [instantiate0]
                            exact instantiate_instantiate 0 j f s
                              (Nat.zero_le j) B
                          rw [← heq]
                          exact ih'
                      | cons _ _ =>
                          simp only [recIdxPosWalk] at h; nomatch h
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      simp only [isPiTel, List.length_cons, recIdxPosWalk,
                        List.map_cons, instantiate, directRecConstHead]
                        at htel hfam h ⊢
                      have ⟨hsc, hfamB⟩ := bool_and_true hfam
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi : familyIdx nparams (instantiate j s A) =
                          (familyIdx nparams A).map (instantiate j s) := by
                        simp only [spineHeadConst] at hsc
                        cases hsp : (appsSpine A).1 with
                        | const r ls =>
                            exact familyIdx_instantiate_const j s nparams
                              (by rw [hsp])
                        | bvar _ => simp only [hsp] at hsc; nomatch hsc
                        | sort _ => simp only [hsp] at hsc; nomatch hsc
                        | app _ _ => simp only [hsp] at hsc; nomatch hsc
                        | lam _ _ => simp only [hsp] at hsc; nomatch hsc
                        | pi _ _ => simp only [hsp] at hsc; nomatch hsc
                        | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
                        | lit _ => simp only [hsp] at hsc; nomatch hsc
                      have hzip' : idxPosZip (pf.map (instantiate j s))
                          (familyIdx nparams (instantiate j s A)) pos =
                            true := by
                        rw [hfi]
                        exact idxPosZip_instantiate j s pf
                          (familyIdx nparams A) pos hzip
                      have htel' :=
                        isPiTel_instantiate 0 f ks.length B htel
                      have hfam' :=
                        directRecConstHead_instantiate 0 f ks B htel hfamB
                      have hrest' :=
                        ih (instantiate0 f B) fs pss htel' hfam' hrest
                      have heq : instantiate j s (instantiate0 f B) =
                          instantiate0 (instantiate j s f)
                            (instantiate (j + 1) (lift 0 1 s) B) := by
                        simp only [instantiate0]
                        exact instantiate_instantiate 0 j f s
                          (Nat.zero_le j) B
                      rw [← heq]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h

theorem idxTyAlignPosGo_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (recPre paramsFields pre rest : List (Expr Nat)) (pos : List Nat)
    (h : idxTyAlignPosGo recType ctorType recPre paramsFields pre rest pos =
      true) :
    idxTyAlignPosGo recType ctorType (recPre.map (lift c 1))
      (paramsFields.map (lift c 1)) (pre.map (lift c 1))
      (rest.map (lift c 1)) pos = true := by
  induction rest generalizing pre pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons i is =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre [] (i :: is) = false := rfl
          rw [hf] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre (x :: xs) [] = false := rfl
          rw [hf] at h; nomatch h
      | cons i is =>
          simp only [idxTyAlignPosGo] at h
          simp only [List.map_append, List.map_cons, List.map_nil]
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [happR] at h; nomatch h
          | some Ur =>
              match Ur with
              | .pi Ar Br =>
                  simp only [happR] at h
                  cases happC : applyTel (paramsFields.take i) ctorType with
                  | none => simp only [happC] at h; nomatch h
                  | some Uc =>
                      match Uc with
                      | .pi Ac Bc =>
                          simp only [happC] at h
                          have ⟨heq, hrest⟩ := bool_and_true h
                          have hAcAr : Ac = Ar := of_decide_eq_true heq
                          have happR' := applyTel_congr_lift c 1
                            (recPre ++ pre) happR
                          rw [hrecCl, List.map_append] at happR'
                          have happC' := applyTel_congr_lift c 1
                            (paramsFields.take i) happC
                          rw [hctorCl, List.map_take] at happC'
                          simp only [idxTyAlignPosGo, List.map_append,
                            List.map_cons, List.map_nil, lift, happR', happC']
                          have heq' :
                              decide (lift c 1 Ac = lift c 1 Ar) = true := by
                            rw [hAcAr]; exact decide_eq_true rfl
                          have ih' := ih (pre ++ [x]) is hrest
                          rw [List.map_append, List.map_cons, List.map_nil]
                            at ih'
                          rw [heq', ih']
                          rfl
                      | .bvar _ => simp only [happC] at h; nomatch h
                      | .sort _ => simp only [happC] at h; nomatch h
                      | .const _ _ => simp only [happC] at h; nomatch h
                      | .app _ _ => simp only [happC] at h; nomatch h
                      | .lam _ _ => simp only [happC] at h; nomatch h
                      | .letE _ _ _ => simp only [happC] at h; nomatch h
                      | .lit _ => simp only [happC] at h; nomatch h
              | .bvar _ => simp only [happR] at h; nomatch h
              | .sort _ => simp only [happR] at h; nomatch h
              | .const _ _ => simp only [happR] at h; nomatch h
              | .app _ _ => simp only [happR] at h; nomatch h
              | .lam _ _ => simp only [happR] at h; nomatch h
              | .letE _ _ _ => simp only [happR] at h; nomatch h
              | .lit _ => simp only [happR] at h; nomatch h

/-- 00 §20.5 `hparamAlign` transport: both stored types are closed,
so `lift` fixes them and only the parameter prefix maps. -/
theorem recCtorParamAlignGo_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (pre rest : List (Expr Nat))
    (h : recCtorParamAlignGo recType ctorType pre rest = true) :
    recCtorParamAlignGo recType ctorType (pre.map (lift c 1))
      (rest.map (lift c 1)) = true := by
  induction rest generalizing pre with
  | nil => rfl
  | cons x xs ih =>
      simp only [recCtorParamAlignGo] at h
      simp only [List.map_cons]
      cases happR : applyTel pre recType with
      | none => simp only [happR] at h; nomatch h
      | some Ur =>
          match Ur with
          | .pi Ar Br =>
              simp only [happR] at h
              cases happC : applyTel pre ctorType with
              | none => simp only [happC] at h; nomatch h
              | some Uc =>
                  match Uc with
                  | .pi Ac Bc =>
                      simp only [happC] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happR' := applyTel_congr_lift c 1 pre happR
                      rw [hrecCl] at happR'
                      have happC' := applyTel_congr_lift c 1 pre happC
                      rw [hctorCl] at happC'
                      simp only [recCtorParamAlignGo, lift, happR', happC']
                      have heq' :
                          decide (lift c 1 Ac = lift c 1 Ar) = true := by
                        rw [hAcAr]; exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) hrest
                      rw [List.map_append, List.map_cons, List.map_nil]
                        at ih'
                      rw [heq', ih']
                      rfl
                  | .bvar _ => simp only [happC] at h; nomatch h
                  | .sort _ => simp only [happC] at h; nomatch h
                  | .const _ _ => simp only [happC] at h; nomatch h
                  | .app _ _ => simp only [happC] at h; nomatch h
                  | .lam _ _ => simp only [happC] at h; nomatch h
                  | .letE _ _ _ => simp only [happC] at h; nomatch h
                  | .lit _ => simp only [happC] at h; nomatch h
          | .bvar _ => simp only [happR] at h; nomatch h
          | .sort _ => simp only [happR] at h; nomatch h
          | .const _ _ => simp only [happR] at h; nomatch h
          | .app _ _ => simp only [happR] at h; nomatch h
          | .lam _ _ => simp only [happR] at h; nomatch h
          | .letE _ _ _ => simp only [happR] at h; nomatch h
          | .lit _ => simp only [happR] at h; nomatch h

theorem recCtorParamAlign_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (params : List (Expr Nat))
    (h : recCtorParamAlign recType ctorType params = true) :
    recCtorParamAlign recType ctorType (params.map (lift c 1)) = true := by
  simp only [recCtorParamAlign] at h ⊢
  have hgo := recCtorParamAlignGo_lift c recType ctorType hrecCl hctorCl
    [] params h
  simp only [List.map_nil] at hgo
  exact hgo

theorem idxTyAlignPosGo_instantiate (j : Nat) (s : Expr Nat)
    (recType ctorType : Expr Nat)
    (hrecCl : instantiate j s recType = recType)
    (hctorCl : instantiate j s ctorType = ctorType)
    (recPre paramsFields pre rest : List (Expr Nat)) (pos : List Nat)
    (h : idxTyAlignPosGo recType ctorType recPre paramsFields pre rest pos =
      true) :
    idxTyAlignPosGo recType ctorType (recPre.map (instantiate j s))
      (paramsFields.map (instantiate j s)) (pre.map (instantiate j s))
      (rest.map (instantiate j s)) pos = true := by
  induction rest generalizing pre pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons i is =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre [] (i :: is) = false := rfl
          rw [hf] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre (x :: xs) [] = false := rfl
          rw [hf] at h; nomatch h
      | cons i is =>
          simp only [idxTyAlignPosGo] at h
          simp only [List.map_append, List.map_cons, List.map_nil]
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [happR] at h; nomatch h
          | some Ur =>
              match Ur with
              | .pi Ar Br =>
                  simp only [happR] at h
                  cases happC : applyTel (paramsFields.take i) ctorType with
                  | none => simp only [happC] at h; nomatch h
                  | some Uc =>
                      match Uc with
                      | .pi Ac Bc =>
                          simp only [happC] at h
                          have ⟨heq, hrest⟩ := bool_and_true h
                          have hAcAr : Ac = Ar := of_decide_eq_true heq
                          have happR' := applyTel_congr_instantiate j s
                            (recPre ++ pre) happR
                          rw [hrecCl, List.map_append] at happR'
                          have happC' := applyTel_congr_instantiate j s
                            (paramsFields.take i) happC
                          rw [hctorCl, List.map_take] at happC'
                          simp only [idxTyAlignPosGo, List.map_append,
                            List.map_cons, List.map_nil, instantiate,
                            happR', happC']
                          have heq' :
                              decide (instantiate j s Ac =
                                instantiate j s Ar) = true := by
                            rw [hAcAr]; exact decide_eq_true rfl
                          have ih' := ih (pre ++ [x]) is hrest
                          rw [List.map_append, List.map_cons, List.map_nil]
                            at ih'
                          rw [heq', ih']
                          rfl
                      | .bvar _ => simp only [happC] at h; nomatch h
                      | .sort _ => simp only [happC] at h; nomatch h
                      | .const _ _ => simp only [happC] at h; nomatch h
                      | .app _ _ => simp only [happC] at h; nomatch h
                      | .lam _ _ => simp only [happC] at h; nomatch h
                      | .letE _ _ _ => simp only [happC] at h; nomatch h
                      | .lit _ => simp only [happC] at h; nomatch h
              | .bvar _ => simp only [happR] at h; nomatch h
              | .sort _ => simp only [happR] at h; nomatch h
              | .const _ _ => simp only [happR] at h; nomatch h
              | .app _ _ => simp only [happR] at h; nomatch h
              | .lam _ _ => simp only [happR] at h; nomatch h
              | .letE _ _ _ => simp only [happR] at h; nomatch h
              | .lit _ => simp only [happR] at h; nomatch h

/-- 00 §20.5 `hparamAlign` transport under `instantiate`. -/
theorem recCtorParamAlignGo_instantiate (j : Nat) (s : Expr Nat)
    (recType ctorType : Expr Nat)
    (hrecCl : instantiate j s recType = recType)
    (hctorCl : instantiate j s ctorType = ctorType)
    (pre rest : List (Expr Nat))
    (h : recCtorParamAlignGo recType ctorType pre rest = true) :
    recCtorParamAlignGo recType ctorType (pre.map (instantiate j s))
      (rest.map (instantiate j s)) = true := by
  induction rest generalizing pre with
  | nil => rfl
  | cons x xs ih =>
      simp only [recCtorParamAlignGo] at h
      simp only [List.map_cons]
      cases happR : applyTel pre recType with
      | none => simp only [happR] at h; nomatch h
      | some Ur =>
          match Ur with
          | .pi Ar Br =>
              simp only [happR] at h
              cases happC : applyTel pre ctorType with
              | none => simp only [happC] at h; nomatch h
              | some Uc =>
                  match Uc with
                  | .pi Ac Bc =>
                      simp only [happC] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happR' := applyTel_congr_instantiate j s pre happR
                      rw [hrecCl] at happR'
                      have happC' := applyTel_congr_instantiate j s pre happC
                      rw [hctorCl] at happC'
                      simp only [recCtorParamAlignGo, instantiate,
                        happR', happC']
                      have heq' :
                          decide (instantiate j s Ac =
                            instantiate j s Ar) = true := by
                        rw [hAcAr]; exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) hrest
                      rw [List.map_append, List.map_cons, List.map_nil]
                        at ih'
                      rw [heq', ih']
                      rfl
                  | .bvar _ => simp only [happC] at h; nomatch h
                  | .sort _ => simp only [happC] at h; nomatch h
                  | .const _ _ => simp only [happC] at h; nomatch h
                  | .app _ _ => simp only [happC] at h; nomatch h
                  | .lam _ _ => simp only [happC] at h; nomatch h
                  | .letE _ _ _ => simp only [happC] at h; nomatch h
                  | .lit _ => simp only [happC] at h; nomatch h
          | .bvar _ => simp only [happR] at h; nomatch h
          | .sort _ => simp only [happR] at h; nomatch h
          | .const _ _ => simp only [happR] at h; nomatch h
          | .app _ _ => simp only [happR] at h; nomatch h
          | .lam _ _ => simp only [happR] at h; nomatch h
          | .letE _ _ _ => simp only [happR] at h; nomatch h
          | .lit _ => simp only [happR] at h; nomatch h

theorem recCtorParamAlign_instantiate (j : Nat) (s : Expr Nat)
    (recType ctorType : Expr Nat)
    (hrecCl : instantiate j s recType = recType)
    (hctorCl : instantiate j s ctorType = ctorType)
    (params : List (Expr Nat))
    (h : recCtorParamAlign recType ctorType params = true) :
    recCtorParamAlign recType ctorType (params.map (instantiate j s)) =
      true := by
  simp only [recCtorParamAlign] at h ⊢
  have hgo := recCtorParamAlignGo_instantiate j s recType ctorType
    hrecCl hctorCl [] params h
  simp only [List.map_nil] at hgo
  exact hgo

theorem recIdxTyWalkPos_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (nparams : Nat) (recPre paramsFields : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxTyWalkPos recType ctorType nparams recPre paramsFields ks T
      fs pss = true) :
    recIdxTyWalkPos recType ctorType nparams (recPre.map (lift c 1))
      (paramsFields.map (lift c 1)) ks (lift c 1 T)
      (fs.map (lift c 1)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTyWalkPos, List.map_nil]
          | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxTyWalkPos, List.map_cons, lift]
                            at h ⊢
                          rw [instantiate0_lift]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxTyWalkPos] at h; nomatch h
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      simp only [recIdxTyWalkPos, List.map_cons, lift]
                        at h ⊢
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      have halign' : idxTyAlignPos recType ctorType
                          (recPre.map (lift c 1))
                          (paramsFields.map (lift c 1))
                          (familyIdx nparams (lift c 1 A)) pos = true := by
                        simp only [idxTyAlignPos, hfi]
                        simp only [idxTyAlignPos] at halign
                        exact idxTyAlignPosGo_lift c recType ctorType
                          hrecCl hctorCl recPre paramsFields []
                          (familyIdx nparams A) pos halign
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [instantiate0_lift]
                      simp only [halign', hrest']
                      rfl
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h

theorem recIdxTyWalkPos_instantiate (j : Nat) (s : Expr Nat)
    (recType ctorType : Expr Nat)
    (hrecCl : instantiate j s recType = recType)
    (hctorCl : instantiate j s ctorType = ctorType)
    (nparams : Nat) (recPre paramsFields : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (htel : isPiTel ks.length T = true)
    (hfam : directRecConstHead ks T = true)
    (h : recIdxTyWalkPos recType ctorType nparams recPre paramsFields ks T
      fs pss = true) :
    recIdxTyWalkPos recType ctorType nparams
      (recPre.map (instantiate j s)) (paramsFields.map (instantiate j s))
      ks (instantiate j s T) (fs.map (instantiate j s)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTyWalkPos, List.map_nil]
          | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [isPiTel, List.length_cons,
                            recIdxTyWalkPos, List.map_cons, instantiate,
                            directRecConstHead] at htel hfam h ⊢
                          have htel' :=
                            isPiTel_instantiate 0 f ks.length B htel
                          have hfam' :=
                            directRecConstHead_instantiate 0 f ks B htel hfam
                          have ih' :=
                            ih (instantiate0 f B) fs pss htel' hfam' h
                          have heq : instantiate j s (instantiate0 f B) =
                              instantiate0 (instantiate j s f)
                                (instantiate (j + 1) (lift 0 1 s) B) := by
                            simp only [instantiate0]
                            exact instantiate_instantiate 0 j f s
                              (Nat.zero_le j) B
                          rw [← heq]
                          exact ih'
                      | cons _ _ =>
                          simp only [recIdxTyWalkPos] at h; nomatch h
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      simp only [isPiTel, List.length_cons, recIdxTyWalkPos,
                        List.map_cons, instantiate, directRecConstHead]
                        at htel hfam h ⊢
                      have ⟨hsc, hfamB⟩ := bool_and_true hfam
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi : familyIdx nparams (instantiate j s A) =
                          (familyIdx nparams A).map (instantiate j s) := by
                        simp only [spineHeadConst] at hsc
                        cases hsp : (appsSpine A).1 with
                        | const r ls =>
                            exact familyIdx_instantiate_const j s nparams
                              (by rw [hsp])
                        | bvar _ => simp only [hsp] at hsc; nomatch hsc
                        | sort _ => simp only [hsp] at hsc; nomatch hsc
                        | app _ _ => simp only [hsp] at hsc; nomatch hsc
                        | lam _ _ => simp only [hsp] at hsc; nomatch hsc
                        | pi _ _ => simp only [hsp] at hsc; nomatch hsc
                        | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
                        | lit _ => simp only [hsp] at hsc; nomatch hsc
                      have halign' : idxTyAlignPos recType ctorType
                          (recPre.map (instantiate j s))
                          (paramsFields.map (instantiate j s))
                          (familyIdx nparams (instantiate j s A)) pos =
                            true := by
                        simp only [idxTyAlignPos, hfi]
                        simp only [idxTyAlignPos] at halign
                        exact idxTyAlignPosGo_instantiate j s recType
                          ctorType hrecCl hctorCl recPre paramsFields []
                          (familyIdx nparams A) pos halign
                      have htel' :=
                        isPiTel_instantiate 0 f ks.length B htel
                      have hfam' :=
                        directRecConstHead_instantiate 0 f ks B htel hfamB
                      have hrest' :=
                        ih (instantiate0 f B) fs pss htel' hfam' hrest
                      have heq : instantiate j s (instantiate0 f B) =
                          instantiate0 (instantiate j s f)
                            (instantiate (j + 1) (lift 0 1 s) B) := by
                        simp only [instantiate0]
                        exact instantiate_instantiate 0 j f s
                          (Nat.zero_le j) B
                      rw [← heq]
                      simp only [halign', hrest']
                      rfl
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h

theorem recIdxTyWalkPos_directRec {recType ctorType : Expr Nat}
    {nparams : Nat} {recPre pf : List (Expr Nat)}
    {A B f : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    {pos : List Nat} {pss : List (List Nat)}
    (h : recIdxTyWalkPos recType ctorType nparams recPre pf
      (.directRec :: ks) (.pi A B) (f :: fs) (pos :: pss) = true) :
    idxTyAlignPos recType ctorType recPre pf (familyIdx nparams A) pos =
      true ∧
      recIdxTyWalkPos recType ctorType nparams recPre pf ks
        (instantiate0 f B) fs pss = true := by
  simp only [recIdxTyWalkPos] at h
  exact bool_and_true h

theorem recIdxPosWalk_directRec {nparams : Nat} {pf : List (Expr Nat)}
    {A B f : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    {pos : List Nat} {pss : List (List Nat)}
    (h : recIdxPosWalk nparams pf (.directRec :: ks) (.pi A B)
      (f :: fs) (pos :: pss) = true) :
    idxPosZip pf (familyIdx nparams A) pos = true ∧
      recIdxPosWalk nparams pf ks (instantiate0 f B) fs pss = true := by
  simp only [recIdxPosWalk] at h
  exact bool_and_true h

def liftWitness (c : Nat) {E : ResolvedEnv} (w : IotaWitness E) : IotaWitness E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (lift c 1)
  fields := w.fields.map (lift c 1)
  ctorParams := w.ctorParams.map (lift c 1)
  kinds := w.kinds
  minor := lift c 1 w.minor
  hlen := by
    simp only [List.length_map]
    exact w.hlen
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by
    simp only [List.length_map]
    exact w.hctorParams
  hnpar := by
    simp only [List.length_map]
    exact w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by
    simp only [List.length_map]
    exact w.hpre
  hminor := by
    rw [List.getElem?_map]
    rw [w.hminor]
    rfl
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by
    simp only [List.length_map]
    exact w.hpeel
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
  ctorAfterParams := lift c 1 w.ctorAfterParams
  hctorAfter := by
    have htake :
        (w.preMajor.map (lift c 1)).take w.nparams =
          (w.preMajor.take w.nparams).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor w.nparams).symm
    rw [htake]
    have hcl : lift c 1 (instantiateLevels w.ls w.ctorMember.mtype) =
        instantiateLevels w.ls w.ctorMember.mtype :=
      lift_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) c 1
    have happ := applyTel_congr_lift c 1
      (w.preMajor.take w.nparams) w.hctorAfter
    rw [hcl] at happ
    exact happ
  hctorTel := isPiTel_lift c 1 w.kinds.length w.ctorAfterParams w.hctorTel
  hfamTel := directRecConstHead_lift c 1 w.kinds w.ctorAfterParams w.hfamTel
  hresTel := resultConstHead_lift c 1 w.kinds w.ctorAfterParams w.hresTel

theorem ctorMajor_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitness E) :
    ctorMajor (liftWitness c w) = lift c 1 (ctorMajor w) := by
  change foldApps (.const w.ctorRef w.lsC)
      (w.ctorParams.map (lift c 1) ++ w.fields.map (lift c 1)) =
    lift c 1 (foldApps (.const w.ctorRef w.lsC)
      (w.ctorParams ++ w.fields))
  rw [foldApps_lift, lift, List.map_append]

/-- 00 §20.5: recursor-side constructor application transports. -/
theorem ctorMajorRec_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitness E) :
    ctorMajorRec (liftWitness c w) = lift c 1 (ctorMajorRec w) := by
  change foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      ((w.preMajor.map (lift c 1)).take w.nparams ++
        w.fields.map (lift c 1)) =
    lift c 1 (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams ++ w.fields))
  rw [foldApps_lift, lift, List.map_append,
    List.map_take (lift c 1) w.preMajor w.nparams]

theorem iotaLhsOf_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitness E) :
    iotaLhsOf (liftWitness c w) = lift c 1 (iotaLhsOf w) := by
  unfold iotaLhsOf
  rw [recCall_lift, ctorMajor_lift]
  simp only [liftWitness, lift]

theorem kinds_map_liftK (c : Nat) : (ks : List RecKind) →
    ks.map (RecKind.liftK c) = ks
  | [] => rfl
  | k :: ks => by
      simp only [List.map_cons, RecKind.liftK_id c k, kinds_map_liftK c ks]

theorem kinds_map_instK (j : Nat) (v : Expr Nat) : (ks : List RecKind) →
    ks.map (RecKind.instK j v) = ks
  | [] => rfl
  | k :: ks => by
      simp only [List.map_cons, RecKind.instK_id j v k, kinds_map_instK j v ks]

theorem iotaRhsOf_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitness E) :
    iotaRhsOf (liftWitness c w) = lift c 1 (iotaRhsOf w) := by
  simp only [iotaRhsOf, liftWitness, foldApps_lift]
  rw [rhsArgs_lift]
  simp only [lift]

/-- F-05a: IotaLift is a theorem over the 05 §11–12 relation. -/
def iotaLift (E : ResolvedEnv) : IotaLift E :=
  fun lhs rhs h c =>
    match h with
    | .of w => by
        have h1 := iotaLhsOf_lift c w
        have h2 := iotaRhsOf_lift c w
        rw [← h1, ← h2]
        exact .of (liftWitness c w)

theorem iotaMdom_lift {E : ResolvedEnv} (c : Nat) (w : IotaWitness E)
    (motive : Expr Nat) :
    iotaMdom (liftWitness c w) (lift c 1 motive) =
      lift c 1 (iotaMdom w motive) := by
  have hmt := minorTel_lift_tel c w.nparams motive
    (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams))
    w.kinds w.ctorAfterParams w.hctorTel
  have hC :
      lift c 1 (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams)) =
      foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        ((w.preMajor.map (lift c 1)).take w.nparams) := by
    rw [foldApps_lift, lift]
    have htake := List.map_take (lift c 1) w.preMajor w.nparams
    rw [htake]
  simp only [iotaMdom, liftWitness]
  rw [hmt, hC]

/-- A `.pos` source types only when slot `i` is a Π. -/
theorem idxSrcTy_pos_dom {fam : Nat} {E : ResolvedEnv} {ctorType : Expr Nat}
    {pf : List (Expr Nat)} {x : Expr Nat} {i : Nat} {Ac : Expr Nat}
    (h : idxSrcTy fam E ctorType pf x (.pos i) = some Ac) :
    ∃ B, applyTel (pf.take i) ctorType = some (.pi Ac B) := by
  simp only [idxSrcTy] at h
  cases happ : applyTel (pf.take i) ctorType with
  | none => simp only [happ] at h; cases h
  | some U =>
      cases U with
      | pi d B =>
          simp only [happ] at h
          cases h
          exact ⟨B, rfl⟩
      | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
          simp only [happ] at h
          cases h

theorem idxSrcTy_constField_dom {fam : Nat} {E : ResolvedEnv}
    {ctorType : Expr Nat} {pf : List (Expr Nat)} {x : Expr Nat} {i : Nat}
    {Ac : Expr Nat}
    (h : idxSrcTy fam E ctorType pf x (.constField i) = some Ac) :
    ∃ r ls B, x = .const r ls ∧
      applyTel (pf.take i) ctorType = some (.pi Ac B) := by
  cases x with
  | const r ls =>
      simp only [idxSrcTy] at h
      cases happ : applyTel (pf.take i) ctorType with
      | none => simp only [happ] at h; cases h
      | some U =>
          cases U with
          | pi d B =>
              simp only [happ] at h
              cases h
              exact ⟨r, ls, B, rfl, rfl⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [happ] at h
              cases h
  | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp only [idxSrcTy] at h
      cases h

theorem idxSrcFuel_lift (n c : Nat) :
    ∀ (x : Expr Nat) (s : IdxSrc), IdxSrcFuel n x s →
      IdxSrcFuel n (lift c 1 x) s := by
  intro x s h
  induction s generalizing x with
  | pos _ =>
      generalize lift c 1 x = y
      cases y <;> simp only [IdxSrcFuel]
  | constField _ =>
      generalize lift c 1 x = y
      cases y <;> simp only [IdxSrcFuel]
  | sort =>
      generalize lift c 1 x = y
      cases y <;> simp only [IdxSrcFuel]
  | lit _ =>
      generalize lift c 1 x = y
      cases y <;> simp only [IdxSrcFuel]
  | constNotFam _ =>
      cases x with
      | const _ _ => simpa only [IdxSrcFuel, lift] using h
      | bvar i =>
          by_cases hi : c ≤ i <;> simp only [lift, hi, ↓reduceIte, IdxSrcFuel]
      | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          exact True.intro
  | app sf sa ihf iha =>
      cases x with
      | app f a =>
          simp only [IdxSrcFuel, lift] at h ⊢
          exact ⟨ihf f h.1, iha a h.2⟩
      | bvar i =>
          by_cases hi : c ≤ i <;> simp only [lift, hi, ↓reduceIte, IdxSrcFuel]
      | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          exact True.intro

theorem idxSrcFuel_instantiate (fam j n : Nat) (pf : List (Expr Nat))
    (v : Expr Nat) : ∀ (x : Expr Nat) (s : IdxSrc),
      idxSrcMatch fam pf x s = true → IdxSrcFuel n x s →
      IdxSrcFuel n (instantiate j v x) s := by
  intro x s hmatch hfuel
  induction s generalizing x with
  | pos _ =>
      generalize instantiate j v x = y
      cases y <;> simp only [IdxSrcFuel]
  | constField _ =>
      generalize instantiate j v x = y
      cases y <;> simp only [IdxSrcFuel]
  | sort =>
      generalize instantiate j v x = y
      cases y <;> simp only [IdxSrcFuel]
  | lit _ =>
      generalize instantiate j v x = y
      cases y <;> simp only [IdxSrcFuel]
  | constNotFam _ =>
      cases x with
      | const _ _ => simpa only [IdxSrcFuel, instantiate] using hfuel
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcMatch] at hmatch
          nomatch hmatch
  | app sf sa ihf iha =>
      cases x with
      | app f a =>
          simp only [idxSrcMatch, Bool.and_eq_true] at hmatch
          simp only [IdxSrcFuel, instantiate] at hfuel ⊢
          exact ⟨ihf f hmatch.1 hfuel.1, iha a hmatch.2 hfuel.2⟩
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcMatch] at hmatch
          nomatch hmatch

theorem idxSrcFuelList_lift (n c : Nat) :
    ∀ (xs : List (Expr Nat)) (ss : List IdxSrc), IdxSrcFuelList n xs ss →
      IdxSrcFuelList n (xs.map (lift c 1)) ss := by
  intro xs
  induction xs with
  | nil => intro ss _; simp only [List.map_nil, IdxSrcFuelList]
  | cons x xs ih =>
      intro ss h
      cases ss with
      | nil => simp only [IdxSrcFuelList]
      | cons s ss =>
          simp only [IdxSrcFuelList, List.map_cons] at h ⊢
          exact ⟨idxSrcFuel_lift n c x s h.1, ih ss h.2⟩

theorem idxSrcFuelList_instantiate (fam j n : Nat)
    (pf : List (Expr Nat)) (v : Expr Nat) :
    ∀ (xs : List (Expr Nat)) (ss : List IdxSrc),
      idxSrcZip fam pf xs ss = true → IdxSrcFuelList n xs ss →
      IdxSrcFuelList n (xs.map (instantiate j v)) ss := by
  intro xs
  induction xs with
  | nil =>
      intro ss hzip _
      cases ss with
      | nil => simp only [List.map_nil, IdxSrcFuelList]
      | cons _ _ => simp only [idxSrcZip] at hzip; nomatch hzip
  | cons x xs ih =>
      intro ss hzip hfuel
      cases ss with
      | nil => simp only [idxSrcZip] at hzip; nomatch hzip
      | cons s ss =>
          have ⟨hmatch, hzip'⟩ := idxSrcZip_cons hzip
          simp only [IdxSrcFuelList, List.map_cons] at hfuel ⊢
          exact ⟨idxSrcFuel_instantiate fam j n pf v x s hmatch hfuel.1,
            ih ss hzip' hfuel.2⟩

/-- Field domains and non-field constants keep their type under `lift`.
`EnvClosed` is what makes `instantiateLevels ls m.mtype` closed, so the
lifted constant is still typed at the same view. -/
theorem idxSrcTy_lift (fam c : Nat) (E : ResolvedEnv) (hcl : EnvClosed E)
    (ctorType : Expr Nat) (hctor : lift c 1 ctorType = ctorType)
    (pf : List (Expr Nat)) :
    (x : Expr Nat) → (s : IdxSrc) → (Ac : Expr Nat) →
    idxSrcTy fam E ctorType pf x s = some Ac →
    idxSrcTy fam E ctorType (pf.map (lift c 1)) (lift c 1 x) s =
      some (lift c 1 Ac) := by
  intro x s
  induction s generalizing x with
  | pos i =>
      intro Ac h
      rcases idxSrcTy_pos_dom h with ⟨B, happ⟩
      have happ' := applyTel_congr_lift c 1 (pf.take i) happ
      -- map_take : (L.take i).map f = (L.map f).take i. happ' has the
      -- left side; idxSrcTy matches on the right side.
      rw [hctor, List.map_take] at happ'
      simp only [lift] at happ'
      simp only [idxSrcTy]
      rw [happ']
  | constField i =>
      intro Ac h
      rcases idxSrcTy_constField_dom h with ⟨r, ls, B, hx, happ⟩
      have happ' := applyTel_congr_lift c 1 (pf.take i) happ
      rw [hctor, List.map_take] at happ'
      simp only [lift] at happ'
      subst hx
      simp only [idxSrcTy, lift]
      rw [happ']
  | constNotFam r =>
      intro Ac h
      cases x with
      | const r' ls =>
          simp only [idxSrcTy, lift] at h ⊢
          cases hdec : (decide (r' = r) && decide (r ≠ fam)) with
          | false => simp only [hdec] at h; cases h
          | true =>
              simp only [hdec] at h ⊢
              cases hm : E.members r with
              | none => simp only [hm] at h; cases h
              | some m =>
                  simp only [hm] at h ⊢
                  cases hlen : decide (ls.length = m.arity) with
                  | false => simp only [hlen] at h; cases h
                  | true =>
                      -- `if` on Bool is `ite (b = true)`. After the
                      -- condition rewrites to `true`, that is `ite True`,
                      -- which does not iota-reduce.
                      simp only [hlen, if_true] at h ⊢
                      cases h
                      rw [lift_of_closed _
                        (instantiateLevels_closed0 ((hcl r m hm).1 0) ls)]
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | app sf sa ihsf ihsa =>
      intro Ac h
      cases x with
      | app f a =>
          cases hf : idxSrcTy fam E ctorType pf f sf with
          | none => simp only [idxSrcTy, hf] at h; cases h
          | some Tf =>
              cases ha : idxSrcTy fam E ctorType pf a sa with
              | none => simp only [idxSrcTy, hf, ha] at h; cases h
              | some Ta =>
                  cases Tf with
                  | pi A B =>
                      simp only [idxSrcTy, hf, ha] at h
                      by_cases hTA : Ta = A
                      · subst hTA
                        simp only [if_pos rfl] at h
                        cases h
                        have hf' := ihsf f (.pi Ta B) hf
                        have ha' := ihsa a Ta ha
                        simp only [lift] at hf'
                        simp only [idxSrcTy, lift, hf', ha', if_true]
                        rw [instantiate0_lift]
                      · simp only [if_neg hTA] at h
                        cases h
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                      simp only [idxSrcTy, hf, ha] at h
                      cases h
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | sort =>
      intro Ac h
      cases x with
      | sort u =>
          simp only [idxSrcTy, lift] at h ⊢
          cases h
          rfl
      | bvar _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | lit _ =>
      intro Ac h
      simp only [idxSrcTy] at h
      cases h

theorem idxSrcAlignGo_lift (fam c : Nat) (E : ResolvedEnv) (hcl : EnvClosed E)
    (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (recPre pf : List (Expr Nat)) :
    (pre xs : List (Expr Nat)) → (ss : List IdxSrc) →
    idxSrcAlignGo fam E recType ctorType recPre pf pre xs ss = true →
    idxSrcAlignGo fam E recType ctorType (recPre.map (lift c 1))
      (pf.map (lift c 1)) (pre.map (lift c 1)) (xs.map (lift c 1)) ss =
      true := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ss h
      cases ss with
      | nil => rfl
      | cons _ _ =>
          simp only [idxSrcAlignGo] at h
          nomatch h
  | cons x xs ih =>
      intro ss h
      cases ss with
      | nil =>
          simp only [idxSrcAlignGo] at h
          nomatch h
      | cons s ss =>
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [idxSrcAlignGo, happR] at h; nomatch h
          | some Ur =>
              cases Ur with
              | pi Ar Br =>
                  simp only [idxSrcAlignGo, happR] at h
                  cases hty : idxSrcTy fam E ctorType pf x s with
                  | none => simp only [hty] at h; nomatch h
                  | some Ac =>
                      simp only [hty] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happ' := applyTel_congr_lift c 1 (recPre ++ pre) happR
                      rw [hrecCl, List.map_append] at happ'
                      simp only [lift] at happ'
                      have hty' := idxSrcTy_lift fam c E hcl ctorType hctorCl
                        pf x s Ac hty
                      have heq' : decide (lift c 1 Ac = lift c 1 Ar) = true := by
                        rw [hAcAr]
                        exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) ss hrest
                      rw [List.map_append, List.map_cons, List.map_nil] at ih'
                      simp only [idxSrcAlignGo, List.map_append, List.map_cons,
                        List.map_nil, happ', hty', heq', ih']
                      rfl
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [idxSrcAlignGo, happR] at h
                  nomatch h

theorem idxSrcAlign_lift (fam c : Nat) (E : ResolvedEnv) (hcl : EnvClosed E)
    (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (recPre pf idx : List (Expr Nat)) (ss : List IdxSrc)
    (h : idxSrcAlign fam E recType ctorType recPre pf idx ss = true) :
    idxSrcAlign fam E recType ctorType (recPre.map (lift c 1))
      (pf.map (lift c 1)) (idx.map (lift c 1)) ss = true := by
  simp only [idxSrcAlign] at h ⊢
  have hgo := idxSrcAlignGo_lift fam c E hcl recType ctorType hrecCl hctorCl
    recPre pf [] idx ss h
  simp only [List.map_nil] at hgo
  exact hgo

theorem recIdxSrcWalk_lift (fam c nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List IdxSrc))
    (h : recIdxSrcWalk fam nparams pf ks T fs pss = true) :
    recIdxSrcWalk fam nparams (pf.map (lift c 1)) ks (lift c 1 T)
      (fs.map (lift c 1)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxSrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxSrcWalk, List.map_cons, lift] at h ⊢
                          rw [instantiate0_lift]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      simp only [recIdxSrcWalk, List.map_cons, lift] at h ⊢
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      have hzip' : idxSrcZip fam (pf.map (lift c 1))
                          (familyIdx nparams (lift c 1 A)) src = true := by
                        rw [hfi]
                        exact idxSrcZip_lift fam c 1 pf (familyIdx nparams A)
                          src hzip
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [instantiate0_lift]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h

theorem recIdxSrcFuelWalk_lift (n c nparams : Nat)
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List IdxSrc))
    (h : recIdxSrcFuelWalk n nparams ks T fs pss) :
    recIdxSrcFuelWalk n nparams ks (lift c 1 T) (fs.map (lift c 1)) pss := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs <;> cases pss <;> simp only [List.map_nil, List.map_cons,
        recIdxSrcFuelWalk]
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [List.map_nil, recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxSrcFuelWalk, List.map_cons, lift] at h ⊢
                          rw [instantiate0_lift]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxSrcFuelWalk]
          | bvar i =>
              by_cases hi : c ≤ i <;>
                simp only [lift, hi, ↓reduceIte, List.map, recIdxSrcFuelWalk]
          | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [lift, recIdxSrcFuelWalk]
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [List.map_nil, recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      simp only [recIdxSrcFuelWalk, List.map_cons, lift] at h ⊢
                      have hfi := familyIdx_lift c 1 nparams A
                      rw [hfi, instantiate0_lift]
                      exact ⟨idxSrcFuelList_lift n c (familyIdx nparams A) src h.1,
                        ih (instantiate0 f B) fs pss h.2⟩
          | bvar i =>
              by_cases hi : c ≤ i <;>
                simp only [lift, hi, ↓reduceIte, List.map, recIdxSrcFuelWalk]
          | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [lift, recIdxSrcFuelWalk]

theorem recIdxTySrcWalk_lift (fam c : Nat) (E : ResolvedEnv) (hcl : EnvClosed E)
    (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (nparams : Nat) (recPre pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List IdxSrc))
    (h : recIdxTySrcWalk fam E recType ctorType nparams recPre pf ks T fs pss =
      true) :
    recIdxTySrcWalk fam E recType ctorType nparams (recPre.map (lift c 1))
      (pf.map (lift c 1)) ks (lift c 1 T) (fs.map (lift c 1)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTySrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxTySrcWalk, List.map_cons, lift] at h ⊢
                          rw [instantiate0_lift]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      simp only [recIdxTySrcWalk, List.map_cons, lift] at h ⊢
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      have halign' : idxSrcAlign fam E recType ctorType
                          (recPre.map (lift c 1)) (pf.map (lift c 1))
                          (familyIdx nparams (lift c 1 A)) src = true := by
                        rw [hfi]
                        exact idxSrcAlign_lift fam c E hcl recType ctorType
                          hrecCl hctorCl recPre pf (familyIdx nparams A) src
                          halign
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [instantiate0_lift]
                      simp only [halign', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h

def liftTyping (c : Nat) {E : ResolvedEnv} (hcl : EnvClosed E)
    (w : IotaWitness E) (ty : IotaTyping E w) :
    IotaTyping E (liftWitness c w) where
  motive := lift c 1 ty.motive
  hmotive := by
    simp only [liftWitness]
    rw [List.getElem?_map, ty.hmotive]
    rfl
  mdom := lift c 1 ty.mdom
  restMin := lift (c + 1) 1 ty.restMin
  hminDom := by
    simp only [liftWitness]
    have htake :
        (w.preMajor.map (lift c 1)).take (w.nparams + 1 + w.ctorIdx) =
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx)).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor (w.nparams + 1 + w.ctorIdx)).symm
    rw [htake]
    have hcl : lift c 1 (instantiateLevels w.ls w.recMember.mtype) =
        instantiateLevels w.ls w.recMember.mtype :=
      lift_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) c 1
    have happ := applyTel_congr_lift c 1
      (w.preMajor.take (w.nparams + 1 + w.ctorIdx)) ty.hminDom
    rw [hcl] at happ
    rw [happ]
    rfl
  hfamSpine := by
    simp only [liftWitness]
    have htk :
        (w.preMajor.map (lift c 1)).take w.nparams =
          (w.preMajor.take w.nparams).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor w.nparams).symm
    rw [htk]
    exact directRecFamilySpine_lift c w.familyRef w.ls w.nparams
      (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams w.fields
      ty.hfamSpine
  hparamAlign := by
    simp only [liftWitness]
    have htk :
        (w.preMajor.map (lift c 1)).take w.nparams =
          (w.preMajor.take w.nparams).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor w.nparams).symm
    rw [htk]
    exact recCtorParamAlign_lift c
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (lift_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) c 1)
      (lift_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) c 1)
      (w.preMajor.take w.nparams) ty.hparamAlign
  hfamSpineExact := by
    simp only [liftWitness]
    have htk :
        (w.preMajor.map (lift c 1)).take w.nparams =
          (w.preMajor.take w.nparams).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor w.nparams).symm
    rw [htk]
    exact directRecFamilySpineExact_lift c w.familyRef
      (w.ls.take w.famMember.arity) w.nparams
      (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams w.fields
      ty.hfamSpineExact
  hctorResShape := ty.hctorResShape
  idxPositions := ty.idxPositions
  hidxWalk := by
    have hpf :
        recParamsFields (liftWitness c w) =
          (recParamsFields w).map (lift c 1) := by
      simp only [recParamsFields, liftWitness]
      rw [← List.map_take, List.map_append]
    rw [hpf]
    exact recIdxFromSpineWalk_lift w.familyRef c w.nparams w.nindices
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields ty.hidxWalk
  hidxPos := by
    have hpf :
        recParamsFields (liftWitness c w) =
          (recParamsFields w).map (lift c 1) := by
      simp only [recParamsFields, liftWitness]
      rw [← List.map_take, List.map_append]
    rw [hpf]
    exact recIdxSrcWalk_lift w.familyRef c w.nparams
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields
      ty.idxPositions ty.hidxPos
  hidxTy := by
    have hpf :
        recParamsFields (liftWitness c w) =
          (recParamsFields w).map (lift c 1) := by
      simp only [recParamsFields, liftWitness]
      rw [← List.map_take, List.map_append]
    have hpre :
        recPrefix (w.preMajor.map (lift c 1)) w.nparams w.nMinors =
          (recPrefix w.preMajor w.nparams w.nMinors).map (lift c 1) :=
      (List.map_take (lift c 1) w.preMajor (w.nparams + 1 + w.nMinors)).symm
    rw [hpf]
    simp only [liftWitness]
    rw [hpre]
    exact recIdxTySrcWalk_lift w.familyRef c E hcl
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (lift_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) c 1)
      (lift_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) c 1)
      w.nparams (recPrefix w.preMajor w.nparams w.nMinors)
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields
      ty.idxPositions ty.hidxTy
  hidxFuel := by
    intro n hraw
    simp only [liftWitness] at hraw ⊢
    exact recIdxSrcFuelWalk_lift n c w.nparams w.kinds
      w.ctorAfterParams w.fields ty.idxPositions (ty.hidxFuel n hraw)
  hminTel := by
    change lift c 1 ty.mdom = iotaMdom (liftWitness c w) (lift c 1 ty.motive)
    rw [iotaMdom_lift, ty.hminTel]

theorem instantiate0_instantiate (j : Nat) (s f B : Expr Nat) :
    instantiate j s (instantiate0 f B) =
      instantiate0 (instantiate j s f) (instantiate (j + 1) (lift 0 1 s) B) :=
  instantiate_instantiate 0 j f s (Nat.zero_le j) B

theorem recIdxFromSpineWalk_instantiate (fam j nparams nindices : Nat)
    (s : Expr Nat) (pf : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    recIdxFromSpineWalk fam nparams nindices pf ks T fs = true →
    recIdxFromSpineWalk fam nparams nindices (pf.map (instantiate j s)) ks
      (instantiate j s T) (fs.map (instantiate j s)) = true
  | [], _, _, _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, htel, hfam, h => by
      simp only [isPiTel, List.length_cons, recIdxFromSpineWalk,
        List.map_cons, instantiate, directRecConstHead] at htel hfam h ⊢
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hfam' :=
        directRecConstHead_instantiate 0 f ks B htel hfam
      have ih := recIdxFromSpineWalk_instantiate fam j nparams nindices s pf
        ks (instantiate0 f B) fs htel' hfam' h
      rw [← instantiate0_instantiate]
      exact ih
  | .directRec :: ks, .pi A B, f :: fs, htel, hfam, h => by
      simp only [isPiTel, List.length_cons, recIdxFromSpineWalk,
        List.map_cons, instantiate, directRecConstHead] at htel hfam h ⊢
      have ⟨hsc, hfamB⟩ := bool_and_true hfam
      have ⟨hlenall, hrest⟩ := bool_and_true h
      have ⟨hlen, hall⟩ := bool_and_true hlenall
      have hfi : familyIdx nparams (instantiate j s A) =
          (familyIdx nparams A).map (instantiate j s) := by
        simp only [spineHeadConst] at hsc
        cases hsp : (appsSpine A).1 with
        | const r ls =>
            exact familyIdx_instantiate_const j s nparams (by rw [hsp])
        | bvar _ => simp only [hsp] at hsc; nomatch hsc
        | sort _ => simp only [hsp] at hsc; nomatch hsc
        | app _ _ => simp only [hsp] at hsc; nomatch hsc
        | lam _ _ => simp only [hsp] at hsc; nomatch hsc
        | pi _ _ => simp only [hsp] at hsc; nomatch hsc
        | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
        | lit _ => simp only [hsp] at hsc; nomatch hsc
      have hlen' :
          decide ((familyIdx nparams (instantiate j s A)).length =
            nindices) = true := by
        rw [hfi, List.length_map]
        exact hlen
      have hall' : ((familyIdx nparams A).map (instantiate j s)).all
          (fun y => idxFamFree fam (pf.map (instantiate j s)) y) = true := by
        exact all_idxFamFree_map_instantiate fam j s
          (familyIdx nparams A) pf hall
      rw [← hfi] at hall'
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hfam' :=
        directRecConstHead_instantiate 0 f ks B htel hfamB
      have hrest' := recIdxFromSpineWalk_instantiate fam j nparams nindices s
        pf ks (instantiate0 f B) fs htel' hfam' hrest
      rw [← instantiate0_instantiate]
      simp only [hlen', hall', hrest']
      rfl
  | .plain :: _, .pi _ _, [], htel, _, _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, instantiate]
  | .directRec :: _, .pi _ _, [], htel, _, _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, instantiate]
  | .plain :: ks, .bvar _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .sort _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .const _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .app _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lam _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .letE _ _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lit _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .bvar _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .sort _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .const _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .app _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lam _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .letE _ _ _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lit _, _, htel, _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

theorem directRecFamilySpine_instantiate (j fam : Nat) (ls : List Level)
    (nparams : Nat) (s : Expr Nat) (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecFamilySpine fam ls nparams params ks T fs = true →
    directRecFamilySpine fam ls nparams (params.map (instantiate j s)) ks
      (instantiate j s T) (fs.map (instantiate j s)) = true
  | [], _, _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, htel, h => by
      simp only [isPiTel, List.length_cons, directRecFamilySpine,
        List.map_cons, instantiate] at htel h ⊢
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have ih := directRecFamilySpine_instantiate j fam ls nparams s params
        ks (instantiate0 f B) fs htel' h
      rw [← instantiate0_instantiate]
      exact ih
  | .directRec :: ks, .pi A B, f :: fs, htel, h => by
      simp only [isPiTel, List.length_cons, directRecFamilySpine,
        List.map_cons, instantiate] at htel h ⊢
      have ⟨hhead, hrest⟩ := bool_and_true h
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hrest' := directRecFamilySpine_instantiate j fam ls nparams s
        params ks (instantiate0 f B) fs htel' hrest
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          have hsp := appsSpine_instantiate_const j s r lsA A hconst
          rw [hsp]
          simp only [hconst] at hhead ⊢
          rw [hhead, ← instantiate0_instantiate]
          exact hrest'
      | bvar _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: _, .pi _ _, [], htel, _ => by
      simp only [directRecFamilySpine, List.map_nil, instantiate]
  | .directRec :: _, .pi _ _, [], htel, _ => by
      simp only [directRecFamilySpine, List.map_nil, instantiate]
  | .plain :: ks, .bvar _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .sort _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .const _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .app _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lam _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .letE _ _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lit _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .bvar _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .sort _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .const _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .app _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lam _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .letE _ _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lit _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

/-- 00 §20.5: the EXACT walk transports under `instantiate` on a
const-headed DirectRec domain (`appsSpine_instantiate_const`). -/
theorem directRecFamilySpineExact_instantiate (j fam : Nat) (ls : List Level)
    (nparams : Nat) (s : Expr Nat) (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    isPiTel ks.length T = true →
    directRecFamilySpineExact fam ls nparams params ks T fs = true →
    directRecFamilySpineExact fam ls nparams
      (params.map (instantiate j s)) ks
      (instantiate j s T) (fs.map (instantiate j s)) = true
  | [], _, _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, htel, h => by
      simp only [isPiTel, List.length_cons, directRecFamilySpineExact,
        List.map_cons, instantiate] at htel h ⊢
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have ih := directRecFamilySpineExact_instantiate j fam ls nparams s
        params ks (instantiate0 f B) fs htel' h
      rw [← instantiate0_instantiate]
      exact ih
  | .directRec :: ks, .pi A B, f :: fs, htel, h => by
      simp only [isPiTel, List.length_cons, directRecFamilySpineExact,
        List.map_cons, instantiate] at htel h ⊢
      have ⟨hh, hrest⟩ := bool_and_true h
      have ⟨hhead, htake⟩ := bool_and_true hh
      have hte : (appsSpine A).2.take nparams = params :=
        of_decide_eq_true htake
      have htake' :
          decide (((appsSpine A).2.map (instantiate j s)).take nparams =
            params.map (instantiate j s)) = true := by
        rw [← List.map_take, hte]
        exact decide_eq_true rfl
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hrest' := directRecFamilySpineExact_instantiate j fam ls nparams s
        params ks (instantiate0 f B) fs htel' hrest
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          have hsp := appsSpine_instantiate_const j s r lsA A hconst
          rw [hsp]
          simp only [hconst] at hhead ⊢
          rw [hhead, htake', ← instantiate0_instantiate]
          exact hrest'
      | bvar _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: _, .pi _ _, [], htel, _ => by
      simp only [directRecFamilySpineExact, List.map_nil, instantiate]
  | .directRec :: _, .pi _ _, [], htel, _ => by
      simp only [directRecFamilySpineExact, List.map_nil, instantiate]
  | .plain :: ks, .bvar _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .sort _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .const _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .app _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lam _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .letE _ _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: ks, .lit _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .bvar _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .sort _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .const _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .app _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lam _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .letE _ _ _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, .lit _, _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

/-- `familyIdx` instantiate is false on a bvar-hit (M-001). Gate on
`isPiTel` (telescope stays Π) and `directRecConstHead` (05 family apps). -/
theorem rhsArgs_instantiate (j nparams nMinors : Nat) (s rec : Expr Nat)
    (preMajor : List (Expr Nat)) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (T : Expr Nat) →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    (rhsArgs rec preMajor nparams nMinors fs ks T).map (instantiate j s) =
      rhsArgs (instantiate j s rec) (preMajor.map (instantiate j s))
        nparams nMinors (fs.map (instantiate j s)) ks (instantiate j s T)
  | [], _, T, _, _ => by simp only [rhsArgs, List.map_nil]
  | f :: fs, [], T, _, _ => by
      simp only [rhsArgs, List.map_cons]
      rw [rhsArgs_instantiate j nparams nMinors s rec preMajor fs [] T
        (isPiTel_zero T) rfl]
  | f :: fs, .plain :: ks, .pi A B, htel, hfam => by
      simp only [isPiTel, List.length_cons, directRecConstHead] at htel hfam
      simp only [rhsArgs, List.map_cons]
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hfam' :=
        directRecConstHead_instantiate 0 f ks B htel hfam
      rw [rhsArgs_instantiate j nparams nMinors s rec
        preMajor fs ks (instantiate0 f B) htel' hfam',
        instantiate0_instantiate]
  | f :: fs, .directRec :: ks, .pi A B, htel, hfam => by
      simp only [isPiTel, List.length_cons, directRecConstHead] at htel hfam
      have ⟨hscA, hfamB⟩ := bool_and_true hfam
      simp only [rhsArgs, List.map_cons]
      rw [recCallField_instantiate j s rec preMajor nparams nMinors f A hscA]
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hfam' :=
        directRecConstHead_instantiate 0 f ks B htel hfamB
      rw [rhsArgs_instantiate j nparams nMinors s rec
        preMajor fs ks (instantiate0 f B) htel' hfam',
        instantiate0_instantiate]
  | f :: fs, .plain :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .plain :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .bvar _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .sort _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .const _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .app _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .lam _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .letE _ _ _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | f :: fs, .directRec :: ks, .lit _, htel, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

def instWitness (j : Nat) (v : Expr Nat) {E : ResolvedEnv}
    (w : IotaWitness E) : IotaWitness E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor.map (instantiate j v)
  fields := w.fields.map (instantiate j v)
  ctorParams := w.ctorParams.map (instantiate j v)
  kinds := w.kinds
  minor := instantiate j v w.minor
  hlen := by
    simp only [List.length_map]
    exact w.hlen
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by
    simp only [List.length_map]
    exact w.hctorParams
  hnpar := by
    simp only [List.length_map]
    exact w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by
    simp only [List.length_map]
    exact w.hpre
  hminor := by
    rw [List.getElem?_map]
    rw [w.hminor]
    rfl
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by
    simp only [List.length_map]
    exact w.hpeel
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
  ctorAfterParams := instantiate j v w.ctorAfterParams
  hctorAfter := by
    have htake :
        (w.preMajor.map (instantiate j v)).take w.nparams =
          (w.preMajor.take w.nparams).map (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor w.nparams).symm
    rw [htake]
    have hcl : instantiate j v (instantiateLevels w.ls w.ctorMember.mtype) =
        instantiateLevels w.ls w.ctorMember.mtype :=
      instantiate_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) j v
    have happ := applyTel_congr_instantiate j v
      (w.preMajor.take w.nparams) w.hctorAfter
    rw [hcl] at happ
    exact happ
  hctorTel := isPiTel_instantiate j v w.kinds.length w.ctorAfterParams
    w.hctorTel
  hfamTel := directRecConstHead_instantiate j v w.kinds w.ctorAfterParams
    w.hctorTel w.hfamTel
  hresTel := resultConstHead_instantiate j v w.kinds w.ctorAfterParams
    w.hctorTel w.hresTel

theorem ctorMajor_instantiate {E : ResolvedEnv} (j : Nat) (s : Expr Nat)
    (w : IotaWitness E) :
    ctorMajor (instWitness j s w) = instantiate j s (ctorMajor w) := by
  change foldApps (.const w.ctorRef w.lsC)
      (w.ctorParams.map (instantiate j s) ++
        w.fields.map (instantiate j s)) =
    instantiate j s (foldApps (.const w.ctorRef w.lsC)
      (w.ctorParams ++ w.fields))
  rw [foldApps_instantiate, instantiate, List.map_append]

/-- 00 §20.5: recursor-side constructor application transports. -/
theorem ctorMajorRec_instantiate {E : ResolvedEnv} (j : Nat) (s : Expr Nat)
    (w : IotaWitness E) :
    ctorMajorRec (instWitness j s w) = instantiate j s (ctorMajorRec w) := by
  change foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      ((w.preMajor.map (instantiate j s)).take w.nparams ++
        w.fields.map (instantiate j s)) =
    instantiate j s (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams ++ w.fields))
  rw [foldApps_instantiate, instantiate, List.map_append,
    List.map_take (instantiate j s) w.preMajor w.nparams]

theorem iotaLhsOf_instantiate {E : ResolvedEnv} (j : Nat) (s : Expr Nat)
    (w : IotaWitness E) :
    iotaLhsOf (instWitness j s w) = instantiate j s (iotaLhsOf w) := by
  unfold iotaLhsOf
  rw [recCall_instantiate, ctorMajor_instantiate]
  simp only [instWitness, instantiate]

theorem iotaRhsOf_instantiate {E : ResolvedEnv} (j : Nat) (s : Expr Nat)
    (w : IotaWitness E) :
    iotaRhsOf (instWitness j s w) = instantiate j s (iotaRhsOf w) := by
  simp only [iotaRhsOf, instWitness, foldApps_instantiate]
  rw [rhsArgs_instantiate j w.nparams w.nMinors s (.const w.recRef w.ls)
    w.preMajor w.fields w.kinds w.ctorAfterParams w.hctorTel w.hfamTel]
  simp only [instantiate]

/-- F-05a: IotaSubst is a theorem over the 05 §11–12 relation. -/
def iotaSubst (E : ResolvedEnv) : IotaSubst E :=
  fun lhs rhs h v c =>
    match h with
    | .of w => by
        have h1 := iotaLhsOf_instantiate c v w
        have h2 := iotaRhsOf_instantiate c v w
        rw [← h1, ← h2]
        exact .of (instWitness c v w)

theorem iotaMdom_instantiate {E : ResolvedEnv} (j : Nat) (v : Expr Nat)
    (w : IotaWitness E) (motive : Expr Nat) :
    iotaMdom (instWitness j v w) (instantiate j v motive) =
      instantiate j v (iotaMdom w motive) := by
  have hmt := minorTel_instantiate_tel j v motive
    (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams))
    w.nparams w.kinds w.ctorAfterParams w.hctorTel w.hfamTel w.hresTel
  have hC :
      instantiate j v (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams)) =
      foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        ((w.preMajor.map (instantiate j v)).take w.nparams) := by
    rw [foldApps_instantiate, instantiate]
    have htake := List.map_take (instantiate j v) w.preMajor w.nparams
    rw [htake]
  simp only [iotaMdom, instWitness]
  rw [hmt, hC]


private theorem srcMembersClosed_of_subset {E : ResolvedEnv} {rs rs' : List Nat}
    (hsub : ∀ r, r ∈ rs' → r ∈ rs) (h : SrcMembersClosed E rs) :
    SrcMembersClosed E rs' := by
  intro r hr
  exact h r (hsub r hr)

private theorem srcMembersBounded_of_subset {E : ResolvedEnv} {rs rs' : List Nat}
    (hsub : ∀ r, r ∈ rs' → r ∈ rs) (h : SrcMembersBounded E rs) :
    SrcMembersBounded E rs' := by
  intro r hr
  exact h r (hsub r hr)

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcTy_instantiate (fam j : Nat) (v : Expr Nat) (E : ResolvedEnv)
    (ctorType : Expr Nat)
    (hctor : instantiate j v ctorType = ctorType) (pf : List (Expr Nat)) :
    (x : Expr Nat) → (s : IdxSrc) →
    SrcMembersClosed E (idxSrcConsts s) → (Ac : Expr Nat) →
    idxSrcTy fam E ctorType pf x s = some Ac →
    idxSrcTy fam E ctorType (pf.map (instantiate j v)) (instantiate j v x) s =
      some (instantiate j v Ac) := by
  intro x s hstable
  induction s generalizing x with
  | pos i =>
      intro Ac h
      rcases idxSrcTy_pos_dom h with ⟨B, happ⟩
      have happ' := applyTel_congr_instantiate j v (pf.take i) happ
      rw [hctor, List.map_take] at happ'
      simp only [instantiate] at happ'
      simp only [idxSrcTy]
      rw [happ']
  | constField i =>
      intro Ac h
      rcases idxSrcTy_constField_dom h with ⟨r, ls, B, hx, happ⟩
      have happ' := applyTel_congr_instantiate j v (pf.take i) happ
      rw [hctor, List.map_take] at happ'
      simp only [instantiate] at happ'
      subst hx
      simp only [idxSrcTy, instantiate]
      rw [happ']
  | constNotFam r =>
      intro Ac h
      cases x with
      | const r' ls =>
          simp only [idxSrcTy, instantiate] at h ⊢
          cases hdec : (decide (r' = r) && decide (r ≠ fam)) with
          | false => simp only [hdec] at h; cases h
          | true =>
              simp only [hdec] at h ⊢
              cases hm : E.members r with
              | none => simp only [hm] at h; cases h
              | some m =>
                  simp only [hm] at h ⊢
                  cases hlen : decide (ls.length = m.arity) with
                  | false => simp only [hlen] at h; cases h
                  | true =>
                      simp only [hlen, if_true] at h ⊢
                      cases h
                      have hmcl := hstable r (by
                        simp only [idxSrcConsts, List.mem_singleton]) m hm 0
                      rw [instantiate_of_closed _
                        (instantiateLevels_closed0 hmcl ls)]
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | app sf sa ihsf ihsa =>
      intro Ac h
      cases x with
      | app f a =>
          cases hf : idxSrcTy fam E ctorType pf f sf with
          | none => simp only [idxSrcTy, hf] at h; cases h
          | some Tf =>
              cases ha : idxSrcTy fam E ctorType pf a sa with
              | none => simp only [idxSrcTy, hf, ha] at h; cases h
              | some Ta =>
                  cases Tf with
                  | pi A B =>
                      simp only [idxSrcTy, hf, ha] at h
                      by_cases hTA : Ta = A
                      · subst hTA
                        simp only [if_pos rfl] at h
                        cases h
                        have hsf : SrcMembersClosed E (idxSrcConsts sf) :=
                          srcMembersClosed_of_subset (by
                            intro r hr
                            simp only [idxSrcConsts]
                            exact List.mem_append_left _ hr) hstable
                        have hsa : SrcMembersClosed E (idxSrcConsts sa) :=
                          srcMembersClosed_of_subset (by
                            intro r hr
                            simp only [idxSrcConsts]
                            exact List.mem_append_right _ hr) hstable
                        have hf' := ihsf f hsf (.pi Ta B) hf
                        have ha' := ihsa a hsa Ta ha
                        simp only [instantiate] at hf'
                        simp only [idxSrcTy, instantiate, hf', ha', if_true,
                          instantiate0]
                        rw [instantiate_instantiate 0 j a v (Nat.zero_le j)]
                      · simp only [if_neg hTA] at h
                        cases h
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                      simp only [idxSrcTy, hf, ha] at h
                      cases h
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | sort =>
      intro Ac h
      cases x with
      | sort u =>
          simp only [idxSrcTy, instantiate] at h ⊢
          cases h
          rfl
      | bvar _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | lit _ =>
      intro Ac h
      simp only [idxSrcTy] at h
      cases h

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcAlignGo_instantiate (fam j : Nat) (v : Expr Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat)
    (hrecCl : instantiate j v recType = recType)
    (hctorCl : instantiate j v ctorType = ctorType)
    (recPre pf : List (Expr Nat)) :
    (pre xs : List (Expr Nat)) → (ss : List IdxSrc) →
    SrcMembersClosed E (ss.flatMap idxSrcConsts) →
    idxSrcAlignGo fam E recType ctorType recPre pf pre xs ss = true →
    idxSrcAlignGo fam E recType ctorType (recPre.map (instantiate j v))
      (pf.map (instantiate j v)) (pre.map (instantiate j v))
      (xs.map (instantiate j v)) ss = true := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ss _ h
      cases ss with
      | nil => rfl
      | cons _ _ => simp only [idxSrcAlignGo] at h; nomatch h
  | cons x xs ih =>
      intro ss hstable h
      cases ss with
      | nil => simp only [idxSrcAlignGo] at h; nomatch h
      | cons s ss =>
          have hs : SrcMembersClosed E (idxSrcConsts s) :=
            srcMembersClosed_of_subset (by
              intro r hr
              simp only [List.flatMap_cons]
              exact List.mem_append_left _ hr) hstable
          have hss : SrcMembersClosed E (ss.flatMap idxSrcConsts) :=
            srcMembersClosed_of_subset (by
              intro r hr
              simp only [List.flatMap_cons]
              exact List.mem_append_right _ hr) hstable
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [idxSrcAlignGo, happR] at h; nomatch h
          | some Ur =>
              cases Ur with
              | pi Ar Br =>
                  simp only [idxSrcAlignGo, happR] at h
                  cases hty : idxSrcTy fam E ctorType pf x s with
                  | none => simp only [hty] at h; nomatch h
                  | some Ac =>
                      simp only [hty] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happ' := applyTel_congr_instantiate j v
                        (recPre ++ pre) happR
                      rw [hrecCl, List.map_append] at happ'
                      simp only [instantiate] at happ'
                      have hty' := idxSrcTy_instantiate fam j v E ctorType
                        hctorCl pf x s hs Ac hty
                      have heq' : decide (instantiate j v Ac =
                          instantiate j v Ar) = true := by
                        rw [hAcAr]
                        exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) ss hss hrest
                      rw [List.map_append, List.map_cons, List.map_nil] at ih'
                      simp only [idxSrcAlignGo, List.map_append, List.map_cons,
                        List.map_nil, happ', hty', heq', ih']
                      rfl
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [idxSrcAlignGo, happR] at h
                  nomatch h

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcAlign_instantiate (fam j : Nat) (v : Expr Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat)
    (hrecCl : instantiate j v recType = recType)
    (hctorCl : instantiate j v ctorType = ctorType)
    (recPre pf idx : List (Expr Nat)) (ss : List IdxSrc)
    (hstable : SrcMembersClosed E (ss.flatMap idxSrcConsts))
    (h : idxSrcAlign fam E recType ctorType recPre pf idx ss = true) :
    idxSrcAlign fam E recType ctorType (recPre.map (instantiate j v))
      (pf.map (instantiate j v)) (idx.map (instantiate j v)) ss = true := by
  simp only [idxSrcAlign] at h ⊢
  have hgo := idxSrcAlignGo_instantiate fam j v E recType ctorType
    hrecCl hctorCl recPre pf [] idx ss hstable h
  simp only [List.map_nil] at hgo
  exact hgo

theorem recIdxSrcWalk_instantiate (fam j nparams : Nat) (v : Expr Nat)
    (pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List IdxSrc))
    (htel : isPiTel ks.length T = true)
    (hfam : directRecConstHead ks T = true)
    (h : recIdxSrcWalk fam nparams pf ks T fs pss = true) :
    recIdxSrcWalk fam nparams (pf.map (instantiate j v)) ks
      (instantiate j v T) (fs.map (instantiate j v)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxSrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [isPiTel, List.length_cons, recIdxSrcWalk,
                            List.map_cons, instantiate, directRecConstHead]
                            at htel hfam h ⊢
                          have htel' := isPiTel_instantiate 0 f ks.length B htel
                          have hfam' :=
                            directRecConstHead_instantiate 0 f ks B htel hfam
                          have ih' := ih (instantiate0 f B) fs pss htel' hfam' h
                          rw [← instantiate0_instantiate]
                          exact ih'
                      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      simp only [isPiTel, List.length_cons, recIdxSrcWalk,
                        List.map_cons, instantiate, directRecConstHead]
                        at htel hfam h ⊢
                      have ⟨hsc, hfamB⟩ := bool_and_true hfam
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi : familyIdx nparams (instantiate j v A) =
                          (familyIdx nparams A).map (instantiate j v) := by
                        simp only [spineHeadConst] at hsc
                        cases hsp : (appsSpine A).1 with
                        | const r ls =>
                            exact familyIdx_instantiate_const j v nparams
                              (by rw [hsp])
                        | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
                            simp only [hsp] at hsc
                            nomatch hsc
                      have hzip' : idxSrcZip fam (pf.map (instantiate j v))
                          (familyIdx nparams (instantiate j v A)) src = true := by
                        rw [hfi]
                        exact idxSrcZip_instantiate fam j v pf
                          (familyIdx nparams A) src hzip
                      have htel' := isPiTel_instantiate 0 f ks.length B htel
                      have hfam' :=
                        directRecConstHead_instantiate 0 f ks B htel hfamB
                      have hrest' := ih (instantiate0 f B) fs pss htel' hfam' hrest
                      rw [← instantiate0_instantiate]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h

theorem recIdxSrcFuelWalk_instantiate (fam j n nparams : Nat)
    (v : Expr Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List IdxSrc))
    (htel : isPiTel ks.length T = true)
    (hfam : directRecConstHead ks T = true)
    (hpos : recIdxSrcWalk fam nparams pf ks T fs pss = true)
    (hfuel : recIdxSrcFuelWalk n nparams ks T fs pss) :
    recIdxSrcFuelWalk n nparams ks (instantiate j v T)
      (fs.map (instantiate j v)) pss := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs <;> cases pss <;> simp only [List.map_nil, List.map_cons,
        recIdxSrcFuelWalk]
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [List.map_nil, recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [isPiTel, List.length_cons, recIdxSrcWalk,
                            recIdxSrcFuelWalk, List.map_cons, instantiate,
                            directRecConstHead] at htel hfam hpos hfuel ⊢
                          have htel' := isPiTel_instantiate 0 f ks.length B htel
                          have hfam' :=
                            directRecConstHead_instantiate 0 f ks B htel hfam
                          have ih' := ih (instantiate0 f B) fs pss htel' hfam'
                            hpos hfuel
                          rw [← instantiate0_instantiate]
                          exact ih'
                      | cons _ _ =>
                          simp only [recIdxSrcWalk] at hpos
                          nomatch hpos
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [isPiTel, List.length_cons] at htel
              nomatch htel
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => exact True.intro
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at hpos; nomatch hpos
                  | cons src pss =>
                      simp only [isPiTel, List.length_cons, recIdxSrcWalk,
                        recIdxSrcFuelWalk, List.map_cons, instantiate,
                        directRecConstHead] at htel hfam hpos hfuel ⊢
                      have ⟨hsc, hfamB⟩ := bool_and_true hfam
                      have ⟨hzip, hpos'⟩ := bool_and_true hpos
                      have hfi : familyIdx nparams (instantiate j v A) =
                          (familyIdx nparams A).map (instantiate j v) := by
                        simp only [spineHeadConst] at hsc
                        cases hsp : (appsSpine A).1 with
                        | const r ls =>
                            exact familyIdx_instantiate_const j v nparams
                              (by rw [hsp])
                        | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
                            simp only [hsp] at hsc
                            nomatch hsc
                      have htel' := isPiTel_instantiate 0 f ks.length B htel
                      have hfam' :=
                        directRecConstHead_instantiate 0 f ks B htel hfamB
                      have hrest' := ih (instantiate0 f B) fs pss htel' hfam'
                        hpos' hfuel.2
                      rw [hfi, ← instantiate0_instantiate]
                      exact ⟨idxSrcFuelList_instantiate fam j n pf v
                        (familyIdx nparams A) src hzip hfuel.1, hrest'⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [isPiTel, List.length_cons] at htel
              nomatch htel

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem recIdxTySrcWalk_instantiate (fam j : Nat) (v : Expr Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat)
    (hrecCl : instantiate j v recType = recType)
    (hctorCl : instantiate j v ctorType = ctorType)
    (nparams : Nat) (recPre pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List IdxSrc))
    (hstable : SrcMembersClosed E (idxSrcConstsAll pss))
    (htel : isPiTel ks.length T = true)
    (hfam : directRecConstHead ks T = true)
    (h : recIdxTySrcWalk fam E recType ctorType nparams recPre pf ks T fs pss =
      true) :
    recIdxTySrcWalk fam E recType ctorType nparams
      (recPre.map (instantiate j v)) (pf.map (instantiate j v)) ks
      (instantiate j v T) (fs.map (instantiate j v)) pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTySrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      have htail : SrcMembersClosed E (idxSrcConstsAll pss) :=
                        srcMembersClosed_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_right _ hr) hstable
                      cases src with
                      | nil =>
                          simp only [isPiTel, List.length_cons, recIdxTySrcWalk,
                            List.map_cons, instantiate, directRecConstHead]
                            at htel hfam h ⊢
                          have htel' := isPiTel_instantiate 0 f ks.length B htel
                          have hfam' :=
                            directRecConstHead_instantiate 0 f ks B htel hfam
                          have ih' := ih (instantiate0 f B) fs pss htail htel'
                            hfam' h
                          rw [← instantiate0_instantiate]
                          exact ih'
                      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      have hsrc : SrcMembersClosed E (src.flatMap idxSrcConsts) :=
                        srcMembersClosed_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_left _ hr) hstable
                      have htail : SrcMembersClosed E (idxSrcConstsAll pss) :=
                        srcMembersClosed_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_right _ hr) hstable
                      simp only [isPiTel, List.length_cons, recIdxTySrcWalk,
                        List.map_cons, instantiate, directRecConstHead]
                        at htel hfam h ⊢
                      have ⟨hsc, hfamB⟩ := bool_and_true hfam
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi : familyIdx nparams (instantiate j v A) =
                          (familyIdx nparams A).map (instantiate j v) := by
                        simp only [spineHeadConst] at hsc
                        cases hsp : (appsSpine A).1 with
                        | const r ls =>
                            exact familyIdx_instantiate_const j v nparams
                              (by rw [hsp])
                        | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
                            simp only [hsp] at hsc
                            nomatch hsc
                      have halign' : idxSrcAlign fam E recType ctorType
                          (recPre.map (instantiate j v))
                          (pf.map (instantiate j v))
                          (familyIdx nparams (instantiate j v A)) src = true := by
                        rw [hfi]
                        exact idxSrcAlign_instantiate fam j v E recType
                          ctorType hrecCl hctorCl recPre pf
                          (familyIdx nparams A) src hsrc halign
                      have htel' := isPiTel_instantiate 0 f ks.length B htel
                      have hfam' :=
                        directRecConstHead_instantiate 0 f ks B htel hfamB
                      have hrest' := ih (instantiate0 f B) fs pss htail htel'
                        hfam' hrest
                      rw [← instantiate0_instantiate]
                      simp only [halign', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h

def instTyping (j : Nat) (v : Expr Nat) {E : ResolvedEnv} (hcl : EnvClosed E)
    (w : IotaWitness E) (ty : IotaTyping E w) :
    IotaTyping E (instWitness j v w) where
  motive := instantiate j v ty.motive
  hmotive := by
    simp only [instWitness]
    rw [List.getElem?_map, ty.hmotive]
    rfl
  mdom := instantiate j v ty.mdom
  restMin := instantiate (j + 1) (lift 0 1 v) ty.restMin
  hminDom := by
    simp only [instWitness]
    have htake :
        (w.preMajor.map (instantiate j v)).take (w.nparams + 1 + w.ctorIdx) =
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx)).map
            (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor
        (w.nparams + 1 + w.ctorIdx)).symm
    rw [htake]
    have hcl : instantiate j v (instantiateLevels w.ls w.recMember.mtype) =
        instantiateLevels w.ls w.recMember.mtype :=
      instantiate_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) j v
    have happ := applyTel_congr_instantiate j v
      (w.preMajor.take (w.nparams + 1 + w.ctorIdx)) ty.hminDom
    rw [hcl] at happ
    rw [happ]
    rfl
  hfamSpine := by
    simp only [instWitness]
    have htk :
        (w.preMajor.map (instantiate j v)).take w.nparams =
          (w.preMajor.take w.nparams).map (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor w.nparams).symm
    rw [htk]
    exact directRecFamilySpine_instantiate j w.familyRef w.ls w.nparams v
      (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams w.fields
      w.hctorTel ty.hfamSpine
  hparamAlign := by
    simp only [instWitness]
    have htk :
        (w.preMajor.map (instantiate j v)).take w.nparams =
          (w.preMajor.take w.nparams).map (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor w.nparams).symm
    rw [htk]
    exact recCtorParamAlign_instantiate j v
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (instantiate_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) j v)
      (instantiate_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) j v)
      (w.preMajor.take w.nparams) ty.hparamAlign
  hfamSpineExact := by
    simp only [instWitness]
    have htk :
        (w.preMajor.map (instantiate j v)).take w.nparams =
          (w.preMajor.take w.nparams).map (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor w.nparams).symm
    rw [htk]
    exact directRecFamilySpineExact_instantiate j w.familyRef
      (w.ls.take w.famMember.arity) w.nparams
      v (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams w.fields
      w.hctorTel ty.hfamSpineExact
  hctorResShape := ty.hctorResShape
  idxPositions := ty.idxPositions
  hidxWalk := by
    have hpf :
        recParamsFields (instWitness j v w) =
          (recParamsFields w).map (instantiate j v) := by
      simp only [recParamsFields, instWitness]
      rw [← List.map_take, List.map_append]
    rw [hpf]
    exact recIdxFromSpineWalk_instantiate w.familyRef j w.nparams w.nindices v
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields
      w.hctorTel w.hfamTel ty.hidxWalk
  hidxPos := by
    have hpf :
        recParamsFields (instWitness j v w) =
          (recParamsFields w).map (instantiate j v) := by
      simp only [recParamsFields, instWitness]
      rw [← List.map_take, List.map_append]
    rw [hpf]
    exact recIdxSrcWalk_instantiate w.familyRef j w.nparams v
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields
      ty.idxPositions w.hctorTel w.hfamTel ty.hidxPos
  hidxTy := by
    have hpf :
        recParamsFields (instWitness j v w) =
          (recParamsFields w).map (instantiate j v) := by
      simp only [recParamsFields, instWitness]
      rw [← List.map_take, List.map_append]
    have hpre :
        recPrefix (w.preMajor.map (instantiate j v)) w.nparams w.nMinors =
          (recPrefix w.preMajor w.nparams w.nMinors).map (instantiate j v) :=
      (List.map_take (instantiate j v) w.preMajor
        (w.nparams + 1 + w.nMinors)).symm
    rw [hpf]
    simp only [instWitness]
    rw [hpre]
    exact recIdxTySrcWalk_instantiate w.familyRef j v E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (instantiate_of_closed _ (instantiateLevels_closed0 w.hrecClosed w.ls) j v)
      (instantiate_of_closed _ (instantiateLevels_closed0 w.hctorClosed w.ls) j v)
      w.nparams (recPrefix w.preMajor w.nparams w.nMinors)
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields
      ty.idxPositions (srcMembersClosed_of_envClosed hcl)
      w.hctorTel w.hfamTel ty.hidxTy
  hidxFuel := by
    intro n hraw
    simp only [instWitness] at hraw ⊢
    exact recIdxSrcFuelWalk_instantiate w.familyRef j n w.nparams v
      (recParamsFields w) w.kinds w.ctorAfterParams w.fields ty.idxPositions
      w.hctorTel w.hfamTel ty.hidxPos (ty.hidxFuel n hraw)
  hminTel := by
    change instantiate j v ty.mdom =
      iotaMdom (instWitness j v w) (instantiate j v ty.motive)
    rw [iotaMdom_instantiate, ty.hminTel]

def extWitness {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitness E) : IotaWitness E' where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := hext w.recRef w.recMember w.hrec
  hctor := hext w.ctorRef w.ctorMember w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor
  fields := w.fields
  ctorParams := w.ctorParams
  kinds := w.kinds
  minor := w.minor
  hlen := w.hlen
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := hext w.familyRef w.famMember w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := w.hctorParams
  hnpar := w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := w.hpre
  hminor := w.hminor
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := w.hpeel
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
  ctorAfterParams := w.ctorAfterParams
  hctorAfter := w.hctorAfter
  hctorTel := w.hctorTel
  hfamTel := w.hfamTel
  hresTel := w.hresTel

theorem iotaLhsOf_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitness E) :
    iotaLhsOf (extWitness hext w) = iotaLhsOf w := rfl

theorem iotaRhsOf_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitness E) :
    iotaRhsOf (extWitness hext w) = iotaRhsOf w := rfl

theorem idxSrcTy_hext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) (ctorType : Expr Nat) (pf : List (Expr Nat)) :
    (x : Expr Nat) → (s : IdxSrc) → (Ac : Expr Nat) →
    idxSrcTy fam E ctorType pf x s = some Ac →
    idxSrcTy fam E' ctorType pf x s = some Ac := by
  intro x s
  induction s generalizing x with
  | pos _ =>
      intro Ac h
      simpa only [idxSrcTy] using h
  | constField i =>
      intro Ac h
      -- eq_2 / eq_3 split on whether `x` is a constant, so a variable
      -- `x` does not reduce. Neither branch reads `E`.
      cases x with
      | const _ _ =>
          simp only [idxSrcTy] at h ⊢
          exact h
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | sort =>
      intro Ac h
      cases x with
      | sort _ =>
          simp only [idxSrcTy] at h ⊢
          exact h
      | bvar _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | lit _ =>
      intro Ac h
      simp only [idxSrcTy] at h
      cases h
  | constNotFam r =>
      intro Ac h
      cases x with
      | const r' ls =>
          simp only [idxSrcTy] at h ⊢
          cases hdec : (decide (r' = r) && decide (r ≠ fam)) with
          | false => simp only [hdec] at h; cases h
          | true =>
              simp only [hdec] at h ⊢
              cases hm : E.members r with
              | none => simp only [hm] at h; cases h
              | some m =>
                  have hm' := hext r m hm
                  simp only [hm, hm'] at h ⊢
                  cases hlen : decide (ls.length = m.arity) with
                  | false => simp only [hlen] at h; cases h
                  | true => simp only [hlen] at h ⊢; exact h
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | app sf sa ihsf ihsa =>
      intro Ac h
      cases x with
      | app f a =>
          cases hf : idxSrcTy fam E ctorType pf f sf with
          | none => simp only [idxSrcTy, hf] at h; cases h
          | some Tf =>
              cases ha : idxSrcTy fam E ctorType pf a sa with
              | none => simp only [idxSrcTy, hf, ha] at h; cases h
              | some Ta =>
                  cases Tf with
                  | pi A B =>
                      simp only [idxSrcTy, hf, ha] at h
                      by_cases hTA : Ta = A
                      · subst hTA
                        simp only [if_pos rfl] at h
                        cases h
                        have hf' := ihsf f (.pi Ta B) hf
                        have ha' := ihsa a Ta ha
                        simp only [idxSrcTy, hf', ha', if_true]
                      · simp only [if_neg hTA] at h
                        cases h
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                      simp only [idxSrcTy, hf, ha] at h
                      cases h
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h

theorem idxSrcAlignGo_hext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) (recType ctorType : Expr Nat) (recPre pf : List (Expr Nat)) :
    (pre xs : List (Expr Nat)) → (ss : List IdxSrc) →
    idxSrcAlignGo fam E recType ctorType recPre pf pre xs ss = true →
    idxSrcAlignGo fam E' recType ctorType recPre pf pre xs ss = true := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ss h
      cases ss with
      | nil => rfl
      | cons _ _ => simp only [idxSrcAlignGo] at h; nomatch h
  | cons x xs ih =>
      intro ss h
      cases ss with
      | nil => simp only [idxSrcAlignGo] at h; nomatch h
      | cons s ss =>
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [idxSrcAlignGo, happR] at h; nomatch h
          | some Ur =>
              cases Ur with
              | pi Ar _ =>
                  simp only [idxSrcAlignGo, happR] at h
                  cases hty : idxSrcTy fam E ctorType pf x s with
                  | none => simp only [hty] at h; nomatch h
                  | some Ac =>
                      simp only [hty] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hty' := idxSrcTy_hext hext fam ctorType pf x s Ac hty
                      have ih' := ih (pre ++ [x]) ss hrest
                      simp only [idxSrcAlignGo, happR, hty', heq, ih']
                      rfl
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [idxSrcAlignGo, happR] at h
                  nomatch h

theorem idxSrcAlign_hext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) (recType ctorType : Expr Nat)
    (recPre pf idx : List (Expr Nat)) (ss : List IdxSrc)
    (h : idxSrcAlign fam E recType ctorType recPre pf idx ss = true) :
    idxSrcAlign fam E' recType ctorType recPre pf idx ss = true := by
  simp only [idxSrcAlign] at h ⊢
  exact idxSrcAlignGo_hext hext fam recType ctorType recPre pf [] idx ss h

theorem recIdxTySrcWalk_hext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) (recType ctorType : Expr Nat) (nparams : Nat)
    (recPre pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List IdxSrc))
    (h : recIdxTySrcWalk fam E recType ctorType nparams recPre pf ks T fs pss =
      true) :
    recIdxTySrcWalk fam E' recType ctorType nparams recPre pf ks T fs pss =
      true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTySrcWalk]
          | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi _ B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxTySrcWalk] at h ⊢
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      simp only [recIdxTySrcWalk, Bool.and_eq_true] at h ⊢
                      exact ⟨idxSrcAlign_hext hext fam recType ctorType recPre pf
                          (familyIdx nparams A) src h.1,
                        ih (instantiate0 f B) fs pss h.2⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h

def extTyping {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (w : IotaWitness E) (ty : IotaTyping E w) :
    IotaTyping E' (extWitness hext w) where
  motive := ty.motive
  hmotive := ty.hmotive
  mdom := ty.mdom
  restMin := ty.restMin
  hminDom := ty.hminDom
  hfamSpine := ty.hfamSpine
  hparamAlign := ty.hparamAlign
  hfamSpineExact := ty.hfamSpineExact
  hctorResShape := ty.hctorResShape
  idxPositions := ty.idxPositions
  hidxWalk := ty.hidxWalk
  hidxPos := ty.hidxPos
  hidxTy := recIdxTySrcWalk_hext hext w.familyRef
    (instantiateLevels w.ls w.recMember.mtype)
    (instantiateLevels w.ls w.ctorMember.mtype) w.nparams
    (recPrefix w.preMajor w.nparams w.nMinors) (recParamsFields w) w.kinds
    w.ctorAfterParams w.fields ty.idxPositions ty.hidxTy
  hidxFuel := ty.hidxFuel
  hminTel := ty.hminTel

theorem instLevel_instLevel (lvls ms : List Level) :
    (l : Level) → levelBounded ms.length l = true →
    instLevel lvls (instLevel ms l) = instLevel (ms.map (instLevel lvls)) l
  | .zero, _ => rfl
  | .succ l, h => by
      simp only [instLevel_succ, instLevel_instLevel lvls ms l h]
  | .max a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      simp only [instLevel_max, instLevel_instLevel lvls ms a h.1,
        instLevel_instLevel lvls ms b h.2]
  | .imax a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      simp only [instLevel_imax, instLevel_instLevel lvls ms a h.1,
        instLevel_instLevel lvls ms b h.2]
  | .param i, h => by
      have hi : i < ms.length := of_decide_eq_true h
      rw [instLevel_param, instLevel_param, List.getElem?_map,
        List.getElem?_eq_getElem hi]
      rfl

theorem map_instLevel_instLevel (lvls ms : List Level) :
    (ns : List Level) → levelsBounded ms.length ns = true →
    (ns.map (instLevel ms)).map (instLevel lvls) =
      ns.map (instLevel (ms.map (instLevel lvls)))
  | [], _ => rfl
  | l :: t, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h
      simp only [List.map, instLevel_instLevel lvls ms l h.1,
        map_instLevel_instLevel lvls ms t h.2]

theorem instantiateLevels_compose (lvls ms : List Level) :
    (e : Expr Nat) → exprLevelsBounded ms.length e = true →
    instantiateLevels lvls (instantiateLevels ms e) =
      instantiateLevels (ms.map (instLevel lvls)) e
  | .bvar _, _ => rfl
  | .sort l, h => by
      simp only [instantiateLevels, instLevel_instLevel lvls ms l h]
  | .const _ ns, h => by
      simp only [instantiateLevels, map_instLevel_instLevel lvls ms ns h]
  | .app f x, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      simp only [instantiateLevels, instantiateLevels_compose lvls ms f h.1,
        instantiateLevels_compose lvls ms x h.2]
  | .lam a b, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      simp only [instantiateLevels, instantiateLevels_compose lvls ms a h.1,
        instantiateLevels_compose lvls ms b h.2]
  | .pi a b, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      simp only [instantiateLevels, instantiateLevels_compose lvls ms a h.1,
        instantiateLevels_compose lvls ms b h.2]
  | .letE a v b, h => by
      simp only [exprLevelsBounded] at h
      have hab := boolAnd_left h
      have hbnd := boolAnd_right h
      simp only [instantiateLevels,
        instantiateLevels_compose lvls ms a (boolAnd_left hab),
        instantiateLevels_compose lvls ms v (boolAnd_right hab),
        instantiateLevels_compose lvls ms b hbnd]
  | .lit _, _ => rfl

/-- Level instantiation of a source type. The localized stability premise's level-boundedness component makes the two level substitutions compose.

SEALED STATEMENT CHANGE (IDX-R2 S1-c): the `hopen` premise is dropped, since idxSrcTy no longer tests openness; strictly stronger.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcTy_instantiateLevels (lvls : List Level) (fam : Nat)
    (E : ResolvedEnv) (ctorType : Expr Nat) (pf : List (Expr Nat)) :
    (x : Expr Nat) → (s : IdxSrc) →
    SrcMembersBounded E (idxSrcConsts s) → (Ac : Expr Nat) →
    idxSrcTy fam E ctorType pf x s = some Ac →
    idxSrcTy fam E (instantiateLevels lvls ctorType)
      (pf.map (instantiateLevels lvls)) (instantiateLevels lvls x) s =
      some (instantiateLevels lvls Ac) := by
  intro x s hstable
  induction s generalizing x with
  | pos i =>
      intro Ac h
      rcases idxSrcTy_pos_dom h with ⟨B, happ⟩
      have happ' :
          applyTel ((pf.map (instantiateLevels lvls)).take i)
            (instantiateLevels lvls ctorType) =
          some (.pi (instantiateLevels lvls Ac)
            (instantiateLevels lvls B)) := by
        rw [← List.map_take, applyTel_instantiateLevels, happ]
        simp only [instantiateLevels, Option.map_some']
      simp only [idxSrcTy]
      rw [happ']
  | constField i =>
      intro Ac h
      rcases idxSrcTy_constField_dom h with ⟨r, ls, B, hx, happ⟩
      have happ' :
          applyTel ((pf.map (instantiateLevels lvls)).take i)
            (instantiateLevels lvls ctorType) =
          some (.pi (instantiateLevels lvls Ac)
            (instantiateLevels lvls B)) := by
        rw [← List.map_take, applyTel_instantiateLevels, happ]
        simp only [instantiateLevels, Option.map_some']
      subst hx
      simp only [idxSrcTy, instantiateLevels]
      rw [happ']
  | constNotFam r =>
      intro Ac h
      cases x with
      | const r' ls =>
          simp only [idxSrcTy, instantiateLevels] at h ⊢
          cases hdec : (decide (r' = r) && decide (r ≠ fam)) with
          | false => simp only [hdec] at h; cases h
          | true =>
              simp only [hdec] at h ⊢
              cases hm : E.members r with
              | none => simp only [hm] at h; cases h
              | some m =>
                  simp only [hm] at h ⊢
                  cases hlen : decide (ls.length = m.arity) with
                  | false => simp only [hlen] at h; cases h
                  | true =>
                      simp only [hlen, if_true] at h
                      cases h
                      have hlenEq : ls.length = m.arity :=
                        of_decide_eq_true hlen
                      -- `decide (n = n)` does not reduce for a variable `n`.
                      have hdec' :
                          decide ((ls.map (instLevel lvls)).length = m.arity) =
                            true := by
                        rw [List.length_map, hlenEq,
                          decide_eq_true (rfl : m.arity = m.arity)]
                      have hb : exprLevelsBounded ls.length m.mtype = true := by
                        rw [hlenEq]
                        exact hstable r (by
                          simp only [idxSrcConsts, List.mem_singleton]) m hm
                      simp only [hdec', if_true]
                      rw [← instantiateLevels_compose lvls ls m.mtype hb]
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | app sf sa ihsf ihsa =>
      intro Ac h
      cases x with
      | app f a =>
          cases hf : idxSrcTy fam E ctorType pf f sf with
          | none => simp only [idxSrcTy, hf] at h; cases h
          | some Tf =>
              cases ha : idxSrcTy fam E ctorType pf a sa with
              | none => simp only [idxSrcTy, hf, ha] at h; cases h
              | some Ta =>
                  cases Tf with
                  | pi A B =>
                      simp only [idxSrcTy, hf, ha] at h
                      by_cases hTA : Ta = A
                      · subst hTA
                        simp only [if_pos rfl] at h
                        cases h
                        have hsf : SrcMembersBounded E (idxSrcConsts sf) :=
                          srcMembersBounded_of_subset (by
                            intro r hr
                            simp only [idxSrcConsts]
                            exact List.mem_append_left _ hr) hstable
                        have hsa : SrcMembersBounded E (idxSrcConsts sa) :=
                          srcMembersBounded_of_subset (by
                            intro r hr
                            simp only [idxSrcConsts]
                            exact List.mem_append_right _ hr) hstable
                        have hf' := ihsf f hsf (.pi Ta B) hf
                        have ha' := ihsa a hsa Ta ha
                        simp only [instantiateLevels] at hf'
                        simp only [idxSrcTy, instantiateLevels, hf', ha',
                          if_true]
                        rw [instantiateLevels_instantiate0]
                      · simp only [if_neg hTA] at h
                        cases h
                  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                      simp only [idxSrcTy, hf, ha] at h
                      cases h
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | sort =>
      intro Ac h
      cases x with
      | sort u =>
          simp only [idxSrcTy, instantiateLevels, instLevel_succ] at h ⊢
          cases h
          rfl
      | bvar _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at h
          cases h
  | lit _ =>
      intro Ac h
      simp only [idxSrcTy] at h
      cases h

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-c): the `hopen` premise is dropped, since idxSrcTy no longer tests openness; strictly stronger.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcAlignGo_instantiateLevels (lvls : List Level) (fam : Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat) (recPre pf : List (Expr Nat)) :
    (pre xs : List (Expr Nat)) → (ss : List IdxSrc) →
    SrcMembersBounded E (ss.flatMap idxSrcConsts) →
    idxSrcAlignGo fam E recType ctorType recPre pf pre xs ss = true →
    idxSrcAlignGo fam E (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType) (recPre.map (instantiateLevels lvls))
      (pf.map (instantiateLevels lvls)) (pre.map (instantiateLevels lvls))
      (xs.map (instantiateLevels lvls)) ss = true := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ss _ h
      cases ss with
      | nil => rfl
      | cons _ _ => simp only [idxSrcAlignGo] at h; nomatch h
  | cons x xs ih =>
      intro ss hstable h
      cases ss with
      | nil => simp only [idxSrcAlignGo] at h; nomatch h
      | cons s ss =>
          have hs : SrcMembersBounded E (idxSrcConsts s) :=
            srcMembersBounded_of_subset (by
              intro r hr
              simp only [List.flatMap_cons]
              exact List.mem_append_left _ hr) hstable
          have hss : SrcMembersBounded E (ss.flatMap idxSrcConsts) :=
            srcMembersBounded_of_subset (by
              intro r hr
              simp only [List.flatMap_cons]
              exact List.mem_append_right _ hr) hstable
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [idxSrcAlignGo, happR] at h; nomatch h
          | some Ur =>
              cases Ur with
              | pi Ar Br =>
                  simp only [idxSrcAlignGo, happR] at h
                  cases hty : idxSrcTy fam E ctorType pf x s with
                  | none => simp only [hty] at h; nomatch h
                  | some Ac =>
                      simp only [hty] at h
                      have ⟨heq, hrest⟩ := bool_and_true h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happ' :
                          applyTel (recPre.map (instantiateLevels lvls) ++
                              pre.map (instantiateLevels lvls))
                            (instantiateLevels lvls recType) =
                          some (.pi (instantiateLevels lvls Ar)
                            (instantiateLevels lvls Br)) := by
                        rw [← List.map_append, applyTel_instantiateLevels, happR]
                        simp only [instantiateLevels, Option.map_some']
                      have hty' := idxSrcTy_instantiateLevels lvls fam E
                        ctorType pf x s hs Ac hty
                      have heq' : decide (instantiateLevels lvls Ac =
                          instantiateLevels lvls Ar) = true := by
                        rw [hAcAr]
                        exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) ss hss hrest
                      rw [List.map_append, List.map_cons, List.map_nil] at ih'
                      simp only [idxSrcAlignGo, happ', hty', heq', ih']
                      rfl
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [idxSrcAlignGo, happR] at h
                  nomatch h

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-c): the `hopen` premise is dropped, since idxSrcTy no longer tests openness; strictly stronger.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem idxSrcAlign_instantiateLevels (lvls : List Level) (fam : Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat) (recPre pf idx : List (Expr Nat))
    (ss : List IdxSrc) (hstable : SrcMembersBounded E (ss.flatMap idxSrcConsts))
    (h : idxSrcAlign fam E recType ctorType recPre pf idx ss = true) :
    idxSrcAlign fam E (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType) (recPre.map (instantiateLevels lvls))
      (pf.map (instantiateLevels lvls)) (idx.map (instantiateLevels lvls)) ss =
      true := by
  simp only [idxSrcAlign] at h ⊢
  have hgo := idxSrcAlignGo_instantiateLevels lvls fam E recType
    ctorType recPre pf [] idx ss hstable h
  simp only [List.map_nil] at hgo
  exact hgo

theorem recIdxSrcWalk_instantiateLevels (lvls : List Level) (fam nparams : Nat)
    (pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List IdxSrc))
    (h : recIdxSrcWalk fam nparams pf ks T fs pss = true) :
    recIdxSrcWalk fam nparams (pf.map (instantiateLevels lvls)) ks
      (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) pss =
      true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxSrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi _ B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxSrcWalk, List.map_cons,
                            instantiateLevels] at h ⊢
                          rw [← instantiateLevels_instantiate0]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxSrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcWalk] at h; nomatch h
                  | cons src pss =>
                      simp only [recIdxSrcWalk, List.map_cons,
                        instantiateLevels] at h ⊢
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_instantiateLevels lvls nparams A
                      have hzip' : idxSrcZip fam
                          (pf.map (instantiateLevels lvls))
                          (familyIdx nparams (instantiateLevels lvls A)) src =
                          true := by
                        rw [hfi]
                        exact idxSrcZip_instantiateLevels fam lvls pf
                          (familyIdx nparams A) src hzip
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [← instantiateLevels_instantiate0]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcWalk] at h
              nomatch h

/-- SEALED STATEMENT CHANGE (IDX-R2 S1-c): the `hopen` premise is dropped, since idxSrcTy no longer tests openness; strictly stronger.

SEALED STATEMENT CHANGE (IDX-R2 S1-d1): the environment premise is localized to the members the sources name; strictly stronger. -/
theorem recIdxTySrcWalk_instantiateLevels (lvls : List Level) (fam : Nat)
    (E : ResolvedEnv) (recType ctorType : Expr Nat) (nparams : Nat)
    (recPre pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List IdxSrc))
    (hstable : SrcMembersBounded E (idxSrcConstsAll pss))
    (h : recIdxTySrcWalk fam E recType ctorType nparams recPre pf ks T fs pss =
      true) :
    recIdxTySrcWalk fam E (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType) nparams
      (recPre.map (instantiateLevels lvls)) (pf.map (instantiateLevels lvls)) ks
      (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) pss =
      true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTySrcWalk, List.map_nil]
          | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi _ B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      have htail : SrcMembersBounded E (idxSrcConstsAll pss) :=
                        srcMembersBounded_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_right _ hr) hstable
                      cases src with
                      | nil =>
                          simp only [recIdxTySrcWalk, List.map_cons,
                            instantiateLevels] at h ⊢
                          rw [← instantiateLevels_instantiate0]
                          exact ih (instantiate0 f B) fs pss htail h
                      | cons _ _ => simp only [recIdxTySrcWalk] at h; nomatch h
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTySrcWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTySrcWalk] at h; nomatch h
                  | cons src pss =>
                      have hsrc : SrcMembersBounded E (src.flatMap idxSrcConsts) :=
                        srcMembersBounded_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_left _ hr) hstable
                      have htail : SrcMembersBounded E (idxSrcConstsAll pss) :=
                        srcMembersBounded_of_subset (by
                          intro r hr
                          simp only [idxSrcConstsAll, List.flatMap_cons]
                          exact List.mem_append_right _ hr) hstable
                      simp only [recIdxTySrcWalk, List.map_cons,
                        instantiateLevels] at h ⊢
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_instantiateLevels lvls nparams A
                      have halign' : idxSrcAlign fam E
                          (instantiateLevels lvls recType)
                          (instantiateLevels lvls ctorType)
                          (recPre.map (instantiateLevels lvls))
                          (pf.map (instantiateLevels lvls))
                          (familyIdx nparams (instantiateLevels lvls A)) src =
                          true := by
                        rw [hfi]
                        exact idxSrcAlign_instantiateLevels lvls fam E recType
                          ctorType recPre pf (familyIdx nparams A) src hsrc halign
                      have hrest' := ih (instantiate0 f B) fs pss htail hrest
                      rw [← instantiateLevels_instantiate0]
                      simp only [halign', hrest']
                      rfl
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxTySrcWalk] at h
              nomatch h

private def idxSrcFuel0B : Expr Nat → IdxSrc → Bool
  | .const _ ls, .constNotFam _ => levelsOpen ls
  | .app f a, .app sf sa => idxSrcFuel0B f sf && idxSrcFuel0B a sa
  | _, _ => true

private def idxSrcFuelList0B : List (Expr Nat) → List IdxSrc → Bool
  | x :: xs, s :: ss => idxSrcFuel0B x s && idxSrcFuelList0B xs ss
  | _, _ => true

/-- Decidable fuel-0 check along the directly recursive index-source walk. -/
def recIdxSrcFuelWalk0B (nparams : Nat) :
    List RecKind → Expr Nat → List (Expr Nat) → List (List IdxSrc) → Bool
  | .plain :: ks, .pi _ B, f :: fs, [] :: pss =>
      recIdxSrcFuelWalk0B nparams ks (instantiate0 f B) fs pss
  | .directRec :: ks, .pi A B, f :: fs, src :: pss =>
      idxSrcFuelList0B (familyIdx nparams A) src &&
        recIdxSrcFuelWalk0B nparams ks (instantiate0 f B) fs pss
  | _, _, _, _ => true

private theorem idxSrcFuel0B_sound : ∀ (x : Expr Nat) (s : IdxSrc),
    idxSrcFuel0B x s = true → IdxSrcFuel 0 x s := by
  intro x s h
  induction s generalizing x with
  | pos _ =>
      cases x <;> simp only [IdxSrcFuel]
  | constField _ =>
      cases x <;> simp only [IdxSrcFuel]
  | sort =>
      cases x <;> simp only [IdxSrcFuel]
  | lit _ =>
      cases x <;> simp only [IdxSrcFuel]
  | constNotFam _ =>
      cases x with
      | const _ ls =>
          simp only [idxSrcFuel0B] at h
          exact levelsOpen_hwf 0 ls h
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [IdxSrcFuel]
  | app sf sa ihf iha =>
      cases x with
      | app f a =>
          simp only [idxSrcFuel0B, Bool.and_eq_true] at h
          exact ⟨ihf f h.1, iha a h.2⟩
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [IdxSrcFuel]

private theorem idxSrcFuelList0B_sound : ∀ (xs : List (Expr Nat))
    (ss : List IdxSrc), idxSrcFuelList0B xs ss = true →
      IdxSrcFuelList 0 xs ss := by
  intro xs
  induction xs with
  | nil =>
      intro ss _
      simp only [IdxSrcFuelList]
  | cons x xs ih =>
      intro ss h
      cases ss with
      | nil => simp only [IdxSrcFuelList]
      | cons s ss =>
          simp only [idxSrcFuelList0B, Bool.and_eq_true] at h
          exact ⟨idxSrcFuel0B_sound x s h.1, ih ss h.2⟩

/-- The explicit fuel-0 check supplies the proposition carried by `IotaTyping.hidxFuel`. -/
theorem recIdxSrcFuelWalk0B_sound (nparams : Nat) :
    ∀ (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
      (pss : List (List IdxSrc)),
      recIdxSrcFuelWalk0B nparams ks T fs pss = true →
      recIdxSrcFuelWalk 0 nparams ks T fs pss := by
  intro ks
  induction ks with
  | nil =>
      intro T fs pss _
      cases fs <;> cases pss <;> simp only [recIdxSrcFuelWalk]
  | cons k ks ih =>
      intro T fs pss h
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxSrcFuelWalk0B] at h
                          simp only [recIdxSrcFuelWalk]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ => simp only [recIdxSrcFuelWalk]
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcFuelWalk]
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      simp only [recIdxSrcFuelWalk0B, Bool.and_eq_true] at h
                      simp only [recIdxSrcFuelWalk]
                      exact ⟨idxSrcFuelList0B_sound (familyIdx nparams A) src h.1,
                        ih (instantiate0 f B) fs pss h.2⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcFuelWalk]

private theorem idxSrcFuelList_pos {n : Nat} (hn : 0 < n) :
    ∀ (xs : List (Expr Nat)) (ss : List IdxSrc), IdxSrcFuelList n xs ss := by
  intro xs
  induction xs with
  | nil => intro ss; simp only [IdxSrcFuelList]
  | cons x xs ih =>
      intro ss
      cases ss with
      | nil => simp only [IdxSrcFuelList]
      | cons s ss => exact ⟨idxSrcFuel_pos hn x s, ih ss⟩

/-- Positive fuel supplies every index source along the directly recursive walk. -/
theorem recIdxSrcFuelWalk_pos {n : Nat} (hn : 0 < n) (nparams : Nat) :
    ∀ (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
      (pss : List (List IdxSrc)), recIdxSrcFuelWalk n nparams ks T fs pss := by
  intro ks
  induction ks with
  | nil =>
      intro T fs pss
      cases fs <;> cases pss <;> simp only [recIdxSrcFuelWalk]
  | cons k ks ih =>
      intro T fs pss
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [recIdxSrcFuelWalk]
                          exact ih (instantiate0 f B) fs pss
                      | cons _ _ => simp only [recIdxSrcFuelWalk]
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcFuelWalk]
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxSrcFuelWalk]
                  | cons src pss =>
                      simp only [recIdxSrcFuelWalk]
                      exact ⟨idxSrcFuelList_pos hn (familyIdx nparams A) src,
                        ih (instantiate0 f B) fs pss⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [recIdxSrcFuelWalk]

/-- Fill-side constructor of the 05 admission bundle (optional).
SR reads `IotaTyping` from `EnvWf` (`envWf_iotaTyping`), not from
this Option being `some`. `recIdxPosBuild` here is on *this* lhs's
args (first-occurrence); declared-type positions live in EnvWf. -/
def iotaTypingCert {E : ResolvedEnv} (w : IotaWitness E) :
    Option (IotaTyping E w) :=
  match hmot : w.preMajor[w.nparams]? with
  | none => none
  | some motive =>
    match hdom : applyTel (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
        (instantiateLevels w.ls w.recMember.mtype) with
    | none => none
    | some (.bvar _) => none
    | some (.sort _) => none
    | some (.const _ _) => none
    | some (.app _ _) => none
    | some (.lam _ _) => none
    | some (.letE _ _ _) => none
    | some (.lit _) => none
    | some (.pi mdom restMin) =>
      if hfamSpine : directRecFamilySpine w.familyRef w.ls w.nparams
          (w.preMajor.take w.nparams) w.kinds w.ctorAfterParams
          w.fields = true then
       if hparamAlign : recCtorParamAlign
           (instantiateLevels w.ls w.recMember.mtype)
           (instantiateLevels w.ls w.ctorMember.mtype)
           (w.preMajor.take w.nparams) = true then
        if hfamSpineExact : directRecFamilySpineExact w.familyRef
            (w.ls.take w.famMember.arity)
            w.nparams (w.preMajor.take w.nparams) w.kinds
            w.ctorAfterParams w.fields = true then
         if hctorResShape : ctorResultParamShape w.familyRef w.ctorResult
             w.famMember.arity w.nparams w.kinds.length = true then
          if hidxWalk : recIdxFromSpineWalk w.familyRef w.nparams w.nindices
            (recParamsFields w) w.kinds w.ctorAfterParams w.fields =
            true then
          match recIdxSrcBuild w.familyRef w.nparams (recParamsFields w)
              w.kinds w.ctorAfterParams w.fields with
          | none => none
          | some idxPositions =>
            if hidxPos : recIdxSrcWalk w.familyRef w.nparams
                (recParamsFields w) w.kinds w.ctorAfterParams w.fields
                idxPositions = true then
              if hidxTy : recIdxTySrcWalk w.familyRef E
                  (instantiateLevels w.ls w.recMember.mtype)
                  (instantiateLevels w.ls w.ctorMember.mtype) w.nparams
                  (recPrefix w.preMajor w.nparams w.nMinors)
                  (recParamsFields w) w.kinds w.ctorAfterParams
                  w.fields idxPositions = true then
                if hidxFuel0 : recIdxSrcFuelWalk0B w.nparams w.kinds
                    w.ctorAfterParams w.fields idxPositions = true then
                  if hminTel : mdom = iotaMdom w motive then
                    some {
                      motive := motive
                      hmotive := hmot
                      mdom := mdom
                      restMin := restMin
                      hminDom := hdom
                      hfamSpine := hfamSpine
                      hparamAlign := hparamAlign
                      hfamSpineExact := hfamSpineExact
                      hctorResShape := hctorResShape
                      idxPositions := idxPositions
                      hidxWalk := hidxWalk
                      hidxPos := hidxPos
                      hidxTy := hidxTy
                      hidxFuel := fun n _ => by
                        cases n with
                        | zero =>
                            exact recIdxSrcFuelWalk0B_sound w.nparams w.kinds
                              w.ctorAfterParams w.fields idxPositions hidxFuel0
                        | succ n =>
                            exact recIdxSrcFuelWalk_pos (Nat.zero_lt_succ n)
                              w.nparams w.kinds w.ctorAfterParams w.fields
                              idxPositions
                      hminTel := hminTel
                    }
                  else none
                else none
              else none
            else none
          else none
         else none
        else none
       else none
      else none

theorem derivedIota_const_false {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {rhs : Expr Nat} (h : DerivedIota E (.const r ls) rhs) : False := by
  generalize e : (Expr.const r ls : Expr Nat) = lhs at h
  cases h with
  | of w =>
      exact foldApps_snoc_ne_const (.const w.recRef w.ls) (ctorMajor w)
        w.preMajor e.symm

def derivedIotaExt {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {lhs rhs : Expr Nat} :
    DerivedIota E lhs rhs → DerivedIota E' lhs rhs
  | .of w => by
      have h1 := iotaLhsOf_ext hext w
      have h2 := iotaRhsOf_ext hext w
      rw [← h1, ← h2]
      exact .of (extWitness hext w)

theorem appsSpine_foldApps (f : Expr Nat) (xs : List (Expr Nat)) :
    appsSpine (foldApps f xs) =
      ((appsSpine f).1, (appsSpine f).2 ++ xs) := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps, List.append_nil]
  | cons x xs ih =>
      simp only [foldApps]
      have ih' := ih (.app f x)
      simp only [appsSpine] at ih' ⊢
      rw [ih']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem foldApps_appsSpine :
    (e : Expr Nat) → foldApps (appsSpine e).1 (appsSpine e).2 = e
  | .app f x => by
      simp only [appsSpine, foldApps_append, foldApps]
      have ih := foldApps_appsSpine f
      simp only [ih]
  | .bvar i => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-! ## Raw const fuel, read off an actual typing

`Open₀` / `RawConstOK` are the raw `HasTy.const` fuel shape
(`∀ l, ∃ k, eval (fun _ => none) l = none ∨ k < n`). They are not
`HasTyT.const`'s `levelsBounded`, and nothing here changes that
constructor, `IotaTyping`, or conjuncts 11b–11d.

The head lemma reads the field the constructor already stores. Along
`.app` it takes the function subderivation; along `.conv` the subject
is unchanged, so the same equality is read inward. No intermediate Π
is rebuilt. -/

/-- `Open₀(L)`: every level is `none` under the empty valuation. -/
def levelsOpen0 (L : List Level) : Prop :=
  ∀ l ∈ L, eval (fun _ => none) l = none

theorem appsSpine_foldApps_const (r : Nat) (U : List Level)
    (args : List (Expr Nat)) :
    appsSpine (foldApps (.const r U) args) = (.const r U, args) := by
  simp only [appsSpine_foldApps, appsSpine, List.nil_append]

/-- A const-headed `foldApps` whose spine does not start with `app`
is the constant itself, with no arguments left. -/
theorem foldApps_const_residual {r : Nat} {U : List Level}
    {args : List (Expr Nat)} {e : Expr Nat}
    (he : e = foldApps (.const r U) args)
    (hsp : appsSpine e = (e, [])) :
    e = .const r U ∧ args = [] := by
  have h := appsSpine_foldApps_const r U args
  rw [← he, hsp] at h
  exact ⟨congrArg Prod.fst h, (congrArg Prod.snd h).symm⟩

/-- One application off a const-headed spine. The function is the same
constant applied to the strict prefix; the Π of that step is not read. -/
theorem foldApps_const_of_app {r : Nat} {U : List Level}
    {args : List (Expr Nat)} {f a : Expr Nat}
    (he : .app f a = foldApps (.const r U) args) :
    f = foldApps (.const r U) (appsSpine f).2 := by
  have h := appsSpine_foldApps_const r U args
  rw [← he] at h
  simp only [appsSpine] at h
  have hhead := congrArg Prod.fst h
  have hback := foldApps_appsSpine f
  rw [hhead] at hback
  exact hback.symm

/-- If an application head is the constant `r` at levels `U`, then `U`
satisfies the fuel field of `HasTy.const`. Specialized to `iotaLhsOf`
below; the intermediate Πs are not recovered. -/
theorem hasTy_foldApps_const_fuel {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (h : HasTy E n Γ e T) →
    (r : Nat) → (U : List Level) → (args : List (Expr Nat)) →
    e = foldApps (.const r U) args →
    rawConstOK n U
  | _, _, _, .const _ _ ls _ _ _ hwf, r, U, args, he => by
      have hc := (foldApps_const_residual he rfl).1
      injection hc with _ hls
      subst hls
      exact hwf
  | _, _, _, .app _ f _ _ _ hf _, r, U, args, he =>
      hasTy_foldApps_const_fuel hf r U (appsSpine f).2
        (foldApps_const_of_app he)
  | _, _, _, .conv _ _ _ _ h _, r, U, args, he =>
      hasTy_foldApps_const_fuel h r U args he
  | _, _, _, .sort _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, .bvar _ _ _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, .pi _ _ _ _ _ _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, .lam _ _ _ _ _ _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, .letE _ _ _ _ _ _ _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, .lit _ _ _ _, r, U, args, he => by
      nomatch (foldApps_const_residual he rfl).1

/-- The recursor head of `iotaLhsOf w` is `const recRef w.ls`. Its fuel
condition is the `hwf` field of that head, not a reconstructed telescope. -/
theorem hasTy_iotaLhs_rawConstOK {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {T : Expr Nat} (w : IotaWitness E)
    (h : HasTy E n Γ (iotaLhsOf w) T) : rawConstOK n w.ls :=
  hasTy_foldApps_const_fuel h w.recRef w.ls
    (w.preMajor ++ [ctorMajor w]) rfl

theorem levelMem_of_getElem? {U : List Level} {i : Nat} {u : Level}
    (h : U[i]? = some u) : u ∈ U := by
  induction U generalizing i with
  | nil =>
      simp only [List.getElem?_nil] at h
      exact Option.noConfusion h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at h
          injection h with hx
          subst hx
          exact List.mem_cons_self x xs
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          exact List.mem_cons_of_mem x (ih h)

/-- `Open₀(L)` and `RawConstOK(n, U)` give `RawConstOK` of the instantiated
declaration levels `L.map (instLevel U)`.

At `n > 0` take `k = 0`. At `n = 0`, `k < 0` is impossible, so every level
in the actual argument list `U` evaluates to `none`; `eval_instLevel`
(DT-002 at `levelParamSubst`) then sends each `l ∈ L` to `none` as well.
This is not "an arbitrary substitution preserves `levelsOpen`": a ground
level in `U` is excluded by the fuel premise, and only at `n = 0`. -/
theorem rawConstOK_instLevel {n : Nat} {L U : List Level}
    (hL : levelsOpen0 L) (hU : rawConstOK n U) :
    rawConstOK n (L.map (instLevel U)) := by
  intro u hu
  rw [List.mem_map] at hu
  rcases hu with ⟨l, hl, rfl⟩
  cases n with
  | succ n =>
      exact ⟨0, Or.inr (Nat.succ_pos n)⟩
  | zero =>
      refine ⟨0, Or.inl ?_⟩
      have hU0 : ∀ v ∈ U, eval (fun _ => none) v = none := by
        intro v hv
        rcases hU v hv with ⟨k, hk⟩
        cases hk with
        | inl hv => exact hv
        | inr hk => exact False.elim (Nat.not_lt_zero k hk)
      rw [eval_instLevel]
      have hρ : ∀ i,
          eval (fun _ => none) ((U[i]?).getD (.param i)) = none := by
        intro i
        match hget : U[i]? with
        | none =>
            simp only [hget, Option.getD_none, eval]
        | some v =>
            simp only [hget, Option.getD_some]
            exact hU0 v (levelMem_of_getElem? hget)
      rw [eval_congr_val hρ l]
      exact hL l hl

/-- Level instantiation transports fuel from zero to the redex's level bound. -/
theorem idxSrcFuel_instantiateLevels_of_zero (n : Nat) (U : List Level) :
    ∀ (x : Expr Nat) (s : IdxSrc), IdxSrcFuel 0 x s → rawConstOK n U →
      IdxSrcFuel n (instantiateLevels U x) s := by
  intro x s hfuel hU
  induction s generalizing x with
  | pos _ =>
      cases x <;> simp only [instantiateLevels, IdxSrcFuel]
  | constField _ =>
      cases x <;> simp only [instantiateLevels, IdxSrcFuel]
  | sort =>
      cases x <;> simp only [instantiateLevels, IdxSrcFuel]
  | lit _ =>
      cases x <;> simp only [instantiateLevels, IdxSrcFuel]
  | constNotFam _ =>
      cases x with
      | const r ls =>
          have hL : levelsOpen0 ls := by
            intro l hl
            rcases hfuel l hl with ⟨k, hk | hk⟩
            · exact hk
            · exact False.elim (Nat.not_lt_zero k hk)
          simpa only [instantiateLevels, IdxSrcFuel] using
            (rawConstOK_instLevel hL hU)
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [instantiateLevels, IdxSrcFuel]
  | app sf sa ihf iha =>
      cases x with
      | app f a =>
          simp only [instantiateLevels, IdxSrcFuel] at hfuel ⊢
          exact ⟨ihf f hfuel.1, iha a hfuel.2⟩
      | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [instantiateLevels, IdxSrcFuel]

/-- List form of `idxSrcFuel_instantiateLevels_of_zero`. -/
theorem idxSrcFuelList_instantiateLevels_of_zero (n : Nat) (U : List Level) :
    ∀ (xs : List (Expr Nat)) (ss : List IdxSrc),
      IdxSrcFuelList 0 xs ss → rawConstOK n U →
      IdxSrcFuelList n (xs.map (instantiateLevels U)) ss := by
  intro xs
  induction xs with
  | nil =>
      intro ss _ _
      cases ss <;> simp only [List.map_nil, IdxSrcFuelList]
  | cons x xs ih =>
      intro ss hfuel hU
      cases ss with
      | nil => simp only [List.map, IdxSrcFuelList]
      | cons s ss =>
          simp only [IdxSrcFuelList, List.map_cons] at hfuel ⊢
          exact ⟨idxSrcFuel_instantiateLevels_of_zero n U x s hfuel.1 hU,
            ih ss hfuel.2 hU⟩

/-- The raw source-guided fuel-zero walk transports through level instantiation to fuel `n`. -/
theorem recIdxSrcFuelWalk_instantiateLevels_of_zero (n nparams : Nat)
    (U : List Level) :
    ∀ (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
      (pss : List (List IdxSrc)),
      recIdxSrcFuelWalk 0 nparams ks T fs pss → rawConstOK n U →
      recIdxSrcFuelWalk n nparams ks (instantiateLevels U T)
        (fs.map (instantiateLevels U)) pss := by
  intro ks
  induction ks with
  | nil =>
      intro T fs pss _ _
      cases fs <;> cases pss <;>
        simp only [instantiateLevels, List.map_nil, List.map_cons,
          recIdxSrcFuelWalk]
  | cons k ks ih =>
      intro T fs pss hfuel hU
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [instantiateLevels, List.map_nil,
                  recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [instantiateLevels, List.map_cons,
                      recIdxSrcFuelWalk]
                  | cons src pss =>
                      cases src with
                      | nil =>
                          simp only [instantiateLevels, List.map_cons,
                            recIdxSrcFuelWalk] at hfuel ⊢
                          rw [← instantiateLevels_instantiate0]
                          exact ih (instantiate0 f B) fs pss hfuel hU
                      | cons _ _ => simp only [instantiateLevels,
                          List.map_cons, recIdxSrcFuelWalk]
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [instantiateLevels, recIdxSrcFuelWalk]
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [instantiateLevels, List.map_nil,
                  recIdxSrcFuelWalk]
              | cons f fs =>
                  cases pss with
                  | nil => simp only [instantiateLevels, List.map_cons,
                      recIdxSrcFuelWalk]
                  | cons src pss =>
                      simp only [instantiateLevels, List.map_cons,
                        recIdxSrcFuelWalk] at hfuel ⊢
                      have hfi := familyIdx_instantiateLevels U nparams A
                      rw [hfi, ← instantiateLevels_instantiate0]
                      exact ⟨idxSrcFuelList_instantiateLevels_of_zero n U
                          (familyIdx nparams A) src hfuel.1 hU,
                        ih (instantiate0 f B) fs pss hfuel.2 hU⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [instantiateLevels, recIdxSrcFuelWalk]

/-- Declaration levels of a typed iota redex, instantiated at the
recursor's own universe arguments. -/
theorem rawConstOK_instLevel_of_iotaLhs {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {T : Expr Nat} {L : List Level} (w : IotaWitness E)
    (h : HasTy E n Γ (iotaLhsOf w) T) (hL : levelsOpen0 L) :
    rawConstOK n (L.map (instLevel w.ls)) :=
  rawConstOK_instLevel hL (hasTy_iotaLhs_rawConstOK w h)

/-- At fuel 0 the `k < n` disjunct is impossible, so `RawConstOK` is the
Bool `levelsOpen`. This is the typing-side supply for `hopen`. It is not
true at `n > 0` (`rawConstOK_pos_not_levelsOpen`). -/
theorem levelsOpen_of_rawConstOK_zero {U : List Level}
    (h : rawConstOK 0 U) : levelsOpen U = true := by
  induction U with
  | nil => rfl
  | cons u us ih =>
      simp only [levelsOpen, Bool.and_eq_true]
      refine ⟨?_, ih (fun v hv => h v (List.mem_cons_of_mem u hv))⟩
      rcases h u (List.mem_cons_self u us) with ⟨k, hk⟩
      cases hk with
      | inl he =>
          simp only [levelOpen, he]
      | inr hk =>
          exact False.elim (Nat.not_lt_zero k hk)

/-- `levelsOpen w.ls` read off `HasTy` of `iotaLhsOf w` at fuel 0. -/
theorem levelsOpen_of_iotaLhs_zero {E : ResolvedEnv} {Γ : LCtx}
    {T : Expr Nat} (w : IotaWitness E)
    (h : HasTy E 0 Γ (iotaLhsOf w) T) : levelsOpen w.ls = true :=
  levelsOpen_of_rawConstOK_zero (hasTy_iotaLhs_rawConstOK w h)

/-! Controls. `param 0 ↦ zero` loses openness; `RawConstOK` at `n > 0`
still follows from the lemma, and at `n = 0` the same image is refused.
`param 0 ↦ param 0` at `n = 0` is the lemma, not a separate reduction. -/

theorem levelsOpen0_param0 : levelsOpen0 [.param 0] := by
  intro l hl
  simp only [List.mem_singleton] at hl
  subst hl
  rfl

theorem rawConstOK_param0_at_zero : rawConstOK 0 [.param 0] := by
  intro u hu
  simp only [List.mem_singleton] at hu
  subst hu
  exact ⟨0, Or.inl rfl⟩

theorem rawConstOK_zero_at_one : rawConstOK 1 [.zero] := by
  intro u hu
  simp only [List.mem_singleton] at hu
  subst hu
  exact ⟨0, Or.inr (Nat.succ_pos 0)⟩

/-- `param 0 ↦ zero`, `n > 0`: the image is ground, and `RawConstOK` is
still the lemma (its `k = 0` branch). -/
theorem rawConstOK_param0_to_zero_pos :
    rawConstOK 1 ([.param 0].map (instLevel [.zero])) :=
  rawConstOK_instLevel levelsOpen0_param0 rawConstOK_zero_at_one

theorem levelOpen_param0_to_zero_lost :
    levelOpen (instLevel [.zero] (.param 0)) = false := rfl

/-- The `n = 0` image of that same substitution is exactly `[zero]`. -/
theorem instLevel_param0_to_zero_list :
    ([.param 0].map (instLevel [.zero])) = [.zero] := rfl

/-- `param 0 ↦ zero`, `n = 0`: `RawConstOK 0 [zero]` is false. Not forged. -/
theorem not_rawConstOK_zero_zero : ¬ rawConstOK 0 [.zero] := by
  intro h
  rcases h .zero (List.mem_cons_self _ _) with ⟨k, hk⟩
  cases hk with
  | inl hnone =>
      simp only [eval] at hnone
      exact Option.noConfusion hnone
  | inr hk =>
      exact Nat.not_lt_zero k hk

/-- `param 0 ↦ param 0`, `n = 0`: the full lemma, both premises open. -/
theorem rawConstOK_open_param_at_zero :
    rawConstOK 0 ([.param 0].map (instLevel [.param 0])) :=
  rawConstOK_instLevel levelsOpen0_param0 rawConstOK_param0_at_zero

/-- The same open parameter, read back as the Bool `hopen` consumes. -/
theorem levelsOpen_param0_at_zero : levelsOpen [.param 0] = true :=
  levelsOpen_of_rawConstOK_zero rawConstOK_param0_at_zero

/-- `n > 0`: `RawConstOK` holds for `[zero]` and `levelsOpen` does not.
The fuel-0 bridge must not be used here. -/
theorem rawConstOK_pos_not_levelsOpen :
    rawConstOK 1 [.zero] ∧ levelsOpen [.zero] = false :=
  ⟨rawConstOK_zero_at_one, rfl⟩

#print axioms hasTy_foldApps_const_fuel
#print axioms hasTy_iotaLhs_rawConstOK
#print axioms rawConstOK_instLevel
#print axioms rawConstOK_instLevel_of_iotaLhs
#print axioms rawConstOK_param0_to_zero_pos
#print axioms not_rawConstOK_zero_zero
#print axioms rawConstOK_open_param_at_zero
#print axioms levelsOpen_of_rawConstOK_zero
#print axioms levelsOpen_of_iotaLhs_zero
#print axioms levelsOpen_param0_at_zero
#print axioms rawConstOK_pos_not_levelsOpen

/-- `appsSpine` peels every `app`; the residual head is never an app. -/
theorem appsSpine_fst_ne_app :
    (e : Expr Nat) → ∀ f x, (appsSpine e).1 ≠ Expr.app f x
  | .app f _, g, y => by
      simp only [appsSpine]
      exact appsSpine_fst_ne_app f g y
  | .bvar _, g, y => by intro h; nomatch h
  | .sort _, g, y => by intro h; nomatch h
  | .const _ _, g, y => by intro h; nomatch h
  | .lam _ _, g, y => by intro h; nomatch h
  | .pi _ _, g, y => by intro h; nomatch h
  | .letE _ _ _, g, y => by intro h; nomatch h
  | .lit _, g, y => by intro h; nomatch h

/-- Two expressions with the same residual head and argument spine are equal. -/
theorem appsSpine_ext {A B : Expr Nat}
    (h1 : (appsSpine A).1 = (appsSpine B).1)
    (h2 : (appsSpine A).2 = (appsSpine B).2) : A = B := by
  have hA := foldApps_appsSpine A
  have hB := foldApps_appsSpine B
  rw [← hA, ← hB, h1, h2]

/-- DirectRec step of `recIdxFromSpineWalk`: length, `idxFamFree`, remainder. -/
theorem recIdxFromSpineWalk_directRec {fam nparams nindices : Nat}
    {pf : List (Expr Nat)} {A B f : Expr Nat} {ks : List RecKind}
    {fs : List (Expr Nat)}
    (h : recIdxFromSpineWalk fam nparams nindices pf (.directRec :: ks)
      (.pi A B) (f :: fs) = true) :
    (familyIdx nparams A).length = nindices ∧
      (familyIdx nparams A).all (fun x => idxFamFree fam pf x) = true ∧
      recIdxFromSpineWalk fam nparams nindices pf ks (instantiate0 f B) fs =
        true := by
  simp only [recIdxFromSpineWalk] at h
  have ⟨hlenall, hrest⟩ := bool_and_true h
  have ⟨hlen, hall⟩ := bool_and_true hlenall
  exact ⟨of_decide_eq_true hlen, hall, hrest⟩

/-- DirectRec step of `recIdxTyWalk`: index-domain alignment and remainder. -/
theorem recIdxTyWalk_directRec {recType ctorType : Expr Nat}
    {nparams : Nat} {recPre pf : List (Expr Nat)}
    {A B f : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    (h : recIdxTyWalk recType ctorType nparams recPre pf
      (.directRec :: ks) (.pi A B) (f :: fs) = true) :
    idxTyAlign recType ctorType recPre pf (familyIdx nparams A) = true ∧
      recIdxTyWalk recType ctorType nparams recPre pf ks
        (instantiate0 f B) fs = true := by
  simp only [recIdxTyWalk] at h
  exact bool_and_true h

/-- Exact-walk sibling of `directRecFamilySpine_directRec` (00 §20.5:
the two predicates coexist, R- and T-class). -/
theorem directRecFamilySpineExact_directRec {fam : Nat} {ls : List Level}
    {nparams : Nat} {params : List (Expr Nat)}
    {A B f : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    (h : directRecFamilySpineExact fam ls nparams params (.directRec :: ks)
      (.pi A B) (f :: fs) = true) :
    directRecFamilySpineExact fam ls nparams params ks
      (instantiate0 f B) fs = true := by
  simp only [directRecFamilySpineExact] at h
  have ⟨_, hrest⟩ := bool_and_true h
  exact hrest

/-- DirectRec step of `directRecFamilySpine`: remainder after this field. -/
theorem directRecFamilySpine_directRec {fam : Nat} {ls : List Level}
    {nparams : Nat} {params : List (Expr Nat)}
    {A B f : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    (h : directRecFamilySpine fam ls nparams params (.directRec :: ks)
      (.pi A B) (f :: fs) = true) :
    directRecFamilySpine fam ls nparams params ks
      (instantiate0 f B) fs = true := by
  simp only [directRecFamilySpine] at h
  have ⟨_, hrest⟩ := bool_and_true h
  exact hrest

/-- With no indices, every DirectRec `familyIdx` is `[]`, so
`idxTyAlign` holds and `recIdxTyWalk` follows from `hidxWalk`. -/
theorem recIdxTyWalk_of_nindices_zero (fam : Nat) (recType ctorType : Expr Nat)
    (nparams : Nat) (recPre pf : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    recIdxFromSpineWalk fam nparams 0 pf ks T fs = true →
    recIdxTyWalk recType ctorType nparams recPre pf ks T fs = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi _ B, f :: fs, h => by
      simp only [recIdxFromSpineWalk] at h
      simp only [recIdxTyWalk]
      exact recIdxTyWalk_of_nindices_zero fam recType ctorType nparams recPre pf
        ks (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      have ⟨hlen, _, hrest⟩ := recIdxFromSpineWalk_directRec h
      have hnil : familyIdx nparams A = [] :=
        List.eq_nil_of_length_eq_zero hlen
      have halign : idxTyAlign recType ctorType recPre pf
          (familyIdx nparams A) = true := by
        rw [hnil]
        simp only [idxTyAlign, idxTyAlignGo]
      simp only [recIdxTyWalk, halign]
      exact recIdxTyWalk_of_nindices_zero fam recType ctorType nparams recPre pf
        ks (instantiate0 f B) fs hrest
  | .plain :: _, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, recIdxTyWalk]
  | .directRec :: _, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, recIdxTyWalk]
  | .plain :: _, .bvar _, _, _ => rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

/-- 05 §8: a DirectRec field domain is the family applied to the
recursor-side parameters and its own indices. Restated over the EXACT
walk (00 §20.5) and in `Type` (00 §18.3 rule 1).

The OLD statement returned `∃ lsA, A = foldApps (.const fam lsA)
(appsSpine A).2` — a SELF-REFERENTIAL equation (`A` occurs on both
sides), on which `subst` cannot fire, and an `∃` its two Type-valued
consumers cannot eliminate; that is the failing statement recorded in
00 §19.7 / §20.4. Here the spine is bound FRESH as `args`, so the
first component is a plain equation about `appsSpine A`, and the
universe list (`ls`) and the parameter prefix (`params`) are
syntactic, supplied by `directRecFamilySpineExact`. -/
def directRec_eq_family {fam : Nat} {ls : List Level} {nparams : Nat}
    {params : List (Expr Nat)} {A B f : Expr Nat} {ks : List RecKind}
    {fs : List (Expr Nat)}
    (h : directRecFamilySpineExact fam ls nparams params (.directRec :: ks)
      (.pi A B) (f :: fs) = true) :
    Σ' (args : List (Expr Nat)),
      (appsSpine A = (Expr.const fam ls, args)) ×'
      (A = foldApps (Expr.const fam ls)
        (params ++ familyIdx nparams A)) := by
  simp only [directRecFamilySpineExact] at h
  have ⟨hh, _⟩ := bool_and_true h
  have ⟨hhead, htake⟩ := bool_and_true hh
  have hte : (appsSpine A).2.take nparams = params :=
    of_decide_eq_true htake
  cases hconst : (appsSpine A).1 with
  | const r lsA =>
      simp only [hconst] at hhead
      have ⟨hr0, hl0⟩ := bool_and_true hhead
      have hr : r = fam := of_decide_eq_true hr0
      have hl : lsA = ls := of_decide_eq_true hl0
      subst hr
      subst hl
      refine ⟨(appsSpine A).2, ?_, ?_⟩
      · have hp : appsSpine A = ((appsSpine A).1, (appsSpine A).2) := rfl
        rw [hconst] at hp
        exact hp
      · have hfold := foldApps_appsSpine A
        rw [hconst] at hfold
        have hsplit : params ++ familyIdx nparams A = (appsSpine A).2 := by
          simp only [familyIdx]
          rw [← hte]
          exact List.take_append_drop nparams (appsSpine A).2
        rw [hsplit]
        exact hfold.symm
  | bvar _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | sort _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | app _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | lam _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | pi _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | letE _ _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | lit _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead

theorem appsSpine_const (r : Nat) (ls : List Level) :
    appsSpine (.const r ls) = (.const r ls, []) := rfl

theorem appsSpine_bvar (i : Nat) :
    appsSpine (.bvar i : Expr Nat) = (.bvar i, []) := rfl

/-- The index read-out of a family application with a KNOWN parameter
prefix (00 §19.2 erratum 6). `familyIdx` drops `nparams` off the
spine; `appsSpine_foldApps` computes the spine of a const-headed
application, whose head contributes the empty prefix
(`appsSpine_const`), so the drop lands exactly past `ps`.

Pure syntax: no `Conv`, no typing, no obligation. It is what turns the
telescope endpoint of a constructor spine into the constructor's
result index list at the discharge site (`iotaLhs_ctorIdx_conv`,
`RcicDTMeta`). -/
theorem familyIdx_foldApps_const {r : Nat} {ls : List Level}
    {nparams : Nat} {ps idx : List (Expr Nat)}
    (hlen : ps.length = nparams) :
    familyIdx nparams (foldApps (.const r ls) (ps ++ idx)) = idx := by
  simp only [familyIdx, appsSpine_foldApps, appsSpine_const,
    List.nil_append]
  exact List.drop_left' hlen

theorem list_snoc_inj {α : Type} {xs ys : List α} {a b : α}
    (h : xs ++ [a] = ys ++ [b]) : xs = ys ∧ a = b := by
  have hlen : (xs ++ [a]).length = (ys ++ [b]).length := congrArg List.length h
  simp only [List.length_append, List.length_singleton] at hlen
  have hx : xs.length = ys.length := Nat.add_right_cancel hlen
  have ⟨hxs, hsing⟩ := List.append_inj h hx
  have hab : a = b := by injection hsing
  exact ⟨hxs, hab⟩

def derivedIota_unpack {E : ResolvedEnv} {lhs rhs : Expr Nat} :
    DerivedIota E lhs rhs →
    Σ' (w : IotaWitness E), (lhs = iotaLhsOf w) ×' (rhs = iotaRhsOf w)
  | .of w => ⟨w, rfl, rfl⟩

/-- 05 §13 last Π-body of a recursor: `F x` as `app (lift 0 1 F) (bvar 0)`. -/
theorem instantiate0_eta (F x : Expr Nat) :
    instantiate0 x (.app (lift 0 1 F) (.bvar 0)) = .app F x := by
  simp only [instantiate0, instantiate]
  rw [instantiate_lift_id 0 x F]
  simp only [↓reduceIte]

theorem instantiate0_minorTel_plain (M : Expr Nat) (nparams : Nat)
    (C x : Expr Nat)
    (ks : List RecKind) (B : Expr Nat)
    (htel : isPiTel ks.length B = true)
    (hfam : directRecConstHead ks B = true)
    (hres : resultConstHead ks B = true) :
    instantiate0 x
      (minorTel (lift 0 1 M) nparams (.app (lift 0 1 C) (.bvar 0)) ks B) =
      minorTel M nparams (.app C x) ks (instantiate0 x B) := by
  have h := minorTel_instantiate_tel 0 x (lift 0 1 M)
    (.app (lift 0 1 C) (.bvar 0)) nparams ks B htel hfam hres
  have hM : instantiate0 x (lift 0 1 M) = M := instantiate_lift_id 0 x M
  have hC : instantiate0 x (.app (lift 0 1 C) (.bvar 0)) = .app C x :=
    instantiate0_eta C x
  simp only [instantiate0] at h hM hC ⊢
  rw [h, hM, hC]

/-- After applying a directRec field `f` and its IH, the remaining
`minorTel` is the original with `ctorAcc` applied to `f`. 05 MinorContextMap:
the field is `bvar 1` under the IH binder (`lift 0 1 B`). -/
theorem instantiate0_minorTel_directRec (M : Expr Nat) (nparams : Nat)
    (C f ih : Expr Nat)
    (ks : List RecKind) (B : Expr Nat)
    (htel : isPiTel ks.length B = true)
    (hfam : directRecConstHead ks B = true)
    (hres : resultConstHead ks B = true) :
    instantiate0 ih
      (instantiate 1 (lift 0 1 f)
        (minorTel (lift 0 2 M) nparams
          (.app (lift 0 2 C) (.bvar 1)) ks (lift 0 1 B))) =
      minorTel M nparams (.app C f) ks (instantiate0 f B) := by
  have htelB : isPiTel ks.length (lift 0 1 B) = true :=
    isPiTel_lift 0 1 ks.length B htel
  have hfamB : directRecConstHead ks (lift 0 1 B) = true :=
    directRecConstHead_lift 0 1 ks B hfam
  have hresB : resultConstHead ks (lift 0 1 B) = true :=
    resultConstHead_lift 0 1 ks B hres
  have h := minorTel_instantiate_tel 1 (lift 0 1 f) (lift 0 2 M)
    (.app (lift 0 2 C) (.bvar 1)) nparams ks (lift 0 1 B) htelB hfamB hresB
  have hM : instantiate 1 (lift 0 1 f) (lift 0 2 M) = lift 0 1 M :=
    instantiate_lift_cancel 2 0 1 (lift 0 1 f) (Nat.zero_le 1) (by omega) M
  have hC : instantiate 1 (lift 0 1 f) (.app (lift 0 2 C) (.bvar 1)) =
      .app (lift 0 1 C) (lift 0 1 f) := by
    simp only [instantiate]
    have hC' : instantiate 1 (lift 0 1 f) (lift 0 2 C) = lift 0 1 C :=
      instantiate_lift_cancel 2 0 1 (lift 0 1 f) (Nat.zero_le 1) (by omega) C
    rw [hC']
    simp only [↓reduceIte]
  have hB : instantiate 1 (lift 0 1 f) (lift 0 1 B) =
      lift 0 1 (instantiate0 f B) := by
    have h := lift_instantiate_high 1 0 0 f (Nat.zero_le 0) B
    simp only [Nat.add_comm 1 0, instantiate0] at h
    exact h.symm
  rw [h, hM, hC, hB]
  have htel0 := isPiTel_lift 0 1 ks.length (instantiate0 f B)
    (isPiTel_instantiate 0 f ks.length B htel)
  have hfam0 := directRecConstHead_lift 0 1 ks (instantiate0 f B)
    (directRecConstHead_instantiate 0 f ks B htel hfam)
  have hres0 := resultConstHead_lift 0 1 ks (instantiate0 f B)
    (resultConstHead_instantiate 0 f ks B htel hres)
  have h2 := minorTel_instantiate_tel 0 ih (lift 0 1 M)
    (.app (lift 0 1 C) (lift 0 1 f)) nparams ks
    (lift 0 1 (instantiate0 f B)) htel0 hfam0 hres0
  simp only [instantiate0] at h2 ⊢
  rw [h2]
  have hM' : instantiate0 ih (lift 0 1 M) = M := instantiate_lift_id 0 ih M
  have hC' : instantiate0 ih (.app (lift 0 1 C) (lift 0 1 f)) = .app C f := by
    simp only [instantiate0, instantiate]
    rw [instantiate_lift_id 0 ih C, instantiate_lift_id 0 ih f]
  have hB' : instantiate0 ih (lift 0 1 (instantiate0 f B)) =
      instantiate0 f B := instantiate_lift_id 0 ih (instantiate0 f B)
  simp only [instantiate0] at hM' hC' hB' ⊢
  rw [hM', hC', hB']

/-- `rhsArgs` applied to the remaining minor type `mdom` yields
`M (result indices) (ctorAcc fields)`. `mdom` is the applyTel
remainder (not the synthesized telescope); the identification
`mdom = minorTel` is `IotaTyping.hminTel`. 00 §19.2 erratum 5: the
conclusion's motive arguments are `familyIdx nparams U`, where `U`
is the constructor telescope with the actual fields applied — read
off the telescope, not lifted in from the redex. This is the bridge
from `hminTel` to the minor's applied type. -/
theorem applyTel_rhsArgs_minorTel (rec : Expr Nat)
    (pre : List (Expr Nat)) (nparams nMinors : Nat)
    (M ctorAcc : Expr Nat) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    (mdom U : Expr Nat) →
    ks.length = fs.length →
    isPiTel ks.length T = true →
    directRecConstHead ks T = true →
    resultConstHead ks T = true →
    applyTel fs T = some U →
    mdom = minorTel M nparams ctorAcc ks T →
    applyTel (rhsArgs rec pre nparams nMinors fs ks T) mdom =
        some (.app (foldApps M (familyIdx nparams U)) (foldApps ctorAcc fs))
  | [], T, [], mdom, U, _, _, _, _, happ, hmdom => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      rw [hmdom]
      simp only [rhsArgs, minorTel, applyTel, foldApps]
  | [], T, _ :: _, mdom, U, hlen, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen
      cases hlen
  | .plain :: ks, T, [], mdom, U, hlen, _, _, _, _, _ => by
      simp only [List.length_cons, List.length_nil] at hlen
      cases hlen
  | .directRec :: ks, T, [], mdom, U, hlen, _, _, _, _, _ => by
      simp only [List.length_cons, List.length_nil] at hlen
      cases hlen
  | .plain :: ks, T, f :: fs, mdom, U, hlen, htel, hfam, hres, happ, hmdom => by
      rw [hmdom]
      match T with
      | .pi A B =>
          simp only [List.length_cons] at hlen htel
          have hlen' : ks.length = fs.length := Nat.succ.inj hlen
          simp only [isPiTel] at htel
          simp only [directRecConstHead] at hfam
          simp only [resultConstHead] at hres
          simp only [applyTel] at happ
          have htel' := isPiTel_instantiate 0 f ks.length B htel
          have hfam' := directRecConstHead_instantiate 0 f ks B htel hfam
          have hres' := resultConstHead_instantiate 0 f ks B htel hres
          have hrest :=
            applyTel_rhsArgs_minorTel rec pre nparams nMinors M
              (.app ctorAcc f) ks (instantiate0 f B) fs
              (minorTel M nparams (.app ctorAcc f) ks (instantiate0 f B)) U
              hlen' htel' hfam' hres' happ rfl
          have hinst := instantiate0_minorTel_plain M nparams ctorAcc
            f ks B htel hfam hres
          simp only [rhsArgs, minorTel, applyTel]
          rw [hinst]
          exact hrest
      | .bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: ks, T, f :: fs, mdom, U, hlen, htel, hfam, hres, happ,
      hmdom => by
      rw [hmdom]
      match T with
      | .pi A B =>
          simp only [List.length_cons] at hlen htel
          have hlen' : ks.length = fs.length := Nat.succ.inj hlen
          simp only [isPiTel] at htel
          simp only [directRecConstHead] at hfam
          simp only [resultConstHead] at hres
          simp only [applyTel] at happ
          have ⟨hhead, hrestH⟩ := bool_and_true hfam
          have htelB := isPiTel_instantiate 0 f ks.length B htel
          have hfamB :=
            directRecConstHead_instantiate 0 f ks B htel hrestH
          have hresB := resultConstHead_instantiate 0 f ks B htel hres
          have hrest :=
            applyTel_rhsArgs_minorTel rec pre nparams nMinors M
              (.app ctorAcc f) ks (instantiate0 f B) fs
              (minorTel M nparams (.app ctorAcc f) ks (instantiate0 f B)) U
              hlen' htelB hfamB hresB happ rfl
          have hinst := instantiate0_minorTel_directRec M nparams ctorAcc
            f (recCallField rec pre nparams nMinors f A) ks B htel hrestH hres
          simp only [rhsArgs, minorTel, applyTel, Nat.add_zero, Nat.zero_add]
          rw [hinst]
          simp only [foldApps] at hrest ⊢
          exact hrest
      | .bvar _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .sort _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .const _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .app _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .lam _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .letE _ _ _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel
      | .lit _ => simp only [isPiTel, List.length_cons] at htel; nomatch htel

/-- 0-ary iota hole, packaged: if the last Π-body is `F x` and the minor
type is `F ctor`, they convert. -/
def conv_of_eta_minor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {F Mty B : Expr Nat} {w : IotaWitness E}
    (hM : Mty = .app F (ctorMajor w))
    (hB : B = .app (lift 0 1 F) (.bvar 0)) :
    Conv E n Γ Mty (instantiate0 (ctorMajor w) B) := by
  rw [hM, hB, instantiate0_eta]
  exact .refl _ _

/-- 05 §13 recursor result body (from inside the major binder). -/
def recBodyExpr (nMinors nindices : Nat) : Expr Nat :=
  foldApps (.bvar (nMinors + nindices + 1))
    ((List.range nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
      [Expr.bvar 0])

/-- 05 §13 last recursor domain (major type) as de Bruijn under
params / motive / minors / indices. -/
def majorTyExpr (familyRef : Nat) (ls : List Level)
    (nparams nMinors nindices : Nat) : Expr Nat :=
  foldApps (.const familyRef ls)
    ((List.range nparams).reverse.map
      (fun i => Expr.bvar (i + nindices + nMinors + 1)) ++
      (List.range nindices).reverse.map (fun i => Expr.bvar i))

/-- 00 §20.6: the major type is a family head applied to pure `bvar`s,
so level instantiation touches ONLY the head's universe list. Composed
with `map_instLevel_canonical` this turns the STORED (canonical-vector)
`hmajorTy` into the redex-side head `ls.take nU`. -/
theorem instantiateLevels_majorTyExpr (lvls : List Level) (familyRef : Nat)
    (ls : List Level) (nparams nMinors nindices : Nat) :
    instantiateLevels lvls
        (majorTyExpr familyRef ls nparams nMinors nindices) =
      majorTyExpr familyRef (ls.map (instLevel lvls))
        nparams nMinors nindices := by
  simp only [majorTyExpr]
  rw [foldApps_instantiateLevels]
  simp only [instantiateLevels, List.map_append]
  rw [map_instantiateLevels_bvars lvls (fun i => i + nindices + nMinors + 1)
      ((List.range nparams).reverse),
    map_instantiateLevels_bvars lvls (fun i => i)
      ((List.range nindices).reverse)]

theorem instPrefix_nil (e : Expr Nat) : instPrefix [] e = e := rfl

theorem instPrefix_cons (a : Expr Nat) (as : List (Expr Nat)) (e : Expr Nat) :
    instPrefix (a :: as) e =
      instPrefix as (instantiate as.length (lift 0 as.length a) e) := rfl

theorem instPrefix_lift (as : List (Expr Nat)) (a : Expr Nat) :
    instPrefix as (lift 0 as.length a) = a := by
  induction as generalizing a with
  | nil =>
      simp only [instPrefix, List.length_nil, lift_zero]
  | cons a' as ih =>
      simp only [instPrefix_cons, List.length_cons]
      have hc : instantiate as.length (lift 0 as.length a')
          (lift 0 (as.length + 1) a) = lift 0 as.length a := by
        have h1 : 0 ≤ as.length := Nat.zero_le _
        have h2 : as.length < (as.length + 1) + 0 := by omega
        have hcan := instantiate_lift_cancel (as.length + 1) 0
          as.length (lift 0 as.length a') h1 h2 a
        have hamt : as.length + 1 - 1 = as.length := by omega
        simp only [Nat.add_zero] at hcan
        rw [hamt] at hcan
        exact hcan
      rw [hc]
      exact ih a

theorem instPrefix_const (args : List (Expr Nat)) (r : Nat)
    (ls : List Level) :
    instPrefix args (.const r ls) = .const r ls := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      simp only [instPrefix_cons, instantiate]
      exact ih

theorem instPrefix_foldApps (args : List (Expr Nat)) (f : Expr Nat)
    (xs : List (Expr Nat)) :
    instPrefix args (foldApps f xs) =
      foldApps (instPrefix args f) (xs.map (instPrefix args)) := by
  induction args generalizing f xs with
  | nil =>
      have hmap : xs.map (instPrefix []) = xs := by
        induction xs with
        | nil => rfl
        | cons x xs ih =>
            simp only [List.map_cons, instPrefix_nil, ih]
      simp only [instPrefix_nil, hmap]
  | cons a as ih =>
      rw [instPrefix_cons, foldApps_instantiate, ih]
      have hmap :
          xs.map (instPrefix as ∘ instantiate as.length
            (lift 0 as.length a)) =
          xs.map (instPrefix (a :: as)) := by
        induction xs with
        | nil => rfl
        | cons x xs ihx =>
            simp only [List.map_cons, Function.comp, instPrefix_cons, ihx]
      simp only [List.map_map]
      rw [hmap]
      rfl

/-- A bvar `j < args.length` instantiates to `args[args.length - 1 - j]`
(innermost bvar 0 is the last arg; no leftover binder). -/
theorem instPrefix_bvar_lt {args : List (Expr Nat)} {j : Nat} {a : Expr Nat}
    (hj : j < args.length)
    (hget : args[args.length - 1 - j]? = some a) :
    instPrefix args (.bvar j) = a := by
  induction args generalizing j a with
  | nil =>
      simp only [List.length_nil] at hj
      exact (Nat.not_lt_zero _ hj).elim
  | cons a0 as ih =>
      simp only [List.length_cons] at hj hget
      rw [instPrefix_cons]
      have hinst :
          instantiate as.length (lift 0 as.length a0) (.bvar j) =
            if j = as.length then lift 0 as.length a0
            else if as.length < j then .bvar (j - 1)
            else .bvar j := rfl
      rw [hinst]
      by_cases heq : j = as.length
      · rw [if_pos heq]
        subst heq
        have hget0 : (a0 :: as)[0]? = some a := by
          have hidx : as.length + 1 - 1 - as.length = 0 := by omega
          rw [← hidx]
          exact hget
        have ha0 : a0 = a := by
          simp only [List.getElem?_cons_zero] at hget0
          injection hget0
        subst ha0
        exact instPrefix_lift as a0
      · rw [if_neg heq]
        by_cases hgt : as.length < j
        · exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ hj) hgt).elim
        · rw [if_neg hgt]
          have hlt : j < as.length := by omega
          have hget' : as[as.length - 1 - j]? = some a := by
            have hidx : as.length + 1 - 1 - j = (as.length - 1 - j) + 1 := by
              omega
            have hget0 : (a0 :: as)[as.length + 1 - 1 - j]? = some a := hget
            rw [hidx, List.getElem?_cons_succ] at hget0
            exact hget0
          exact ih hlt hget'

/-- Instantiate `e` under `args.length + 1` binders (the last binder
remains), substituting the outer `args` outermost-first. Remaining
free `bvar 0` is the uninstantiated last binder (the major). -/
def instTel : List (Expr Nat) → Expr Nat → Expr Nat
  | [], e => e
  | a :: as, e =>
      instTel as (instantiate (as.length + 1) (lift 0 (as.length + 1) a) e)

theorem instTel_nil (e : Expr Nat) : instTel [] e = e := rfl

theorem instTel_cons (a : Expr Nat) (as : List (Expr Nat)) (e : Expr Nat) :
    instTel (a :: as) e =
      instTel as (instantiate (as.length + 1) (lift 0 (as.length + 1) a) e) :=
  rfl

theorem instTel_bvar_zero (args : List (Expr Nat)) :
    instTel args (.bvar 0) = .bvar 0 := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      have hne : ¬ (0 = as.length + 1) := by omega
      have hnlt : ¬ (as.length + 1 < 0) := Nat.not_lt_zero _
      rw [instTel_cons, instantiate, if_neg hne, if_neg hnlt]
      exact ih

/-- Instantiating the remaining outer binders after a lift of
`as.length + 1` leaves a lift of 1 (the last binder). -/
theorem instTel_lift_succ (as : List (Expr Nat)) (a : Expr Nat) :
    instTel as (lift 0 (as.length + 1) a) = lift 0 1 a := by
  induction as generalizing a with
  | nil => rfl
  | cons a' as ih =>
      simp only [instTel_cons, List.length_cons]
      have hc : instantiate (as.length + 1) (lift 0 (as.length + 1) a')
          (lift 0 (as.length + 1 + 1) a) = lift 0 (as.length + 1) a := by
        have h1 : 0 ≤ as.length + 1 := Nat.zero_le _
        have h2 : as.length + 1 < (as.length + 1 + 1) + 0 := by omega
        have hcan := instantiate_lift_cancel (as.length + 1 + 1) 0
          (as.length + 1) (lift 0 (as.length + 1) a') h1 h2 a
        have hamt : as.length + 1 + 1 - 1 = as.length + 1 := by omega
        simp only [Nat.add_zero] at hcan
        rw [hamt] at hcan
        exact hcan
      rw [hc]
      exact ih a

theorem map_instTel_nil (xs : List (Expr Nat)) :
    xs.map (instTel []) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, instTel_nil, ih]

theorem instTel_foldApps (args : List (Expr Nat)) (f : Expr Nat)
    (xs : List (Expr Nat)) :
    instTel args (foldApps f xs) =
      foldApps (instTel args f) (xs.map (instTel args)) := by
  induction args generalizing f xs with
  | nil =>
      rw [instTel_nil, map_instTel_nil, instTel_nil]
  | cons a as ih =>
      rw [instTel_cons, foldApps_instantiate, ih]
      have hmap :
          xs.map (instTel as ∘ instantiate (as.length + 1)
            (lift 0 (as.length + 1) a)) =
          xs.map (instTel (a :: as)) := by
        induction xs with
        | nil => rfl
        | cons x xs ihx =>
            simp only [List.map_cons, Function.comp, instTel_cons, ihx]
      simp only [List.map_map]
      rw [hmap]
      rfl

theorem getElem?_drop {α} (xs : List α) (k i : Nat) :
    (xs.drop k)[i]? = xs[k + i]? := by
  induction k generalizing xs with
  | zero =>
      simp only [List.drop_zero, Nat.zero_add]
  | succ k ih =>
      cases xs with
      | nil =>
          simp only [List.drop_nil, List.getElem?_nil]
      | cons x xs =>
          simp only [List.drop_succ_cons]
          have ih' := ih xs
          rw [ih']
          have hidx : (k + 1) + i = (k + i) + 1 := by omega
          rw [hidx, List.getElem?_cons_succ]

theorem getElem?_take {α} (xs : List α) (n i : Nat) (hi : i < n) :
    (xs.take n)[i]? = xs[i]? := by
  induction n generalizing xs i with
  | zero =>
      exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
      cases xs with
      | nil =>
          simp only [List.take_nil, List.getElem?_nil]
      | cons x xs =>
          cases i with
          | zero =>
              simp only [List.take_succ_cons, List.getElem?_cons_zero]
          | succ i =>
              simp only [List.take_succ_cons, List.getElem?_cons_succ]
              exact ih xs i (Nat.succ_lt_succ_iff.mp hi)

/-- A positive bvar `j ≤ args.length` instantiates to the corresponding
outer argument, lifted under the remaining (major) binder. Outermost
arg is `bvar args.length`. -/
theorem instTel_bvar_at {args : List (Expr Nat)} {j : Nat} {a : Expr Nat}
    (hj : 0 < j) (hle : j ≤ args.length)
    (hget : args[args.length - j]? = some a) :
    instTel args (.bvar j) = lift 0 1 a := by
  induction args generalizing j a with
  | nil =>
      simp only [List.length_nil] at hle
      have : False := by omega
      exact this.elim
  | cons a0 as ih =>
      simp only [List.length_cons] at hle hget
      rw [instTel_cons]
      have hinst :
          instantiate (as.length + 1) (lift 0 (as.length + 1) a0) (.bvar j) =
            if j = as.length + 1 then lift 0 (as.length + 1) a0
            else if as.length + 1 < j then .bvar (j - 1)
            else .bvar j := rfl
      rw [hinst]
      by_cases heq : j = as.length + 1
      · rw [if_pos heq]
        subst heq
        have hget0 : (a0 :: as)[0]? = some a := by
          have hidx : as.length + 1 - (as.length + 1) = 0 := Nat.sub_self _
          rw [← hidx]
          exact hget
        have ha0 : a0 = a := by
          simp only [List.getElem?_cons_zero] at hget0
          injection hget0
        subst ha0
        exact instTel_lift_succ as a0
      · rw [if_neg heq]
        by_cases hgt : as.length + 1 < j
        · exact (Nat.not_lt_of_ge hle hgt).elim
        · rw [if_neg hgt]
          have hlt : j < as.length + 1 := by omega
          have hle' : j ≤ as.length := Nat.le_of_lt_succ hlt
          have hget' : as[as.length - j]? = some a := by
            have hidx : as.length + 1 - j = (as.length - j) + 1 := by omega
            have hget0 : (a0 :: as)[as.length + 1 - j]? = some a := hget
            rw [hidx, List.getElem?_cons_succ] at hget0
            exact hget0
          exact ih hj hle' hget'

theorem preMajor_motive_get {E : ResolvedEnv} (w : IotaWitness E) :
    ∃ m, w.preMajor[w.nparams]? = some m := by
  have hlen := w.hpre
  have hlt : w.nparams < w.preMajor.length := by omega
  refine ⟨w.preMajor[w.nparams]'hlt, ?_⟩
  exact List.getElem?_eq_getElem hlt

theorem instTel_motive {E : ResolvedEnv} (w : IotaWitness E) {m : Expr Nat}
    (hm : w.preMajor[w.nparams]? = some m) :
    instTel w.preMajor (.bvar (w.nMinors + w.nindices + 1)) = lift 0 1 m := by
  have hlen := w.hpre
  have hj : 0 < w.nMinors + w.nindices + 1 := Nat.succ_pos _
  have hle : w.nMinors + w.nindices + 1 ≤ w.preMajor.length := by omega
  have hget : w.preMajor[w.preMajor.length - (w.nMinors + w.nindices + 1)]? =
      some m := by
    have hidx : w.preMajor.length - (w.nMinors + w.nindices + 1) = w.nparams := by
      omega
    rw [hidx]
    exact hm
  exact instTel_bvar_at hj hle hget

theorem instTel_index {E : ResolvedEnv} (w : IotaWitness E) (i : Nat)
    (hi : i < w.nindices) {a : Expr Nat}
    (ha : w.preMajor[w.preMajor.length - (i + 1)]? = some a) :
    instTel w.preMajor (.bvar (i + 1)) = lift 0 1 a := by
  have hlen := w.hpre
  have hj : 0 < i + 1 := Nat.succ_pos _
  have hle : i + 1 ≤ w.preMajor.length := by omega
  exact instTel_bvar_at hj hle ha

theorem map_instTel_index_bvars {E : ResolvedEnv} (w : IotaWitness E) :
    ((List.range w.nindices).reverse.map (fun i => (Expr.bvar (i + 1) : Expr Nat))).map
      (instTel w.preMajor) =
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)).map (lift 0 1) := by
  have hlen := w.hpre
  have hdroplen : (w.preMajor.drop (w.nparams + 1 + w.nMinors)).length =
      w.nindices := by
    simp only [List.length_drop, hlen]
    omega
  refine List.ext_getElem ?hlen' ?hget
  · simp only [List.length_map, List.length_reverse, List.length_range, hdroplen]
  · intro i hi1 hi2
    have hi : i < w.nindices := by
      simp only [List.length_map, List.length_reverse, List.length_range] at hi1
      exact hi1
    have hi' : w.nindices - 1 - i < w.nindices := by omega
    have hltA : w.preMajor.length - ((w.nindices - 1 - i) + 1) <
        w.preMajor.length := by omega
    let a := w.preMajor[w.preMajor.length - ((w.nindices - 1 - i) + 1)]'hltA
    have ha : w.preMajor[w.preMajor.length - ((w.nindices - 1 - i) + 1)]? =
        some a := List.getElem?_eq_getElem hltA
    have hinst := instTel_index w (w.nindices - 1 - i) hi' ha
    have hleft :
        (((List.range w.nindices).reverse.map
            (fun k => (Expr.bvar (k + 1) : Expr Nat))).map
          (instTel w.preMajor))[i]'hi1 =
          instTel w.preMajor (.bvar ((w.nindices - 1 - i) + 1)) := by
      simp only [List.getElem_map]
      rw [List.getElem_reverse, List.getElem_range]
      simp only [List.length_range]
    have hpos : i < (w.preMajor.drop (w.nparams + 1 + w.nMinors)).length := by
      rw [hdroplen]; exact hi
    have hdrop : (w.preMajor.drop (w.nparams + 1 + w.nMinors))[i]'hpos = a := by
      have hsome : (w.preMajor.drop (w.nparams + 1 + w.nMinors))[i]? = some a := by
        rw [getElem?_drop]
        have hidx' : w.nparams + 1 + w.nMinors + i =
            w.preMajor.length - ((w.nindices - 1 - i) + 1) := by omega
        rw [hidx']
        exact ha
      have ⟨_, heq⟩ := List.getElem?_eq_some.mp hsome
      exact heq
    rw [hleft, hinst]
    simp only [List.getElem_map]
    exact congrArg (lift 0 1) hdrop.symm

/-- 05 §13 after outer instantiation: last Π-body is `F major` as
`app (lift 0 1 F) (bvar 0)`, `F = foldApps motive indices`. -/
theorem instTel_hrecBody {E : ResolvedEnv} (w : IotaWitness E) {m : Expr Nat}
    (hm : w.preMajor[w.nparams]? = some m) :
    instTel w.preMajor w.recBody =
      .app (lift 0 1 (foldApps m
        (w.preMajor.drop (w.nparams + 1 + w.nMinors)))) (.bvar 0) := by
  rw [w.hrecBody]
  change instTel w.preMajor (recBodyExpr w.nMinors w.nindices) =
    .app (lift 0 1 (foldApps m
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)))) (.bvar 0)
  unfold recBodyExpr
  rw [instTel_foldApps, List.map_append, List.map_cons, List.map_nil,
    instTel_bvar_zero, map_instTel_index_bvars, instTel_motive w hm,
    foldApps_snoc, foldApps_lift]

/-- Motive slot of `recPrefix ++ idx` is the same as of `preMajor`. -/
theorem instTel_motive_idx {E : ResolvedEnv} (w : IotaWitness E)
    (idx : List (Expr Nat)) (hidxlen : idx.length = w.nindices)
    {m : Expr Nat} (hm : w.preMajor[w.nparams]? = some m) :
    instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
      (.bvar (w.nMinors + w.nindices + 1)) = lift 0 1 m := by
  let args := recPrefix w.preMajor w.nparams w.nMinors ++ idx
  have hprelen :
      (recPrefix w.preMajor w.nparams w.nMinors).length =
        w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre
    omega
  have hargs : args.length = w.nparams + 1 + w.nMinors + w.nindices := by
    simp only [args, List.length_append, hprelen, hidxlen]
  have hj : 0 < w.nMinors + w.nindices + 1 := Nat.succ_pos _
  have hle : w.nMinors + w.nindices + 1 ≤ args.length := by
    rw [hargs]; omega
  have hget : args[args.length - (w.nMinors + w.nindices + 1)]? = some m := by
    have hpos : args.length - (w.nMinors + w.nindices + 1) = w.nparams := by
      rw [hargs]; omega
    rw [hpos]
    have hlt : w.nparams <
        (recPrefix w.preMajor w.nparams w.nMinors).length := by
      rw [hprelen]; omega
    have happ := List.getElem?_append_left (l₂ := idx) hlt
    have htk := getElem?_take w.preMajor (w.nparams + 1 + w.nMinors)
      w.nparams (by omega)
    exact happ.trans (htk.trans hm)
  exact instTel_bvar_at hj hle hget

/-- Index bvars of `recBody` instantiate to `idx` under `recPrefix ++ idx`. -/
theorem map_instTel_index_bvars_idx {E : ResolvedEnv} (w : IotaWitness E)
    (idx : List (Expr Nat)) (hidxlen : idx.length = w.nindices) :
    ((List.range w.nindices).reverse.map
        (fun i => (Expr.bvar (i + 1) : Expr Nat))).map
      (instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)) =
      idx.map (lift 0 1) := by
  let args := recPrefix w.preMajor w.nparams w.nMinors ++ idx
  have hprelen :
      (recPrefix w.preMajor w.nparams w.nMinors).length =
        w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre
    omega
  have hargs : args.length = w.nparams + 1 + w.nMinors + w.nindices := by
    simp only [args, List.length_append, hprelen, hidxlen]
  refine List.ext_getElem ?hlen' ?hget
  · simp only [List.length_map, List.length_reverse, List.length_range,
      hidxlen]
  · intro i hi1 hi2
    have hi : i < w.nindices := by
      simp only [List.length_map, List.length_reverse, List.length_range] at hi1
      exact hi1
    have hj : 0 < w.nindices - i := by omega
    have hle : w.nindices - i ≤ args.length := by
      rw [hargs]; omega
    have hpos : i < idx.length := by rw [hidxlen]; exact hi
    let a := idx[i]'hpos
    have ha : idx[i]? = some a := List.getElem?_eq_getElem hpos
    have hgetA : args[args.length - (w.nindices - i)]? = some a := by
      have hidxpos' : args.length - (w.nindices - i) =
          (recPrefix w.preMajor w.nparams w.nMinors).length + i := by
        rw [hargs, hprelen]; omega
      rw [hidxpos']
      have hdrop := getElem?_drop args
        (recPrefix w.preMajor w.nparams w.nMinors).length i
      have hl : args.drop (recPrefix w.preMajor w.nparams w.nMinors).length =
          idx := List.drop_left _ _
      rw [← hdrop, hl]
      exact ha
    have hinst := instTel_bvar_at (args := args)
      (j := w.nindices - i) hj hle hgetA
    have hleft :
        (((List.range w.nindices).reverse.map
            (fun k => (Expr.bvar (k + 1) : Expr Nat))).map
          (instTel args))[i]'hi1 =
          instTel args (.bvar ((w.nindices - 1 - i) + 1)) := by
      simp only [List.getElem_map]
      rw [List.getElem_reverse, List.getElem_range]
      simp only [List.length_range]
    have hj' : (w.nindices - 1 - i) + 1 = w.nindices - i := by omega
    rw [hleft, hj', hinst]
    simp only [List.getElem_map]

/-- 05 §13 last Π-body after `recPrefix ++ idx`: `motive idx major`. -/
theorem instTel_hrecBody_idx {E : ResolvedEnv} (w : IotaWitness E)
    (idx : List (Expr Nat)) (hidxlen : idx.length = w.nindices)
    {m : Expr Nat} (hm : w.preMajor[w.nparams]? = some m) :
    instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx) w.recBody =
      .app (lift 0 1 (foldApps m idx)) (.bvar 0) := by
  rw [w.hrecBody]
  change instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
      (recBodyExpr w.nMinors w.nindices) =
    .app (lift 0 1 (foldApps m idx)) (.bvar 0)
  unfold recBodyExpr
  rw [instTel_foldApps, List.map_append, List.map_cons, List.map_nil,
    instTel_bvar_zero, map_instTel_index_bvars_idx w idx hidxlen,
    instTel_motive_idx w idx hidxlen hm, foldApps_snoc, foldApps_lift]

def peelPis_succ {n : Nat} {T : Expr Nat} {ds : List (Expr Nat)}
    {r : Expr Nat} (h : peelPis (n + 1) T = some (ds, r)) :
    Σ' (A B : Expr Nat) (ds' : List (Expr Nat)),
      (T = .pi A B) ×' (ds = A :: ds') ×' (peelPis n B = some (ds', r)) := by
  cases T with
  | pi A B =>
      cases hpeel : peelPis n B with
      | none =>
          simp only [peelPis, hpeel] at h
          exact Option.noConfusion h
      | some pr =>
          simp only [peelPis, hpeel] at h
          injection h with hpair
          injection hpair with hds hr
          cases pr with
          | mk ds' r' =>
              subst hds
              subst hr
              exact ⟨A, B, ds', rfl, rfl, hpeel⟩
  | bvar _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | sort _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | const _ _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | app _ _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | lam _ _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | letE _ _ _ =>
      simp only [peelPis] at h; exact Option.noConfusion h
  | lit _ =>
      simp only [peelPis] at h; exact Option.noConfusion h

/-- Peeling after `instantiate` only needs the inner body: the remaining
body is instantiated at index `j + n`, replacement lifted by `n`. -/
def peelPis_instantiate_body (n j : Nat) (v e : Expr Nat)
    {ds : List (Expr Nat)} {r : Expr Nat}
    (h : peelPis n e = some (ds, r)) :
    Σ' (ds' : List (Expr Nat)),
      peelPis n (instantiate j v e) =
        some (ds', instantiate (j + n) (lift 0 n v) r) := by
  induction n generalizing j v e ds r with
  | zero =>
      simp only [peelPis] at h
      injection h with hpair
      injection hpair with hds hr
      subst hds
      subst hr
      refine ⟨[], ?_⟩
      simp only [peelPis, Nat.add_zero, lift_zero]
  | succ n ih =>
      have ⟨A, B, ds', hE, hds, hpeel⟩ := peelPis_succ h
      subst hE
      subst hds
      simp only [instantiate, peelPis]
      have ⟨ds'', hinner⟩ := ih (j + 1) (lift 0 1 v) B hpeel
      refine ⟨instantiate j v A :: ds'', ?_⟩
      simp only [hinner]
      have hidx : j + 1 + n = j + (n + 1) := by omega
      have hlift : lift 0 n (lift 0 1 v) = lift 0 (n + 1) v := by
        have hmerge := lift_lift_merge n 1 0 0 (Nat.le_refl 0) (by omega) v
        simp only [Nat.add_comm 1 n] at hmerge
        exact hmerge
      rw [hidx, hlift]

/-- Instantiating a peeled telescope instantiates the domain at index
`k` by `instantiate (j+k) (lift 0 k v)`. -/
theorem peelPis_instantiate_get (n k j : Nat) (v e : Expr Nat)
    {ds : List (Expr Nat)} {r D : Expr Nat}
    (h : peelPis n e = some (ds, r))
    (hk : ds[k]? = some D) :
    ∀ {ds' : List (Expr Nat)} {r' : Expr Nat},
      peelPis n (instantiate j v e) = some (ds', r') →
        ds'[k]? = some (instantiate (j + k) (lift 0 k v) D) := by
  induction n generalizing k j v e ds r D with
  | zero =>
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds _
      subst hds
      simp only [List.getElem?_nil] at hk
      exact Option.noConfusion hk
  | succ n ih =>
      have ⟨A, B, ds1, hE, hds, hpeel⟩ := peelPis_succ h
      subst hE
      subst hds
      intro ds' r' hinst
      simp only [instantiate, peelPis] at hinst
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero] at hk
          injection hk with hD
          subst hD
          cases hinner : peelPis n (instantiate (j + 1) (lift 0 1 v) B) with
          | none =>
              simp only [hinner] at hinst
              exact Option.noConfusion hinst
          | some pr =>
              simp only [hinner] at hinst
              injection hinst with hpair
              injection hpair with hds' _
              subst hds'
              cases pr with
              | mk ds1' r1' =>
                  simp only [List.getElem?_cons_zero, Nat.add_zero, lift_zero]
      | succ k' =>
          simp only [List.getElem?_cons_succ] at hk
          have ⟨ds'', hinner0⟩ :=
            peelPis_instantiate_body n (j + 1) (lift 0 1 v) B hpeel
          cases hinner : peelPis n (instantiate (j + 1) (lift 0 1 v) B) with
          | none =>
              simp only [hinner] at hinst
              exact Option.noConfusion hinst
          | some pr =>
              simp only [hinner] at hinst
              injection hinst with hpair
              injection hpair with hds' _
              subst hds'
              cases pr with
              | mk ds1' r1' =>
                  have hget :=
                    ih k' (j + 1) (lift 0 1 v) B hpeel hk hinner
                  simp only [List.getElem?_cons_succ]
                  have hidx : j + 1 + k' = j + (k' + 1) := by omega
                  have hlift : lift 0 k' (lift 0 1 v) = lift 0 (k' + 1) v := by
                    have hmerge :=
                      lift_lift_merge k' 1 0 0 (Nat.le_refl 0) (by omega) v
                    simp only [Nat.add_comm 1 k'] at hmerge
                    exact hmerge
                  rw [hidx, hlift] at hget
                  exact hget

/-- Last remaining Π after applying `args` to a `(args.length+1)`-Π:
the last peeled domain, instantiated with `instPrefix` (no leftover
binder). -/
def applyTel_last_dom :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (args.length + 1) T = some (ds, r) →
    {D : Expr Nat} →
    ds[args.length]? = some D →
    Σ' (B : Expr Nat),
      applyTel args T = some (Expr.pi (instPrefix args D) B)
  | [], T, ds, r, hpeel, D, hD => by
      have ⟨A, B, ds', hT, hds, h0⟩ := peelPis_succ (n := 0) hpeel
      subst hT
      subst hds
      simp only [peelPis] at h0
      injection h0 with hp
      injection hp with hds' hr
      subst hds'
      subst hr
      simp only [List.length_nil, List.getElem?_cons_zero] at hD
      injection hD with hDA
      subst hDA
      exact ⟨B, rfl⟩
  | a :: as, T, ds, r, hpeel, D, hD => by
      have ⟨A0, B0, ds', hT, hds, hpeel'⟩ :=
        peelPis_succ (n := as.length + 1) hpeel
      subst hT
      subst hds
      simp only [List.length_cons, List.getElem?_cons_succ] at hD
      have ⟨ds'', hinstP⟩ :=
        peelPis_instantiate_body (as.length + 1) 0 a B0 hpeel'
      simp only [instantiate0, Nat.zero_add] at hinstP
      have hD' :
          ds''[as.length]? =
            some (instantiate as.length (lift 0 as.length a) D) := by
        have hgot :=
          peelPis_instantiate_get (as.length + 1) as.length 0 a B0
            hpeel' hD hinstP
        simp only [Nat.zero_add] at hgot
        exact hgot
      have ⟨B, happ⟩ :=
        applyTel_last_dom as (instantiate0 a B0) hinstP hD'
      refine ⟨B, ?_⟩
      simp only [applyTel_cons_pi, instPrefix_cons]
      exact happ

theorem peelPis_isPiTel :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → isPiTel n T = true
  | 0, _, _, _, _ => rfl
  | n + 1, .pi A B, _, _, h => by
      have ⟨A', B', ds', hT, _, hpeel⟩ := peelPis_succ (n := n) h
      injection hT with hA hB
      subst hA
      subst hB
      simp only [isPiTel]
      exact peelPis_isPiTel n B hpeel
  | n + 1, .bvar _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .sort _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .const _ _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .app _ _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .lam _ _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .letE _ _ _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .lit _, _, _, h => by
      simp only [peelPis] at h; exact Option.noConfusion h

/-- Remaining minor Π after params+motive+previous minors. R-class:
computed from `recMember.mtype` and `preMajor` lengths, not a
witness equation. Stated at an ARBITRARY level instantiation of the
stored recursor type (00 §20.6 STORED-TYPE VIEWS): `peelPis` never
substitutes, so the Π-telescope shape is level-blind, and this is the
computation whose result `IotaTyping.hminDom` names at `lvls := w.ls`.
The raw form is the instance `lvls := []` (`instantiateLevels_nil`). -/
def recMinorDom {E : ResolvedEnv} (w : IotaWitness E) (lvls : List Level) :
    Σ' (mdom restMin : Expr Nat),
      applyTel (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
        (instantiateLevels lvls w.recMember.mtype) =
        some (Expr.pi mdom restMin) := by
  have htelR : isPiTel
      (w.nparams + 1 + w.nMinors + w.nindices + 1)
      (instantiateLevels lvls w.recMember.mtype) =
        true :=
    peelPis_isPiTel _ _
      (peelPis_instantiateLevels lvls _ _ w.hpeelRec)
  have hm : w.nparams + 1 + w.ctorIdx ≤
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have := w.hidx; omega
  have hm1 : w.nparams + 1 + w.ctorIdx + 1 ≤
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have := w.hidx; omega
  have hlenPref :
      (w.preMajor.take (w.nparams + 1 + w.ctorIdx)).length =
        w.nparams + 1 + w.ctorIdx := by
    simp only [List.length_take, w.hpre]; omega
  have ⟨U, hU⟩ := applyTel_isPiTel (w.nparams + 1 + w.ctorIdx)
    (instantiateLevels lvls w.recMember.mtype)
    (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
    hlenPref (isPiTel_le hm htelR)
  have ⟨A, B, hpi⟩ := applyTel_drop1_pi (w.nparams + 1 + w.ctorIdx)
    (instantiateLevels lvls w.recMember.mtype)
    (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
    hlenPref (isPiTel_le hm1 htelR) hU
  exact ⟨A, B, hU.trans (congrArg some hpi)⟩

def peelPis_after_applyTel (n m : Nat) :
    (xs : List (Expr Nat)) → (T : Expr Nat) →
    xs.length = n →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (n + m) T = some (ds, r) →
    {U : Expr Nat} →
    applyTel xs T = some U →
    Σ' (ds' : List (Expr Nat)) (r' : Expr Nat),
      peelPis m U = some (ds', r')
  | [], T, hlen, ds, r, hpeel, U, happ => by
      have hn : n = 0 := hlen.symm
      subst hn
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      simp only [Nat.zero_add] at hpeel
      exact ⟨ds, r, hpeel⟩
  | x :: xs, T, hlen, ds, r, hpeel, U, happ => by
      simp only [List.length_cons] at hlen
      have hn : n = xs.length + 1 := hlen.symm
      subst hn
      have hidx : xs.length + 1 + m = (xs.length + m) + 1 := by omega
      rw [hidx] at hpeel
      have ⟨A, B, ds', hT, _, hinner⟩ := peelPis_succ (n := xs.length + m) hpeel
      subst hT
      simp only [applyTel] at happ
      have ⟨_, hinst⟩ :=
        peelPis_instantiate_body (xs.length + m) 0 x B hinner
      simp only [instantiate0, Nat.zero_add] at hinst
      exact peelPis_after_applyTel xs.length m xs (instantiate0 x B)
        rfl hinst happ

def lastPi_after_args :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (args.length + 1) T = some (ds, r) →
    Σ' (A : Expr Nat),
      applyTel args T = some (Expr.pi A (instTel args r))
  | [], T, ds, r, h => by
      have ⟨A, B, ds', hT, hds, hpeel⟩ := peelPis_succ (n := 0) h
      subst hT
      simp only [peelPis] at hpeel
      injection hpeel with hpair
      injection hpair with hds' hr
      subst hr
      exact ⟨A, by simp only [applyTel_nil, instTel_nil]⟩
  | a :: as, T, ds, r, h => by
      have ⟨A0, B0, ds', hT, hds, hpeel⟩ :=
        peelPis_succ (n := as.length + 1) h
      subst hT
      subst hds
      simp only [List.length_cons, applyTel_cons_pi]
      have ⟨ds'', hinst⟩ :=
        peelPis_instantiate_body (as.length + 1) 0 a B0 hpeel
      simp only [instantiate0, Nat.zero_add] at hinst
      have ⟨A, happ⟩ := lastPi_after_args as (instantiate0 a B0) hinst
      refine ⟨A, ?_⟩
      rw [happ]
      simp only [instTel_cons]

/-- 05 §13 recursor signature as stored on the witness:
`peelPis` of the recursor type yields `recDoms` and the body
`motive indices major` (de Bruijn). -/
theorem recursor_sig {E : ResolvedEnv} (w : IotaWitness E) :
    peelPis (w.nparams + 1 + w.nMinors + w.nindices + 1) w.recMember.mtype =
      some (w.recDoms,
        foldApps (.bvar (w.nMinors + w.nindices + 1))
          ((List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
            [Expr.bvar 0])) := by
  rw [w.hpeelRec, w.hrecBody]

/-- Instantiating the 05 §13 major-type de Bruijn form with
`params ++ motive ++ minors ++ idx` yields `I params idx`. Motive
and minors do not occur. -/
theorem instPrefix_majorTy (args : List (Expr Nat))
    (familyRef : Nat) (ls : List Level)
    (nparams nMinors nindices : Nat)
    (hlen : args.length = nparams + 1 + nMinors + nindices)
    {params idx : List (Expr Nat)}
    (hp : args.take nparams = params)
    (hi : args.drop (nparams + 1 + nMinors) = idx)
    (hidxlen : idx.length = nindices) :
    instPrefix args (majorTyExpr familyRef ls nparams nMinors nindices) =
      foldApps (.const familyRef ls) (params ++ idx) := by
  simp only [majorTyExpr]
  rw [instPrefix_foldApps, instPrefix_const, List.map_append]
  have hpar :
      ((List.range nparams).reverse.map
        (fun i => (Expr.bvar (i + nindices + nMinors + 1) : Expr Nat))).map
        (instPrefix args) = params := by
    refine List.ext_getElem ?hlenP ?hgetP
    · simp only [List.length_map, List.length_reverse, List.length_range]
      have : params.length = nparams := by
        rw [← hp, List.length_take, hlen]
        omega
      exact this.symm
    · intro k hk1 hk2
      have hk : k < nparams := by
        simp only [List.length_map, List.length_reverse, List.length_range]
          at hk1
        exact hk1
      have hget : args[args.length - 1 -
          (nparams - 1 - k + nindices + nMinors + 1)]? =
          some (params[k]'hk2) := by
        have hidx : args.length - 1 -
            (nparams - 1 - k + nindices + nMinors + 1) = k := by
          omega
        rw [hidx]
        have hpos : k < params.length := hk2
        have htake : (args.take nparams)[k]? = some (params[k]'hpos) := by
          rw [hp]
          exact List.getElem?_eq_getElem hpos
        have htk := getElem?_take args nparams k hk
        rw [htk] at htake
        exact htake
      have hinst := instPrefix_bvar_lt
        (j := nparams - 1 - k + nindices + nMinors + 1) (by omega) hget
      simp only [List.getElem_map]
      rw [List.getElem_reverse, List.getElem_range]
      simp only [List.length_range]
      exact hinst
  have hidx :
      ((List.range nindices).reverse.map
        (fun i => (Expr.bvar i : Expr Nat))).map
        (instPrefix args) = idx := by
    refine List.ext_getElem ?hlenI ?hgetI
    · simp only [List.length_map, List.length_reverse, List.length_range]
      exact hidxlen.symm
    · intro k hk1 hk2
      have hk : k < nindices := by
        simp only [List.length_map, List.length_reverse, List.length_range]
          at hk1
        exact hk1
      have hget : args[args.length - 1 - (nindices - 1 - k)]? =
          some (idx[k]'hk2) := by
        have hidx' : args.length - 1 - (nindices - 1 - k) =
            nparams + 1 + nMinors + k := by omega
        rw [hidx']
        have hpos : k < idx.length := hk2
        have hdrop' : (args.drop (nparams + 1 + nMinors))[k]? =
            some (idx[k]'hpos) := by
          rw [hi]
          exact List.getElem?_eq_getElem hpos
        have hdrop := getElem?_drop args (nparams + 1 + nMinors) k
        rw [hdrop] at hdrop'
        exact hdrop'
      have hinst := instPrefix_bvar_lt (j := nindices - 1 - k)
        (by omega) hget
      simp only [List.getElem_map]
      rw [List.getElem_reverse, List.getElem_range]
      simp only [List.length_range]
      exact hinst
  rw [hpar, hidx]

/-- Split a mapped list at a prefix whose image is already named. -/
theorem map_take_drop_split {α β : Type} (f : α → β) (k : Nat) (l : List α)
    {ps : List β} (h : (l.take k).map f = ps) :
    l.map f = ps ++ (l.drop k).map f := by
  rw [← h, ← List.map_append, List.take_append_drop]

/-- `applyTel` of a FULL telescope: the result is `instPrefix args` of
the peeled body. Zero-leftover sibling of `applyTel_last_dom`. -/
def applyTel_peelPis_result :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis args.length T = some (ds, r) →
    applyTel args T = some (instPrefix args r)
  | [], T, ds, r, hpeel => by
      simp only [List.length_nil, peelPis] at hpeel
      injection hpeel with hp
      injection hp with _hds hr
      subst hr
      simp only [applyTel, instPrefix]
  | a :: as, T, ds, r, hpeel => by
      have ⟨A0, B0, _ds', hT, _hds, hpeel'⟩ :=
        peelPis_succ (n := as.length) hpeel
      subst hT
      have ⟨_ds'', hinstP⟩ :=
        peelPis_instantiate_body as.length 0 a B0 hpeel'
      simp only [instantiate0, Nat.zero_add] at hinstP
      have hrec := applyTel_peelPis_result as (instantiate0 a B0) hinstP
      simp only [applyTel_cons_pi, instPrefix_cons]
      exact hrec

/-- The 05 §6 PARAMETER prefix of a constructor result instantiates to
the parameters supplied to the telescope. This is the `hpar` half of
`instPrefix_majorTy`, stated for an arbitrary tail: only the first
`nparams` result arguments are pinned (00 §20.5). -/
theorem instPrefix_paramPrefix (args : List (Expr Nat))
    (nparams nfields : Nat)
    (hlen : args.length = nparams + nfields)
    {ps : List (Expr Nat)} (hp : args.take nparams = ps) :
    ((List.range nparams).reverse.map
        (fun i => (Expr.bvar (i + nfields) : Expr Nat))).map
        (instPrefix args) = ps := by
  refine List.ext_getElem ?hlenP ?hgetP
  · simp only [List.length_map, List.length_reverse, List.length_range]
    have hps : ps.length = nparams := by
      rw [← hp, List.length_take, hlen]
      omega
    exact hps.symm
  · intro k hk1 hk2
    have hk : k < nparams := by
      simp only [List.length_map, List.length_reverse, List.length_range]
        at hk1
      exact hk1
    have hget : args[args.length - 1 - (nparams - 1 - k + nfields)]? =
        some (ps[k]'hk2) := by
      have hidx : args.length - 1 - (nparams - 1 - k + nfields) = k := by
        omega
      rw [hidx]
      have hpos : k < ps.length := hk2
      have htake : (args.take nparams)[k]? = some (ps[k]'hpos) := by
        rw [hp]
        exact List.getElem?_eq_getElem hpos
      have htk := getElem?_take args nparams k hk
      rw [htk] at htake
      exact htake
    have hinst := instPrefix_bvar_lt
      (j := nparams - 1 - k + nfields) (by omega) hget
    simp only [List.getElem_map]
    rw [List.getElem_reverse, List.getElem_range]
    simp only [List.length_range]
    exact hinst

/-- 05 §6 constructor result, instantiated: the family applied to the
supplied parameters followed by the (instantiated) result indices.
Consumes `ctorResultParamShape` (00 §20.5 declaration-level T-class).
Chained in `Σ'` (00 §18.3 rule 1). -/
def instPrefix_ctorResult {fam : Nat} {res : Expr Nat}
    {nU nparams nfields : Nat}
    (h : ctorResultParamShape fam res nU nparams nfields = true)
    (args : List (Expr Nat)) (hlen : args.length = nparams + nfields)
    {ps : List (Expr Nat)} (hp : args.take nparams = ps) :
    Σ' (idx : List (Expr Nat)),
      instPrefix args res =
        foldApps (Expr.const fam ((List.range nU).map Level.param))
          (ps ++ idx) := by
  have hfold : foldApps (appsSpine res).1 (appsSpine res).2 = res :=
    foldApps_appsSpine res
  simp only [ctorResultParamShape] at h
  cases hhead : (appsSpine res).1 with
  | const r lsR =>
      simp only [hhead] at h
      have ⟨hrl, htk⟩ := bool_and_true h
      have ⟨hr, hlv⟩ := bool_and_true hrl
      have hrfam : r = fam := of_decide_eq_true hr
      subst hrfam
      have hlsR : lsR = (List.range nU).map Level.param :=
        of_decide_eq_true hlv
      subst hlsR
      have htake : (appsSpine res).2.take nparams =
          (List.range nparams).reverse.map
            (fun i => (Expr.bvar (i + nfields) : Expr Nat)) :=
        of_decide_eq_true htk
      refine ⟨((appsSpine res).2.drop nparams).map (instPrefix args), ?_⟩
      have hres :
          foldApps (Expr.const r ((List.range nU).map Level.param))
            (appsSpine res).2 = res := by
        rw [← hhead]; exact hfold
      have hstep :
          instPrefix args (foldApps
              (Expr.const r ((List.range nU).map Level.param))
              (appsSpine res).2) =
            foldApps (Expr.const r ((List.range nU).map Level.param))
              ((appsSpine res).2.map (instPrefix args)) := by
        rw [instPrefix_foldApps, instPrefix_const]
      rw [hres] at hstep
      rw [hstep]
      have hmapP :
          ((appsSpine res).2.take nparams).map (instPrefix args) = ps := by
        rw [htake]
        exact instPrefix_paramPrefix args nparams nfields hlen hp
      rw [map_take_drop_split (instPrefix args) nparams (appsSpine res).2 hmapP]
  | bvar _ => simp only [hhead] at h; nomatch h
  | sort _ => simp only [hhead] at h; nomatch h
  | app _ _ => simp only [hhead] at h; nomatch h
  | lam _ _ => simp only [hhead] at h; nomatch h
  | pi _ _ => simp only [hhead] at h; nomatch h
  | letE _ _ _ => simp only [hhead] at h; nomatch h
  | lit _ => simp only [hhead] at h; nomatch h

/-- 00 §20.6 STORED-TYPE VIEWS: 05 §6 read at the INSTANTIATED
constructor result. The stored result carries 05 §2's canonical
universe vector, so `instantiateLevels lvls` turns the family head into
exactly `lvls.take nU` — the SAME head `applyTel_recPrefix_idx_last`
produces on the recursor side. The two heads are what
`FamAppConvInj`'s LEVEL half then compares; without the pinned vector
the constructor head was an unconstrained existential `lsR` and no
comparison was possible. -/
def instPrefix_ctorResult_inst {fam : Nat} {res : Expr Nat}
    {nU nparams nfields : Nat}
    (h : ctorResultParamShape fam res nU nparams nfields = true)
    (lvls : List Level) (hnU : nU ≤ lvls.length)
    (args : List (Expr Nat)) (hlen : args.length = nparams + nfields)
    {ps : List (Expr Nat)} (hp : args.take nparams = ps) :
    Σ' (idx : List (Expr Nat)),
      instPrefix args (instantiateLevels lvls res) =
        foldApps (Expr.const fam (lvls.take nU)) (ps ++ idx) := by
  have hfold : foldApps (appsSpine res).1 (appsSpine res).2 = res :=
    foldApps_appsSpine res
  simp only [ctorResultParamShape] at h
  cases hhead : (appsSpine res).1 with
  | const r lsR =>
      simp only [hhead] at h
      have ⟨hrl, htk⟩ := bool_and_true h
      have ⟨hr, hlv⟩ := bool_and_true hrl
      have hrfam : r = fam := of_decide_eq_true hr
      subst hrfam
      have hlsR : lsR = (List.range nU).map Level.param :=
        of_decide_eq_true hlv
      subst hlsR
      have htake : (appsSpine res).2.take nparams =
          (List.range nparams).reverse.map
            (fun i => (Expr.bvar (i + nfields) : Expr Nat)) :=
        of_decide_eq_true htk
      have hres :
          foldApps (Expr.const r ((List.range nU).map Level.param))
            (appsSpine res).2 = res := by
        rw [← hhead]; exact hfold
      have hIL : instantiateLevels lvls res =
          foldApps (Expr.const r (lvls.take nU))
            ((appsSpine res).2.map (instantiateLevels lvls)) := by
        have h1 : instantiateLevels lvls res =
            instantiateLevels lvls
              (foldApps (Expr.const r ((List.range nU).map Level.param))
                (appsSpine res).2) := by
          rw [hres]
        rw [h1, foldApps_instantiateLevels]
        simp only [instantiateLevels]
        rw [map_instLevel_canonical nU lvls hnU]
      refine ⟨(((appsSpine res).2.map (instantiateLevels lvls)).drop
        nparams).map (instPrefix args), ?_⟩
      rw [hIL, instPrefix_foldApps, instPrefix_const]
      have hmapP :
          (((appsSpine res).2.map (instantiateLevels lvls)).take
            nparams).map (instPrefix args) = ps := by
        rw [← List.map_take, htake,
          map_instantiateLevels_bvars lvls (fun i => i + nfields)
            ((List.range nparams).reverse)]
        exact instPrefix_paramPrefix args nparams nfields hlen hp
      rw [map_take_drop_split (instPrefix args) nparams
        ((appsSpine res).2.map (instantiateLevels lvls)) hmapP]
  | bvar _ => simp only [hhead] at h; nomatch h
  | sort _ => simp only [hhead] at h; nomatch h
  | app _ _ => simp only [hhead] at h; nomatch h
  | lam _ _ => simp only [hhead] at h; nomatch h
  | pi _ _ => simp only [hhead] at h; nomatch h
  | letE _ _ _ => simp only [hhead] at h; nomatch h
  | lit _ => simp only [hhead] at h; nomatch h

/-- 05 §6 at an arbitrary parameter list: applying `ps ++ fs` to the
constructor's stored type — read through the 00 §20.6 view
`instantiateLevels lvls` — yields the family applied to `ps` and the
result indices, at the head `lvls.take famMember.arity`. The ctor-side
instance (`lvls := w.lsC`, `ps := w.ctorParams`, §20.6 view (3)) is the
left-hand side of the conversion `FamAppConvInj` consumes; the
recursor-side instance is `lvls := w.ls` (view (1)/(2)).

Footprint (M-003, statement change): the level list is now a PARAMETER
and the new premise `hnU : famMember.arity ≤ lvls.length` is required.
It is not a weakening — the conclusion's head went from an
existentially quantified `lsR` to the named `lvls.take famMember.arity`
— but it does have to be discharged at every call site. Its supplier is
`HasTy.const`'s `hlen` (`|ls| = member.arity`) together with 05 §3 /
00 §20.6 group arity coherence on `EnvWf.indMember`
(`famMember.arity = ctorMember.arity`, `recMember.arity ∈ {nU, nU+1}`),
which is F-04 / W3 work; this file cannot see `EnvWf`. -/
def ctorSpine_famApp {E : ResolvedEnv} (w : IotaWitness E)
    (hshape : ctorResultParamShape w.familyRef w.ctorResult
      w.famMember.arity w.nparams w.kinds.length = true)
    (lvls : List Level) (hnU : w.famMember.arity ≤ lvls.length)
    (ps fs : List (Expr Nat))
    (hps : ps.length = w.nparams) (hfs : fs.length = w.fields.length) :
    Σ' (idx : List (Expr Nat)),
      applyTel (ps ++ fs) (instantiateLevels lvls w.ctorMember.mtype) =
        some (foldApps (Expr.const w.familyRef (lvls.take w.famMember.arity))
          (ps ++ idx)) := by
  have hlen : (ps ++ fs).length = w.nparams + w.fields.length := by
    simp only [List.length_append, hps, hfs]
  have hpeel : peelPis (ps ++ fs).length w.ctorMember.mtype =
      some (w.ctorDoms, w.ctorResult) := by
    rw [hlen]; exact w.hpeel
  have hpeelI := peelPis_instantiateLevels lvls (ps ++ fs).length
    w.ctorMember.mtype hpeel
  have happ := applyTel_peelPis_result (ps ++ fs)
    (instantiateLevels lvls w.ctorMember.mtype) hpeelI
  have hlen' : (ps ++ fs).length = w.nparams + w.kinds.length := by
    rw [hlen, w.hlen]
  have htk : (ps ++ fs).take w.nparams = ps := by
    rw [← hps]
    exact List.take_left ps fs
  have ⟨idx, heq⟩ :=
    instPrefix_ctorResult_inst hshape lvls hnU (ps ++ fs) hlen' htk
  exact ⟨idx, by rw [happ, heq]⟩

/-- 05 §13: applying `recPrefix ++ idx` to the recursor type — read
through the 00 §20.6 recursor-side view `instantiateLevels w.ls` —
leaves `Π (I (w.ls.take nU) params idx) _`. The leftover body is
identified separately (`instTel` of `recBody`).

The head `w.ls.take w.famMember.arity` is now DERIVED, not asserted:
`hmajorTy` states the RAW stored domain, which carries 05 §2's
canonical vector, and `instantiateLevels_majorTyExpr` +
`map_instLevel_canonical` map that vector to `w.ls.take nU`.

Footprint (M-003, statement change): new premise
`hnU : w.famMember.arity ≤ w.ls.length`, supplied by `HasTy.const`'s
`hlen` plus 00 §20.6 group arity coherence on `EnvWf.indMember`
(F-04 / W3); this file cannot see `EnvWf`. -/
def applyTel_recPrefix_idx_last {E : ResolvedEnv} (w : IotaWitness E)
    (hnU : w.famMember.arity ≤ w.ls.length)
    (idx : List (Expr Nat))
    (hidxlen : idx.length = w.nindices) :
    Σ' (B : Expr Nat),
      applyTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
        (instantiateLevels w.ls w.recMember.mtype) =
        some (Expr.pi
          (foldApps (.const w.familyRef (w.ls.take w.famMember.arity))
            (w.preMajor.take w.nparams ++ idx))
          B) := by
  have hpreLen :
      (recPrefix w.preMajor w.nparams w.nMinors).length =
        w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre
    omega
  have hargs :
      (recPrefix w.preMajor w.nparams w.nMinors ++ idx).length =
        w.nparams + 1 + w.nMinors + w.nindices := by
    simp only [List.length_append, hpreLen, hidxlen]
  have hpeel := peelPis_instantiateLevels w.ls _ _ w.hpeelRec
  have hlen1 : (recPrefix w.preMajor w.nparams w.nMinors ++ idx).length + 1 =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by omega
  rw [← hlen1] at hpeel
  have hmaj : w.recDoms[w.nparams + 1 + w.nMinors + w.nindices]? =
      some (majorTyExpr w.familyRef
        ((List.range w.famMember.arity).map Level.param)
        w.nparams w.nMinors w.nindices) := by
    simpa only [majorTyExpr] using w.hmajorTy
  have hD :
      (w.recDoms.map (instantiateLevels w.ls))[
        (recPrefix w.preMajor w.nparams w.nMinors ++ idx).length]? =
        some (majorTyExpr w.familyRef (w.ls.take w.famMember.arity)
          w.nparams w.nMinors w.nindices) := by
    rw [hargs, List.getElem?_map, hmaj, Option.map_some',
      instantiateLevels_majorTyExpr,
      map_instLevel_canonical w.famMember.arity w.ls hnU]
  have ⟨B, happ⟩ :=
    applyTel_last_dom (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
      (instantiateLevels w.ls w.recMember.mtype) hpeel hD
  have hp :
      (recPrefix w.preMajor w.nparams w.nMinors ++ idx).take w.nparams =
        w.preMajor.take w.nparams := by
    simp only [recPrefix]
    have hle : w.nparams ≤
        (w.preMajor.take (w.nparams + 1 + w.nMinors)).length := by
      simp only [List.length_take]
      have := w.hpre
      omega
    have htk := List.take_append_of_le_length
      (l₁ := w.preMajor.take (w.nparams + 1 + w.nMinors))
      (l₂ := idx) hle
    have htk2 := List.take_take w.nparams (w.nparams + 1 + w.nMinors)
      w.preMajor
    have hmin : min w.nparams (w.nparams + 1 + w.nMinors) = w.nparams := by
      omega
    rw [htk, htk2, hmin]
  have hid :
      (recPrefix w.preMajor w.nparams w.nMinors ++ idx).drop
        (w.nparams + 1 + w.nMinors) = idx := by
    simp only [recPrefix]
    have heq : (w.preMajor.take (w.nparams + 1 + w.nMinors)).length =
        w.nparams + 1 + w.nMinors := by
      simp only [List.length_take]
      have := w.hpre
      omega
    have h :=
      List.drop_left (w.preMajor.take (w.nparams + 1 + w.nMinors)) idx
    rw [heq] at h
    exact h
  have hinst := instPrefix_majorTy
    (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
    w.familyRef (w.ls.take w.famMember.arity)
    w.nparams w.nMinors w.nindices hargs hp hid hidxlen
  rw [hinst] at happ
  exact ⟨B, happ⟩

/-- 00 §20.6: the recursor BODY is level-inert. `hrecBody` pins it to a
`foldApps` of bound variables only, and `instantiateLevels` is the
identity on `bvar`, so every recursor-side view of `recBody` is the
stored one. This is what lets the instantiated `recLastPi`/`recLastPi_idx`
siblings below keep `instTel _ w.recBody` on the nose rather than
carrying an `instantiateLevels` around the leftover Π-body. -/
theorem instantiateLevels_recBody {E : ResolvedEnv} (w : IotaWitness E)
    (lvls : List Level) : instantiateLevels lvls w.recBody = w.recBody := by
  rw [w.hrecBody, foldApps_instantiateLevels, List.map_append]
  have h1 :
      ((List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1))).map
          (instantiateLevels lvls) =
        (List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) :=
    map_instantiateLevels_bvars lvls (fun i => i + 1)
      (List.range w.nindices).reverse
  rw [h1]
  rfl

/-- 00 §20.6 recursor-side view (1) of `recLastPi`: the same last Π, read
through `instantiateLevels lvls`. Raw is the instance `lvls = []`
(`instantiateLevels_nil`). Proof is `recLastPi`'s verbatim, with
`peelPis_instantiateLevels` in front of `hpeelRec` and
`instantiateLevels_recBody` collapsing the body. -/
def recLastPi_inst {E : ResolvedEnv} (w : IotaWitness E) (lvls : List Level) :
    Σ' (A : Expr Nat),
      applyTel w.preMajor (instantiateLevels lvls w.recMember.mtype) =
        some (Expr.pi A (instTel w.preMajor w.recBody)) := by
  have hlen : w.preMajor.length + 1 =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have := w.hpre
    omega
  have hpeel := peelPis_instantiateLevels lvls _ _ w.hpeelRec
  rw [← hlen] at hpeel
  have ⟨A, happ⟩ :=
    lastPi_after_args w.preMajor (instantiateLevels lvls w.recMember.mtype) hpeel
  rw [instantiateLevels_recBody w lvls] at happ
  exact ⟨A, happ⟩

/-- 00 §20.6 recursor-side view (1) of `applyTel_recPrefix`. -/
def applyTel_recPrefix_inst {E : ResolvedEnv} (w : IotaWitness E)
    (lvls : List Level) :
    Σ' (U : Expr Nat),
      applyTel (recPrefix w.preMajor w.nparams w.nMinors)
        (instantiateLevels lvls w.recMember.mtype) = some U := by
  have ⟨_, happ⟩ := recLastPi_inst w lvls
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at happ
  have ⟨U, hpre, _⟩ := applyTel_append_split
    (recPrefix w.preMajor w.nparams w.nMinors)
    (w.preMajor.drop (w.nparams + 1 + w.nMinors)) happ
  exact ⟨U, hpre⟩

/-- Syntactic last Π of a recursor after applying `preMajor`:
`Π _ (instTel preMajor recBody)`. -/
def recLastPi {E : ResolvedEnv} (w : IotaWitness E) :
    Σ' (A : Expr Nat),
      applyTel w.preMajor w.recMember.mtype =
        some (Expr.pi A (instTel w.preMajor w.recBody)) := by
  have hlen : w.preMajor.length + 1 =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have := w.hpre
    omega
  have hpeel := w.hpeelRec
  rw [← hlen] at hpeel
  exact lastPi_after_args w.preMajor w.recMember.mtype hpeel

/-- 00 §20.6 recursor-side view (1) of `recLastPi_idx`. -/
def recLastPi_idx_inst {E : ResolvedEnv} (w : IotaWitness E)
    (lvls : List Level)
    (idx : List (Expr Nat)) (hidxlen : idx.length = w.nindices) :
    Σ' (A : Expr Nat),
      applyTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
        (instantiateLevels lvls w.recMember.mtype) =
        some (Expr.pi A
          (instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
            w.recBody)) := by
  have hprelen :
      (recPrefix w.preMajor w.nparams w.nMinors).length =
        w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre
    omega
  have hlen :
      (recPrefix w.preMajor w.nparams w.nMinors ++ idx).length + 1 =
        w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    simp only [List.length_append]
    omega
  have hpeel := peelPis_instantiateLevels lvls _ _ w.hpeelRec
  rw [← hlen] at hpeel
  have ⟨A, happ⟩ := lastPi_after_args
    (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
    (instantiateLevels lvls w.recMember.mtype) hpeel
  rw [instantiateLevels_recBody w lvls] at happ
  exact ⟨A, happ⟩

/-- Last Π after `recPrefix ++ idx`: domain is identified by
`applyTel_recPrefix_idx_last`; body is `instTel` of `recBody`. -/
def recLastPi_idx {E : ResolvedEnv} (w : IotaWitness E)
    (idx : List (Expr Nat)) (hidxlen : idx.length = w.nindices) :
    Σ' (A : Expr Nat),
      applyTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
        w.recMember.mtype =
        some (Expr.pi A
          (instTel (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
            w.recBody)) := by
  have hprelen :
      (recPrefix w.preMajor w.nparams w.nMinors).length =
        w.nparams + 1 + w.nMinors := by
    simp only [recPrefix, List.length_take]
    have := w.hpre
    omega
  have hlen :
      (recPrefix w.preMajor w.nparams w.nMinors ++ idx).length + 1 =
        w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    simp only [List.length_append]
    omega
  have hpeel := w.hpeelRec
  rw [← hlen] at hpeel
  exact lastPi_after_args
    (recPrefix w.preMajor w.nparams w.nMinors ++ idx)
    w.recMember.mtype hpeel

def applyTel_recPrefix {E : ResolvedEnv} (w : IotaWitness E) :
    Σ' (U : Expr Nat),
      applyTel (recPrefix w.preMajor w.nparams w.nMinors)
        w.recMember.mtype = some U := by
  have ⟨_, happ⟩ := recLastPi w
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at happ
  have ⟨U, hpre, _⟩ := applyTel_append_split
    (recPrefix w.preMajor w.nparams w.nMinors)
    (w.preMajor.drop (w.nparams + 1 + w.nMinors)) happ
  exact ⟨U, hpre⟩

theorem recPrefix_length {E : ResolvedEnv} (w : IotaWitness E) :
    (recPrefix w.preMajor w.nparams w.nMinors).length =
      w.nparams + 1 + w.nMinors := by
  simp only [recPrefix, List.length_take]
  have := w.hpre
  omega

def isPiTel_recPrefix_rem {E : ResolvedEnv} (w : IotaWitness E)
    {U : Expr Nat}
    (happ : applyTel (recPrefix w.preMajor w.nparams w.nMinors)
      w.recMember.mtype = some U) :
    isPiTel (w.nindices + 1) U = true := by
  have hlen := recPrefix_length w
  have hpeel := w.hpeelRec
  have hsum : w.nparams + 1 + w.nMinors + w.nindices + 1 =
      (w.nparams + 1 + w.nMinors) + (w.nindices + 1) := by omega
  rw [hsum] at hpeel
  have ⟨_, _, hrem⟩ :=
    peelPis_after_applyTel (w.nparams + 1 + w.nMinors) (w.nindices + 1)
      (recPrefix w.preMajor w.nparams w.nMinors) w.recMember.mtype
      hlen hpeel happ
  exact peelPis_isPiTel (w.nindices + 1) U hrem

/-- 00 §20.6 recursor-side view (1) of `isPiTel_recPrefix_rem`. -/
theorem isPiTel_recPrefix_rem_inst {E : ResolvedEnv} (w : IotaWitness E)
    (lvls : List Level) {U : Expr Nat}
    (happ : applyTel (recPrefix w.preMajor w.nparams w.nMinors)
      (instantiateLevels lvls w.recMember.mtype) = some U) :
    isPiTel (w.nindices + 1) U = true := by
  have hlen := recPrefix_length w
  have hpeel := peelPis_instantiateLevels lvls _ _ w.hpeelRec
  have hsum : w.nparams + 1 + w.nMinors + w.nindices + 1 =
      (w.nparams + 1 + w.nMinors) + (w.nindices + 1) := by omega
  rw [hsum] at hpeel
  have ⟨_, _, hrem⟩ :=
    peelPis_after_applyTel (w.nparams + 1 + w.nMinors) (w.nindices + 1)
      (recPrefix w.preMajor w.nparams w.nMinors)
      (instantiateLevels lvls w.recMember.mtype)
      hlen hpeel happ
  exact peelPis_isPiTel (w.nindices + 1) U hrem

theorem iotaRhs_nil_fields {E : ResolvedEnv} (w : IotaWitness E)
    (hf : w.fields = []) : iotaRhsOf w = w.minor := by
  have hk : w.kinds = [] := by
    have hlen := w.hlen
    rw [hf] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  unfold iotaRhsOf
  rw [hf, hk]
  rfl

/-- 05 §12: iota rhs is a function of lhs (and E). Unblocks F-05b diamond. -/
theorem iotaDet {E : ResolvedEnv} {lhs rhs rhs' : Expr Nat}
    (h1 : DerivedIota E lhs rhs) (h2 : DerivedIota E lhs rhs') :
    rhs = rhs' := by
  let ⟨w1, hl1, hr1⟩ := derivedIota_unpack h1
  let ⟨w2, hl2, hr2⟩ := derivedIota_unpack h2
  subst hr1
  subst hr2
  have hL : iotaLhsOf w1 = iotaLhsOf w2 := hl1.symm.trans hl2
  unfold iotaLhsOf recCall at hL
  have s1 := appsSpine_foldApps (.const w1.recRef w1.ls)
    (w1.preMajor ++ [ctorMajor w1])
  have s2 := appsSpine_foldApps (.const w2.recRef w2.ls)
    (w2.preMajor ++ [ctorMajor w2])
  simp only [appsSpine_const, List.nil_append] at s1 s2
  have hs : appsSpine (foldApps (.const w1.recRef w1.ls)
      (w1.preMajor ++ [ctorMajor w1])) =
      appsSpine (foldApps (.const w2.recRef w2.ls)
        (w2.preMajor ++ [ctorMajor w2])) := congrArg appsSpine hL
  rw [s1, s2] at hs
  injection hs with hhead hargs
  injection hhead with hrec hls
  have ⟨hpre, hmaj⟩ := list_snoc_inj hargs
  have sc1 := appsSpine_foldApps (.const w1.ctorRef w1.lsC)
    (w1.ctorParams ++ w1.fields)
  have sc2 := appsSpine_foldApps (.const w2.ctorRef w2.lsC)
    (w2.ctorParams ++ w2.fields)
  simp only [appsSpine_const, List.nil_append] at sc1 sc2
  have hmajS : appsSpine (ctorMajor w1) = appsSpine (ctorMajor w2) :=
    congrArg appsSpine hmaj
  unfold ctorMajor ctorSpine at hmajS
  rw [sc1, sc2] at hmajS
  injection hmajS with hchead hctorArgs
  injection hchead with hctor hlsC
  have hmemr : w1.recMember = w2.recMember := by
    have a := w1.hrec
    have b := w2.hrec
    rw [← hrec] at b
    have eq : some w1.recMember = some w2.recMember := a.symm.trans b
    injection eq
  have hmemc : w1.ctorMember = w2.ctorMember := by
    have a := w1.hctor
    have b := w2.hctor
    rw [← hctor] at b
    have eq : some w1.ctorMember = some w2.ctorMember := a.symm.trans b
    injection eq
  have hpeelEq : w1.ctorDoms = w2.ctorDoms ∧ w1.ctorResult = w2.ctorResult := by
    have a := w1.hpeel
    have b := w2.hpeel
    rw [w1.hnpar] at a
    rw [w2.hnpar, ← hmemc] at b
    have eq : some (w1.ctorDoms, w1.ctorResult) = some (w2.ctorDoms, w2.ctorResult) :=
      a.symm.trans b
    injection eq with hp
    injection hp with h1 h2
    exact ⟨h1, h2⟩
  have hf1 := w1.hfamApp
  have hf2 := w2.hfamApp
  rw [← hpeelEq.2] at hf2
  unfold isFamilyApp at hf1 hf2
  split at hf1
  · rename_i r ls' args heq
    have hr1 : r = w1.familyRef := by
      cases hdec : decide (r = w1.familyRef) with
      | true => exact of_decide_eq_true hdec
      | false =>
          simp only [hdec, Bool.false_and] at hf1
          exact Bool.noConfusion hf1
    have hf2' : (decide (r = w2.familyRef) &&
        args.all (fun a => !occursConst w2.familyRef a)) = true := by
      rw [heq] at hf2
      exact hf2
    have hr2 : r = w2.familyRef := by
      cases hdec : decide (r = w2.familyRef) with
      | true => exact of_decide_eq_true hdec
      | false =>
          simp only [hdec, Bool.false_and] at hf2'
          exact Bool.noConfusion hf2'
    have hfam : w1.familyRef = w2.familyRef := hr1.symm.trans hr2
    have hmemf : w1.famMember = w2.famMember := by
      have a := w1.hfam
      have b := w2.hfam
      rw [← hfam] at b
      have eq : some w1.famMember = some w2.famMember := a.symm.trans b
      injection eq
    have hnmin : w1.nMinors = w2.nMinors := by
      have a := w1.hrecIdx
      have b := w2.hrecIdx
      rw [← hrec, ← hfam] at b
      have := a.symm.trans b
      omega
    have hrecBodyEq : w1.recBody = w2.recBody := by
      have a := w1.hpeelRec
      have b := w2.hpeelRec
      have L1 : w1.nparams + 1 + w1.nMinors + w1.nindices + 1 =
          w1.preMajor.length + 1 := by
        have := w1.hpre; omega
      have L2 : w2.nparams + 1 + w2.nMinors + w2.nindices + 1 =
          w2.preMajor.length + 1 := by
        have := w2.hpre; omega
      rw [L1] at a
      rw [L2, ← hpre, ← hmemr] at b
      have eq : some (w1.recDoms, w1.recBody) = some (w2.recDoms, w2.recBody) :=
        a.symm.trans b
      injection eq with hp
      exact (Prod.mk.inj hp).2
    have hnidx : w1.nindices = w2.nindices := by
      have eq := w1.hrecBody.symm.trans (hrecBodyEq.trans w2.hrecBody)
      have s1 := appsSpine_foldApps
        (.bvar (w1.nMinors + w1.nindices + 1) : Expr Nat)
        ((List.range w1.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
          [Expr.bvar 0])
      have s2 := appsSpine_foldApps
        (.bvar (w2.nMinors + w2.nindices + 1) : Expr Nat)
        ((List.range w2.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
          [Expr.bvar 0])
      simp only [appsSpine_bvar, List.nil_append] at s1 s2
      have hs := congrArg appsSpine eq
      rw [s1, s2] at hs
      injection hs with hhead _
      injection hhead with hidx
      omega
    have hnpar : w1.nparams = w2.nparams := by
      have := w1.hpre
      have := w2.hpre
      have := congrArg List.length hpre
      omega
    have hfields : w1.fields = w2.fields := by
      have hlen : w1.ctorParams.length = w2.ctorParams.length := by
        rw [w1.hctorParams, w2.hctorParams, hnpar]
      have ⟨_, hf⟩ := List.append_inj hctorArgs hlen
      exact hf
    have hidx : w1.ctorIdx = w2.ctorIdx := by
      have a := w1.hctorIdx
      have b := w2.hctorIdx
      rw [← hctor, ← hfam] at b
      have := a.symm.trans b
      omega
    have hmin : w1.minor = w2.minor := by
      have a := w1.hminor
      have b := w2.hminor
      rw [← hpre, ← hnpar, ← hidx] at b
      have eq : some w1.minor = some w2.minor := a.symm.trans b
      injection eq
    have hk : w1.kinds = w2.kinds := by
      have a := w1.hkinds
      have b := w2.hkinds
      rw [← hfam, ← hpeelEq.1, ← hnpar] at b
      have eq : some w1.kinds = some w2.kinds := a.symm.trans b
      injection eq
    have hcap : w1.ctorAfterParams = w2.ctorAfterParams := by
      have a := w1.hctorAfter
      have b := w2.hctorAfter
      rw [hpre, hnpar, hmemc, hls] at a
      have eq : some w1.ctorAfterParams = some w2.ctorAfterParams :=
        a.symm.trans b
      injection eq
    unfold iotaRhsOf
    rw [hrec, hls, hpre, hfields, hmin, hk, hnpar, hnmin, hcap]
  · exact Bool.noConfusion hf1

/-- Witness-level determinism: same lhs, two `IotaWitness`es, same rhs.
Spine fixes recRef/ls/preMajor/ctorMajor; lookup fixes member/minor.
Wrapper around sealed `iotaDet`. Iota-vs-iota is then refl on the rhs
plus recursion on the two `hr : ParRed (iotaRhsOf w) _`. -/
theorem iotaWitness_deterministic {E : ResolvedEnv}
    {w1 w2 : IotaWitness E}
    (h : iotaLhsOf w1 = iotaLhsOf w2) :
    iotaRhsOf w1 = iotaRhsOf w2 := by
  have d2 : DerivedIota E (iotaLhsOf w1) (iotaRhsOf w2) := by
    rw [h]
    exact .of w2
  exact iotaDet (.of w1) d2

/-- Identity spine `[bvar (n-1), ..., bvar 0]`. Declared-type
index-position walks run on this spine; lhs args are instances. -/
def bvarSpine (n : Nat) : List (Expr Nat) :=
  (List.range n).reverse.map Expr.bvar

theorem bvarSpine_length (n : Nat) : (bvarSpine n).length = n := by
  simp only [bvarSpine, List.length_map, List.length_reverse, List.length_range]

-- DELETED (00 §20.7 D1, batch B5): `ctorIdxPosBuild`, the declared-type
-- `recIdxPosBuild` on the CONSTRUCTOR identity spine `bvarSpine
-- (nparams + nfields)`. That base carries NO motive slot and NO minor
-- slots, so `recPrefix` — which `IotaTyping.hminDom` and `hidxTy` read —
-- cannot be expressed on it at all, which is why the admission plan's
-- first draft rated `hidxTy` "hardest; NOT today". 00 §20.7 RE-BASES the
-- identity spine to the FULL recursor prefix `bvarSpine (nparams + 1 +
-- nMinors + nfields)`, on which the two prefixes are SUBLISTS OF ONE
-- LIST, and `declaredIdxPositions` (`RcicAdmit.lean`) is the supplier
-- that replaces this one. Measured at the deletion: ZERO Lean call
-- sites. Deleted rather than left beside its successor, because a second
-- declared-position builder on a different base is exactly the "two
-- implementations of one belief" a reader would have to adjudicate.

/-- 05 recursor-group admission, recorded on the *prefix* env at
recursor-add (ctors already present; recRef still fresh). `typing` is
the readout: declared positions transported to any instance witness
in an extension that contains this recursor. Kernel iota never
recomputes `listIndexOf` on lhs args.

THE INTENDED CONSTRUCTOR IS `RecursorGroupIdxAdmitted.ofAdmitted`
(`RcicAdmit.lean`, 00 §20.7 batch B5): it derives `typing` from the
declaration-level `Bool` equation `recursorGroupAdmitted E r m = true`,
decided at recursor-add from `(E, r, m)` and nothing else, through
`iotaTyping_of_admitted`. The five carriers of `RcicFixtures.lean` are
built that way, by `.ofAdmitted rfl`, and `EnvWf` is thereby inhabited
over an INDEXED family (`vecEnv`) and over a UNIVERSE-POLYMORPHIC one
(`listUEnv`), which is what ends the vacuity recorded below.

THE BOOL IS SUFFICIENT, NOT REQUIRED (00 §20.7 D13). This structure is
NOT restated to carry the Bool: `typing` remains its only field, so a
hand-rolled `typing` still discharges `EnvWf.indMember`'s `hidxAdm`,
and a recursor the Bool refuses may still enter an `EnvWf` by any other
inhabitant. "Checks at recursor-add, exactly as a kernel does" is a
statement about `recursorGroupAdmitted`, not about this judgment; and
the DT-018 footprint records a change in how `hidxAdm` CAN BE SUPPLIED,
not in what it MEANS.

00 §19.2 erratum 5 removed the two facts that made this bundle
REFUTED for indexed families: `IotaTyping.hminApply` mentioned
`preMajor.drop (nparams + 1 + nMinors)`, which no `IotaWitness` field
constrains, so a junk-index record-update of a legal witness falsified
it while leaving both sides of the iota rule fixed (RULE ∀-BUNDLE).
Its content is now `hminTel` (bridged by `applyTel_rhsArgs_minorTel`)
plus the index agreement at the ACTUAL fields, which is a fact about
the redex's TYPING and not a bundle field (00 §19.2 erratum 6:
`IndexCoherentConv`, `RcicInvertFamily`; discharged downstream by
`iotaLhs_ctorIdx_conv`, `RcicDTMeta`). Removing a refutation was NOT
producing an inhabitant, and between erratum 5 and 00 §20.7 batch B5
`typing` WAS uninhabited here, so `EnvWf`-conditioned theorems WERE
vacuous over indexed families — a state of the tree that ended when the
declaration-level bundle (`recursorGroupAdmitted` /
`iotaTyping_of_admitted`, over the two-stage declared→instance walk
transport) landed. -/
structure RecursorGroupIdxAdmitted (E : ResolvedEnv) (recRef : Nat)
    (m : CheckedMember) : Type where
  typing : ∀ {E' : ResolvedEnv}
    (_hext : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (_hrec : E'.members recRef = some m)
    (w : IotaWitness E'),
    w.recRef = recRef →
    w.recMember = m →
    IotaTyping E' w

end Rcic.Declarative

