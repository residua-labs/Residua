import rcic.RcicConvPlus

/-!
# Syntactic sortRow, build step 3k — replacing one assumption

`research/rcic/semantic/S3_ES_ARMS.md` §12. `piInv`'s codomain sits one binder
deeper than `TyP.cctx`. The missing transport is `setAssump k Dom'`: the
context with the assumption at position `k` replaced, term and ascribed type
unchanged.

This module is the context arithmetic and the one arm that does not rebuild:
a `bvar` whose index is `k`. Its new lookup is `lift 0 (k + 1) Dom'`; the old
ascribed type is `lift 0 (k + 1) Dom`. The derivation is a `bvar` node at the
new lookup, then `conv` along the domain conversion weakened across the
`k + 1` newer entries (`CvP.symm`, then `wk` at cutoff 0). `closure_claim`
stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Replace the assumption at position `k`. A short context is left unchanged.
    The list is matched first, so `setAssump k A []` reduces while `k` is a variable. -/
def setAssump (k : Nat) (A : Expr Nat) : LCtx → LCtx
  | [] => []
  | d :: Γ =>
    match k with
    | 0 => .assumption A :: Γ
    | k + 1 => d :: setAssump k A Γ

theorem setAssump_zero (A : Expr Nat) (d : LocalDecl) (Γ : LCtx) :
    setAssump 0 A (d :: Γ) = .assumption A :: Γ := rfl

theorem setAssump_succ (k : Nat) (A : Expr Nat) (d : LocalDecl) (Γ : LCtx) :
    setAssump (k + 1) A (d :: Γ) = d :: setAssump k A Γ := rfl

theorem setAssump_nil (k : Nat) (A : Expr Nat) : setAssump k A [] = [] := by
  cases k <;> rfl

theorem length_setAssump (Dom' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → (setAssump k Dom' Γ).length = Γ.length
  | [], k => by rw [setAssump_nil]
  | _ :: Γ, 0 => by rw [setAssump_zero]; rfl
  | _ :: Γ, k + 1 => by
      rw [setAssump_succ, List.length_cons, List.length_cons]
      exact congrArg Nat.succ (length_setAssump Dom' Γ k)

theorem drop_setAssump (Dom' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → (setAssump k Dom' Γ).drop (k + 1) = Γ.drop (k + 1)
  | [], k => by rw [setAssump_nil]
  | _ :: Γ, 0 => by rw [setAssump_zero, List.drop_one]; rfl
  | _ :: Γ, k + 1 => by
      rw [setAssump_succ, List.drop_succ_cons, List.drop_succ_cons]
      exact drop_setAssump Dom' Γ k

/-- An index other than `k` reads the same declaration. -/
theorem get?_setAssump_ne (Dom' : Expr Nat) :
    (Γ : LCtx) → (k i : Nat) → i ≠ k → (setAssump k Dom' Γ).get? i = Γ.get? i
  | [], _, i, _ => by rw [setAssump_nil]
  | _ :: _, 0, 0, hne => absurd rfl hne
  | _ :: Γ, 0, i + 1, _ => by
      rw [setAssump_zero, List.get?_cons_succ, List.get?_cons_succ]
  | _ :: _, k + 1, 0, _ => by
      rw [setAssump_succ, List.get?_cons_zero, List.get?_cons_zero]
  | _ :: Γ, k + 1, i + 1, hne => by
      rw [setAssump_succ, List.get?_cons_succ, List.get?_cons_succ]
      exact get?_setAssump_ne Dom' Γ k i (fun h => hne (congrArg Nat.succ h))

theorem lt_length_of_get? {d : LocalDecl} :
    (Γ : LCtx) → (k : Nat) → Γ.get? k = some d → k < Γ.length
  | [], k, h => by rw [List.get?_nil] at h; cases h
  | _ :: _, 0, _ => Nat.zero_lt_succ _
  | _ :: Γ, k + 1, h => by
      rw [List.get?_cons_succ] at h
      exact Nat.succ_lt_succ (lt_length_of_get? Γ k h)

theorem lookupType_setAssump_ne {k i : Nat} {A Dom' : Expr Nat} {Γ : LCtx}
    (hne : i ≠ k) (h : lookupType Γ i = some A) :
    lookupType (setAssump k Dom' Γ) i = some A := by
  unfold lookupType at h ⊢
  rw [get?_setAssump_ne Dom' Γ k i hne]
  exact h

theorem lookupType_of_assumption {Γ : LCtx} {k : Nat} {Dom A : Expr Nat}
    (hget : Γ.get? k = some (.assumption Dom)) (hl : lookupType Γ k = some A) :
    A = lift 0 (k + 1) Dom := by
  have hlu : lookupType Γ k = some (lift 0 (k + 1) Dom) := by
    unfold lookupType
    rw [hget]
  exact Option.some.inj (hl.symm.trans hlu)

theorem lookupType_of_letBinding {Γ : LCtx} {k : Nat} {Dom w A : Expr Nat}
    (hget : Γ.get? k = some (.letBinding Dom w)) (hl : lookupType Γ k = some A) :
    A = lift 0 (k + 1) Dom := by
  have hlu : lookupType Γ k = some (lift 0 (k + 1) Dom) := by
    unfold lookupType
    rw [hget]
  exact Option.some.inj (hl.symm.trans hlu)

/-- The replaced slot's lookup is the new stored type, lifted by `k + 1`. -/
theorem lookupType_setAssump_hit (Dom' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → {Dom : Expr Nat} → Γ.get? k = some (.assumption Dom) →
      lookupType (setAssump k Dom' Γ) k = some (lift 0 (k + 1) Dom')
  | _ :: _, 0, _, _ => by
      rw [setAssump_zero, lookupType, List.get?_cons_zero]
  | d :: Γ, k + 1, Dom, h => by
      rw [List.get?_cons_succ] at h
      rw [setAssump_succ, lookupType_cons_succ,
        lookupType_setAssump_hit Dom' Γ k h, Option.map_some']
      exact congrArg some (lift_lift_merge 1 (k + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Dom')
  | [], _, _, h => by rw [List.get?_nil] at h; cases h

/-- `c < k`: the insertion is newer than the target, so the target's index
    shifts by one and `setAssump` commutes with `insertAt`. -/
theorem setAssump_insertAt_gt (d : LocalDecl) (Dom' : Expr Nat) :
    (c k : Nat) → (Γ : LCtx) → c < k →
      setAssump k Dom' (insertAt d c Γ) = insertAt d c (setAssump (k - 1) Dom' Γ)
  | 0, 0, _, hck => absurd hck (Nat.lt_irrefl 0)
  | 0, k + 1, Γ, _ => by
      simp only [insertAt_zero, setAssump_succ, Nat.add_sub_cancel]
  | c + 1, 0, _, hck => absurd hck (Nat.not_lt_zero (c + 1))
  | c + 1, k + 1, [], _ => by
      have hL : setAssump (k + 1) Dom' (insertAt d (c + 1) []) = [d] := by
        rw [show insertAt d (c + 1) ([] : LCtx) = [d] from rfl, setAssump_succ, setAssump_nil]
      have hR : insertAt d (c + 1) (setAssump k Dom' []) = [d] := by
        rw [setAssump_nil, show insertAt d (c + 1) ([] : LCtx) = [d] from rfl]
      exact hL.trans hR.symm
  | c + 1, k + 1, x :: Γ, hck => by
      have hk : c < k := Nat.lt_of_succ_lt_succ hck
      have hkpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le c) hk
      have hR : insertAt d (c + 1) (setAssump k Dom' (x :: Γ)) =
          liftDecl c x :: insertAt d c (setAssump (k - 1) Dom' Γ) := by
        have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)).symm
        rw [hk1, setAssump_succ, insertAt_succ_cons, Nat.add_sub_cancel]
      rw [show (k + 1) - 1 = k from Nat.add_sub_cancel k 1]
      rw [insertAt_succ_cons, setAssump_succ, setAssump_insertAt_gt d Dom' c k Γ hk, hR]

/-- `c = k` and the context is long enough for the insertion to land at `c`:
    replacing that slot is `insertAt` of the new assumption. -/
theorem setAssump_insertAt_eq (Dom' : Expr Nat) (d : LocalDecl) :
    (c : Nat) → (Γ : LCtx) → c ≤ Γ.length →
      setAssump c Dom' (insertAt d c Γ) = insertAt (.assumption Dom') c Γ
  | 0, Γ, _ => by simp only [insertAt_zero, setAssump_zero]
  | c + 1, [], hle => absurd hle (Nat.not_succ_le_zero c)
  | c + 1, x :: Γ, hle => by
      simp only [insertAt_succ_cons, setAssump_succ, List.length_cons] at *
      exact congrArg (liftDecl c x :: ·) (setAssump_insertAt_eq Dom' d c Γ (Nat.le_of_succ_le_succ hle))

/-! ## Weakening across a prefix, as one lift -/

def tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e e' T T' : Expr Nat}
    (he : e = e') (hT : T = T') (D : TyP E n Γ e T) : TyP E n Γ e' T' :=
  he ▸ hT ▸ D

def tyCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {e T : Expr Nat}
    (hΓ : Γ = Γ') (D : TyP E n Γ e T) : TyP E n Γ' e T :=
  hΓ ▸ D

def cvCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a a' b b' T T' : Expr Nat}
    (ha : a = a') (hb : b = b') (hT : T = T') (h : CvP E n Γ a b T) :
    CvP E n Γ a' b' T' :=
  ha ▸ hb ▸ hT ▸ h

def cvCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {a b T : Expr Nat}
    (hΓ : Γ = Γ') (h : CvP E n Γ a b T) : CvP E n Γ' a b T :=
  hΓ ▸ h

/-- Insert `ds` (newest first) at cutoff 0. Each step is `TyP.wk`; the nested
    lifts merge by `lift_lift_merge`. -/
def wkFront {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
    (ds : List LocalDecl) → TyP E n Γ e T →
      TyP E n (ds ++ Γ) (lift 0 ds.length e) (lift 0 ds.length T)
  | [], D => by
      rw [List.length_nil, List.nil_append, lift_zero, lift_zero]
      exact D
  | d :: ds, D =>
      let D1 := wkFront ds D
      let D2 := TyP.wk E n (ds ++ Γ) (lift 0 ds.length e) (lift 0 ds.length T) d 0 D1
      tyCast
        (lift_lift_merge 1 ds.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) e)
        (lift_lift_merge 1 ds.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) T)
        D2

def cvFront {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    (ds : List LocalDecl) → CvP E n Γ a b T →
      CvP E n (ds ++ Γ) (lift 0 ds.length a) (lift 0 ds.length b) (lift 0 ds.length T)
  | [], h => by
      rw [List.length_nil, List.nil_append, lift_zero, lift_zero, lift_zero]
      exact h
  | d :: ds, h =>
      let h1 := cvFront ds h
      let h2 := CvP.wk E n (ds ++ Γ) (lift 0 ds.length a) (lift 0 ds.length b)
        (lift 0 ds.length T) d 0 h1
      cvCast
        (lift_lift_merge 1 ds.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) a)
        (lift_lift_merge 1 ds.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) b)
        (lift_lift_merge 1 ds.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) T)
        h2

/-- A variable at the replaced slot, retyped at its old lookup.
    The new node types it at `lift 0 (k + 1) Dom'`; `conv` along the weakened
    `symm` sends that to `lift 0 (k + 1) Dom`. -/
def retypeBvarSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Dom' : Expr Nat} {u : Level}
    (h : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u))
    (hget : Γ.get? k = some (.assumption Dom)) :
    TyP E n (setAssump k Dom' Γ) (.bvar k) (lift 0 (k + 1) Dom) := by
  let Γ' := setAssump k Dom' Γ
  let pref := Γ'.take (k + 1)
  have hdrop : Γ'.drop (k + 1) = Γ.drop (k + 1) := drop_setAssump Dom' Γ k
  have hlen : k < Γ.length := lt_length_of_get? Γ k hget
  have hlen' : k < Γ'.length := by rw [length_setAssump Dom' Γ k]; exact hlen
  have hpref : pref.length = k + 1 := by
    rw [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hlen')]
  have hctx : pref ++ Γ.drop (k + 1) = Γ' := by
    rw [← hdrop]
    exact List.take_append_drop (k + 1) Γ'
  let hTy' := wkFront pref h.dr
  let hTy := tyCastCtx hctx (hpref ▸ hTy')
  have hlook : lookupType Γ' k = some (lift 0 (k + 1) Dom') :=
    lookupType_setAssump_hit Dom' Γ k hget
  let hb := TyP.bvar E n Γ' k (lift 0 (k + 1) Dom') u hlook hTy
  let hsym := CvP.symm E n (Γ.drop (k + 1)) Dom Dom' (.sort u) h h.dr h.dl
  let hc0 := cvFront pref hsym
  let hc := cvCastCtx hctx (hpref ▸ hc0)
  exact TyP.conv E n Γ' (.bvar k) (lift 0 (k + 1) Dom') (lift 0 (k + 1) Dom) u hb hc

#print axioms setAssump_zero
#print axioms setAssump_succ
#print axioms setAssump_nil
#print axioms length_setAssump
#print axioms drop_setAssump
#print axioms get?_setAssump_ne
#print axioms lt_length_of_get?
#print axioms lookupType_setAssump_ne
#print axioms lookupType_of_assumption
#print axioms lookupType_setAssump_hit
#print axioms setAssump_insertAt_gt
#print axioms setAssump_insertAt_eq
#print axioms tyCast
#print axioms tyCastCtx
#print axioms cvCast
#print axioms cvCastCtx
#print axioms wkFront
#print axioms cvFront
#print axioms retypeBvarSlot

end Rcic.Syn
