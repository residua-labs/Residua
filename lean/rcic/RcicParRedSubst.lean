/-
RCIC ParRed, piece 5 of 7: term-only instantiate congruence (the
beta/zeta engine).

`assumpPad` / `instLCtx`, the mutual `parRed_instantiate_term`,
`parRed_instantiate_both` and `parRed_instantiate_let` families with
their bridge lemmas (`parRed_weaken_lctx`,
`parRed_instantiate_both0/_assump`, `parRed_instantiate_let0`,
`parRedStar_instantiate_zeta`), and `parRed_rhsArgs_congr` /
`parRed_iotaRhs_congr`.  This is what the pairwise diamond invokes
for its beta and zeta cases.  `parRedStar_instantiate_arg` is
lifted here from its original position inside the
complete-development narrative: it is the star closure of
`parRed_instantiate_arg` and is consumed by the instantiate
families below, which must not depend on `RcicParRedDevel`.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.
-/
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicParRedWeight

namespace Rcic.Declarative

def parRedStar_instantiate_arg {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {v v' : Expr Nat} :
    {c : Nat} → ParRedStar E n Γ v v' → (e : Expr Nat) →
    ParRedStar E n Γ (instantiate c v e) (instantiate c v' e)
  | c, .refl _ _, e => .refl _ _
  | c, .tail h hs, e =>
      .tail (parRed_instantiate_arg hE h (c := c) e)
        (parRedStar_instantiate_arg hE (c := c) hs e)

/-! ### Term-only instantiate congruence (beta/zeta engine).

`parRed_instantiate_arg` fixes the term and reduces the replacement.
This dual fixes the replacement and reduces the term, under a dummy
assumption at index `c + Δ.length` (pads in front of `base`, extra
binders in `Δ`). `lookupValue` of a pad is `none`, so zeta never
fires at the hole; binders in `Δ` (assumption or let) are themselves
instantiated (`instLCtx`). -/

def assumpPad : Nat → LCtx → LCtx
  | 0, Γ => Γ
  | n + 1, Γ => dummyAssump :: assumpPad n Γ

theorem assumpPad_zero (Γ : LCtx) : assumpPad 0 Γ = Γ := rfl

theorem assumpPad_succ (n : Nat) (Γ : LCtx) :
    assumpPad (n + 1) Γ = dummyAssump :: assumpPad n Γ := rfl

theorem assumpPad_length (k : Nat) (Γ : LCtx) :
    (assumpPad k Γ).length = k + Γ.length := by
  induction k generalizing Γ with
  | zero => simp only [assumpPad, Nat.zero_add]
  | succ k ih =>
      simp only [assumpPad, List.length_cons, ih, Nat.succ_add]

theorem lookupValue_assumpPad_lt (k : Nat) (Γ : LCtx) (i : Nat)
    (h : i < k) : lookupValue (assumpPad k Γ) i = none := by
  induction k generalizing i with
  | zero => exfalso; omega
  | succ k ih =>
      match i with
      | 0 =>
          simp only [assumpPad, dummyAssump, lookupValue, List.get?_cons_zero]
      | i' + 1 =>
          simp only [assumpPad, lookupValue_cons_succ]
          rw [ih i' (by omega)]
          rfl

theorem lift_zero_succ (n : Nat) (e : Expr Nat) :
    lift 0 1 (lift 0 n e) = lift 0 (n + 1) e :=
  lift_lift_merge 1 n 0 0 (Nat.le_refl 0) (Nat.zero_le n) e

theorem lift_zero_comp (n m : Nat) (e : Expr Nat) :
    lift 0 n (lift 0 m e) = lift 0 (n + m) e := by
  rw [lift_lift_merge n m 0 0 (Nat.zero_le 0) (by omega)]
  rw [Nat.add_comm m n]

theorem instantiate_of_lift_succ (k : Nat) (s v : Expr Nat) :
    instantiate (k + 1) (lift 0 1 s) (lift 0 1 v) =
      lift 0 1 (instantiate k s v) := by
  have h := lift_instantiate_high 1 0 k s (Nat.zero_le k) v
  simp only [Nat.zero_add] at h
  have hcomm : 1 + k = k + 1 := Nat.add_comm 1 k
  rw [hcomm] at h
  exact h.symm

theorem instantiate0_lam (s B b : Expr Nat) :
    instantiate0 s (.lam B b) =
      .lam (instantiate0 s B) (instantiate 1 (lift 0 1 s) b) := rfl

theorem instantiate0_pi (s B b : Expr Nat) :
    instantiate0 s (.pi B b) =
      .pi (instantiate0 s B) (instantiate 1 (lift 0 1 s) b) := rfl

theorem instantiate_one_bvar (s : Expr Nat) :
    instantiate 1 s (.bvar 1) = s := rfl

theorem instantiate_lift2_id (s v : Expr Nat) :
    instantiate 1 (lift 0 1 s) (lift 0 2 v) = lift 0 1 v := by
  have h2 : lift 0 2 v = lift 0 1 (lift 0 1 v) :=
    (lift_zero_succ 1 v).symm
  rw [h2, instantiate_of_lift_succ 0 s (lift 0 1 v),
    instantiate_lift_id 0 s v]

theorem lookupValue_assump_let_one (B A v : Expr Nat) (Γ : LCtx) :
    lookupValue (.assumption B :: .letBinding A v :: Γ) 1 =
      some (lift 0 2 v) := by
  simp only [lookupValue, List.get?_cons_succ, List.get?_cons_zero]

theorem lookupValue_assump_let_assump_ne (B A A' v : Expr Nat) (Γ : LCtx)
    {i : Nat} (h : i ≠ 1) :
    lookupValue (.assumption B :: .letBinding A v :: Γ) i =
      lookupValue (.assumption B :: .assumption A' :: Γ) i := by
  cases i with
  | zero =>
      simp only [lookupValue, List.get?_cons_zero]
  | succ i' =>
      have hi' : i' ≠ 0 := fun heq => h (congrArg Nat.succ heq)
      rw [lookupValue_cons_succ, lookupValue_cons_succ,
        lookupValue_let_assump_ne A A' v Γ hi']

theorem lookupValue_assump_assump_irrel (B A A' : Expr Nat) (Γ : LCtx)
    (i : Nat) :
    lookupValue (.assumption B :: .assumption A :: Γ) i =
      lookupValue (.assumption B :: .assumption A' :: Γ) i := by
  cases i with
  | zero =>
      simp only [lookupValue, List.get?_cons_zero]
  | succ i' =>
      rw [lookupValue_cons_succ, lookupValue_cons_succ,
        lookupValue_assumption_irrel A A' Γ i']

theorem lookupValue_assumpPad_ge (k : Nat) (Γ : LCtx) (i : Nat) :
    lookupValue (assumpPad k Γ) (k + i) =
      (lookupValue Γ i).map (lift 0 k) := by
  induction k with
  | zero =>
      simp only [assumpPad, Nat.zero_add]
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v =>
          simp only [Option.map_some']
          exact congrArg some (lift_zero 0 v).symm
  | succ k ih =>
      simp only [assumpPad, Nat.succ_add]
      rw [lookupValue_cons_succ, ih]
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v =>
          simp only [Option.map_some', lift_zero_succ]

theorem lookupValue_append_left (Δ Γ : LCtx) (i : Nat)
    (h : i < Δ.length) :
    lookupValue (Δ ++ Γ) i = lookupValue Δ i := by
  induction Δ generalizing i with
  | nil =>
      simp only [List.length_nil] at h; omega
  | cons x Δ ih =>
      match i with
      | 0 =>
          simp only [List.cons_append, lookupValue, List.get?_cons_zero]
      | i' + 1 =>
          have hi' : i' < Δ.length := by
            simp only [List.length_cons] at h; omega
          simp only [List.cons_append, lookupValue_cons_succ]
          rw [ih i' hi']

theorem lookupValue_append_right (Δ Γ : LCtx) (i : Nat) :
    lookupValue (Δ ++ Γ) (Δ.length + i) =
      (lookupValue Γ i).map (lift 0 Δ.length) := by
  induction Δ with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v =>
          simp only [Option.map_some']
          exact congrArg some (lift_zero 0 v).symm
  | cons x Δ ih =>
      simp only [List.cons_append, List.length_cons, Nat.succ_add]
      rw [lookupValue_cons_succ, ih]
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v =>
          simp only [Option.map_some', lift_zero_succ]

/-- Instantiate stored declarations of a newest-first prefix. The hole
sits at index `c + Δ.length` in `Δ ++ assumpPad (c+1) base`. -/
def instLCtx (c : Nat) (s : Expr Nat) : LCtx → LCtx
  | [] => []
  | .assumption A :: Δ =>
      .assumption (instantiate (c + Δ.length) (lift 0 Δ.length s) A) ::
        instLCtx c s Δ
  | .letBinding A w :: Δ =>
      .letBinding
        (instantiate (c + Δ.length) (lift 0 Δ.length s) A)
        (instantiate (c + Δ.length) (lift 0 Δ.length s) w) ::
        instLCtx c s Δ

theorem instLCtx_nil (c : Nat) (s : Expr Nat) : instLCtx c s [] = [] := rfl

theorem instLCtx_length (c : Nat) (s : Expr Nat) :
    (Δ : LCtx) → (instLCtx c s Δ).length = Δ.length
  | [] => rfl
  | .assumption _ :: Δ => by
      simp only [instLCtx, List.length_cons, instLCtx_length c s Δ]
  | .letBinding _ _ :: Δ => by
      simp only [instLCtx, List.length_cons, instLCtx_length c s Δ]

theorem lookupValue_dummy_slot (Δ : LCtx) (c : Nat) (base : LCtx) :
    lookupValue (Δ ++ assumpPad (c + 1) base) (c + Δ.length) = none := by
  have hidx : c + Δ.length = Δ.length + c := Nat.add_comm _ _
  rw [hidx, lookupValue_append_right]
  have hpad : lookupValue (assumpPad (c + 1) base) c = none :=
    lookupValue_assumpPad_lt (c + 1) base c (Nat.lt_succ_self c)
  simp only [hpad, Option.map_none']

theorem length_cons_add (x : LocalDecl) (Δ : LCtx) :
    (x :: Δ).length = Δ.length + 1 :=
  List.length_cons x Δ

theorem instantiate_binder_shift (c : Nat) (s : Expr Nat) (Δ : LCtx)
    (e : Expr Nat) (x : LocalDecl) :
    instantiate (c + (x :: Δ).length) (lift 0 (x :: Δ).length s) e =
      instantiate (c + Δ.length + 1) (lift 0 1 (lift 0 Δ.length s)) e := by
  have hidx : c + (Δ.length + 1) = c + Δ.length + 1 := by omega
  rw [length_cons_add, hidx, (lift_zero_succ Δ.length s).symm]

theorem instantiate_binder_shift0 (s : Expr Nat) (Δ : LCtx)
    (e : Expr Nat) (x : LocalDecl) :
    instantiate (x :: Δ).length (lift 0 (x :: Δ).length s) e =
      instantiate (Δ.length + 1) (lift 0 1 (lift 0 Δ.length s)) e := by
  have h := instantiate_binder_shift 0 s Δ e x
  simp only [Nat.zero_add] at h
  exact h

/-- Lookup in the prefix, after instantiating stored lets, is
instantiate of the source lookup. -/
theorem lookupValue_instLCtx (c : Nat) (s : Expr Nat) (Δ : LCtx) (i : Nat)
    (hi : i < Δ.length) :
    lookupValue (instLCtx c s Δ) i =
      (lookupValue Δ i).map
        (instantiate (c + Δ.length) (lift 0 Δ.length s)) := by
  induction Δ generalizing i with
  | nil =>
      simp only [List.length_nil] at hi; omega
  | cons d Δ ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero =>
              simp only [instLCtx, lookupValue, List.get?_cons_zero]
              rfl
          | succ i' =>
              have hi' : i' < Δ.length := by
                simp only [List.length_cons] at hi; omega
              simp only [instLCtx, lookupValue_cons_succ, ih i' hi']
              cases hv : lookupValue Δ i' with
              | none => rfl
              | some v =>
                  simp only [Option.map_some']
                  have hk :=
                    instantiate_of_lift_succ (c + Δ.length) (lift 0 Δ.length s) v
                  have hidx : c + (Δ.length + 1) = (c + Δ.length) + 1 := by omega
                  rw [length_cons_add, hidx, (lift_zero_succ Δ.length s).symm, hk]
      | letBinding A w =>
          cases i with
          | zero =>
              simp only [instLCtx, lookupValue, List.get?_cons_zero, Option.map_some']
              have hk :=
                instantiate_of_lift_succ (c + Δ.length) (lift 0 Δ.length s) w
              have hidx : c + (Δ.length + 1) = (c + Δ.length) + 1 := by omega
              rw [length_cons_add, hidx, (lift_zero_succ Δ.length s).symm, hk]
          | succ i' =>
              have hi' : i' < Δ.length := by
                simp only [List.length_cons] at hi; omega
              simp only [instLCtx, lookupValue_cons_succ, ih i' hi']
              cases hv : lookupValue Δ i' with
              | none => rfl
              | some v =>
                  simp only [Option.map_some']
                  have hk :=
                    instantiate_of_lift_succ (c + Δ.length) (lift 0 Δ.length s) v
                  have hidx : c + (Δ.length + 1) = (c + Δ.length) + 1 := by omega
                  rw [length_cons_add, hidx, (lift_zero_succ Δ.length s).symm, hk]

theorem lookupValue_inst_source_lt (c : Nat) (s : Expr Nat)
    (Δ base : LCtx) (i : Nat) (hi : i < c + Δ.length) :
    lookupValue (instLCtx c s Δ ++ assumpPad c base) i =
      (lookupValue (Δ ++ assumpPad (c + 1) base) i).map
        (instantiate (c + Δ.length) (lift 0 Δ.length s)) := by
  by_cases hΔ : i < Δ.length
  · have hlen : i < (instLCtx c s Δ).length := by
      rw [instLCtx_length]; exact hΔ
    rw [lookupValue_append_left (instLCtx c s Δ) (assumpPad c base) i hlen,
      lookupValue_append_left Δ (assumpPad (c + 1) base) i hΔ,
      lookupValue_instLCtx c s Δ i hΔ]
  · have hiΔ : Δ.length ≤ i := Nat.le_of_not_lt hΔ
    have ⟨i0, hi0⟩ := Nat.exists_eq_add_of_le hiΔ
    subst hi0
    have hi0c : i0 < c := by omega
    have hlenI : (instLCtx c s Δ).length = Δ.length := instLCtx_length c s Δ
    have hL :
        lookupValue (instLCtx c s Δ ++ assumpPad c base)
          ((instLCtx c s Δ).length + i0) =
          (lookupValue (assumpPad c base) i0).map
            (lift 0 (instLCtx c s Δ).length) :=
      lookupValue_append_right (instLCtx c s Δ) (assumpPad c base) i0
    rw [hlenI] at hL
    rw [hL, lookupValue_append_right Δ (assumpPad (c + 1) base) i0,
      lookupValue_assumpPad_lt c base i0 hi0c,
      lookupValue_assumpPad_lt (c + 1) base i0 (Nat.lt_trans hi0c (Nat.lt_succ_self c))]
    rfl

theorem lookupValue_inst_source_gt (c : Nat) (s : Expr Nat)
    (Δ base : LCtx) (i : Nat) (hi : c + Δ.length < i) :
    lookupValue (instLCtx c s Δ ++ assumpPad c base) (i - 1) =
      (lookupValue (Δ ++ assumpPad (c + 1) base) i).map
        (instantiate (c + Δ.length) (lift 0 Δ.length s)) := by
  have hlenI : (instLCtx c s Δ).length = Δ.length := instLCtx_length c s Δ
  have hi1 : Δ.length ≤ i - 1 := by omega
  have ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi1
  have hj' : i = Δ.length + (j + 1) := by omega
  have hL :
      lookupValue (instLCtx c s Δ ++ assumpPad c base)
        ((instLCtx c s Δ).length + j) =
        (lookupValue (assumpPad c base) j).map
          (lift 0 (instLCtx c s Δ).length) :=
    lookupValue_append_right (instLCtx c s Δ) (assumpPad c base) j
  rw [hlenI] at hL
  have hi1eq : i - 1 = Δ.length + j := by omega
  rw [hi1eq, hL, hj', lookupValue_append_right Δ (assumpPad (c + 1) base) (j + 1)]
  have hpad :
      lookupValue (assumpPad (c + 1) base) (j + 1) =
        (lookupValue (assumpPad c base) j).map (lift 0 1) := by
    simp only [assumpPad_succ, lookupValue_cons_succ]
  rw [hpad]
  cases hv : lookupValue (assumpPad c base) j with
  | none => rfl
  | some v =>
      simp only [Option.map_some']
      have hjc : c ≤ j :=
        Nat.le_of_not_lt fun hlt => by
          have hnone := lookupValue_assumpPad_lt c base j hlt
          rw [hnone] at hv
          exact Option.noConfusion hv
      have ⟨j0, hj0⟩ := Nat.exists_eq_add_of_le hjc
      subst hj0
      rw [lookupValue_assumpPad_ge] at hv
      cases hb : lookupValue base j0 with
      | none =>
          simp only [hb, Option.map_none'] at hv
          exact nomatch hv
      | some v0 =>
          simp only [hb, Option.map_some'] at hv
          injection hv with hvEq
          subst hvEq
          -- LHS: lift 0 Δ.length (lift 0 c v0)
          -- RHS: instantiate k sΔ (lift 0 Δ.length (lift 0 1 (lift 0 c v0)))
          have hcomp1 : lift 0 Δ.length (lift 0 c v0) = lift 0 (Δ.length + c) v0 :=
            lift_zero_comp Δ.length c v0
          have hcomp2 :
              lift 0 Δ.length (lift 0 1 (lift 0 c v0)) =
                lift 0 (Δ.length + (c + 1)) v0 := by
            rw [lift_zero_succ c v0, lift_zero_comp Δ.length (c + 1) v0]
          have hcancel :
              instantiate (c + Δ.length) (lift 0 Δ.length s)
                (lift 0 (Δ.length + (c + 1)) v0) =
              lift 0 (Δ.length + c) v0 := by
            have hidx : c + Δ.length = Δ.length + c := Nat.add_comm _ _
            rw [hidx]
            exact instantiate_lift_cancel (Δ.length + (c + 1)) 0 (Δ.length + c)
              (lift 0 Δ.length s) (Nat.zero_le _) (by omega) v0
          rw [hcomp1, hcomp2, hcancel]

theorem instantiate_foldApps_const (j : Nat) (s : Expr Nat)
    (r : Nat) (ls : List Level) (xs : List (Expr Nat)) :
    instantiate j s (foldApps (.const r ls) xs) =
      foldApps (.const r ls) (xs.map (instantiate j s)) := by
  rw [foldApps_instantiate, instantiate]

theorem assumpPad_drop (k : Nat) (Γ : LCtx) : (assumpPad k Γ).drop k = Γ := by
  induction k generalizing Γ with
  | zero => simp only [assumpPad, List.drop]
  | succ k ih => simp only [assumpPad, List.drop]; exact ih Γ

theorem drop_append_length (xs ys : List LocalDecl) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => simp only [List.nil_append, List.length_nil, List.drop]
  | cons _ xs ih => simp only [List.cons_append, List.length_cons, List.drop]; exact ih

theorem instLCtx_drop (c : Nat) (s : Expr Nat) :
    (n : Nat) → (Δ : LCtx) →
    instLCtx c s (Δ.drop n) = (instLCtx c s Δ).drop n
  | 0, Δ => by simp only [List.drop]
  | _n + 1, [] => by simp only [List.drop, instLCtx]
  | n + 1, .assumption _ :: Δ => by
      simp only [List.drop, instLCtx]; exact instLCtx_drop c s n Δ
  | n + 1, .letBinding _ _ :: Δ => by
      simp only [List.drop, instLCtx]; exact instLCtx_drop c s n Δ

/-- Cut sits in the tail: drop past an earlier let. -/
theorem inst_cut_drop_lt (c : Nat) (s : Expr Nat) (Δ base : LCtx) {i : Nat}
    (h : i < Δ.length) :
    (instLCtx c s Δ ++ assumpPad c base).drop (i + 1) =
      instLCtx c s (Δ.drop (i + 1)) ++ assumpPad c base := by
  have hle : i + 1 ≤ (instLCtx c s Δ).length := by
    rw [instLCtx_length]; omega
  rw [List.drop_append_of_le_length hle, instLCtx_drop]

/-- Cut sits in the prefix: tail after a later let is the original tail. -/
theorem inst_cut_drop_gt (c : Nat) (s : Expr Nat) (Δ base : LCtx) {i : Nat}
    (h : c + Δ.length < i) :
    (instLCtx c s Δ ++ assumpPad c base).drop i =
      (Δ ++ assumpPad (c + 1) base).drop (i + 1) := by
  have hL : (instLCtx c s Δ ++ assumpPad c base).drop (c + Δ.length) = base := by
    have hlen := instLCtx_length c s Δ
    have hswap : c + Δ.length = (instLCtx c s Δ).length + c := by
      rw [hlen]; exact Nat.add_comm _ _
    rw [hswap, ← List.drop_drop, drop_append_length]
    exact assumpPad_drop c base
  have hR : (Δ ++ assumpPad (c + 1) base).drop (c + Δ.length + 1) = base := by
    have hswap : c + Δ.length + 1 = Δ.length + (c + 1) := by omega
    rw [hswap, ← List.drop_drop, drop_append_length]
    exact assumpPad_drop (c + 1) base
  have hi : i = (c + Δ.length) + (i - (c + Δ.length)) := by omega
  have hi1 : i + 1 = (c + Δ.length + 1) + (i - (c + Δ.length)) := by omega
  calc (instLCtx c s Δ ++ assumpPad c base).drop i
      = (instLCtx c s Δ ++ assumpPad c base).drop
          ((c + Δ.length) + (i - (c + Δ.length))) :=
        congrArg (fun n =>
          (instLCtx c s Δ ++ assumpPad c base).drop n) hi
    _ = ((instLCtx c s Δ ++ assumpPad c base).drop (c + Δ.length)).drop
          (i - (c + Δ.length)) :=
        (List.drop_drop (i - (c + Δ.length)) (c + Δ.length)
          (instLCtx c s Δ ++ assumpPad c base)).symm
    _ = base.drop (i - (c + Δ.length)) :=
        congrArg (fun t => t.drop (i - (c + Δ.length))) hL
    _ = ((Δ ++ assumpPad (c + 1) base).drop (c + Δ.length + 1)).drop
          (i - (c + Δ.length)) :=
        congrArg (fun t => t.drop (i - (c + Δ.length))) hR.symm
    _ = (Δ ++ assumpPad (c + 1) base).drop
          ((c + Δ.length + 1) + (i - (c + Δ.length))) :=
        List.drop_drop (i - (c + Δ.length)) (c + Δ.length + 1)
          (Δ ++ assumpPad (c + 1) base)
    _ = (Δ ++ assumpPad (c + 1) base).drop (i + 1) :=
        congrArg (fun n => (Δ ++ assumpPad (c + 1) base).drop n) hi1.symm

theorem inst_let_drop_lt (w : Expr Nat) (Δ base : LCtx) {i : Nat}
    (h : i < Δ.length) :
    (instLCtx 0 w Δ ++ base).drop (i + 1) =
      instLCtx 0 w (Δ.drop (i + 1)) ++ base := by
  have hle : i + 1 ≤ (instLCtx 0 w Δ).length := by
    rw [instLCtx_length]; omega
  rw [List.drop_append_of_le_length hle, instLCtx_drop]

theorem inst_let_drop_gt (A w : Expr Nat) (Δ base : LCtx) {i : Nat}
    (h : Δ.length < i) :
    (instLCtx 0 w Δ ++ base).drop i =
      (Δ ++ .letBinding A w :: base).drop (i + 1) := by
  have hL : (instLCtx 0 w Δ ++ base).drop Δ.length = base := by
    rw [← instLCtx_length 0 w Δ, drop_append_length]
  have hR : (Δ ++ .letBinding A w :: base).drop (Δ.length + 1) = base := by
    have h : (Δ ++ .letBinding A w :: base).drop (Δ.length + 1) =
        ((Δ ++ .letBinding A w :: base).drop Δ.length).drop 1 :=
      (List.drop_drop 1 Δ.length _).symm
    rw [h, drop_append_length]
    simp only [List.drop]
  have hi : i = Δ.length + (i - Δ.length) := by omega
  have hi1 : i + 1 = (Δ.length + 1) + (i - Δ.length) := by omega
  calc (instLCtx 0 w Δ ++ base).drop i
      = (instLCtx 0 w Δ ++ base).drop (Δ.length + (i - Δ.length)) :=
        congrArg (fun n => (instLCtx 0 w Δ ++ base).drop n) hi
    _ = ((instLCtx 0 w Δ ++ base).drop Δ.length).drop (i - Δ.length) :=
        (List.drop_drop (i - Δ.length) Δ.length (instLCtx 0 w Δ ++ base)).symm
    _ = base.drop (i - Δ.length) :=
        congrArg (fun t => t.drop (i - Δ.length)) hL
    _ = ((Δ ++ .letBinding A w :: base).drop (Δ.length + 1)).drop
          (i - Δ.length) :=
        congrArg (fun t => t.drop (i - Δ.length)) hR.symm
    _ = (Δ ++ .letBinding A w :: base).drop
          ((Δ.length + 1) + (i - Δ.length)) :=
        List.drop_drop (i - Δ.length) (Δ.length + 1)
          (Δ ++ .letBinding A w :: base)
    _ = (Δ ++ .letBinding A w :: base).drop (i + 1) :=
        congrArg (fun n => (Δ ++ .letBinding A w :: base).drop n) hi1.symm

theorem drop_append_succ_let (Δ : LCtx) (A w : Expr Nat) (base : LCtx) :
    (Δ ++ .letBinding A w :: base).drop (Δ.length + 1) = base := by
  have h : (Δ ++ .letBinding A w :: base).drop (Δ.length + 1) =
      ((Δ ++ .letBinding A w :: base).drop Δ.length).drop 1 :=
    (List.drop_drop 1 Δ.length _).symm
  rw [h, drop_append_length]
  simp only [List.drop]

theorem length_drop_of_le {α} (xs : List α) {n : Nat} (h : n ≤ xs.length) :
    (xs.drop n).length = xs.length - n := by
  induction xs generalizing n with
  | nil =>
      have : n = 0 := by simp only [List.length_nil] at h; omega
      subst this; rfl
  | cons _ xs ih =>
      cases n with
      | zero => simp only [List.drop, Nat.sub_zero]
      | succ n =>
          simp only [List.drop, List.length_cons]
          have : n ≤ xs.length := by
            simp only [List.length_cons] at h; omega
          rw [ih this]; omega

mutual
/-- Term-only instantiate: the ParRed lives in Δ ++ assumpPad (c+1) base. -/
def parRed_instantiate_term {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} :
    {Γ : LCtx} → {e e' : Expr Nat} →
    ParRed E n Γ e e' →
    (c : Nat) → (s : Expr Nat) → (Δ : LCtx) →
    (hΔ : Γ = Δ ++ assumpPad (c + 1) base) →
    ParRed E n (instLCtx c s Δ ++ assumpPad c base)
      (instantiate (c + Δ.length) (lift 0 Δ.length s) e)
      (instantiate (c + Δ.length) (lift 0 Δ.length s) e')
  | Γ, _, _, .refl _ e, c, s, Δ, _hΔ => .refl _ _
  | Γ, _, _, .sortEq _ l₁ l₂ h, c, s, Δ, _hΔ => by
      simp only [instantiate]
      exact .sortEq _ l₁ l₂ h
  | Γ, _, _, .consts _ r ls ls' h, c, s, Δ, _hΔ => by
      simp only [instantiate]
      exact .consts _ r ls ls' h
  | Γ, _, _, .lit _ t, c, s, Δ, _hΔ => by
      simp only [instantiate, natExpand_instantiate]
      exact .lit _ t
  | Γ, _, _, .bvarZeta _ i A v v' hlk hv, c, s, Δ, hΔ => by
      let k := c + Δ.length
      let sΔ := lift 0 Δ.length s
      simp only [instantiate]
      have hlkV := lookupValue_of_get?_let hlk
      have hlkΔ : lookupValue (Δ ++ assumpPad (c + 1) base) i =
          some (lift 0 (i + 1) v) := by
        rw [← hΔ]; exact hlkV
      by_cases hic : i < k
      · -- Cut sits in the tail; recurse on `hv`.
        have hltΔ : i < Δ.length := by
          by_cases hge : i < Δ.length
          · exact hge
          · have hiΔ : Δ.length ≤ i := Nat.le_of_not_lt hge
            have ⟨j, hj⟩ := Nat.exists_eq_add_of_le hiΔ
            subst hj
            have hjc : j < c := by omega
            have hnone := lookupValue_append_right Δ (assumpPad (c + 1) base) j
            have hpad := lookupValue_assumpPad_lt (c + 1) base j
              (Nat.lt_trans hjc (Nat.lt_succ_self c))
            simp only [hpad, Option.map_none'] at hnone
            rw [hnone] at hlkΔ
            exact nomatch hlkΔ
        have hne : i ≠ k := by omega
        have hnlt : ¬ k < i := by omega
        simp only [if_neg hne, if_neg hnlt]
        have hΔt : Γ.drop (i + 1) =
            Δ.drop (i + 1) ++ assumpPad (c + 1) base := by
          rw [hΔ, List.drop_append_of_le_length (Nat.succ_le_of_lt hltΔ)]
        have hv' :=
          parRed_instantiate_term hE hv c s (Δ.drop (i + 1)) hΔt
        have hdrop := inst_cut_drop_lt c s Δ base hltΔ
        rw [← hdrop] at hv'
        have hmap := lookupValue_inst_source_lt c s Δ base i (by omega)
        rw [hlkΔ, Option.map_some'] at hmap
        let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hlenD : (Δ.drop (i + 1)).length = Δ.length - (i + 1) :=
          length_drop_of_le Δ (Nat.succ_le_of_lt hltΔ)
        have hsL :
            lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length s) = sΔ := by
          rw [hlenD, lift_zero_comp]
          have : i + 1 + (Δ.length - (i + 1)) = Δ.length := by omega
          rw [this]
        have hj : i + 1 + (c + (Δ.drop (i + 1)).length) = k := by
          rw [hlenD]; omega
        have hcomm (e : Expr Nat) :
            instantiate k sΔ (lift 0 (i + 1) e) =
              lift 0 (i + 1)
                (instantiate (c + (Δ.drop (i + 1)).length)
                  (lift 0 (Δ.drop (i + 1)).length s) e) := by
          have h1 := lift_instantiate_high (i + 1) 0
            (c + (Δ.drop (i + 1)).length)
            (lift 0 (Δ.drop (i + 1)).length s) (Nat.zero_le _) e
          rw [h1, hj, hsL]
        have hstored : stored =
            instantiate (c + (Δ.drop (i + 1)).length)
              (lift 0 (Δ.drop (i + 1)).length s) v :=
          lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm v))
        rw [← hstored] at hv'
        exact (hcomm v') ▸
          .bvarZeta _ i A' stored _ hg' hv'
      · -- Cut sits in the prefix; reuse `hv`. Dummy slot is nomatch.
        by_cases hi : i = k
        · subst hi
          have hnone := lookupValue_dummy_slot Δ c base
          rw [hnone] at hlkΔ
          exact nomatch hlkΔ
        · have hgt : k < i := by omega
          simp only [if_neg hi, if_pos hgt]
          have hmap := lookupValue_inst_source_gt c s Δ base i (by omega)
          rw [hlkΔ, Option.map_some'] at hmap
          let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan :
              instantiate k sΔ (lift 0 (i + 1) v) = lift 0 i v :=
            instantiate_lift_cancel (i + 1) 0 k sΔ (Nat.zero_le k)
              (by omega) v
          have hi1 : (i - 1) + 1 = i := by omega
          have hstored : stored = v :=
            lift_zero_amount_inj i (by
              have heq' : instantiate k sΔ (lift 0 (i + 1) v) =
                  lift 0 ((i - 1) + 1) stored := heq
              rw [hi1] at heq'
              exact heq'.symm.trans hcan)
          have htgt : lift 0 i v' =
              instantiate k sΔ (lift 0 (i + 1) v') :=
            (instantiate_lift_cancel (i + 1) 0 k sΔ (Nat.zero_le k)
              (by omega) v').symm
          have hdrop := inst_cut_drop_gt c s Δ base hgt
          have hv' : ParRed E n
              ((instLCtx c s Δ ++ assumpPad c base).drop i) v v' := by
            rw [hdrop, ← hΔ]; exact hv
          have hbz :=
            ParRed.bvarZeta (instLCtx c s Δ ++ assumpPad c base) (i - 1)
              A' v v' (hstored ▸ hg') (by rw [hi1]; exact hv')
          exact htgt ▸ (hi1 ▸ hbz)
  | Γ, _, _, .delta _ r ls m b hres hbody htr, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hid := (envWf_subst_inst hE r m hres).2 b hbody ls
        (lift 0 Δ.length s) (c + Δ.length)
      rw [hid]
      exact .delta _ r ls m b hres hbody htr
  | Γ, _, _, .app _ f f' x x' hf ha, c, s, Δ, hΔ => by
      simp only [instantiate]
      exact .app _ _ _ _ _
        (parRed_instantiate_term hE hf c s Δ hΔ)
        (parRed_instantiate_term hE ha c s Δ hΔ)
  | Γ, _, _, .lam _ A A' b b' hA hb, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad (c + 1) base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_term hE hA c s Δ hΔ
      have hb' :=
        parRed_instantiate_term hE hb c s (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift c s Δ b (.assumption A)] at hb'
      rw [instantiate_binder_shift c s Δ b' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append] at hb'
      exact .lam _ _ _ _ _ hA' hb'
  | Γ, _, _, .pi _ A A' b b' hA hb, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad (c + 1) base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_term hE hA c s Δ hΔ
      have hb' :=
        parRed_instantiate_term hE hb c s (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift c s Δ b (.assumption A)] at hb'
      rw [instantiate_binder_shift c s Δ b' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append] at hb'
      exact .pi _ _ _ _ _ hA' hb'
  | Γ, _, _, .letE _ A A' v v' b b' hA hv hb, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding A v :: Γ =
            (.letBinding A v :: Δ) ++ assumpPad (c + 1) base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_term hE hA c s Δ hΔ
      have hv' := parRed_instantiate_term hE hv c s Δ hΔ
      have hb' :=
        parRed_instantiate_term hE hb c s (.letBinding A v :: Δ) hΔb
      rw [instantiate_binder_shift c s Δ b (.letBinding A v)] at hb'
      rw [instantiate_binder_shift c s Δ b' (.letBinding A v)] at hb'
      simp only [instLCtx, List.cons_append] at hb'
      exact .letE _ _ _ _ _ _ _ hA' hv' hb'
  | Γ, _, _, .beta _ A A' body body' arg arg' hA hb ha, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad (c + 1) base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_term hE hA c s Δ hΔ
      have ha' := parRed_instantiate_term hE ha c s Δ hΔ
      have hb' :=
        parRed_instantiate_term hE hb c s (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift c s Δ body (.assumption A)] at hb'
      rw [instantiate_binder_shift c s Δ body' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append] at hb'
      have hcomm :=
        instantiate_instantiate 0 (c + Δ.length) arg'
          (lift 0 Δ.length s) (Nat.zero_le _) body'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .beta _ _ _ _ _ _ _ hA' hb' ha'
  | Γ, _, _, .zeta _ A A' v v' b b' hA hv hb, c, s, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding A v :: Γ =
            (.letBinding A v :: Δ) ++ assumpPad (c + 1) base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_term hE hA c s Δ hΔ
      have hv' := parRed_instantiate_term hE hv c s Δ hΔ
      have hb' :=
        parRed_instantiate_term hE hb c s (.letBinding A v :: Δ) hΔb
      rw [instantiate_binder_shift c s Δ b (.letBinding A v)] at hb'
      rw [instantiate_binder_shift c s Δ b' (.letBinding A v)] at hb'
      simp only [instLCtx, List.cons_append] at hb'
      have hcomm :=
        instantiate_instantiate 0 (c + Δ.length) v'
          (lift 0 Δ.length s) (Nat.zero_le _) b'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .zeta _ _ _ _ _ _ _ hA' hv' hb'
  | Γ, _, _, .iotaSpine _ w lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs, c, s, Δ, hΔ => by
      let k := c + Δ.length
      let s' := lift 0 Δ.length s
      have hf' := parRedArgs_instantiate_term hE hf c s Δ hΔ
      have ha' := parRedArgs_instantiate_term hE ha c s Δ hΔ
      have hsrc :
          instantiate k s'
            (recCall (.const w.recRef lsR) pre
              (foldApps (.const w.ctorRef lsC) fields)) =
          recCall (.const (instWitness k s' w).recRef lsR)
            (pre.map (instantiate k s'))
            (foldApps (.const (instWitness k s' w).ctorRef lsC)
              (fields.map (instantiate k s'))) := by
        rw [recCall_instantiate, instantiate, instantiate_foldApps_const]
        rfl
      rw [hsrc]
      have hpreLen' : (pre'.map (instantiate k s')).length =
          (instWitness k s' w).preMajor.length := by
        simp only [instWitness, List.length_map]; exact hpreLen
      have hfieldsLen' : (fields'.map (instantiate k s')).length =
          ((instWitness k s' w).ctorParams ++
            (instWitness k s' w).fields).length := by
        simp only [instWitness]
        exact map_ctorSpine_length (instantiate k s') hfieldsLen
      have hlhs' : iotaLhsOf (instWitness k s' w) =
          recCall (.const (instWitness k s' w).recRef (instWitness k s' w).ls)
            (pre'.map (instantiate k s'))
            (foldApps (.const (instWitness k s' w).ctorRef (instWitness k s' w).lsC)
              (fields'.map (instantiate k s'))) := by
        have := congrArg (instantiate k s') hlhs
        rw [← iotaLhsOf_instantiate, recCall_instantiate, instantiate,
          instantiate_foldApps_const] at this
        exact this
      rw [← iotaRhsOf_instantiate k s' w]
      exact .iotaSpine _ (instWitness k s' w) lsR lsC hlsR hlsC
        (pre.map (instantiate k s')) (pre'.map (instantiate k s'))
        (fields.map (instantiate k s')) (fields'.map (instantiate k s'))
        hf' ha' hpreLen' hfieldsLen' hlhs'

def parRedArgs_instantiate_term {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {Γ : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (c : Nat) (s : Expr Nat) (Δ : LCtx)
    (hΔ : Γ = Δ ++ assumpPad (c + 1) base) :
    ParRedArgs E n (instLCtx c s Δ ++ assumpPad c base)
      (xs.map (instantiate (c + Δ.length) (lift 0 Δ.length s)))
      (ys.map (instantiate (c + Δ.length) (lift 0 Δ.length s))) :=
  match h with
  | ParRedArgs.nil Γ => ParRedArgs.nil _
  | ParRedArgs.cons hx t =>
      .cons (parRed_instantiate_term hE hx c s Δ hΔ)
        (parRedArgs_instantiate_term hE (h := t) c s Δ hΔ)

def parRedStar_instantiate_term {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} :
    {Γ : LCtx} → {e e' : Expr Nat} →
    ParRedStar E n Γ e e' →
    (c : Nat) → (s : Expr Nat) → (Δ : LCtx) →
    (hΔ : Γ = Δ ++ assumpPad (c + 1) base) →
    ParRedStar E n (instLCtx c s Δ ++ assumpPad c base)
      (instantiate (c + Δ.length) (lift 0 Δ.length s) e)
      (instantiate (c + Δ.length) (lift 0 Δ.length s) e')
  | _, _, _, .refl _ e, c, s, Δ, _hΔ => .refl _ _
  | _, _, _, .tail h hs, c, s, Δ, hΔ =>
      .tail (parRed_instantiate_term hE h c s Δ hΔ)
        (parRedStar_instantiate_term hE hs c s Δ hΔ)
end

/-- Weaken through a context prefix. `lift_zero_succ` merges the lifts. -/
def parRed_weaken_lctx {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    (Δ : LCtx) → {Γ : LCtx} → {a b : Expr Nat} →
    ParRed E n Γ a b →
    ParRed E n (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b)
  | [], _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact h
  | d :: Δ, Γ, a, b, h => by
      have ih := parRed_weaken_lctx hE Δ h
      have hw := parRed_weaken d hE (c := 0) ih
      simp only [List.cons_append, List.length_cons]
      have ha : lift 0 1 (lift 0 Δ.length a) = lift 0 (Δ.length + 1) a :=
        lift_zero_succ Δ.length a
      have hb : lift 0 1 (lift 0 Δ.length b) = lift 0 (Δ.length + 1) b :=
        lift_zero_succ Δ.length b
      rw [← ha, ← hb]
      exact hw

/-- Iterate single-binder weaken. bvarZeta diamond lifts a tail join
by `i+1` binders (`Δ = Γ.take (i+1)`). -/
def parRed_lift_n {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :=
  parRed_weaken_lctx (hE := hE)

mutual
def parRed_instantiate_both {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {v v' : Expr Nat}
    (hv : ParRed E n base v v') :
    {Γ : LCtx} → {e e' : Expr Nat} →
    ParRed E n Γ e e' →
    (Δ : LCtx) →
    (hΔ : Γ = Δ ++ assumpPad 1 base) →
    ParRed E n (instLCtx 0 v Δ ++ base)
      (instantiate Δ.length (lift 0 Δ.length v) e)
      (instantiate Δ.length (lift 0 Δ.length v') e')
  | Γ, _, _, .refl _ e, Δ, _hΔ => by
      have hvw := parRed_weaken_lctx hE (instLCtx 0 v Δ) hv
      rw [instLCtx_length] at hvw
      exact parRed_instantiate_arg hE hvw (c := Δ.length) e
  | Γ, _, _, .sortEq _ l₁ l₂ h, Δ, _hΔ => by
      simp only [instantiate]
      exact .sortEq _ l₁ l₂ h
  | Γ, _, _, .consts _ r ls ls' h, Δ, _hΔ => by
      simp only [instantiate]
      exact .consts _ r ls ls' h
  | Γ, _, _, .lit _ t, Δ, _hΔ => by
      simp only [instantiate, natExpand_instantiate]
      exact .lit _ t
  | Γ, _, _, .bvarZeta _ i A val val' hlk hval, Δ, hΔ => by
      let k := Δ.length
      let s := lift 0 Δ.length v
      let s' := lift 0 Δ.length v'
      simp only [instantiate]
      have hlkV := lookupValue_of_get?_let hlk
      have hlkΔ : lookupValue (Δ ++ assumpPad 1 base) i =
          some (lift 0 (i + 1) val) := by
        rw [← hΔ]; exact hlkV
      by_cases hic : i < k
      · have hne : i ≠ k := by omega
        have hnlt : ¬ k < i := by omega
        simp only [if_neg hne, if_neg hnlt]
        have hΔt : Γ.drop (i + 1) =
            Δ.drop (i + 1) ++ assumpPad 1 base := by
          rw [hΔ, List.drop_append_of_le_length (Nat.succ_le_of_lt hic)]
        have hvI :=
          parRed_instantiate_both hE hv hval (Δ.drop (i + 1)) hΔt
        have hdrop := inst_cut_drop_lt 0 v Δ base hic
        simp only [Nat.zero_add, assumpPad_zero] at hdrop
        rw [← hdrop] at hvI
        have hmap := lookupValue_inst_source_lt 0 v Δ base i (by omega)
        simp only [Nat.zero_add] at hmap
        rw [hlkΔ, Option.map_some'] at hmap
        simp only [assumpPad] at hmap
        let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hlenD : (Δ.drop (i + 1)).length = Δ.length - (i + 1) :=
          length_drop_of_le Δ (Nat.succ_le_of_lt hic)
        have hsL :
            lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length v) = s := by
          rw [hlenD, lift_zero_comp]
          have : i + 1 + (Δ.length - (i + 1)) = Δ.length := by omega
          rw [this]
        have hsL' :
            lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length v') = s' := by
          rw [hlenD, lift_zero_comp]
          have : i + 1 + (Δ.length - (i + 1)) = Δ.length := by omega
          rw [this]
        have hj : i + 1 + (Δ.drop (i + 1)).length = k := by
          rw [hlenD]; omega
        have hcomm (e subst : Expr Nat)
            (hsEq : lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length subst) =
              lift 0 Δ.length subst) :
            instantiate k (lift 0 Δ.length subst) (lift 0 (i + 1) e) =
              lift 0 (i + 1)
                (instantiate (Δ.drop (i + 1)).length
                  (lift 0 (Δ.drop (i + 1)).length subst) e) := by
          have h1 := lift_instantiate_high (i + 1) 0
            (Δ.drop (i + 1)).length
            (lift 0 (Δ.drop (i + 1)).length subst) (Nat.zero_le _) e
          rw [h1, hj, hsEq]
        have hstored : stored =
            instantiate (Δ.drop (i + 1)).length
              (lift 0 (Δ.drop (i + 1)).length v) val :=
          lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm val v hsL))
        rw [← hstored] at hvI
        exact (hcomm val' v' hsL') ▸
          .bvarZeta _ i A' stored _ hg' hvI
      · by_cases hi : i = k
        · subst hi
          have hnone := lookupValue_dummy_slot Δ 0 base
          simp only [Nat.zero_add] at hnone
          rw [hnone] at hlkΔ
          exact nomatch hlkΔ
        · have hgt : k < i := by omega
          simp only [if_neg hi, if_pos hgt]
          have hmap := lookupValue_inst_source_gt 0 v Δ base i (by omega)
          simp only [Nat.zero_add] at hmap
          rw [hlkΔ, Option.map_some'] at hmap
          simp only [assumpPad] at hmap
          let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan :
              instantiate k s (lift 0 (i + 1) val) = lift 0 i val :=
            instantiate_lift_cancel (i + 1) 0 k s (Nat.zero_le k)
              (by omega) val
          have hi1 : (i - 1) + 1 = i := by omega
          have hstored : stored = val :=
            lift_zero_amount_inj i (by
              have heq' : instantiate k s (lift 0 (i + 1) val) =
                  lift 0 ((i - 1) + 1) stored := heq
              rw [hi1] at heq'
              exact heq'.symm.trans hcan)
          have htgt : lift 0 i val' =
              instantiate k s' (lift 0 (i + 1) val') :=
            (instantiate_lift_cancel (i + 1) 0 k s' (Nat.zero_le k)
              (by omega) val').symm
          have hgt0 : 0 + Δ.length < i := by
            simp only [Nat.zero_add]; exact hgt
          have hdrop := inst_cut_drop_gt 0 v Δ base hgt0
          simp only [Nat.zero_add, assumpPad_zero] at hdrop
          have hvI : ParRed E n
              ((instLCtx 0 v Δ ++ base).drop i) val val' := by
            rw [hdrop, ← hΔ]; exact hval
          have hbz :=
            ParRed.bvarZeta (instLCtx 0 v Δ ++ base) (i - 1)
              A' val val' (hstored ▸ hg') (by rw [hi1]; exact hvI)
          exact htgt ▸ (hi1 ▸ hbz)
  | Γ, _, _, .delta _ r ls m b hres hbody htr, Δ, hΔ => by
      simp only [instantiate]
      have hid' := (envWf_subst_inst hE r m hres).2 b hbody ls
        (lift 0 Δ.length v') Δ.length
      rw [hid']
      exact .delta _ r ls m b hres hbody htr
  | Γ, _, _, .app _ f f' x x' hf ha, Δ, hΔ => by
      simp only [instantiate]
      exact .app _ _ _ _ _
        (parRed_instantiate_both hE hv hf Δ hΔ)
        (parRed_instantiate_both hE hv ha Δ hΔ)
  | Γ, _, _, .lam _ A A' b b' hA hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad 1 base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_both hE hv hA Δ hΔ
      have hb' :=
        parRed_instantiate_both hE hv hb (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift0 v Δ b (.assumption A)] at hb'
      rw [instantiate_binder_shift0 v' Δ b' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .lam _ _ _ _ _ hA' hb'
  | Γ, _, _, .pi _ A A' b b' hA hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad 1 base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_both hE hv hA Δ hΔ
      have hb' :=
        parRed_instantiate_both hE hv hb (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift0 v Δ b (.assumption A)] at hb'
      rw [instantiate_binder_shift0 v' Δ b' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .pi _ _ _ _ _ hA' hb'
  | Γ, _, _, .letE _ A A' w w' b b' hA hw hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding A w :: Γ =
            (.letBinding A w :: Δ) ++ assumpPad 1 base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_both hE hv hA Δ hΔ
      have hw' := parRed_instantiate_both hE hv hw Δ hΔ
      have hb' :=
        parRed_instantiate_both hE hv hb (.letBinding A w :: Δ) hΔb
      rw [instantiate_binder_shift0 v Δ b (.letBinding A w)] at hb'
      rw [instantiate_binder_shift0 v' Δ b' (.letBinding A w)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .letE _ _ _ _ _ _ _ hA' hw' hb'
  | Γ, _, _, .beta _ A A' body body' arg arg' hA hb ha, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption A :: Γ =
            (.assumption A :: Δ) ++ assumpPad 1 base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_both hE hv hA Δ hΔ
      have ha' := parRed_instantiate_both hE hv ha Δ hΔ
      have hb' :=
        parRed_instantiate_both hE hv hb (.assumption A :: Δ) hΔb
      rw [instantiate_binder_shift0 v Δ body (.assumption A)] at hb'
      rw [instantiate_binder_shift0 v' Δ body' (.assumption A)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      have hcomm :=
        instantiate_instantiate 0 Δ.length arg'
          (lift 0 Δ.length v') (Nat.zero_le _) body'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .beta _ _ _ _ _ _ _ hA' hb' ha'
  | Γ, _, _, .zeta _ A A' w w' b b' hA hw hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding A w :: Γ =
            (.letBinding A w :: Δ) ++ assumpPad 1 base := by
        rw [hΔ, List.cons_append]
      have hA' := parRed_instantiate_both hE hv hA Δ hΔ
      have hw' := parRed_instantiate_both hE hv hw Δ hΔ
      have hb' :=
        parRed_instantiate_both hE hv hb (.letBinding A w :: Δ) hΔb
      rw [instantiate_binder_shift0 v Δ b (.letBinding A w)] at hb'
      rw [instantiate_binder_shift0 v' Δ b' (.letBinding A w)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      have hcomm :=
        instantiate_instantiate 0 Δ.length w'
          (lift 0 Δ.length v') (Nat.zero_le _) b'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .zeta _ _ _ _ _ _ _ hA' hw' hb'
  | Γ, _, _, .iotaSpine _ w lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs, Δ, hΔ => by
      let k := Δ.length
      let sL := lift 0 Δ.length v
      let sR := lift 0 Δ.length v'
      have hf' := parRedArgs_instantiate_both hE hv hf Δ hΔ
      have ha' := parRedArgs_instantiate_both hE hv ha Δ hΔ
      have hsrc :
          instantiate k sL
            (recCall (.const w.recRef lsR) pre
              (foldApps (.const w.ctorRef lsC) fields)) =
          recCall (.const (instWitness k sR w).recRef lsR)
            (pre.map (instantiate k sL))
            (foldApps (.const (instWitness k sR w).ctorRef lsC)
              (fields.map (instantiate k sL))) := by
        rw [recCall_instantiate, instantiate, instantiate_foldApps_const]
        rfl
      rw [hsrc]
      have hpreLen' : (pre'.map (instantiate k sR)).length =
          (instWitness k sR w).preMajor.length := by
        simp only [instWitness, List.length_map]; exact hpreLen
      have hfieldsLen' : (fields'.map (instantiate k sR)).length =
          ((instWitness k sR w).ctorParams ++
            (instWitness k sR w).fields).length := by
        simp only [instWitness]
        exact map_ctorSpine_length (instantiate k sR) hfieldsLen
      have hlhs' : iotaLhsOf (instWitness k sR w) =
          recCall (.const (instWitness k sR w).recRef (instWitness k sR w).ls)
            (pre'.map (instantiate k sR))
            (foldApps (.const (instWitness k sR w).ctorRef (instWitness k sR w).lsC)
              (fields'.map (instantiate k sR))) := by
        have := congrArg (instantiate k sR) hlhs
        rw [← iotaLhsOf_instantiate, recCall_instantiate, instantiate,
          instantiate_foldApps_const] at this
        exact this
      rw [← iotaRhsOf_instantiate k sR w]
      exact .iotaSpine _ (instWitness k sR w) lsR lsC hlsR hlsC
        (pre.map (instantiate k sL)) (pre'.map (instantiate k sR))
        (fields.map (instantiate k sL)) (fields'.map (instantiate k sR))
        hf' ha' hpreLen' hfieldsLen' hlhs'

def parRedArgs_instantiate_both {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {v v' : Expr Nat}
    (hv : ParRed E n base v v') {Γ : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (Δ : LCtx)
    (hΔ : Γ = Δ ++ assumpPad 1 base) :
    ParRedArgs E n (instLCtx 0 v Δ ++ base)
      (xs.map (instantiate Δ.length (lift 0 Δ.length v)))
      (ys.map (instantiate Δ.length (lift 0 Δ.length v'))) :=
  match h with
  | ParRedArgs.nil Γ => ParRedArgs.nil _
  | ParRedArgs.cons hx t =>
      .cons (parRed_instantiate_both hE hv hx Δ hΔ)
        (parRedArgs_instantiate_both hE hv (h := t) Δ hΔ)
end

/-- Wrapper: body in a dummy assumption, both substitutions reduce. -/
def parRed_instantiate_both0 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {v v' : Expr Nat}
    (hv : ParRed E n Γ v v') {e e' : Expr Nat}
    (h : ParRed E n (dummyAssump :: Γ) e e') :
    ParRed E n Γ (instantiate0 v e) (instantiate0 v' e') := by
  have hΔ : dummyAssump :: Γ = ([] : LCtx) ++ assumpPad 1 Γ := by
    simp only [List.nil_append, assumpPad]
  have r := parRed_instantiate_both hE hv h [] hΔ
  simp only [instLCtx, List.nil_append, assumpPad, List.length_nil,
    lift_zero, instantiate0] at r
  exact r

/-- Beta/zeta/rhsArgs caller: body under an arbitrary assumption. -/
def parRed_instantiate_both_assump {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A v v' : Expr Nat}
    (hv : ParRed E n Γ v v') {e e' : Expr Nat}
    (h : ParRed E n (.assumption A :: Γ) e e') :
    ParRed E n Γ (instantiate0 v e) (instantiate0 v' e') :=
  parRed_instantiate_both0 hE hv (parRed_replace_assump h)

/-- Iota-vs-congr engine: pointwise ParRed of recursor prefix and
constructor fields lifts to ParRedArgs of `rhsArgs`. Telescope
cursors start as `ctorAfterParams` (refl) and step by
`parRed_instantiate_both_assump`. DirectRec IH is
`parRed_recCallField_congr` with `parRed_familyIdx` of the Π-domain.
`none` = `parRed_familyIdx` none (redex in a DirectRec domain). -/
def parRed_rhsArgs_congr {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} (rec : Expr Nat)
    {pre pre' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ pre pre')
    (nparams nMinors : Nat) :
    {fs fs' : List (Expr Nat)} →
    ParRedArgs E n Γ fs fs' →
    (ks : List RecKind) →
    {T T' : Expr Nat} →
    ParRed E n Γ T T' →
    Option (ParRedArgs E n Γ
      (rhsArgs rec pre nparams nMinors fs ks T)
      (rhsArgs rec pre' nparams nMinors fs' ks T'))
  | [], [], _, _ks, _T, _T', _hT => some (ParRedArgs.nil Γ)
  | [], _ :: _, hfs, _, _, _, _ => nomatch hfs
  | _ :: _, [], hfs, _, _, _, _ => nomatch hfs
  | _f :: fs, _f' :: fs', .cons hf hfs, ks, T, T', hT =>
      match ks, T with
      | [], _ =>
          match parRed_rhsArgs_congr hE rec hpre nparams nMinors hfs [] hT with
          | some ht => some (.cons hf ht)
          | none => none
      | .plain :: ks, .pi _ B => by
          have ⟨_A', B', heq, _hA, hB⟩ := parRed_pi hT rfl
          subst heq
          have hTnext := parRed_instantiate_both_assump hE hf hB
          match parRed_rhsArgs_congr hE rec hpre nparams nMinors hfs ks
              hTnext with
          | some ht => exact some (.cons hf ht)
          | none => exact none
      | .directRec :: ks, .pi A B => by
          have ⟨_A', B', heq, hA, hB⟩ := parRed_pi hT rfl
          subst heq
          match parRed_familyIdx nparams hA with
          | none => exact none
          | some hidx =>
              have hrc :=
                parRed_recCallField_congr (.refl _ rec) hpre
                  nparams nMinors hf hidx
              have hTnext := parRed_instantiate_both_assump hE hf hB
              match parRed_rhsArgs_congr hE rec hpre nparams nMinors hfs ks
                  hTnext with
              | some ht => exact some (.cons hf (.cons hrc ht))
              | none => exact none
      | _k :: _ks, .bvar _ => none
      | _k :: _ks, .sort _ => none
      | _k :: _ks, .const _ _ => none
      | _k :: _ks, .app _ _ => none
      | _k :: _ks, .lam _ _ => none
      | _k :: _ks, .letE _ _ _ => none
      | _k :: _ks, .lit _ => none

/-
Attempt 51 failing statement (iota-vs-congr, pairwise diamond route).

parRed_iotaRhs_congr : Option
  (ParRed (iotaRhsOf w) (foldApps minor' (rhsArgs rec pre' fields' ...)))

none when:
  (1) parRed_familyIdx none — ParRed of a DirectRec Π-domain fires a
      redex (delta/beta/iota). The two keys (parRed_foldApps_congr,
      parRed_instantiate_arg) plus instantiate_both construct forward
      congruence; they do not invert a redex in the field type.
  (2) remaining kinds with a non-Π telescope cursor (not a well-formed
      ctor telescope; hctorTel starts as a Π-tel).

Refl of the domain is some (parRed_familyIdx .refl). Total iota-vs-congr
is this Option with none uninhabited under hfamSpine. Not yet proved.
Do not grind; architect takes the file if the keys cannot close it.
-/

/-- Spine-arg congruence of `iotaRhsOf`. `none` is the iota-vs-congr
failing statement (DirectRec domain redex). -/
def parRed_iotaRhs_congr {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {w : IotaWitness E}
    {pre' : List (Expr Nat)} {fields' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ w.preMajor pre')
    (hfs : ParRedArgs E n Γ w.fields fields') :
    Option (Σ' (minor' : Expr Nat),
      (pre'[w.nparams + 1 + w.ctorIdx]? = some minor') ×'
      ParRed E n Γ (iotaRhsOf w)
        (foldApps minor'
          (rhsArgs (.const w.recRef w.ls) pre' w.nparams w.nMinors
            fields' w.kinds w.ctorAfterParams))) :=
  match parRedArgs_get hpre w.hminor with
  | ⟨minor', hmin, hminor⟩ =>
      match parRed_rhsArgs_congr hE (.const w.recRef w.ls) hpre
          w.nparams w.nMinors hfs w.kinds (.refl _ w.ctorAfterParams) with
      | none => none
      | some hargs =>
          some ⟨minor', hmin,
            parRed_foldApps_congr hargs hminor⟩

/-- Wrapper: term in a dummy assumption, instantiate at 0. -/
def parRed_instantiate_term0 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {s : Expr Nat} {e e' : Expr Nat}
    (h : ParRed E n (dummyAssump :: Γ) e e') :
    ParRed E n Γ (instantiate0 s e) (instantiate0 s e') := by
  have hΔ : dummyAssump :: Γ = ([] : LCtx) ++ assumpPad 1 Γ := by
    simp only [List.nil_append, assumpPad]
  have r := parRed_instantiate_term hE h (c := 0) s [] hΔ
  simp only [instLCtx, List.nil_append, assumpPad, List.length_nil,
    lift_zero, instantiate0] at r
  exact r

/-- Beta/zeta caller: body in an arbitrary assumption, dummy-irrel first. -/
def parRed_instantiate_term_assump {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A s : Expr Nat} {e e' : Expr Nat}
    (h : ParRed E n (.assumption A :: Γ) e e') :
    ParRed E n Γ (instantiate0 s e) (instantiate0 s e') :=
  parRed_instantiate_term0 hE (parRed_replace_assump h)

/-- Instantiate at index 1: hole is the second binder (the let, under
one extra assumption). -/
def parRed_instantiate_term1 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A s : Expr Nat} {e e' : Expr Nat}
    (h : ParRed E n (.assumption A :: dummyAssump :: Γ) e e') :
    ParRed E n (.assumption (instantiate0 s A) :: Γ)
      (instantiate 1 (lift 0 1 s) e)
      (instantiate 1 (lift 0 1 s) e') := by
  have hΔ :
      LocalDecl.assumption A :: dummyAssump :: Γ =
        [LocalDecl.assumption A] ++ assumpPad (0 + 1) Γ := by
    simp only [Nat.zero_add, assumpPad, List.cons_append, List.nil_append]
  have r := parRed_instantiate_term hE h (c := 0) s [.assumption A] hΔ
  simp only [instLCtx, List.length_nil, List.length_cons, Nat.add_zero,
    Nat.zero_add, lift_zero, instantiate0, assumpPad,
    List.nil_append] at r
  exact r

def parRedStar_instantiate_term0 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {s : Expr Nat} {e e' : Expr Nat} :
    ParRedStar E n (dummyAssump :: Γ) e e' →
    ParRedStar E n Γ (instantiate0 s e) (instantiate0 s e')
  | .refl _ _ => .refl _ _
  | .tail h hs =>
      .tail (parRed_instantiate_term0 hE h)
        (parRedStar_instantiate_term0 hE hs)

def parRedStar_instantiate_term_assump {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A s : Expr Nat} {e e' : Expr Nat}
    (h : ParRedStar E n (.assumption A :: Γ) e e') :
    ParRedStar E n Γ (instantiate0 s e) (instantiate0 s e') :=
  parRedStar_instantiate_term0 hE (parRedStar_replace_assump h)

def parRedStar_instantiate_term1 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A s : Expr Nat} {e e' : Expr Nat} :
    ParRedStar E n (.assumption A :: dummyAssump :: Γ) e e' →
    ParRedStar E n (.assumption (instantiate0 s A) :: Γ)
      (instantiate 1 (lift 0 1 s) e)
      (instantiate 1 (lift 0 1 s) e')
  | .refl _ _ => .refl _ _
  | .tail h hs =>
      .tail (parRed_instantiate_term1 hE h)
        (parRedStar_instantiate_term1 hE hs)

/-- Beta composition: arg reduces, then the body (in an assumption).
`instantiate0 arg' body' ⇒* instantiate0 v bodyDevel`. Do not trans
through `star_to_devel` of the redex (M-001). -/
def parRedStar_instantiate_beta {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A : Expr Nat}
    {arg arg' body body' : Expr Nat}
    (ha : ParRedStar E n Γ arg' arg)
    (hb : ParRedStar E n (.assumption A :: Γ) body' body) :
    ParRedStar E n Γ (instantiate0 arg' body') (instantiate0 arg body) :=
  parRedStar_trans
    (parRedStar_instantiate_arg hE (c := 0) ha body')
    (parRedStar_instantiate_term_assump hE hb)

theorem lookupValue_head_succ_irrel (d d' : LocalDecl) (Γ : LCtx) (i : Nat) :
    lookupValue (d :: Γ) (i + 1) = lookupValue (d' :: Γ) (i + 1) := by
  simp only [lookupValue_cons_succ]

theorem lookupValue_let_eq_dummy (A : Expr Nat) (w : Expr Nat)
    (base : LCtx) {i : Nat} (h : i ≠ 0) :
    lookupValue (.letBinding A w :: base) i =
      lookupValue (dummyAssump :: base) i := by
  cases i with
  | zero => exact (h rfl).elim
  | succ i' =>
      exact lookupValue_head_succ_irrel (.letBinding A w) dummyAssump base i'

theorem lookupValue_let_tail (Δ : LCtx) (A : Expr Nat) (w : Expr Nat)
    (base : LCtx) (i : Nat) (h : i ≠ Δ.length) :
    lookupValue (Δ ++ .letBinding A w :: base) i =
      lookupValue (Δ ++ dummyAssump :: base) i := by
  by_cases hlt : i < Δ.length
  · rw [lookupValue_append_left Δ (.letBinding A w :: base) i hlt,
      lookupValue_append_left Δ (dummyAssump :: base) i hlt]
  · have hiΔ : Δ.length ≤ i := Nat.le_of_not_lt hlt
    have ⟨j, hj⟩ := Nat.exists_eq_add_of_le hiΔ
    subst hj
    have hj0 : j ≠ 0 := by
      intro hjz; subst hjz
      exact h (by simp only [Nat.add_zero])
    rw [lookupValue_append_right Δ (.letBinding A w :: base) j,
      lookupValue_append_right Δ (dummyAssump :: base) j,
      lookupValue_let_eq_dummy A w base hj0]

theorem lookupValue_let_slot (Δ : LCtx) (A : Expr Nat) (w : Expr Nat)
    (base : LCtx) :
    lookupValue (Δ ++ .letBinding A w :: base) Δ.length =
      some (lift 0 (Δ.length + 1) w) := by
  have h := lookupValue_append_right Δ (.letBinding A w :: base) 0
  simp only [Nat.add_zero] at h
  rw [h]
  simp only [lookupValue, List.get?_cons_zero, Option.map_some']
  exact congrArg some (lift_zero_comp Δ.length 1 w)

mutual
/-- Let-ctx instantiate: drop let A w after substituting `w` on the
source and `w'` on the target (`hsubst : w ⇒ w'` in `base`). Dual of
`parRed_instantiate_both` whose hole is a dummy. -/
def parRed_instantiate_let {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {A w w' : Expr Nat}
    (hsubst : ParRed E n base w w') :
    {Γ : LCtx} → {e e' : Expr Nat} →
    ParRed E n Γ e e' →
    (Δ : LCtx) →
    (hΔ : Γ = Δ ++ (.letBinding A w :: base)) →
    ParRed E n (instLCtx 0 w Δ ++ base)
      (instantiate Δ.length (lift 0 Δ.length w) e)
      (instantiate Δ.length (lift 0 Δ.length w') e')
  | Γ, _, _, .refl _ e, Δ, _hΔ => by
      have hvw := parRed_weaken_lctx hE (instLCtx 0 w Δ) hsubst
      rw [instLCtx_length] at hvw
      exact parRed_instantiate_arg hE hvw (c := Δ.length) e
  | Γ, _, _, .sortEq _ l₁ l₂ h, Δ, _hΔ => by
      simp only [instantiate]
      exact .sortEq _ l₁ l₂ h
  | Γ, _, _, .consts _ r ls ls' h, Δ, _hΔ => by
      simp only [instantiate]
      exact .consts _ r ls ls' h
  | Γ, _, _, .lit _ t, Δ, _hΔ => by
      simp only [instantiate, natExpand_instantiate]
      exact .lit _ t
  | Γ, _, _, .bvarZeta _ i A0 v v' hlk hv, Δ, hΔ => by
      let k := Δ.length
      let s := lift 0 Δ.length w
      let s' := lift 0 Δ.length w'
      simp only [instantiate]
      have hlkV := lookupValue_of_get?_let hlk
      have hlkΔ : lookupValue (Δ ++ .letBinding A w :: base) i =
          some (lift 0 (i + 1) v) := by
        rw [← hΔ]; exact hlkV
      by_cases hic : i < k
      · have hne : i ≠ k := by omega
        have hnlt : ¬ k < i := by omega
        simp only [if_neg hne, if_neg hnlt]
        have hΔt : Γ.drop (i + 1) =
            Δ.drop (i + 1) ++ (.letBinding A w :: base) := by
          rw [hΔ, List.drop_append_of_le_length (Nat.succ_le_of_lt hic)]
        have hvI := parRed_instantiate_let hE hsubst hv (Δ.drop (i + 1)) hΔt
        have hdrop := inst_let_drop_lt w Δ base hic
        rw [← hdrop] at hvI
        have hmap := lookupValue_inst_source_lt 0 w Δ base i (by
          simp only [Nat.zero_add]; exact hic)
        have htail := lookupValue_let_tail Δ A w base i (by omega)
        rw [show dummyAssump :: base = assumpPad 1 base from rfl] at htail
        rw [htail] at hlkΔ
        simp only [Nat.zero_add] at hmap
        rw [hlkΔ, Option.map_some'] at hmap
        have hpad0 : assumpPad 0 base = base := assumpPad_zero base
        rw [hpad0] at hmap
        let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hlenD : (Δ.drop (i + 1)).length = Δ.length - (i + 1) :=
          length_drop_of_le Δ (Nat.succ_le_of_lt hic)
        have hsL :
            lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length w) = s := by
          rw [hlenD, lift_zero_comp]
          have : i + 1 + (Δ.length - (i + 1)) = Δ.length := by omega
          rw [this]
        have hj : i + 1 + (Δ.drop (i + 1)).length = k := by
          rw [hlenD]; omega
        have hsL' :
            lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length w') = s' := by
          rw [hlenD, lift_zero_comp]
          have : i + 1 + (Δ.length - (i + 1)) = Δ.length := by omega
          rw [this]
        have hcomm (e subst : Expr Nat)
            (hsEq : lift 0 (i + 1) (lift 0 (Δ.drop (i + 1)).length subst) =
              lift 0 Δ.length subst) :
            instantiate k (lift 0 Δ.length subst) (lift 0 (i + 1) e) =
              lift 0 (i + 1)
                (instantiate (Δ.drop (i + 1)).length
                  (lift 0 (Δ.drop (i + 1)).length subst) e) := by
          have h1 := lift_instantiate_high (i + 1) 0
            (Δ.drop (i + 1)).length
            (lift 0 (Δ.drop (i + 1)).length subst) (Nat.zero_le _) e
          rw [h1, hj, hsEq]
        have hstored : stored =
            instantiate (Δ.drop (i + 1)).length
              (lift 0 (Δ.drop (i + 1)).length w) v :=
          lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm v w hsL))
        rw [← hstored] at hvI
        exact (hcomm v' w' hsL') ▸
          .bvarZeta _ i A' stored _ hg' hvI
      · by_cases hi : i = k
        · subst hi
          have hslot := lookupValue_let_slot Δ A w base
          rw [hslot] at hlkΔ
          injection hlkΔ with hvEq
          have hvw : v = w := lift_zero_amount_inj (Δ.length + 1) (by
            simp only [k] at hvEq; exact hvEq.symm)
          simp only [if_pos (rfl : k = k)]
          have hid : instantiate k s' (lift 0 (k + 1) v') = lift 0 k v' :=
            instantiate_lift_cancel (k + 1) 0 k s' (Nat.zero_le k)
              (by omega) v'
          have htail : Γ.drop (k + 1) = base := by
            rw [hΔ]; exact drop_append_succ_let Δ A w base
          have hvb : ParRed E n base v v' := htail ▸ hv
          have hvw' := parRed_weaken_lctx hE (instLCtx 0 w Δ) hvb
          rw [instLCtx_length] at hvw'
          rw [hid]
          exact hvw ▸ hvw'
        · have hgt : k < i := by omega
          simp only [if_neg hi, if_pos hgt]
          have hmap := lookupValue_inst_source_gt 0 w Δ base i (by
            simp only [Nat.zero_add]; exact hgt)
          have htail := lookupValue_let_tail Δ A w base i (by omega)
          rw [show dummyAssump :: base = assumpPad 1 base from rfl] at htail
          rw [htail] at hlkΔ
          simp only [Nat.zero_add] at hmap
          rw [hlkΔ, Option.map_some'] at hmap
          have hpad0 : assumpPad 0 base = base := assumpPad_zero base
          rw [hpad0] at hmap
          let ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan :
              instantiate k s (lift 0 (i + 1) v) = lift 0 i v :=
            instantiate_lift_cancel (i + 1) 0 k s (Nat.zero_le k)
              (by omega) v
          have hi1 : (i - 1) + 1 = i := by omega
          have hstored : stored = v :=
            lift_zero_amount_inj i (by
              have heq' : instantiate k s (lift 0 (i + 1) v) =
                  lift 0 ((i - 1) + 1) stored := heq
              rw [hi1] at heq'
              exact heq'.symm.trans hcan)
          have htgt : lift 0 i v' =
              instantiate k s' (lift 0 (i + 1) v') :=
            (instantiate_lift_cancel (i + 1) 0 k s' (Nat.zero_le k)
              (by omega) v').symm
          have hdrop := inst_let_drop_gt A w Δ base hgt
          have hvI : ParRed E n
              ((instLCtx 0 w Δ ++ base).drop i) v v' := by
            rw [hdrop, ← hΔ]; exact hv
          have hbz :=
            ParRed.bvarZeta (instLCtx 0 w Δ ++ base) (i - 1)
              A' v v' (hstored ▸ hg') (by rw [hi1]; exact hvI)
          exact htgt ▸ (hi1 ▸ hbz)
  | Γ, _, _, .delta _ r ls m b hres hbody htr, Δ, hΔ => by
      simp only [instantiate]
      have hid' := (envWf_subst_inst hE r m hres).2 b hbody ls
        (lift 0 Δ.length w') Δ.length
      rw [hid']
      exact .delta _ r ls m b hres hbody htr
  | Γ, _, _, .app _ f f' x x' hf ha, Δ, hΔ => by
      simp only [instantiate]
      exact .app _ _ _ _ _
        (parRed_instantiate_let hE hsubst hf Δ hΔ)
        (parRed_instantiate_let hE hsubst ha Δ hΔ)
  | Γ, _, _, .lam _ B B' b b' hB hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption B :: Γ =
            (.assumption B :: Δ) ++ (.letBinding A w :: base) := by
        rw [hΔ, List.cons_append]
      have hB' := parRed_instantiate_let hE hsubst hB Δ hΔ
      have hb' := parRed_instantiate_let hE hsubst hb (.assumption B :: Δ) hΔb
      rw [instantiate_binder_shift0 w Δ b (.assumption B)] at hb'
      rw [instantiate_binder_shift0 w' Δ b' (.assumption B)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .lam _ _ _ _ _ hB' hb'
  | Γ, _, _, .pi _ B B' b b' hB hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption B :: Γ =
            (.assumption B :: Δ) ++ (.letBinding A w :: base) := by
        rw [hΔ, List.cons_append]
      have hB' := parRed_instantiate_let hE hsubst hB Δ hΔ
      have hb' := parRed_instantiate_let hE hsubst hb (.assumption B :: Δ) hΔb
      rw [instantiate_binder_shift0 w Δ b (.assumption B)] at hb'
      rw [instantiate_binder_shift0 w' Δ b' (.assumption B)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .pi _ _ _ _ _ hB' hb'
  | Γ, _, _, .letE _ B B' u u' b b' hB hu hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding B u :: Γ =
            (.letBinding B u :: Δ) ++ (.letBinding A w :: base) := by
        rw [hΔ, List.cons_append]
      have hB' := parRed_instantiate_let hE hsubst hB Δ hΔ
      have hu' := parRed_instantiate_let hE hsubst hu Δ hΔ
      have hb' := parRed_instantiate_let hE hsubst hb (.letBinding B u :: Δ) hΔb
      rw [instantiate_binder_shift0 w Δ b (.letBinding B u)] at hb'
      rw [instantiate_binder_shift0 w' Δ b' (.letBinding B u)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      exact .letE _ _ _ _ _ _ _ hB' hu' hb'
  | Γ, _, _, .beta _ B B' body body' arg arg' hB hb ha, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.assumption B :: Γ =
            (.assumption B :: Δ) ++ (.letBinding A w :: base) := by
        rw [hΔ, List.cons_append]
      have hB' := parRed_instantiate_let hE hsubst hB Δ hΔ
      have ha' := parRed_instantiate_let hE hsubst ha Δ hΔ
      have hb' := parRed_instantiate_let hE hsubst hb (.assumption B :: Δ) hΔb
      rw [instantiate_binder_shift0 w Δ body (.assumption B)] at hb'
      rw [instantiate_binder_shift0 w' Δ body' (.assumption B)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      have hcomm :=
        instantiate_instantiate 0 Δ.length arg'
          (lift 0 Δ.length w') (Nat.zero_le _) body'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .beta _ _ _ _ _ _ _ hB' hb' ha'
  | Γ, _, _, .zeta _ B B' u u' b b' hB hu hb, Δ, hΔ => by
      simp only [instantiate]
      have hΔb :
          LocalDecl.letBinding B u :: Γ =
            (.letBinding B u :: Δ) ++ (.letBinding A w :: base) := by
        rw [hΔ, List.cons_append]
      have hB' := parRed_instantiate_let hE hsubst hB Δ hΔ
      have hu' := parRed_instantiate_let hE hsubst hu Δ hΔ
      have hb' := parRed_instantiate_let hE hsubst hb (.letBinding B u :: Δ) hΔb
      rw [instantiate_binder_shift0 w Δ b (.letBinding B u)] at hb'
      rw [instantiate_binder_shift0 w' Δ b' (.letBinding B u)] at hb'
      simp only [instLCtx, List.cons_append, Nat.zero_add] at hb'
      have hcomm :=
        instantiate_instantiate 0 Δ.length u'
          (lift 0 Δ.length w') (Nat.zero_le _) b'
      simp only [instantiate0] at hcomm ⊢
      rw [hcomm]
      exact .zeta _ _ _ _ _ _ _ hB' hu' hb'
  | Γ, _, _, .iotaSpine _ wit lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs, Δ, hΔ => by
      let k := Δ.length
      let s := lift 0 Δ.length w
      let s' := lift 0 Δ.length w'
      have hf' := parRedArgs_instantiate_let hE hsubst hf Δ hΔ
      have ha' := parRedArgs_instantiate_let hE hsubst ha Δ hΔ
      have hsrc :
          instantiate k s
            (recCall (.const wit.recRef lsR) pre
              (foldApps (.const wit.ctorRef lsC) fields)) =
          recCall (.const (instWitness k s' wit).recRef lsR)
            (pre.map (instantiate k s))
            (foldApps (.const (instWitness k s' wit).ctorRef lsC)
              (fields.map (instantiate k s))) := by
        rw [recCall_instantiate, instantiate, instantiate_foldApps_const]
        rfl
      rw [hsrc]
      have hpreLen' : (pre'.map (instantiate k s')).length =
          (instWitness k s' wit).preMajor.length := by
        simp only [instWitness, List.length_map]; exact hpreLen
      have hfieldsLen' : (fields'.map (instantiate k s')).length =
          ((instWitness k s' wit).ctorParams ++
            (instWitness k s' wit).fields).length := by
        simp only [instWitness]
        exact map_ctorSpine_length (instantiate k s') hfieldsLen
      have hlhs' : iotaLhsOf (instWitness k s' wit) =
          recCall (.const (instWitness k s' wit).recRef (instWitness k s' wit).ls)
            (pre'.map (instantiate k s'))
            (foldApps (.const (instWitness k s' wit).ctorRef (instWitness k s' wit).lsC)
              (fields'.map (instantiate k s'))) := by
        have := congrArg (instantiate k s') hlhs
        rw [← iotaLhsOf_instantiate, recCall_instantiate, instantiate,
          instantiate_foldApps_const] at this
        exact this
      rw [← iotaRhsOf_instantiate k s' wit]
      exact .iotaSpine _ (instWitness k s' wit) lsR lsC hlsR hlsC
        (pre.map (instantiate k s)) (pre'.map (instantiate k s'))
        (fields.map (instantiate k s)) (fields'.map (instantiate k s'))
        hf' ha' hpreLen' hfieldsLen' hlhs'

def parRedArgs_instantiate_let {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {A w w' : Expr Nat}
    (hsubst : ParRed E n base w w')
    {Γ : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (Δ : LCtx)
    (hΔ : Γ = Δ ++ (.letBinding A w :: base)) :
    ParRedArgs E n (instLCtx 0 w Δ ++ base)
      (xs.map (instantiate Δ.length (lift 0 Δ.length w)))
      (ys.map (instantiate Δ.length (lift 0 Δ.length w'))) :=
  match h with
  | ParRedArgs.nil Γ => ParRedArgs.nil _
  | ParRedArgs.cons hx t =>
      .cons (parRed_instantiate_let hE hsubst hx Δ hΔ)
        (parRedArgs_instantiate_let hE hsubst (h := t) Δ hΔ)

def parRedStar_instantiate_let {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {base : LCtx} {A w : Expr Nat} :
    {Γ : LCtx} → {e e' : Expr Nat} →
    ParRedStar E n Γ e e' →
    (Δ : LCtx) →
    (hΔ : Γ = Δ ++ (.letBinding A w :: base)) →
    ParRedStar E n (instLCtx 0 w Δ ++ base)
      (instantiate Δ.length (lift 0 Δ.length w) e)
      (instantiate Δ.length (lift 0 Δ.length w) e')
  | _, _, _, .refl _ e, Δ, _hΔ => .refl _ _
  | _, _, _, .tail h hs, Δ, hΔ =>
      .tail (parRed_instantiate_let hE (.refl base w) h Δ hΔ)
        (parRedStar_instantiate_let hE hs Δ hΔ)
end

def parRed_instantiate_let0 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A w : Expr Nat} {e e' : Expr Nat}
    (h : ParRed E n (.letBinding A w :: Γ) e e') :
    ParRed E n Γ (instantiate0 w e) (instantiate0 w e') := by
  have hΔ : LocalDecl.letBinding A w :: Γ =
      ([] : LCtx) ++ (.letBinding A w :: Γ) := by
    simp only [List.nil_append]
  have r := parRed_instantiate_let hE (.refl Γ w) h [] hΔ
  simp only [instLCtx, List.nil_append, List.length_nil, lift_zero,
    instantiate0] at r
  exact r

/-- TML substitution: `v ⇒ v'` in Γ and `b ⇒ b'` under `let v`
gives `instantiate0 v b ⇒ instantiate0 v' b'` in Γ. Total.
`bvar 0` refl uses `hv`; `bvar 0` zeta uses the value premise;
`bvar (i+1)` shifts. -/
def parRed_instantiate_both_let {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A v v' : Expr Nat}
    (hv : ParRed E n Γ v v') {e e' : Expr Nat}
    (h : ParRed E n (.letBinding A v :: Γ) e e') :
    ParRed E n Γ (instantiate0 v e) (instantiate0 v' e') := by
  have hΔ : LocalDecl.letBinding A v :: Γ =
      ([] : LCtx) ++ (.letBinding A v :: Γ) := by
    simp only [List.nil_append]
  have r := parRed_instantiate_let hE hv h [] hΔ
  simp only [instLCtx, List.nil_append, List.length_nil, lift_zero,
    instantiate0] at r
  exact r

def parRedStar_instantiate_let0 {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A w : Expr Nat} {e e' : Expr Nat} :
    ParRedStar E n (.letBinding A w :: Γ) e e' →
    ParRedStar E n Γ (instantiate0 w e) (instantiate0 w e')
  | .refl _ _ => .refl _ _
  | .tail h hs =>
      .tail (parRed_instantiate_let0 hE h)
        (parRedStar_instantiate_let0 hE hs)

/-- Zeta composition: value reduces, then the body (in a let). -/
def parRedStar_instantiate_zeta {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A : Expr Nat}
    {v v' b b' : Expr Nat}
    (hv : ParRedStar E n Γ v' v)
    (hb : ParRedStar E n (.letBinding A v :: Γ) b' b) :
    ParRedStar E n Γ (instantiate0 v' b') (instantiate0 v b) :=
  parRedStar_trans
    (parRedStar_instantiate_arg hE (c := 0) hv b')
    (parRedStar_instantiate_let0 hE hb)

/-- Saturated-fuel fact: every member's prefix rank is `< fuel`. -/
theorem envWf_member_rank_lt {E : ResolvedEnv} {n fuel : Nat}
    (hE : EnvWf E n) {r : Nat} {m : CheckedMember}
    (hmem : E.members r = some m)
    (hfuel : envWf_rank hE ≤ fuel) :
    envWf_rank (envWf_of_member hE hmem).2.1 < fuel :=
  Nat.lt_of_lt_of_le (envWf_of_member hE hmem).2.2.2 hfuel

/-- Indices of `ParRed` are unconstrained here, so constructor match
does not hit the iota-rhs/sortEq dependent-elim wall. `PLift` because
`Option` is Type-valued and `Eq` is Prop. -/
def parRed_eq_of_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} : ParRed E n Γ a b → Option (PLift (a = b))
  | .refl _ _ => some ⟨rfl⟩
  | .sortEq .. => none
  | .consts .. => none
  | .bvarZeta .. => none
  | .delta .. => none
  | .app .. => none
  | .beta .. => none
  | .lam .. => none
  | .pi .. => none
  | .letE .. => none
  | .zeta .. => none
  | .iotaSpine .. => none
  | .lit .. => none

def parRedArgs_eq_of_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) :
    Option (PLift (xs = ys)) :=
  match h with
  | ParRedArgs.nil _ => some ⟨rfl⟩
  | ParRedArgs.cons hx t =>
      match parRed_eq_of_refl hx, parRedArgs_eq_of_refl t with
      | some ⟨e1⟩, some ⟨e2⟩ => some ⟨e1 ▸ e2 ▸ rfl⟩
      | _, _ => none

def parRedStar_eq_of_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} : ParRedStar E n Γ a b → Option (PLift (a = b))
  | .refl _ _ => some ⟨rfl⟩
  | .tail _ _ => none

end Rcic.Declarative
