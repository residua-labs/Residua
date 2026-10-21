/-
RCIC ParRed, piece 2 of 7: fragment characterizations, the
iota-vs-app engine, the attempt-51 pairwise route, and `unlift`.

`parRedStar_sort_eq` / `parRed_pi_inj` / `parRedStar_pi_inj` (the
F-05b fragment forms of SortConvChar / PiConvInj), the pointwise
`ParRedArgs` calculus (`take`/`drop`/`append`/`snoc`/`ctor_split`),
`parRed_foldApps_congr`, `parRed_iota_vs_app`, `parRed_familyIdx`,
and the `unlift` / `etaContract` inverse of `lift cutoff 1`.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.
-/
import rcic.RcicParRedCore

namespace Rcic.Declarative

/-! ### Fragment characterizations (attempt 3). Conv-level SortConvChar /
PiConvInj remain the named obligations. -/

/-- Multi-step parallel reduction of the fragment.
(`ParRedStar` is a separate inductive; iotaSpine no longer carries a
star field.) -/
def parRedStar_sort {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRedStar E n Γ a e → {u : Level} → a = .sort u →
    Σ' (v : Level), (e = .sort v) ×' eqN u v
  | _, _, _, .refl _ a, u, heq => by
      subst heq
      exact ⟨u, rfl, eqN_refl u⟩
  | _, _, _, .tail h hs, u, heq =>
      let ⟨w, hw, q⟩ := parRed_sort h heq
      let ⟨v, hv, q2⟩ := parRedStar_sort hs hw
      ⟨v, hv, eqN_trans q q2⟩

/-- Fragment SortConvChar: star-join of sorts is =ₙ. -/
theorem parRedStar_sort_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u v : Level} (h : ParRedStar E n Γ (.sort u) (.sort v)) : eqN u v :=
  let ⟨_w, hsort, heqn⟩ := parRedStar_sort h rfl
  match hsort with
  | Eq.refl _ => heqn

def parRedStar_trans {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b c : Expr Nat} →
    ParRedStar E n Γ a b → ParRedStar E n Γ b c → ParRedStar E n Γ a c
  | _, _, _, _, .refl _ _, hs => hs
  | _, _, _, _, .tail h ht, hs => .tail h (parRedStar_trans ht hs)

def parRedStar_one {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat}
    (h : ParRed E n Γ a b) : ParRedStar E n Γ a b :=
  .tail h (.refl _ _)

def parRedStar_assump_to_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v : Expr Nat} {a b : Expr Nat} :
    ParRedStar E n (.assumption A :: Γ) a b →
    ParRedStar E n (.letBinding A' v :: Γ) a b :=
  parRedStar_lookup_mono (lookupValue_assump_subset_let A A' v Γ)

def parRedStar_lift_append {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    (pre : LCtx) → {Γ : LCtx} → {a b : Expr Nat} →
    ParRedStar E n Γ a b →
    ParRedStar E n (pre ++ Γ) (lift 0 pre.length a) (lift 0 pre.length b)
  | [], _, _, _, hs => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact hs
  | d :: pre, Γ, a, b, hs => by
      have ih := parRedStar_lift_append hE pre hs
      have w := parRedStar_weaken d hE (c := 0) ih
      simp only [insertAt_zero] at w
      have hA :
          lift 0 1 (lift 0 pre.length a) = lift 0 (pre.length + 1) a :=
        lift_lift_merge 1 pre.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) a
      have hB :
          lift 0 1 (lift 0 pre.length b) = lift 0 (pre.length + 1) b :=
        lift_lift_merge 1 pre.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) b
      rw [hA, hB] at w
      simp only [List.length_cons, List.cons_append, Nat.succ_eq_add_one]
      exact w

def parRedStar_replace_assump {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {a b : Expr Nat} :
    ParRedStar E n (.assumption A :: Γ) a b →
    ParRedStar E n (.assumption A' :: Γ) a b :=
  parRedStar_ctx_lookup (lookupValue_assumption_irrel A A' Γ)

/-- A pi star-reduces only to a pi (congruence). -/
def parRedStar_pi {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRedStar E n Γ a e → {A B : Expr Nat} → a = .pi A B →
    Σ' (A' B' : Expr Nat),
      (e = .pi A' B') ×'
      ParRedStar E n Γ A A' ×'
      ParRedStar E n (LocalDecl.assumption A :: Γ) B B'
  | _, _, _, .refl _ a, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, .refl _ _, .refl _ _⟩
  | _, _, _, .tail h hs, A, B, heq =>
      let ⟨A1, B1, he1, hA, hB⟩ := parRed_pi h heq
      let ⟨A', B', he', hAs, hBs⟩ := parRedStar_pi hs he1
      ⟨A', B', he',
        .tail hA hAs,
        .tail hB (parRedStar_replace_assump (A := A1) (A' := A) hBs)⟩

/-- Π-injectivity of ParRedStar (stronger than `parRed_pi_inj`). -/
def parRedStar_pi_inj {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B A' B' : Expr Nat}
    (h : ParRedStar E n Γ (.pi A B) (.pi A' B')) :
    ParRedStar E n Γ A A' ×'
      ParRedStar E n (LocalDecl.assumption A :: Γ) B B' :=
  let ⟨_A1, _B1, heq, hA, hB⟩ := parRedStar_pi h rfl
  match heq with
  | Eq.refl _ => ⟨hA, hB⟩

/-- Diamond of ParRed at a sort (no iota-vs-app: a sort is not an iota lhs). -/
def parRed_diamond_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u : Level} {b c : Expr Nat}
    (h1 : ParRed E n Γ (.sort u) b) (h2 : ParRed E n Γ (.sort u) c) :
    Σ' (d : Expr Nat), ParRed E n Γ b d ×' ParRed E n Γ c d := by
  have ⟨v1, e1, q1⟩ := parRed_sort h1 rfl
  have ⟨v2, e2, q2⟩ := parRed_sort h2 rfl
  subst e1; subst e2
  exact ⟨.sort v1, .refl _ _,
    .sortEq _ v2 v1 (eqN_trans (eqN_symm q2) q1)⟩

/-- A lambda parallel-reduces only to a lambda (congruence). -/
def parRed_lam {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRed E n Γ a e → {A b : Expr Nat} → a = .lam A b →
    Σ' (A' b' : Expr Nat),
      (e = .lam A' b') ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) b b'
  | _, _, _, .refl _ a, A, b, heq => by
      subst heq
      exact ⟨A, b, rfl, .refl _ _, .refl _ _⟩
  | _, _, _, .sortEq _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .lam _ A₀ A₁ b₀ b₁ hA hb, A, b, heq => by
      injection heq with hAeq hbeq
      subst hAeq
      subst hbeq
      exact ⟨A₁, b₁, rfl, hA, hb⟩
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, b, heq =>
      (foldApps_const_ne_lam
        (pre ++ [foldApps (.const w.ctorRef lsC) fields]) heq).elim
  | _, _, _, .lit _ _, _, _, heq => nomatch heq

/-- A lambda star-reduces only to a lambda (congruence). -/
def parRedStar_lam {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRedStar E n Γ a e → {A b : Expr Nat} → a = .lam A b →
    Σ' (A' b' : Expr Nat),
      (e = .lam A' b') ×'
      ParRedStar E n Γ A A' ×'
      ParRedStar E n (LocalDecl.assumption A :: Γ) b b'
  | _, _, _, .refl _ a, A, b, heq => by
      subst heq
      exact ⟨A, b, rfl, .refl _ _, .refl _ _⟩
  | _, _, _, .tail h hs, A, b, heq =>
      let ⟨A1, b1, he1, hA, hb⟩ := parRed_lam h heq
      let ⟨A', b', he', hAs, hbs⟩ := parRedStar_lam hs he1
      ⟨A', b', he',
        .tail hA hAs,
        .tail hb (parRedStar_replace_assump (A := A1) (A' := A) hbs)⟩

def parRedStar_lam_inj {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b A' b' : Expr Nat}
    (h : ParRedStar E n Γ (.lam A b) (.lam A' b')) :
    ParRedStar E n Γ A A' ×'
      ParRedStar E n (LocalDecl.assumption A :: Γ) b b' :=
  let ⟨_A1, _b1, heq, hA, hb⟩ := parRedStar_lam h rfl
  match heq with
  | Eq.refl _ => ⟨hA, hb⟩

/-- Argument-only instantiate congruence: `e` is fixed, the replacement
parallel-reduces. Beta's "arg reduces, body stays" side. Under binders
the replacement is weakened (`parRed_weaken`); no LitLift. -/
def parRed_instantiate_arg {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {v v' : Expr Nat}
    (hv : ParRed E n Γ v v') :
    {c : Nat} → (e : Expr Nat) →
    ParRed E n Γ (instantiate c v e) (instantiate c v' e)
  | c, .bvar i => by
      simp only [instantiate]
      by_cases hi : i = c
      · simp only [if_pos hi]
        exact hv
      · simp only [if_neg hi]
        split
        · exact .refl _ _
        · exact .refl _ _
  | c, .sort l => by
      simp only [instantiate]
      exact .refl _ _
  | c, .const r ls => by
      simp only [instantiate]
      exact .refl _ _
  | c, .app f x => by
      simp only [instantiate]
      exact .app _ _ _ _ _
        (parRed_instantiate_arg hE hv f) (parRed_instantiate_arg hE hv x)
  | c, .lam A b => by
      simp only [instantiate]
      let hA := parRed_instantiate_arg hE hv (c := c) A
      let Ainst := instantiate c v A
      exact .lam _ _ _ _ _ hA
        (parRed_instantiate_arg hE
          (parRed_weaken (.assumption Ainst) hE (c := 0) hv) (c := c + 1) b)
  | c, .pi A b => by
      simp only [instantiate]
      let hA := parRed_instantiate_arg hE hv (c := c) A
      let Ainst := instantiate c v A
      exact .pi _ _ _ _ _ hA
        (parRed_instantiate_arg hE
          (parRed_weaken (.assumption Ainst) hE (c := 0) hv) (c := c + 1) b)
  | c, .letE A w b => by
      simp only [instantiate]
      let hA := parRed_instantiate_arg hE hv (c := c) A
      let hw := parRed_instantiate_arg hE hv (c := c) w
      let Ainst := instantiate c v A
      let winst := instantiate c v w
      exact .letE _ _ _ _ _ _ _ hA hw
        (parRed_instantiate_arg hE
          (parRed_weaken (.letBinding Ainst winst) hE (c := 0) hv) (c := c + 1) b)
  | c, .lit t => by
      simp only [instantiate]
      exact .refl _ _

/-! ### Pointwise ParRed of argument lists (iota-vs-app engine).
`ParRedArgs` is the mutual inductive next to `ParRed`. -/

theorem parRedArgs_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) :
    xs.length = ys.length :=
  match h with
  | ParRedArgs.nil _ => rfl
  | ParRedArgs.cons _ t => congrArg Nat.succ (parRedArgs_length (h := t))

def parRedArgs_get {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys)
    {i : Nat} {x : Expr Nat} (hg : xs[i]? = some x) :
    Σ' (y : Expr Nat), (ys[i]? = some y) ×' ParRed E n Γ x y :=
  match h with
  | ParRedArgs.nil _ => by
      cases i <;> exact Option.noConfusion hg
  | ParRedArgs.cons (x := x) (y := y) hx _hs => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hg
          injection hg with hxy
          subst hxy
          exact ⟨y, List.getElem?_cons_zero, hx⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at hg ⊢
          exact parRedArgs_get (h := _hs) hg

/-- Append one pointwise reduct. -/
def parRedArgs_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} {x y : Expr Nat}
    (h : ParRedArgs E n Γ xs ys) (hx : ParRed E n Γ x y) :
    ParRedArgs E n Γ (xs ++ [x]) (ys ++ [y]) :=
  match h with
  | ParRedArgs.nil Γ => .cons hx (ParRedArgs.nil Γ)
  | ParRedArgs.cons h hs => .cons h (parRedArgs_snoc (h := hs) hx)

/-- Congruence: pointwise ParRed of a spine is ParRed of `foldApps`. -/
def parRed_foldApps_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs xs') (hf : ParRed E n Γ f f') :
    ParRed E n Γ (foldApps f xs) (foldApps f' xs') :=
  match h with
  | ParRedArgs.nil _ => hf
  | ParRedArgs.cons (xs := xs) (ys := ys) hx hxs =>
      parRed_foldApps_congr (xs := xs) (xs' := ys) hxs (.app _ _ _ _ _ hf hx)

/-- Recursor-call congruence: prefix + major, same head const. -/
def parRed_recCall_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level}
    {pre pre' : List (Expr Nat)} {maj maj' : Expr Nat}
    (hp : ParRedArgs E n Γ pre pre') (hm : ParRed E n Γ maj maj') :
    ParRed E n Γ
      (recCall (.const r ls) pre maj)
      (recCall (.const r ls) pre' maj') := by
  simp only [recCall]
  exact parRed_foldApps_congr (parRedArgs_snoc hp hm) (.refl _ _)

def list_snoc_of_ne_nil {α : Type} :
    (xs : List α) → xs ≠ [] →
    Σ' (ys : List α) (x : α), xs = ys ++ [x]
  | [], h => (h rfl).elim
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: xs, _ =>
      let ⟨ys, z, hz⟩ := list_snoc_of_ne_nil (y :: xs) (by intro n; cases n)
      ⟨x :: ys, z, by simp only [List.cons_append, hz]⟩

def foldApps_cons_is_app (f x : Expr Nat) :
    (xs : List (Expr Nat)) →
    Σ' (g a : Expr Nat), foldApps f (x :: xs) = .app g a
  | [] => ⟨f, x, rfl⟩
  | y :: ys =>
      let ⟨g, a, hg⟩ := foldApps_cons_is_app (.app f x) y ys
      ⟨g, a, hg⟩

theorem iotaLhsOf_app {E : ResolvedEnv} (w : IotaWitness E) :
    iotaLhsOf w =
      .app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w) :=
  foldApps_snoc (.const w.recRef w.ls) (ctorMajor w) w.preMajor

/-- Const-headed spine: ParRed is pointwise congruence, or a redex
fired (delta on a bare const / iota / beta on a prefix). Recursor
and constructor heads are rigid, so the iota-lhs use is the left
summand. -/
def parRed_foldApps_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} :
    {e t : Expr Nat} →
    ParRed E n Γ e t →
    (xs : List (Expr Nat)) →
    e = foldApps (.const r ls) xs →
    Option
      ((ls' : List Level) ×'
        (xs' : List (Expr Nat)) ×'
          (t = foldApps (.const r ls') xs') ×'
          eqNList ls ls' ×'
          ParRedArgs E n Γ xs xs')
  | _, _, .refl _ e, xs, heq => by
      subst heq
      exact some ⟨ls, xs, rfl, eqNList_refl ls, parRedArgs_refl xs⟩
  | _, _, .sortEq _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .consts _ r0 ls0 ls' h, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact some ⟨ls', [], rfl, h, ParRedArgs.nil Γ⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .delta .., xs, heq => by
      cases xs with
      | nil => exact none
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .app _ f0 f0' a0 a0' hf ha, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by intro n; cases n
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 ha0
          subst hf0
          subst ha0
          match parRed_foldApps_const hf ys rfl with
          | some ⟨ls', ys', hfeq, hls, hys⟩ =>
              subst hfeq
              have hargs : ParRedArgs E n Γ (z :: zs) (ys' ++ [a0']) := by
                rw [hsplit]
                exact parRedArgs_snoc hys ha
              exact some ⟨ls', ys' ++ [a0'],
                (foldApps_snoc (.const r ls') a0' ys').symm, hls, hargs⟩
          | none => exact none
  | _, _, .beta _ _ _ _ _ _ _ _ _ _, _xs, _heq =>
      none
  | _, _, .lam _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .letE _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .zeta _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _xs, _heq =>
      none
  | _, _, .lit _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq

/-- TML wrapper: `ParRedArgs` + reduced-spine witness `w2` is
`iotaSpine`. Join of iota-vs-app is this constructor on the app
side (refl args of the remaining spine) plus `congr_total` on the
iota side. -/
def parRed_iota_vs_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {w : IotaWitness E} {lsR lsC : List Level}
    (hlsR : eqNList w.ls lsR) (hlsC : eqNList w.lsC lsC)
    {pre pre' fields fields' : List (Expr Nat)}
    (hf : ParRedArgs E n Γ pre pre')
    (ha : ParRedArgs E n Γ fields fields')
    (hpreLen : pre'.length = w.preMajor.length)
    (hfieldsLen : fields'.length =
        (w.ctorParams ++ w.fields).length)
    (hlhs : iotaLhsOf w =
        recCall (.const w.recRef w.ls) pre'
          (foldApps (.const w.ctorRef w.lsC) fields')) :
    ParRed E n Γ
      (recCall (.const w.recRef lsR) pre
        (foldApps (.const w.ctorRef lsC) fields))
      (iotaRhsOf w) :=
  .iotaSpine Γ w lsR lsC hlsR hlsC pre pre' fields fields'
    hf ha hpreLen hfieldsLen hlhs

/-- Inject `hlhs` of iotaSpine: the reduced-spine witness is the
recursor/ctor application of `pre'`/`fields'`. -/
theorem appsSpine_recCall (r : Nat) (ls : List Level)
    (pre : List (Expr Nat)) (major : Expr Nat) :
    appsSpine (recCall (.const r ls) pre major) =
      (.const r ls, pre ++ [major]) := by
  simp only [recCall]
  rw [appsSpine_foldApps, appsSpine_const, List.nil_append]

theorem iotaLhsOf_recCall_inj_full {E : ResolvedEnv} {w : IotaWitness E}
    {r c : Nat} {lsR lsC : List Level} {pre' fields' : List (Expr Nat)}
    (hlhs : iotaLhsOf w =
        recCall (.const r lsR) pre'
          (foldApps (.const c lsC) fields')) :
    w.recRef = r ∧ w.ls = lsR ∧ w.preMajor = pre' ∧
      w.ctorRef = c ∧ w.lsC = lsC ∧
      w.ctorParams ++ w.fields = fields' := by
  have hs := congrArg appsSpine hlhs
  simp only [iotaLhsOf, recCall] at hs
  rw [appsSpine_foldApps, appsSpine_const, List.nil_append,
    appsSpine_foldApps, appsSpine_const, List.nil_append] at hs
  injection hs with hhead hsp
  injection hhead with href hls
  have ⟨hpre, hmaj⟩ := list_snoc_inj hsp
  have hs2 := congrArg appsSpine hmaj
  simp only [ctorMajor] at hs2
  rw [appsSpine_foldApps, appsSpine_const, List.nil_append,
    appsSpine_foldApps, appsSpine_const, List.nil_append] at hs2
  injection hs2 with hhead2 hfields
  injection hhead2 with hctor hlsC
  exact ⟨href, hls, hpre, hctor, hlsC, hfields⟩

theorem iotaLhsOf_recCall_inj {E : ResolvedEnv} {w : IotaWitness E}
    {lsR lsC : List Level} {pre' fields' : List (Expr Nat)}
    (hlhs : iotaLhsOf w =
        recCall (.const w.recRef lsR) pre'
          (foldApps (.const w.ctorRef lsC) fields')) :
    w.ls = lsR ∧ w.preMajor = pre' ∧
      w.lsC = lsC ∧
      w.ctorParams ++ w.fields = fields' :=
  let ⟨_, hls, hpre, _, hlsC, hfields⟩ := iotaLhsOf_recCall_inj_full hlhs
  ⟨hls, hpre, hlsC, hfields⟩

/-- Env-determined fields of two witnesses with the same rec/ctor
refs and the same prefix length. Does not identify `ls`,
`preMajor`, `fields`, or `ctorAfterParams`. Port of the
`iotaDet` member/peel/family fragment. -/
theorem iotaWitness_env_of_same_refs {E : ResolvedEnv}
    {w1 w2 : IotaWitness E}
    (hrec : w1.recRef = w2.recRef)
    (hctor : w1.ctorRef = w2.ctorRef)
    (hlen : w1.preMajor.length = w2.preMajor.length) :
    w1.recMember = w2.recMember ∧
      w1.ctorMember = w2.ctorMember ∧
      w1.familyRef = w2.familyRef ∧
      w1.nMinors = w2.nMinors ∧
      w1.nindices = w2.nindices ∧
      w1.nparams = w2.nparams ∧
      w1.ctorIdx = w2.ctorIdx ∧
      w1.kinds = w2.kinds := by
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
    have eq : some (w1.ctorDoms, w1.ctorResult) =
        some (w2.ctorDoms, w2.ctorResult) := a.symm.trans b
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
      rw [L2, ← hlen, ← hmemr] at b
      have eq : some (w1.recDoms, w1.recBody) =
          some (w2.recDoms, w2.recBody) := a.symm.trans b
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
      have := hnmin
      have := hnidx
      have := hlen
      omega
    have hidx : w1.ctorIdx = w2.ctorIdx := by
      have a := w1.hctorIdx
      have b := w2.hctorIdx
      rw [← hctor, ← hfam] at b
      have := a.symm.trans b
      omega
    have hk : w1.kinds = w2.kinds := by
      have a := w1.hkinds
      have b := w2.hkinds
      rw [← hfam, ← hpeelEq.1, ← hnpar] at b
      have eq : some w1.kinds = some w2.kinds := a.symm.trans b
      injection eq
    exact ⟨hmemr, hmemc, hfam, hnmin, hnidx, hnpar, hidx, hk⟩
  · exact Bool.noConfusion hf1

/-! ### Pairwise diamond route (attempt 51).

Takahashi `develWf` is a conservative partial function (fuel/cert
fallback). Architect ruling: abandon the function; prove
ParRed × ParRed diamond (Tait–Martin-Löf). No function ⇒ no
adequacy. Keys: `iotaWitness_deterministic`, sealed
`parRed_foldApps_congr` + `parRed_instantiate_arg`. -/

def parRedArgs_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs xs' ys ys' : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs xs') (hy : ParRedArgs E n Γ ys ys') :
    ParRedArgs E n Γ (xs ++ ys) (xs' ++ ys') :=
  match h with
  | ParRedArgs.nil _ => hy
  | ParRedArgs.cons hx hxs => .cons hx (parRedArgs_append (h := hxs) hy)

def parRedArgs_take {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) (k : Nat) :
    ParRedArgs E n Γ (xs.take k) (ys.take k) :=
  match xs, ys, h, k with
  | [], [], ParRedArgs.nil Γ, k =>
      match k with
      | 0 => ParRedArgs.nil Γ
      | _ + 1 => ParRedArgs.nil Γ
  | _x :: _, _y :: _, ParRedArgs.cons hx hs, 0 =>
      ParRedArgs.nil Γ
  | _x :: xs, _y :: ys, ParRedArgs.cons hx hs, k + 1 =>
      .cons hx (parRedArgs_take (xs := xs) (ys := ys) hs k)

def parRedArgs_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) (k : Nat) :
    ParRedArgs E n Γ (xs.drop k) (ys.drop k) :=
  match xs, ys, h, k with
  | _, _, h, 0 => h
  | [], [], ParRedArgs.nil Γ, _k + 1 =>
      ParRedArgs.nil Γ
  | _x :: xs, _y :: ys, ParRedArgs.cons _ hs, k + 1 =>
      parRedArgs_drop (xs := xs) (ys := ys) hs k

/-- KEY A: ctorParams is a free copy, not `preMajor.take nparams`.
Split a ParRedArgs of `ctorParams ++ fields` into the two pieces. -/
def parRedArgs_ctor_split {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ctorParams fields fields' ys : List (Expr Nat)} {nparams : Nat}
    (hlenC : ctorParams.length = nparams)
    (hfs : ctorParams ++ fields = fields')
    (ha : ParRedArgs E n Γ fields' ys) :
    ParRedArgs E n Γ fields (ys.drop nparams) ×'
      ParRedArgs E n Γ ctorParams (ys.take nparams) :=
  have hd := parRedArgs_drop ha nparams
  have hd' : ParRedArgs E n Γ
      ((ctorParams ++ fields).drop nparams) (ys.drop nparams) :=
    hfs ▸ hd
  have ht := parRedArgs_take ha nparams
  have ht' : ParRedArgs E n Γ
      ((ctorParams ++ fields).take nparams) (ys.take nparams) :=
    hfs ▸ ht
  ⟨List.drop_left' (l₁ := ctorParams) (l₂ := fields) hlenC ▸ hd',
    List.take_left' (l₁ := ctorParams) (l₂ := fields) hlenC ▸ ht'⟩

/-- Pointwise instantiate-arg on a list. -/
def parRedArgs_instantiate {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {v v' : Expr Nat}
    (hv : ParRed E n Γ v v') (c : Nat) :
    (xs : List (Expr Nat)) →
    ParRedArgs E n Γ
      (xs.map (instantiate c v)) (xs.map (instantiate c v'))
  | [] => ParRedArgs.nil Γ
  | x :: xs =>
      .cons (parRed_instantiate_arg hE hv (c := c) x)
        (parRedArgs_instantiate hE hv c xs)

def parRed_recPrefix {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (nparams nMinors : Nat) {pre pre' : List (Expr Nat)}
    (h : ParRedArgs E n Γ pre pre') :
    ParRedArgs E n Γ
      (recPrefix pre nparams nMinors)
      (recPrefix pre' nparams nMinors) :=
  parRedArgs_take h (nparams + 1 + nMinors)

/-- `familyIdx` of a const-headed type under instantiate-arg.
Sealed `familyIdx_instantiate_const` + `parRed_instantiate_arg`. -/
def parRed_familyIdx_instantiate {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {f f' : Expr Nat}
    (hf : ParRed E n Γ f f') (c nparams : Nat) {A : Expr Nat}
    (hsc : spineHeadConst A = true) :
    ParRedArgs E n Γ
      (familyIdx nparams (instantiate c f A))
      (familyIdx nparams (instantiate c f' A)) := by
  have hmap : familyIdx nparams (instantiate c f A) =
      (familyIdx nparams A).map (instantiate c f) := by
    simp only [spineHeadConst] at hsc
    cases hsp : (appsSpine A).1 with
    | const r ls =>
        exact familyIdx_instantiate_const c f nparams (by rw [hsp])
    | bvar _ => simp only [hsp] at hsc; nomatch hsc
    | sort _ => simp only [hsp] at hsc; nomatch hsc
    | app _ _ => simp only [hsp] at hsc; nomatch hsc
    | lam _ _ => simp only [hsp] at hsc; nomatch hsc
    | pi _ _ => simp only [hsp] at hsc; nomatch hsc
    | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
    | lit _ => simp only [hsp] at hsc; nomatch hsc
  have hmap' : familyIdx nparams (instantiate c f' A) =
      (familyIdx nparams A).map (instantiate c f') := by
    simp only [spineHeadConst] at hsc
    cases hsp : (appsSpine A).1 with
    | const r ls =>
        exact familyIdx_instantiate_const c f' nparams (by rw [hsp])
    | bvar _ => simp only [hsp] at hsc; nomatch hsc
    | sort _ => simp only [hsp] at hsc; nomatch hsc
    | app _ _ => simp only [hsp] at hsc; nomatch hsc
    | lam _ _ => simp only [hsp] at hsc; nomatch hsc
    | pi _ _ => simp only [hsp] at hsc; nomatch hsc
    | letE _ _ _ => simp only [hsp] at hsc; nomatch hsc
    | lit _ => simp only [hsp] at hsc; nomatch hsc
  rw [hmap, hmap']
  exact parRedArgs_instantiate hE hf c (familyIdx nparams A)

/-- Forward congruence of `recCallField`. `hidx` is `familyIdx` of the
two DirectRec domains (refl when the telescope cursor is shared;
`parRed_familyIdx_instantiate` after one instantiate-arg). -/
def parRed_recCallField_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {rec rec' : Expr Nat}
    (hrec : ParRed E n Γ rec rec')
    {pre pre' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ pre pre')
    (nparams nMinors : Nat)
    {f f' : Expr Nat}
    (hf : ParRed E n Γ f f')
    {A A' : Expr Nat}
    (hidx : ParRedArgs E n Γ
      (familyIdx nparams A) (familyIdx nparams A')) :
    ParRed E n Γ
      (recCallField rec pre nparams nMinors f A)
      (recCallField rec' pre' nparams nMinors f' A') :=
  parRed_foldApps_congr
    (parRedArgs_append
      (parRedArgs_append (parRed_recPrefix nparams nMinors hpre) hidx)
      (.cons hf (ParRedArgs.nil Γ)))
    hrec

/-- Invert ParRed of a const-headed type into ParRedArgs of `familyIdx`.
`none` when a redex fires in the type (delta/beta/iota of the spine).
The two keys (`foldApps_congr`, `instantiate_arg`) construct forward
congruence; they do not invert a redex. DirectRec domains are
inductive-headed (`hfamSpine`); if this `none` is reachable from
`instantiate_both` of a constructor telescope, that is the
iota-vs-congr failing statement. -/
def parRed_familyIdx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (nparams : Nat) {A A' : Expr Nat}
    (h : ParRed E n Γ A A') :
    Option (ParRedArgs E n Γ
      (familyIdx nparams A) (familyIdx nparams A')) :=
  match h with
  | .refl _ A => some (parRedArgs_refl (familyIdx nparams A))
  | h =>
      match hsp : (appsSpine A).1 with
      | .const r ls =>
          have heq : A = foldApps (.const r ls) (appsSpine A).2 := by
            have hfold := foldApps_appsSpine A
            rw [hsp] at hfold
            exact hfold.symm
          match parRed_foldApps_const h (appsSpine A).2 heq with
          | some ⟨_ls', xs', heqA', _q, hargs⟩ =>
              some <| by
                subst heqA'
                simp only [familyIdx]
                have hsp' :
                    (appsSpine (foldApps (.const r _ls') xs')).2 =
                      xs' := by
                  rw [appsSpine_foldApps, appsSpine_const, List.nil_append]
                rw [hsp']
                exact parRedArgs_drop hargs nparams
          | none => none
      | .bvar _ => none
      | .sort _ => none
      | .app _ _ => none
      | .lam _ _ => none
      | .pi _ _ => none
      | .letE _ _ _ => none
      | .lit _ => none

/-! Inverse of `lift cutoff 1`. Fails iff the term mentions `bvar cutoff`.
Eta-short devel contracts `lam A (app (lift 0 1 f) (bvar 0))` to `f`. -/
def unlift (cutoff : Nat) : Expr Nat → Option (Expr Nat)
  | .bvar i =>
      if i = cutoff then none
      else if cutoff < i then some (.bvar (i - 1))
      else some (.bvar i)
  | .sort l => some (.sort l)
  | .const r ls => some (.const r ls)
  | .app f x =>
      match unlift cutoff f, unlift cutoff x with
      | some f', some x' => some (.app f' x')
      | _, _ => none
  | .lam a b =>
      match unlift cutoff a, unlift (cutoff + 1) b with
      | some a', some b' => some (.lam a' b')
      | _, _ => none
  | .pi a b =>
      match unlift cutoff a, unlift (cutoff + 1) b with
      | some a', some b' => some (.pi a' b')
      | _, _ => none
  | .letE a v b =>
      match unlift cutoff a, unlift cutoff v, unlift (cutoff + 1) b with
      | some a', some v', some b' => some (.letE a' v' b')
      | _, _, _ => none
  | .lit t => some (.lit t)

theorem unlift_lift (c : Nat) (e : Expr Nat) :
    unlift c (lift c 1 e) = some e := by
  induction e generalizing c with
  | bvar i =>
      by_cases hle : c ≤ i
      · rw [lift, if_pos hle, unlift, if_neg (by omega : ¬ (i + 1 = c)),
            if_pos (by omega : c < i + 1)]
        rfl
      · rw [lift, if_neg hle, unlift, if_neg (by omega : ¬ (i = c)),
            if_neg (by omega : ¬ (c < i))]
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx =>
      simp only [lift, unlift, ihf, ihx]
  | lam a b iha ihb =>
      simp only [lift, unlift, iha, ihb]
  | pi a b iha ihb =>
      simp only [lift, unlift, iha, ihb]
  | letE a v b iha ihv ihb =>
      simp only [lift, unlift, iha, ihv, ihb]
  | lit t => rfl

theorem lift_unlift (c : Nat) :
    (e : Expr Nat) → (e' : Expr Nat) → unlift c e = some e' →
    lift c 1 e' = e
  | .bvar i, e', h => by
      simp only [unlift] at h
      split at h
      · nomatch h
      · split at h
        · injection h with he
          subst he
          simp only [lift]
          rw [if_pos (by omega : c ≤ i - 1)]
          rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
        · injection h with he
          subst he
          simp only [lift]
          rw [if_neg (by omega : ¬ (c ≤ i))]
  | .sort l, e', h => by
      simp only [unlift] at h
      injection h with he; subst he; rfl
  | .const r ls, e', h => by
      simp only [unlift] at h
      injection h with he; subst he; rfl
  | .app f x, e', h => by
      simp only [unlift] at h
      cases hf : unlift c f with
      | none => simp only [hf] at h; cases unlift c x <;> nomatch h
      | some f' =>
          cases hx : unlift c x with
          | none => simp only [hf, hx] at h; nomatch h
          | some x' =>
              simp only [hf, hx] at h
              injection h with he; subst he
              simp only [lift]
              rw [lift_unlift c f f' hf, lift_unlift c x x' hx]
  | .lam a b, e', h => by
      simp only [unlift] at h
      cases ha : unlift c a with
      | none => simp only [ha] at h; cases unlift (c + 1) b <;> nomatch h
      | some a' =>
          cases hb : unlift (c + 1) b with
          | none => simp only [ha, hb] at h; nomatch h
          | some b' =>
              simp only [ha, hb] at h
              injection h with he; subst he
              simp only [lift]
              rw [lift_unlift c a a' ha, lift_unlift (c + 1) b b' hb]
  | .pi a b, e', h => by
      simp only [unlift] at h
      cases ha : unlift c a with
      | none => simp only [ha] at h; cases unlift (c + 1) b <;> nomatch h
      | some a' =>
          cases hb : unlift (c + 1) b with
          | none => simp only [ha, hb] at h; nomatch h
          | some b' =>
              simp only [ha, hb] at h
              injection h with he; subst he
              simp only [lift]
              rw [lift_unlift c a a' ha, lift_unlift (c + 1) b b' hb]
  | .letE a v b, e', h => by
      simp only [unlift] at h
      cases ha : unlift c a with
      | none =>
          simp only [ha] at h
          cases unlift c v <;> cases unlift (c + 1) b <;> nomatch h
      | some a' =>
          cases hv : unlift c v with
          | none =>
              simp only [ha, hv] at h
              cases unlift (c + 1) b <;> nomatch h
          | some v' =>
              cases hb : unlift (c + 1) b with
              | none => simp only [ha, hv, hb] at h; nomatch h
              | some b' =>
                  simp only [ha, hv, hb] at h
                  injection h with he; subst he
                  simp only [lift]
                  rw [lift_unlift c a a' ha, lift_unlift c v v' hv,
                    lift_unlift (c + 1) b b' hb]
  | .lit t, e', h => by
      simp only [unlift] at h
      injection h with he; subst he; rfl

def unliftList (c : Nat) : List (Expr Nat) → Option (List (Expr Nat))
  | [] => some []
  | x :: xs =>
      match unlift c x with
      | none => none
      | some x' =>
          match unliftList c xs with
          | none => none
          | some xs' => some (x' :: xs')

theorem unliftList_map_lift (c : Nat) :
    (xs : List (Expr Nat)) → unliftList c (xs.map (lift c 1)) = some xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, unliftList, unlift_lift, unliftList_map_lift c xs]

theorem unliftList_lift (c : Nat) :
    (xs xs' : List (Expr Nat)) → unliftList c xs = some xs' →
    xs = xs'.map (lift c 1)
  | [], xs', h => by
      simp only [unliftList] at h
      injection h with he; subst he; rfl
  | x :: xs, xs', h => by
      simp only [unliftList] at h
      cases hx : unlift c x with
      | none => simp only [hx] at h; nomatch h
      | some x' =>
          cases hxs : unliftList c xs with
          | none => simp only [hx, hxs] at h; nomatch h
          | some xs'' =>
              simp only [hx, hxs] at h
              injection h with he; subst he
              simp only [List.map_cons]
              rw [lift_unlift c x x' hx, unliftList_lift c xs xs'' hxs]

theorem unliftList_of_eq_map {c : Nat} {xs ys : List (Expr Nat)}
    (h : xs = ys.map (lift c 1)) :
    unliftList c xs = some ys := by
  rw [h]
  exact unliftList_map_lift c ys

theorem map_eq_snoc_unlift {c : Nat} :
    (ys : List (Expr Nat)) → (xs : List (Expr Nat)) → (z : Expr Nat) →
    xs ++ [z] = ys.map (lift c 1) →
    ∃ ys' y, ys = ys' ++ [y] ∧ xs = ys'.map (lift c 1) ∧ z = lift c 1 y
  | [], xs, z, h => by
      simp only [List.map_nil] at h
      cases xs with
      | nil => nomatch h
      | cons _ xs =>
          simp only [List.cons_append] at h
          nomatch h
  | y :: ys, xs, z, h => by
      match xs with
      | [] =>
          match ys with
          | [] =>
              simp only [List.map_cons, List.map_nil, List.nil_append] at h
              injection h with hz
              exact ⟨[], y, rfl, rfl, hz⟩
          | y2 :: ys =>
              simp only [List.map_cons, List.nil_append] at h
              injection h with _ htl
              nomatch htl
      | x :: xs =>
          simp only [List.map_cons, List.cons_append] at h
          injection h with hxy hrest
          have ⟨ys', y', hys, hxs, hz⟩ :=
            map_eq_snoc_unlift ys xs z hrest
          exact ⟨y :: ys', y', by rw [hys]; rfl,
            by simp only [List.map_cons, hxy.symm, hxs], hz⟩

/-- Eta-contraction of a developed body: `app f (bvar 0)` with `f` in
the image of `lift 0 1`. -/
def etaContract : Expr Nat → Option (Expr Nat)
  | .app f (.bvar 0) => unlift 0 f
  | _ => none

theorem etaContract_eta (f : Expr Nat) :
    etaContract (.app (lift 0 1 f) (.bvar 0)) = some f := by
  simp only [etaContract, unlift_lift]

end Rcic.Declarative
