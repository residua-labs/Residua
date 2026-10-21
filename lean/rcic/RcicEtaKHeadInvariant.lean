import rcic.RcicEtaKPeakPins

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# A-2 Step 1 — Multi-step head invariants for the positive Eq η/K peak

For any `ParRedTStar` path from a `const 65` spine with `< 6` arguments, every
successor is a `const 65` spine with the exact same argument count, provided no
step hits a `PEqT.proof` root on the `const 65` spine. Generalizing the
induction to track only the argument count `k` (and universe-level equivalence
class `ls₀`) over arbitrary argument terms and arbitrary step types avoids any
`AllVars` restriction on arguments.

Symmetrically, on the right side of the peak (`contracted = .lam domain (.bvar 1)`),
every `ParRedTStar` successor retains a `.lam _ (.bvar 1)` shape unless a step
hits a `PEqT.proof` root at the λ-root or at its `.bvar 1` body.

Every constructor of `ParRedT` (17 arms) and `PEqT` (9 arms) is covered.
No `ParRedT` rule is changed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8EtaK

/-- Every legacy `IotaWitness` at `eqEnvT` with `recRef = 65` has total
    application arity `preMajor.length + 1 = 6`. -/
theorem rec65_witness_arity (w : IotaWitness eqEnvT) (href : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hmem := w.hrec
  rw [href] at hmem
  change some eqRecT = some w.recMember at hmem
  have hm : w.recMember = eqRecT := (Option.some.inj hmem).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  rw [w.hpre]
  exact hn

/-- Every schema `IotaWitnessS` at `eqEnvT` with `recRef = 65` also has total
    application arity `preMajor.length + 1 = 6`. -/
theorem rec65_witnessS_arity (w : IotaWitnessS eqEnvT) (href : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hmem := w.hrec
  rw [href] at hmem
  change some eqRecT = some w.recMember at hmem
  have hm : w.recMember = eqRecT := (Option.some.inj hmem).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  rw [w.hpre]
  exact hn

/-- A `const 65` spine with `< 6` arguments cannot be a `recCall` source for
    `iotaStarK` or `IotaWitness`. -/
theorem short_rec65_not_K_source
    {ls : List Level} {xs : List (Expr Nat)} (hshort : xs.length < 6)
    (w : IotaWitness eqEnvT) (major : Expr Nat) :
    recCall (.const w.recRef w.ls) w.preMajor major ≠
      foldApps (.const 65 ls) xs := by
  intro heq
  have hs := congrArg appsSpine heq
  change appsSpine (foldApps (.const w.recRef w.ls)
    (w.preMajor ++ [major])) = appsSpine (foldApps (.const 65 ls) xs) at hs
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  have hh : Expr.const w.recRef w.ls = Expr.const 65 ls :=
    congrArg Prod.fst hs
  have href : w.recRef = 65 := by
    injection hh
  have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
  have hlen : w.preMajor.length + 1 = xs.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] using hl
  have hfull := rec65_witness_arity w href
  omega

/-- A `const 65` spine with `< 5` arguments cannot be the η-contracted source
    `f` of `ParRedT.iotaStarKEta` (`recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0)`). -/
theorem short_rec65_not_etaK_source
    {ls : List Level} {xs : List (Expr Nat)} (hshort : xs.length < 5)
    (w : IotaWitness eqEnvT) {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (heq : f = foldApps (.const 65 ls) xs) : False := by
  have hhd := iotaStarKEta_head happ
  have hs := congrArg appsSpine heq
  rw [appsSpine_foldApps_const] at hs
  have h1 : (appsSpine f).1 = .const 65 ls := congrArg Prod.fst hs
  have h2 : (appsSpine f).2 = xs := congrArg Prod.snd hs
  have hconst : Expr.const w.recRef w.ls = Expr.const 65 ls :=
    hhd.1.symm.trans h1
  have href : w.recRef = 65 := by
    injection hconst
  have hlen : xs.length = w.preMajor.length := by
    have hm := congrArg List.length hhd.2.1
    rw [List.length_map, h2] at hm
    exact hm
  have hfull := rec65_witness_arity w href
  omega

/-- Predicate asserting that a `ParRedT` step does not use the 18th constructor
    `ParRedT.iotaStarKEta` anywhere in its derivation tree (i.e. lies in the
    pre-repair 17-constructor subsystem). -/
def NoEtaKStep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Prop
  | _, _, _, _, .iotaStarKEta .. => False
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _ =>
      NoEtaKStep hv
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _ =>
      NoEtaKStep hf ∧ NoEtaKStep ha
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _ =>
      NoEtaKStep hb ∧ NoEtaKStep ha
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _ =>
      NoEtaKStep hb
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ =>
      NoEtaKStep hv ∧ NoEtaKStep hb
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ =>
      NoEtaKStep hv ∧ NoEtaKStep hb
  | _, _, _, _, .eta _ _ _ _ _ hf _ =>
      NoEtaKStep hf
  | _, _, _, _, .iotaSpine _ _ _ _ _ hstep _ _ _ =>
      NoEtaKStep hstep
  | _, _, _, _, .conv _ _ _ _ _ h _ =>
      NoEtaKStep h
  | _, _, _, _, _ => True

/-- Multi-step lift of `NoEtaKStep` to `ParRedTStar`. -/
def NoEtaKStar {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    ParRedTStar PEq E n Γ a b T → Prop
  | .refl _ _ _ _ => True
  | .tail h hs => NoEtaKStep h ∧ NoEtaKStar hs

/-- `KEtaFree h` (`NoEtaKStep h`): no `ParRedT.iotaStarKEta` node anywhere in `h`. -/
abbrev KEtaFree := @NoEtaKStep

/-- `KEtaFreeStar hs` (`NoEtaKStar hs`): no `ParRedT.iotaStarKEta` node anywhere in `hs`. -/
abbrev KEtaFreeStar := @NoEtaKStar

/-- Neither arm of `DerivedIotaU` (`IotaWitness` or `IotaWitnessS`) can fire on
    a `const 65` spine with `< 6` arguments. -/
theorem short_rec65_not_derivedIotaU
    {ls : List Level} {xs : List (Expr Nat)} {lhs rhs : Expr Nat}
    (hshort : xs.length < 6)
    (hI : DerivedIotaU eqEnvT lhs rhs)
    (heq : lhs = foldApps (.const 65 ls) xs) : False := by
  cases hI with
  | ofU w =>
      exact short_rec65_not_K_source hshort w (ctorMajor w) heq
  | ofUS w =>
      have hs := congrArg appsSpine heq
      change appsSpine (foldApps (.const w.recRef w.ls)
        (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)])) =
        appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
      have hh : Expr.const w.recRef w.ls = Expr.const 65 ls :=
        congrArg Prod.fst hs
      have href : w.recRef = 65 := by
        injection hh
      have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
      have hlen : w.preMajor.length + 1 = xs.length := by
        simpa only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add] using hl
      have hfull := rec65_witnessS_arity w href
      omega

/-- If `e = foldApps (.const r ls) xs`, then the head of `appsSpine e` is `.const r ls`. -/
theorem appsSpine_fst_of_eq_foldApps_const {e : Expr Nat} {r : Nat} {ls : List Level}
    {xs : List (Expr Nat)} (h : e = foldApps (.const r ls) xs) :
    (appsSpine e).1 = .const r ls := by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  exact congrArg Prod.fst hs

/-- A constant-headed application spine is never a λ-abstraction. -/
theorem foldApps_const_ne_lam_any {r : Nat} {ls : List Level}
    {xs : List (Expr Nat)} {A body : Expr Nat}
    (h : foldApps (.const r ls) xs = .lam A body) : False :=
  nomatch appsSpine_fst_of_eq_foldApps_const h.symm

/-- `DerivedIotaU` never has a `.bvar` source. -/
theorem derivedIotaU_bvar_source_false {E : ResolvedEnv} {lhs rhs : Expr Nat}
    {i : Nat} (hI : DerivedIotaU E lhs rhs) (heq : lhs = .bvar i) : False := by
  cases hI with
  | ofU w =>
      exact foldApps_snoc_ne_bvar (.const w.recRef w.ls)
        (ctorMajor w) w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_bvar (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
        w.preMajor heq

/-- `DerivedIotaU` never has a `.lam` source. -/
theorem derivedIotaU_lam_source_false {E : ResolvedEnv} {lhs rhs A body : Expr Nat}
    (hI : DerivedIotaU E lhs rhs) (heq : lhs = .lam A body) : False := by
  cases hI with
  | ofU w =>
      exact foldApps_const_ne_lam_any
        (xs := w.preMajor ++ [ctorMajor w]) heq
  | ofUS w =>
      exact foldApps_const_ne_lam_any
        (xs := w.preMajor ++ [foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)]) heq

/-- General `const 65` spine predicate parameterized by level class `ls₀` and
    argument count `k`. No syntactic restriction is placed on `xs`. -/
def Const65SpineAt (ls₀ : List Level) (k : Nat) (e : Expr Nat) : Prop :=
  ∃ (ls : List Level) (xs : List (Expr Nat)),
    e = foldApps (.const 65 ls) xs ∧ xs.length = k ∧ eqNList ls ls₀

/-- Proof-root witness on a `const 65` spine of length `≤ k` at level class `ls₀`. -/
def HasConst65ProofRoot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ls₀ : List Level) (k : Nat) : Prop :=
  ∃ (ls : List Level) (xs : List (Expr Nat)) (P : Expr Nat),
    xs.length ≤ k ∧ eqNList ls ls₀ ∧
    Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
    Nonempty (HasTyT E n Γ (foldApps (.const 65 ls) xs) P)

theorem hasConst65ProofRoot_mono {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₀ : List Level} {k₁ k₂ : Nat} (hle : k₁ ≤ k₂)
    (h : HasConst65ProofRoot E n Γ ls₀ k₁) :
    HasConst65ProofRoot E n Γ ls₀ k₂ := by
  rcases h with ⟨ls, xs, P, hlen, hls, hP, hp⟩
  exact ⟨ls, xs, P, Nat.le_trans hlen hle, hls, hP, hp⟩

/-- Raw `PEqT` step from a `const 65` spine of length `k`: either preserves
    `Const65SpineAt ls₀ k` or hits a `PEqT.proof` root on a spine prefix of
    length `≤ k`. Covers all 9 `PEqT` constructors. -/
theorem peqT_const65_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₀ : List Level} :
    {a b : Expr Nat} → PEqT E n Γ a b →
    ∀ {ls : List Level} {xs : List (Expr Nat)} {k : Nat},
      a = foldApps (.const 65 ls) xs →
      xs.length = k →
      eqNList ls ls₀ →
      Const65SpineAt ls₀ k b ∨ HasConst65ProofRoot E n Γ ls₀ k
  | _, _, .const _ r ls1 ls2 hc, ls, xs, k, heq, hk, hls => by
      have hs := congrArg appsSpine heq
      change (.const r ls1, []) = appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : Expr.const r ls1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      subst hx
      injection hh with hr hls1
      subst hr
      subst hls1
      subst hk
      exact .inl ⟨ls2, [], rfl, rfl, eqNList_trans (eqNList_symm hc) hls⟩
  | _, _, .app _ f f' x x' hf _ha, ls, xs, k, heq, hk, hls => by
      have hs := congrArg appsSpine heq
      change ((appsSpine f).1, (appsSpine f).2 ++ [x]) =
        appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : (appsSpine f).1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : (appsSpine f).2 ++ [x] = xs := congrArg Prod.snd hs
      have hf_eq : f = foldApps (.const 65 ls) (appsSpine f).2 := by
        rw [← hh]
        exact (foldApps_appsSpine f).symm
      have hlen_le : (appsSpine f).2.length ≤ k := by
        have hl := congrArg List.length hx
        simp only [List.length_append, List.length_singleton] at hl
        omega
      rcases peqT_const65_spine hf hf_eq rfl hls with hfc | hprf
      · rcases hfc with ⟨ls', ys', hf'_eq, hys'_len, hls'⟩
        refine .inl ⟨ls', ys' ++ [x'], ?_, ?_, hls'⟩
        · rw [hf'_eq, foldApps_snoc]
        · have hl := congrArg List.length hx
          simp only [List.length_append, List.length_singleton] at hl ⊢
          omega
      · exact .inr (hasConst65ProofRoot_mono hlen_le hprf)
  | _, _, .proof _ _ _ P _ hP _ hp _, ls, xs, k, heq, hk, hls => by
      subst heq
      subst hk
      exact .inr ⟨ls, xs, P, Nat.le_refl _, hls, ⟨hP⟩, ⟨hp⟩⟩
  | _, _, .bvar .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .sort .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Unconditional single-step `ParRedT` invariant from a `const 65` spine with
    `k < 5` arguments at `eqEnvT` across all 18 `ParRedT` constructors
    (including `.iotaStarKEta`, which requires arity 5). -/
theorem parRedT_const65_spine_lt5 {n : Nat} {Γ : LCtx} {ls₀ : List Level} :
    {a b T : Expr Nat} → ParRedT (PEqLeafT eqEnvT n) eqEnvT n Γ a b T →
    ∀ {ls : List Level} {xs : List (Expr Nat)} {k : Nat},
      a = foldApps (.const 65 ls) xs →
      xs.length = k →
      k < 5 →
      eqNList ls ls₀ →
      Const65SpineAt ls₀ k b ∨ HasConst65ProofRoot eqEnvT n Γ ls₀ k
  | _, _, _, .refl _ _ _ _, ls, xs, k, heq, hk, _, hls =>
      .inl ⟨ls, xs, heq, hk, hls⟩
  | _, _, _, .consts _ r ls1 ls2 _ hc _ _, ls, xs, k, heq, hk, _, hls => by
      have hs := congrArg appsSpine heq
      change (.const r ls1, []) = appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : Expr.const r ls1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      subst hx
      injection hh with hr hls1
      subst hr
      subst hls1
      subst hk
      exact .inl ⟨ls2, [], rfl, rfl, eqNList_trans (eqNList_symm hc) hls⟩
  | _, _, _, .delta _ r ls1 m body _ hres hbody _ _ _ _ _, _, _, _, heq, _, _, _ => by
      have hh := appsSpine_fst_of_eq_foldApps_const heq
      injection hh with hr _
      subst hr
      change some eqRecT = some m at hres
      have hm : m = eqRecT := (Option.some.inj hres).symm
      subst hm
      cases hbody
  | _, _, _, .app _ f f' x x' _ _ _ _ _ hf _ _ _ _ha _, ls, xs, k, heq, hk, hk5, hls => by
      have hs := congrArg appsSpine heq
      change ((appsSpine f).1, (appsSpine f).2 ++ [x]) =
        appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : (appsSpine f).1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : (appsSpine f).2 ++ [x] = xs := congrArg Prod.snd hs
      have hf_eq : f = foldApps (.const 65 ls) (appsSpine f).2 := by
        rw [← hh]
        exact (foldApps_appsSpine f).symm
      have hl := congrArg List.length hx
      simp only [List.length_append, List.length_singleton] at hl
      have hlen_lt : (appsSpine f).2.length < 5 := by omega
      have hlen_le : (appsSpine f).2.length ≤ k := by omega
      rcases parRedT_const65_spine_lt5 hf hf_eq rfl hlen_lt hls with hfc | hprf
      · rcases hfc with ⟨ls', ys', hf'_eq, hys'_len, hls'⟩
        refine .inl ⟨ls', ys' ++ [x'], ?_, ?_, hls'⟩
        · rw [hf'_eq, foldApps_snoc]
        · simp only [List.length_append, List.length_singleton]
          omega
      · exact .inr (hasConst65ProofRoot_mono hlen_le hprf)
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, ls, xs, k, heq, hk, hk5, hls => by
      rcases parRedT_const65_spine_lt5 hstep heq hk hk5 hls with hfc | hprf
      · rcases hfc with ⟨ls', xs', hstep_eq, hxs'_len, _⟩
        have hshort : xs'.length < 6 := by omega
        exact False.elim (short_rec65_not_derivedIotaU hshort hI hstep_eq)
      · exact .inr hprf
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      ls, xs, k, heq, hk, hk5, _ => by
      have hshort : xs.length < 6 := by omega
      exact False.elim (short_rec65_not_K_source hshort w major heq)
  | _, _, _, .iotaStarKEta _ w _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _,
      ls, xs, k, heq, hk, hk5, _ => by
      have hshort : xs.length < 5 := by omega
      exact False.elim (short_rec65_not_etaK_source hshort w happ heq)
  | _, _, _, .peq _ _ _ _ leaf, ls, xs, k, heq, hk, _, hls =>
      peqT_const65_spine leaf.1 heq hk hls
  | _, _, _, .conv _ _ _ _ _ h _, ls, xs, k, heq, hk, hk5, hls =>
      parRedT_const65_spine_lt5 h heq hk hk5 hls
  | _, _, _, .sortEq .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Unconditional multi-step `ParRedTStar` head invariant for a `const 65` spine
    with `k < 5` arguments across all 18 `ParRedT` constructors. -/
theorem parRedTStar_const65_spine_lt5 {n : Nat} {Γ : LCtx} {ls₀ : List Level}
    {k : Nat} (hk5 : k < 5) :
    {a b T : Expr Nat} → ParRedTStar (PEqLeafT eqEnvT n) eqEnvT n Γ a b T →
    Const65SpineAt ls₀ k a →
    Const65SpineAt ls₀ k b ∨ HasConst65ProofRoot eqEnvT n Γ ls₀ k
  | _, _, _, .refl _ _ _ _, ha => .inl ha
  | _, _, _, .tail h hs, ⟨ls, xs, heq, hk, hls⟩ => by
      rcases parRedT_const65_spine_lt5 h heq hk hk5 hls with hb | hprf
      · exact parRedTStar_const65_spine_lt5 hk5 hs hb
      · exact .inr hprf

/-- When `HasConst65ProofRoot` is excluded, every 18-constructor `ParRedTStar`
    successor of a `const 65` spine with `k < 5` arguments is a `const 65` spine
    with the same argument count `k`. -/
theorem parRedTStar_const65_spine_lt5_of_no_proof {n : Nat} {Γ : LCtx}
    {ls₀ : List Level} {k : Nat} (hk5 : k < 5)
    (hNoPrf : ¬ HasConst65ProofRoot eqEnvT n Γ ls₀ k)
    {a b T : Expr Nat}
    (hs : ParRedTStar (PEqLeafT eqEnvT n) eqEnvT n Γ a b T)
    (ha : Const65SpineAt ls₀ k a) :
    Const65SpineAt ls₀ k b := by
  rcases parRedTStar_const65_spine_lt5 hk5 hs ha with hb | hprf
  · exact hb
  · exact False.elim (hNoPrf hprf)

/-- Single-step `ParRedT` invariant from a `const 65` spine with `k < 6`
    arguments at `eqEnvT` for steps satisfying `NoEtaKStep`: every step
    preserves `Const65SpineAt ls₀ k` unless a `PEqT.proof` root occurs on a
    spine prefix of length `≤ k`. -/
theorem parRedT_const65_spine {n : Nat} {Γ : LCtx} {ls₀ : List Level} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT eqEnvT n) eqEnvT n Γ a b T) →
    NoEtaKStep h →
    ∀ {ls : List Level} {xs : List (Expr Nat)} {k : Nat},
      a = foldApps (.const 65 ls) xs →
      xs.length = k →
      k < 6 →
      eqNList ls ls₀ →
      Const65SpineAt ls₀ k b ∨ HasConst65ProofRoot eqEnvT n Γ ls₀ k
  | _, _, _, .refl _ _ _ _, _, ls, xs, k, heq, hk, _, hls =>
      .inl ⟨ls, xs, heq, hk, hls⟩
  | _, _, _, .consts _ r ls1 ls2 _ hc _ _, _, ls, xs, k, heq, hk, _, hls => by
      have hs := congrArg appsSpine heq
      change (.const r ls1, []) = appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : Expr.const r ls1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      subst hx
      injection hh with hr hls1
      subst hr
      subst hls1
      subst hk
      exact .inl ⟨ls2, [], rfl, rfl, eqNList_trans (eqNList_symm hc) hls⟩
  | _, _, _, .delta _ r ls1 m body _ hres hbody _ _ _ _ _, _, _, _, _, heq, _, _, _ => by
      have hh := appsSpine_fst_of_eq_foldApps_const heq
      injection hh with hr _
      subst hr
      change some eqRecT = some m at hres
      have hm : m = eqRecT := (Option.some.inj hres).symm
      subst hm
      cases hbody
  | _, _, _, .app _ f f' x x' _ _ _ _ _ hf _ _ _ _ha _, hno, ls, xs, k, heq, hk, hk6, hls => by
      have hs := congrArg appsSpine heq
      change ((appsSpine f).1, (appsSpine f).2 ++ [x]) =
        appsSpine (foldApps (.const 65 ls) xs) at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : (appsSpine f).1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : (appsSpine f).2 ++ [x] = xs := congrArg Prod.snd hs
      have hf_eq : f = foldApps (.const 65 ls) (appsSpine f).2 := by
        rw [← hh]
        exact (foldApps_appsSpine f).symm
      have hl := congrArg List.length hx
      simp only [List.length_append, List.length_singleton] at hl
      have hlen_lt : (appsSpine f).2.length < 6 := by omega
      have hlen_le : (appsSpine f).2.length ≤ k := by omega
      rcases parRedT_const65_spine hf hno.1 hf_eq rfl hlen_lt hls with hfc | hprf
      · rcases hfc with ⟨ls', ys', hf'_eq, hys'_len, hls'⟩
        refine .inl ⟨ls', ys' ++ [x'], ?_, ?_, hls'⟩
        · rw [hf'_eq, foldApps_snoc]
        · simp only [List.length_append, List.length_singleton]
          omega
      · exact .inr (hasConst65ProofRoot_mono hlen_le hprf)
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, hno, ls, xs, k, heq, hk, hk6, hls => by
      rcases parRedT_const65_spine hstep hno heq hk hk6 hls with hfc | hprf
      · rcases hfc with ⟨ls', xs', hstep_eq, hxs'_len, _⟩
        have hshort : xs'.length < 6 := by omega
        exact False.elim (short_rec65_not_derivedIotaU hshort hI hstep_eq)
      · exact .inr hprf
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      _, ls, xs, k, heq, hk, hk6, _ => by
      have hshort : xs.length < 6 := by omega
      exact False.elim (short_rec65_not_K_source hshort w major heq)
  | _, _, _, .iotaStarKEta .., hno, _, _, _, _, _, _, _ =>
      False.elim hno
  | _, _, _, .peq _ _ _ _ leaf, _, ls, xs, k, heq, hk, _, hls =>
      peqT_const65_spine leaf.1 heq hk hls
  | _, _, _, .conv _ _ _ _ _ h _, hno, ls, xs, k, heq, hk, hk6, hls =>
      parRedT_const65_spine h hno heq hk hk6 hls
  | _, _, _, .sortEq .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, _, heq, _, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Multi-step `ParRedTStar` head invariant for a `const 65` spine with `k < 6`
    arguments along any `NoEtaKStar` path: every finite path preserves
    `Const65SpineAt ls₀ k` unless a step hits a `PEqT.proof` root on a spine
    prefix of length `≤ k`. -/
theorem parRedTStar_const65_spine {n : Nat} {Γ : LCtx} {ls₀ : List Level}
    {k : Nat} (hk6 : k < 6) :
    {a b T : Expr Nat} → (hs : ParRedTStar (PEqLeafT eqEnvT n) eqEnvT n Γ a b T) →
    NoEtaKStar hs →
    Const65SpineAt ls₀ k a →
    Const65SpineAt ls₀ k b ∨ HasConst65ProofRoot eqEnvT n Γ ls₀ k
  | _, _, _, .refl _ _ _ _, _, ha => .inl ha
  | _, _, _, .tail h hs, hno, ⟨ls, xs, heq, hk, hls⟩ => by
      rcases hno with ⟨hno1, hno2⟩
      rcases parRedT_const65_spine h hno1 heq hk hk6 hls with hb | hprf
      · exact parRedTStar_const65_spine hk6 hs hno2 hb
      · exact .inr hprf

/-- When `HasConst65ProofRoot` is excluded, every `NoEtaKStar` successor of a
    `const 65` spine with `k < 6` arguments is a `const 65` spine with the same
    argument count `k`. -/
theorem parRedTStar_const65_spine_of_no_proof {n : Nat} {Γ : LCtx}
    {ls₀ : List Level} {k : Nat} (hk6 : k < 6)
    (hNoPrf : ¬ HasConst65ProofRoot eqEnvT n Γ ls₀ k)
    {a b T : Expr Nat}
    (hs : ParRedTStar (PEqLeafT eqEnvT n) eqEnvT n Γ a b T)
    (hno : NoEtaKStar hs)
    (ha : Const65SpineAt ls₀ k a) :
    Const65SpineAt ls₀ k b := by
  rcases parRedTStar_const65_spine hk6 hs hno ha with hb | hprf
  · exact hb
  · exact False.elim (hNoPrf hprf)

/-! ## Right-side λ-head invariant (`contracted` and its successors) -/

/-- The right-side shape: a λ-abstraction whose body is `.bvar 1`. -/
def ContractedLam (e : Expr Nat) : Prop :=
  ∃ A : Expr Nat, e = .lam A (.bvar 1)

/-- Proof-root witness on the right side: either at `.lam A (.bvar 1)` in `Γ`
    or at the body `.bvar 1` under a well-formed binder `.assumption A :: Γ`. -/
def HasContractedProofRoot (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Prop :=
  (∃ (A P : Expr Nat),
    Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
    Nonempty (HasTyT E n Γ (.lam A (.bvar 1)) P)) ∨
  (∃ (A P : Expr Nat),
    Nonempty (CtxWfT E n (.assumption A :: Γ)) ∧
    Nonempty (HasTyT E n (.assumption A :: Γ) P (.sort .zero)) ∧
    Nonempty (HasTyT E n (.assumption A :: Γ) (.bvar 1) P))

/-- Raw `PEqT` step from `.bvar i`: either stays `.bvar i` or is a `PEqT.proof`
    root on `.bvar i`. -/
theorem peqT_bvar_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} :
    {a b : Expr Nat} → PEqT E n Γ a b → a = .bvar i →
    b = .bvar i ∨
      ∃ P : Expr Nat,
        Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
        Nonempty (HasTyT E n Γ (.bvar i) P)
  | _, _, .bvar _ _, heq => .inl heq
  | _, _, .proof _ _ _ P _ hP _ hp _, heq => by
      subst heq
      exact .inr ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  | _, _, .sort .., heq => nomatch heq
  | _, _, .const .., heq => nomatch heq
  | _, _, .app .., heq => nomatch heq
  | _, _, .lam .., heq => nomatch heq
  | _, _, .pi .., heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .lit .., heq => nomatch heq

/-- Single-step `ParRedT` from `.bvar i` at a non-let slot: either stays
    `.bvar i` or hits a `PEqT.proof` root on `.bvar i`. -/
theorem parRedT_bvar_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    (hz : ∀ B v, Γ.get? i ≠ some (.letBinding B v)) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T → a = .bvar i →
    b = .bvar i ∨
      ∃ P : Expr Nat,
        Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
        Nonempty (HasTyT E n Γ (.bvar i) P)
  | _, _, _, .refl _ _ _ _, heq => .inl heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ hget _ _ _, heq => by
      cases heq
      exact False.elim (hz _ _ hget)
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, heq => by
      rcases parRedT_bvar_step hz hstep heq with hb | hprf
      · exact False.elim (derivedIotaU_bvar_source_false hI hb)
      · exact .inr hprf
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      False.elim (foldApps_snoc_ne_bvar (.const w.recRef w.ls) major w.preMajor heq)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .peq _ _ _ _ leaf, heq =>
      peqT_bvar_step leaf.1 heq
  | _, _, _, .conv _ _ _ _ _ h _, heq =>
      parRedT_bvar_step hz h heq
  | _, _, _, .sortEq .., heq => nomatch heq
  | _, _, _, .consts .., heq => nomatch heq
  | _, _, _, .delta .., heq => nomatch heq
  | _, _, _, .app .., heq => nomatch heq
  | _, _, _, .beta .., heq => nomatch heq
  | _, _, _, .lam .., heq => nomatch heq
  | _, _, _, .pi .., heq => nomatch heq
  | _, _, _, .letE .., heq => nomatch heq
  | _, _, _, .zeta .., heq => nomatch heq
  | _, _, _, .lit .., heq => nomatch heq
  | _, _, _, .eta .., heq => nomatch heq

/-- Raw `PEqT` step from `.lam A (.bvar 1)` (typed at `T`): either stays in
    `ContractedLam` or hits `HasContractedProofRoot`. -/
theorem peqT_contracted_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → PEqT E n Γ a b → HasTyT E n Γ a T →
    ∀ {A : Expr Nat}, a = .lam A (.bvar 1) →
    ContractedLam b ∨ HasContractedProofRoot E n Γ
  | _, _, _, .lam _ A₀ A' _ _ _ hb, ht, A, heq => by
      injection heq with hAeq hbeq
      subst hAeq
      obtain ⟨u, _, hA, _, _⟩ := hasTyTInv_lam ht rfl
      have hΓA : CtxWfT E n (.assumption A₀ :: Γ) :=
        .assumption Γ A₀ u hΓ hA
      rcases peqT_bvar_step hb hbeq with hb' | ⟨P, hP, hp⟩
      · exact .inl ⟨A', congrArg (Expr.lam A') hb'⟩
      · exact .inr (.inr ⟨A₀, P, ⟨hΓA⟩, hP, hp⟩)
  | _, _, _, .proof _ _ _ P _ hP _ hp _, _, A, heq => by
      subst heq
      exact .inr (.inl ⟨A, P, ⟨hP⟩, ⟨hp⟩⟩)
  | _, _, _, .bvar .., _, _, heq => nomatch heq
  | _, _, _, .sort .., _, _, heq => nomatch heq
  | _, _, _, .const .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .pi .., _, _, heq => nomatch heq
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .lit .., _, _, heq => nomatch heq

/-- Single-step `ParRedT` invariant from `.lam A (.bvar 1)`: every step
    preserves `ContractedLam` unless `HasContractedProofRoot` occurs.
    Covers all 18 `ParRedT` constructors. -/
theorem parRedT_contracted_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hz0 : ∀ B v, Γ.get? 0 ≠ some (.letBinding B v)) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T →
    ∀ {A : Expr Nat}, a = .lam A (.bvar 1) →
    ContractedLam b ∨ HasContractedProofRoot E n Γ
  | _, _, _, .refl _ _ _ _, A, heq => .inl ⟨A, heq⟩
  | _, _, _, .lam _ A₀ A' _ _ _ u _ _ hA _ hb _, A, heq => by
      injection heq with hAeq hbeq
      subst hAeq
      have hΓA : CtxWfT E n (.assumption A₀ :: Γ) :=
        .assumption Γ A₀ u hΓ hA
      have hz1 : ∀ B v, (LocalDecl.assumption A₀ :: Γ).get? 1 ≠
          some (.letBinding B v) := hz0
      rcases parRedT_bvar_step hz1 hb hbeq with hb' | ⟨P, hP, hp⟩
      · exact .inl ⟨A', congrArg (Expr.lam A') hb'⟩
      · exact .inr (.inr ⟨A₀, P, ⟨hΓA⟩, hP, hp⟩)
  | _, _, _, .eta _ f _ A₀ _ _ _, A, heq => by
      injection heq with _ hbeq
      cases hbeq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, heq => by
      rcases parRedT_contracted_lam hΓ hz0 hstep heq with ⟨A', hb⟩ | hprf
      · exact False.elim (derivedIotaU_lam_source_false hI hb)
      · exact .inr hprf
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, heq =>
      False.elim (foldApps_const_ne_lam_any (xs := w.preMajor ++ [major]) heq)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .peq _ _ _ _ leaf, _, heq =>
      peqT_contracted_lam hΓ leaf.1 leaf.2.1 heq
  | _, _, _, .conv _ _ _ _ _ h _, _, heq =>
      parRedT_contracted_lam hΓ hz0 h heq
  | _, _, _, .sortEq .., _, heq => nomatch heq
  | _, _, _, .consts .., _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app .., _, heq => nomatch heq
  | _, _, _, .beta .., _, heq => nomatch heq
  | _, _, _, .pi .., _, heq => nomatch heq
  | _, _, _, .letE .., _, heq => nomatch heq
  | _, _, _, .zeta .., _, heq => nomatch heq
  | _, _, _, .lit .., _, heq => nomatch heq

/-- Multi-step `ParRedTStar` invariant for `ContractedLam`: every finite path
    from `.lam A (.bvar 1)` preserves `ContractedLam` unless a step hits
    `HasContractedProofRoot`. -/
theorem parRedTStar_contracted_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hz0 : ∀ B v, Γ.get? 0 ≠ some (.letBinding B v)) :
    {a b T : Expr Nat} → ParRedTStar (PEqLeafT E n) E n Γ a b T →
    ContractedLam a →
    ContractedLam b ∨ HasContractedProofRoot E n Γ
  | _, _, _, .refl _ _ _ _, ha => .inl ha
  | _, _, _, .tail h hs, ⟨A, heq⟩ => by
      rcases parRedT_contracted_lam hΓ hz0 h heq with hb | hprf
      · exact parRedTStar_contracted_lam hΓ hz0 hs hb
      · exact .inr hprf

/-- When `HasContractedProofRoot` is excluded, every `ParRedTStar` successor of
    `contracted` keeps its `.lam _ (.bvar 1)` shape (and in particular a `.lam`
    head). -/
theorem parRedTStar_contracted_lam_of_no_proof {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hz0 : ∀ B v, Γ.get? 0 ≠ some (.letBinding B v))
    (hNoPrf : ¬ HasContractedProofRoot E n Γ)
    {a b T : Expr Nat}
    (hs : ParRedTStar (PEqLeafT E n) E n Γ a b T)
    (ha : ContractedLam a) :
    ContractedLam b := by
  rcases parRedTStar_contracted_lam hΓ hz0 hs ha with hb | hprf
  · exact hb
  · exact False.elim (hNoPrf hprf)

/-! ## Endpoint specialization and syntactic head clash -/

/-- `partialRec u` is a `const 65` spine of length 5 at level list `[u]`. -/
theorem const65SpineAt_partialRec (u : Level) :
    Const65SpineAt [u] 5 (partialRec u) :=
  ⟨[u], [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2], rfl, rfl,
    eqNList_refl [u]⟩

/-- `contracted` has `ContractedLam` shape. -/
theorem contractedLam_contracted : ContractedLam contracted :=
  ⟨domain, rfl⟩

/-- Slot 0 of `ctx u` is an `.assumption`, never a `.letBinding`. -/
theorem ctx_get0_ne_letBinding (u : Level) :
    ∀ B v, (ctx u).get? 0 ≠ some (.letBinding B v) := by
  intro B v h
  cases h

/-- No expression can be both a `const 65` spine and a `ContractedLam`. -/
theorem const65SpineAt_not_contractedLam {ls₀ : List Level} {k : Nat}
    {e : Expr Nat} (hc : Const65SpineAt ls₀ k e) (hl : ContractedLam e) :
    False := by
  rcases hc with ⟨ls, xs, heq, _, _⟩
  rcases hl with ⟨A, hlam⟩
  rw [heq] at hlam
  exact foldApps_const_ne_lam_any hlam

/-- Excluding proof roots on both sides refutes any common `NoEtaKStar` reduct
    between `partialRec u` and `contracted` (the pre-repair 17-constructor
    obstruction). -/
theorem partialRec_not_joinable_of_no_proof (u : Level)
    (hu : levelsBounded 2 [u] = true)
    (hNoLeft : ¬ HasConst65ProofRoot eqEnvT 2 (ctx u) [u] 5)
    (hNoRight : ¬ HasContractedProofRoot eqEnvT 2 (ctx u)) :
    ¬ ∃ (join : Expr Nat)
        (hsL : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2
          (ctx u) (partialRec u) join commonIndex)
        (hsR : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2
          (ctx u) contracted join commonIndex),
        NoEtaKStar hsL ∧ NoEtaKStar hsR := by
  rintro ⟨join, hsL, hsR, hnoL, _hnoR⟩
  have hL : Const65SpineAt [u] 5 join :=
    parRedTStar_const65_spine_of_no_proof (by decide) hNoLeft hsL hnoL
      (const65SpineAt_partialRec u)
  have hR : ContractedLam join :=
    parRedTStar_contracted_lam_of_no_proof (contextWf u hu)
      (ctx_get0_ne_letBinding u) hNoRight hsR contractedLam_contracted
  exact const65SpineAt_not_contractedLam hL hR

/-- Excluding proof roots on both sides also refutes modulo-`PEqLeafT`
    joinability along `NoEtaKStar` paths between `partialRec u` and
    `contracted`. -/
theorem partialRec_not_modulo_joinable_of_no_proof (u : Level)
    (hu : levelsBounded 2 [u] = true)
    (hNoLeft : ¬ HasConst65ProofRoot eqEnvT 2 (ctx u) [u] 5)
    (hNoRight : ¬ HasContractedProofRoot eqEnvT 2 (ctx u)) :
    ¬ ∃ (u' v' : Expr Nat)
        (hsL : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2
          (ctx u) (partialRec u) u' commonIndex)
        (hsR : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2
          (ctx u) contracted v' commonIndex),
        NoEtaKStar hsL ∧ NoEtaKStar hsR ∧
        Nonempty (PEqLeafT eqEnvT 2 (ctx u) u' v' commonIndex) := by
  rintro ⟨u', v', hsL, hsR, hnoL, _hnoR, ⟨hpeq⟩⟩
  have hL : Const65SpineAt [u] 5 u' :=
    parRedTStar_const65_spine_of_no_proof (by decide) hNoLeft hsL hnoL
      (const65SpineAt_partialRec u)
  have hR : ContractedLam v' :=
    parRedTStar_contracted_lam_of_no_proof (contextWf u hu)
      (ctx_get0_ne_letBinding u) hNoRight hsR contractedLam_contracted
  rcases hL with ⟨ls, xs, hu'_eq, hk, hls⟩
  rcases peqT_const65_spine hpeq.1 hu'_eq hk hls with hLv | hprf
  · exact const65SpineAt_not_contractedLam hLv hR
  · exact hNoLeft hprf

#print axioms rec65_witness_arity
#print axioms rec65_witnessS_arity
#print axioms short_rec65_not_K_source
#print axioms short_rec65_not_etaK_source
#print axioms NoEtaKStep
#print axioms NoEtaKStar
#print axioms KEtaFree
#print axioms KEtaFreeStar
#print axioms short_rec65_not_derivedIotaU
#print axioms appsSpine_fst_of_eq_foldApps_const
#print axioms foldApps_const_ne_lam_any
#print axioms derivedIotaU_bvar_source_false
#print axioms derivedIotaU_lam_source_false
#print axioms hasConst65ProofRoot_mono
#print axioms peqT_const65_spine
#print axioms parRedT_const65_spine_lt5
#print axioms parRedTStar_const65_spine_lt5
#print axioms parRedTStar_const65_spine_lt5_of_no_proof
#print axioms parRedT_const65_spine
#print axioms parRedTStar_const65_spine
#print axioms parRedTStar_const65_spine_of_no_proof
#print axioms peqT_bvar_step
#print axioms parRedT_bvar_step
#print axioms peqT_contracted_lam
#print axioms parRedT_contracted_lam
#print axioms parRedTStar_contracted_lam
#print axioms parRedTStar_contracted_lam_of_no_proof
#print axioms const65SpineAt_partialRec
#print axioms contractedLam_contracted
#print axioms ctx_get0_ne_letBinding
#print axioms const65SpineAt_not_contractedLam
#print axioms partialRec_not_joinable_of_no_proof
#print axioms partialRec_not_modulo_joinable_of_no_proof

end Rcic.Declarative.F8EtaK
