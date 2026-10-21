import rcic.RcicTypedScopeCheck
import rcic.RcicTypedWeaken
import rcic.RcicTypedLevels

/-!
# IA-rec segment A, infrastructure: building a telescope's typing on the typed root

The forward direction of IA-021 (lane IA-rec, #6290) types the recursor 05 §13 derives from the
typed content admission already carries. Admission states that content per domain (`TelTypedT`,
`RcicTypedEnv.lean:40`), at the family's universe arity. This module turns it into typings of the
objects the recursor type is built from. Nothing here reads a recursor, a minor, or `hT`.

* `hasTyT_levelMono` / `convT_levelMono` (M1): a derivation at universe arity `n` is one at every
  `n' ≥ n`. Only `const`, `delta` and `consts` read the arity. An `AnySort` recursor has arity `n+1`
  over a family typed at `n` (05 §3, §11). Before this module only the untyped judgment
  (`ScmSrcGroupsEnvWf.lean:49`, private) and the copy (`hasTyA_lvlWk`) had it.
* `hasTyT_policyPi_build` (M2): domains typed in their prefix contexts and a body typed under all of
  them give the Π-telescope a typing, at the imax of their sorts (`piSortT`). It is the forward
  direction of a telescope inversion; no row, no environment premise.
* `hasTyT_foldApps_policyLocals` (M4): a head typed at a telescope lifted past that telescope, applied
  to the telescope's own locals, is typed at the telescope's codomain. The family constant at its
  canonical levels (the motive's domain, the major) and the motive variable (the recursor's body) are
  both such heads. Pure syntax: no environment premise.
* `hasTyT_weakenUnderTel`: a block of binders inserted under a telescope prefix, the prefix's domains
  lifted past it (`liftDomsT`). Iterated `hasTyTWeaken`.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) M1: level-context weakening -/

mutual

/-- level-context weakening on the typed judgment: a derivation at universe arity `n` is a derivation
    at every `n' ≥ n`. Only the `const` rule reads the arity (`levelsBounded`). -/
def hasTyT_levelMono {E : ResolvedEnv} {n n' : Nat} (hn : n ≤ n') :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → HasTyT E n' Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A h => .bvar Γ i A h
  | _, _, _, .const Γ r ls m hres hlen hwf => .const Γ r ls m hres hlen (levelsBounded_mono hn ls hwf)
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A u B v (hasTyT_levelMono hn hA) (hasTyT_levelMono hn hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam Γ A u body B (hasTyT_levelMono hn hA) (hasTyT_levelMono hn hbody)
  | _, _, _, .app Γ f a A B hf ha =>
      .app Γ f a A B (hasTyT_levelMono hn hf) (hasTyT_levelMono hn ha)
  | _, _, _, .letE Γ A u value B body hA hv hb =>
      .letE Γ A u value B body (hasTyT_levelMono hn hA) (hasTyT_levelMono hn hv)
        (hasTyT_levelMono hn hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyT_levelMono hn hexp)
  | _, _, _, .conv Γ e A B u h hc =>
      .conv Γ e A B u (hasTyT_levelMono hn h) (convT_levelMono hn hc)

/-- level-context weakening on typed conversion: `delta` and `consts` read the arity. -/
def convT_levelMono {E : ResolvedEnv} {n n' : Nat} (hn : n ≤ n') :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → ConvT E n' Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (hasTyT_levelMono hn h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (convT_levelMono hn h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      .trans Γ a b c A (convT_levelMono hn h1) (convT_levelMono hn h2)
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg =>
      .beta Γ A body arg B u (hasTyT_levelMono hn hA) (hasTyT_levelMono hn hbody)
        (hasTyT_levelMono hn harg)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb =>
      .zeta Γ A value body B u (hasTyT_levelMono hn hA) (hasTyT_levelMono hn hv)
        (hasTyT_levelMono hn hb)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (hasTyT_levelMono hn hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b hres hbody htr hlen (levelsBounded_mono hn ls hwf) (hasTyT_levelMono hn hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T h (hasTyT_levelMono hn hlhs) (hasTyT_levelMono hn hrhs)
  | _, _, _, _, .lit Γ t exp T h hexp => .lit Γ t exp T h (hasTyT_levelMono hn hexp)
  | _, _, _, _, .app Γ f g a b A B h1 h2 =>
      .app Γ f g a b A B (convT_levelMono hn h1) (convT_levelMono hn h2)
  | _, _, _, _, .lam Γ A A' b b' B u hA hb =>
      .lam Γ A A' b b' B u (convT_levelMono hn hA) (convT_levelMono hn hb)
  | _, _, _, _, .pi Γ A A' B B' u v hA hB =>
      .pi Γ A A' B B' u v (convT_levelMono hn hA) (convT_levelMono hn hB)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb =>
      .letE Γ A A' v v' b b' B u (convT_levelMono hn hA) (convT_levelMono hn hv)
        (convT_levelMono hn hb)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h =>
      .consts Γ r ls ls' m hres hlen (levelsBounded_mono hn ls hwf) (levelsBounded_mono hn ls' hwf') h
  | _, _, _, _, .eta Γ f A B h => .eta Γ f A B (hasTyT_levelMono hn h)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyT_levelMono hn hP) (hasTyT_levelMono hn hp) (hasTyT_levelMono hn hq)
  | _, _, _, _, .tyConv Γ a b A A' u h hA =>
      .tyConv Γ a b A A' u (convT_levelMono hn h) (convT_levelMono hn hA)

end

/-- argument lists lift the same way: `n` only bounds the `const` rules inside. -/
def argsTyT_levelMono {E : ResolvedEnv} {n n' : Nat} (hn : n ≤ n') :
    {Γ : LCtx} → {T : Expr Nat} → {as : List (Expr Nat)} →
    ArgsTyT E n Γ T as → ArgsTyT E n' Γ T as
  | _, _, _, .nil l => .nil l
  | _, _, _, .cons A B a as ha tl =>
      .cons A B a as (hasTyT_levelMono hn ha) (argsTyT_levelMono hn tl)

/-- the field typing lifts: every leaf is an `ArgsTyT` or a `HasTyT`. An
    `AnySort` recursor cell runs at `m.arity = fm.arity + 1` (05 §11) on fields
    typed at the family's arity. -/
def fieldsTyT_levelMono {E : ResolvedEnv} {n n' : Nat} (hn : n ≤ n') :
    {idxTel : Nat → Expr Nat} → {Γ : LCtx} → {k : Nat} →
    {fs : List FieldT} → {res : List (Expr Nat)} →
    FieldsTyT E n idxTel Γ k fs res → FieldsTyT E n' idxTel Γ k fs res
  | _, _, _, _, _, .nil Γ k res hres => .nil Γ k res (argsTyT_levelMono hn hres)
  | _, _, _, _, _, .plain Γ k D u fs res hD tl =>
      .plain Γ k D u fs res (hasTyT_levelMono hn hD) (fieldsTyT_levelMono hn tl)
  | _, _, _, _, _, .drec Γ k idx fs res hidx tl =>
      .drec Γ k idx fs res (argsTyT_levelMono hn hidx) (fieldsTyT_levelMono hn tl)
  | _, _, _, _, _, .drecD Γ k D idx fs res hidx tl =>
      .drecD Γ k D idx fs res (argsTyT_levelMono hn hidx) (fieldsTyT_levelMono hn tl)

/-! ## (2) de Bruijn and context bookkeeping -/

/-- instantiating at `k` with the local `c` places past a lift that opened `c + 1` places above `k`
    leaves a lift by `c`: applying a lifted telescope to the local of its next domain. -/
theorem instantiate_bvar_lift_succ (c : Nat) (R : Expr Nat) (k : Nat) :
    instantiate k (.bvar (c + k)) (lift (k + 1) (c + 1) R) = lift k c R := by
  induction R generalizing k with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      have hb := ihb (k + 1)
      simp only [lift, instantiate, iha, Nat.zero_le, if_true]
      exact congrArg _ hb
  | pi a b iha ihb =>
      have hb := ihb (k + 1)
      simp only [lift, instantiate, iha, Nat.zero_le, if_true]
      exact congrArg _ hb
  | letE a v b iha ihv ihb =>
      have hb := ihb (k + 1)
      simp only [lift, instantiate, iha, ihv, Nat.zero_le, if_true]
      exact congrArg _ hb
  | lit t => rfl

theorem length_liftDomsT (c a : Nat) : (ds : List (Expr Nat)) → (liftDomsT c a ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg Nat.succ (length_liftDomsT (c + 1) a ds)

theorem getElem_liftDomsT (a : Nat) : (ds : List (Expr Nat)) → (c j : Nat) → (h : j < ds.length) →
    (liftDomsT c a ds)[j]'(by rw [length_liftDomsT]; exact h) = lift (c + j) a ds[j]
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: ds, c, j + 1, h => by
      show (liftDomsT (c + 1) a ds)[j]'_ = _
      rw [getElem_liftDomsT a ds (c + 1) j (Nat.lt_of_succ_lt_succ h)]
      simp only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]

theorem liftDomsT_zero (c : Nat) : (ds : List (Expr Nat)) → liftDomsT c 0 ds = ds
  | [] => rfl
  | D :: ds => by simp only [liftDomsT, lift_zero, liftDomsT_zero (c + 1) ds]

theorem liftDomsT_succ (c a : Nat) : (ds : List (Expr Nat)) →
    liftDomsT c 1 (liftDomsT c a ds) = liftDomsT c (a + 1) ds
  | [] => rfl
  | D :: ds => by
      simp only [liftDomsT]
      rw [lift_lift_merge 1 a c c (Nat.le_refl _) (Nat.le_add_left c a), liftDomsT_succ (c + 1) a ds]

/-- a lift moves under a telescope: the domains at their own depths, the body past all of them. -/
theorem lift_policyPi (a : Nat) : (ds : List (Expr Nat)) → (c : Nat) → (body : Expr Nat) →
    lift c a (policyPi ds body) = policyPi (liftDomsT c a ds) (lift (c + ds.length) a body)
  | [], c, body => rfl
  | D :: ds, c, body => by
      show Expr.pi (lift c a D) (lift (c + 1) a (policyPi ds body)) = _
      rw [lift_policyPi a ds (c + 1) body]
      simp only [liftDomsT, policyPi, List.length_cons, Nat.add_assoc, Nat.add_comm 1 ds.length]

/-- the context before domain `j + 1` is the one before `j`, with domain `j` innermost. -/
theorem policyPrefixContext_succ (ds : List (Expr Nat)) (j : Nat) (hj : j < ds.length) :
    policyPrefixContext ds (j + 1) = .assumption ds[j] :: policyPrefixContext ds j := by
  simp only [policyPrefixContext, List.take_succ, List.getElem?_eq_getElem hj, Option.toList,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.map_cons]

/-- a telescope split after its first part: the second part's prefix, under the whole first part. -/
theorem policyPrefixContext_append (ps is : List (Expr Nat)) (j : Nat) :
    policyPrefixContext (ps ++ is) (ps.length + j) =
      policyPrefixContext is j ++ policyPrefixContext ps ps.length := by
  simp only [policyPrefixContext, List.take_append_eq_append_take, Nat.add_sub_cancel_left,
    List.take_of_length_le (Nat.le_add_right ps.length j), List.take_length, List.reverse_append,
    List.map_append]

/-- the whole telescope as a context, then `Γ`: the local of the domain with `post` after it is
    `bvar post.length`, at the domain lifted past itself and `post`. -/
theorem lookupType_append_assumption (L : LCtx) (X : Expr Nat) (Γ : LCtx) :
    lookupType (L ++ .assumption X :: Γ) L.length = some (lift 0 (L.length + 1) X) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
      simp only [List.cons_append, List.length_cons]
      rw [lookupType_cons_succ, ih, Option.map_some',
        lift_lift_merge 1 (L.length + 1) 0 0 (Nat.le_refl _) (Nat.zero_le _)]

theorem policyPrefixContext_full_split (pre post : List (Expr Nat)) (d : Expr Nat) (Γ : LCtx) :
    policyPrefixContext (pre ++ d :: post) (pre ++ d :: post).length ++ Γ =
      post.reverse.map LocalDecl.assumption ++
        (.assumption d :: (pre.reverse.map LocalDecl.assumption ++ Γ)) := by
  simp only [policyPrefixContext, List.take_length, List.reverse_append, List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append]

/-- `policyLocals N` reads its `i`-th entry from the outside: the local `N - 1 - i`. -/
theorem policyLocals_getElem? (N i : Nat) (h : i < N) :
    (policyLocals N)[i]? = some (.bvar (N - 1 - i)) := by
  have hr : i < (List.range N).length := by rw [List.length_range]; exact h
  rw [policyLocals, List.getElem?_map, List.getElem?_reverse hr, List.length_range,
    List.getElem?_range (by omega)]
  rfl

theorem policyLocals_length (N : Nat) : (policyLocals N).length = N := by
  simp only [policyLocals, List.length_map, List.length_reverse, List.length_range]

/-- closedness restricts from a fresh-ref extension to its base: a recursor cell's prefix is closed
    when the environment after the recursor is. -/
theorem envClosed_of_extend_fresh {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (h : EnvClosed (extendEnv E r m)) (hfr : E.members r = none) : EnvClosed E := by
  intro r' m' hm'
  have hne : r' ≠ r := fun he => by rw [he, hfr] at hm'; exact Option.noConfusion hm'
  exact h r' m' (by rw [members_extendEnv_ne E r m hne]; exact hm')

/-! ## (3) M4: a telescope-typed head applied to the telescope's locals -/

/-- the induction behind M4: `pre` already applied, `post` still to go. -/
def hasTyT_foldApps_policyLocals_go {E : ResolvedEnv} {n : Nat} (ds : List (Expr Nat)) (Γ : LCtx)
    (B H : Expr Nat) :
    (post pre : List (Expr Nat)) → ds = pre ++ post →
    HasTyT E n (policyPrefixContext ds ds.length ++ Γ)
      (foldApps H ((policyLocals ds.length).take pre.length)) (lift 0 post.length (policyPi post B)) →
    HasTyT E n (policyPrefixContext ds ds.length ++ Γ) (foldApps H (policyLocals ds.length)) B
  | [], pre, hds, h => by
      have hpre : pre = ds := by rw [hds, List.append_nil]
      have htake : (policyLocals ds.length).take pre.length = policyLocals ds.length := by
        rw [hpre]; exact List.take_of_length_le (Nat.le_of_eq (policyLocals_length _))
      rw [htake] at h
      simpa only [List.length_nil, policyPi, lift_zero] using h
  | d :: post, pre, hds, h => by
      have hN : ds.length = pre.length + 1 + post.length := by
        rw [hds]; simp only [List.length_append, List.length_cons]; omega
      have hlook : lookupType (policyPrefixContext ds ds.length ++ Γ) post.length =
          some (lift 0 (post.length + 1) d) := by
        have hsplit := policyPrefixContext_full_split pre post d Γ
        rw [← hds] at hsplit
        rw [hsplit]
        have hl : (post.reverse.map LocalDecl.assumption).length = post.length := by
          simp only [List.length_map, List.length_reverse]
        have := lookupType_append_assumption (post.reverse.map LocalDecl.assumption) d
          (pre.reverse.map LocalDecl.assumption ++ Γ)
        rw [hl] at this
        exact this
      have hx : HasTyT E n (policyPrefixContext ds ds.length ++ Γ) (.bvar post.length)
          (lift 0 (post.length + 1) d) := .bvar _ _ _ hlook
      have h' : HasTyT E n (policyPrefixContext ds ds.length ++ Γ)
          (foldApps H ((policyLocals ds.length).take pre.length))
          (.pi (lift 0 (post.length + 1) d) (lift 1 (post.length + 1) (policyPi post B))) := by
        simpa only [List.length_cons, policyPi, lift] using h
      have happ := HasTyT.app _ _ _ _ _ h' hx
      have hinst : instantiate0 (.bvar post.length) (lift 1 (post.length + 1) (policyPi post B)) =
          lift 0 post.length (policyPi post B) := by
        have := instantiate_bvar_lift_succ post.length (policyPi post B) 0
        simpa only [Nat.add_zero, Nat.zero_add] using this
      rw [hinst] at happ
      have htake : (policyLocals ds.length).take (pre.length + 1) =
          (policyLocals ds.length).take pre.length ++ [.bvar post.length] := by
        rw [List.take_succ, policyLocals_getElem? ds.length pre.length (by omega)]
        simp only [Option.toList]
        congr 3
        omega
      have hstep : HasTyT E n (policyPrefixContext ds ds.length ++ Γ)
          (foldApps H ((policyLocals ds.length).take (pre ++ [d]).length))
          (lift 0 post.length (policyPi post B)) := by
        rw [List.length_append, List.length_singleton, htake, foldApps_snoc]
        exact happ
      exact hasTyT_foldApps_policyLocals_go ds Γ B H post (pre ++ [d])
        (by rw [hds, List.append_assoc, List.singleton_append]) hstep

/-- M4: a head typed at a telescope lifted past it, applied to the telescope's own locals
    `[bvar (N-1), …, bvar 0]`, is typed at the telescope's codomain. No environment premise. -/
def hasTyT_foldApps_policyLocals {E : ResolvedEnv} {n : Nat} (ds : List (Expr Nat)) (Γ : LCtx)
    (B H : Expr Nat)
    (hH : HasTyT E n (policyPrefixContext ds ds.length ++ Γ) H (lift 0 ds.length (policyPi ds B))) :
    HasTyT E n (policyPrefixContext ds ds.length ++ Γ) (foldApps H (policyLocals ds.length)) B :=
  hasTyT_foldApps_policyLocals_go ds Γ B H ds [] (List.nil_append ds).symm
    (by simpa only [List.length_nil, List.take_zero, foldApps] using hH)

/-! ## (4) M2: a telescope typed from its domains -/

/-- the sort of a Π-telescope: the imax of its domains' sorts with the body's. -/
def piSortT : (k : Nat) → (Fin k → Level) → Level → Level
  | 0, _, w => w
  | k + 1, ls, w => .imax (ls 0) (piSortT k (fun i => ls i.succ) w)

/-- M2: every domain sort-typed in its prefix context, and the body sort-typed under all of them,
    give the telescope a typing at `piSortT`. The forward direction of a telescope inversion. -/
theorem hasTyT_policyPi_build {E : ResolvedEnv} {n : Nat} :
    (ds : List (Expr Nat)) → {Γ : LCtx} → {body : Expr Nat} → {w : Level} →
    (ls : Fin ds.length → Level) →
    (∀ i : Fin ds.length,
      Nonempty (HasTyT E n (policyPrefixContext ds i.val ++ Γ) ds[i.val] (.sort (ls i)))) →
    Nonempty (HasTyT E n (policyPrefixContext ds ds.length ++ Γ) body (.sort w)) →
    Nonempty (HasTyT E n Γ (policyPi ds body) (.sort (piSortT ds.length ls w)))
  | [], Γ, body, w, _, _, hb => by simpa only [policyPrefixContext, List.take_nil, List.reverse_nil,
      List.map_nil, List.nil_append, policyPi, piSortT, List.length_nil] using hb
  | A :: ds, Γ, body, w, ls, hd, hb => by
      have hctx : ∀ j, policyPrefixContext (A :: ds) (j + 1) ++ Γ =
          policyPrefixContext ds j ++ (.assumption A :: Γ) := by
        intro j
        have h := policyPrefixContext_append [A] ds j
        simp only [List.length_singleton, List.singleton_append] at h
        rw [Nat.add_comm, h]
        simp [policyPrefixContext]
      obtain ⟨hA⟩ := hd ⟨0, Nat.succ_pos _⟩
      have hA' : HasTyT E n Γ A (.sort (ls ⟨0, Nat.succ_pos _⟩)) := by
        simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
          List.nil_append, List.getElem_cons_zero] using hA
      have hb' : Nonempty (HasTyT E n (policyPrefixContext ds ds.length ++ (.assumption A :: Γ))
          body (.sort w)) := by
        rw [← hctx]; exact hb
      obtain ⟨hB⟩ := hasTyT_policyPi_build ds (Γ := .assumption A :: Γ) (fun i => ls i.succ)
        (fun i => by
          obtain ⟨hi⟩ := hd i.succ
          have hi' : HasTyT E n (policyPrefixContext (A :: ds) (i.val + 1) ++ Γ) ds[i.val]
              (.sort (ls i.succ)) := hi
          rw [hctx] at hi'
          exact ⟨hi'⟩)
        hb'
      exact ⟨.pi Γ A _ (policyPi ds body) _ hA' hB⟩

/-! ## (5) a block of binders under a telescope prefix -/

/-- inserting one binder just under a telescope prefix lifts the prefix's domains past it. -/
theorem insertAt_policyPrefixContext (d : LocalDecl) (Γ : LCtx) (ds : List (Expr Nat)) :
    (j : Nat) → j ≤ ds.length →
    insertAt d j (policyPrefixContext ds j ++ Γ) =
      policyPrefixContext (liftDomsT 0 1 ds) j ++ (d :: Γ)
  | 0, _ => rfl
  | j + 1, hj => by
      have hj' : j < ds.length := hj
      have hjl : j < (liftDomsT 0 1 ds).length := by rw [length_liftDomsT]; exact hj'
      rw [policyPrefixContext_succ ds j hj', policyPrefixContext_succ (liftDomsT 0 1 ds) j hjl]
      simp only [List.cons_append, insertAt_succ_cons, liftDecl]
      rw [insertAt_policyPrefixContext d Γ ds j (Nat.le_of_lt hj'),
        getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add]

/-- a block `Δ` (innermost first) inserted under the first `j` domains of a telescope: the term and
    its type lift by `Δ.length` at `j`, the prefix's domains by `Δ.length` at their own depths. -/
def hasTyT_weakenUnderTel {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (ds : List (Expr Nat))
    (j : Nat) (hj : j ≤ ds.length) {Γ : LCtx} :
    (Δ : LCtx) → {e A : Expr Nat} → HasTyT E n (policyPrefixContext ds j ++ Γ) e A →
    HasTyT E n (policyPrefixContext (liftDomsT 0 Δ.length ds) j ++ (Δ ++ Γ))
      (lift j Δ.length e) (lift j Δ.length A)
  | [], e, A, h => by
      simpa only [List.length_nil, liftDomsT_zero, lift_zero, List.nil_append] using h
  | d :: Δ, e, A, h => by
      have ih := hasTyT_weakenUnderTel hcl ds j hj Δ h
      have hw := hasTyTWeaken d hcl (c := j) ih
      rw [insertAt_policyPrefixContext d (Δ ++ Γ) (liftDomsT 0 Δ.length ds) j
          (by rw [length_liftDomsT]; exact hj),
        liftDomsT_succ, lift_lift_merge 1 Δ.length j j (Nat.le_refl _) (Nat.le_add_left _ _),
        lift_lift_merge 1 Δ.length j j (Nat.le_refl _) (Nat.le_add_left _ _)] at hw
      simpa only [List.length_cons, List.cons_append] using hw

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyT_levelMono
#print axioms Rcic.Declarative.convT_levelMono
#print axioms Rcic.Declarative.instantiate_bvar_lift_succ
#print axioms Rcic.Declarative.lift_policyPi
#print axioms Rcic.Declarative.policyPrefixContext_append
#print axioms Rcic.Declarative.hasTyT_foldApps_policyLocals
#print axioms Rcic.Declarative.hasTyT_policyPi_build
#print axioms Rcic.Declarative.hasTyT_weakenUnderTel
