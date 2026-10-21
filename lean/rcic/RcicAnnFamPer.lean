import rcic.RcicAnnFam

/-!
# M2-f (3b) — the `fam` clause's metatheory below the relation

What the clause's symmetry, transitivity and transport consume, stated with no
reference to the relation (`RcicAnnLR`): every fact about the relation's own
data arrives as a hypothesis, so the relation's modules discharge them from
their induction hypotheses.

(0) Levels: `isZero` is `=ₙ 0` (moved here from `RcicAnnLRConv`); `=ₙ` on
    level lists is an equivalence.
(1) Rigid telescopes: a Π-telescope whose body is a sort or a constant-headed
    spine keeps its Π-count under instantiation of variables and of levels, so
    whether `applyTelA xs T` is a Π is decided by `xs.length` alone
    (`applyTelA_rigid`). A family's type is one (body `sort u₀`), and so is every
    constructor's (body headed by its family, `memberFamRefA`).
(2) The Prop boundary of a family application is read off the family's result
    sort: `IsPropTy (I ls xs) ↔ ls.length = arity ∧ xs.length = #Π ∧
    isZero (instLevel ls u₀)` (`isPropTy_famApp_iff`), the same at `=ₙ` level
    lists and index lists of equal length (`isPropTy_famApp_congr`).
(3) Term chains retype along a type conversion.
(4) The walk calculus: walks flip and compose, position by position, given what
    each position needs.
(5) The fixed point: the carrier moves along related indices (`lfpWA_carrier`),
    and the fixed point is symmetric and transitive (`lfpWA_symm`, `lfpWA_trans`),
    given the per-position facts as hypotheses at every world of the clause
    (R-NoFunRec-1 step 1 (1a): the fixed point ranges over worlds, and so do these
    inductions).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) levels -/

theorem eval_of_isZero : (l : Level) → isZero l = true → ∀ ρ : Nat → Option Nat, eval ρ l = some 0
  | .zero, _, _ => rfl
  | .succ _, h, _ => by simp [isZero] at h
  | .param _, h, _ => by simp [isZero] at h
  | .max a b, h, ρ => by
      simp only [isZero, Bool.and_eq_true] at h
      rw [eval, eval_of_isZero a h.1 ρ, eval_of_isZero b h.2 ρ]
      rfl
  | .imax a b, h, ρ => by
      simp only [isZero] at h
      rw [eval, eval_of_isZero b h ρ]
      rfl

theorem eval_max_zero {ρ : Nat → Option Nat} {a b : Level} (h : eval ρ (.max a b) = some 0) :
    eval ρ a = some 0 ∧ eval ρ b = some 0 := by
  simp only [eval] at h
  cases hx : eval ρ a with
  | none => rw [hx] at h; simp at h
  | some x =>
    cases hy : eval ρ b with
    | none => rw [hx, hy] at h; simp at h
    | some y =>
      rw [hx, hy] at h
      have hm : max x y = 0 := Option.some.inj h
      have hx0 := Nat.le_max_left x y
      have hy0 := Nat.le_max_right x y
      rw [hm] at hx0 hy0
      have ex : x = 0 := Nat.eq_zero_of_le_zero hx0
      have ey : y = 0 := Nat.eq_zero_of_le_zero hy0
      subst ex; subst ey
      exact ⟨by first | rfl | exact hx, by first | rfl | exact hy⟩

theorem eval_imax_zero {ρ : Nat → Option Nat} {a b : Level} (h : eval ρ (.imax a b) = some 0) :
    eval ρ b = some 0 := by
  simp only [eval] at h
  cases hy : eval ρ b with
  | none => rw [hy] at h; simp at h
  | some y =>
    rw [hy] at h
    by_cases h0 : y = 0
    · subst h0; first | rfl | exact hy
    · have h' : ((eval ρ a).map fun x => max x y) = some 0 := by
        have h'' : (if y = 0 then some 0 else (eval ρ a).map fun x => max x y) = some 0 := h
        rwa [if_neg h0] at h''
      cases hx : eval ρ a with
      | none => rw [hx] at h'; simp at h'
      | some x =>
        rw [hx] at h'
        have hm : max x y = 0 := Option.some.inj h'
        have hy0 := Nat.le_max_right x y
        rw [hm] at hy0
        exact absurd (Nat.eq_zero_of_le_zero hy0) h0

theorem isZero_of_eqN_zero : (l : Level) → eqN l .zero → isZero l = true
  | .zero, _ => rfl
  | .succ l, h => absurd h (not_eqN_succ_zero l)
  | .param _, h => by have h0 := h (fun _ => some 1); simp [eval] at h0
  | .max a b, h => by
      have ha : eqN a .zero := fun ρ => (eval_max_zero (h ρ)).1
      have hb : eqN b .zero := fun ρ => (eval_max_zero (h ρ)).2
      simp only [isZero, isZero_of_eqN_zero a ha, isZero_of_eqN_zero b hb, Bool.and_self]
  | .imax a b, h => by
      have hb : eqN b .zero := fun ρ => eval_imax_zero (h ρ)
      simp only [isZero, isZero_of_eqN_zero b hb]

theorem isZero_iff_eqN_zero (l : Level) : isZero l = true ↔ eqN l .zero :=
  ⟨fun h ρ => eval_of_isZero l h ρ, isZero_of_eqN_zero l⟩

theorem isZero_eqN {v v' : Level} (h : eqN v v') : isZero v = isZero v' := by
  cases hv : isZero v <;> cases hv' : isZero v' <;> try rfl
  · have : isZero v = true :=
      (isZero_iff_eqN_zero v).2 (eqNA_trans h ((isZero_iff_eqN_zero v').1 hv'))
    rw [hv] at this; exact absurd this (by decide)
  · have : isZero v' = true :=
      (isZero_iff_eqN_zero v').2 (eqNA_trans (eqNA_symm h) ((isZero_iff_eqN_zero v).1 hv))
    rw [hv'] at this; exact absurd this (by decide)

/-- whether a pi is a proposition is read off its annotation up to `=ₙ`. -/
theorem isPropTy_pi_eqN {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {D D' C C' : ExprA}
    {u v u' v' : Level} (hv : eqN v v') :
    IsPropTy E I Γ (.pi D u C v) ↔ IsPropTy E I Γ (.pi D' u' C' v') := by
  rw [isPropTy_pi_iff, isPropTy_pi_iff, isZero_eqN hv]



/-! ## (1) rigid telescopes -/

/-- the body of a Π-telescope is RIGID: a sort or a constant-headed spine. Neither
    instantiation of variables nor of levels turns it into a Π. -/
def RigidBodyA (e : ExprA) : Prop :=
  (∃ l, e = .sort l) ∨ (∃ r ls, (appsSpineA e).1 = .const r ls)

theorem appsSpineA_instantiateA_head : (e : ExprA) → (k : Nat) → (a : ExprA) → {r : Nat} →
    {ls : List Level} → (appsSpineA e).1 = .const r ls →
    (appsSpineA (instantiateA k a e)).1 = .const r ls
  | .const _ _, _, _, _, _, h => h
  | .app f _, k, a, _, _, h => by
      rw [appsSpineA_app_fst] at h
      show (appsSpineA (.app (instantiateA k a f) _)).1 = _
      rw [appsSpineA_app_fst]
      exact appsSpineA_instantiateA_head f k a h
  | .bvar _, _, _, _, _, h => ExprA.noConfusion h
  | .sort _, _, _, _, _, h => ExprA.noConfusion h
  | .lam _ _ _, _, _, _, _, h => ExprA.noConfusion h
  | .pi _ _ _ _, _, _, _, _, h => ExprA.noConfusion h
  | .letE _ _ _, _, _, _, _, h => ExprA.noConfusion h
  | .lit _, _, _, _, _, h => ExprA.noConfusion h

theorem appsSpineA_instantiateLevelsA_head (lsF : List Level) : (e : ExprA) → {r : Nat} →
    {ls : List Level} → (appsSpineA e).1 = .const r ls →
    (appsSpineA (instantiateLevelsA lsF e)).1 = .const r (ls.map (instLevel lsF))
  | .const _ _, _, _, h => by
      injection h with h1 h2
      subst h1; subst h2; rfl
  | .app f _, _, _, h => by
      rw [appsSpineA_app_fst] at h
      show (appsSpineA (.app (instantiateLevelsA lsF f) _)).1 = _
      rw [appsSpineA_app_fst]
      exact appsSpineA_instantiateLevelsA_head lsF f h
  | .bvar _, _, _, h => ExprA.noConfusion h
  | .sort _, _, _, h => ExprA.noConfusion h
  | .lam _ _ _, _, _, h => ExprA.noConfusion h
  | .pi _ _ _ _, _, _, h => ExprA.noConfusion h
  | .letE _ _ _, _, _, h => ExprA.noConfusion h
  | .lit _, _, _, h => ExprA.noConfusion h

theorem rigid_instantiateA : (e : ExprA) → (k : Nat) → (a : ExprA) → RigidBodyA (piBodyA e) →
    RigidBodyA (piBodyA (instantiateA k a e)) ∧
      (piDomsA (instantiateA k a e)).length = (piDomsA e).length
  | .pi _ _ B _, k, a, h => by
      have ih := rigid_instantiateA B (k + 1) (liftA 0 1 a) h
      exact ⟨ih.1, by simp only [instantiateA, piDomsA, List.length_cons, ih.2]⟩
  | .sort l, _, _, _ => ⟨Or.inl ⟨l, rfl⟩, rfl⟩
  | .const r ls, _, _, _ => ⟨Or.inr ⟨r, ls, rfl⟩, rfl⟩
  | .app f x, k, a, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ⟨Or.inr ⟨r, ls, appsSpineA_instantiateA_head (.app f x) k a hr⟩, rfl⟩
  | .bvar _, _, _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .lam _ _ _, _, _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .letE _ _ _, _, _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .lit _, _, _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr

theorem rigid_instantiateLevelsA (lsF : List Level) : (e : ExprA) → RigidBodyA (piBodyA e) →
    RigidBodyA (piBodyA (instantiateLevelsA lsF e)) ∧
      (piDomsA (instantiateLevelsA lsF e)).length = (piDomsA e).length
  | .pi _ _ B _, h => by
      have ih := rigid_instantiateLevelsA lsF B h
      exact ⟨ih.1, by simp only [instantiateLevelsA, piDomsA, List.length_cons, ih.2]⟩
  | .sort l, _ => ⟨Or.inl ⟨instLevel lsF l, rfl⟩, rfl⟩
  | .const r ls, _ => ⟨Or.inr ⟨r, ls.map (instLevel lsF), rfl⟩, rfl⟩
  | .app f x, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ⟨Or.inr ⟨r, _, appsSpineA_instantiateLevelsA_head lsF (.app f x) hr⟩, rfl⟩
  | .bvar _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .lam _ _ _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .letE _ _ _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr
  | .lit _, h => by
      rcases h with ⟨l, hl⟩ | ⟨r, ls, hr⟩
      · exact ExprA.noConfusion hl
      · exact ExprA.noConfusion hr

/-- on a rigid telescope, `applyTelA xs` is a Π exactly when `xs` is shorter than
    the telescope. -/
theorem applyTelA_rigid : (xs : List ExprA) → (T : ExprA) → RigidBodyA (piBodyA T) →
    ((∃ D u C v, applyTelA xs T = some (.pi D u C v)) ↔ xs.length < (piDomsA T).length)
  | [], .pi _ _ _ _, _ => ⟨fun _ => by simp [piDomsA], fun _ => ⟨_, _, _, _, rfl⟩⟩
  | [], .sort _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .const _ _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .app _ _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .bvar _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .lam _ _ _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .letE _ _ _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], .lit _, _ =>
      ⟨fun ⟨_, _, _, _, h⟩ => ExprA.noConfusion (Option.some.inj h), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | x :: xs, .pi _ _ B _, h => by
      have hr := rigid_instantiateA B 0 x h
      have ih := applyTelA_rigid xs (instantiate0A x B) hr.1
      show (∃ D u C v, applyTelA xs (instantiate0A x B) = some (.pi D u C v)) ↔ _
      rw [ih]
      show xs.length < (piDomsA (instantiateA 0 x B)).length ↔ xs.length + 1 < (piDomsA B).length + 1
      rw [hr.2]
      exact Nat.succ_lt_succ_iff.symm
  | _ :: _, .sort _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .const _ _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .app _ _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .bvar _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .lam _ _ _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .letE _ _ _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, .lit _, _ => ⟨fun ⟨_, _, _, _, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_lt_zero _)⟩

/-- two rigid telescopes of one Π-count: a Π after `xs` gives a Π after any `xs'` of
    the same length. -/
theorem applyTelA_pi_transfer {T T' : ExprA} (hT : RigidBodyA (piBodyA T))
    (hT' : RigidBodyA (piBodyA T')) (hlen : (piDomsA T).length = (piDomsA T').length)
    {xs xs' : List ExprA} (hxs : xs.length = xs'.length) {D : ExprA} {u : Level} {C : ExprA}
    {v : Level} (h : applyTelA xs T = some (.pi D u C v)) :
    ∃ D' u' C' v', applyTelA xs' T' = some (.pi D' u' C' v') :=
  (applyTelA_rigid xs' T' hT').2 (by
    rw [← hxs, ← hlen]; exact (applyTelA_rigid xs T hT).1 ⟨D, u, C, v, h⟩)

/-- the same telescope at two level lists. -/
theorem applyTelA_pi_transfer_levels {T₀ : ExprA} (hT₀ : RigidBodyA (piBodyA T₀))
    (ls ls' : List Level) {xs xs' : List ExprA} (hxs : xs.length = xs'.length) {D : ExprA}
    {u : Level} {C : ExprA} {v : Level} (h : applyTelA xs (instantiateLevelsA ls T₀) = some (.pi D u C v)) :
    ∃ D' u' C' v', applyTelA xs' (instantiateLevelsA ls' T₀) = some (.pi D' u' C' v') :=
  applyTelA_pi_transfer (rigid_instantiateLevelsA ls T₀ hT₀).1 (rigid_instantiateLevelsA ls' T₀ hT₀).1
    (by rw [(rigid_instantiateLevelsA ls T₀ hT₀).2, (rigid_instantiateLevelsA ls' T₀ hT₀).2]) hxs h

/-- a constructor's telescope is rigid: its body is headed by its family. -/
theorem rigid_of_memberFamRefA {cm : CheckedMemberA} {r : Nat} (h : memberFamRefA cm = some r) :
    RigidBodyA (piBodyA cm.mtypeA) := by
  obtain ⟨ls, hls⟩ := spineHeadRefA_some h
  exact Or.inr ⟨r, ls, hls⟩

/-- the normed telescope is rigid (R-NoDeltaRec-4d-iii): `none` collapses to the stored type;
    `some` is a `ctorTypeA` build whose body is the family application (`EnvNormCtorTypeA`). -/
theorem rigid_of_memberFamRefA_getD {E : ResolvedEnvA} {c : Nat} {cm : CheckedMemberA} {r : Nat}
    (hN : EnvNormCtorTypeA E) (hm : E.members c = some cm) (hk : cm.mclass = .constructorM)
    (h : memberFamRefA cm = some r) :
    RigidBodyA (piBodyA (cm.normA.getD cm.mtypeA)) := by
  cases hn : cm.normA with
  | none =>
      show RigidBodyA (piBodyA (Option.getD none cm.mtypeA))
      rw [Option.getD_none]; exact rigid_of_memberFamRefA h
  | some T =>
      obtain ⟨f', ls', hTe⟩ := hN _ _ hm hk T hn
      exact Or.inr ⟨f', ls', hTe⟩

/-- a family's telescope is rigid: its body is a sort. -/
theorem rigid_of_sortBody {T : ExprA} {u₀ : Level} (h : piBodyA T = .sort u₀) :
    RigidBodyA (piBodyA T) := Or.inl ⟨u₀, h⟩

/-- on a rigid telescope, `applyTelA xs` succeeds exactly when `xs` is no longer than
    the telescope (M2-f (3c)). -/
theorem applyTelA_rigid_some : (xs : List ExprA) → (T : ExprA) → RigidBodyA (piBodyA T) →
    ((∃ R, applyTelA xs T = some R) ↔ xs.length ≤ (piDomsA T).length)
  | [], T, _ => ⟨fun _ => Nat.zero_le _, fun _ => ⟨T, rfl⟩⟩
  | x :: xs, .pi _ _ B _, h => by
      have hr := rigid_instantiateA B 0 x h
      have ih := applyTelA_rigid_some xs (instantiate0A x B) hr.1
      show (∃ R, applyTelA xs (instantiate0A x B) = some R) ↔ _
      rw [ih]
      show xs.length ≤ (piDomsA (instantiateA 0 x B)).length ↔ xs.length + 1 ≤ (piDomsA B).length + 1
      rw [hr.2]
      exact Nat.succ_le_succ_iff.symm
  | _ :: _, .sort _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .const _ _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .app _ _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .bvar _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .lam _ _ _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .letE _ _ _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
  | _ :: _, .lit _, _ => ⟨fun ⟨_, h⟩ => Option.noConfusion h, fun h => absurd h (Nat.not_succ_le_zero _)⟩

/-- the same rigid telescope at two level lists: success after `xs` gives success after
    any `xs'` of the same length. -/
theorem applyTelA_some_transfer_levels {T₀ : ExprA} (hT₀ : RigidBodyA (piBodyA T₀))
    (ls ls' : List Level) {xs xs' : List ExprA} (hxs : xs.length = xs'.length) {R : ExprA}
    (h : applyTelA xs (instantiateLevelsA ls T₀) = some R) :
    ∃ R', applyTelA xs' (instantiateLevelsA ls' T₀) = some R' :=
  (applyTelA_rigid_some xs' _ (rigid_instantiateLevelsA ls' T₀ hT₀).1).2 (by
    rw [← hxs, (rigid_instantiateLevelsA ls' T₀ hT₀).2, ← (rigid_instantiateLevelsA ls T₀ hT₀).2]
    exact (applyTelA_rigid_some xs _ (rigid_instantiateLevelsA ls T₀ hT₀).1).1 ⟨R, h⟩)

/-- a rigid telescope after two parameter lists of one length (at two level lists): a Π
    after a prefix of the first is a Π after any prefix of the same length of the
    second (the cross move's telescopes, M2-f (3c)). -/
theorem applyTelA_pi_cross {T₀ : ExprA} (hT₀ : RigidBodyA (piBodyA T₀)) {ls ls' : List Level}
    {ps ps' : List ExprA} (hps : ps.length = ps'.length) {T T' : ExprA}
    (hT : applyTelA ps (instantiateLevelsA ls T₀) = some T)
    (hT' : applyTelA ps' (instantiateLevelsA ls' T₀) = some T')
    {pre pre' : List ExprA} (hpre : pre.length = pre'.length) {D : ExprA} {u : Level} {C : ExprA}
    {v : Level} (h : applyTelA pre T = some (.pi D u C v)) :
    ∃ D' u' C' v', applyTelA pre' T' = some (.pi D' u' C' v') := by
  have h1 : applyTelA (ps ++ pre) (instantiateLevelsA ls T₀) = some (.pi D u C v) := by
    rw [applyTelA_append, hT]; exact h
  obtain ⟨D', u', C', v', h2⟩ := applyTelA_pi_transfer_levels hT₀ ls ls' (xs' := ps' ++ pre')
    (by simp only [List.length_append, hps, hpre]) h1
  rw [applyTelA_append, hT'] at h2
  exact ⟨D', u', C', v', h2⟩

/-- the same, for success. -/
theorem applyTelA_some_cross {T₀ : ExprA} (hT₀ : RigidBodyA (piBodyA T₀)) {ls ls' : List Level}
    {ps ps' : List ExprA} (hps : ps.length = ps'.length) {T T' : ExprA}
    (hT : applyTelA ps (instantiateLevelsA ls T₀) = some T)
    (hT' : applyTelA ps' (instantiateLevelsA ls' T₀) = some T')
    {pre pre' : List ExprA} (hpre : pre.length = pre'.length) {R : ExprA}
    (h : applyTelA pre T = some R) : ∃ R', applyTelA pre' T' = some R' := by
  have h1 : applyTelA (ps ++ pre) (instantiateLevelsA ls T₀) = some R := by
    rw [applyTelA_append, hT]; exact h
  obtain ⟨R', h2⟩ := applyTelA_some_transfer_levels hT₀ ls ls' (xs' := ps' ++ pre')
    (by simp only [List.length_append, hps, hpre]) h1
  rw [applyTelA_append, hT'] at h2
  exact ⟨R', h2⟩

/-! ## (2) the Prop boundary of a family application -/

theorem piBodyA_instantiateA_sort : (e : ExprA) → (k : Nat) → (a : ExprA) → {l : Level} →
    piBodyA e = .sort l → piBodyA (instantiateA k a e) = .sort l
  | .pi _ _ B _, k, a, _, h => piBodyA_instantiateA_sort B (k + 1) (liftA 0 1 a) h
  | .sort _, _, _, _, h => h
  | .const _ _, _, _, _, h => ExprA.noConfusion h
  | .app _ _, _, _, _, h => ExprA.noConfusion h
  | .bvar _, _, _, _, h => ExprA.noConfusion h
  | .lam _ _ _, _, _, _, h => ExprA.noConfusion h
  | .letE _ _ _, _, _, _, h => ExprA.noConfusion h
  | .lit _, _, _, _, h => ExprA.noConfusion h

theorem piBodyA_instantiateLevelsA_sort (lsF : List Level) : (e : ExprA) → {l : Level} →
    piBodyA e = .sort l → piBodyA (instantiateLevelsA lsF e) = .sort (instLevel lsF l)
  | .pi _ _ B _, _, h => piBodyA_instantiateLevelsA_sort lsF B h
  | .sort _, _, h => by
      injection h with h
      subst h; rfl
  | .const _ _, _, h => ExprA.noConfusion h
  | .app _ _, _, h => ExprA.noConfusion h
  | .bvar _, _, h => ExprA.noConfusion h
  | .lam _ _ _, _, h => ExprA.noConfusion h
  | .letE _ _ _, _, h => ExprA.noConfusion h
  | .lit _, _, h => ExprA.noConfusion h

/-- on a sort-bodied telescope, `applyTelA` is the sort exactly at full length, a Π
    below it, and `none` above it. -/
theorem applyTelA_sortBody : (xs : List ExprA) → (T : ExprA) → {l : Level} → piBodyA T = .sort l →
    ∀ {R : ExprA}, applyTelA xs T = some R →
      (xs.length = (piDomsA T).length ∧ R = .sort l) ∨
      (xs.length < (piDomsA T).length ∧ ∃ D u C v, R = .pi D u C v)
  | [], .pi D u C v, _, _, R, h => by
      injection h with h
      subst h
      exact Or.inr ⟨by simp [piDomsA], D, u, C, v, rfl⟩
  | [], .sort l', _, hb, R, h => by
      injection h with h
      subst h
      exact Or.inl ⟨rfl, hb⟩
  | [], .const _ _, _, hb, _, _ => ExprA.noConfusion hb
  | [], .app _ _, _, hb, _, _ => ExprA.noConfusion hb
  | [], .bvar _, _, hb, _, _ => ExprA.noConfusion hb
  | [], .lam _ _ _, _, hb, _, _ => ExprA.noConfusion hb
  | [], .letE _ _ _, _, hb, _, _ => ExprA.noConfusion hb
  | [], .lit _, _, hb, _, _ => ExprA.noConfusion hb
  | x :: xs, .pi _ _ B _, l, hb, R, h => by
      have hb' : piBodyA (instantiate0A x B) = .sort l := piBodyA_instantiateA_sort B 0 x hb
      have hlen := (rigid_instantiateA B 0 x (Or.inl ⟨l, hb⟩)).2
      rcases applyTelA_sortBody xs (instantiate0A x B) hb' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, h2⟩
        show xs.length + 1 = (piDomsA B).length + 1
        rw [h1]; exact congrArg (· + 1) hlen
      · refine Or.inr ⟨?_, h2⟩
        show xs.length + 1 < (piDomsA B).length + 1
        exact Nat.succ_lt_succ (by rw [← hlen]; exact h1)
  | _ :: _, .sort _, _, _, _, h => Option.noConfusion h
  | _ :: _, .const _ _, _, hb, _, _ => ExprA.noConfusion hb
  | _ :: _, .app _ _, _, hb, _, _ => ExprA.noConfusion hb
  | _ :: _, .bvar _, _, hb, _, _ => ExprA.noConfusion hb
  | _ :: _, .lam _ _ _, _, hb, _, _ => ExprA.noConfusion hb
  | _ :: _, .letE _ _ _, _, hb, _, _ => ExprA.noConfusion hb
  | _ :: _, .lit _, _, hb, _, _ => ExprA.noConfusion hb

theorem applyTelA_sortBody_full : (xs : List ExprA) → (T : ExprA) → {l : Level} → piBodyA T = .sort l →
    xs.length = (piDomsA T).length → applyTelA xs T = some (.sort l)
  | [], .sort l', _, hb, _ => by
      have hb' : ExprA.sort l' = ExprA.sort _ := hb
      injection hb' with e
      subst e; rfl
  | [], .pi _ _ _ _, _, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | [], .const _ _, _, hb, _ => ExprA.noConfusion hb
  | [], .app _ _, _, hb, _ => ExprA.noConfusion hb
  | [], .bvar _, _, hb, _ => ExprA.noConfusion hb
  | [], .lam _ _ _, _, hb, _ => ExprA.noConfusion hb
  | [], .letE _ _ _, _, hb, _ => ExprA.noConfusion hb
  | [], .lit _, _, hb, _ => ExprA.noConfusion hb
  | x :: xs, .pi _ _ B _, l, hb, h => by
      have hb' : piBodyA (instantiate0A x B) = .sort l := piBodyA_instantiateA_sort B 0 x hb
      have hlen := (rigid_instantiateA B 0 x (Or.inl ⟨l, hb⟩)).2
      show applyTelA xs (instantiate0A x B) = _
      refine applyTelA_sortBody_full xs (instantiate0A x B) hb' ?_
      show xs.length = (piDomsA (instantiateA 0 x B)).length
      rw [hlen]
      exact Nat.succ.inj h
  | _ :: _, .sort _, _, _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: _, .const _ _, _, hb, _ => ExprA.noConfusion hb
  | _ :: _, .app _ _, _, hb, _ => ExprA.noConfusion hb
  | _ :: _, .bvar _, _, hb, _ => ExprA.noConfusion hb
  | _ :: _, .lam _ _ _, _, hb, _ => ExprA.noConfusion hb
  | _ :: _, .letE _ _ _, _, hb, _ => ExprA.noConfusion hb
  | _ :: _, .lit _, _, hb, _ => ExprA.noConfusion hb

/-- induction from the right end of a list. -/
theorem listSnocInd {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ (ys : List α) (y : α), motive ys → motive (ys ++ [y])) (xs : List α) : motive xs := by
  have key : ∀ zs : List α, motive zs.reverse := by
    intro zs
    induction zs with
    | nil => exact nil
    | cons z zs ih => rw [List.reverse_cons]; exact snoc _ _ ih
  have h := key xs.reverse
  rwa [List.reverse_reverse] at h

section Infer
variable {E : ResolvedEnvA} {iota : IotaFnA}

theorem inferA_app_of_pi {fuel : Nat} {Γ : LCtxA} {f a A B : ExprA} {u v : Level}
    (h : inferA E iota fuel Γ f = some (.pi A u B v)) :
    inferA E iota (fuel + 1) Γ (.app f a) = some (instantiate0A a B) := by
  have hw : whnfA E iota Γ fuel (.pi A u B v) = some (.pi A u B v) :=
    whnfA_of_normal E iota Γ fuel _ rfl
  simp only [inferA, h, hw]

/-- the type synthesised for a family application, below full length. -/
theorem inferA_famSpine {r : Nat} {m : CheckedMemberA} {ls : List Level} (hm : E.members r = some m)
    (hlen : ls.length = m.arity) {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀) (Γ : LCtxA)
    (xs : List ExprA) (hxs : xs.length ≤ (piDomsA m.mtypeA).length) :
    inferA E iota (xs.length + 1) Γ (foldAppsA (.const r ls) xs) =
      applyTelA xs (instantiateLevelsA ls m.mtypeA) := by
  have hb := piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
  have hl := (rigid_instantiateLevelsA ls m.mtypeA (Or.inl ⟨u₀, hsh⟩)).2
  induction xs using listSnocInd with
  | nil => simp only [inferA, hm, if_pos hlen, List.length_nil, foldAppsA, applyTelA]
  | snoc ys y ih =>
      have hys : ys.length < (piDomsA m.mtypeA).length := by
        simp only [List.length_append, List.length_singleton] at hxs; omega
      obtain ⟨D, u, C, v, hpi⟩ := (applyTelA_rigid ys _ (Or.inl ⟨_, hb⟩)).2 (by rw [hl]; exact hys)
      have hi := ih (Nat.le_of_lt hys)
      rw [hpi] at hi
      rw [foldAppsA_append, applyTelA_snoc ys _ hpi]
      simp only [List.length_append, List.length_singleton]
      exact inferA_app_of_pi hi

/-- and its inversion: whatever is synthesised for a family application is the
    telescope applied, and the level list has the family's arity. -/
theorem inferA_famSpine_inv {r : Nat} {m : CheckedMemberA} {ls : List Level}
    (hm : E.members r = some m) {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀) (Γ : LCtxA)
    (xs : List ExprA) : ∀ {fuel : Nat} {T : ExprA},
      inferA E iota fuel Γ (foldAppsA (.const r ls) xs) = some T →
      ls.length = m.arity ∧ applyTelA xs (instantiateLevelsA ls m.mtypeA) = some T := by
  have hb := piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
  induction xs using listSnocInd with
  | nil =>
      intro fuel T h
      cases fuel with
      | zero => exact Option.noConfusion h
      | succ fuel =>
          simp only [foldAppsA, inferA, hm] at h
          by_cases hlen : ls.length = m.arity
          · rw [if_pos hlen] at h
            exact ⟨hlen, h⟩
          · rw [if_neg hlen] at h
            exact Option.noConfusion h
  | snoc ys y ih =>
      intro fuel T h
      rw [foldAppsA_append] at h
      cases fuel with
      | zero => exact Option.noConfusion h
      | succ fuel =>
          cases hf : inferA E iota fuel Γ (foldAppsA (.const r ls) ys) with
          | none => simp [foldAppsA, inferA, hf] at h
          | some Tf =>
              obtain ⟨hlen, hTf⟩ := ih hf
              refine ⟨hlen, ?_⟩
              rcases applyTelA_sortBody ys _ hb hTf with ⟨_, hs⟩ | ⟨_, D, u, C, v, hp⟩
              · subst hs
                have hw : whnfA E iota Γ fuel (.sort (instLevel ls u₀)) = some (.sort (instLevel ls u₀)) :=
                  whnfA_of_normal E iota Γ fuel _ rfl
                simp [foldAppsA, inferA, hf, hw] at h
              · subst hp
                have hw : whnfA E iota Γ fuel (.pi D u C v) = some (.pi D u C v) :=
                  whnfA_of_normal E iota Γ fuel _ rfl
                simp only [foldAppsA, inferA, hf, hw] at h
                rw [applyTelA_snoc ys _ hTf]
                exact h

end Infer

/-- **the Prop boundary of a family application**, read off the family's result sort. -/
theorem isPropTy_famApp_iff {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} (hm : E.members r = some m) {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (ls : List Level) (xs : List ExprA) :
    IsPropTy E I Γ (foldAppsA (.const r ls) xs) ↔
      ls.length = m.arity ∧ xs.length = (piDomsA m.mtypeA).length ∧ isZero (instLevel ls u₀) = true := by
  have hb := piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
  have hl := (rigid_instantiateLevelsA ls m.mtypeA (Or.inl ⟨u₀, hsh⟩)).2
  constructor
  · rintro ⟨fuel, l, hs, hz⟩
    cases hT : inferA E I.fn fuel Γ (foldAppsA (.const r ls) xs) with
    | none => simp [inferSortA, hT] at hs
    | some T =>
        obtain ⟨hlen, hap⟩ := inferA_famSpine_inv hm hsh Γ xs hT
        rcases applyTelA_sortBody xs _ hb hap with ⟨h1, h2⟩ | ⟨_, D, u, C, v, hp⟩
        · subst h2
          have hw : whnfA E I.fn Γ fuel (.sort (instLevel ls u₀)) = some (.sort (instLevel ls u₀)) :=
            whnfA_of_normal E I.fn Γ fuel _ rfl
          simp only [inferSortA, hT, hw, Option.some.injEq] at hs
          subst hs
          exact ⟨hlen, by rw [h1, hl], hz⟩
        · subst hp
          have hw : whnfA E I.fn Γ fuel (.pi D u C v) = some (.pi D u C v) :=
            whnfA_of_normal E I.fn Γ fuel _ rfl
          simp [inferSortA, hT, hw] at hs
  · rintro ⟨hlen, hxs, hz⟩
    refine ⟨xs.length + 1, instLevel ls u₀, ?_, hz⟩
    have hi := inferA_famSpine (iota := I.fn) hm hlen hsh Γ xs (Nat.le_of_eq hxs)
    rw [applyTelA_sortBody_full xs _ hb (by rw [hl]; exact hxs)] at hi
    have hw : whnfA E I.fn Γ (xs.length + 1) (.sort (instLevel ls u₀)) =
        some (.sort (instLevel ls u₀)) := whnfA_of_normal E I.fn Γ _ _ rfl
    simp only [inferSortA, hi, hw]

/-- the Prop boundary is the same at `=ₙ` level lists and index lists of one length,
    in any context. -/
theorem isPropTy_famApp_congr {E : ResolvedEnvA} {I : IotaIfaceA} {Γ Γ' : LCtxA} {r : Nat}
    {m : CheckedMemberA} (hm : E.members r = some m) {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {ls ls' : List Level} (hls : eqNList ls ls') {xs xs' : List ExprA} (hxs : xs.length = xs'.length) :
    IsPropTy E I Γ (foldAppsA (.const r ls) xs) ↔ IsPropTy E I Γ' (foldAppsA (.const r ls') xs') := by
  rw [isPropTy_famApp_iff hm hsh, isPropTy_famApp_iff hm hsh, eqNListA_length hls, hxs,
    isZero_eqN (instLevel_eqNList hls u₀)]

/-- the sort of a family application moves along `=ₙ` level lists and index lists of
    one length, with its `isZero`. -/
theorem famApp_sort_transfer {m : CheckedMemberA} {u₀ : Level}
    (hsh : piBodyA m.mtypeA = .sort u₀) {ls ls' : List Level} (hls : eqNList ls ls')
    {xs xs' : List ExprA} (hxs : xs.length = xs'.length) {u : Level}
    (hu : applyTelA xs (instantiateLevelsA ls m.mtypeA) = some (.sort u)) :
    applyTelA xs' (instantiateLevelsA ls' m.mtypeA) = some (.sort (instLevel ls' u₀)) ∧
      isZero (instLevel ls' u₀) = isZero u := by
  have hb := piBodyA_instantiateLevelsA_sort ls m.mtypeA hsh
  have hb' := piBodyA_instantiateLevelsA_sort ls' m.mtypeA hsh
  have hl := (rigid_instantiateLevelsA ls m.mtypeA (Or.inl ⟨u₀, hsh⟩)).2
  have hl' := (rigid_instantiateLevelsA ls' m.mtypeA (Or.inl ⟨u₀, hsh⟩)).2
  rcases applyTelA_sortBody xs _ hb hu with ⟨h1, h2⟩ | ⟨_, _, _, _, _, hp⟩
  · injection h2 with h2
    subst h2
    refine ⟨applyTelA_sortBody_full xs' _ hb' (by rw [hl', ← hxs, h1, hl]), ?_⟩
    exact (isZero_eqN (instLevel_eqNList hls u₀)).symm
  · exact ExprA.noConfusion hp

/-- a family application that is triple-like is a proposition: its head is a family,
    so it is not the non-shape branch. -/
theorem tripleLikeA_famApp_isProp {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {r : Nat}
    {ls : List Level} {xs : List ExprA} {m : CheckedMemberA} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (h : TripleLikeA E I Γ (foldAppsA (.const r ls) xs)) :
    IsPropTy E I Γ (foldAppsA (.const r ls) xs) :=
  h.2.elim id (fun hs => (hs (by rw [foldAppsA_const_head]; exact ⟨m, hm, hind⟩)).elim)

/-! ## (3) term chains retype along a type conversion -/

section Retype
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

def tmChainA_retype {C C' : ExprA} (hc : TyConvA E I n Γ C C') :
    {a N : ExprA} → TmChainA E I n Γ C a N → TmChainA E I n Γ C' a N
  | _, _, .refl a h => .refl a (hasTyA_of_tyConvA h hc)
  | _, _, .cons a a' N ha hs t =>
      .cons a a' N (hasTyA_of_tyConvA ha hc) (.conv _ _ _ _ _ hs hc) (tmChainA_retype hc t)

theorem tyHRedStarA_retype {C C' a N : ExprA} (hc : Nonempty (TyConvA E I n Γ C C'))
    (h : TyHRedStarA E I n Γ a N C) : TyHRedStarA E I n Γ a N C' :=
  hc.elim fun c => h.elim fun t => ⟨tmChainA_retype c t⟩

theorem convA_retype {C C' a b : ExprA} (hc : Nonempty (TyConvA E I n Γ C C'))
    (h : Nonempty (ConvA E I n Γ a b C)) : Nonempty (ConvA E I n Γ a b C') :=
  hc.elim fun c => h.elim fun t => ⟨convA_of_tyConvA t c⟩

theorem tyConvA_symm_ne {C C' : ExprA} (h : Nonempty (TyConvA E I n Γ C C')) :
    Nonempty (TyConvA E I n Γ C' C) :=
  h.elim fun c => ⟨c.symm⟩

theorem declPairA_retype {C C' f f' : ExprA} (hc : Nonempty (TyConvA E I n Γ C C'))
    (h : DeclPairA E I n Γ C f f') : DeclPairA E I n Γ C' f f' :=
  ⟨hc.elim fun c => h.1.elim fun t => ⟨hasTyA_of_tyConvA t c⟩,
    hc.elim fun c => h.2.1.elim fun t => ⟨hasTyA_of_tyConvA t c⟩, convA_retype hc h.2.2⟩

theorem declPairA_symm {C f f' : ExprA} (h : DeclPairA E I n Γ C f f') : DeclPairA E I n Γ C f' f :=
  ⟨h.2.1, h.1, h.2.2.elim fun c => ⟨.symm _ _ _ _ c⟩⟩

theorem declPairA_trans {C f f' f'' : ExprA} (h : DeclPairA E I n Γ C f f')
    (h' : DeclPairA E I n Γ C f' f'') : DeclPairA E I n Γ C f f'' :=
  ⟨h.1, h'.2.1, h.2.2.elim fun c => h'.2.2.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩⟩

end Retype

#print axioms isZero_eqN
#print axioms applyTelA_rigid
#print axioms isPropTy_famApp_iff
#print axioms isPropTy_famApp_congr
#print axioms famApp_sort_transfer

/-! ## (4) the walk calculus (walks from any start: M2-f (3c) starts them at the carrier's
parameters) -/

/-- a plain walk FLIPS: the right arguments walk the second telescope, given at each
    position the Π on the right and the flipped pair. -/
theorem argsRelPA_flip {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {i₀ : Nat}
    {prev₀ prev₀' : List ExprA} {T₀ T₀' : ExprA}
    (hpos : ∀ (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre' pre →
      applyTelA pre T₀ = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre' T₀' = some (.pi A' u' B' v') ∧
        ∀ f f', R (i₀ + pre.length) (prev₀ ++ pre) f f' → R' (i₀ + pre.length) (prev₀' ++ pre') f' f) :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {xs xs' : List ExprA},
      ArgsRelPA R i prev T xs xs' →
      ∀ (pre pre' : List ExprA) (T' : ExprA), i = i₀ + pre.length → prev = prev₀ ++ pre →
        applyTelA pre T₀ = some T → applyTelA pre' T₀' = some T' →
        ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre' pre →
        ArgsRelPA R' i (prev₀' ++ pre') T' xs' xs := by
  intro i prev T xs xs' h
  induction h with
  | nil i prev T => intro _ _ T' _ _ _ _ _ _; exact .nil i _ T'
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro pre pre' T' hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos pre pre' A u B v hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hf' := hmap f f' hf
      have hlen : pre'.length = pre.length := (argsRelPA_length hp).symm
      have hp2 := argsRelPA_snoc hp (f := f) (f' := f') hT hf
      have hp2' := argsRelPA_snoc hp' (f := f') (f' := f) hpi' (by rw [hlen]; exact hf')
      have ihr := ih (pre ++ [f]) (pre' ++ [f']) (instantiate0A f' B') (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre' T₀' hpi') hp2 hp2'
      exact .cons (i₀ + pre.length) (prev₀' ++ pre') A' u' B' v' f' f fs' fs hf' (by simpa using ihr)

/-- two plain walks COMPOSE, given at each position the Π on the middle telescope and
    the composite pair. -/
theorem argsRelPA_comp {R R₂ : Nat → List ExprA → ExprA → ExprA → Prop} {i₀ : Nat}
    {prev₀ prev₀₂ : List ExprA} {T₀ T₀₂ : ExprA}
    (hpos : ∀ (p₁ p₂ p₃ : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA R i₀ prev₀ T₀ p₁ p₂ → ArgsRelPA R₂ i₀ prev₀₂ T₀₂ p₂ p₃ → ArgsRelPA R i₀ prev₀ T₀ p₁ p₃ →
      applyTelA p₁ T₀ = some (.pi A u B v) →
      ∃ A₂ u₂ B₂ v₂, applyTelA p₂ T₀₂ = some (.pi A₂ u₂ B₂ v₂) ∧
        ∀ f₁ f₂ f₃, R (i₀ + p₁.length) (prev₀ ++ p₁) f₁ f₂ → R₂ (i₀ + p₁.length) (prev₀₂ ++ p₂) f₂ f₃ →
          R (i₀ + p₁.length) (prev₀ ++ p₁) f₁ f₃) :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {xs ys : List ExprA},
      ArgsRelPA R i prev T xs ys →
      ∀ (pre pre₂ pre₃ : List ExprA) (T₂ : ExprA) (zs : List ExprA), i = i₀ + pre.length →
        prev = prev₀ ++ pre → applyTelA pre T₀ = some T → applyTelA pre₂ T₀₂ = some T₂ →
        ArgsRelPA R i₀ prev₀ T₀ pre pre₂ → ArgsRelPA R₂ i₀ prev₀₂ T₀₂ pre₂ pre₃ →
        ArgsRelPA R i₀ prev₀ T₀ pre pre₃ →
        ArgsRelPA R₂ i (prev₀₂ ++ pre₂) T₂ ys zs → ArgsRelPA R i prev T xs zs := by
  intro i prev T xs ys h
  induction h with
  | nil i prev T =>
      intro _ _ _ _ zs _ _ _ _ _ _ _ h2
      cases h2
      exact .nil i prev T
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro pre pre₂ pre₃ T₂ zs hi hprev hT hT₂ hp₁₂ hp₂₃ hp₁₃ h2
      subst hi; subst hprev
      obtain ⟨A₂, u₂, B₂, v₂, hpi₂, hmap⟩ := hpos pre pre₂ pre₃ A u B v hp₁₂ hp₂₃ hp₁₃ hT
      rw [hpi₂] at hT₂
      injection hT₂ with hT₂
      subst hT₂
      cases h2 with
      | cons _ _ _ _ _ _ _ f'' _ fs'' hf₂ hs₂ =>
          have hl₂ : pre₂.length = pre.length := (argsRelPA_length hp₁₂).symm
          have hf₃ := hmap f f' f'' hf hf₂
          have hp₁₂' := argsRelPA_snoc hp₁₂ (f := f) (f' := f') hT hf
          have hp₂₃' := argsRelPA_snoc hp₂₃ (f := f') (f' := f'') hpi₂ (by rw [hl₂]; exact hf₂)
          have hp₁₃' := argsRelPA_snoc hp₁₃ (f := f) (f' := f'') hT hf₃
          exact .cons (i₀ + pre.length) (prev₀ ++ pre) A u B v f f'' fs fs'' hf₃
            (by
              have := ih (pre ++ [f]) (pre₂ ++ [f']) (pre₃ ++ [f'']) (instantiate0A f' B₂) fs''
                (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre₂ T₀₂ hpi₂)
                hp₁₂' hp₂₃' hp₁₃' (by simpa using hs₂)
              simpa using this)

/-- a plain walk gives its RIGHT arguments related to themselves along a second telescope, given at
    each position the Π on the second telescope and the right pair related to itself there (the inner
    walks of a function-recursive position, R-NoFunRec-1 step 1 (1b)). -/
theorem argsRelPA_rrefl {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {i₀ : Nat}
    {prev₀ prev₀' : List ExprA} {T₀ T₀' : ExprA}
    (hpos : ∀ (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre' pre' →
      applyTelA pre T₀ = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre' T₀' = some (.pi A' u' B' v') ∧
        ∀ f f', R (i₀ + pre.length) (prev₀ ++ pre) f f' → R' (i₀ + pre.length) (prev₀' ++ pre') f' f') :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {xs xs' : List ExprA},
      ArgsRelPA R i prev T xs xs' →
      ∀ (pre pre' : List ExprA) (T' : ExprA), i = i₀ + pre.length → prev = prev₀ ++ pre →
        applyTelA pre T₀ = some T → applyTelA pre' T₀' = some T' →
        ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre' pre' →
        ArgsRelPA R' i (prev₀' ++ pre') T' xs' xs' := by
  intro i prev T xs xs' h
  induction h with
  | nil i prev T => intro _ _ T' _ _ _ _ _ _; exact .nil i _ T'
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro pre pre' T' hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos pre pre' A u B v hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hf' := hmap f f' hf
      have hlen : pre'.length = pre.length := (argsRelPA_length hp).symm
      have hp2 := argsRelPA_snoc hp (f := f) (f' := f') hT hf
      have hp2' := argsRelPA_snoc hp' (f := f') (f' := f') hpi' (by rw [hlen]; exact hf')
      have ihr := ih (pre ++ [f]) (pre' ++ [f']) (instantiate0A f' B') (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre' T₀' hpi') hp2 hp2'
      exact .cons (i₀ + pre.length) (prev₀' ++ pre') A' u' B' v' f' f' fs' fs' hf' (by simpa using ihr)

/-- a constructor walk FLIPS, given at each position the Π on the right and the flipped
    pair at the position's kind. -/
theorem argsRelA_flip {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {X X' : CRelA}
    {F F' : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    {i₀ : Nat} {prev₀ prev₀' : List ExprA} {T₀ T₀' : ExprA} (kinds : List FieldShape)
    (hpos : ∀ (kd : FieldShape) (ksPre ks : List FieldShape) (pre pre' : List ExprA) (A : ExprA)
      (u : Level) (B : ExprA) (v : Level), kinds = ksPre ++ kd :: ks →
      ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' → ArgsRelA R' X' F' i₀ prev₀' T₀' ksPre pre' pre →
      applyTelA pre T₀ = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre' T₀' = some (.pi A' u' B' v') ∧
        ∀ f f', kindRelA R X F (i₀ + ksPre.length) (prev₀ ++ pre) A kd f f' →
          kindRelA R' X' F' (i₀ + ksPre.length) (prev₀' ++ pre') A' kd f' f) :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs fs' : List ExprA},
      ArgsRelA R X F i prev T ks fs fs' →
      ∀ (ksPre : List FieldShape) (pre pre' : List ExprA) (T' : ExprA), kinds = ksPre ++ ks →
        i = i₀ + ksPre.length → prev = prev₀ ++ pre → applyTelA pre T₀ = some T →
        applyTelA pre' T₀' = some T' →
        ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' → ArgsRelA R' X' F' i₀ prev₀' T₀' ksPre pre' pre →
        ArgsRelA R' X' F' i (prev₀' ++ pre') T' ks fs' fs := by
  intro i prev T ks fs fs' h
  induction h with
  | nil i prev T => intro _ _ _ T' _ _ _ _ _ _ _; exact .nil i _ T'
  | plain i prev A u B v f f' ks fs fs' hR _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos .nonrecursive ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hR' : R' (i₀ + ksPre.length) (prev₀' ++ pre') f' f := hmap f f' hR
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') FieldShape.nonrecursive hT (by exact hR)
      have hp2' := argsRelA_snoc hp' (f := f') (f' := f) FieldShape.nonrecursive hpi' (by exact hR')
      have ihr := ih (ksPre ++ [FieldShape.nonrecursive]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f' B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre' T₀' hpi') hp2 hp2'
      exact .plain (i₀ + ksPre.length) (prev₀' ++ pre') A' u' B' v' f' f ks fs' fs hR'
        (by simpa using ihr)
  | directRec i prev A u B v f f' ks fs fs' hY _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos (.recursive 0) ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hY' : X' A' f' f := hmap f f' hY
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive 0) hT hY
      have hp2' := argsRelA_snoc hp' (f := f') (f' := f) (FieldShape.recursive 0) hpi' hY'
      have ihr := ih (ksPre ++ [(FieldShape.recursive 0)]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f' B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre' T₀' hpi') hp2 hp2'
      exact .directRec (i₀ + ksPre.length) (prev₀' ++ pre') A' u' B' v' f' f ks fs' fs hY'
        (by simpa using ihr)
  | funRec i prev A u B v f f' j ks fs fs' hF _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos (.recursive (j + 1)) ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hF' : F' (i₀ + ksPre.length) (prev₀' ++ pre') A' j f' f := hmap f f' hF
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT hF
      have hp2' := argsRelA_snoc hp' (f := f') (f' := f) (FieldShape.recursive (j + 1)) hpi' hF'
      have ihr := ih (ksPre ++ [FieldShape.recursive (j + 1)]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f' B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre' T₀' hpi') hp2 hp2'
      exact .funRec (i₀ + ksPre.length) (prev₀' ++ pre') A' u' B' v' f' f j ks fs' fs hF'
        (by simpa using ihr)

/-- two constructor walks COMPOSE, given at each position the Π on the middle telescope
    and the composite pair at the position's kind. -/
theorem argsRelA_comp {R R₂ : Nat → List ExprA → ExprA → ExprA → Prop} {X X₂ X₃ : CRelA}
    {F F₂ F₃ : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    {i₀ : Nat} {prev₀ prev₀₂ : List ExprA} {T₀ T₀₂ : ExprA} (kinds : List FieldShape)
    (hpos : ∀ (kd : FieldShape) (ksPre ks : List FieldShape) (p₁ p₂ p₃ : List ExprA) (A : ExprA)
      (u : Level) (B : ExprA) (v : Level), kinds = ksPre ++ kd :: ks →
      ArgsRelA R X F i₀ prev₀ T₀ ksPre p₁ p₂ → ArgsRelA R₂ X₂ F₂ i₀ prev₀₂ T₀₂ ksPre p₂ p₃ →
      ArgsRelA R X₃ F₃ i₀ prev₀ T₀ ksPre p₁ p₃ → applyTelA p₁ T₀ = some (.pi A u B v) →
      ∃ A₂ u₂ B₂ v₂, applyTelA p₂ T₀₂ = some (.pi A₂ u₂ B₂ v₂) ∧
        ∀ f₁ f₂ f₃, kindRelA R X F (i₀ + ksPre.length) (prev₀ ++ p₁) A kd f₁ f₂ →
          kindRelA R₂ X₂ F₂ (i₀ + ksPre.length) (prev₀₂ ++ p₂) A₂ kd f₂ f₃ →
          kindRelA R X₃ F₃ (i₀ + ksPre.length) (prev₀ ++ p₁) A kd f₁ f₃) :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs gs : List ExprA},
      ArgsRelA R X F i prev T ks fs gs →
      ∀ (ksPre : List FieldShape) (pre pre₂ pre₃ : List ExprA) (T₂ : ExprA) (hs : List ExprA),
        kinds = ksPre ++ ks → i = i₀ + ksPre.length → prev = prev₀ ++ pre → applyTelA pre T₀ = some T →
        applyTelA pre₂ T₀₂ = some T₂ →
        ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre₂ → ArgsRelA R₂ X₂ F₂ i₀ prev₀₂ T₀₂ ksPre pre₂ pre₃ →
        ArgsRelA R X₃ F₃ i₀ prev₀ T₀ ksPre pre pre₃ →
        ArgsRelA R₂ X₂ F₂ i (prev₀₂ ++ pre₂) T₂ ks gs hs → ArgsRelA R X₃ F₃ i prev T ks fs hs := by
  intro i prev T ks fs gs h
  induction h with
  | nil i prev T =>
      intro _ _ _ _ _ hs _ _ _ _ _ _ _ _ h2
      cases h2
      exact .nil i prev T
  | plain i prev A u B v f f' ks fs fs' hR _ ih =>
      intro ksPre pre pre₂ pre₃ T₂ hs hk hi hprev hT hT₂ hp₁₂ hp₂₃ hp₁₃ h2
      subst hi; subst hprev
      obtain ⟨A₂, u₂, B₂, v₂, hpi₂, hmap⟩ :=
        hpos .nonrecursive ksPre ks pre pre₂ pre₃ A u B v hk hp₁₂ hp₂₃ hp₁₃ hT
      rw [hpi₂] at hT₂
      injection hT₂ with hT₂
      subst hT₂
      cases h2 with
      | plain _ _ _ _ _ _ _ f'' _ _ hs'' hR₂ hs₂ =>
          have hR₃ : R (i₀ + ksPre.length) (prev₀ ++ pre) f f'' := hmap f f' f'' hR hR₂
          have hp₁₂' := argsRelA_snoc hp₁₂ (f := f) (f' := f') FieldShape.nonrecursive hT (by exact hR)
          have hp₂₃' := argsRelA_snoc hp₂₃ (f := f') (f' := f'') FieldShape.nonrecursive hpi₂ (by exact hR₂)
          have hp₁₃' := argsRelA_snoc hp₁₃ (f := f) (f' := f'') FieldShape.nonrecursive hT (by exact hR₃)
          exact .plain (i₀ + ksPre.length) (prev₀ ++ pre) A u B v f f'' ks fs hs'' hR₃
            (by
              have := ih (ksPre ++ [FieldShape.nonrecursive]) (pre ++ [f]) (pre₂ ++ [f']) (pre₃ ++ [f''])
                (instantiate0A f' B₂) hs'' (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
                (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre₂ T₀₂ hpi₂) hp₁₂' hp₂₃' hp₁₃'
                (by simpa using hs₂)
              simpa using this)
  | directRec i prev A u B v f f' ks fs fs' hY _ ih =>
      intro ksPre pre pre₂ pre₃ T₂ hs hk hi hprev hT hT₂ hp₁₂ hp₂₃ hp₁₃ h2
      subst hi; subst hprev
      obtain ⟨A₂, u₂, B₂, v₂, hpi₂, hmap⟩ :=
        hpos (.recursive 0) ksPre ks pre pre₂ pre₃ A u B v hk hp₁₂ hp₂₃ hp₁₃ hT
      rw [hpi₂] at hT₂
      injection hT₂ with hT₂
      subst hT₂
      cases h2 with
      | directRec _ _ _ _ _ _ _ f'' _ _ hs'' hY₂ hs₂ =>
          have hY₃ : X₃ A f f'' := hmap f f' f'' hY hY₂
          have hp₁₂' := argsRelA_snoc hp₁₂ (f := f) (f' := f') (FieldShape.recursive 0) hT hY
          have hp₂₃' := argsRelA_snoc hp₂₃ (f := f') (f' := f'') (FieldShape.recursive 0) hpi₂ hY₂
          have hp₁₃' := argsRelA_snoc hp₁₃ (f := f) (f' := f'') (FieldShape.recursive 0) hT hY₃
          exact .directRec (i₀ + ksPre.length) (prev₀ ++ pre) A u B v f f'' ks fs hs'' hY₃
            (by
              have := ih (ksPre ++ [(FieldShape.recursive 0)]) (pre ++ [f]) (pre₂ ++ [f']) (pre₃ ++ [f''])
                (instantiate0A f' B₂) hs'' (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
                (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre₂ T₀₂ hpi₂) hp₁₂' hp₂₃' hp₁₃'
                (by simpa using hs₂)
              simpa using this)
  | funRec i prev A u B v f f' j ks fs fs' hF _ ih =>
      intro ksPre pre pre₂ pre₃ T₂ hs hk hi hprev hT hT₂ hp₁₂ hp₂₃ hp₁₃ h2
      subst hi; subst hprev
      obtain ⟨A₂, u₂, B₂, v₂, hpi₂, hmap⟩ :=
        hpos (.recursive (j + 1)) ksPre ks pre pre₂ pre₃ A u B v hk hp₁₂ hp₂₃ hp₁₃ hT
      rw [hpi₂] at hT₂
      injection hT₂ with hT₂
      subst hT₂
      cases h2 with
      | funRec _ _ _ _ _ _ _ f'' _ _ _ hs'' hF₂ hs₂ =>
          have hF₃ : F₃ (i₀ + ksPre.length) (prev₀ ++ pre) A j f f'' := hmap f f' f'' hF hF₂
          have hp₁₂' := argsRelA_snoc hp₁₂ (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT hF
          have hp₂₃' := argsRelA_snoc hp₂₃ (f := f') (f' := f'') (FieldShape.recursive (j + 1)) hpi₂ hF₂
          have hp₁₃' := argsRelA_snoc hp₁₃ (f := f) (f' := f'') (FieldShape.recursive (j + 1)) hT hF₃
          exact .funRec (i₀ + ksPre.length) (prev₀ ++ pre) A u B v f f'' j ks fs hs'' hF₃
            (by
              have := ih (ksPre ++ [FieldShape.recursive (j + 1)]) (pre ++ [f]) (pre₂ ++ [f']) (pre₃ ++ [f''])
                (instantiate0A f' B₂) hs'' (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
                (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre₂ T₀₂ hpi₂) hp₁₂' hp₂₃' hp₁₃'
                (by simpa using hs₂)
              simpa using this)

/-- a plain walk CROSSES to a second start: the same arguments walk a second telescope
    from a second prefix, given at each position the Π on the second telescope and the
    pair carried over (M2-f (3c): the carrier's parameters change). -/
theorem argsRelPA_cross {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {i₀ : Nat}
    {prev₀ prev₀' : List ExprA} {T₀ T₀' : ExprA}
    (hpos : ∀ (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre pre' →
      applyTelA pre T₀ = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre T₀' = some (.pi A' u' B' v') ∧
        ∀ f f', R (i₀ + pre.length) (prev₀ ++ pre) f f' → R' (i₀ + pre.length) (prev₀' ++ pre) f f') :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {xs xs' : List ExprA},
      ArgsRelPA R i prev T xs xs' →
      ∀ (pre pre' : List ExprA) (T' : ExprA), i = i₀ + pre.length → prev = prev₀ ++ pre →
        applyTelA pre T₀ = some T → applyTelA pre T₀' = some T' →
        ArgsRelPA R i₀ prev₀ T₀ pre pre' → ArgsRelPA R' i₀ prev₀' T₀' pre pre' →
        ArgsRelPA R' i (prev₀' ++ pre) T' xs xs' := by
  intro i prev T xs xs' h
  induction h with
  | nil i prev T => intro _ _ T' _ _ _ _ _ _; exact .nil i _ T'
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro pre pre' T' hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos pre pre' A u B v hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hf' := hmap f f' hf
      have hp2 := argsRelPA_snoc hp (f := f) (f' := f') hT hf
      have hp2' := argsRelPA_snoc hp' (f := f) (f' := f') hpi' hf'
      have ihr := ih (pre ++ [f]) (pre' ++ [f']) (instantiate0A f B') (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) (applyTelA_snoc pre T₀' hpi') hp2 hp2'
      exact .cons (i₀ + pre.length) (prev₀' ++ pre) A' u' B' v' f f' fs fs' hf' (by simpa using ihr)

/-- a constructor walk CROSSES to a second start, given at each position the Π on the
    second telescope and the pair carried over at the position's kind. -/
theorem argsRelA_cross {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {X X' : CRelA}
    {F F' : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    {i₀ : Nat} {prev₀ prev₀' : List ExprA} {T₀ T₀' : ExprA} (kinds : List FieldShape)
    (hpos : ∀ (kd : FieldShape) (ksPre ks : List FieldShape) (pre pre' : List ExprA) (A : ExprA)
      (u : Level) (B : ExprA) (v : Level), kinds = ksPre ++ kd :: ks →
      ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' → ArgsRelA R' X' F' i₀ prev₀' T₀' ksPre pre pre' →
      applyTelA pre T₀ = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre T₀' = some (.pi A' u' B' v') ∧
        ∀ f f', kindRelA R X F (i₀ + ksPre.length) (prev₀ ++ pre) A kd f f' →
          kindRelA R' X' F' (i₀ + ksPre.length) (prev₀' ++ pre) A' kd f f') :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs fs' : List ExprA},
      ArgsRelA R X F i prev T ks fs fs' →
      ∀ (ksPre : List FieldShape) (pre pre' : List ExprA) (T' : ExprA), kinds = ksPre ++ ks →
        i = i₀ + ksPre.length → prev = prev₀ ++ pre → applyTelA pre T₀ = some T →
        applyTelA pre T₀' = some T' →
        ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' → ArgsRelA R' X' F' i₀ prev₀' T₀' ksPre pre pre' →
        ArgsRelA R' X' F' i (prev₀' ++ pre) T' ks fs fs' := by
  intro i prev T ks fs fs' h
  induction h with
  | nil i prev T => intro _ _ _ T' _ _ _ _ _ _ _; exact .nil i _ T'
  | plain i prev A u B v f f' ks fs fs' hR _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos .nonrecursive ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hR' : R' (i₀ + ksPre.length) (prev₀' ++ pre) f f' := hmap f f' hR
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') FieldShape.nonrecursive hT (by exact hR)
      have hp2' := argsRelA_snoc hp' (f := f) (f' := f') FieldShape.nonrecursive hpi' (by exact hR')
      have ihr := ih (ksPre ++ [FieldShape.nonrecursive]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre T₀' hpi') hp2 hp2'
      exact .plain (i₀ + ksPre.length) (prev₀' ++ pre) A' u' B' v' f f' ks fs fs' hR'
        (by simpa using ihr)
  | directRec i prev A u B v f f' ks fs fs' hY _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos (.recursive 0) ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hY' : X' A' f f' := hmap f f' hY
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive 0) hT hY
      have hp2' := argsRelA_snoc hp' (f := f) (f' := f') (FieldShape.recursive 0) hpi' hY'
      have ihr := ih (ksPre ++ [(FieldShape.recursive 0)]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre T₀' hpi') hp2 hp2'
      exact .directRec (i₀ + ksPre.length) (prev₀' ++ pre) A' u' B' v' f f' ks fs fs' hY'
        (by simpa using ihr)
  | funRec i prev A u B v f f' j ks fs fs' hF _ ih =>
      intro ksPre pre pre' T' hk hi hprev hT hT' hp hp'
      subst hi; subst hprev
      obtain ⟨A', u', B', v', hpi', hmap⟩ := hpos (.recursive (j + 1)) ksPre ks pre pre' A u B v hk hp hp' hT
      rw [hpi'] at hT'
      injection hT' with hT'
      subst hT'
      have hF' : F' (i₀ + ksPre.length) (prev₀' ++ pre) A' j f f' := hmap f f' hF
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT hF
      have hp2' := argsRelA_snoc hp' (f := f) (f' := f') (FieldShape.recursive (j + 1)) hpi' hF'
      have ihr := ih (ksPre ++ [FieldShape.recursive (j + 1)]) (pre ++ [f]) (pre' ++ [f']) (instantiate0A f B')
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp) (applyTelA_snoc pre T₀ hT)
        (applyTelA_snoc pre T₀' hpi') hp2 hp2'
      exact .funRec (i₀ + ksPre.length) (prev₀' ++ pre) A' u' B' v' f f' j ks fs fs' hF'
        (by simpa using ihr)

/-- a plain walk instantiates its telescope: the left arguments reach a type. -/
theorem argsRelPA_applyTel_some {R : Nat → List ExprA → ExprA → ExprA → Prop} :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {xs ys : List ExprA},
      ArgsRelPA R i prev T xs ys → ∃ T', applyTelA xs T = some T'
  | _, _, T, _, _, .nil _ _ _ => ⟨T, rfl⟩
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ hs => by
      obtain ⟨T', h⟩ := argsRelPA_applyTel_some hs
      exact ⟨T', h⟩

/-! ### the function-recursive position (R-NoFunRec-1 step 1 (1b))

A function-recursive pair is a Kripke Π into the fixed point (`FunRelA`). It flips, composes and
crosses as a Π does: through its inner walks (the plain walk calculus above), then at the codomain
reached, by the fixed point's own law there (the caller's `hX`). -/

/-- a function-recursive pair FLIPS: the right inner walks flip to the left ones, and the codomain's
    pair flips across the two codomains reached. -/
theorem funRelA_flip {RI RI' : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {XF XF' : WkSpecA → CRelA} {OK : WkSpecA → Prop} {i : Nat} {prev prev' : List ExprA} {A A' : ExprA}
    {j : Nat}
    (hin : ∀ ρ', OK ρ' → ∀ zs zs', ArgsRelPA (RI' i prev' ρ') 0 [] (wkExprA ρ' A') zs zs' →
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs' zs)
    (hX : ∀ ρ', OK ρ' → ∀ (zs zs' : List ExprA) (C C' a b : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs' zs → zs'.length = j + 1 →
        applyTelA zs' (wkExprA ρ' A) = some C → applyTelA zs (wkExprA ρ' A') = some C' →
        XF ρ' C a b → XF' ρ' C' b a)
    {f f' : ExprA} (h : FunRelA RI XF OK i prev A j f f') : FunRelA RI' XF' OK i prev' A' j f' f := by
  intro ρ' hρ' zs zs' C' hzs hlen hC'
  have hw := hin ρ' hρ' zs zs' hzs
  have hlen' : zs'.length = j + 1 := by rw [← argsRelPA_length hzs]; exact hlen
  obtain ⟨C, hC⟩ := argsRelPA_applyTel_some hw
  exact hX ρ' hρ' zs zs' C C' _ _ hw hlen' hC hC' (h ρ' hρ' zs' zs C hw hlen' hC)

/-- two function-recursive pairs COMPOSE: a left inner walk gives a reflexive one on the middle
    telescope, and the codomain's pairs compose across the two codomains reached. -/
theorem funRelA_comp {RI RI₂ : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {XF XF₂ XF₃ : WkSpecA → CRelA} {OK : WkSpecA → Prop} {i : Nat} {prev prev₂ : List ExprA}
    {A A₂ : ExprA} {j : Nat}
    (hrefl : ∀ ρ', OK ρ' → ∀ zs zs'', ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs'' →
        ArgsRelPA (RI₂ i prev₂ ρ') 0 [] (wkExprA ρ' A₂) zs'' zs'')
    (hX : ∀ ρ', OK ρ' → ∀ (zs zs'' : List ExprA) (C C₂ a b c : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs'' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' A) = some C → applyTelA zs'' (wkExprA ρ' A₂) = some C₂ →
        XF ρ' C a b → XF₂ ρ' C₂ b c → XF₃ ρ' C a c)
    {f f' f'' : ExprA} (h₁ : FunRelA RI XF OK i prev A j f f')
    (h₂ : FunRelA RI₂ XF₂ OK i prev₂ A₂ j f' f'') : FunRelA RI XF₃ OK i prev A j f f'' := by
  intro ρ' hρ' zs zs'' C hzs hlen hC
  have hw₂ := hrefl ρ' hρ' zs zs'' hzs
  have hlen'' : zs''.length = j + 1 := by rw [← argsRelPA_length hzs]; exact hlen
  obtain ⟨C₂, hC₂⟩ := argsRelPA_applyTel_some hw₂
  exact hX ρ' hρ' zs zs'' C C₂ _ _ _ hzs hlen hC hC₂ (h₁ ρ' hρ' zs zs'' C hzs hlen hC)
    (h₂ ρ' hρ' zs'' zs'' C₂ hw₂ hlen'' hC₂)

/-- a function-recursive pair CROSSES to a second domain: the second's inner walks cross back to the
    first's, and the codomain's pair crosses between the two codomains reached. -/
theorem funRelA_cross {RI RI' : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {XF XF' : WkSpecA → CRelA} {OK : WkSpecA → Prop} {i : Nat} {prev prev' : List ExprA} {A A' : ExprA}
    {j : Nat}
    (hin : ∀ ρ', OK ρ' → ∀ zs zs', ArgsRelPA (RI' i prev' ρ') 0 [] (wkExprA ρ' A') zs zs' →
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs')
    (hX : ∀ ρ', OK ρ' → ∀ (zs zs' : List ExprA) (C C' a b : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' A) = some C → applyTelA zs (wkExprA ρ' A') = some C' →
        XF ρ' C a b → XF' ρ' C' a b)
    {f f' : ExprA} (h : FunRelA RI XF OK i prev A j f f') : FunRelA RI' XF' OK i prev' A' j f f' := by
  intro ρ' hρ' zs zs' C' hzs hlen hC'
  have hw := hin ρ' hρ' zs zs' hzs
  obtain ⟨C, hC⟩ := argsRelPA_applyTel_some hw
  exact hX ρ' hρ' zs zs' C C' _ _ hw hlen hC hC' (h ρ' hρ' zs zs' C hw hlen hC)

/-- the family clause's function-recursive pair FLIPS (`funRelA_flip`), its declared pair along the
    conversion of the two declared domains (R-NoFunRec-1 step 1 (1c-ε2d-L2)). -/
theorem famFunRelA_flip {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {m : CheckedMemberA}
    {RI RI' : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {ps ps' : List ExprA} {ls ls' : List Level} {XF XF' : WkSpecA → CRelA} {i : Nat}
    {prev prev' : List ExprA} {A A' : ExprA} {j : Nat} (hdom : Nonempty (TyConvA E I n Γ A A'))
    (hin : ∀ ρ', WkOkA E I n ρ' Γ → ∀ zs zs', ArgsRelPA (RI' i prev' ρ') 0 [] (wkExprA ρ' A') zs zs' →
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs' zs)
    (hX : ∀ ρ', WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (C C' a b : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs' zs → zs'.length = j + 1 →
        applyTelA zs' (wkExprA ρ' A) = some C → applyTelA zs (wkExprA ρ' A') = some C' →
        famRecRelA m (ps.map (wkExprA ρ')) ls (XF ρ') C a b →
        famRecRelA m (ps'.map (wkExprA ρ')) ls' (XF' ρ') C' b a)
    {f f' : ExprA} (h : famFunRelA E I n Γ m RI ps ls XF i prev A j f f') :
    famFunRelA E I n Γ m RI' ps' ls' XF' i prev' A' j f' f :=
  ⟨funRelA_flip hin hX h.1, declPairA_retype hdom (declPairA_symm h.2)⟩

/-- the function-recursive pair COMPOSES (`funRelA_comp`), its declared pairs along the conversion of
    the two declared domains. -/
theorem famFunRelA_comp {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {m : CheckedMemberA}
    {RI RI₂ : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {ps ps₂ ps₃ : List ExprA} {ls ls₂ ls₃ : List Level} {XF XF₂ XF₃ : WkSpecA → CRelA} {i : Nat}
    {prev prev₂ : List ExprA} {A A₂ : ExprA} {j : Nat} (hdom : Nonempty (TyConvA E I n Γ A A₂))
    (hrefl : ∀ ρ', WkOkA E I n ρ' Γ → ∀ zs zs'', ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs'' →
        ArgsRelPA (RI₂ i prev₂ ρ') 0 [] (wkExprA ρ' A₂) zs'' zs'')
    (hX : ∀ ρ', WkOkA E I n ρ' Γ → ∀ (zs zs'' : List ExprA) (C C₂ a b c : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs'' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' A) = some C → applyTelA zs'' (wkExprA ρ' A₂) = some C₂ →
        famRecRelA m (ps.map (wkExprA ρ')) ls (XF ρ') C a b →
        famRecRelA m (ps₂.map (wkExprA ρ')) ls₂ (XF₂ ρ') C₂ b c →
        famRecRelA m (ps₃.map (wkExprA ρ')) ls₃ (XF₃ ρ') C a c)
    {f f' f'' : ExprA} (h₁ : famFunRelA E I n Γ m RI ps ls XF i prev A j f f')
    (h₂ : famFunRelA E I n Γ m RI₂ ps₂ ls₂ XF₂ i prev₂ A₂ j f' f'') :
    famFunRelA E I n Γ m RI ps₃ ls₃ XF₃ i prev A j f f'' :=
  ⟨funRelA_comp hrefl hX h₁.1 h₂.1,
    declPairA_trans h₁.2 (declPairA_retype (hdom.elim fun c => ⟨c.symm⟩) h₂.2)⟩

/-- the function-recursive pair CROSSES (`funRelA_cross`), its declared pair along the conversion of
    the two declared domains. -/
theorem famFunRelA_cross {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {m : CheckedMemberA}
    {RI RI' : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {ps ps' : List ExprA} {ls ls' : List Level} {XF XF' : WkSpecA → CRelA} {i : Nat}
    {prev prev' : List ExprA} {A A' : ExprA} {j : Nat} (hdom : Nonempty (TyConvA E I n Γ A A'))
    (hin : ∀ ρ', WkOkA E I n ρ' Γ → ∀ zs zs', ArgsRelPA (RI' i prev' ρ') 0 [] (wkExprA ρ' A') zs zs' →
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs')
    (hX : ∀ ρ', WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (C C' a b : ExprA),
        ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' A) = some C → applyTelA zs (wkExprA ρ' A') = some C' →
        famRecRelA m (ps.map (wkExprA ρ')) ls (XF ρ') C a b →
        famRecRelA m (ps'.map (wkExprA ρ')) ls' (XF' ρ') C' a b)
    {f f' : ExprA} (h : famFunRelA E I n Γ m RI ps ls XF i prev A j f f') :
    famFunRelA E I n Γ m RI' ps' ls' XF' i prev' A' j f f' :=
  ⟨funRelA_cross hin hX h.1, declPairA_retype hdom h.2⟩

/-! ## (5) the fixed point on a fiber: carrier, symmetry, transitivity

A FIBER is the set of carriers with the same parameters `ps` (the family's
`nparamsA` first arguments) and levels `=ₙ` a fixed `ls₀`; the operator's recursive
positions never leave it (`famRecRelA`), so every induction below is over a fiber. -/

/-- what the index walks need to flip and compose on a fiber, across `=ₙ` level lists:
    at each position the Π on the other side, the flipped pair, and the composite pair
    (the clause's PER and transport induction hypotheses discharge it). -/
def IdxPerA (n : Nat) (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (m : CheckedMemberA)
    (ps : List ExprA) (ls₀ : List Level) : Prop :=
  ∀ (lsF lsF' : List Level) (TF TF' : ExprA), eqNListB n ls₀ lsF → eqNListB n lsF lsF' →
    applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
    applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF' →
    (∀ (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' →
      ArgsRelPA (RsF lsF') m.nparamsA ps TF' pre' pre →
      applyTelA pre TF = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre' TF' = some (.pi A' u' B' v') ∧
        ∀ f f', RsF lsF (m.nparamsA + pre.length) (ps ++ pre) f f' →
          RsF lsF' (m.nparamsA + pre.length) (ps ++ pre') f' f) ∧
    (∀ (p₁ p₂ p₃ : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
      ArgsRelPA (RsF lsF) m.nparamsA ps TF p₁ p₂ →
      ArgsRelPA (RsF lsF') m.nparamsA ps TF' p₂ p₃ →
      ArgsRelPA (RsF lsF) m.nparamsA ps TF p₁ p₃ →
      applyTelA p₁ TF = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA p₂ TF' = some (.pi A' u' B' v') ∧
        ∀ f₁ f₂ f₃, RsF lsF (m.nparamsA + p₁.length) (ps ++ p₁) f₁ f₂ →
          RsF lsF' (m.nparamsA + p₁.length) (ps ++ p₂) f₂ f₃ →
          RsF lsF (m.nparamsA + p₁.length) (ps ++ p₁) f₁ f₃)

namespace IdxPerA
variable {n : Nat} {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {m : CheckedMemberA}
  {ps : List ExprA} {ls₀ : List Level}

theorem flip (h : IdxPerA n RsF m ps ls₀) {lsF lsF' : List Level} {TF TF' : ExprA}
    (hl₀ : eqNListB n ls₀ lsF) (hls : eqNListB n lsF lsF')
    (hTF : applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF)
    (hTF' : applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF')
    {xs xs' : List ExprA} (hw : ArgsRelPA (RsF lsF) m.nparamsA ps TF xs xs') :
    ArgsRelPA (RsF lsF') m.nparamsA ps TF' xs' xs := by
  have := argsRelPA_flip (h lsF lsF' TF TF' hl₀ hls hTF hTF').1 hw [] [] TF' (by simp) (by simp)
    rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using this

theorem comp (h : IdxPerA n RsF m ps ls₀) {lsF lsF' : List Level} {TF TF' : ExprA}
    (hl₀ : eqNListB n ls₀ lsF) (hls : eqNListB n lsF lsF')
    (hTF : applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF)
    (hTF' : applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF')
    {x₁ x₂ x₃ : List ExprA} (h₁₂ : ArgsRelPA (RsF lsF) m.nparamsA ps TF x₁ x₂)
    (h₂₃ : ArgsRelPA (RsF lsF') m.nparamsA ps TF' x₂ x₃) :
    ArgsRelPA (RsF lsF) m.nparamsA ps TF x₁ x₃ :=
  argsRelPA_comp (h lsF lsF' TF TF' hl₀ hls hTF hTF').2 h₁₂ [] [] [] TF' x₃ (by simp) (by simp)
    rfl rfl (.nil _ _ _) (.nil _ _ _) (.nil _ _ _) (by simpa using h₂₃)

end IdxPerA

section FixedPoint
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
  {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
  {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}

/-- the coherence of a constructor form, with its two sides swapped. -/
theorem famCohA_swap {RsF₀ : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {A : ExprA}
    {args args' : List ExprA} {T T' : ExprA}
    (h : FamCohA r m RsF₀ A args T args' T') : FamCohA r m RsF₀ A args' T' args T := by
  obtain ⟨lsA, lsR, lsR', xsA, isR, isR', TF, R₁, R₁', h1, hTF, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨lsA, lsR', lsR, xsA, isR', isR, TF, R₁', R₁, h1, hTF, h6, h7, h8, h9, h2, h3, h4, h5⟩

theorem carrierParamsA_famApp {ps is : List ExprA} (hps : ps.length = m.nparamsA) (ls : List Level) :
    carrierParamsA m (foldAppsA (.const r ls) (ps ++ is)) = ps := by
  rw [carrierParamsA_foldAppsA, ← hps, List.take_left]

/-- **the carrier moves along related indices within a fiber** (at a world `ρ`, `ps` the
    fiber's parameters there): one unfolding, the conversion and the chains retyped, the
    index coherence flipped and composed through `IdxPerA`, the walk's fiber relation
    re-levelled. -/
theorem lfpWA_carrier {ρ : WkSpecA} {ps : List ExprA} {ls₀ : List Level}
    (hI : IdxPerA n (RsF ρ) m ps ls₀)
    (hps : ps.length = m.nparamsA) {ls ls' : List Level} {is is' : List ExprA} {TF TF' : ExprA}
    (hl₀ : eqNList ls₀ ls) (hls : eqNListB n ls ls')
    (hTF : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF)
    (hTF' : applyTelA ps (instantiateLevelsA ls' m.mtypeA) = some TF')
    (hw : ArgsRelPA (RsF ρ ls) m.nparamsA ps TF is is')
    (hc : Nonempty (TyConvA E I n (wkCtxA ρ Γ) (foldAppsA (.const r ls) (ps ++ is))
      (foldAppsA (.const r ls') (ps ++ is'))))
    {a b : ExprA}
    (h : LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ (foldAppsA (.const r ls) (ps ++ is)) a b) :
    LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ (foldAppsA (.const r ls') (ps ++ is')) a b := by
  have hu := LfpWA.unfold famPhiWA_mono h
  refine LfpWA.fold famPhiWA_mono ⟨convA_retype hc hu.1, ?_⟩
  have hP₁ := carrierParamsA_famApp (r := r) (is := is) hps ls
  have hP₂ := carrierParamsA_famApp (r := r) (is := is') hps ls'
  rcases hu.2 with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hlsC,
      hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
  · rw [carrierLevelsA_foldAppsA] at hlC
    rw [hP₁] at hT hT'
    rw [hP₁, carrierLevelsA_foldAppsA] at hargs
    refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, ?_, hlsC, hkinds,
      ?_, ?_, ?_, hp₁, hp₂, tyHRedStarA_retype hc ha, tyHRedStarA_retype hc hb, hna, hnb, ?_⟩
    · rw [carrierLevelsA_foldAppsA]
      exact ⟨⟨eqNListA_trans (eqNListA_symm hls.1) hlC.1.1, hlC.1.2⟩, hls.2⟩
    · rw [hP₂]; exact hT
    · rw [hP₂]; exact hT'
    · obtain ⟨lsA, lsR, lsR', xsA, isR, isR', TF₀, R₁, R₁', hspA, hTF₀, hta, hspR, hlsA, hwR, hta',
        hspR', hlsA', hwR'⟩ := hcoh
      rw [foldAppsA_const_head] at hspA
      injection hspA with h1 h2
      injection h1 with _ h1
      subst h1; subst h2
      have htk : (ps ++ is).take m.nparamsA = ps := by rw [← hps, List.take_left]
      have hdr : (ps ++ is).drop m.nparamsA = is := by rw [← hps, List.drop_left]
      rw [htk] at hTF₀ hspR hwR hspR' hwR'
      rw [hdr] at hwR hwR'
      rw [hTF₀] at hTF
      injection hTF with hTF
      subst hTF
      have hflip := hI.flip ⟨hl₀, hlC.2⟩ hls hTF₀ hTF' hw
      have hl₀' : eqNListB n ls₀ ls' := ⟨eqNListA_trans hl₀ hls.1, hls.2⟩
      have htk' : (ps ++ is').take m.nparamsA = ps := by rw [← hps, List.take_left]
      have hdr' : (ps ++ is').drop m.nparamsA = is' := by rw [← hps, List.drop_left]
      refine ⟨ls', lsR, lsR', ps ++ is', isR, isR', TF', R₁, R₁', foldAppsA_const_head _ _ _, ?_, hta, ?_,
        eqNListA_trans (eqNListA_symm hls.1) hlsA, ?_, hta', ?_, eqNListA_trans (eqNListA_symm hls.1) hlsA', ?_⟩
      · rw [htk']; exact hTF'
      · rw [htk']; exact hspR
      · rw [htk', hdr']
        exact hI.comp hl₀' (eqNListB_symm hls hlC.2) hTF' hTF₀ hflip hwR
      · rw [htk']; exact hspR'
      · rw [htk', hdr']
        exact hI.comp hl₀' (eqNListB_symm hls hlC.2) hTF' hTF₀ hflip hwR'
    · rw [hP₂, carrierLevelsA_foldAppsA]
      exact ⟨argsRelA_mono (fun D x y hd => ⟨hd.1, eqNListA_trans hd.2.1 hls.1, hd.2.2⟩)
        (famFunRelA_mono (fun _ _ D x y hd => ⟨hd.1, eqNListA_trans hd.2.1 hls.1, hd.2.2⟩)) hargs.1, hargs.2⟩
  · exact Or.inr ⟨N, N', tyHRedStarA_retype hc ha, tyHRedStarA_retype hc hb, hN, hN'⟩

/-- what a recursive position (or the result) of two related constructor telescopes
    carries: its two domains are applications of the family at `=ₙ` levels, with the
    parameters `ps` on the left and `ps'` on the right, indices related along the
    family telescope from the LEFT parameters, and convertible. Across parameters it
    is `EqKA.fam`'s cross datum; within a fiber (`ps' = ps`) the clause's `hFldRec`. The left
    domain's levels are `=ₙ` the fiber's `ls₀` (a recursive domain never leaves its fiber). -/
def RecDomRelXA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ls₀ : List Level) (ps ps' : List ExprA)
    (A A' : ExprA) : Prop :=
  ∃ (lsA lsA' : List Level) (isA isA' : List ExprA) (TF TF' : ExprA),
    A = foldAppsA (.const r lsA) (ps ++ isA) ∧ A' = foldAppsA (.const r lsA') (ps' ++ isA') ∧
    eqNListB n ls₀ lsA ∧ eqNListB n lsA lsA' ∧ applyTelA ps (instantiateLevelsA lsA m.mtypeA) = some TF ∧
    applyTelA ps' (instantiateLevelsA lsA' m.mtypeA) = some TF' ∧
    ArgsRelPA (RsF lsA) m.nparamsA ps TF isA isA' ∧
    Nonempty (TyConvA E I n Γ A A')

/-- within a fiber. -/
abbrev RecDomRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ls₀ : List Level) (ps : List ExprA)
    (A A' : ExprA) : Prop :=
  RecDomRelXA E I n Γ r m RsF ls₀ ps ps A A'

/-- the fixed point moves both ways between related recursive domains of a fiber (at a
    world `ρ`, `ps` the fiber's parameters there). -/
theorem lfpWA_recDom {ρ : WkSpecA} {ps : List ExprA} {ls₀ : List Level}
    (hI : IdxPerA n (RsF ρ) m ps ls₀) (hps : ps.length = m.nparamsA) {A A' : ExprA}
    (hd : RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ ps A A') {a b : ExprA} :
    (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A' a b) ∧
    (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A' a b → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b) := by
  obtain ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', hl₀, hls, hTF, hTF', hw, hc⟩ := hd
  subst hA; subst hA'
  exact ⟨lfpWA_carrier hI hps hl₀.1 hls hTF hTF' hw hc,
    lfpWA_carrier hI hps (eqNListA_trans hl₀.1 hls.1) (eqNListB_symm hls hl₀.2) hTF' hTF
      (hI.flip hl₀ hls hTF hTF' hw) (hc.elim fun c => ⟨c.symm⟩)⟩

/-- the right domain of a cross-related pair lies on the right parameters, at levels `=ₙ` any list
    the left domain's are. -/
theorem recDomRelXA_right {RsF₀ : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {Γ₀ : LCtxA}
    {ls₀ : List Level} {ps ps' : List ExprA} (hps' : ps'.length = m.nparamsA) {A A' : ExprA}
    (hd : RecDomRelXA E I n Γ₀ r m RsF₀ ls₀ ps ps' A A') {L : List Level}
    (hL : eqNList (carrierLevelsA A) L) : carrierParamsA m A' = ps' ∧ eqNList (carrierLevelsA A') L := by
  obtain ⟨lsA, lsA', isA, isA', _, _, hA, hA', _, hls, _, _, _, _⟩ := hd
  subst hA; subst hA'
  rw [carrierLevelsA_foldAppsA] at hL
  refine ⟨carrierParamsA_famApp hps' lsA', ?_⟩
  rw [carrierLevelsA_foldAppsA]
  exact eqNListA_trans (eqNListA_symm hls.1) hL

/-- and the left domain on the left parameters, at levels `=ₙ` any list the right domain's are. -/
theorem recDomRelXA_left {RsF₀ : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {Γ₀ : LCtxA}
    {ls₀ : List Level} {ps ps' : List ExprA} (hps : ps.length = m.nparamsA) {A A' : ExprA}
    (hd : RecDomRelXA E I n Γ₀ r m RsF₀ ls₀ ps ps' A A') {L : List Level}
    (hL : eqNList (carrierLevelsA A') L) : carrierParamsA m A = ps ∧ eqNList (carrierLevelsA A) L := by
  obtain ⟨lsA, lsA', isA, isA', _, _, hA, hA', _, hls, _, _, _, _⟩ := hd
  subst hA; subst hA'
  rw [carrierLevelsA_foldAppsA] at hL
  refine ⟨carrierParamsA_famApp hps lsA, ?_⟩
  rw [carrierLevelsA_foldAppsA]
  exact eqNListA_trans hls.1 hL

/-- a cross-related pair at an extension `ρ'` of a world `ρ` is one at the composed world. -/
theorem recDomRelXA_comp_world {RsF₀ : List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {Γ₀ : LCtxA} {ρ ρ' : WkSpecA} {ls₀ : List Level} {ps ps' : List ExprA} {A A' : ExprA}
    (h : RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ₀)) r m RsF₀ ls₀ ((ps.map (wkExprA ρ)).map (wkExprA ρ'))
      ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) A A') :
    RecDomRelXA E I n (wkCtxA (WkSpecA.comp ρ ρ') Γ₀) r m RsF₀ ls₀ (ps.map (wkExprA (WkSpecA.comp ρ ρ')))
      (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) A A' := by
  rw [wkCtxA_comp, ← map_wkExprA_comp, ← map_wkExprA_comp]
  exact h

/-- what the inner walks of a function-recursive position need within a fiber (R-NoFunRec-1 step 1
    (1b)), at an extension of the walk's world: the left inner relations `RI` along `A`, the right
    `RI'` along `A'`. A right inner walk flips to a left one; a left one relates its right arguments to
    themselves on the right; after `j + 1` left-related inner arguments the two codomains reached are
    related recursive domains. -/
def InnerPerA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ls₀ : List Level) (ps : List ExprA)
    (RI RI' : Nat → List ExprA → ExprA → ExprA → Prop) (A A' : ExprA) (j : Nat) : Prop :=
  (∀ zs zs' : List ExprA, ArgsRelPA RI' 0 [] A' zs zs' → ArgsRelPA RI 0 [] A zs' zs) ∧
  (∀ zs zs' : List ExprA, ArgsRelPA RI 0 [] A zs zs' → ArgsRelPA RI' 0 [] A' zs' zs') ∧
  (∀ (zs zs' : List ExprA) (C C' : ExprA), ArgsRelPA RI 0 [] A zs zs' → zs.length = j + 1 →
    applyTelA zs A = some C → applyTelA zs' A' = some C' → RecDomRelA E I n Γ r m RsF ls₀ ps C C')

/-- what a constructor walk needs at its positions within a fiber, at two `=ₙ` level
    lists and related prefixes: the Π on the second telescope; at a plain position the
    flipped pair and the composite pair; at a directly recursive position the two domains
    related; at a function-recursive one, at every well-formed extension `ρ'` of the fiber's
    world, the inner walks' data (`InnerPerA`, the codomains at the fiber's data there `RsFX ρ'`), and
    the two declared domains type-convertible (R-NoFunRec-1 step 1 (1c-ε2d-L1; carried, not read yet).
    The walks' recursive positions read `X` (the fixed point at the world the fiber lies in) and
    `XF ρ'` (at its extensions), their inner positions `RI` (R-NoFunRec-1 step 1 (1b)). -/
def CtorPerA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (X : CRelA) (XF : WkSpecA → CRelA)
    (RsFX : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ps : List ExprA)
    (ls₀ : List Level) : Prop :=
  ∀ (c : Nat) (cm : CheckedMemberA) (kinds : List FieldShape) (lsA lsC lsC' : List Level) (T T' : ExprA),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → eqNList ls₀ lsA → eqNListB n lsA lsC →
    eqNListB n lsC lsC' →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
    ∀ (kd : FieldShape) (ksPre ks : List FieldShape) (pre pre' q : List ExprA) (A : ExprA) (u : Level)
      (B : ExprA) (v : Level), kinds = ksPre ++ kd :: ks →
      ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
        m.nparamsA ps T ksPre pre pre' →
      ArgsRelA (Rs c lsC') (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC') ps lsA XF)
        m.nparamsA ps T' ksPre pre' q →
      applyTelA pre T = some (.pi A u B v) →
      ∃ A' u' B' v', applyTelA pre' T' = some (.pi A' u' B' v') ∧
        (kd = .nonrecursive →
          (∀ f f', Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre) f f' →
            Rs c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') f' f) ∧
          (∀ f₁ f₂ f₃, Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre) f₁ f₂ →
            Rs c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') f₂ f₃ →
            Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre) f₁ f₃)) ∧
        (kd = .recursive 0 → RecDomRelA E I n Γ r m RsF ls₀ ps A A') ∧
        (∀ j, kd = .recursive (j + 1) → ∀ ρ', WkOkA E I n ρ' Γ →
          InnerPerA E I n (wkCtxA ρ' Γ) r m (RsFX ρ') ls₀ (ps.map (wkExprA ρ'))
            (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ')
            (RI c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') ρ') (wkExprA ρ' A) (wkExprA ρ' A') j) ∧
        (∀ j, kd = .recursive (j + 1) → Nonempty (TyConvA E I n Γ A A'))

/-- a fiber's walk data at EVERY world of the clause (R-NoFunRec-1 step 1 (1a)): there the
    index walks and the constructor walks flip and compose (`IdxPerA`, and `CtorPerA` at the
    fixed point of that world and of its extensions), the fiber's parameters weakened to it. -/
abbrev FiberPerWA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat)
    (m : CheckedMemberA) (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
    (ps : List ExprA) (ls₀ : List Level) : Prop :=
  ∀ ρ : WkSpecA, WkOk₀A E I n ρ Γ → IdxPerA n (RsF ρ) m (ps.map (wkExprA ρ)) ls₀ ∧
    CtorPerA E I n (wkCtxA ρ Γ) r m (Rs ρ) (RsF ρ) (fun c lsC => innerRelsA RsI ρ c lsC)
      (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ)
      (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))
      (fun ρ' => RsF (WkSpecA.comp ρ ρ')) (ps.map (wkExprA ρ)) ls₀

/-- **the fixed point is symmetric on a fiber** (the conjunction device: induction
    with the pair of both orientations as the pre-fixed point; the motive at every world). -/
theorem lfpWA_symm {ps : List ExprA} {ls₀ : List Level} (hP : FiberPerWA E I n Γ r m Rs RsF RsI ps ls₀)
    (hps : ps.length = m.nparamsA) :
    ∀ {ρ : WkSpecA} {A a b : ExprA}, WkOk₀A E I n ρ Γ → carrierParamsA m A = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA A) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A b a := by
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps
  intro ρ A a b hρ hAp hAl h
  have hY := h (fun ρ C x y => WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA C) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧ LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C y x)
    (fun ρ C x y hs hρ hCp hCl => by
      obtain ⟨hI, hC⟩ := hP ρ hρ
      have hX : ∀ D f f', famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (fun C x y =>
            WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) → eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧ LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C y x)
            D f f' →
          famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ)
            D f f' ∧
          LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ D f' f ∧ eqNList ls₀ (carrierLevelsA D) :=
        fun D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 hρ hd.1 hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2, hlD⟩
      -- and at the world's well-formed extensions
      have hXF : ∀ ρ', WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ D f f',
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C) (fun C x y =>
            WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ → carrierParamsA m C = ps.map (wkExprA (WkSpecA.comp ρ ρ')) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C x y ∧
              LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C y x) D f f' →
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')) D f f' ∧
          LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') D f' f ∧
          eqNList ls₀ (carrierLevelsA D) :=
        fun ρ' hρ' D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 (wkOk₀A_comp_ext hρ hρ') (hd.1.trans (map_wkExprA_comp ρ ρ' ps)) hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2, hlD⟩
      refine ⟨LfpWA.fold famPhiWA_mono (famPhiA_fib_mono (fun D f f' hd => by
          rw [hCp] at hd ⊢; exact (hX D f f' hd).1) (fun ρ' hρ' D f f' hd => by
          rw [hCp] at hd ⊢; exact (hXF ρ' hρ' D f f' hd).1) hs), ?_⟩
      obtain ⟨hcv, hs⟩ := hs
      refine LfpWA.fold famPhiWA_mono ⟨hcv.elim fun c => ⟨.symm _ _ _ _ c⟩, ?_⟩
      rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hlsC,
          hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
      · refine Or.inl ⟨c, cm, lsC', lsC, kinds, ps₂, ps₁, fs', fs, T', T, hcm, hk, hfam,
          ⟨eqNListB_trans hlC.1 hlsC, hlC.2⟩, eqNListB_symm hlsC hlC.1.2, hkinds, hT', hT, famCohA_swap hcoh, hp₂, hp₁,
          hb, ha, hnb, hna, ?_, hargs.2.2, hargs.2.1⟩
        rw [hCp] at hT hT' hargs ⊢
        have hl₀C : eqNList ls₀ (carrierLevelsA C) := hCl
        have hflip := argsRelA_flip (X' := famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC') (ps.map (wkExprA ρ))
              (carrierLevelsA C) (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            kinds
          (fun kd ksPre ks pre pre' A u B v hsp hp hp' hT₀ => by
            obtain ⟨A', u', B', v', hT₀', hpl, hrec, hfun, hdomC⟩ := hC c cm kinds (carrierLevelsA C) lsC lsC' T T'
              hcm hk hfam hkinds hl₀C hlC.1 hlsC hT hT' kd ksPre ks pre pre' pre A u B v hsp
              (argsRelA_mono (fun D f f' hd => (hX D f f' hd).1)
                (famFunRelA_mono (fun ρ' hρ' D f f' hd => (hXF ρ' hρ' D f f' hd).1)) hp) hp' hT₀
            refine ⟨A', u', B', v', hT₀', ?_⟩
            cases kd using FieldShape.cases3 with
            | funRec j =>
                -- the inner walks flip back; the codomains reached are related recursive domains
                intro f f' hff
                simp only [kindRelA] at hff ⊢
                refine famFunRelA_flip (hdomC j rfl) (fun ρ' hρ' zs zs' hzs => (hfun j rfl ρ' hρ').1 zs zs' hzs)
                  (fun ρ' hρ' zs zs' D D' x y hw hlen hD hD' hxy => ?_) hff
                have hxy' := hXF ρ' hρ' D x y hxy
                have hrd := (hfun j rfl ρ' hρ').2.2 zs' zs D D' hw hlen hD hD'
                obtain ⟨hpD', hlD'⟩ := recDomRelXA_right (by rw [List.length_map]; exact hpsρ ρ) hrd
                  hxy'.1.2.1
                exact ⟨hpD', hlD', (lfpWA_recDom (hP _ (wkOk₀A_comp_ext hρ hρ')).1 (hpsρ _)
                  (recDomRelXA_comp_world hrd)).1 hxy'.2.1⟩
            | plain => exact (hpl rfl).1
            | directRec =>
                intro f f' hff
                have hX' := hX A f f' hff
                have hrd := hrec rfl
                obtain ⟨lsA, lsA', isA, isA', TFa, TFa', hA, hA', _, hlsAA, _, _, _, _⟩ := id hrd
                have hlA : carrierLevelsA A = lsA := by rw [hA, carrierLevelsA_foldAppsA]
                refine ⟨?_, ?_, (lfpWA_recDom hI (hpsρ ρ) hrd).1 hX'.2.1⟩
                · rw [hA', carrierParamsA_famApp (hpsρ ρ)]
                · rw [hA', carrierLevelsA_foldAppsA]
                  have h1 := hX'.1.2.1
                  rw [hlA] at h1
                  exact eqNListA_trans (eqNListA_symm hlsAA.1) h1)
          hargs.1 [] [] [] T' (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
        simpa using hflip
      · exact Or.inr ⟨N', N, hb, ha, hN', hN⟩)
  exact (hY hρ hAp hAl).2

/-- **the fixed point is transitive on a fiber**: the middle term's two reducts are one
    (`tyHRedStarA_det`, both normal), so a constructor meets a constructor of the same
    name and arguments, and never a stuck term. -/
theorem lfpWA_trans {ps : List ExprA} {ls₀ : List Level} (hP : FiberPerWA E I n Γ r m Rs RsF RsI ps ls₀)
    (hps : ps.length = m.nparamsA) :
    ∀ {ρ : WkSpecA} {A a b c : ExprA}, WkOk₀A E I n ρ Γ → carrierParamsA m A = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA A) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A b c → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a c := by
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps
  intro ρ A a b c hρ hAp hAl h
  have hY := h (fun ρ C x y => WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA C) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧
      ∀ z, LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C y z → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x z)
    (fun ρ C x y hs hρ hCp hCl => by
      obtain ⟨hI, hC⟩ := hP ρ hρ
      have hX : ∀ D f f', famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (fun C x y =>
            WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) → eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧
            ∀ z, LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C y z →
              LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x z) D f f' →
          famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ)
            D f f' ∧
          (∀ z, LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ D f' z →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ D f z) ∧
          eqNList ls₀ (carrierLevelsA D) :=
        fun D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 hρ hd.1 hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2, hlD⟩
      -- and at the world's well-formed extensions
      have hXF : ∀ ρ', WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ D f f',
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C) (fun C x y =>
            WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ → carrierParamsA m C = ps.map (wkExprA (WkSpecA.comp ρ ρ')) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C x y ∧
            ∀ z, LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C y z →
              LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C x z) D f f' →
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')) D f f' ∧
          (∀ z, LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') D f' z →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') D f z) ∧
          eqNList ls₀ (carrierLevelsA D) :=
        fun ρ' hρ' D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 (wkOk₀A_comp_ext hρ hρ') (hd.1.trans (map_wkExprA_comp ρ ρ' ps)) hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2, hlD⟩
      refine ⟨LfpWA.fold famPhiWA_mono (famPhiA_fib_mono (fun D f f' hd => by
          rw [hCp] at hd ⊢; exact (hX D f f' hd).1) (fun ρ' hρ' D f f' hd => by
          rw [hCp] at hd ⊢; exact (hXF ρ' hρ' D f f' hd).1) hs), fun z hyz => ?_⟩
      obtain ⟨hcv, hs⟩ := hs
      obtain ⟨hcv₂, hs₂⟩ := LfpWA.unfold famPhiWA_mono hyz
      refine LfpWA.fold famPhiWA_mono
        ⟨hcv.elim fun c₁ => hcv₂.elim fun c₂ => ⟨.trans _ _ _ _ _ c₁ c₂⟩, ?_⟩
      rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hlsC,
          hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
      · rcases hs₂ with ⟨c₂, cm₂, lsD, lsD', kinds₂, ps₃, ps₄, gs, gs', U, U', hcm₂, hk₂, hfam₂, hlD,
            hlsD, hkinds₂, hU, hU', hcoh₂, hp₃, hp₄, ha₂, hb₂, hna₂, hnb₂, hargs₂⟩ | ⟨M, M', ha₂, _, hM, _⟩
        · have e := tyHRedStarA_det hb ha₂ hnb hna₂
          obtain ⟨ec, els, eargs⟩ := foldAppsA_const_inj e
          subst ec; subst els
          have hpl : ps₂.length = ps₃.length := by rw [hp₂, hp₃]
          obtain ⟨eps, efs⟩ := List.append_inj eargs hpl
          subst eps; subst efs
          rw [hcm] at hcm₂
          injection hcm₂ with ecm
          subst ecm
          rw [hkinds] at hkinds₂
          injection hkinds₂ with ek
          subst ek
          rw [hT'] at hU
          injection hU with eU
          subst eU
          refine Or.inl ⟨c, cm, lsC, lsD', kinds, ps₁, ps₄, fs, gs', T, U', hcm, hk, hfam, hlC,
            eqNListB_trans hlsC hlsD, hkinds, hT, hU', ?_, hp₁, hp₄, ha, hb₂, hna, hnb₂, ?_, hargs.2.1,
            hargs₂.2.2⟩
          · obtain ⟨lsA, lsR, _, xsA, isR, _, TF, R₁, _, hspA, hTF, hta, hspR, hlsA, hwR, _, _, _, _⟩ := hcoh
            obtain ⟨lsA₂, _, lsR₂', xsA₂, _, isR₂', TF₂, _, R₂', hspA₂, hTF₂, _, _, _, _, hta₂', hspR₂',
              hlsA₂', hwR₂'⟩ := hcoh₂
            rw [hspA] at hspA₂
            injection hspA₂ with h1 h2
            injection h1 with _ h1
            subst h1; subst h2
            rw [hTF] at hTF₂
            injection hTF₂ with hTF₂
            subst hTF₂
            exact ⟨lsA, lsR, lsR₂', xsA, isR, isR₂', TF, R₁, R₂', hspA, hTF, hta, hspR, hlsA, hwR, hta₂',
              hspR₂', hlsA₂', hwR₂'⟩
          · rw [hCp] at hT hT' hargs hargs₂ ⊢
            have hl₀C : eqNList ls₀ (carrierLevelsA C) := hCl
            have hcomp := argsRelA_comp (X₂ := famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
                (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (X₃ := famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
                (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (F₂ := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC') (ps.map (wkExprA ρ))
                (carrierLevelsA C) (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
              (F₃ := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ))
                (carrierLevelsA C) (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
              kinds
              (fun kd ksPre ks p₁ p₂ p₃ A u B v hsp hp₁₂ hp₂₃ _ hT₀ => by
                obtain ⟨A', u', B', v', hT₀', hpl, hrec, hfun, hdomC⟩ := hC c cm kinds (carrierLevelsA C) lsC lsC'
                  T T' hcm hk hfam hkinds hl₀C hlC.1 hlsC hT hT' kd ksPre ks p₁ p₂ p₃ A u B v hsp
                  (argsRelA_mono (fun D f f' hd => (hX D f f' hd).1)
                    (famFunRelA_mono (fun ρ' hρ' D f f' hd => (hXF ρ' hρ' D f f' hd).1)) hp₁₂) hp₂₃ hT₀
                refine ⟨A', u', B', v', hT₀', ?_⟩
                cases kd using FieldShape.cases3 with
                | funRec j =>
                    -- the middle inner arguments related to themselves; the codomains reached related
                    intro f₁ f₂ f₃ h₁₂ h₂₃
                    simp only [kindRelA] at h₁₂ h₂₃ ⊢
                    refine famFunRelA_comp (hdomC j rfl) (fun ρ' hρ' zs zs'' hzs => (hfun j rfl ρ' hρ').2.1 zs zs'' hzs)
                      (fun ρ' hρ' zs zs'' D D₂ x y z hw hlen hD hD₂ hxy hyz => ?_) h₁₂ h₂₃
                    have hxy' := hXF ρ' hρ' D x y hxy
                    have hrd := (hfun j rfl ρ' hρ').2.2 zs zs'' D D₂ hw hlen hD hD₂
                    exact ⟨hxy'.1.1, hxy'.1.2.1, hxy'.2.1 z ((lfpWA_recDom (hP _ (wkOk₀A_comp_ext hρ hρ')).1
                      (hpsρ _) (recDomRelXA_comp_world hrd)).2 hyz.2.2)⟩
                | plain => exact (hpl rfl).2
                | directRec =>
                    intro f₁ f₂ f₃ h₁₂ h₂₃
                    have hX₁ := hX A f₁ f₂ h₁₂
                    exact ⟨hX₁.1.1, hX₁.1.2.1,
                      hX₁.2.1 f₃ ((lfpWA_recDom hI (hpsρ ρ) (hrec rfl)).2 h₂₃.2.2)⟩)
              hargs.1 [] [] [] [] T' gs' (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
              (.nil _ _ _) (by simpa using hargs₂.1)
            exact hcomp
        · have e := tyHRedStarA_det hb ha₂ hnb hM.1
          exact absurd (e ▸ ctorHeadA_foldAppsA hcm hk lsC' (ps₂ ++ fs')) hM.2
      · rcases hs₂ with ⟨c₂, cm₂, lsD, _, _, ps₃, _, gs, _, _, _, hcm₂, hk₂, _, _, _, _, _, _, _, _, _,
            ha₂, _, hna₂, _, _⟩ | ⟨M, M', ha₂, hb₂, _, hM'⟩
        · have e := tyHRedStarA_det hb ha₂ hN'.1 hna₂
          exact absurd (e ▸ ctorHeadA_foldAppsA hcm₂ hk₂ lsD (ps₃ ++ gs)) hN'.2
        · exact Or.inr ⟨N, M', ha, hb₂, hN, hM'⟩)
  exact fun hbc => (hY hρ hAp hAl).2 c hbc

end FixedPoint

/-! ## (6) across fibers: the cross move (M2-f (3c))

Two clauses' data at two parameter lists: `(Rs, RsF)` on the fiber `(ps, ls₀)` and
`(Rs', RsF')` on `(ps', ls₀')`. What `EqKA.fam`'s cross data supply at the identity
world — every walk taken from the LEFT parameters, the relation equalities from the
transport induction hypotheses (`CrossDataA`) — carries the left fixed point to the
right one along cross-related carriers (`RecDomRelXA`), and back. -/

/-- what the inner walks of a function-recursive position need to cross between fibers
    (R-NoFunRec-1 step 1 (1b)), at an extension of the walks' world: the inner walks move both ways
    between the left relations `RI` along `A` and the right `RI'` along `A'`, and after `j + 1`
    left-related inner arguments the two codomains reached are cross-related. -/
def InnerCrossA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ls₀ : List Level) (ps ps' : List ExprA)
    (RI RI' : Nat → List ExprA → ExprA → ExprA → Prop) (A A' : ExprA) (j : Nat) : Prop :=
  (∀ zs zs' : List ExprA, ArgsRelPA RI' 0 [] A' zs zs' → ArgsRelPA RI 0 [] A zs zs') ∧
  (∀ zs zs' : List ExprA, ArgsRelPA RI 0 [] A zs zs' → ArgsRelPA RI' 0 [] A' zs zs') ∧
  (∀ (zs zs' : List ExprA) (C C' : ExprA), ArgsRelPA RI 0 [] A zs zs' → zs.length = j + 1 →
    applyTelA zs A = some C → applyTelA zs A' = some C' → RecDomRelXA E I n Γ r m RsF ls₀ ps ps' C C')

/-- what the carrier needs to cross between the fibers `(ps, ls₀)` and `(ps', ls₀')`:
    (F) the index relations agree at doubly-walked prefixes across the parameters (one level
    list),
    (C) so do the plain-field relations, (R) the directly recursive domains are cross-related,
    (I) at a function-recursive position, at every well-formed extension `ρ'` of the fibers' world,
    the inner walks cross (`InnerCrossA`, the codomains at the left fiber's data there `RsFX ρ'`;
    R-NoFunRec-1 step 1 (1b)),
    (S) so are both lists' results, (P) the two parameter lists are convertible along the family's
    telescope at every bounded list `=ₙ` the fiber's (M2-f (6)), (D) the declared Π-domains of a
    function-recursive position type-convertible across the parameters (R-NoFunRec-1 step 1
    (1c-ε2d-L1); carried, not read yet). Every walk is taken from the LEFT
    parameters; its recursive positions read `X` on the left and `X'` on the right (the two fixed
    points at the world the fibers lie in), `XF ρ'` and `XF' ρ'` at its extensions, its inner positions
    `RI` and `RI'`. -/
def CrossDataA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs Rs' : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF RsF' : List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RI RI' : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (X X' : CRelA) (XF XF' : WkSpecA → CRelA)
    (RsFX : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (ps ps' : List ExprA) (ls₀ ls₀' : List Level) : Prop :=
  (∀ (lsF : List Level) (TF TF' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
      (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    eqNListB n ls₀ lsF →
    applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
    applyTelA ps' (instantiateLevelsA lsF m.mtypeA) = some TF' →
    ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' →
    ArgsRelPA (RsF' lsF) m.nparamsA ps' TF' pre pre' →
    applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre TF' = some (.pi D' uD' C' vC') →
    RsF lsF (m.nparamsA + pre.length) (ps ++ pre) = RsF' lsF (m.nparamsA + pre.length) (ps' ++ pre)) ∧
  (∀ (c : Nat) (cm : CheckedMemberA) (lsA lsA' lsC : List Level) (kinds ksPre ks : List FieldShape)
      (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
    eqNList ls₀ lsA → eqNListB n lsA lsC → eqNList ls₀' lsA' → eqNListB n lsA' lsC →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps' (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
    ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
      m.nparamsA ps T ksPre pre pre' →
    ArgsRelA (Rs' c lsC) (famRecRelA m ps' lsA' X') (famFunRelA E I n Γ m (RI' c lsC) ps' lsA' XF')
      m.nparamsA ps' T' ksPre pre pre' →
    applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
    Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre) =
      Rs' c lsC (m.nparamsA + ksPre.length) (ps' ++ pre)) ∧
  (∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
      (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
    eqNList ls₀ lsA → eqNListB n lsA lsC →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps' (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
    ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
      m.nparamsA ps T ksPre pre pre' →
    applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
    RecDomRelXA E I n Γ r m RsF ls₀ ps ps' D D') ∧
  (∀ (c : Nat) (cm : CheckedMemberA) (lsA lsA' lsC : List Level) (kinds ksPre ks : List FieldShape)
      (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
    eqNList ls₀ lsA → eqNListB n lsA lsC → eqNList ls₀' lsA' → eqNListB n lsA' lsC →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps' (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
    ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
      m.nparamsA ps T ksPre pre pre' →
    ArgsRelA (Rs' c lsC) (famRecRelA m ps' lsA' X') (famFunRelA E I n Γ m (RI' c lsC) ps' lsA' XF')
      m.nparamsA ps' T' ksPre pre pre' →
    applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
    ∀ ρ', WkOkA E I n ρ' Γ →
      InnerCrossA E I n (wkCtxA ρ' Γ) r m (RsFX ρ') ls₀ (ps.map (wkExprA ρ')) (ps'.map (wkExprA ρ'))
        (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ')
        (RI' c lsC (m.nparamsA + ksPre.length) (ps' ++ pre) ρ') (wkExprA ρ' D) (wkExprA ρ' D') j) ∧
  (∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level) (kinds : List FieldShape)
      (T T₁ T' T₁' : ExprA) (pre pre' : List ExprA) (R R₁ R' R₁' : ExprA),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
    eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps' (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T₁ →
    applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
    applyTelA ps' (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T₁' →
    ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
      m.nparamsA ps T kinds pre pre' →
    applyTelA pre T = some R → applyTelA pre T₁ = some R₁ →
    applyTelA pre' T' = some R' → applyTelA pre' T₁' = some R₁' →
    RecDomRelXA E I n Γ r m RsF ls₀ ps ps' R R₁ ∧ RecDomRelXA E I n Γ r m RsF ls₀ ps ps' R' R₁') ∧
  (∀ lsX : List Level, eqNListB n ls₀ lsX →
    ParConvA E I n Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) ps ps') ∧
  (∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
      (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
    ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
    eqNList ls₀ lsA → eqNListB n lsA lsC →
    applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
    applyTelA ps' (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
    ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
      m.nparamsA ps T ksPre pre pre' →
    applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
    Nonempty (TyConvA E I n Γ D D'))

/-- the index walks flip and compose at EVERY world of the clause (R-NoFunRec-1 step 1 (1a)),
    the fiber's parameters weakened to it. -/
abbrev IdxPerWA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (m : CheckedMemberA)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (ps : List ExprA)
    (ls₀ : List Level) : Prop :=
  ∀ ρ : WkSpecA, WkOk₀A E I n ρ Γ → IdxPerA n (RsF ρ) m (ps.map (wkExprA ρ)) ls₀

/-- the cross data at EVERY world of the clause (R-NoFunRec-1 step 1 (1a)): the two instances'
    data there, the parameters weakened to it, the walks at the two fixed points of that world and of
    its extensions. -/
abbrev CrossWA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs Rs' : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF RsF' : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI RsI' : InnerRelsA) (ps ps' : List ExprA) (ls₀ ls₀' : List Level) : Prop :=
  ∀ ρ : WkSpecA, WkOk₀A E I n ρ Γ → CrossDataA E I n (wkCtxA ρ Γ) r m (Rs ρ) (Rs' ρ) (RsF ρ) (RsF' ρ)
    (fun c lsC => innerRelsA RsI ρ c lsC) (fun c lsC => innerRelsA RsI' ρ c lsC)
    (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ) (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ)
    (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))
    (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ'))
    (fun ρ' => RsF (WkSpecA.comp ρ ρ'))
    (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) ls₀ ls₀'

section Cross
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
  {Rs Rs' : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
  {RsF RsF' : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI RsI' : InnerRelsA}

/-- **the carrier crosses from the left fiber to the right one** along cross-related
    carriers: induction on the left fixed point with, as pre-fixed point, the pair of
    the left fixed point and the crossed one; at a constructor form the telescopes are
    re-instantiated at the right parameters (rigid), the field walk crosses position by
    position (`argsRelA_cross`: (C) at plain positions, (R) and the induction
    hypothesis at recursive ones), and the index coherence goes left-flip, compose,
    compose with the results' cross datum (S), then crosses (F). -/
theorem lfpWA_cross_fwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hEN : EnvNormCtorTypeA E)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level} (hI : IdxPerWA E I n Γ m RsF ps ls₀)
    (hX : CrossWA E I n Γ r m Rs Rs' RsF RsF' RsI RsI' ps ps' ls₀ ls₀')
    (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA) (hl : eqNList ls₀ ls₀') :
    ∀ {ρ : WkSpecA} {A a b : ExprA}, WkOk₀A E I n ρ Γ → carrierParamsA m A = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA A) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b →
      ∀ {A' : ExprA}, RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ))
          (ps'.map (wkExprA ρ)) A A' →
        LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ A' a b := by
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps
  have hps'ρ : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps'
  have hplρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = (ps'.map (wkExprA ρ)).length := fun ρ => by
    rw [hpsρ, hps'ρ]
  intro ρ A a b hρ hAp hAl h
  have hY := h (fun ρ C x y => WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA C) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧
      ∀ C', RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) C C' →
        LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ C' x y)
    (fun ρ C x y hs hρ hCp hCl => by
      obtain ⟨hXF, hXC, hXR, hXI, hXS, hXP, hXD⟩ := hX ρ hρ
      have hIρ := hI ρ hρ
      have hXm : ∀ D f f', famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (fun C x y => WkOk₀A E I n ρ Γ →
            carrierParamsA m C = (ps.map (wkExprA ρ)) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y ∧
            ∀ C', RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) C C' →
              LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ C' x y) D f f' →
          famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ) D f f' ∧
          (∀ D', RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) D D' →
            LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ D' f f') :=
        fun D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 hρ hd.1 hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2⟩
      -- and at the world's well-formed extensions
      have hXFm : ∀ ρ', WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ D f f',
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C) (fun C x y =>
            WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ → carrierParamsA m C = ps.map (wkExprA (WkSpecA.comp ρ ρ')) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C x y ∧
            ∀ C', RecDomRelXA E I n (wkCtxA (WkSpecA.comp ρ ρ') Γ) r m (RsF (WkSpecA.comp ρ ρ')) ls₀
                (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) C C' →
              LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ') C' x y) D f f' →
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')) D f f' ∧
          (∀ D', RecDomRelXA E I n (wkCtxA (WkSpecA.comp ρ ρ') Γ) r m (RsF (WkSpecA.comp ρ ρ')) ls₀
              (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) D D' →
            LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ') D' f f') :=
        fun ρ' hρ' D f f' hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 (wkOk₀A_comp_ext hρ hρ') (hd.1.trans (map_wkExprA_comp ρ ρ' ps)) hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2⟩
      refine ⟨LfpWA.fold famPhiWA_mono (famPhiA_fib_mono (fun D f f' hd => by
          rw [hCp] at hd ⊢; exact (hXm D f f' hd).1) (fun ρ' hρ' D f f' hd => by
          rw [hCp] at hd ⊢; exact (hXFm ρ' hρ' D f f' hd).1) hs), fun C' hCC' => ?_⟩
      obtain ⟨lsA, lsA', isA, isA', TFA, TFA', hCe, hC'e, hl₀AB, hlsAA, hTFA, hTFA', hwA, hcA⟩ := id hCC'
      have hClA : carrierLevelsA C = lsA := by rw [hCe, carrierLevelsA_foldAppsA]
      have hC'lA : carrierLevelsA C' = lsA' := by rw [hC'e, carrierLevelsA_foldAppsA]
      have hC'p : carrierParamsA m C' = (ps'.map (wkExprA ρ)) := by rw [hC'e, carrierParamsA_famApp (hps'ρ ρ)]
      have hl₀A : eqNList ls₀ lsA := by rw [← hClA]; exact hCl
      have hl₀A' : eqNList ls₀ lsA' := eqNListA_trans hl₀A hlsAA.1
      have hl₀A'B : eqNListB n ls₀ lsA' := ⟨hl₀A', hlsAA.2⟩
      have hl₀'A' : eqNList ls₀' lsA' := eqNListA_trans (eqNListA_symm hl) hl₀A'
      obtain ⟨hcv, hs⟩ := hs
      refine LfpWA.fold famPhiWA_mono ⟨convA_retype hcA hcv, ?_⟩
      rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hlsC,
          hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
      · rw [hCp] at hT hT' hargs
        have hlAC : eqNListB n lsA lsC := by rw [← hClA]; exact hlC.1
        have hlA'C : eqNListB n lsA' lsC := ⟨eqNListA_trans (eqNListA_symm hlsAA.1) hlAC.1, hlAC.2⟩
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨T₁', hT₁'⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ ρ) hT'
        -- the field walk crosses
        have hargs₁ : ArgsRelA (Rs' ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA' (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI' ρ c lsC) (ps'.map (wkExprA ρ)) lsA'
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps'.map (wkExprA ρ)) T₁ kinds fs fs' := by
          have hw := argsRelA_cross
            (X' := famRecRelA m (ps'.map (wkExprA ρ)) lsA' (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ))
            (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI' ρ c lsC) (ps'.map (wkExprA ρ)) lsA'
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ'))) kinds
            (fun kd ksPre ks pre pre' D uD Cc vC hsp hp hp' hTD => by
              obtain ⟨D', uD', Cc', vC', hTD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT₁ rfl hTD
              refine ⟨D', uD', Cc', vC', hTD', ?_⟩
              have hpL := argsRelA_mono (fun D f f' hd => (hXm D f f' hd).1)
                (famFunRelA_mono (fun ρ' hρ' D f f' hd => (hXFm ρ' hρ' D f f' hd).1)) hp
              cases kd using FieldShape.cases3 with
              | funRec j =>
                  -- the inner walks cross; the codomains reached are cross-related
                  intro f f' hr
                  simp only [kindRelA] at hr ⊢
                  have hI' := hXI c cm (carrierLevelsA C) lsA' lsC kinds ksPre ks j T T₁ pre pre' D uD Cc vC
                    D' uD' Cc' vC' hcm hk hfam hkinds hsp hCl hlC.1 hl₀'A' hlA'C hT hT₁ hpL hp' hTD hTD'
                  have hdomX := hXD c cm (carrierLevelsA C) lsC kinds ksPre ks j T T₁ pre pre' D uD Cc vC D' uD'
                    Cc' vC' hcm hk hfam hkinds hsp hCl hlC.1 hT hT₁ hpL hTD hTD'
                  refine famFunRelA_cross hdomX (fun ρ' hρ' zs zs' hzs => (hI' ρ' hρ').1 zs zs' hzs)
                    (fun ρ' hρ' zs zs' El Er x y hw hlen hEl hEr hxy => ?_) hr
                  have hxy' := hXFm ρ' hρ' El x y hxy
                  have hrd := (hI' ρ' hρ').2.2 zs zs' El Er hw hlen hEl hEr
                  have h1 := hxy'.1.2.1
                  rw [hClA] at h1
                  obtain ⟨hpEr, hlEr⟩ := recDomRelXA_right (by rw [List.length_map]; exact hps'ρ ρ) hrd
                    (eqNListA_trans h1 hlsAA.1)
                  exact ⟨hpEr, hlEr, hxy'.2 Er (recDomRelXA_comp_world hrd)⟩
              | plain =>
                  intro f f' hr
                  have heq := hXC c cm (carrierLevelsA C) lsA' lsC kinds ksPre ks T T₁ pre pre' D uD Cc vC
                    D' uD' Cc' vC' hcm hk hfam hkinds hsp hCl hlC.1 hl₀'A' hlA'C hT hT₁ hpL hp' hTD hTD'
                  show Rs' ρ c lsC _ ((ps'.map (wkExprA ρ)) ++ pre) f f'
                  rw [← heq]; exact hr
              | directRec =>
                  intro f f' hr
                  have hrd := hXR c cm (carrierLevelsA C) lsC kinds ksPre ks T T₁ pre pre' D uD Cc vC
                    D' uD' Cc' vC' hcm hk hfam hkinds hsp hCl hlC.1 hT hT₁ hpL hTD hTD'
                  obtain ⟨lsD, lsD', isD, isD', _, _, hLe, hRe, _, hlsDD, _, _, _, _⟩ := id hrd
                  have hX' := hXm D f f' hr
                  refine ⟨by rw [hRe, carrierParamsA_famApp (hps'ρ ρ)], ?_, hX'.2 D' hrd⟩
                  rw [hRe, carrierLevelsA_foldAppsA]
                  have h1 := hX'.1.2.1
                  rw [hLe, carrierLevelsA_foldAppsA, hClA] at h1
                  exact eqNListA_trans (eqNListA_trans (eqNListA_symm hlsDD.1) h1) hlsAA.1)
            hargs.1 [] [] [] T₁ (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
          simpa using hw
        -- the index coherence: left-flip, compose, compose with the results' datum, cross
        have key : ∀ (Ra Rb : ExprA) (lsR : List Level) (isR : List ExprA),
            appsSpineA Ra = (.const r lsR, (ps.map (wkExprA ρ)) ++ isR) → eqNList lsA lsR →
            ArgsRelPA (RsF ρ lsA) m.nparamsA (ps.map (wkExprA ρ)) TFA isA isR →
            RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) Ra Rb →
            ∃ (lsRb : List Level) (isRb : List ExprA),
              appsSpineA Rb = (.const r lsRb, (ps'.map (wkExprA ρ)) ++ isRb) ∧ eqNList lsA' lsRb ∧
              ArgsRelPA (RsF' ρ lsA') m.nparamsA (ps'.map (wkExprA ρ)) TFA' isA' isRb := by
          intro Ra Rb lsR isR hspa hlsR hw hrd
          obtain ⟨lsRa, lsRb, isRa, isRb, TFRa, _, hRa, hRb, hl₀Ra, hlsRR, hTFRa, _, hwRR, _⟩ := hrd
          rw [hRa, foldAppsA_const_head] at hspa
          injection hspa with e1 e2
          injection e1 with _ e1
          have e2' : isRa = isR := List.append_cancel_left e2
          subst lsR
          subst isR
          refine ⟨lsRb, isRb, by rw [hRb, foldAppsA_const_head], ?_, ?_⟩
          · exact eqNListA_trans (eqNListA_trans (eqNListA_symm hlsAA.1) hlsR) hlsRR.1
          · obtain ⟨TFl', hTFl'⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsA lsA'
              (xs' := (ps.map (wkExprA ρ))) rfl hTFA
            have v1 := hIρ.flip hl₀AB hlsAA hTFA hTFl' hwA
            have v2 := hIρ.comp hl₀A'B (eqNListB_symm hlsAA hl₀AB.2) hTFl' hTFA v1 hw
            have v3 := hIρ.comp hl₀A'B ⟨eqNListA_trans (eqNListA_symm hlsAA.1) hlsR, hl₀Ra.2⟩ hTFl' hTFRa v2
              hwRR
            have v4 := argsRelPA_cross (R := RsF ρ lsA') (R' := RsF' ρ lsA') (i₀ := m.nparamsA)
              (prev₀ := (ps.map (wkExprA ρ))) (prev₀' := (ps'.map (wkExprA ρ))) (T₀ := TFl') (T₀' := TFA')
              (fun pre pre' D uD Cc vC hp hp' hTD => by
                obtain ⟨D', uD', Cc', vC', hTD'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ ρ)
                  hTFl' hTFA' rfl hTD
                refine ⟨D', uD', Cc', vC', hTD', fun f f' hr => ?_⟩
                have heq := hXF lsA' TFl' TFA' pre pre' D uD Cc vC D' uD' Cc' vC' hl₀A'B hTFl' hTFA' hp hp'
                  hTD hTD'
                rw [← heq]; exact hr)
              v3 [] [] TFA' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
            simpa using v4
        obtain ⟨lsA₀, lsR, lsR', xsA, isR, isR', TF₀, R₁, R₁', hspA, hTF₀, hta, hspR, hlsA, hwR, hta',
          hspR', hlsA', hwR'⟩ := hcoh
        rw [hCe, foldAppsA_const_head] at hspA
        injection hspA with h1 h2
        injection h1 with _ h1
        subst lsA₀
        subst xsA
        have htk : ((ps.map (wkExprA ρ)) ++ isA).take m.nparamsA = (ps.map (wkExprA ρ)) := by rw [← (hpsρ ρ), List.take_left]
        have hdr : ((ps.map (wkExprA ρ)) ++ isA).drop m.nparamsA = isA := by rw [← (hpsρ ρ), List.drop_left]
        rw [htk] at hTF₀ hspR hwR hspR' hwR'
        rw [hdr] at hwR hwR'
        rw [hTF₀] at hTFA
        injection hTFA with e
        subst TF₀
        obtain ⟨R₂, hR₂⟩ := applyTelA_some_cross hrig (hplρ ρ) hT hT₁ rfl hta
        obtain ⟨R₂', hR₂'⟩ := applyTelA_some_cross hrig (hplρ ρ) hT' hT₁' rfl hta'
        obtain ⟨hrd, hrd'⟩ := hXS c cm (carrierLevelsA C) lsC lsC' kinds T T₁ T' T₁' fs fs' R₁ R₂ R₁' R₂'
          hcm hk hfam hkinds hCl hlC.1 hlsC hT hT₁ hT' hT₁'
          (argsRelA_mono (fun D f f' hd => (hXm D f f' hd).1)
            (famFunRelA_mono (fun ρ' hρ' D f f' hd => (hXFm ρ' hρ' D f f' hd).1)) hargs.1) hta hR₂ hta' hR₂'
        obtain ⟨lsRb, isRb, hspRb, hlsRb, hwRb⟩ := key R₁ R₂ lsR isR hspR hlsA hwR hrd
        obtain ⟨lsRb', isRb', hspRb', hlsRb', hwRb'⟩ := key R₁' R₂' lsR' isR' hspR' hlsA' hwR' hrd'
        have htk' : ((ps'.map (wkExprA ρ)) ++ isA').take m.nparamsA = (ps'.map (wkExprA ρ)) := by rw [← (hps'ρ ρ), List.take_left]
        have hdr' : ((ps'.map (wkExprA ρ)) ++ isA').drop m.nparamsA = isA' := by rw [← (hps'ρ ρ), List.drop_left]
        refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T₁, T₁', hcm, hk, hfam, ?_, hlsC,
          hkinds, ?_, ?_, ⟨lsA', lsRb, lsRb', (ps'.map (wkExprA ρ)) ++ isA', isRb, isRb', TFA', R₂, R₂', ?_, ?_, hR₂, ?_,
            hlsRb, ?_, hR₂', ?_, hlsRb', ?_⟩, hp₁, hp₂, tyHRedStarA_retype hcA ha,
          tyHRedStarA_retype hcA hb, hna, hnb, ?_⟩
        · rw [hC'lA]; exact ⟨hlA'C, hlsAA.2⟩
        · rw [hC'p]; exact hT₁
        · rw [hC'p]; exact hT₁'
        · rw [hC'e, foldAppsA_const_head]
        · rw [htk']; exact hTFA'
        · rw [htk']; exact hspRb
        · rw [htk', hdr']; exact hwRb
        · rw [htk']; exact hspRb'
        · rw [htk', hdr']; exact hwRb'
        · have hP0 : eqNListB n ls₀ lsC := ⟨eqNListA_trans hCl hlC.1.1, hlC.1.2⟩
          have hP0' : eqNListB n ls₀ lsC' := ⟨eqNListA_trans hP0.1 hlsC.1, hlsC.2⟩
          rw [hC'p, hC'lA]
          exact ⟨hargs₁, convArgsA_rebase (hXP lsC hP0) hargs.2.1, convArgsA_rebase (hXP lsC' hP0') hargs.2.2⟩
      · exact Or.inr ⟨N, N', tyHRedStarA_retype hcA ha, tyHRedStarA_retype hcA hb, hN, hN'⟩)
  intro A' hK
  exact (hY hρ hAp hAl).2 A' hK

/-- **and back**: the right fixed point crosses to the left along the same cross
    relation (the walks are rebuilt on the left, where every cross datum is stated). -/
theorem lfpWA_cross_bwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hEN : EnvNormCtorTypeA E)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level} (hI : IdxPerWA E I n Γ m RsF ps ls₀)
    (hX : CrossWA E I n Γ r m Rs Rs' RsF RsF' RsI RsI' ps ps' ls₀ ls₀')
    (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA) (hl : eqNList ls₀ ls₀') :
    ∀ {ρ : WkSpecA} {A' a b : ExprA}, WkOk₀A E I n ρ Γ → carrierParamsA m A' = ps'.map (wkExprA ρ) →
      eqNList ls₀' (carrierLevelsA A') →
      LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ A' a b →
      ∀ {A : ExprA}, RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ))
          (ps'.map (wkExprA ρ)) A A' →
        LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b := by
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps
  have hps'ρ : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by
    rw [List.length_map]; exact hps'
  have hplρ : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = (ps.map (wkExprA ρ)).length := fun ρ => by
    rw [hpsρ, hps'ρ]
  intro ρ A' a b hρ hA'p hA'l h
  have hY := h (fun ρ C' x y => WkOk₀A E I n ρ Γ → carrierParamsA m C' = ps'.map (wkExprA ρ) →
      eqNList ls₀' (carrierLevelsA C') →
      LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ C' x y ∧
      ∀ C, RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) C C' →
        LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y)
    (fun ρ C' x y hs hρ hC'p hC'l => by
      obtain ⟨hXF, hXC, hXR, hXI, hXS, hXP, hXD⟩ := hX ρ hρ
      have hIρ := hI ρ hρ
      have hXm : ∀ D' f f', famRecRelA m (ps'.map (wkExprA ρ)) (carrierLevelsA C') (fun C' x y => WkOk₀A E I n ρ Γ →
            carrierParamsA m C' = (ps'.map (wkExprA ρ)) →
            eqNList ls₀' (carrierLevelsA C') →
            LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ C' x y ∧
            ∀ C, RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) C C' → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C x y)
            D' f f' →
          famRecRelA m (ps'.map (wkExprA ρ)) (carrierLevelsA C') (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ) D' f f' ∧
          (∀ D, RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) D D' → LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ D f f') :=
        fun D' f f' hd => by
          have hlD : eqNList ls₀' (carrierLevelsA D') := eqNListA_trans hC'l (eqNListA_symm hd.2.1)
          have hh := hd.2.2 hρ hd.1 hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2⟩
      -- and at the world's well-formed extensions
      have hXFm : ∀ ρ', WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ D' f f',
          famRecRelA m ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C') (fun C' x y =>
            WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ → carrierParamsA m C' = ps'.map (wkExprA (WkSpecA.comp ρ ρ')) →
            eqNList ls₀' (carrierLevelsA C') →
            LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ') C' x y ∧
            ∀ C, RecDomRelXA E I n (wkCtxA (WkSpecA.comp ρ ρ') Γ) r m (RsF (WkSpecA.comp ρ ρ')) ls₀
                (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) C C' →
              LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') C x y) D' f f' →
          famRecRelA m ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C')
            (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ')) D' f f' ∧
          (∀ D, RecDomRelXA E I n (wkCtxA (WkSpecA.comp ρ ρ') Γ) r m (RsF (WkSpecA.comp ρ ρ')) ls₀
              (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) D D' →
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ') D f f') :=
        fun ρ' hρ' D' f f' hd => by
          have hlD : eqNList ls₀' (carrierLevelsA D') := eqNListA_trans hC'l (eqNListA_symm hd.2.1)
          have hh := hd.2.2 (wkOk₀A_comp_ext hρ hρ') (hd.1.trans (map_wkExprA_comp ρ ρ' ps')) hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, hh.2⟩
      refine ⟨LfpWA.fold famPhiWA_mono (famPhiA_fib_mono (fun D f f' hd => by
          rw [hC'p] at hd ⊢; exact (hXm D f f' hd).1) (fun ρ' hρ' D f f' hd => by
          rw [hC'p] at hd ⊢; exact (hXFm ρ' hρ' D f f' hd).1) hs), fun C hCC' => ?_⟩
      obtain ⟨lsA, lsA', isA, isA', TFA, TFA', hCe, hC'e, hl₀AB, hlsAA, hTFA, hTFA', hwA, hcA⟩ := id hCC'
      have hClA : carrierLevelsA C = lsA := by rw [hCe, carrierLevelsA_foldAppsA]
      have hC'lA : carrierLevelsA C' = lsA' := by rw [hC'e, carrierLevelsA_foldAppsA]
      have hCp : carrierParamsA m C = (ps.map (wkExprA ρ)) := by rw [hCe, carrierParamsA_famApp (hpsρ ρ)]
      have hl₀'A' : eqNList ls₀' lsA' := by rw [← hC'lA]; exact hC'l
      have hl₀A' : eqNList ls₀ lsA' := eqNListA_trans hl hl₀'A'
      have hl₀A : eqNList ls₀ lsA := eqNListA_trans hl₀A' (eqNListA_symm hlsAA.1)
      have hcA' : Nonempty (TyConvA E I n (wkCtxA ρ Γ) C' C) := hcA.elim fun c => ⟨c.symm⟩
      obtain ⟨hcv, hs⟩ := hs
      refine LfpWA.fold famPhiWA_mono ⟨convA_retype hcA' hcv, ?_⟩
      rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T₁, T₁', hcm, hk, hfam, hlC, hlsC,
          hkinds, hT₁, hT₁', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
      · rw [hC'p] at hT₁ hT₁' hargs
        have hlA'C : eqNListB n lsA' lsC := by rw [← hC'lA]; exact hlC.1
        have hlAC : eqNListB n lsA lsC := ⟨eqNListA_trans hlsAA.1 hlA'C.1, hlA'C.2⟩
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T, hT⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT₁
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ ρ) hT₁'
        -- the field walk crosses back
        have hargs₀ : ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T kinds fs fs' := by
          have hw := argsRelA_cross
            (X' := famRecRelA m (ps.map (wkExprA ρ)) lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) kinds
            (fun kd ksPre ks pre pre' D uD Cc vC hsp hp hp' hTD => by
              obtain ⟨D', uD', Cc', vC', hTD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT₁ hT rfl hTD
              refine ⟨D', uD', Cc', vC', hTD', ?_⟩
              have hpR := argsRelA_mono (fun D f f' hd => (hXm D f f' hd).1)
                (famFunRelA_mono (fun ρ' hρ' D f f' hd => (hXFm ρ' hρ' D f f' hd).1)) hp
              cases kd using FieldShape.cases3 with
              | funRec j =>
                  -- the inner walks cross back; the codomains reached are cross-related
                  intro f f' hr
                  simp only [kindRelA] at hr ⊢
                  have hI' := hXI c cm lsA (carrierLevelsA C') lsC kinds ksPre ks j T T₁ pre pre' D' uD' Cc'
                    vC' D uD Cc vC hcm hk hfam hkinds hsp hl₀A hlAC hC'l hlC.1 hT hT₁ hp' hpR hTD' hTD
                  have hdomX' := tyConvA_symm_ne (hXD c cm lsA lsC kinds ksPre ks j T T₁ pre pre' D' uD' Cc' vC' D uD Cc vC hcm hk
                    hfam hkinds hsp hl₀A hlAC hT hT₁ hp' hTD' hTD)
                  refine famFunRelA_cross hdomX' (fun ρ' hρ' zs zs' hzs => (hI' ρ' hρ').2.1 zs zs' hzs)
                    (fun ρ' hρ' zs zs' Er El x y hw hlen hEr hEl hxy => ?_) hr
                  have hxy' := hXFm ρ' hρ' Er x y hxy
                  have hrd := (hI' ρ' hρ').2.2 zs zs' El Er ((hI' ρ' hρ').1 zs zs' hw) hlen hEl hEr
                  have h1 := hxy'.1.2.1
                  rw [hC'lA] at h1
                  obtain ⟨hpEl, hlEl⟩ := recDomRelXA_left (by rw [List.length_map]; exact hpsρ ρ) hrd
                    (eqNListA_trans h1 (eqNListA_symm hlsAA.1))
                  exact ⟨hpEl, hlEl, hxy'.2 El (recDomRelXA_comp_world hrd)⟩
              | plain =>
                  intro f f' hr
                  have heq := hXC c cm lsA (carrierLevelsA C') lsC kinds ksPre ks T T₁ pre pre' D' uD' Cc'
                    vC' D uD Cc vC hcm hk hfam hkinds hsp hl₀A hlAC hC'l hlC.1 hT hT₁ hp' hpR hTD' hTD
                  show Rs ρ c lsC _ ((ps.map (wkExprA ρ)) ++ pre) f f'
                  rw [heq]; exact hr
              | directRec =>
                  intro f f' hr
                  have hrd := hXR c cm lsA lsC kinds ksPre ks T T₁ pre pre' D' uD' Cc' vC' D uD Cc vC
                    hcm hk hfam hkinds hsp hl₀A hlAC hT hT₁ hp' hTD' hTD
                  obtain ⟨lsD, lsD', isD, isD', _, _, hLe, hRe, _, hlsDD, _, _, _, _⟩ := id hrd
                  have hX' := hXm D f f' hr
                  refine ⟨by rw [hLe, carrierParamsA_famApp (hpsρ ρ)], ?_, hX'.2 D' hrd⟩
                  rw [hLe, carrierLevelsA_foldAppsA]
                  have h1 := hX'.1.2.1
                  rw [hRe, carrierLevelsA_foldAppsA, hC'lA] at h1
                  exact eqNListA_trans (eqNListA_trans hlsDD.1 h1) (eqNListA_symm hlsAA.1))
            hargs.1 [] [] [] T (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
          simpa using hw
        -- the index coherence: cross the right walk, compose, compose with the flipped
        -- results' datum
        have key : ∀ (Ra Rb : ExprA) (lsR : List Level) (isR : List ExprA),
            appsSpineA Rb = (.const r lsR, (ps'.map (wkExprA ρ)) ++ isR) → eqNList lsA' lsR →
            ArgsRelPA (RsF' ρ lsA') m.nparamsA (ps'.map (wkExprA ρ)) TFA' isA' isR →
            RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls₀ (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) Ra Rb →
            ∃ (lsRa : List Level) (isRa : List ExprA),
              appsSpineA Ra = (.const r lsRa, (ps.map (wkExprA ρ)) ++ isRa) ∧ eqNList lsA lsRa ∧
              ArgsRelPA (RsF ρ lsA) m.nparamsA (ps.map (wkExprA ρ)) TFA isA isRa := by
          intro Ra Rb lsR isR hspb hlsR hw hrd
          obtain ⟨lsRa, lsRb, isRa, isRb, TFRa, _, hRa, hRb, hl₀Ra, hlsRR, hTFRa, _, hwRR, _⟩ := hrd
          rw [hRb, foldAppsA_const_head] at hspb
          injection hspb with e1 e2
          injection e1 with _ e1
          have e2' : isRb = isR := List.append_cancel_left e2
          subst lsR
          subst isR
          have hlARa : eqNList lsA lsRa :=
            eqNListA_trans (eqNListA_trans hlsAA.1 hlsR) (eqNListA_symm hlsRR.1)
          refine ⟨lsRa, isRa, by rw [hRa, foldAppsA_const_head], hlARa, ?_⟩
          obtain ⟨TFl', hTFl'⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsA lsA'
            (xs' := (ps.map (wkExprA ρ))) rfl hTFA
          have u1 := argsRelPA_cross (R := RsF' ρ lsA') (R' := RsF ρ lsA') (i₀ := m.nparamsA)
            (prev₀ := (ps'.map (wkExprA ρ))) (prev₀' := (ps.map (wkExprA ρ))) (T₀ := TFA') (T₀' := TFl')
            (fun pre pre' D uD Cc vC hp hp' hTD => by
              obtain ⟨D', uD', Cc', vC', hTD'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ ρ)
                hTFA' hTFl' rfl hTD
              refine ⟨D', uD', Cc', vC', hTD', fun f f' hr => ?_⟩
              have heq := hXF lsA' TFl' TFA' pre pre' D' uD' Cc' vC' D uD Cc vC ⟨hl₀A', hlsAA.2⟩ hTFl' hTFA' hp' hp
                hTD' hTD
              rw [heq]; exact hr)
            hw [] [] TFl' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
          have u1' : ArgsRelPA (RsF ρ lsA') m.nparamsA (ps.map (wkExprA ρ)) TFl' isA' isRb := by simpa using u1
          have u2 := hIρ.comp hl₀AB hlsAA hTFA hTFl' hwA u1'
          have u3 := hIρ.flip ⟨eqNListA_trans hl₀A hlARa, hl₀Ra.2⟩ ⟨eqNListA_symm hlARa, hl₀AB.2⟩ hTFRa hTFA hwRR
          exact hIρ.comp hl₀AB (eqNListB_refl hl₀AB.2) hTFA hTFA u2 u3
        obtain ⟨lsA₀, lsR, lsR', xsA, isR, isR', TF₀, R₂, R₂', hspA, hTF₀, hta, hspR, hlsA, hwR, hta',
          hspR', hlsA', hwR'⟩ := hcoh
        rw [hC'e, foldAppsA_const_head] at hspA
        injection hspA with h1 h2
        injection h1 with _ h1
        subst lsA₀
        subst xsA
        have htk' : ((ps'.map (wkExprA ρ)) ++ isA').take m.nparamsA = (ps'.map (wkExprA ρ)) := by rw [← (hps'ρ ρ), List.take_left]
        have hdr' : ((ps'.map (wkExprA ρ)) ++ isA').drop m.nparamsA = isA' := by rw [← (hps'ρ ρ), List.drop_left]
        rw [htk'] at hTF₀ hspR hwR hspR' hwR'
        rw [hdr'] at hwR hwR'
        rw [hTF₀] at hTFA'
        injection hTFA' with e
        subst TF₀
        obtain ⟨R₁, hR₁⟩ := applyTelA_some_cross hrig (hplρ ρ) hT₁ hT rfl hta
        obtain ⟨R₁', hR₁'⟩ := applyTelA_some_cross hrig (hplρ ρ) hT₁' hT' rfl hta'
        obtain ⟨hrd, hrd'⟩ := hXS c cm lsA lsC lsC' kinds T T₁ T' T₁' fs fs' R₁ R₂ R₁' R₂'
          hcm hk hfam hkinds hl₀A hlAC hlsC hT hT₁ hT' hT₁' hargs₀ hR₁ hta hR₁' hta'
        obtain ⟨lsRa, isRa, hspRa, hlsRa, hwRa⟩ := key R₁ R₂ lsR isR hspR hlsA hwR hrd
        obtain ⟨lsRa', isRa', hspRa', hlsRa', hwRa'⟩ := key R₁' R₂' lsR' isR' hspR' hlsA' hwR' hrd'
        have htk : ((ps.map (wkExprA ρ)) ++ isA).take m.nparamsA = (ps.map (wkExprA ρ)) := by rw [← (hpsρ ρ), List.take_left]
        have hdr : ((ps.map (wkExprA ρ)) ++ isA).drop m.nparamsA = isA := by rw [← (hpsρ ρ), List.drop_left]
        refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, ?_, hlsC,
          hkinds, ?_, ?_, ⟨lsA, lsRa, lsRa', (ps.map (wkExprA ρ)) ++ isA, isRa, isRa', TFA, R₁, R₁', ?_, ?_, hR₁, ?_,
            hlsRa, ?_, hR₁', ?_, hlsRa', ?_⟩, hp₁, hp₂, tyHRedStarA_retype hcA' ha,
          tyHRedStarA_retype hcA' hb, hna, hnb, ?_⟩
        · rw [hClA]; exact ⟨hlAC, hl₀AB.2⟩
        · rw [hCp]; exact hT
        · rw [hCp]; exact hT'
        · rw [hCe, foldAppsA_const_head]
        · rw [htk]; exact hTFA
        · rw [htk]; exact hspRa
        · rw [htk, hdr]; exact hwRa
        · rw [htk]; exact hspRa'
        · rw [htk, hdr]; exact hwRa'
        · have hQ0 : eqNListB n ls₀ lsC := ⟨eqNListA_trans (eqNListA_trans hl hC'l) hlC.1.1, hlC.1.2⟩
          have hQ0' : eqNListB n ls₀ lsC' := ⟨eqNListA_trans hQ0.1 hlsC.1, hlsC.2⟩
          rw [hCp, hClA]
          exact ⟨hargs₀, convArgsA_rebase (parConvA_symm (hXP lsC hQ0)) hargs.2.1,
            convArgsA_rebase (parConvA_symm (hXP lsC' hQ0')) hargs.2.2⟩
      · exact Or.inr ⟨N, N', tyHRedStarA_retype hcA' ha, tyHRedStarA_retype hcA' hb, hN, hN'⟩)
  intro A hK
  exact (hY hρ hA'p hA'l).2 A hK

end Cross

/-! ## (7) walks across fibers, flips, carried relations (M2-f (3c))

What the symmetry and transitivity of `EqKA.fam` consume: a walk crosses between fibers
(the cross move at its recursive positions), a walk flips on its fiber, and the
cross-related pairs reverse, chain and compose. A clause's relations CARRIED to other
parameters (`carryRelA`) are the right instance's data in the reversed equality: at the
new parameters and a prefix, the old relation at the old parameters and the same prefix. -/

/-- a relation family carried from the parameters `ps` to any parameters of the same
    count: it reads the old relation at `ps` and the prefix past the parameters. -/
def carryRelA (m : CheckedMemberA) (ps : List ExprA) (R : Nat → List ExprA → ExprA → ExprA → Prop) :
    Nat → List ExprA → ExprA → ExprA → Prop :=
  fun i prev => R i (ps ++ prev.drop m.nparamsA)

theorem carryRelA_app {m : CheckedMemberA} {ps ps' : List ExprA}
    {R : Nat → List ExprA → ExprA → ExprA → Prop} (hps' : ps'.length = m.nparamsA) (i : Nat)
    (pre : List ExprA) : carryRelA m ps R i (ps' ++ pre) = R i (ps ++ pre) := by
  simp only [carryRelA, ← hps', List.drop_left]

/-- a clause's Kripke data carried to the parameters of another instance: at every world,
    the relations read at the old (weakened) parameters. -/
def famCarryRsA (m : CheckedMemberA) (ps : List ExprA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop) :
    WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ c lsC => carryRelA m (ps.map (wkExprA ρ)) (Rs ρ c lsC)

def famCarryRsFA (m : CheckedMemberA) (ps : List ExprA)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) :
    WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ lsF => carryRelA m (ps.map (wkExprA ρ)) (RsF ρ lsF)

/-- a family application that is a proposition is fully applied: its telescope applies
    to any list no longer than a prefix of its arguments, at any level list. -/
theorem famApp_tel_of_isProp {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} (hm : E.members r = some m) {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {ls : List Level} {xs ys : List ExprA} (hP : IsPropTy E I Γ (foldAppsA (.const r ls) (xs ++ ys)))
    (ls' : List Level) {xs' : List ExprA} (hxs : xs'.length = xs.length) :
    ∃ TF, applyTelA xs' (instantiateLevelsA ls' m.mtypeA) = some TF := by
  obtain ⟨_, hlen, _⟩ := (isPropTy_famApp_iff hm hsh ls (xs ++ ys)).1 hP
  have hr := rigid_instantiateLevelsA ls' m.mtypeA (rigid_of_sortBody hsh)
  exact (applyTelA_rigid_some xs' _ hr.1).2 (by
    rw [hr.2, hxs, ← hlen, List.length_append]; omega)

section Walks
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
  {Rs Rs' : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
  {RsF RsF' : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {X X' : CRelA}
  {RI RI' : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
  {XF XF' : WkSpecA → CRelA} {RsFX : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop}

/-- an index walk crosses to the right fiber ((F)). -/
theorem argsRelPA_famCross_fwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level}
    (hX : CrossDataA E I n Γ r m Rs Rs' RsF RsF' RI RI' X X' XF XF' RsFX ps ps' ls₀ ls₀') (hpl : ps.length = ps'.length)
    {lsF : List Level} {TF TF' : ExprA} (hl : eqNListB n ls₀ lsF)
    (hTF : applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF)
    (hTF' : applyTelA ps' (instantiateLevelsA lsF m.mtypeA) = some TF')
    {xs xs' : List ExprA} (hw : ArgsRelPA (RsF lsF) m.nparamsA ps TF xs xs') :
    ArgsRelPA (RsF' lsF) m.nparamsA ps' TF' xs xs' := by
  obtain ⟨hXF, -, -, -⟩ := hX
  have h := argsRelPA_cross (R := RsF lsF) (R' := RsF' lsF) (i₀ := m.nparamsA) (prev₀ := ps)
    (prev₀' := ps') (T₀ := TF) (T₀' := TF')
    (fun pre pre' D uD C vC hp hp' hTD => by
      obtain ⟨D', uD', C', vC', hTD'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) hpl hTF hTF' rfl hTD
      refine ⟨D', uD', C', vC', hTD', fun f f' hr => ?_⟩
      rw [← hXF lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl hTF hTF' hp hp' hTD hTD']
      exact hr)
    hw [] [] TF' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- an index walk crosses back to the left fiber ((F)). -/
theorem argsRelPA_famCross_bwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level}
    (hX : CrossDataA E I n Γ r m Rs Rs' RsF RsF' RI RI' X X' XF XF' RsFX ps ps' ls₀ ls₀') (hpl : ps.length = ps'.length)
    {lsF : List Level} {TF TF' : ExprA} (hl : eqNListB n ls₀ lsF)
    (hTF : applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF)
    (hTF' : applyTelA ps' (instantiateLevelsA lsF m.mtypeA) = some TF')
    {xs xs' : List ExprA} (hw : ArgsRelPA (RsF' lsF) m.nparamsA ps' TF' xs xs') :
    ArgsRelPA (RsF lsF) m.nparamsA ps TF xs xs' := by
  obtain ⟨hXF, -, -, -⟩ := hX
  have h := argsRelPA_cross (R := RsF' lsF) (R' := RsF lsF) (i₀ := m.nparamsA) (prev₀ := ps')
    (prev₀' := ps) (T₀ := TF') (T₀' := TF)
    (fun pre pre' D uD C vC hp hp' hTD => by
      obtain ⟨D', uD', C', vC', hTD'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) hpl.symm hTF' hTF rfl
        hTD
      refine ⟨D', uD', C', vC', hTD', fun f f' hr => ?_⟩
      rw [hXF lsF TF TF' pre pre' D' uD' C' vC' D uD C vC hl hTF hTF' hp' hp hTD' hTD]
      exact hr)
    hw [] [] TF (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- a cross-related pair at another `=ₙ` fiber level. -/
theorem recDomRelXA_lvl {ls₀ ls₀' : List Level} (h : eqNList ls₀' ls₀) {ps ps' : List ExprA}
    {A A' : ExprA} (hd : RecDomRelXA E I n Γ r m RsF ls₀ ps ps' A A') :
    RecDomRelXA E I n Γ r m RsF ls₀' ps ps' A A' := by
  obtain ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', hl₀, hls, hTF, hTF', hw, hc⟩ := hd
  exact ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', ⟨eqNListA_trans h hl₀.1, hl₀.2⟩, hls, hTF, hTF', hw, hc⟩

/-- a cross-related pair reversed onto the CARRIED index relations: the walk flipped on
    the left fiber, then read at the right parameters. -/
theorem recDomRelXA_rev {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀) {ps ps' : List ExprA}
    {ls₀ : List Level} (hI : IdxPerA n RsF m ps ls₀) (hps' : ps'.length = m.nparamsA)
    (hpl : ps.length = ps'.length) {D D' : ExprA} (hd : RecDomRelXA E I n Γ r m RsF ls₀ ps ps' D D') :
    RecDomRelXA E I n Γ r m (fun lsF => carryRelA m ps (RsF lsF)) ls₀ ps' ps D' D := by
  obtain ⟨lsD, lsD', isD, isD', TF, TF', hD, hD', hl₀, hls, hTF, hTF', hw, hc⟩ := hd
  subst hD; subst hD'
  obtain ⟨TFl, hTFl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsD lsD' (xs' := ps) rfl hTF
  have hflip := hI.flip hl₀ hls hTF hTFl hw
  refine ⟨lsD', lsD, isD', isD, TF', TF, rfl, rfl, eqNListB_trans hl₀ hls, eqNListB_symm hls hl₀.2, hTF', hTF, ?_,
    hc.elim fun c => ⟨c.symm⟩⟩
  have h := argsRelPA_cross (R := RsF lsD') (R' := carryRelA m ps (RsF lsD')) (i₀ := m.nparamsA)
    (prev₀ := ps) (prev₀' := ps') (T₀ := TFl) (T₀' := TF')
    (fun pre _ A u B v _ _ hT => by
      obtain ⟨A', u', B', v', hT'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) hpl hTFl hTF' rfl hT
      exact ⟨A', u', B', v', hT', fun f f' hr => by rw [carryRelA_app hps']; exact hr⟩)
    hflip [] [] TF' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- three cross-related pairs through the left fiber chain into one on the CARRIED
    relations: `D₁' ~ D₁ ~ D₂ ~ D₂'`. -/
theorem recDomRelXA_chain {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀) {ps ps' : List ExprA}
    {ls₀ : List Level} (hI : IdxPerA n RsF m ps ls₀) (hps' : ps'.length = m.nparamsA)
    (hpl : ps.length = ps'.length) {D₁ D₁' D₂ D₂' : ExprA}
    (h1 : RecDomRelXA E I n Γ r m RsF ls₀ ps ps' D₁ D₁') (h2 : RecDomRelXA E I n Γ r m RsF ls₀ ps ps D₁ D₂)
    (h3 : RecDomRelXA E I n Γ r m RsF ls₀ ps ps' D₂ D₂') :
    RecDomRelXA E I n Γ r m (fun lsF => carryRelA m ps (RsF lsF)) ls₀ ps' ps' D₁' D₂' := by
  obtain ⟨l1, l1', i1, i1', TF1, TF1', hD1, hD1', hl₀, hl1, hTF1, hTF1', w1, c1⟩ := h1
  obtain ⟨l1b, l2, i1b, i2, TF1b, TF2, hD1b, hD2, _, hl12, hTF1b, hTF2, w2, c2⟩ := h2
  obtain ⟨l2b, l2', i2b, i2', TF2b, TF2', hD2b, hD2', _, hl2, hTF2b, hTF2', w3, c3⟩ := h3
  obtain ⟨_, e1l, e1x⟩ := foldAppsA_const_inj (hD1.symm.trans hD1b)
  have e1i : i1 = i1b := List.append_cancel_left e1x
  subst l1b; subst i1b
  obtain ⟨_, e2l, e2x⟩ := foldAppsA_const_inj (hD2.symm.trans hD2b)
  have e2i : i2 = i2b := List.append_cancel_left e2x
  subst l2b; subst i2b
  rw [hTF1] at hTF1b
  injection hTF1b with e1T
  subst TF1b
  rw [hTF2] at hTF2b
  injection hTF2b with e2T
  subst TF2b
  obtain ⟨TFl, hTFl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) l1 l1' (xs' := ps) rfl hTF1
  have hl₀' : eqNListB n ls₀ l1' := eqNListB_trans hl₀ hl1
  have v1 := hI.flip hl₀ hl1 hTF1 hTFl w1
  have v2 := hI.comp hl₀' (eqNListB_symm hl1 hl₀.2) hTFl hTF1 v1 w2
  have v3 := hI.comp hl₀' ⟨eqNListA_trans (eqNListA_symm hl1.1) hl12.1, hl12.2⟩ hTFl hTF2 v2 w3
  refine ⟨l1', l2', i1', i2', TF1', TF2', hD1', hD2', hl₀',
    ⟨eqNListA_trans (eqNListA_trans (eqNListA_symm hl1.1) hl12.1) hl2.1, hl2.2⟩, hTF1', hTF2', ?_, ?_⟩
  · have h := argsRelPA_cross (R := RsF l1') (R' := carryRelA m ps (RsF l1')) (i₀ := m.nparamsA)
      (prev₀ := ps) (prev₀' := ps') (T₀ := TFl) (T₀' := TF1')
      (fun pre _ A u B v _ _ hT => by
        obtain ⟨A', u', B', v', hT'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) hpl hTFl hTF1' rfl hT
        exact ⟨A', u', B', v', hT', fun f f' hr => by rw [carryRelA_app hps']; exact hr⟩)
      v3 [] [] TF1' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
    simpa using h
  · rw [hD1] at c1 c2
    exact c1.elim fun t1 => c2.elim fun t2 => c3.elim fun t3 => ⟨.trans _ _ _ _ t1.symm (.trans _ _ _ _ t2 t3)⟩

/-- two cross-related pairs across three parameter lists compose: the second's walk read
    on the first fiber through (F), then composed there. -/
theorem recDomRelXA_comp {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {ps ps' ps'' : List ExprA} {ls₀ ls₀' : List Level} (hI : IdxPerA n RsF m ps ls₀)
    (hX : CrossDataA E I n Γ r m Rs Rs' RsF RsF' RI RI' X X' XF XF' RsFX ps ps' ls₀ ls₀') (hpl : ps.length = ps'.length)
    {D D' D'' : ExprA} (h1 : RecDomRelXA E I n Γ r m RsF ls₀ ps ps' D D')
    (h2 : RecDomRelXA E I n Γ r m RsF' ls₀' ps' ps'' D' D'') :
    RecDomRelXA E I n Γ r m RsF ls₀ ps ps'' D D'' := by
  obtain ⟨la, lb, ia, ib, TFa, TFb, hD, hD', hl₀, hlab, hTFa, hTFb, w1, c1⟩ := h1
  obtain ⟨lb2, lx, ib2, ix, TFb2, TFx, hD'b, hD'', _, hlbx, hTFb2, hTFx, w2, c2⟩ := h2
  obtain ⟨_, el, ex⟩ := foldAppsA_const_inj (hD'.symm.trans hD'b)
  have ei : ib = ib2 := List.append_cancel_left ex
  subst lb2; subst ib2
  rw [hTFb] at hTFb2
  injection hTFb2 with eT
  subst TFb2
  obtain ⟨TFbl, hTFbl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) la lb (xs' := ps) rfl hTFa
  have w2' := argsRelPA_famCross_bwd hsh hX hpl (eqNListB_trans hl₀ hlab) hTFbl hTFb w2
  refine ⟨la, lx, ia, ix, TFa, TFx, hD, hD'', hl₀, eqNListB_trans hlab hlbx, hTFa, hTFx,
    hI.comp hl₀ hlab hTFa hTFbl w1 w2', ?_⟩
  rw [hD'] at c1
  rw [hD'b] at c2
  exact c1.elim fun t1 => c2.elim fun t2 => ⟨.trans _ _ _ _ t1 t2⟩

end Walks

section WalksW
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
  {Rs Rs' : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
  {RsF RsF' : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI RsI' : InnerRelsA}

/-- a constructor walk crosses to the right fiber (at a world `ρ` of the clause): (C) at plain
    positions, (R) and the cross move at recursive ones. -/
theorem argsRelA_famCross_fwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hEN : EnvNormCtorTypeA E)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level} (hI : IdxPerWA E I n Γ m RsF ps ls₀)
    (hX : CrossWA E I n Γ r m Rs Rs' RsF RsF' RsI RsI' ps ps' ls₀ ls₀')
    (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA) (hl : eqNList ls₀ ls₀')
    {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ)
    {c : Nat} {cm : CheckedMemberA} {kinds : List FieldShape} {lsA lsA' lsC : List Level} {T T' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some r)
    (hkinds : ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds) (hl₀A : eqNList ls₀ lsA)
    (hlAC : eqNListB n lsA lsC) (hlAA' : eqNList lsA lsA')
    (hT : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hT' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T')
    {ks₀ rest : List FieldShape} (hsp₀ : kinds = ks₀ ++ rest) {pre pre' : List ExprA}
    (hw : ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps.map (wkExprA ρ)) T ks₀ pre pre') :
    ArgsRelA (Rs' ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA'
        (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI' ρ c lsC) (ps'.map (wkExprA ρ)) lsA'
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps'.map (wkExprA ρ)) T' ks₀ pre pre' := by
  obtain ⟨_, hXC, hXR, hXI, _, _, hXD⟩ := hX ρ hρ
  have hps'ρ : (ps'.map (wkExprA ρ)).length = m.nparamsA := by rw [List.length_map]; exact hps'
  have hpl : (ps.map (wkExprA ρ)).length = (ps'.map (wkExprA ρ)).length := by
    rw [List.length_map, List.length_map, hps, hps']
  have hl₀'A' : eqNList ls₀' lsA' := eqNListA_trans (eqNListA_symm hl) (eqNListA_trans hl₀A hlAA')
  have hlA'C : eqNListB n lsA' lsC := ⟨eqNListA_trans (eqNListA_symm hlAA') hlAC.1, hlAC.2⟩
  have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
  have h := argsRelA_cross (X' := famRecRelA m (ps'.map (wkExprA ρ)) lsA'
      (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ))
      (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI' ρ c lsC) (ps'.map (wkExprA ρ)) lsA'
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ'))) ks₀
    (fun kd ksPre ks p₁ p₁' D uD C vC hsp hp hp' hTD => by
      obtain ⟨D', uD', C', vC', hTD'⟩ := applyTelA_pi_cross hrig hpl hT hT' rfl hTD
      have hsp' : kinds = ksPre ++ kd :: (ks ++ rest) := by rw [hsp₀, hsp, List.append_assoc]; rfl
      refine ⟨D', uD', C', vC', hTD', ?_⟩
      cases kd using FieldShape.cases3 with
      | funRec j =>
          -- the inner walks cross; the codomains reached cross at the composed world
          intro f f' hr
          simp only [kindRelA] at hr ⊢
          have hI' := hXI c cm lsA lsA' lsC kinds ksPre (ks ++ rest) j T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hl₀'A' hlA'C hT hT' hp hp' hTD hTD'
          have hdomX := hXD c cm lsA lsC kinds ksPre (ks ++ rest) j T T' p₁ p₁' D uD C vC D' uD' C' vC' hcm hk
            hfam hkinds hsp' hl₀A hlAC hT hT' hp hTD hTD'
          refine famFunRelA_cross hdomX (fun ρ' hρ' zs zs' hzs => (hI' ρ' hρ').1 zs zs' hzs)
            (fun ρ' hρ' zs zs' El Er x y hwz hlen hEl hEr hxy => ?_) hr
          have hrd := (hI' ρ' hρ').2.2 zs zs' El Er hwz hlen hEl hEr
          have hl₀El : eqNList ls₀ (carrierLevelsA El) := eqNListA_trans hl₀A (eqNListA_symm hxy.2.1)
          obtain ⟨hpEr, hlEr⟩ := recDomRelXA_right (by rw [List.length_map]; exact hps'ρ) hrd
            (eqNListA_trans hxy.2.1 hlAA')
          exact ⟨hpEr, hlEr, lfpWA_cross_fwd hsh hEN hI hX hps hps' hl (wkOk₀A_comp_ext hρ hρ')
            (hxy.1.trans (map_wkExprA_comp ρ ρ' ps)) hl₀El hxy.2.2 (recDomRelXA_comp_world hrd)⟩
      | plain =>
          intro f f' hr
          have heq := hXC c cm lsA lsA' lsC kinds ksPre (ks ++ rest) T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hl₀'A' hlA'C hT hT' hp hp' hTD hTD'
          show Rs' ρ c lsC _ (ps'.map (wkExprA ρ) ++ p₁) f f'
          rw [← heq]; exact hr
      | directRec =>
          intro f f' hr
          have hr' : famRecRelA m (ps.map (wkExprA ρ)) lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ) D f f' := hr
          have hrd := hXR c cm lsA lsC kinds ksPre (ks ++ rest) T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hT hT' hp hTD hTD'
          obtain ⟨lsD, lsD', isD, isD', _, _, hLe, hRe, _, hlsDD, _, _, _, _⟩ := id hrd
          have hl₀D : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hl₀A (eqNListA_symm hr'.2.1)
          refine ⟨by rw [hRe, carrierParamsA_famApp hps'ρ], ?_,
            lfpWA_cross_fwd hsh hEN hI hX hps hps' hl hρ hr'.1 hl₀D hr'.2.2 hrd⟩
          rw [hRe, carrierLevelsA_foldAppsA]
          have h1 := hr'.2.1
          rw [hLe, carrierLevelsA_foldAppsA] at h1
          exact eqNListA_trans (eqNListA_trans (eqNListA_symm hlsDD.1) h1) hlAA')
    hw [] [] [] T' (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- a constructor walk crosses back to the left fiber (at a world `ρ` of the clause). -/
theorem argsRelA_famCross_bwd {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hEN : EnvNormCtorTypeA E)
    {ps ps' : List ExprA} {ls₀ ls₀' : List Level} (hI : IdxPerWA E I n Γ m RsF ps ls₀)
    (hX : CrossWA E I n Γ r m Rs Rs' RsF RsF' RsI RsI' ps ps' ls₀ ls₀')
    (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA) (hl : eqNList ls₀ ls₀')
    {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ)
    {c : Nat} {cm : CheckedMemberA} {kinds : List FieldShape} {lsA lsA' lsC : List Level} {T T' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some r)
    (hkinds : ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds) (hl₀A : eqNList ls₀ lsA)
    (hlAC : eqNListB n lsA lsC) (hlAA' : eqNList lsA lsA')
    (hT : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hT' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T')
    {ks₀ rest : List FieldShape} (hsp₀ : kinds = ks₀ ++ rest) {pre pre' : List ExprA}
    (hw : ArgsRelA (Rs' ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA'
        (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI' ρ c lsC) (ps'.map (wkExprA ρ)) lsA'
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps'.map (wkExprA ρ)) T' ks₀ pre pre') :
    ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps.map (wkExprA ρ)) T ks₀ pre pre' := by
  obtain ⟨_, hXC, hXR, hXI, _, _, hXD⟩ := hX ρ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = m.nparamsA := by rw [List.length_map]; exact hps
  have hpl : (ps'.map (wkExprA ρ)).length = (ps.map (wkExprA ρ)).length := by
    rw [List.length_map, List.length_map, hps, hps']
  have hl₀'A' : eqNList ls₀' lsA' := eqNListA_trans (eqNListA_symm hl) (eqNListA_trans hl₀A hlAA')
  have hlA'C : eqNListB n lsA' lsC := ⟨eqNListA_trans (eqNListA_symm hlAA') hlAC.1, hlAC.2⟩
  have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
  have h := argsRelA_cross (X' := famRecRelA m (ps.map (wkExprA ρ)) lsA
      (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) ks₀
    (fun kd ksPre ks p₁ p₁' D' uD' C' vC' hsp hp hp' hTD' => by
      obtain ⟨D, uD, C, vC, hTD⟩ := applyTelA_pi_cross hrig hpl hT' hT rfl hTD'
      have hsp' : kinds = ksPre ++ kd :: (ks ++ rest) := by rw [hsp₀, hsp, List.append_assoc]; rfl
      refine ⟨D, uD, C, vC, hTD, ?_⟩
      cases kd using FieldShape.cases3 with
      | funRec j =>
          -- the inner walks cross back; the codomains reached cross back at the composed world
          intro f f' hr
          simp only [kindRelA] at hr ⊢
          have hI' := hXI c cm lsA lsA' lsC kinds ksPre (ks ++ rest) j T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hl₀'A' hlA'C hT hT' hp' hp hTD hTD'
          have hdomX' := tyConvA_symm_ne (hXD c cm lsA lsC kinds ksPre (ks ++ rest) j T T' p₁ p₁' D uD C vC D' uD' C' vC' hcm hk
            hfam hkinds hsp' hl₀A hlAC hT hT' hp' hTD hTD')
          refine famFunRelA_cross hdomX' (fun ρ' hρ' zs zs' hzs => (hI' ρ' hρ').2.1 zs zs' hzs)
            (fun ρ' hρ' zs zs' Er El x y hwz hlen hEr hEl hxy => ?_) hr
          have hrd := (hI' ρ' hρ').2.2 zs zs' El Er ((hI' ρ' hρ').1 zs zs' hwz) hlen hEl hEr
          have hl₀'Er : eqNList ls₀' (carrierLevelsA Er) := eqNListA_trans hl₀'A' (eqNListA_symm hxy.2.1)
          obtain ⟨hpEl, hlEl⟩ := recDomRelXA_left (by rw [List.length_map]; exact hpsρ) hrd
            (eqNListA_trans hxy.2.1 (eqNListA_symm hlAA'))
          exact ⟨hpEl, hlEl, lfpWA_cross_bwd hsh hEN hI hX hps hps' hl (wkOk₀A_comp_ext hρ hρ')
            (hxy.1.trans (map_wkExprA_comp ρ ρ' ps')) hl₀'Er hxy.2.2 (recDomRelXA_comp_world hrd)⟩
      | plain =>
          intro f f' hr
          have heq := hXC c cm lsA lsA' lsC kinds ksPre (ks ++ rest) T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hl₀'A' hlA'C hT hT' hp' hp hTD hTD'
          show Rs ρ c lsC _ (ps.map (wkExprA ρ) ++ p₁) f f'
          rw [heq]; exact hr
      | directRec =>
          intro f f' hr
          have hr' : famRecRelA m (ps'.map (wkExprA ρ)) lsA' (LfpWA (FamPhiWA E I n Γ r m Rs' RsF' RsI') ρ)
              D' f f' := hr
          have hrd := hXR c cm lsA lsC kinds ksPre (ks ++ rest) T T' p₁ p₁' D uD C vC D' uD' C' vC'
            hcm hk hfam hkinds hsp' hl₀A hlAC hT hT' hp' hTD hTD'
          obtain ⟨lsD, lsD', isD, isD', _, _, hLe, hRe, _, hlsDD, _, _, _, _⟩ := id hrd
          have hl₀'D : eqNList ls₀' (carrierLevelsA D') := eqNListA_trans hl₀'A' (eqNListA_symm hr'.2.1)
          refine ⟨by rw [hLe, carrierParamsA_famApp hpsρ], ?_,
            lfpWA_cross_bwd hsh hEN hI hX hps hps' hl hρ hr'.1 hl₀'D hr'.2.2 hrd⟩
          rw [hLe, carrierLevelsA_foldAppsA]
          have h1 := hr'.2.1
          rw [hRe, carrierLevelsA_foldAppsA] at h1
          exact eqNListA_trans (eqNListA_trans hlsDD.1 h1) (eqNListA_symm hlAA'))
    hw [] [] [] T (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- a constructor walk FLIPS on its fiber (at a world `ρ` of the clause): the right arguments
    walk the second level list's telescope (`CtorPerA` at plain positions; at recursive ones
    the fixed point's symmetry and its move between related recursive domains). -/
theorem ctorWalkA_flip {ps : List ExprA} {ls₀ : List Level}
    (hEN : EnvNormCtorTypeA E) (hP : FiberPerWA E I n Γ r m Rs RsF RsI ps ls₀)
    (hps : ps.length = m.nparamsA) {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ)
    {c : Nat} {cm : CheckedMemberA} {kinds : List FieldShape} {lsA lsC lsC' : List Level} {T T' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some r)
    (hkinds : ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds) (hl₀A : eqNList ls₀ lsA)
    (hlAC : eqNListB n lsA lsC) (hlsC : eqNListB n lsC lsC')
    (hT : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hT' : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    {ks₀ rest : List FieldShape} (hsp₀ : kinds = ks₀ ++ rest) {pre pre' : List ExprA}
    (hw : ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps.map (wkExprA ρ)) T ks₀ pre pre') :
    ArgsRelA (Rs ρ c lsC') (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC') (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
      m.nparamsA (ps.map (wkExprA ρ)) T' ks₀ pre' pre := by
  obtain ⟨hI, hC⟩ := hP ρ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = m.nparamsA := by rw [List.length_map]; exact hps
  have hflip := argsRelA_flip (X' := famRecRelA m (ps.map (wkExprA ρ)) lsA
      (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
      (F' := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC') (ps.map (wkExprA ρ)) lsA
        (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) ks₀
    (fun kd ksPre ks p₁ p₁' A u B v hsp hp hp' hT₀ => by
      have hsp' : kinds = ksPre ++ kd :: (ks ++ rest) := by rw [hsp₀, hsp, List.append_assoc]; rfl
      obtain ⟨A', u', B', v', hT₀', hpl, hrec, hfun, hdomC⟩ := hC c cm kinds lsA lsC lsC' T T' hcm hk hfam hkinds
        hl₀A hlAC hlsC hT hT' kd ksPre (ks ++ rest) p₁ p₁' p₁ A u B v hsp' hp hp' hT₀
      refine ⟨A', u', B', v', hT₀', ?_⟩
      cases kd using FieldShape.cases3 with
      | funRec j =>
          -- the inner walks flip back; at the composed world the fixed point's symmetry, then the
          -- move between the related codomains
          intro f f' hff
          simp only [kindRelA] at hff ⊢
          refine famFunRelA_flip (hdomC j rfl) (fun ρ' hρ' zs zs' hzs => (hfun j rfl ρ' hρ').1 zs zs' hzs)
            (fun ρ' hρ' zs zs' D D' x y hwz hlen hD hD' hxy => ?_) hff
          have hρc := wkOk₀A_comp_ext hρ hρ'
          have hrd := (hfun j rfl ρ' hρ').2.2 zs' zs D D' hwz hlen hD hD'
          have hl₀D : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hl₀A (eqNListA_symm hxy.2.1)
          obtain ⟨hpD', hlD'⟩ := recDomRelXA_right (by rw [List.length_map]; exact hpsρ) hrd hxy.2.1
          exact ⟨hpD', hlD', (lfpWA_recDom (hP _ hρc).1 (by rw [List.length_map]; exact hps)
            (recDomRelXA_comp_world hrd)).1
            (lfpWA_symm hP hps hρc (hxy.1.trans (map_wkExprA_comp ρ ρ' ps)) hl₀D hxy.2.2)⟩
      | plain => exact (hpl rfl).1
      | directRec =>
          intro f f' hff
          have hff' : famRecRelA m (ps.map (wkExprA ρ)) lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ)
              A f f' := hff
          have hrd := hrec rfl
          obtain ⟨lsD, lsD', isD, isD', _, _, hD, hD', _, hlsDD, _, _, _, _⟩ := id hrd
          have hlD : carrierLevelsA A = lsD := by rw [hD, carrierLevelsA_foldAppsA]
          have hl₀D : eqNList ls₀ (carrierLevelsA A) := eqNListA_trans hl₀A (eqNListA_symm hff'.2.1)
          refine ⟨?_, ?_, (lfpWA_recDom hI hpsρ hrd).1 (lfpWA_symm hP hps hρ hff'.1 hl₀D hff'.2.2)⟩
          · rw [hD', carrierParamsA_famApp hpsρ]
          · rw [hD', carrierLevelsA_foldAppsA]
            have h1 := hff'.2.1
            rw [hlD] at h1
            exact eqNListA_trans (eqNListA_symm hlsDD.1) h1)
    hw [] [] [] T' (by simp) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using hflip

end WalksW



#print axioms argsRelPA_applyTel_some
#print axioms argsRelPA_rrefl
#print axioms recDomRelXA_right
#print axioms recDomRelXA_left
#print axioms recDomRelXA_comp_world
#print axioms funRelA_flip
#print axioms funRelA_comp
#print axioms funRelA_cross
#print axioms argsRelPA_flip
#print axioms argsRelPA_comp
#print axioms argsRelA_flip
#print axioms argsRelA_comp
#print axioms lfpWA_carrier
#print axioms lfpWA_recDom
#print axioms lfpWA_symm
#print axioms lfpWA_trans
#print axioms argsRelPA_cross
#print axioms argsRelA_cross
#print axioms lfpWA_cross_fwd
#print axioms lfpWA_cross_bwd
#print axioms argsRelA_famCross_fwd
#print axioms argsRelA_famCross_bwd
#print axioms ctorWalkA_flip
#print axioms recDomRelXA_rev
#print axioms recDomRelXA_chain
#print axioms recDomRelXA_comp

end Rcic.Declarative.Ann
