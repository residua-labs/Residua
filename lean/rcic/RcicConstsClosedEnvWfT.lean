import rcic.RcicIotaShapeStable
import rcic.RcicWitnessFuelStable
import rcic.RcicTypedEnv
import rcic.RcicEnv

/-!
# DT-019 S1 — `ConstsMemberClosed` from `EnvWfT`

`ConstsMemberClosed E e` (`RcicIotaShapeStable`) is the fuel-free closure
certificate the ι-schema env-transfer lemmas consume: every constant of `e` is a
member of `E`, and every transparent member reached is closed again on its body.
A well-formed environment supplies it for every term whose constants are
members: each body was typed when its member was admitted (`hv`/`hp`), so its
constants are members of the prefix, and the environment only grows after
(`BodiesClosed`); group members carry no body (`hnobody`).

* `BodiesClosed E` — every transparent body, at every level instantiation, is
  closed in `E`.
* `constsMemberClosed_of_constsIn` — `BodiesClosed E → ConstsIn E e →
  ConstsMemberClosed E e`.
* `bodiesClosed_of_envWfT`, `membersClosed_of_envWfT` — the discharges.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-- every transparent member's body is closed, at every level instantiation. -/
def BodiesClosed (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ b, transparent m.mclass = true → m.body = some b →
    ∀ ls, ConstsMemberClosed E (instantiateLevels ls b)

/-- every member's stored type is closed. -/
def MembersClosed (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ConstsMemberClosed E m.mtype

theorem constsMemberClosed_mono {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    ∀ {e : Expr Nat}, ConstsMemberClosed E e → ConstsMemberClosed E' e
  | _, .bvar i => .bvar i
  | _, .sort l => .sort l
  | _, .lit t h => .lit t (constsMemberClosed_mono hext h)
  | _, .const r ls m hmem hbody =>
      .const r ls m (hext r m hmem)
        (fun b htr hb => constsMemberClosed_mono hext (hbody b htr hb))
  | _, .app hf ha => .app (constsMemberClosed_mono hext hf) (constsMemberClosed_mono hext ha)
  | _, .lam hA hb => .lam (constsMemberClosed_mono hext hA) (constsMemberClosed_mono hext hb)
  | _, .pi hA hb => .pi (constsMemberClosed_mono hext hA) (constsMemberClosed_mono hext hb)
  | _, .letE hA hv hb =>
      .letE (constsMemberClosed_mono hext hA) (constsMemberClosed_mono hext hv)
        (constsMemberClosed_mono hext hb)

theorem constsIn_mono' {E E' : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) :
    ∀ {e : Expr Nat}, ConstsIn E e → ConstsIn E' e
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .lit 0, h => let ⟨m, hm⟩ := h; ⟨m, hsub 1 m hm⟩
  | .lit (_ + 1), h =>
      let ⟨⟨m1, h1⟩, m2, h2⟩ := h
      ⟨⟨m1, hsub 1 m1 h1⟩, m2, hsub 2 m2 h2⟩
  | .const r _, ⟨m, hm⟩ => ⟨m, hsub r m hm⟩
  | .app _ _, ⟨hf, ha⟩ => ⟨constsIn_mono' hsub hf, constsIn_mono' hsub ha⟩
  | .lam _ _, ⟨hA, hb⟩ => ⟨constsIn_mono' hsub hA, constsIn_mono' hsub hb⟩
  | .pi _ _, ⟨hA, hb⟩ => ⟨constsIn_mono' hsub hA, constsIn_mono' hsub hb⟩
  | .letE _ _ _, ⟨hA, hv, hb⟩ =>
      ⟨constsIn_mono' hsub hA, constsIn_mono' hsub hv, constsIn_mono' hsub hb⟩

theorem constsIn_instantiateLevels {E : ResolvedEnv} (ls : List Level) :
    ∀ {e : Expr Nat}, ConstsIn E e → ConstsIn E (instantiateLevels ls e)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .lit _, h => h
  | .const _ _, ⟨m, hm⟩ => ⟨m, hm⟩
  | .app _ _, ⟨hf, ha⟩ => ⟨constsIn_instantiateLevels ls hf, constsIn_instantiateLevels ls ha⟩
  | .lam _ _, ⟨hA, hb⟩ => ⟨constsIn_instantiateLevels ls hA, constsIn_instantiateLevels ls hb⟩
  | .pi _ _, ⟨hA, hb⟩ => ⟨constsIn_instantiateLevels ls hA, constsIn_instantiateLevels ls hb⟩
  | .letE _ _ _, ⟨hA, hv, hb⟩ =>
      ⟨constsIn_instantiateLevels ls hA, constsIn_instantiateLevels ls hv,
        constsIn_instantiateLevels ls hb⟩

private theorem natExpand_closed {E : ResolvedEnv}
    (c1 : ConstsMemberClosed E (.const 1 [])) (c2 : ConstsMemberClosed E (.const 2 [])) :
    (t : Nat) → ConstsMemberClosed E (natExpand t)
  | 0 => c1
  | t + 1 => .app c2 (natExpand_closed c1 c2 t)

/-- under closed bodies, every term whose constants are members is closed. -/
theorem constsMemberClosed_of_constsIn {E : ResolvedEnv} (hB : BodiesClosed E) :
    ∀ e : Expr Nat, ConstsIn E e → ConstsMemberClosed E e
  | .bvar i, _ => .bvar i
  | .sort l, _ => .sort l
  | .const r ls, ⟨m, hm⟩ => .const r ls m hm (fun b htr hb => hB r m hm b htr hb ls)
  | .app f a, ⟨hf, ha⟩ =>
      .app (constsMemberClosed_of_constsIn hB f hf) (constsMemberClosed_of_constsIn hB a ha)
  | .lam A b, ⟨hA, hb⟩ =>
      .lam (constsMemberClosed_of_constsIn hB A hA) (constsMemberClosed_of_constsIn hB b hb)
  | .pi A b, ⟨hA, hb⟩ =>
      .pi (constsMemberClosed_of_constsIn hB A hA) (constsMemberClosed_of_constsIn hB b hb)
  | .letE A v b, ⟨hA, hv, hb⟩ =>
      .letE (constsMemberClosed_of_constsIn hB A hA) (constsMemberClosed_of_constsIn hB v hv)
        (constsMemberClosed_of_constsIn hB b hb)
  | .lit 0, ⟨m, hm⟩ => .lit 0 (.const 1 [] m hm (fun b htr hb => hB 1 m hm b htr hb []))
  | .lit (t + 1), ⟨⟨m1, h1⟩, m2, h2⟩ =>
      .lit (t + 1) (natExpand_closed
        (.const 1 [] m1 h1 (fun b htr hb => hB 1 m1 h1 b htr hb []))
        (.const 2 [] m2 h2 (fun b htr hb => hB 2 m2 h2 b htr hb []))
        (t + 1))

/-! ## the discharges from `EnvWfT` -/

/-- a fresh extension by a body-free member keeps the bodies closed. -/
theorem bodiesClosed_extend_nobody {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) (hnobody : m.body = none) (hB : BodiesClosed E) :
    BodiesClosed (extendEnv E r m) := by
  intro r' m' hm' b htr hb ls
  by_cases hrr : r' = r
  · subst hrr
    rw [members_extend_eq] at hm'
    cases hm'
    rw [hnobody] at hb
    cases hb
  · rw [members_extend_ne E r m r' hrr] at hm'
    exact constsMemberClosed_mono (members_extend_preserved hfresh) (hB r' m' hm' b htr hb ls)

/-- a fresh extension by a member whose body is typed in the base keeps the bodies closed. -/
theorem bodiesClosed_extend_body {E : ResolvedEnv} {r : Nat} {cls : MemberClass}
    {A v : Expr Nat} (hfresh : E.members r = none)
    (hv : ConstsIn E v) (hB : BodiesClosed E) :
    BodiesClosed (extendEnv E r ⟨cls, 0, A, some v⟩) := by
  intro r' m' hm' b htr hb ls
  by_cases hrr : r' = r
  · subst hrr
    rw [members_extend_eq] at hm'
    cases hm'
    cases hb
    exact constsMemberClosed_mono (members_extend_preserved hfresh)
      (constsMemberClosed_of_constsIn hB _ (constsIn_instantiateLevels ls hv))
  · rw [members_extend_ne E r _ r' hrr] at hm'
    exact constsMemberClosed_mono (members_extend_preserved hfresh) (hB r' m' hm' b htr hb ls)

theorem bodiesClosed_groupMembersT {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → BodiesClosed E → BodiesClosed E'
  | _, _, _, .nil _, hB => hB
  | _, _, _, .cons _ _ _ _ _ hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest, hB =>
      bodiesClosed_groupMembersT hrest (bodiesClosed_extend_nobody hfresh hnobody hB)

/-- `EnvWfT` discharges `BodiesClosed`. -/
theorem bodiesClosed_of_envWfT : {E : ResolvedEnv} → EnvWfT E → BodiesClosed E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiom _ _ _ _ hE hfresh _ _ _ =>
      bodiesClosed_extend_nobody hfresh rfl (bodiesClosed_of_envWfT hE)
  | _, .definition _ _ _ _ _ hE hfresh _ hv _ _ _ _ =>
      bodiesClosed_extend_body hfresh (hasTyT_constsIn hv) (bodiesClosed_of_envWfT hE)
  | _, .thm _ _ _ _ hE hfresh _ hp _ _ _ _ =>
      bodiesClosed_extend_body hfresh (hasTyT_constsIn hp) (bodiesClosed_of_envWfT hE)
  | _, .opaque _ _ _ _ _ hE hfresh _ hv _ _ _ _ =>
      bodiesClosed_extend_body hfresh (hasTyT_constsIn hv) (bodiesClosed_of_envWfT hE)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      bodiesClosed_groupMembersT hmem (bodiesClosed_of_envWfT hE)

/-- a fresh extension by a member whose stored type's constants are members of the base
    keeps every stored type closed. -/
theorem membersClosed_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) (hB : BodiesClosed E) (hM : MembersClosed E)
    (hm : ConstsIn E m.mtype) : MembersClosed (extendEnv E r m) := by
  intro r' m' hm'
  by_cases hrr : r' = r
  · subst hrr
    rw [members_extend_eq] at hm'
    cases hm'
    exact constsMemberClosed_mono (members_extend_preserved hfresh)
      (constsMemberClosed_of_constsIn hB _ hm)
  · rw [members_extend_ne E r m r' hrr] at hm'
    exact constsMemberClosed_mono (members_extend_preserved hfresh) (hM r' m' hm')

theorem membersClosed_groupMembersT {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → BodiesClosed E → MembersClosed E → MembersClosed E'
  | _, _, _, .nil _, _, hM => hM
  | _, _, _, .cons _ _ _ _ _ hfresh hnobody _ _ _ _ _ _ _ _ hT _ _ hrest, hB, hM =>
      membersClosed_groupMembersT hrest (bodiesClosed_extend_nobody hfresh hnobody hB)
        (membersClosed_extend hfresh hB hM (hasTyT_constsIn hT))

/-- `EnvWfT` discharges `MembersClosed`. -/
theorem membersClosed_of_envWfT : {E : ResolvedEnv} → EnvWfT E → MembersClosed E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiom _ _ _ _ hE hfresh hA _ _ =>
      membersClosed_extend hfresh (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE)
        (hasTyT_constsIn hA)
  | _, .definition _ _ _ _ _ hE hfresh hA _ _ _ _ _ =>
      membersClosed_extend hfresh (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE)
        (hasTyT_constsIn hA)
  | _, .thm _ _ _ _ hE hfresh hA _ _ _ _ _ =>
      membersClosed_extend hfresh (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE)
        (hasTyT_constsIn hA)
  | _, .opaque _ _ _ _ _ hE hfresh hA _ _ _ _ _ =>
      membersClosed_extend hfresh (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE)
        (hasTyT_constsIn hA)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      membersClosed_groupMembersT hmem (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE)

/-! ## telescope splitting -/

theorem constsMemberClosed_policyPi_inv {E : ResolvedEnv} :
    (ds : List (Expr Nat)) → {b : Expr Nat} → ConstsMemberClosed E (policyPi ds b) →
    (∀ d ∈ ds, ConstsMemberClosed E d) ∧ ConstsMemberClosed E b
  | [], _, h => ⟨fun _ hd => absurd hd (List.not_mem_nil _), h⟩
  | d :: ds, b, h => by
      cases h with
      | pi hA hb =>
          obtain ⟨hds, hb'⟩ := constsMemberClosed_policyPi_inv ds hb
          refine ⟨fun x hx => ?_, hb'⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hA
          · exact hds x hx'

theorem constsMemberClosed_policyPi {E : ResolvedEnv} :
    (ds : List (Expr Nat)) → {b : Expr Nat} → (∀ d ∈ ds, ConstsMemberClosed E d) →
    ConstsMemberClosed E b → ConstsMemberClosed E (policyPi ds b)
  | [], _, _, hb => hb
  | d :: ds, b, hds, hb =>
      .pi (hds d (List.mem_cons_self _ _))
        (constsMemberClosed_policyPi ds (fun x hx => hds x (List.mem_cons_of_mem _ hx)) hb)

/-! ## completeness: a closure certificate yields a fuel

`constsMemberFuel_sound` reads a certificate off a successful check; the
converse picks the fuel as the certificate's depth — the fuel-indexed
env-transfer lemmas (`fieldShapesFuel_ext`, `iotaOpenRhs_ext`) are then
reachable from `ConstsMemberClosed` without touching their private closure-form
cores, and the analysis-fuel monotonicity (`fieldShapesFuel_mono`,
`iotaOpenRhs_mono`) absorbs the fuel mismatch. -/

theorem constsMemberFuel_bvar (E : ResolvedEnv) (f i : Nat) :
    constsMemberFuel E (f + 1) (.bvar i) = true := by simp only [constsMemberFuel]

theorem constsMemberFuel_sort (E : ResolvedEnv) (f : Nat) (l : Level) :
    constsMemberFuel E (f + 1) (.sort l) = true := by simp only [constsMemberFuel]

theorem constsMemberFuel_app (E : ResolvedEnv) (f : Nat) (a b : Expr Nat) :
    constsMemberFuel E (f + 1) (.app a b) =
      (constsMemberFuel E (f + 1) a && constsMemberFuel E (f + 1) b) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_lam (E : ResolvedEnv) (f : Nat) (a b : Expr Nat) :
    constsMemberFuel E (f + 1) (.lam a b) =
      (constsMemberFuel E (f + 1) a && constsMemberFuel E (f + 1) b) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_pi (E : ResolvedEnv) (f : Nat) (a b : Expr Nat) :
    constsMemberFuel E (f + 1) (.pi a b) =
      (constsMemberFuel E (f + 1) a && constsMemberFuel E (f + 1) b) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_letE (E : ResolvedEnv) (f : Nat) (a v b : Expr Nat) :
    constsMemberFuel E (f + 1) (.letE a v b) =
      (constsMemberFuel E (f + 1) a && constsMemberFuel E (f + 1) v &&
        constsMemberFuel E (f + 1) b) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_lit_zero (E : ResolvedEnv) (f : Nat) :
    constsMemberFuel E (f + 1) (.lit 0) = constsMemberFuel E (f + 1) (.const 1 []) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_lit_succ (E : ResolvedEnv) (f t : Nat) :
    constsMemberFuel E (f + 1) (.lit (t + 1)) =
      (constsMemberFuel E (f + 1) (.const 2 []) && constsMemberFuel E (f + 1) (.const 1 [])) := by
  simp only [constsMemberFuel]

theorem constsMemberFuel_consts_of_natExpand (E : ResolvedEnv) (f : Nat) :
    (t : Nat) → constsMemberFuel E (f + 1) (natExpand t) = true →
      constsMemberFuel E (f + 1) (.const 1 []) = true ∧
        (t ≠ 0 → constsMemberFuel E (f + 1) (.const 2 []) = true)
  | 0, h => ⟨h, fun h0 => absurd rfl h0⟩
  | t + 1, h => by
      have h' : (constsMemberFuel E (f + 1) (.const 2 []) &&
          constsMemberFuel E (f + 1) (natExpand t)) = true := by
        rw [← constsMemberFuel_app]; exact h
      rw [Bool.and_eq_true] at h'
      exact ⟨(constsMemberFuel_consts_of_natExpand E f t h'.2).1, fun _ => h'.1⟩

theorem constsMemberFuel_complete {E : ResolvedEnv} {e : Expr Nat}
    (h : ConstsMemberClosed E e) : ∃ fuel, constsMemberFuel E fuel e = true := by
  induction h with
  | bvar i => exact ⟨1, constsMemberFuel_bvar E 0 i⟩
  | sort l => exact ⟨1, constsMemberFuel_sort E 0 l⟩
  | lit t _ ih =>
      obtain ⟨F, hF⟩ := ih
      cases F with
      | zero => simp [constsMemberFuel] at hF
      | succ f =>
          obtain ⟨h1, h2⟩ := constsMemberFuel_consts_of_natExpand E f t hF
          refine ⟨f + 1, ?_⟩
          cases t with
          | zero => rw [constsMemberFuel_lit_zero]; exact h1
          | succ t => rw [constsMemberFuel_lit_succ, h2 (Nat.succ_ne_zero t), h1]; rfl
  | const r ls m hmem hbody ih =>
      cases hb : m.body with
      | none => exact ⟨1, by simp [constsMemberFuel, hmem, hb]⟩
      | some b =>
          cases htr : transparent m.mclass with
          | false => exact ⟨1, by simp [constsMemberFuel, hmem, hb, htr]⟩
          | true =>
              obtain ⟨F, hF⟩ := ih b htr hb
              exact ⟨F + 1, by simp [constsMemberFuel, hmem, hb, htr, hF]⟩
  | app _ _ ihf iha =>
      obtain ⟨F1, h1⟩ := ihf
      obtain ⟨F2, h2⟩ := iha
      refine ⟨max F1 F2 + 1, ?_⟩
      rw [constsMemberFuel_app, constsMemberFuel_mono E F1 _ h1 _ (by omega),
        constsMemberFuel_mono E F2 _ h2 _ (by omega)]
      rfl
  | lam _ _ ihA ihb =>
      obtain ⟨F1, h1⟩ := ihA
      obtain ⟨F2, h2⟩ := ihb
      refine ⟨max F1 F2 + 1, ?_⟩
      rw [constsMemberFuel_lam, constsMemberFuel_mono E F1 _ h1 _ (by omega),
        constsMemberFuel_mono E F2 _ h2 _ (by omega)]
      rfl
  | pi _ _ ihA ihb =>
      obtain ⟨F1, h1⟩ := ihA
      obtain ⟨F2, h2⟩ := ihb
      refine ⟨max F1 F2 + 1, ?_⟩
      rw [constsMemberFuel_pi, constsMemberFuel_mono E F1 _ h1 _ (by omega),
        constsMemberFuel_mono E F2 _ h2 _ (by omega)]
      rfl
  | letE _ _ _ ihA ihv ihb =>
      obtain ⟨F1, h1⟩ := ihA
      obtain ⟨F2, h2⟩ := ihv
      obtain ⟨F3, h3⟩ := ihb
      refine ⟨max (max F1 F2) F3 + 1, ?_⟩
      rw [constsMemberFuel_letE, constsMemberFuel_mono E F1 _ h1 _ (by omega),
        constsMemberFuel_mono E F2 _ h2 _ (by omega),
        constsMemberFuel_mono E F3 _ h3 _ (by omega)]
      rfl

/-- one fuel for a whole list of closed terms. -/
theorem constsMemberFuel_complete_list (E : ResolvedEnv) :
    (Ts : List (Expr Nat)) → (∀ T ∈ Ts, ConstsMemberClosed E T) →
    ∃ F, ∀ T ∈ Ts, constsMemberFuel E F T = true
  | [], _ => ⟨0, fun _ h => absurd h (List.not_mem_nil _)⟩
  | T :: Ts, h => by
      obtain ⟨F1, h1⟩ := constsMemberFuel_complete (h T (List.mem_cons_self _ _))
      obtain ⟨F2, h2⟩ :=
        constsMemberFuel_complete_list E Ts (fun x hx => h x (List.mem_cons_of_mem _ hx))
      refine ⟨max F1 F2, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact constsMemberFuel_mono E F1 _ h1 _ (Nat.le_max_left _ _)
      · exact constsMemberFuel_mono E F2 _ (h2 x hx') _ (Nat.le_max_right _ _)

end Rcic.Declarative
