import rcic.RcicAnnKDeterminism

/-!
# Positive static apartness and normal syntax for LR3

`ApartA3` is inhabited by structural and stored-layout mismatches.  None of
its constructors carries a negated conversion or a negated K frame.  Its
exclusion theorem is derived from the actual frame invariants.

This first certificate language does not decide whether the indices of a
structurally eligible K call are convertible.  Such a call needs a separate
positive index-separation certificate before it can be certified stuck.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

inductive NonAppA3 : ExprA → Prop
  | bvar (i : Nat) : NonAppA3 (.bvar i)
  | sort (l : Level) : NonAppA3 (.sort l)
  | const (r : Nat) (ls : List Level) : NonAppA3 (.const r ls)
  | lam (A : ExprA) (u : Level) (b : ExprA) : NonAppA3 (.lam A u b)
  | pi (A : ExprA) (u : Level) (B : ExprA) (v : Level) : NonAppA3 (.pi A u B v)
  | letE (A v b : ExprA) : NonAppA3 (.letE A v b)
  | lit (t : Nat) : NonAppA3 (.lit t)

theorem NonAppA3.not_app {e : ExprA} (h : NonAppA3 e) (f a : ExprA) : e ≠ .app f a := by
  cases h <;> intro he <;> exact ExprA.noConfusion he

inductive NonConstA3 : ExprA → Prop
  | bvar (i : Nat) : NonConstA3 (.bvar i)
  | sort (l : Level) : NonConstA3 (.sort l)
  | app (f a : ExprA) : NonConstA3 (.app f a)
  | lam (A : ExprA) (u : Level) (b : ExprA) : NonConstA3 (.lam A u b)
  | pi (A : ExprA) (u : Level) (B : ExprA) (v : Level) : NonConstA3 (.pi A u B v)
  | letE (A v b : ExprA) : NonConstA3 (.letE A v b)
  | lit (t : Nat) : NonConstA3 (.lit t)

theorem NonConstA3.not_const {e : ExprA} (h : NonConstA3 e) (r : Nat) (ls : List Level) :
    e ≠ .const r ls := by
  cases h <;> intro he <;> exact ExprA.noConfusion he

def propTailA3 : ExprA → Bool
  | .sort .zero => true
  | _ => false

/-- Each constructor is a positive, decidable fact about stored syntax. -/
inductive LayoutApartA3 (g : IotaGroupA) : Prop
  | zeroMinors (h : g.nMinors = 0)
  | manyMinors (h : 2 ≤ g.nMinors)
  | fewerParams (h : piCountA (g.ctorM.normA.getD g.ctorM.mtypeA) < g.nparams)
  | hasFields (h : g.nparams < piCountA (g.ctorM.normA.getD g.ctorM.mtypeA))
  | otherTail (h : propTailA3 (piBodyA g.famM.mtypeA) = false)

inductive ApartA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → Prop
  | nonApp {e : ExprA} (h : NonAppA3 e) : ApartA3 E I n Γ e
  | nonConstHead {e : ExprA} (h : NonConstA3 (appsSpineA e).1) : ApartA3 E I n Γ e
  | noGroup {e : ExprA} {r : Nat} {ls : List Level}
      (hh : (appsSpineA e).1 = .const r ls)
      (hg : iotaGroupA E r (r - 1) = none) : ApartA3 E I n Γ e
  | short {e : ExprA} {r : Nat} {ls : List Level} {m : CheckedMemberA}
      (hh : (appsSpineA e).1 = .const r ls) (hm : E.members r = some m)
      (hn : (appsSpineA e).2.length < piCountA m.mtypeA) : ApartA3 E I n Γ e
  | long {e : ExprA} {r : Nat} {ls : List Level} {m : CheckedMemberA}
      (hh : (appsSpineA e).1 = .const r ls) (hm : E.members r = some m)
      (hn : piCountA m.mtypeA < (appsSpineA e).2.length) : ApartA3 E I n Γ e
  | layout {e : ExprA} {r : Nat} {ls : List Level} {g : IotaGroupA}
      (hh : (appsSpineA e).1 = .const r ls)
      (hg : iotaGroupA E r (r - 1) = some g)
      (hbad : LayoutApartA3 g) : ApartA3 E I n Γ e

theorem frame_recRef {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {s : KStage.Shape} (w : KStage.Frame E I n Γ s) {e : ExprA} {r : Nat} {ls : List Level}
    (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls) : s.recRef = r := by
  have h := (congrArg (fun a => (appsSpineA a).1) he).trans hh
  simp only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA, appsSpineA_foldAppsA] at h
  exact (ExprA.const.inj h).1

theorem frame_group {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {s : KStage.Shape} (w : KStage.Frame E I n Γ s) {e : ExprA} {r : Nat} {ls : List Level}
    (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls) :
    iotaGroupA E r (r - 1) = some s.group := by
  have hr := frame_recRef w he hh
  have hc : s.ctorRef = r - 1 := by
    have hn := w.target.ctorNext
    omega
  simpa only [hr, hc] using w.target.group

theorem frame_arity {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {s : KStage.Shape} (w : KStage.Frame E I n Γ s) {e : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls)
    (hm : E.members r = some m) : (appsSpineA e).2.length = piCountA m.mtypeA := by
  have hr := frame_recRef w he hh
  have hres := (iotaGroupA_some w.target.group).1
  rw [hr] at hres
  have hmem := Option.some.inj (hres.symm.trans hm)
  have hcount : (appsSpineA s.source).2.length = piCountA s.group.recM.mtypeA := by
    simpa only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA,
      appsSpineA_foldAppsA, List.nil_append, List.length_append,
      List.length_cons, List.length_nil] using w.target.arity
  simpa only [he, hmem] using hcount

/-- Static apartness excludes a genuine old-stage K frame. -/
theorem ApartA3.excludes {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {e : ExprA} (h : ApartA3 E I n Γ e) {s : KStage.Shape}
    (w : KStage.Frame E I n Γ s) (he : s.source = e) : False := by
  cases h with
  | nonApp h => exact h.not_app s.prefix s.major he.symm
  | nonConstHead h =>
      have hh : (appsSpineA e).1 = .const s.recRef s.recLevels := by
        rw [← he]
        simp only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA, appsSpineA_foldAppsA]
      exact h.not_const _ _ hh
  | noGroup hh hg => exact Option.noConfusion ((frame_group w he hh).symm.trans hg)
  | short hh hm hn => have hc := frame_arity w he hh hm; omega
  | long hh hm hn => have hc := frame_arity w he hh hm; omega
  | layout hh hg hbad =>
      have hgroup := Option.some.inj (hg.symm.trans (frame_group w he hh))
      subst hgroup
      cases hbad with
      | zeroMinors h => have hc := w.target.oneConstructor; omega
      | manyMinors h => have hc := w.target.oneConstructor; omega
      | fewerParams h => have hc := w.target.noFields; omega
      | hasFields h => have hc := w.target.noFields; omega
      | otherTail h => rw [w.target.propFamily] at h; exact Bool.noConfusion h

mutual
  inductive NormalA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → Prop
    | sort (l : Level) : NormalA3 E I n Γ (.sort l)
    | lam (A : ExprA) (u : Level) (b : ExprA) : NormalA3 E I n Γ (.lam A u b)
    | pi (A : ExprA) (u : Level) (B : ExprA) (v : Level) : NormalA3 E I n Γ (.pi A u B v)
    | neutral {e : ExprA} (h : NeutralA3 E I n Γ e) : NormalA3 E I n Γ e

  inductive NeutralA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → Prop
    | bvar (i : Nat) (hv : lookupValueA Γ i = none) : NeutralA3 E I n Γ (.bvar i)
    | missing (r : Nat) (ls : List Level) (hm : E.members r = none) :
        NeutralA3 E I n Γ (.const r ls)
    | rigid (r : Nat) (ls : List Level) (m : CheckedMemberA)
        (hm : E.members r = some m) (ht : transparent m.mclass = false) :
        NeutralA3 E I n Γ (.const r ls)
    | noBody (r : Nat) (ls : List Level) (m : CheckedMemberA)
        (hm : E.members r = some m) (hb : m.bodyA = none) :
        NeutralA3 E I n Γ (.const r ls)
    | appIdle {f a : ExprA} (hf : NeutralA3 E I n Γ f)
        (ha : ApartA3 E I n Γ (.app f a))
        (hs : structPosA E f = false) (hi : I.fn (.app f a) = none)
        (hr : recAtMajorA E f = false) : NeutralA3 E I n Γ (.app f a)
    | appMajor {f a : ExprA} (hf : NeutralA3 E I n Γ f)
        (ha : ApartA3 E I n Γ (.app f a))
        (hs : structPosA E f = false) (hi : I.fn (.app f a) = none)
        (hr : recAtMajorA E f = true) (hu : unitMinorA E f = none)
        (hx : NormalA3 E I n Γ a) : NeutralA3 E I n Γ (.app f a)
end

theorem NeutralA3.not_lam {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {e : ExprA} (h : NeutralA3 E I n Γ e) : ∀ A u b, e ≠ .lam A u b := by
  cases h <;> intro _ _ _ he <;> exact ExprA.noConfusion he

theorem NeutralA3.apart {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {e : ExprA} (h : NeutralA3 E I n Γ e) : ApartA3 E I n Γ e := by
  cases h with
  | bvar i _ => exact .nonApp (.bvar i)
  | missing r ls _ => exact .nonApp (.const r ls)
  | rigid r ls _ _ _ => exact .nonApp (.const r ls)
  | noBody r ls _ _ _ => exact .nonApp (.const r ls)
  | appIdle _ ha _ _ _ => exact ha
  | appMajor _ ha _ _ _ _ _ => exact ha

theorem NormalA3.apart {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {e : ExprA} (h : NormalA3 E I n Γ e) : ApartA3 E I n Γ e := by
  cases h with
  | sort l => exact .nonApp (.sort l)
  | lam A u b => exact .nonApp (.lam A u b)
  | pi A u B v => exact .nonApp (.pi A u B v)
  | neutral h => exact h.apart

theorem normalA3_app_function {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {f a : ExprA} (h : NormalA3 E I n Γ (.app f a)) : NormalA3 E I n Γ f := by
  cases h with
  | neutral h =>
      cases h with
      | appIdle hf _ _ _ _ => exact .neutral hf
      | appMajor hf _ _ _ _ _ _ => exact .neutral hf

mutual
  theorem NormalA3.old_none {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
      {e : ExprA} : NormalA3 E I n Γ e → hStepFnA E I.fn Γ e = none
    | .sort _ => rfl
    | .lam _ _ _ => rfl
    | .pi _ _ _ _ => rfl
    | .neutral h => NeutralA3.old_none h

  theorem NeutralA3.old_none {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
      {e : ExprA} : NeutralA3 E I n Γ e → hStepFnA E I.fn Γ e = none
    | .bvar _ hv => hv
    | .missing r ls hm => by simp [hStepFnA, hm]
    | .rigid r ls m hm ht => by simp [hStepFnA, hm, ht]
    | .noBody r ls m hm hb => by simp [hStepFnA, hm, hb]
    | .appIdle (a := a) hf _ hs hi hr => by
        rw [hStepFnA_app_nonlam E I.fn Γ a hf.not_lam]
        simp [NeutralA3.old_none hf, hs, hi, hr]
    | .appMajor (a := a) hf _ hs hi hr hu hx => by
        rw [hStepFnA_app_nonlam E I.fn Γ a hf.not_lam]
        simp [NeutralA3.old_none hf, hs, hi, hr, hu, NormalA3.old_none hx]
end

/-- Every partial recursor prefix has a positive neutral derivation.  No
normality test or decision about index conversion is used. -/
theorem neutralA3_below {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hR : IotaRecHeadA E I) (Γ : LCtxA) :
    (e : ExprA) → {r : Nat} → {ls : List Level} → {m : CheckedMemberA} →
    (appsSpineA e).1 = .const r ls → E.members r = some m → m.mclass = .recursorM →
    BelowMajorA E e → NeutralA3 E I n Γ e
  | .const r' ls', r, ls, m, he, hres, hc, _ => by
      have h1 : ExprA.const r' ls' = .const r ls := he
      injection h1 with h1 _
      subst h1
      exact .rigid r' ls' m hres (by simp [hc, transparent])
  | .app f x, r, ls, m, he, hres, hc, hb => by
      have hf : (appsSpineA f).1 = .const r ls := he
      have hr := recAtMajorA_of_below hb
      exact .appIdle
        (neutralA3_below hR Γ f hf hres hc (belowMajorA_app hb))
        (.short he hres (hb r ls m he hres hc))
        (structPosA_of_not_rec hr) (iotaFn_none_of_below hR he hres hb) hr
  | .bvar _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .sort _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .lit _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h

theorem target_prefix_below {E : ResolvedEnvA} {s : KStage.Shape}
    (w : KStage.Target E s) : BelowMajorA E s.prefix := by
  intro r ls m hh hm _
  have hr : s.recRef = r := by
    have h := hh
    simp only [KStage.Shape.prefix, appsSpineA_foldAppsA, appsSpineA] at h
    exact (ExprA.const.inj h).1
  have hres := (iotaGroupA_some w.group).1
  rw [hr] at hres
  have hmem := Option.some.inj (hres.symm.trans hm)
  have hc : s.pre.length < piCountA m.mtypeA := by
    have ha := w.arity
    rw [hmem] at ha
    omega
  simpa only [KStage.Shape.prefix, appsSpineA_foldAppsA, appsSpineA,
    List.nil_append] using hc

/-- The actual K target supplies its positive neutral prefix generically. -/
theorem target_prefix_neutral {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hR : IotaRecHeadA E I) (Γ : LCtxA) {s : KStage.Shape} (w : KStage.Target E s) :
    NeutralA3 E I n Γ s.prefix :=
  neutralA3_below hR Γ s.prefix (r := s.recRef) (ls := s.recLevels) (m := s.group.recM)
    (by simp only [KStage.Shape.prefix, appsSpineA_foldAppsA, appsSpineA])
    (iotaGroupA_some w.group).1 (iotaGroupA_some w.group).2.1
    (target_prefix_below w)

#print axioms NonAppA3
#print axioms NonAppA3.not_app
#print axioms NonConstA3
#print axioms NonConstA3.not_const
#print axioms propTailA3
#print axioms LayoutApartA3
#print axioms ApartA3
#print axioms frame_recRef
#print axioms frame_group
#print axioms frame_arity
#print axioms ApartA3.excludes
#print axioms NormalA3
#print axioms NeutralA3
#print axioms NeutralA3.not_lam
#print axioms NeutralA3.apart
#print axioms NormalA3.apart
#print axioms normalA3_app_function
#print axioms NormalA3.old_none
#print axioms NeutralA3.old_none
#print axioms neutralA3_below
#print axioms target_prefix_below
#print axioms target_prefix_neutral

end Rcic.Declarative.Ann.LR3
