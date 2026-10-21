import rcic.RcicAnnLevels

/-!
# M2-e (7) — context conversion for the judgments

Two contexts whose declarations are pointwise convertible (`CtxConvA`: the same
declaration, or an assumption / let-binding whose type and value are
convertible, typed, in the target context) type the same terms at the same
types: `hasTyA_ctxConv`, `convA_ctxConv`. A variable's type in the target is the
original or a convertible one (`ctxConvA_lookupType`, `TyLookA`), and the
`bvar` case retypes through `conv`; a let-bound variable's value is the original
or a convertible one (`ctxConvA_lookupValue`, `ValLookA`), and the `zetaLocal`
case composes the ζ-step with that conversion through `tyConv` and `trans`. The
ι rule's redex is a recursor spine at exact arity (`IotaRecHeadTypedA`, read at the typed
redex: M2-f (1), (4b)), whose
function part is strictly below the major, and the head step never reads the
context on such a spine (`hStepFnA_ctx_below`: the major arm, which does read the
context, is dead below the major). The
binder cases extend the conversion by the SAME declaration (`CtxConvA.same`),
which needs no typing. Results are `Nonempty` (the conversion's own data is
`Nonempty`, so nothing is chosen).

What it is for: level irrelevance (M2-e (8)) — instantiating a derivation at `ls'`
types the right component of a `pi`/`lam` congruence in the `ls'`-instantiated
context, while the rule wants it in the `ls`-instantiated one; the two are
pointwise convertible.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) pointwise convertible contexts -/

inductive CtxConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : LCtxA → LCtxA → Prop
  | nil : CtxConvA E I n [] []
  /-- the same declaration on both sides: no typing needed. -/
  | same {Γ Γ' : LCtxA} (d : LocalDeclA) (h : CtxConvA E I n Γ Γ') :
      CtxConvA E I n (d :: Γ) (d :: Γ')
  | assumption {Γ Γ' : LCtxA} {A A' : ExprA} {u : Level} (h : CtxConvA E I n Γ Γ')
      (hA : Nonempty (HasTyA E I n Γ' A (.sort u))) (hA' : Nonempty (HasTyA E I n Γ' A' (.sort u)))
      (hc : Nonempty (ConvA E I n Γ' A A' (.sort u))) :
      CtxConvA E I n (.assumption A :: Γ) (.assumption A' :: Γ')
  | letBinding {Γ Γ' : LCtxA} {A A' v v' : ExprA} {u : Level} (h : CtxConvA E I n Γ Γ')
      (hA : Nonempty (HasTyA E I n Γ' A (.sort u))) (hA' : Nonempty (HasTyA E I n Γ' A' (.sort u)))
      (hc : Nonempty (ConvA E I n Γ' A A' (.sort u)))
      (hv' : Nonempty (HasTyA E I n Γ' v' A')) (hcv : Nonempty (ConvA E I n Γ' v v' A)) :
      CtxConvA E I n (.letBinding A v :: Γ) (.letBinding A' v' :: Γ')

theorem ctxConvA_refl {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    (Γ : LCtxA) → CtxConvA E I n Γ Γ
  | [] => .nil
  | d :: Γ => .same d (ctxConvA_refl Γ)

section Look
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a variable's type in the target: the original, or a convertible one, both typed. -/
def TyLookA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ' : LCtxA) (A A' : ExprA) : Prop :=
  A' = A ∨ ∃ u, Nonempty (HasTyA E I n Γ' A (.sort u)) ∧ Nonempty (HasTyA E I n Γ' A' (.sort u)) ∧
    Nonempty (ConvA E I n Γ' A A' (.sort u))

/-- a let-bound variable's value in the target: the original, or a convertible one. -/
def ValLookA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ' : LCtxA) (A A' v v' : ExprA) : Prop :=
  (A' = A ∧ v' = v) ∨ ∃ u, Nonempty (HasTyA E I n Γ' A (.sort u)) ∧ Nonempty (HasTyA E I n Γ' A' (.sort u)) ∧
    Nonempty (ConvA E I n Γ' A A' (.sort u)) ∧ Nonempty (HasTyA E I n Γ' v' A') ∧
    Nonempty (ConvA E I n Γ' v v' A)

theorem tyLookA_lift (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) {Γ' : LCtxA}
    {A A' : ExprA} (h : TyLookA E I n Γ' A A') :
    TyLookA E I n (d :: Γ') (liftA 0 1 A) (liftA 0 1 A') :=
  h.elim (fun e => Or.inl (by rw [e])) fun ⟨u, hA, hA', hc⟩ => Or.inr ⟨u,
    hA.elim fun t => ⟨hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) t⟩,
    hA'.elim fun t => ⟨hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) t⟩,
    hc.elim fun c => ⟨convWeakenA hE hI d (c := 0) (Nat.zero_le _) c⟩⟩

theorem valLookA_lift (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) {Γ' : LCtxA}
    {A A' v v' : ExprA} (h : ValLookA E I n Γ' A A' v v') :
    ValLookA E I n (d :: Γ') (liftA 0 1 A) (liftA 0 1 A') (liftA 0 1 v) (liftA 0 1 v') :=
  h.elim (fun ⟨eA, ev⟩ => Or.inl ⟨by rw [eA], by rw [ev]⟩) fun ⟨u, hA, hA', hc, hv', hcv⟩ => Or.inr ⟨u,
    hA.elim fun t => ⟨hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) t⟩,
    hA'.elim fun t => ⟨hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) t⟩,
    hc.elim fun c => ⟨convWeakenA hE hI d (c := 0) (Nat.zero_le _) c⟩,
    hv'.elim fun t => ⟨hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) t⟩,
    hcv.elim fun c => ⟨convWeakenA hE hI d (c := 0) (Nat.zero_le _) c⟩⟩

/-- the tail step of the type lookup: index `i + 1` reads the tail at `i`, lifted. -/
theorem lookupType_succ_conv (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ Γ' : LCtxA} (d d' : LocalDeclA)
    {i : Nat}
    (ih : ∀ {A₀ : ExprA}, lookupTypeA Γ i = some A₀ →
      ∃ A', lookupTypeA Γ' i = some A' ∧ TyLookA E I n Γ' A₀ A')
    {A : ExprA} (h : lookupTypeA (d :: Γ) (i + 1) = some A) :
    ∃ A', lookupTypeA (d' :: Γ') (i + 1) = some A' ∧ TyLookA E I n (d' :: Γ') A A' := by
  rw [lookupTypeA_cons_succ] at h
  cases hΓ : lookupTypeA Γ i with
  | none => rw [hΓ] at h; cases h
  | some A₀ =>
      rw [hΓ] at h
      cases h
      obtain ⟨A', hA', hl⟩ := ih hΓ
      exact ⟨liftA 0 1 A', by rw [lookupTypeA_cons_succ, hA']; rfl, tyLookA_lift hE hI d' hl⟩

theorem lookupValue_succ_conv (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ Γ' : LCtxA} (d d' : LocalDeclA)
    {i : Nat}
    (ih : ∀ {v₀ : ExprA}, lookupValueA Γ i = some v₀ →
      ∃ v' A A', lookupTypeA Γ i = some A ∧ lookupValueA Γ' i = some v' ∧
        lookupTypeA Γ' i = some A' ∧ ValLookA E I n Γ' A A' v₀ v')
    {v : ExprA} (h : lookupValueA (d :: Γ) (i + 1) = some v) :
    ∃ v' A A', lookupTypeA (d :: Γ) (i + 1) = some A ∧ lookupValueA (d' :: Γ') (i + 1) = some v' ∧
      lookupTypeA (d' :: Γ') (i + 1) = some A' ∧ ValLookA E I n (d' :: Γ') A A' v v' := by
  rw [lookupValueA_cons_succ] at h
  cases hΓ : lookupValueA Γ i with
  | none => rw [hΓ] at h; cases h
  | some v₀ =>
      rw [hΓ] at h
      cases h
      obtain ⟨v', A, A', hty, hval', hty', hl⟩ := ih hΓ
      exact ⟨liftA 0 1 v', liftA 0 1 A, liftA 0 1 A',
        by rw [lookupTypeA_cons_succ, hty]; rfl, by rw [lookupValueA_cons_succ, hval']; rfl,
        by rw [lookupTypeA_cons_succ, hty']; rfl, valLookA_lift hE hI d' hl⟩

theorem ctxConvA_lookupType (hE : EnvClosedA E) (hI : IotaLiftA I) :
    {Γ Γ' : LCtxA} → CtxConvA E I n Γ Γ' → (i : Nat) → {A : ExprA} →
    lookupTypeA Γ i = some A → ∃ A', lookupTypeA Γ' i = some A' ∧ TyLookA E I n Γ' A A'
  | _, _, .nil, i, _, h => by cases i <;> cases h
  | _, _, .same d _, 0, A, h => ⟨A, by cases d <;> exact h, Or.inl rfl⟩
  | _, _, .same d hcc, i + 1, _, h =>
      lookupType_succ_conv hE hI d d (fun h₀ => ctxConvA_lookupType hE hI hcc i h₀) h
  | _, _, .assumption (A := A₀) (A' := A₀') (u := u) _ hA hA' hc, 0, _, h => by
      cases h
      exact ⟨liftA 0 1 A₀', rfl, tyLookA_lift hE hI (.assumption A₀') (Or.inr ⟨u, hA, hA', hc⟩)⟩
  | _, _, .assumption (A := A₀) (A' := A₀') hcc _ _ _, i + 1, _, h =>
      lookupType_succ_conv hE hI (.assumption A₀) (.assumption A₀')
        (fun h₀ => ctxConvA_lookupType hE hI hcc i h₀) h
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') (u := u) _ hA hA' hc _ _, 0, _, h => by
      cases h
      exact ⟨liftA 0 1 A₀', rfl,
        tyLookA_lift hE hI (.letBinding A₀' v₀') (Or.inr ⟨u, hA, hA', hc⟩)⟩
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') hcc _ _ _ _ _, i + 1, _, h =>
      lookupType_succ_conv hE hI (.letBinding A₀ v₀) (.letBinding A₀' v₀')
        (fun h₀ => ctxConvA_lookupType hE hI hcc i h₀) h

theorem ctxConvA_lookupValue (hE : EnvClosedA E) (hI : IotaLiftA I) :
    {Γ Γ' : LCtxA} → CtxConvA E I n Γ Γ' → (i : Nat) → {v : ExprA} →
    lookupValueA Γ i = some v →
    ∃ v' A A', lookupTypeA Γ i = some A ∧ lookupValueA Γ' i = some v' ∧
      lookupTypeA Γ' i = some A' ∧ ValLookA E I n Γ' A A' v v'
  | _, _, .nil, i, _, h => by cases i <;> cases h
  | _, _, .same (.assumption a) _, 0, _, h => by cases h
  | _, _, .same (.letBinding a w) _, 0, _, h => by
      cases h
      exact ⟨liftA 0 1 w, liftA 0 1 a, liftA 0 1 a, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | _, _, .same d hcc, i + 1, _, h =>
      lookupValue_succ_conv hE hI d d (fun h₀ => ctxConvA_lookupValue hE hI hcc i h₀) h
  | _, _, .assumption _ _ _ _, 0, _, h => by cases h
  | _, _, .assumption (A := A₀) (A' := A₀') hcc _ _ _, i + 1, _, h =>
      lookupValue_succ_conv hE hI (.assumption A₀) (.assumption A₀')
        (fun h₀ => ctxConvA_lookupValue hE hI hcc i h₀) h
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') (u := u) _ hA hA' hc hv' hcv, 0, _, h => by
      cases h
      exact ⟨liftA 0 1 v₀', liftA 0 1 A₀, liftA 0 1 A₀', rfl, rfl, rfl,
        valLookA_lift hE hI (.letBinding A₀' v₀') (Or.inr ⟨u, hA, hA', hc, hv', hcv⟩)⟩
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') hcc _ _ _ _ _, i + 1, _, h =>
      lookupValue_succ_conv hE hI (.letBinding A₀ v₀) (.letBinding A₀' v₀')
        (fun h₀ => ctxConvA_lookupValue hE hI hcc i h₀) h

end Look

/-! ## (2) the head step reads no context on a member-headed spine strictly below the
    major: the major arm, which reads an argument through `Γ` (ζ-local), is dead there -/

theorem hStepFnA_ctx_below (E : ResolvedEnvA) (I : IotaFnA) (Γ Γ' : LCtxA) :
    (e : ExprA) → (∃ r ls, (appsSpineA e).1 = .const r ls) → BelowMajorA E e →
    hStepFnA E I Γ e = hStepFnA E I Γ' e
  | .const _ _, _, _ => rfl
  | .app f x, ⟨r, ls, hr⟩, hb => by
      have hf : ∃ r ls, (appsSpineA f).1 = .const r ls := ⟨r, ls, hr⟩
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by
        subst e; simp [appsSpineA] at hr
      rw [hStepFnA_app_nonlam E I Γ x hnl, hStepFnA_app_nonlam E I Γ' x hnl,
        hStepFnA_ctx_below E I Γ Γ' f hf (belowMajorA_app hb),
        structPosA_of_not_rec (recAtMajorA_of_below hb), recAtMajorA_of_below hb]
      cases hStepFnA E I Γ' f with
      | some f' => rfl
      | none => cases I (.app f x) <;> rfl
  | .bvar _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h
  | .sort _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h
  | .lam _ _ _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h
  | .pi _ _ _ _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h
  | .letE _ _ _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h
  | .lit _, ⟨_, _, h⟩, _ => by simp [appsSpineA] at h

theorem iotaRecHeadTypedA_prefix {E₀ E : ResolvedEnvA} {I : IotaIfaceA} (hpre : PrefixA E₀ E)
    (hR : IotaRecHeadA E I) : IotaRecHeadTypedA E₀ I := by
  intro n Γ e e' T hfn ht
  obtain ⟨ht⟩ := ht
  obtain ⟨r, ls, m, hsp, hres, hc, hlen⟩ := hR e e' hfn
  obtain ⟨m₀, hm₀⟩ := constsInA_head e (hasTyA_constsIn ht) r ls hsp
  have e₀ : m₀ = m := Option.some.inj ((hpre r m₀ hm₀).symm.trans hres)
  subst e₀
  exact ⟨r, ls, m₀, hsp, hm₀, hc, hlen⟩

/-- a declarative ι step moves between ANY two contexts: its redex is a recursor
    spine at exact arity (`IotaRecHeadTypedA` at the typed redex), whose function part is
    strictly below the major and so steps the same way in every context. -/
theorem iotaRel_ctx {E : ResolvedEnvA} {I : IotaIfaceA} (hR : IotaRecHeadTypedA E I) {n : Nat}
    {Γ Γ' : LCtxA} {e e' T : ExprA} (h : I.rel E Γ e e') (ht : HasTyA E I n Γ e T) :
    I.rel E Γ' e e' := by
  obtain ⟨r, ls, m, hsp, hres, hc, hlen⟩ := hR n Γ e e' T h.1 ⟨ht⟩
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases e with
  | app f x =>
      have hf : (appsSpineA f).1 = .const r ls := hsp
      have hb : BelowMajorA E f := belowMajorA_of_at hsp hres hlen
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by
        subst e; simp [appsSpineA] at hf
      have hctx := hStepFnA_ctx_below E I.fn Γ Γ' f ⟨r, ls, hf⟩ hb
      rw [hStepFnA_app_nonlam E I.fn Γ x hnl] at h2
      cases hff : hStepFnA E I.fn Γ f with
      | some f' =>
          rw [hff] at h2
          have h2' : some (ExprA.app f' x) = some e' := h2
          injection h2' with h2'
          rw [← h2']
          exact hStepFnA_app_head E I.fn Γ' x (hctx.symm.trans hff)
      | none =>
          cases hp : structPosA E f with
          | true =>
              -- W-1 (e): at the struct position the step is the struct arm's, which reads no context
              rw [hStepFnA_app_structPos E I.fn Γ' hnl (hctx.symm.trans hff) hp,
                ← hStepFnA_app_structPos E I.fn Γ hnl hff hp]
              exact h.2
          | false => exact hStepFnA_app_iota E I.fn Γ' hnl (hctx.symm.trans hff) hp h.1
  | const r' ls' =>
      exfalso
      have h1 : ExprA.const r' ls' = .const r ls := hsp
      injection h1 with h1 _
      subst h1
      have h2' : (match E.members r' with
          | some m => if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none
          | none => none) = some e' := h2
      rw [hres] at h2'
      simp [hc, transparent] at h2'
  | bvar _ => simp [appsSpineA] at hsp
  | sort _ => simp [appsSpineA] at hsp
  | lam _ _ _ => simp [appsSpineA] at hsp
  | pi _ _ _ _ => simp [appsSpineA] at hsp
  | letE _ _ _ => simp [appsSpineA] at hsp
  | lit _ => simp [appsSpineA] at hsp

/-! ## (3) the judgments under context conversion -/

section Conv
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

mutual

theorem hasTyA_ctxConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) :
    {Γ Γ' : LCtxA} → CtxConvA E I n Γ Γ' → {e A : ExprA} → HasTyA E I n Γ e A →
    Nonempty (HasTyA E I n Γ' e A)
  | _, Γ', _, _, _, .sort _ l => ⟨.sort Γ' l⟩
  | _, Γ', hcc, _, _, .bvar _ i A u h hA => by
      obtain ⟨A', hA', hl⟩ := ctxConvA_lookupType hE hI hcc i h
      have hAΓ' := hasTyA_ctxConv hE hI hR hcc hA
      rcases hl with e | ⟨u', tA, tA', hc⟩
      · rw [e] at hA'
        exact hAΓ'.elim fun t => ⟨.bvar Γ' i A u hA' t⟩
      · exact tA.elim fun t => tA'.elim fun t' => hc.elim fun c =>
          ⟨.conv Γ' (.bvar i) A' A u' u' (.bvar Γ' i A' u' hA' t') t' (eqNA_refl u') t
            (.symm Γ' A A' (.sort u') c)⟩
  | _, Γ', hcc, _, _, .const _ r ls m u hres hlen hwf hT =>
      (hasTyA_ctxConv hE hI hR hcc hT).elim fun t => ⟨.const Γ' r ls m u hres hlen hwf t⟩
  | _, Γ', hcc, _, _, .pi _ A u B v hA hB =>
      (hasTyA_ctxConv hE hI hR hcc hA).elim fun a =>
        (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hB).elim fun b => ⟨.pi Γ' A u B v a b⟩
  | _, Γ', hcc, _, _, .lam _ A u body B v hA hB hbody =>
      (hasTyA_ctxConv hE hI hR hcc hA).elim fun a =>
        (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hB).elim fun b =>
        (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hbody).elim fun t =>
          ⟨.lam Γ' A u body B v a b t⟩
  | _, Γ', hcc, _, _, .app _ f a A B u v w hB hTy hf ha =>
      (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hB).elim fun b =>
        (hasTyA_ctxConv hE hI hR hcc hTy).elim fun ty =>
        (hasTyA_ctxConv hE hI hR hcc hf).elim fun tf =>
        (hasTyA_ctxConv hE hI hR hcc ha).elim fun ta => ⟨.app Γ' f a A B u v w b ty tf ta⟩
  | _, Γ', hcc, _, _, .letE _ A u w value B body hA hv hTy hb =>
      (hasTyA_ctxConv hE hI hR hcc hA).elim fun a =>
        (hasTyA_ctxConv hE hI hR hcc hv).elim fun tv =>
        (hasTyA_ctxConv hE hI hR hcc hTy).elim fun ty =>
        (hasTyA_ctxConv hE hI hR (.same (.letBinding A value) hcc) hb).elim fun tb =>
          ⟨.letE Γ' A u w value B body a tv ty tb⟩
  | _, Γ', hcc, _, _, .lit _ t T hexp =>
      (hasTyA_ctxConv hE hI hR hcc hexp).elim fun h => ⟨.lit Γ' t T h⟩
  | _, Γ', hcc, _, _, .conv _ e A B l u h hAl hlu hB hc =>
      (hasTyA_ctxConv hE hI hR hcc h).elim fun t =>
        (hasTyA_ctxConv hE hI hR hcc hAl).elim fun tAl =>
        (hasTyA_ctxConv hE hI hR hcc hB).elim fun tB =>
        (convA_ctxConv hE hI hR hcc hc).elim fun c => ⟨.conv Γ' e A B l u t tAl hlu tB c⟩

theorem convA_ctxConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) :
    {Γ Γ' : LCtxA} → CtxConvA E I n Γ Γ' → {a b A : ExprA} → ConvA E I n Γ a b A →
    Nonempty (ConvA E I n Γ' a b A)
  | _, Γ', hcc, _, _, _, .refl _ a A h => (hasTyA_ctxConv hE hI hR hcc h).elim fun t => ⟨.refl Γ' a A t⟩
  | _, Γ', hcc, _, _, _, .symm _ a b A h => (convA_ctxConv hE hI hR hcc h).elim fun c => ⟨.symm Γ' a b A c⟩
  | _, Γ', hcc, _, _, _, .trans _ a b c A h1 h2 =>
      (convA_ctxConv hE hI hR hcc h1).elim fun c1 => (convA_ctxConv hE hI hR hcc h2).elim fun c2 =>
        ⟨.trans Γ' a b c A c1 c2⟩
  | _, Γ', hcc, _, _, _, .beta _ A u body arg B hA hbody harg hred =>
      (hasTyA_ctxConv hE hI hR hcc hA).elim fun a =>
        (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hbody).elim fun tb =>
        (hasTyA_ctxConv hE hI hR hcc harg).elim fun ta =>
        (hasTyA_ctxConv hE hI hR hcc hred).elim fun tr => ⟨.beta Γ' A u body arg B a tb ta tr⟩
  | _, Γ', hcc, _, _, _, .zeta _ A value body B u hA hv hb hred =>
      (hasTyA_ctxConv hE hI hR hcc hA).elim fun a =>
        (hasTyA_ctxConv hE hI hR hcc hv).elim fun tv =>
        (hasTyA_ctxConv hE hI hR (.same (.letBinding A value) hcc) hb).elim fun tb =>
        (hasTyA_ctxConv hE hI hR hcc hred).elim fun tr => ⟨.zeta Γ' A value body B u a tv tb tr⟩
  | _, Γ', hcc, _, _, _, .zetaLocal _ i A v hval hty hv => by
      obtain ⟨v', A₀, A', hty₀, hval', hty', hl⟩ := ctxConvA_lookupValue hE hI hcc i hval
      have eA : A₀ = A := Option.some.inj (hty₀.symm.trans hty)
      rw [eA] at hl
      have hvΓ' := hasTyA_ctxConv hE hI hR hcc hv
      rcases hl with ⟨eA', ev⟩ | ⟨u, tA, tA', hc, tv', hcv⟩
      · rw [eA'] at hty'
        rw [ev] at hval'
        exact hvΓ'.elim fun t => ⟨.zetaLocal Γ' i A v hval' hty' t⟩
      · exact tA.elim fun ta => tA'.elim fun ta' => hc.elim fun c => tv'.elim fun tv' => hcv.elim fun cv =>
          ⟨.trans Γ' (.bvar i) v' v A
            (.tyConv Γ' (.bvar i) v' A' A u u u (.zetaLocal Γ' i A' v' hval' hty' tv') ta'
              (eqNA_refl u) ta (eqNA_refl u) (.symm Γ' A A' (.sort u) c))
            (.symm Γ' v v' A cv)⟩
  | _, Γ', hcc, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb =>
      (hasTyA_ctxConv hE hI hR hcc hb).elim fun t => ⟨.delta Γ' r ls m b hres hbody htr hlen hwf t⟩
  | _, Γ', hcc, _, _, _, .iota _ lhs rhs T h hlhs hrhs =>
      (hasTyA_ctxConv hE hI hR hcc hlhs).elim fun tl => (hasTyA_ctxConv hE hI hR hcc hrhs).elim fun tr =>
        ⟨.iota Γ' lhs rhs T (iotaRel_ctx hR h hlhs) tl tr⟩
  | _, Γ', hcc, _, _, _, .structIota _ f a rhs e T hrec hs h hlhs hrhs hcv =>
      (hasTyA_ctxConv hE hI hR hcc hlhs).elim fun tl => (hasTyA_ctxConv hE hI hR hcc hrhs).elim fun tr =>
        (convA_ctxConv hE hI hR hcc hcv).elim fun c => ⟨.structIota Γ' f a rhs e T hrec hs h tl tr c⟩
  | _, Γ', hcc, _, _, _, .lit _ t T hexp =>
      (hasTyA_ctxConv hE hI hR hcc hexp).elim fun h => ⟨.lit Γ' t T h⟩
  | _, Γ', hcc, _, _, _, .app _ f g a b A B u v h1 h2 hB hrt =>
      (convA_ctxConv hE hI hR hcc h1).elim fun c1 => (convA_ctxConv hE hI hR hcc h2).elim fun c2 =>
        (hasTyA_ctxConv hE hI hR (.same (.assumption A) hcc) hB).elim fun tB =>
        (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr => ⟨.app Γ' f g a b A B u v c1 c2 tB tr⟩
  | _, Γ', hcc, _, _, _, .lam _ A A' b b' B u u' v hu hA hb hrt =>
      (convA_ctxConv hE hI hR hcc hA).elim fun cA =>
        (convA_ctxConv hE hI hR (.same (.assumption A) hcc) hb).elim fun cb =>
        (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr => ⟨.lam Γ' A A' b b' B u u' v hu cA cb tr⟩
  | _, Γ', hcc, _, _, _, .pi _ A A' B B' u u' v v' hu hv hA hB hrt =>
      (convA_ctxConv hE hI hR hcc hA).elim fun cA =>
        (convA_ctxConv hE hI hR (.same (.assumption A) hcc) hB).elim fun cB =>
        (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr => ⟨.pi Γ' A A' B B' u u' v v' hu hv cA cB tr⟩
  | _, Γ', hcc, _, _, _, .letE _ A A' v v' b b' B u hA hv hb hrt =>
      (convA_ctxConv hE hI hR hcc hA).elim fun cA => (convA_ctxConv hE hI hR hcc hv).elim fun cv =>
        (convA_ctxConv hE hI hR (.same (.letBinding A v) hcc) hb).elim fun cb =>
        (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr => ⟨.letE Γ' A A' v v' b b' B u cA cv cb tr⟩
  | _, Γ', _, _, _, _, .sorts _ l₁ l₂ h => ⟨.sorts Γ' l₁ l₂ h⟩
  | _, Γ', hcc, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h hrt =>
      (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr => ⟨.consts Γ' r ls ls' m hres hlen hwf hwf' h tr⟩
  | _, Γ', hcc, _, _, _, .eta _ f A B u v h hrt =>
      (hasTyA_ctxConv hE hI hR hcc h).elim fun t => (hasTyA_ctxConv hE hI hR hcc hrt).elim fun tr =>
        ⟨.eta Γ' f A B u v t tr⟩
  | _, Γ', hcc, _, _, _, .irr _ P p q hP hp hq =>
      (hasTyA_ctxConv hE hI hR hcc hP).elim fun tP => (hasTyA_ctxConv hE hI hR hcc hp).elim fun tp =>
        (hasTyA_ctxConv hE hI hR hcc hq).elim fun tq => ⟨.irr Γ' P p q tP tp tq⟩
  | _, Γ', hcc, _, _, _, .tyConv _ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      (convA_ctxConv hE hI hR hcc h).elim fun c =>
        (hasTyA_ctxConv hE hI hR hcc hAl).elim fun tAl =>
        (hasTyA_ctxConv hE hI hR hcc hA'l).elim fun tA'l =>
        (convA_ctxConv hE hI hR hcc hA).elim fun cA =>
          ⟨.tyConv Γ' a b A A' l l' u c tAl hlu tA'l hl'u cA⟩

end

end Conv

#print axioms ctxConvA_lookupType
#print axioms ctxConvA_lookupValue
#print axioms hStepFnA_ctx_below
#print axioms iotaRecHeadTypedA_prefix
#print axioms iotaRel_ctx
#print axioms hasTyA_ctxConv
#print axioms convA_ctxConv

end Rcic.Declarative.Ann
