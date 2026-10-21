import rcic.RcicNativeValleyFronts

/-!
# RcicNativeValleyAppBeta — the `app × beta` row
(Wall 1, `NativeConvValleys`, piece 12)

`OpenRows.app_beta` (`RcicNativeValleyAssemble`): the function child of an `app` node steps out
of `lam A body` while the other side β-contracts. Recursion on the certificate of the function
child's step (its source read through an equation, the index chain `hc` accumulated through
`conv` roots):

* `refl` (the λ is unchanged) and `lam` (the λ steps by congruence) — CLOSED: the bodies join
  by the induction hypothesis under the source domain, the arguments join by the induction
  hypothesis at the two nodes' domains `A'` / `A`; the `app` side then β-contracts onto the
  joint body and argument (`betaLeg`, certificate `ConvT.beta` then the one-step certified mixed
  substitution `CertSubst0`), the β side substitutes the joins (`CertSubst0`, realigned by the
  argument child's certificate); the `lam` case moves the body join under the stepped domain by
  `CertAssumpCtx`. Two same-term re-presentations enter, both `Retype`: the argument child
  `arg ⇒ a'` is typed by the `app` node at `A'` and consumed by the β at `A`, and the `app`
  side's output is built at the β's natural index and presented at the `app` node's index
  through its right-endpoint typing.
* `conv` — peeled, `hc` extended.
* `peq` (the λ is a proof) — CLOSED modulo `PropAlign` and `PiPropCodom`: `T₀ : Prop` transfers
  to the λ's other type `Π A' B'`, whose codomain instance `B'[arg]` is then `Prop`; the join is
  the β-reduct, reached from the `app` side by one irrelevance step (its typing at the `app`
  index through `Retype` of the β node).
* `eta`, `iotaSpine` — the fronts `AppBetaEta`, `AppBetaIota` (the η/β interaction).
* every other root is refuted by the source shape.

`app_beta_of` has exactly the field's statement.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The induction hypothesis is monotone in its bound. -/
def IHBelow.mono {m m' : Nat} (h : m ≤ m') (ih : IHBelow E n PEq m') : IHBelow E n PEq m :=
  fun {_} hΓ {_ _ _ _ _} {_} cp {_} cq hlt => ih hΓ cp cq (Nat.lt_of_lt_of_le hlt h)

/-- The argument join of `app × beta`, re-presented at the β node's domain `A`: the `app`
    node's argument child (`arg ⇒ a'` at `A'`) is first retyped to `A` (where `arg` is typed by
    the β node), its right endpoint types `a'` at `A`, and the join's `a'`-leg is retyped
    there. -/
def argJoin (L : LeafIface E n PEq) (Rt : Retype E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {arg a' arg' A' A : Expr Nat} {ha : ParRedT PEq E n Γ arg a' A'} (ca : Certified ha)
    {ha₂ : ParRedT PEq E n Γ arg arg' A} (ca₂ : Certified ha₂)
    {m : Nat} (ih : IHBelow E n PEq m) (hsz : sizeOf ha + sizeOf ha₂ < m) :
    Σ' (a₃ : Expr Nat), CStep E n PEq Γ a' a₃ A ×' CStep E n PEq Γ arg' a₃ A :=
  let harg : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha₂
  let haA : CStep E n PEq Γ arg a' A := Rt hΓ harg ⟨ha, ca⟩
  let ⟨a₃, pa, qa⟩ := ih hΓ ca ca₂ hsz
  ⟨a₃, Rt hΓ (haA.rightTyped L hΓ) pa, qa⟩

/-- The β side's output: the β-reduct substitutes the body join and the argument join
    (`CertSubst0`), realigned to the β node's index by the argument child's certificate. -/
def betaRight (L : LeafIface E n PEq) (S : CertSubst0 E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body' b₃ arg arg' a₃ B : Expr Nat} {u v' : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v'))
    {ha₂ : ParRedT PEq E n Γ arg arg' A} (ca₂ : Certified ha₂)
    (qb : CStep E n PEq (.assumption A :: Γ) body' b₃ B) (qa : CStep E n PEq Γ arg' a₃ A) :
    CStep E n PEq Γ (instantiate0 arg' body') (instantiate0 a₃ b₃) (instantiate0 arg B) :=
  let harg : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha₂
  (S hΓ hA qb qa).reindex (.of _ _ _ v'
    (convT_inst0_valueSort hA hB₂ (qa.leftTyped L hΓ) harg (.symm _ _ _ _ ca₂.root)))

/-- One β-contraction onto joint body and argument, at its natural index `B₁[a']`: the
    certificate is `ConvT.beta` followed by the certified mixed substitution's. -/
def betaLeg (hW : EnvWfT E) (L : LeafIface E n PEq) (S : CertSubst0 E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A₁ b₁ b₃ a' a₃ B₁ : Expr Nat} {u₁ v₁ : Level}
    (hA₁ : HasTyT E n Γ A₁ (.sort u₁)) (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (pb : CStep E n PEq (.assumption A₁ :: Γ) b₁ b₃ B₁) (pa : CStep E n PEq Γ a' a₃ A₁) :
    CStep E n PEq Γ (.app (.lam A₁ b₁) a') (instantiate0 a₃ b₃) (instantiate0 a' B₁) :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hb₁ : HasTyT E n (.assumption A₁ :: Γ) b₁ B₁ := pb.leftTyped L (.assumption Γ A₁ u₁ hΓ hA₁)
  let ha'₁ : HasTyT E n Γ a' A₁ := pa.leftTyped L hΓ
  let hTy₁ : HasTyT E n Γ (instantiate0 a' B₁) (.sort v₁) := hasTyT_subst0S hcl hinst hB₁ ha'₁
  let sub := S hΓ hA₁ pb pa
  let cert : ConvT E n Γ (.app (.lam A₁ b₁) a') (instantiate0 a₃ b₃) (instantiate0 a' B₁) :=
    .trans _ _ _ _ _ (.beta Γ A₁ b₁ a' B₁ u₁ hA₁ hb₁ ha'₁) sub.toConvT
  ⟨.beta Γ A₁ b₁ b₃ a' a₃ B₁ u₁ v₁ v₁ hA₁ hB₁ hTy₁ pb.step pa.step (convEnds hW hΓ cert).2.1,
    .beta cert pb.cert pa.cert⟩

/-- The core of `app × beta`: recursion on the certificate of the function child's step, the
    source read through `x = lam A body`, the index chain `hc` accumulated; the β node's data
    fixed. -/
def appBetaCore (hW : EnvWfT E) (L : LeafIface E n PEq) (Rt : Retype E n PEq)
    (PA : PropAlign E n) (PC : PiPropCodom E n) (S : CertSubst0 E n PEq)
    (Ac : CertAssumpCtx E n PEq) (AE : AppBetaEta E n PEq) (AI : AppBetaIota E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body arg a' A' B' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    (hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'} (ca : Certified ha)
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (cq : Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb
      ha₂ hred))
    (cb : Certified hb) (ca₂ : Certified ha₂)
    (hpq : HasTyT E n Γ (.app (.lam A body) arg) (instantiate0 arg B'))
    (m : Nat) (ih : IHBelow E n PEq m) :
    {x f' T₀ : Expr Nat} → {hf : ParRedT PEq E n Γ x f' T₀} → Certified hf → x = .lam A body →
    TyConvT E n Γ T₀ (.pi A' B') → HasTyT E n Γ (.app f' a') (instantiate0 arg B') →
    sizeOf hf + sizeOf ha + sizeOf hb + sizeOf ha₂ < m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx, _, hr, hsz => by
      subst hx
      obtain ⟨a₃, pa, qa⟩ := argJoin L Rt hΓ ca ca₂ ih (by omega)
      have hbody' : HasTyT E n (.assumption A :: Γ) body' B :=
        parRedT_hasTy_right L.typed (.assumption Γ A u hΓ hA) hb
      have right := betaRight L S hΓ hA hB₂ ca₂ ⟨.refl _ body' B hbody', .refl (.refl _ _ _ hbody')⟩ qa
      have left := betaLeg hW L S hΓ hA hB₂ ⟨hb, cb⟩ pa
      exact ⟨instantiate0 a₃ body', Rt hΓ hr left, right⟩
  | _, _, _, _, @Certified.lam _ _ _ _ _ A'' _ f_body B₀ u₀ v₀ hc₀ hA₀ hB₀ hb₀ _ _ cb₀, hx, _,
      hr, hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      have hcl := envClosed_of_envWfT hW
      obtain ⟨a₃, pa, qa⟩ := argJoin L Rt hΓ ca ca₂ ih (by simp at hsz; omega)
      obtain ⟨b₃, pb, qb⟩ := ih (.assumption Γ _ u hΓ hA) cb₀ cb (by simp at hsz; omega)
      have right := betaRight L S hΓ hA hB₂ ca₂ qb qa
      have hA'' : HasTyT E n Γ A'' (.sort u₀) := (convEnds hW hΓ hc₀).2.1
      have hctx : CtxConvT E n (.assumption _ :: Γ) (.assumption A'' :: Γ) :=
        .assumption (ctxConvT_refl Γ) hA₀ hA'' hc₀
      have pb'' : CStep E n PEq (.assumption A'' :: Γ) f_body b₃ B₀ := Ac hA₀ hA'' hc₀ pb
      have hB₀'' : HasTyT E n (.assumption A'' :: Γ) B₀ (.sort v₀) := hasTyT_ctx hcl hctx hB₀
      have pa'' : CStep E n PEq Γ a' a₃ A'' := pa.reindex (.of _ _ _ u₀ hc₀)
      have left := betaLeg hW L S hΓ hA'' hB₀'' pb'' pa''
      exact ⟨instantiate0 a₃ b₃, Rt hΓ hr left, right⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hcT _ ch, hx, hc, hr, hsz =>
      appBetaCore hW L Rt PA PC S Ac AE AI hΓ hB hTy ca cq cb ca₂ hpq m ih ch hx
        (.trans _ _ _ _ hcT hc) hr (by simp at hsz; omega)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx, hc, hr, _ => by
      subst hx
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hT₀ := L.prop h
      have hlam := (L.typed h).1
      have hlam' : HasTyT E n Γ (.lam A body) (.pi A' B') := hasTyT_of_tyConv hlam hc
      have hpi0 : HasTyT E n Γ (.pi A' B') (.sort .zero) := PA hΓ hlam hlam' hT₀
      have hB'0 : HasTyT E n (.assumption A' :: Γ) B' (.sort .zero) := PC hΓ hpi0
      have harg' : HasTyT E n Γ arg A' := parRedT_hasTy_left L.typed hΓ ha
      have hP : HasTyT E n Γ (instantiate0 arg B') (.sort .zero) := by
        have h0 := hasTyT_subst0S hcl hinst hB'0 harg'
        simpa only [instantiate0, instantiate] using h0
      have hq' : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B') :=
        (Rt hΓ hpq ⟨ParRedT.beta Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂ hred,
          cq⟩).rightTyped L hΓ
      exact ⟨instantiate0 arg' body', CStep.irr L hP hr hq',
        ⟨.refl Γ _ _ hred, .refl (.refl Γ _ _ hred)⟩⟩
  | _, _, _, _, cf@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₀), hx, hc, hr, hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      exact AE hΓ hc hB hTy hr cf cf₀ ca cq cb ca₂ hpq m ih hsz
  | _, _, _, _, cf@(@Certified.iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ cinner), hx, hc, hr, hsz => by
      subst hx
      exact AI hΓ hc hB hTy hr cf cinner ca cq cb ca₂ hpq m ih hsz
  | _, _, _, _, .sortEq .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .consts .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .bvarZeta .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .delta .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .app .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .beta .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .pi .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .letE .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .zeta .., hx, _, _, _ => nomatch hx
  | _, _, _, _, .lit .., hx, _, _, _ => nomatch hx

/-- `OpenRows.app_beta` from the fronts: exactly the field's statement. -/
noncomputable def app_beta_of (hW : EnvWfT E) (L : LeafIface E n PEq) (Rt : Retype E n PEq)
    (PA : PropAlign E n) (PC : PiPropCodom E n) (S : CertSubst0 E n PEq)
    (Ac : CertAssumpCtx E n PEq) (AE : AppBetaEta E n PEq) (AI : AppBetaIota E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A body f' arg a' A' B' T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ (.lam A body) f' T₀} {hc : TyConvT E n Γ T₀ (.pi A' B')}
    {hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w)}
    {ha : ParRedT PEq E n Γ arg a' A'} {hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B')}
    {body' arg' B : Expr Nat} {u v' w' : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)},
    Certified (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
      ha hr) →
    Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
      hred) →
    Certified hf → Certified ha → Certified hb → Certified ha₂ →
    IHBelow E n PEq
      (sizeOf (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
        ha hr) +
       sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
        hred)) →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B) :=
  fun {Γ} hΓ {A body f' arg a' A' B' T₀ v w hf hc hB hTy ha hr body' arg' B u v' w' hA hB₂ hTy₂
      hb ha₂ hred} _ cq cf ca cb ca₂ ih =>
    appBetaCore hW L Rt PA PC S Ac AE AI hΓ hB hTy ca cq cb ca₂
      (parRedT_hasTy_left L.typed hΓ
        (ParRedT.app Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy ha hr))
      _ ih cf rfl hc hr (by simp; omega)

end Rcic.Declarative.NativeValleys
