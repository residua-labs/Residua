import rcic.RcicNativeLeafJoinL

/-!
# RcicNativeIotaDeco — `iotaSpine × iotaSpine` with decorations

The landed ι row (`RcicNativeValleyIota.iotaCore`) joins a certified step out of a
stepped redex with the redex's ι-reduct: ι re-fires at the stepped redex, or the step
went through a leaf and the join is the stepped redex itself.  Its `app` root is the
front `IotaRefireT`.  With decorations three further things are needed, and this module
names them exactly and constructs the row from them.

* `IotaReductTyping`: a typing of the ι-reduct computed from a typing of the redex,
  respecting decorations.  Two re-fired legs then agree at their common reduct whenever
  their redex typings agree (the induction hypothesis' `target`).
* `IotaRefireD`: `IotaRefireT` with the two decoration clauses — the leg's source
  decoration is the supplied reduct typing's, and in the re-fire case its target
  decoration is the reduct typing's.  `IotaLegD` is the output shape; the `stay` case
  carries no target clause (the row adjusts on the star side).
* identity re-decoration at the centre (`identityStepOf_nonliteral`): the stored
  typings of the two input `iotaSpine` nodes and of the induction hypothesis' legs are
  arbitrary, and a single certified step out of a literal cannot change its decoration.
  The row therefore takes the reducts and the induction hypothesis' centre to be
  nonliteral; literal ι-reducts are the named remainder (`iota_iota_literal_remainder`
  states the exact missing object).

`iotaCoreD` is the decorated core: recursion on the certificate of the step out of the
redex (the landed recursion, `conv` peeled, nested `iotaSpine` through the inner step with
`IotaDetU`, the `app` root through `IotaRefireD`), its outputs in `IotaLegD` relative to
the step's computed right typing.  `stepJoinL_iota_iota` is the row: from a one-step
coherent join of the two spines it produces an asymmetric join (`StepJoinL`) of the two
reducts — the stay/stay case re-decorates the centre on the star side, the mixed cases
append the missing ι hop with the other side's typing stored, the re-fire/re-fire case
is one step each by `IotaDetU` and `IotaReductTyping.deco`.  The leaf's decoration law
(`hIrr`) is a parameter, discharged by `rfl` for the canonical leaf
(`ProofLeafAudit.irrDeco`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.IotaDecoAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent StepJoin)
open LeafJoinAudit (StepJoinL)

/-! ### the exact objects -/

/-- A decoration-respecting ι-reduct typing: the reduct's typing is a function of the
    redex's typing (at any index), and two redex typings with one decoration give reduct
    typings with one decoration. -/
structure IotaReductTyping (E : ResolvedEnv) (n : Nat) : Type where
  ty : ∀ {Γ : LCtx} {k j T : Expr Nat}, HasTyT E n Γ k T → DerivedIotaU E k j → HasTyT E n Γ j T
  deco : ∀ {Γ : LCtx} {k j T₁ T₂ : Expr Nat} (hk₁ : HasTyT E n Γ k T₁) (hk₂ : HasTyT E n Γ k T₂)
    (hI₁ hI₂ : DerivedIotaU E k j), decoOf hk₁ = decoOf hk₂ →
    decoOf (ty hk₁ hI₁) = decoOf (ty hk₂ hI₂)

/-- The decorated ι leg out of a reduct `rhs`, relative to a typing `hk` of the stepped
    redex `k`: its source decoration is the supplied reduct typing's; in the re-fire case
    its target decoration is the reduct typing of `hk`. -/
inductive IotaLegD (L : LeafIface E n PEq) (IT : IotaReductTyping E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {rhs k T : Expr Nat} (hrhs : HasTyT E n Γ rhs T)
    (hk : HasTyT E n Γ k T) : Type
  | stay (s : CStep E n PEq Γ rhs k T) (hl : decoOf (s.leftTyped L hΓ) = decoOf hrhs)
  | refire {j : Expr Nat} (hI' : DerivedIotaU E k j) (s : CStep E n PEq Γ rhs j T)
      (hl : decoOf (s.leftTyped L hΓ) = decoOf hrhs)
      (hr : decoOf (s.rightTyped L hΓ) = decoOf (IT.ty hk hI'))

set_option linter.unusedVariables false in
/-- `IotaRefireT` with decorations: the classical ι row at an `app`-congruence root,
    its leg in `IotaLegD` relative to the app node's stored right typing. -/
def IotaRefireD (L : LeafIface E n PEq) (IT : IotaReductTyping E n) : Type :=
  ∀ {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
    {ha : ParRedT PEq E n Γ a a' A} {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
    {rhs : Expr Nat},
    DerivedIotaU E (.app f a) rhs → ConvT E n Γ (.app f a) rhs (instantiate0 a B) →
    Certified (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) →
    Certified hf → Certified ha → (hrhs : HasTyT E n Γ rhs (instantiate0 a B)) →
    IotaLegD L IT hΓ hrhs hr

/-! ### the decorated core -/

/-- Reindexing a leg: both clauses survive (`reindex_left_deco`, `reindex_right_deco`,
    `IotaReductTyping.deco` across the index change). -/
def IotaLegD.reindex (L : LeafIface E n PEq) (IT : IotaReductTyping E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {rhs k A T : Expr Nat} {hrhs : HasTyT E n Γ rhs A}
    {hk : HasTyT E n Γ k A} (hcT : TyConvT E n Γ A T)
    (leg : IotaLegD L IT hΓ hrhs hk) :
    IotaLegD L IT hΓ (hasTyT_of_tyConvT hrhs hcT) (hasTyT_of_tyConvT hk hcT) :=
  match leg with
  | .stay s hl =>
      .stay (s.reindex hcT)
        ((DecoReindexAudit.reindex_left_deco L hΓ s hcT).trans
          (hl.trans (decoOf_hasTyT_of_tyConvT hrhs hcT).symm))
  | .refire hI' s hl hr =>
      .refire hI' (s.reindex hcT)
        ((DecoReindexAudit.reindex_left_deco L hΓ s hcT).trans
          (hl.trans (decoOf_hasTyT_of_tyConvT hrhs hcT).symm))
        ((DecoReindexAudit.reindex_right_deco L hΓ s hcT).trans
          (hr.trans (IT.deco hk _ hI' hI' (decoOf_hasTyT_of_tyConvT hk hcT).symm)))

/-- The decorated ι core: the landed recursion with decorations.  `hnlit` is used only
    at the `refl` root, where the leg is an identity re-decoration of the reduct. -/
def iotaCoreD (hW : EnvWfT E) (L : LeafIface E n PEq) (IT : IotaReductTyping E n)
    (hIrr : ∀ {Γ : LCtx} {p q T : Expr Nat} (hP : HasTyT E n Γ T (.sort .zero))
      (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T),
      decoOf (L.typed (L.ofIrr hP hp hq)).1 = decoOf hp)
    (D : IotaDetU E) (IR : IotaRefireD L IT) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {lhs' rhs : Expr Nat} (hI : DerivedIotaU E lhs' rhs) (hnlit : ∀ t : Nat, rhs ≠ .lit t) :
    {x k T : Expr Nat} → {p : ParRedT PEq E n Γ x k T} → Certified p → x = lhs' →
    ConvT E n Γ lhs' rhs T → (hrhs : HasTyT E n Γ rhs T) →
    IotaLegD L IT hΓ hrhs (parRedT_hasTy_right L.typed hΓ p)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h₀ _, hx, _, hrhs => by
      subst hx
      let r := DecoIdentityAudit.identityStepOf_nonliteral hW L hΓ hrhs (IT.ty h₀ hI) hnlit
      exact .refire hI r.1 r.2.1 r.2.2
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx, _, hrhs => by
      subst hx
      exact .stay (CStep.irr L (L.prop h) hrhs (L.typed h).2) (hIrr (L.prop h) hrhs (L.typed h).2)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ A _ _ hcT _ ch, hx, hc, hrhs =>
      let hrhsA : HasTyT E n Γ rhs A := hasTyT_of_tyConvT hrhs hcT.symmT
      let hcA : ConvT E n Γ lhs' rhs A := convT_of_tyConv hc hcT.symmT
      let leg := (iotaCoreD hW L IT hIrr D IR hΓ hI hnlit ch hx hcA hrhsA).reindex L IT hΓ hcT
      match leg with
      | .stay s hl => .stay s (hl.trans (by simp only [hrhsA, decoOf_hasTyT_of_tyConvT]))
      | .refire hI' s hl hr =>
          .refire hI' s (hl.trans (by simp only [hrhsA, decoOf_hasTyT_of_tyConvT]))
            (hr.trans (IT.deco _ _ hI' hI' (by
              simp only [parRedT_hasTy_right, parRedT_typed, decoOf_hasTyT_of_tyConvT])))
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ m k T _ hI₂ hm hk c₂ cinner, hx, hc, hrhs =>
      match iotaCoreD hW L IT hIrr D IR hΓ hI hnlit cinner hx hc hrhs with
      | .stay s hl =>
          .stay ⟨.iotaSpine Γ rhs m k T s.step hI₂ (s.rightTyped L hΓ) hk,
            .iotaSpine (.trans _ _ _ _ _ s.toConvT
              (.trans _ _ _ _ _ (.symm _ _ _ _ cinner.root) c₂)) s.cert⟩ hl
      | .refire hIj s hl _ => by
          have e := D hIj hI₂
          subst e
          exact .stay s hl
  | _, _, _, _, cq@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf ca), hx, hc,
      hrhs => by
      subst hx
      exact IR hΓ hI hc cq cf ca hrhs
  | _, _, _, _, .sortEq .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .consts .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .bvarZeta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .delta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .beta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp only [recCall, foldApps_snoc, Expr.app.injEq] at hx
      exact (F8EtaK.foldApps_const_ne_lam_any hx.1.symm).elim
  | _, _, _, _, .lam .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .pi .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .letE .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .zeta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .lit .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .eta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx

/-! ### the row -/

/-- `iotaSpine × iotaSpine` as an asymmetric coherent join, from a one-step coherent join
    of the two spines.  Nonliterality of the two reducts (identity re-decoration at the
    `refl` roots of the core) and of the spines' join centre (stay/stay) is assumed. -/
def stepJoinL_iota_iota (hW : EnvWfT E) (L : LeafIface E n PEq) (IT : IotaReductTyping E n)
    (hIrr : ∀ {Γ : LCtx} {p q T : Expr Nat} (hP : HasTyT E n Γ T (.sort .zero))
      (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T),
      decoOf (L.typed (L.ofIrr hP hp hq)).1 = decoOf hp)
    (D : IotaDetU E) (IR : IotaRefireD L IT) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {lhs m₁ m₂ r₁ r₂ T : Expr Nat}
    {hstep₁ : ParRedT PEq E n Γ lhs m₁ T} (hI₁ : DerivedIotaU E m₁ r₁)
    (hm₁ : HasTyT E n Γ m₁ T) (hr₁ : HasTyT E n Γ r₁ T) (c₁ : ConvT E n Γ lhs r₁ T)
    (cs₁ : Certified hstep₁)
    {hstep₂ : ParRedT PEq E n Γ lhs m₂ T} (hI₂ : DerivedIotaU E m₂ r₂)
    (hm₂ : HasTyT E n Γ m₂ T) (hr₂ : HasTyT E n Γ r₂ T) (c₂ : ConvT E n Γ lhs r₂ T)
    (cs₂ : Certified hstep₂)
    (hnlit₁ : ∀ t : Nat, r₁ ≠ .lit t) (hnlit₂ : ∀ t : Nat, r₂ ≠ .lit t)
    (ih : StepJoin L hΓ ⟨hstep₁, cs₁⟩ ⟨hstep₂, cs₂⟩)
    (hnlitk : ∀ t : Nat, ih.centre ≠ .lit t) :
    StepJoinL L hΓ ⟨.iotaSpine Γ lhs m₁ r₁ T hstep₁ hI₁ hm₁ hr₁, .iotaSpine c₁ cs₁⟩
      ⟨.iotaSpine Γ lhs m₂ r₂ T hstep₂ hI₂ hm₂ hr₂, .iotaSpine c₂ cs₂⟩ :=
  let k := ih.centre
  let l₁ : CStep E n PEq Γ m₁ k T := ih.left
  let l₂ : CStep E n PEq Γ m₂ k T := ih.right
  let cm₁ : ConvT E n Γ m₁ r₁ T := .trans _ _ _ _ _ (.symm _ _ _ _ cs₁.root) c₁
  let cm₂ : ConvT E n Γ m₂ r₂ T := .trans _ _ _ _ _ (.symm _ _ _ _ cs₂.root) c₂
  let leg₁ := iotaCoreD hW L IT hIrr D IR hΓ hI₁ hnlit₁ l₁.cert rfl cm₁ hr₁
  let leg₂ := iotaCoreD hW L IT hIrr D IR hΓ hI₂ hnlit₂ l₂.cert rfl cm₂ hr₂
  match leg₁, leg₂ with
  | .stay s₁ hl₁, .stay s₂ hl₂ =>
      let id := DecoIdentityAudit.identityStepOf_nonliteral hW L hΓ (s₁.rightTyped L hΓ)
        (s₂.rightTyped L hΓ) hnlitk
      { centre := k
        left := .tail s₁ (.tail id.1 (.refl Γ k T (s₂.rightTyped L hΓ)))
        right := s₂
        leftCoherent := ⟨id.2.1.symm, id.2.2, True.intro⟩
        leftSource := hl₁
        rightSource := hl₂
        target := by simp only [CStar.rightTyped] }
  | .stay s₁ hl₁, .refire hI₂' s₂ hl₂ _ =>
      let hk₁ : HasTyT E n Γ k T := s₁.rightTyped L hΓ
      let ckj : ConvT E n Γ k _ T :=
        .trans _ _ _ _ _ (.symm _ _ _ _ l₂.toConvT) (.trans _ _ _ _ _ cm₂ s₂.toConvT)
      let hop : CStep E n PEq Γ k _ T :=
        ⟨.iotaSpine Γ k k _ T (.refl Γ k T hk₁) hI₂' hk₁ (s₂.rightTyped L hΓ),
          .iotaSpine ckj (.refl (.refl Γ k T hk₁))⟩
      { centre := _
        left := .tail s₁ (.tail hop (.refl Γ _ T (s₂.rightTyped L hΓ)))
        right := s₂
        leftCoherent := ⟨rfl, rfl, True.intro⟩
        leftSource := hl₁
        rightSource := hl₂
        target := by simp only [CStar.rightTyped] }
  | .refire hI₁' s₁ hl₁ _, .stay s₂ hl₂ =>
      let crj : ConvT E n Γ r₂ _ T :=
        .trans _ _ _ _ _ s₂.toConvT
          (.trans _ _ _ _ _ (.symm _ _ _ _ l₁.toConvT) (.trans _ _ _ _ _ cm₁ s₁.toConvT))
      { centre := _
        left := .tail s₁ (.refl Γ _ T (s₁.rightTyped L hΓ))
        right := ⟨.iotaSpine Γ r₂ k _ T s₂.step hI₁' (s₂.rightTyped L hΓ) (s₁.rightTyped L hΓ),
          .iotaSpine crj s₂.cert⟩
        leftCoherent := ⟨rfl, True.intro⟩
        leftSource := hl₁
        rightSource := hl₂
        target := by
          simp only [CStar.rightTyped, CStep.rightTyped, parRedT_hasTy_right, parRedT_typed] }
  | .refire hI₁' s₁ hl₁ hr₁', .refire hI₂' s₂ hl₂ hr₂' => by
      have e := D hI₁' hI₂'
      subst e
      exact
        { centre := _
          left := .tail s₁ (.refl Γ _ T (s₁.rightTyped L hΓ))
          right := s₂
          leftCoherent := ⟨rfl, True.intro⟩
          leftSource := hl₁
          rightSource := hl₂
          target := by
            simp only [CStar.rightTyped]
            exact hr₁'.trans ((IT.deco _ _ hI₁' hI₂' ih.target).trans hr₂'.symm) }

/-- The exact missing object at a literal centre: a single certified step out of a
    literal with prescribed, distinct endpoint decorations.  (Its absence is the
    literal-rigidity of `expansionStepOf_typing`: every certified step out of `.lit t`
    is `refl`, `lit`, `peq`, or an index conversion of one, and the first two tie the
    target decoration to the source.) -/
def LiteralRedecoration (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t : Nat} {T : Expr Nat}
    (h₁ h₂ : HasTyT E n Γ (.lit t) T),
    Σ' (s : CStep E n PEq Γ (.lit t) (.lit t) T),
      decoOf (s.leftTyped L hΓ) = decoOf h₁ ∧ decoOf (s.rightTyped L hΓ) = decoOf h₂

/-- With literal re-decoration supplied, the nonliterality premises of the core and the
    row are discharged: an identity step with prescribed endpoint decorations exists at
    every term. -/
def identityStepOf_literalRedecoration (hW : EnvWfT E) (L : LeafIface E n PEq)
    (LR : LiteralRedecoration E n PEq L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (h₁ h₂ : HasTyT E n Γ e T) :
    Σ' (s : CStep E n PEq Γ e e T),
      decoOf (s.leftTyped L hΓ) = decoOf h₁ ∧ decoOf (s.rightTyped L hΓ) = decoOf h₂ := by
  cases e
  all_goals first
    | exact LR hΓ h₁ h₂
    | exact DecoIdentityAudit.identityStepOf_nonliteral hW L hΓ h₁ h₂ (by intro t heq; cases heq)

#print axioms IotaReductTyping
#print axioms IotaLegD
#print axioms IotaRefireD
#print axioms IotaLegD.reindex
#print axioms iotaCoreD
#print axioms stepJoinL_iota_iota
#print axioms LiteralRedecoration
#print axioms identityStepOf_literalRedecoration

end Rcic.Declarative.NativeValleys.IotaDecoAudit
