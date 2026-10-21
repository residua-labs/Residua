import rcic.RcicNativeProofLeaf
import rcic.RcicNativeDecoLeaf
import rcic.RcicNativeValleyDecoRows

/-!
# RcicNativeLeafJoinL — the proof-leaf rows of `CoherentDiamond`, and the asymmetric join

Which rows of `DecoStarAudit.CoherentDiamond` involve the irrelevance leaf, and in what
shape can they be joined?

* **Every `Prop`-indexed peak is a one-step `StepJoin`** under the canonical leaf
  (`stepJoin_of_propIndex`): the leaf absorbs both reducts, and because
  `proofLeafIface.typed` returns the stored typings verbatim, all three decoration
  equalities hold by `rfl`.  The `peq × q` and `p × peq` rows are instances
  (`stepJoin_peq_left`, `stepJoin_peq_right`); they need no source-decoration
  hypothesis.  So the leaf-at-the-root rows of `CoherentDiamond` are closed.

* **The leaf inside an η-redex body** (`RcicNativeValleyEtaLeaf`'s peak, `lam × eta`) is
  the other leaf row.  Strip consumes a join as `D hΓ p q` with `p` the step being
  stripped and `q` the head of the star, and recurses on the star's tail with the
  joining leg out of `q`'s reduct; that leg must therefore be ONE step, while the leg out
  of `p`'s reduct may be a star.  `StepJoinL` is exactly that shape (left star, right
  step, the three equalities), and `stripOfL` / `confluenceOfL` consume it with the
  same recursions as `stripOf` / `confluenceOf` (the original star's tail; the generated
  leg in the other argument).  Every `StepJoin` is a `StepJoinL`.

  The η/leaf peak satisfies `StepJoinL` in the orientation `(lam-leaf, eta)`
  (`etaLeaf_stepJoinL`, for every leaf interface: the published two-step repair
  `etaLeaf_valleyJoin` with the three equalities checked), and REFUTES it in the
  orientation `(eta, lam-leaf)` (`coherentDiamondL_false_of_notProof`): a single
  certified step out of the stepped λ lands on a λ, while every certified star out of
  `x p` stays an application of `x`.  Since strip meets both orientations, no
  strip-consumable variant of `StepJoin` admits the η/leaf row.  The `NotProof` premises
  are those of `etaLeaf_no_join`, with the application premise strengthened to every
  argument (the star passes through `x a'` for arbitrary proofs `a'`).

* `cdiamondD_false_of_notProof`: #7588's source-only `CDiamondD` is refuted on the same
  peak for every leaf interface (the two steps share their source decoration,
  `peak_source_deco_eq`), as `CoherentDiamond` already was.

* `LeafAdjJoin` names the shape the η/leaf peak satisfies in BOTH orientations
  (`etaLeaf_leafAdjJoin`, `etaLeaf_leafAdjJoin_symm`): each reduct first moves along a
  star of pure irrelevance steps (`PureLeaf`), then takes one certified step.  Its
  consumer is not strip (the adjustment is not a step out of the star's reduct); it is
  the square completion for the relation "leaf-adjust, then step", which needs the
  diamond on leaf-equivalent sources — stated here as the exact remaining object, not
  constructed.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.LeafJoinAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent StepJoin StripJoin StarJoin)

/-! ### the asymmetric join and its consumer -/

/-- A join with a coherent star on the stripped step's side and one certified step on the
    star's side; the three decoration equalities of `StepJoin`. -/
structure StepJoinL (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T) where
  centre : Expr Nat
  left : CStar E n PEq Γ d centre T
  right : CStep E n PEq Γ e centre T
  leftCoherent : Coherent L hΓ left
  leftSource : decoOf (left.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (right.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ)
  target : decoOf left.rightTyped = decoOf (right.rightTyped L hΓ)

/-- Every one-step coherent join is an asymmetric one. -/
def StepJoinL.ofStepJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} {p : CStep E n PEq Γ b d T} {q : CStep E n PEq Γ b e T}
    (j : StepJoin L hΓ p q) : StepJoinL L hΓ p q :=
  { centre := j.centre
    left := CStar.ofStep L hΓ j.left
    right := j.right
    leftCoherent := ⟨rfl, True.intro⟩
    leftSource := j.leftSource
    rightSource := j.rightSource
    target := by simpa only [CStar.ofStep, CStar.rightTyped] using j.target }

/-- The asymmetric coherent diamond: the weakest join shape strip consumes. -/
def CoherentDiamondL (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
      decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ) → StepJoinL L hΓ p q

/-- `CoherentDiamond` gives `CoherentDiamondL`. -/
def coherentDiamondL_of_coherentDiamond (L : LeafIface E n PEq)
    (D : DecoStarAudit.CoherentDiamond L) : CoherentDiamondL L :=
  fun {_} hΓ {_ _ _ _} p q hd => StepJoinL.ofStepJoin L hΓ (D hΓ p q hd)

/-- Strip from the asymmetric diamond.  The recursive call is on the original star's
    tail `qs`; the generated single step `j.right` is the other argument.  The joining
    star `j.left` is concatenated in front of the recursive left star by
    `coherent_trans`, whose interface hypothesis is `j.target` against the recursive
    `leftSource`. -/
def stripOfL (L : LeafIface E n PEq) (D : CoherentDiamondL L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d T : Expr Nat}
    (p : CStep E n PEq Γ b d T) :
    {e : Expr Nat} → (s : CStar E n PEq Γ b e T) → Coherent L hΓ s →
      decoOf (p.leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) →
      StripJoin L hΓ p s
  | _, .refl _ _ _ _, _, hsource =>
      { centre := d
        left := .refl Γ d T (p.rightTyped L hΓ)
        right := p
        leftCoherent := True.intro
        leftSource := rfl
        rightSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource
        target := by simp only [CStar.rightTyped] }
  | _, .tail q qs, hcoh, hsource => by
      let j := D hΓ p q hsource
      have hnext : decoOf (j.right.leftTyped L hΓ) = decoOf (qs.leftTyped L hΓ) :=
        j.rightSource.trans hcoh.1
      let r := stripOfL L D hΓ j.right qs hcoh.2 hnext
      have hmid : decoOf j.left.rightTyped = decoOf (r.left.leftTyped L hΓ) :=
        j.target.trans r.leftSource.symm
      have joined := StepTransferRowsAudit.coherent_trans L hΓ j.left r.left
        j.leftCoherent r.leftCoherent hmid
      exact
        { centre := r.centre
          left := j.left.trans r.left
          right := r.right
          leftCoherent := joined.1
          leftSource := joined.2.1.trans j.leftSource
          rightSource := by simpa only [CStar.rightTyped] using r.rightSource
          target := by
            rw [joined.2.2]
            simpa only [CStar.rightTyped] using r.target }

/-- Confluence from the asymmetric diamond: the recursion of `confluenceOf` verbatim,
    strip replaced by `stripOfL`. -/
def confluenceOfL (L : LeafIface E n PEq) (D : CoherentDiamondL L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d T : Expr Nat} :
    (s : CStar E n PEq Γ b d T) → {e : Expr Nat} →
      (t : CStar E n PEq Γ b e T) → Coherent L hΓ s → Coherent L hΓ t →
      decoOf (s.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ) →
      StarJoin L hΓ s t
  | .refl _ _ _ _, e, t, _, ht, hsource =>
      { centre := e
        left := t
        right := .refl Γ e T t.rightTyped
        leftCoherent := ht
        rightCoherent := True.intro
        leftSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource.symm
        rightSource := rfl
        target := by simp only [CStar.rightTyped] }
  | .tail p ps, _, t, hs, ht, hsource => by
      let j := stripOfL L D hΓ p t ht hsource
      have hnext : decoOf (ps.leftTyped L hΓ) = decoOf (j.left.leftTyped L hΓ) :=
        hs.1.symm.trans j.leftSource.symm
      let r := confluenceOfL L D hΓ ps j.left hs.2 j.leftCoherent hnext
      exact
        { centre := r.centre
          left := r.left
          right := .tail j.right r.right
          leftCoherent := r.leftCoherent
          rightCoherent := ⟨j.target.symm.trans r.rightSource.symm, r.rightCoherent⟩
          leftSource := by simpa only [CStar.rightTyped] using r.leftSource
          rightSource := j.rightSource
          target := by simpa only [CStar.rightTyped] using r.target }

/-! ### the leaf-at-the-root rows under the canonical leaf -/

/-- At a `Prop`-sorted index every peak joins in one leaf step on the left and the
    reflexive step on the right; the equalities are definitional because the canonical
    leaf stores the typings verbatim.  No source-decoration hypothesis is used. -/
def stepJoin_of_propIndex {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero))
    (p : CStep E n (ProofLeaf E n) Γ b d T) (q : CStep E n (ProofLeaf E n) Γ b e T) :
    StepJoin (proofLeafIface E n) hΓ p q :=
  let L := proofLeafIface E n
  { centre := e
    left := CStep.irr L hT (p.rightTyped L hΓ) (q.rightTyped L hΓ)
    right := ⟨.refl Γ e T (q.rightTyped L hΓ), .refl (.refl Γ e T (q.rightTyped L hΓ))⟩
    leftSource := rfl
    rightSource := rfl
    target := rfl }

/-- `CoherentDiamond` restricted to `Prop`-sorted indices, under the canonical leaf. -/
def coherentDiamond_propIndex {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero))
    (p : CStep E n (ProofLeaf E n) Γ b d T) (q : CStep E n (ProofLeaf E n) Γ b e T)
    (_ : decoOf (p.leftTyped (proofLeafIface E n) hΓ) = decoOf (q.leftTyped (proofLeafIface E n) hΓ)) :
    StepJoin (proofLeafIface E n) hΓ p q :=
  stepJoin_of_propIndex hΓ hT p q

/-- The `peq × q` row: the leaf's own `Prop` sorting is the index's. -/
def stepJoin_peq_left {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (hl : ProofLeaf E n Γ b d T) (c : ConvT E n Γ b d T)
    (q : CStep E n (ProofLeaf E n) Γ b e T) :
    StepJoin (proofLeafIface E n) hΓ ⟨.peq Γ b d T hl, .peq c⟩ q :=
  stepJoin_of_propIndex hΓ hl.hT _ q

/-- The `p × peq` row. -/
def stepJoin_peq_right {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (p : CStep E n (ProofLeaf E n) Γ b d T)
    (hl : ProofLeaf E n Γ b e T) (c : ConvT E n Γ b e T) :
    StepJoin (proofLeafIface E n) hΓ p ⟨.peq Γ b e T hl, .peq c⟩ :=
  stepJoin_of_propIndex hΓ hl.hT p _

/-! ### the η/leaf peak: the asymmetric join holds in one orientation -/

/-- The reverse leaf under the binder: the bound variable back to the lifted `p`
    (the first step of the published repair `etaLeaf_valleyJoin`, whose pieces are
    `let`-bound there and not addressable; the typings are the fixture's). -/
def etaLeafRevLeaf (L : LeafIface E n PEq) : PEq etaLeafCtx₁ (.bvar 0) (.bvar 1) etaLeafP :=
  L.ofIrr (etaLeafP_ty _) etaLeafY_var₁ etaLeafP_var₁

/-- Its certificate. -/
def etaLeafRevLeafConv : ConvT E n etaLeafCtx₁ (.bvar 0) (.bvar 1) etaLeafP :=
  .irr _ etaLeafP (.bvar 0) (.bvar 1) (etaLeafP_ty _) etaLeafY_var₁ etaLeafP_var₁

/-- `x y ⇒ lift f = x p` under the binder. -/
def etaLeafRevInnerStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx₁ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF)
      (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 2) (.bvar 0) (.bvar 1) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX
    (.imax .zero (.succ .zero)) (.imax .zero (.succ .zero))
    (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) (.refl _ _) (etaLeafPiP_ty _) (etaLeafPiP_ty _)
    (.peq _ (.bvar 0) (.bvar 1) etaLeafP (etaLeafRevLeaf L)) etaLeafLiftF_ty

/-- Its certificate. -/
def etaLeafRevInnerConv :
    ConvT E n etaLeafCtx₁ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF)
      (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 2) (.bvar 0) (.bvar 1) etaLeafP (.pi etaLeafP (.sort .zero))
    (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) etaLeafRevLeafConv

/-- The inner reverse step is certified. -/
def etaLeafRevInnerCert (L : LeafIface E n PEq) : Certified (etaLeafRevInnerStep L) :=
  .app etaLeafRevInnerConv (.refl (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁))
    (.peq etaLeafRevLeafConv)

/-- The body `(x y) y ⇒ (x p) y` under the binder. -/
def etaLeafRevBodyStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx₁ etaLeafBody' etaLeafBody (.sort .zero) :=
  .app _ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
    (.pi etaLeafP (.sort .zero)) (.succ .zero) (.succ .zero)
    (etaLeafRevInnerStep L) (.refl _ _) (.sort _ _) (.sort _ _)
    (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁) etaLeafBody_ty

/-- Its certificate. -/
def etaLeafRevBodyConv : ConvT E n etaLeafCtx₁ etaLeafBody' etaLeafBody (.sort .zero) :=
  .app _ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
    etaLeafRevInnerConv (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁)

/-- The reverse body step is certified. -/
def etaLeafRevBodyCert (L : LeafIface E n PEq) : Certified (etaLeafRevBodyStep L) :=
  .app etaLeafRevBodyConv (etaLeafRevInnerCert L)
    (.refl (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁))

/-- The reverse λ step `d ⇒ b` at `P → Prop`. -/
def etaLeafRevLamStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx (.lam etaLeafP etaLeafBody') (.lam etaLeafP etaLeafBody)
      (.pi etaLeafP (.sort .zero)) :=
  .lam _ etaLeafP etaLeafP etaLeafBody' etaLeafBody (.sort .zero) .zero (.succ .zero)
    (.refl _ etaLeafP _ (etaLeafP_ty _)) (etaLeafP_ty _) (.sort _ _) (etaLeafRevBodyStep L)
    etaLeafB_ty

/-- The reverse λ step is certified. -/
def etaLeafRevLamCert (L : LeafIface E n PEq) : Certified (etaLeafRevLamStep L) :=
  .lam (.lam _ etaLeafP etaLeafP etaLeafBody' etaLeafBody (.sort .zero) .zero
    (.refl _ etaLeafP _ (etaLeafP_ty _)) etaLeafRevBodyConv) (etaLeafRevBodyCert L)

/-- The reverse λ step as a certified step. -/
def etaLeafRevStep (L : LeafIface E n PEq) :
    CStep E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody') (.lam etaLeafP etaLeafBody)
      (.pi etaLeafP (.sort .zero)) :=
  ⟨etaLeafRevLamStep L, etaLeafRevLamCert L⟩

/-- The η step as a certified step. -/
def etaLeafEtaCStep :
    CStep E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody) etaLeafF (.pi etaLeafP (.sort .zero)) :=
  ⟨etaLeafEtaStep, etaLeafEtaCert⟩

/-- The reflexive step at `f`. -/
def etaLeafFRefl : CStep E n PEq etaLeafCtx etaLeafF etaLeafF (.pi etaLeafP (.sort .zero)) :=
  ⟨.refl etaLeafCtx etaLeafF _ etaLeafF_ty, .refl (.refl etaLeafCtx etaLeafF _ etaLeafF_ty)⟩

/-- The two-step repair with the three equalities: the reverse leaf restores the lifted
    term, η contracts it, the η side is reflexive.  The only non-definitional interface is
    the leaf's typing of the bound variable, whose decoration is forced. -/
def etaLeaf_stepJoinL (L : LeafIface E n PEq) :
    StepJoinL L etaLeafCtx_wf ⟨etaLeafLamStep L, etaLeafLamCert L⟩
      ⟨etaLeafEtaStep, etaLeafEtaCert⟩ where
  centre := etaLeafF
  left := .tail (etaLeafRevStep L) (.tail etaLeafEtaCStep (.refl etaLeafCtx etaLeafF _ etaLeafF_ty))
  right := etaLeafFRefl
  leftCoherent := by
    simp only [Coherent, etaLeafRevStep, etaLeafEtaCStep, CStep.rightTyped, CStep.leftTyped,
      CStar.leftTyped, parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed,
      etaLeafRevLamStep, etaLeafEtaStep, and_self]
  leftSource := by
    simp only [etaLeafRevStep, CStep.rightTyped, CStep.leftTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed, hasTyT_of_tyConvT,
      etaLeafRevLamStep, etaLeafRevBodyStep, etaLeafRevInnerStep, etaLeafLamStep,
      etaLeafBodyStep, etaLeafInnerStep, etaLeafD_ty, etaLeafBody'_ty, etaLeafXY_ty,
      etaLeafX_var₁, etaLeafY_var₁, decoOf,
      deco_subsingleton_bvar rfl (decoOf (L.typed (etaLeafRevLeaf L)).1) (.bvar 0)]
  rightSource := by
    simp only [etaLeafFRefl, CStep.rightTyped, CStep.leftTyped, parRedT_hasTy_right,
      parRedT_hasTy_left, parRedT_typed, etaLeafEtaStep]
  target := by
    simp only [etaLeafFRefl, CStar.rightTyped, CStep.rightTyped, parRedT_hasTy_right,
      parRedT_typed]

/-! ### the η/leaf peak: the asymmetric join fails in the other orientation -/

/-- `appVarStep_target` for an arbitrary argument: a certified step out of `app (bvar i) a`
    — `bvar i` an assumption variable that is not a proof, the application not a proof —
    lands on an application of `bvar i`. -/
theorem appVarStep_target' (L : LeafIface E n PEq) {Γ : LCtx} {i : Nat} {X : Expr Nat}
    (hget : Γ.get? i = some (.assumption X)) (hnpx : NotProof E n Γ (.bvar i))
    (hnpf : ∀ a : Expr Nat, NotProof E n Γ (.app (.bvar i) a)) :
    {x j T : Expr Nat} → {p : ParRedT PEq E n Γ x j T} → Certified p →
    (a : Expr Nat) → x = .app (.bvar i) a → ∃ a' : Expr Nat, j = .app (.bvar i) a'
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, a, hx => by subst hx; exact ⟨a, rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, a, hx =>
      appVarStep_target' L hget hnpx hnpf ch a hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, a, hx => by
      subst hx; exact (hnpf a (L.typed h).1 (L.prop h)).elim
  | _, _, _, _, @Certified.app _ _ _ _ _ _ _ a' _ _ _ _ _ _ _ _ _ _ _ _ cf _, _, hx => by
      injection hx with h1 _
      have e := bvarStep_target L hget hnpx cf h1
      subst e
      exact ⟨a', rfl⟩
  | _, _, _, _, @Certified.beta .., _, hx => by
      injection hx with h1 _
      exact nomatch h1
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, a, hx => by
      obtain ⟨a', e⟩ := appVarStep_target' L hget hnpx hnpf cs a hx
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
      have hs := F8EtaK.appsSpine_fst_of_eq_foldApps_const hl.1
      simp [appsSpine] at hs
  | _, _, _, _, .sortEq .., _, hx => nomatch hx
  | _, _, _, _, .consts .., _, hx => nomatch hx
  | _, _, _, _, .bvarZeta .., _, hx => nomatch hx
  | _, _, _, _, .delta .., _, hx => nomatch hx
  | _, _, _, _, .lam .., _, hx => nomatch hx
  | _, _, _, _, .pi .., _, hx => nomatch hx
  | _, _, _, _, .letE .., _, hx => nomatch hx
  | _, _, _, _, .zeta .., _, hx => nomatch hx
  | _, _, _, _, .lit .., _, hx => nomatch hx
  | _, _, _, _, .eta .., _, hx => nomatch hx

/-- Along a certified star the shape `app (bvar i) _` is kept. -/
theorem appVarStar_target (L : LeafIface E n PEq) {Γ : LCtx} {i : Nat} {X : Expr Nat}
    (hget : Γ.get? i = some (.assumption X)) (hnpx : NotProof E n Γ (.bvar i))
    (hnpf : ∀ a : Expr Nat, NotProof E n Γ (.app (.bvar i) a)) :
    {x c T : Expr Nat} → CStar E n PEq Γ x c T →
    (a : Expr Nat) → x = .app (.bvar i) a → ∃ a' : Expr Nat, c = .app (.bvar i) a'
  | _, _, _, .refl _ _ _ _, a, hx => ⟨a, hx⟩
  | _, _, _, .tail s ss, a, hx => by
      obtain ⟨a', h'⟩ := appVarStep_target' L hget hnpx hnpf s.cert a hx
      exact appVarStar_target L hget hnpx hnpf ss a' h'

/-- In the orientation `(eta, lam-leaf)` the asymmetric join does not exist: the single
    step out of the stepped λ lands on a λ, the star out of `x p` on an application of
    `x`.  Hence `CoherentDiamondL` is refuted under the `NotProof` premises. -/
theorem coherentDiamondL_false_of_notProof (L : LeafIface E n PEq)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (hnpf : ∀ a : Expr Nat, NotProof E n etaLeafCtx (.app (.bvar 1) a))
    (D : CoherentDiamondL L) : False := by
  let j := D etaLeafCtx_wf ⟨etaLeafEtaStep, etaLeafEtaCert⟩
    ⟨etaLeafLamStep L, etaLeafLamCert L⟩ (DecoLeafAudit.peak_source_deco_eq L).symm
  obtain ⟨A', b', e₁⟩ := lamStep_target L etaLeafBody'_not_eta hnpd j.right.cert rfl
  obtain ⟨a', e₂⟩ := appVarStar_target (Γ := etaLeafCtx) (i := 1) (X := etaLeafX) L rfl hnpx hnpf
    j.left (.bvar 0) rfl
  rw [e₁] at e₂
  exact nomatch e₂

/-- #7588's source-only decorated diamond is refuted on the same peak, for every leaf
    interface: the two steps share their source decoration. -/
theorem cdiamondD_false_of_notProof (L : LeafIface E n PEq)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF) (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (D : CDiamondD E n PEq L) : False := by
  have hd : stepDeco L (etaLeafLamStep L) =
      stepDeco L (etaLeafEtaStep (PEq := PEq) (E := E) (n := n)) := by
    rw [← decoOf_parRedT_hasTy_left L etaLeafCtx_wf, ← decoOf_parRedT_hasTy_left L etaLeafCtx_wf]
    exact DecoLeafAudit.peak_source_deco_eq L
  exact etaLeaf_no_join L hnpd hnpf hnpx
    (D etaLeafCtx_wf ⟨etaLeafLamStep L, etaLeafLamCert L⟩ ⟨etaLeafEtaStep, etaLeafEtaCert⟩ hd)

/-! ### the shape the η/leaf peak satisfies in both orientations -/

/-- A pure irrelevance step: every leaf of the derivation is `refl` or `peq`, under
    congruence and index conversion only. -/
inductive PureLeaf : {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Prop
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A} : PureLeaf (.refl Γ a A h)
  | peq {Γ : LCtx} {p q T : Expr Nat} {h : PEq Γ p q T} : PureLeaf (.peq Γ p q T h)
  | app {Γ : LCtx} {f f' a a' A B T₀ : Expr Nat} {v w : Level}
      {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
      {ha : ParRedT PEq E n Γ a a' A}
      {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
      (pf : PureLeaf hf) (pa : PureLeaf ha) :
      PureLeaf (.app Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr)
  | lam {Γ : LCtx} {A A' body body' B : Expr Nat} {u v : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.lam A' body') (.pi A B)}
      (pb : PureLeaf hb) : PureLeaf (.lam Γ A A' body body' B u v hc hA hB hb hrt)
  | letE {Γ : LCtx} {A A' value value' body body' B : Expr Nat} {u w : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hv : ParRedT PEq E n Γ value value' A}
      {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
      {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
      {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)}
      (pv : PureLeaf hv) (pb : PureLeaf hb) :
      PureLeaf (.letE Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt)
  | conv {Γ : LCtx} {a b A A' : Expr Nat} {h : ParRedT PEq E n Γ a b A}
      {hc : TyConvT E n Γ A A'} (ph : PureLeaf h) : PureLeaf (.conv Γ a b A A' h hc)

/-- A star of pure irrelevance steps. -/
inductive LeafStar : {Γ : LCtx} → {a b T : Expr Nat} → CStar E n PEq Γ a b T → Prop
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A} : LeafStar (.refl Γ a A h)
  | tail {Γ : LCtx} {a b c A : Expr Nat} {s : CStep E n PEq Γ a b A}
      {ss : CStar E n PEq Γ b c A} (hs : PureLeaf s.step) (ht : LeafStar ss) :
      LeafStar (.tail s ss)

/-- A join after leaf adjustment: each reduct moves along a coherent star of pure
    irrelevance steps, then takes one certified step; the three equalities as in
    `StepJoin`, read at the adjusted sources.  This is the exact shape the η/leaf peak
    satisfies in both orientations.  Its consumer is not strip. -/
structure LeafAdjJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T) where
  centre : Expr Nat
  dAdj : Expr Nat
  eAdj : Expr Nat
  leftAdj : CStar E n PEq Γ d dAdj T
  rightAdj : CStar E n PEq Γ e eAdj T
  leftAdjLeaf : LeafStar leftAdj
  rightAdjLeaf : LeafStar rightAdj
  leftAdjCoherent : Coherent L hΓ leftAdj
  rightAdjCoherent : Coherent L hΓ rightAdj
  left : CStep E n PEq Γ dAdj centre T
  right : CStep E n PEq Γ eAdj centre T
  leftSource : decoOf (leftAdj.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (rightAdj.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ)
  leftAdjInterface : decoOf leftAdj.rightTyped = decoOf (left.leftTyped L hΓ)
  rightAdjInterface : decoOf rightAdj.rightTyped = decoOf (right.leftTyped L hΓ)
  target : decoOf (left.rightTyped L hΓ) = decoOf (right.rightTyped L hΓ)

/-- The leaf-adjusted coherent diamond: the exact remaining statement for the η/leaf row. -/
def CoherentDiamondAdj (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
      decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ) → LeafAdjJoin L hΓ p q

/-- The reverse λ step is a pure irrelevance step. -/
theorem etaLeafRevLamStep_pureLeaf (L : LeafIface E n PEq) : PureLeaf (etaLeafRevLamStep L) :=
  .lam (.app (.app .refl .peq) .refl)

/-- The η/leaf peak in the orientation `(lam-leaf, eta)`: the λ side adjusts by the
    reverse leaf and contracts by η, the η side is unadjusted and reflexive. -/
def etaLeaf_leafAdjJoin (L : LeafIface E n PEq) :
    LeafAdjJoin L etaLeafCtx_wf ⟨etaLeafLamStep L, etaLeafLamCert L⟩
      ⟨etaLeafEtaStep, etaLeafEtaCert⟩ where
  centre := etaLeafF
  dAdj := .lam etaLeafP etaLeafBody
  eAdj := etaLeafF
  leftAdj := .tail (etaLeafRevStep L) (.refl etaLeafCtx _ _ etaLeafB_ty)
  rightAdj := .refl etaLeafCtx etaLeafF _ etaLeafF_ty
  leftAdjLeaf := .tail (etaLeafRevLamStep_pureLeaf L) .refl
  rightAdjLeaf := .refl
  leftAdjCoherent := by
    simp only [Coherent, etaLeafRevStep, CStep.rightTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_typed, etaLeafRevLamStep, and_self]
  rightAdjCoherent := True.intro
  left := etaLeafEtaCStep
  right := etaLeafFRefl
  leftSource := by
    simp only [etaLeafRevStep, CStep.rightTyped, CStep.leftTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed, hasTyT_of_tyConvT,
      etaLeafRevLamStep, etaLeafRevBodyStep, etaLeafRevInnerStep, etaLeafLamStep,
      etaLeafBodyStep, etaLeafInnerStep, etaLeafD_ty, etaLeafBody'_ty, etaLeafXY_ty,
      etaLeafX_var₁, etaLeafY_var₁, decoOf,
      deco_subsingleton_bvar rfl (decoOf (L.typed (etaLeafRevLeaf L)).1) (.bvar 0)]
  rightSource := by
    simp only [etaLeafFRefl, CStep.rightTyped, CStep.leftTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed, etaLeafEtaStep]
  leftAdjInterface := by
    simp only [etaLeafEtaCStep, CStar.rightTyped, CStep.leftTyped, parRedT_hasTy_left,
      parRedT_typed, etaLeafEtaStep]
  rightAdjInterface := by
    simp only [etaLeafFRefl, CStar.rightTyped, CStep.leftTyped, parRedT_hasTy_left,
      parRedT_typed]
  target := by
    simp only [etaLeafEtaCStep, etaLeafFRefl, CStep.rightTyped, parRedT_hasTy_right,
      parRedT_typed, etaLeafEtaStep]

/-- The η/leaf peak in the orientation `(eta, lam-leaf)`: the same data mirrored. -/
def etaLeaf_leafAdjJoin_symm (L : LeafIface E n PEq) :
    LeafAdjJoin L etaLeafCtx_wf ⟨etaLeafEtaStep, etaLeafEtaCert⟩
      ⟨etaLeafLamStep L, etaLeafLamCert L⟩ :=
  let j := etaLeaf_leafAdjJoin L
  { centre := j.centre
    dAdj := j.eAdj
    eAdj := j.dAdj
    leftAdj := j.rightAdj
    rightAdj := j.leftAdj
    leftAdjLeaf := j.rightAdjLeaf
    rightAdjLeaf := j.leftAdjLeaf
    leftAdjCoherent := j.rightAdjCoherent
    rightAdjCoherent := j.leftAdjCoherent
    left := j.right
    right := j.left
    leftSource := j.rightSource
    rightSource := j.leftSource
    leftAdjInterface := j.rightAdjInterface
    rightAdjInterface := j.leftAdjInterface
    target := j.target.symm }

#print axioms StepJoinL
#print axioms StepJoinL.ofStepJoin
#print axioms CoherentDiamondL
#print axioms coherentDiamondL_of_coherentDiamond
#print axioms stripOfL
#print axioms confluenceOfL
#print axioms stepJoin_of_propIndex
#print axioms coherentDiamond_propIndex
#print axioms stepJoin_peq_left
#print axioms stepJoin_peq_right
#print axioms etaLeafRevLeaf
#print axioms etaLeafRevLeafConv
#print axioms etaLeafRevInnerStep
#print axioms etaLeafRevInnerConv
#print axioms etaLeafRevInnerCert
#print axioms etaLeafRevBodyStep
#print axioms etaLeafRevBodyConv
#print axioms etaLeafRevBodyCert
#print axioms etaLeafRevLamStep
#print axioms etaLeafRevLamCert
#print axioms etaLeafRevStep
#print axioms etaLeafEtaCStep
#print axioms etaLeafFRefl
#print axioms etaLeaf_stepJoinL
#print axioms appVarStep_target'
#print axioms appVarStar_target
#print axioms coherentDiamondL_false_of_notProof
#print axioms cdiamondD_false_of_notProof
#print axioms PureLeaf
#print axioms LeafStar
#print axioms LeafAdjJoin
#print axioms CoherentDiamondAdj
#print axioms etaLeafRevLamStep_pureLeaf
#print axioms etaLeaf_leafAdjJoin
#print axioms etaLeaf_leafAdjJoin_symm

end Rcic.Declarative.NativeValleys.LeafJoinAudit
