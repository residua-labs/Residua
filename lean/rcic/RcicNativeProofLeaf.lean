import rcic.RcicNativeValleyDecoTransfer
import rcic.RcicNativeStepTransferRows

/-!
# RcicNativeProofLeaf — the canonical proof leaf and typing-indexed single-step transfer

`ProofLeaf` is the spec's internal proof-only leaf
(`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §5.2): exactly the three
premises of `ConvT.irr`.  `proofLeafIface` is the `LeafIface` instance the producer
instantiates; its `typed` field returns the two stored typings VERBATIM, so
`decoOf (L.typed (L.ofIrr hT hp hq)).1 = decoOf hp` holds by `rfl`.  This is the
decoration-preservation law whose absence drives both the `ofIrr` roundtrip
counterexample (`RcicNativeDecoLeafIface`) and the single-step transfer counterexample
(`RcicNativeStepTransferCounterexample`); the latter's `retag` is impossible here
because `typed` does not rebuild the typing.  The lift and context-transport laws
(`proofLeaf_liftDeco`, `proofLeaf_ctxDeco`) discharge the `hPEqLDeco` / `hPEqCDeco` /
`hPEqIrrDeco` premises of `RcicNativeValleyDecoBook` for this interface.

`StepDecoTransferT` is the typing-indexed form of #7588's `StepDecoTransfer`: the
requested decoration is given as an actual typing `h : HasTyT E n Γ b T`, as every
caller has it (`p.leftTyped L hΓ`).  The existential form is strictly stronger as a
type (`stepDecoTransferT_of_transfer`), and is not inhabitable from the typing-indexed
form without a choice principle, because `Deco b` does not record the application
domains the rebuilt typings need.  Under the canonical leaf the typing-indexed contract
is constructed (`stepDecoTransferT_proofLeaf`) from `EnvWfT`, `PiInj` and `SortUniq`
by recursion on the certificate, with the typing peeled to its root node at every
constructor:

* `peq` — one irrelevance leaf carrying the requested typing (premise-free; this is the
  row the generic counterexample refutes);
* `refl`, `eta` — the requested typing is stored directly (premise-free);
* `lit`, `conv`, `iotaSpine`, `sortEq`, `consts`, `delta`, `bvarZeta` — premise-free
  (`expansionStepOf_typing`, chain transport, subsingleton decorations);
* `pi`, `lam`, `letE`, `zeta` — `SortUniq` retypes the binder's domain conversion; the
  body / value typings are re-presented at the step's index by `uniq_of_piInj_sortUniq`;
* `app`, `beta` — `uniq_of_piInj_sortUniq` aligns the children's indices, `PiInj` the
  β codomain, regularity (`tySort`) and `hasTyTInv_pi` supply the sort premises of
  #7588's `stepDecoTransfer_app` / `stepDecoTransfer_beta`.

`stepDecoTransferT_of_propIndex` is the premise-free special case at a `Prop`-sorted
index: the whole transfer is one leaf step.  The admitted fixture of
`admitted_single_step_transfer_false` (a closed proof of a closed `Prop`) is an
instance.  No unconditional single-step transfer is claimed: the uniqueness-shaped
inputs are exactly the named fronts `PiInj` and `SortUniq`, and an admitted
counterexample to the conditional statement would refute them.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}

/-! ### the canonical leaf -/

/-- The spec's proof-only leaf (§5.2): a `Prop`-sorted type and two of its inhabitants,
    exactly `ConvT.irr`'s premises. -/
structure ProofLeaf (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (p q T : Expr Nat) : Type where
  hT : HasTyT E n Γ T (.sort .zero)
  hp : HasTyT E n Γ p T
  hq : HasTyT E n Γ q T

/-- The canonical leaf interface: the stored typings are returned verbatim. -/
def proofLeafIface (E : ResolvedEnv) (n : Nat) : LeafIface E n (ProofLeaf E n) where
  typed := fun l => (l.hp, l.hq)
  conv := fun l => .irr _ _ _ _ l.hT l.hp l.hq
  prop := fun l => l.hT
  ofIrr := fun hT hp hq => ⟨hT, hp, hq⟩

namespace ProofLeafAudit

/-- `typed ∘ ofIrr` is the identity on the two typings. -/
theorem typed_ofIrr {Γ : LCtx} {p q T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero)) (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T) :
    (proofLeafIface E n).typed ((proofLeafIface E n).ofIrr hT hp hq) = (hp, hq) := rfl

/-- The irrelevance decoration law (`hPEqIrrDeco` of `stepDeco_csubstMixed`). -/
theorem irrDeco {Γ : LCtx} {p q T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero)) (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T) :
    decoOf ((proofLeafIface E n).typed ((proofLeafIface E n).ofIrr hT hp hq)).1 = decoOf hp :=
  rfl

/-- The leaf's source decoration is the stored typing's. -/
theorem stepDeco_irr {Γ : LCtx} {p q T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero)) (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T) :
    stepDeco (proofLeafIface E n) (CStep.irr (proofLeafIface E n) hT hp hq).step = decoOf hp :=
  rfl

/-- Leaf weakening (`hPEqL`): the three typings weaken by `hasTyTWeaken`; the sort is
    fixed by `lift`. -/
def lift (hcl : EnvClosed E) {Γ : LCtx} {p q T : Expr Nat} {d : LocalDecl} {c : Nat}
    (l : ProofLeaf E n Γ p q T) :
    ProofLeaf E n (insertAt d c Γ) (Rcic.Declarative.lift c 1 p) (Rcic.Declarative.lift c 1 q)
      (Rcic.Declarative.lift c 1 T) :=
  ⟨by simpa only [Rcic.Declarative.lift] using hasTyTWeaken d hcl (c := c) l.hT,
    hasTyTWeaken d hcl l.hp, hasTyTWeaken d hcl l.hq⟩

/-- Leaf weakening preserves the source decoration up to `decoLift` (`hPEqLDeco`). -/
theorem liftDeco (hcl : EnvClosed E) {Γ : LCtx} {p q T : Expr Nat} {d : LocalDecl} {c : Nat}
    (l : ProofLeaf E n Γ p q T) :
    decoOf ((proofLeafIface E n).typed (lift hcl (d := d) (c := c) l)).1 =
      decoLift c 1 (decoOf ((proofLeafIface E n).typed l).1) :=
  decoOf_hasTyTWeaken d hcl l.hp

/-- Leaf context transport along `LetAnnCtxConvT` (`hPEqC`), through its image in
    `CtxConvT`. -/
def ctx (hcl : EnvClosed E) {Γ Γ' : LCtx} {p q T : Expr Nat}
    (hcc : LetAnnCtxConvT E n Γ Γ') (l : ProofLeaf E n Γ p q T) : ProofLeaf E n Γ' p q T :=
  ⟨hasTyT_ctx hcl (letAnnCtxConvT_to_ctxConvT hcc) l.hT,
    hasTyT_ctx hcl (letAnnCtxConvT_to_ctxConvT hcc) l.hp,
    hasTyT_ctx hcl (letAnnCtxConvT_to_ctxConvT hcc) l.hq⟩

/-- Context transport preserves the source decoration (`hPEqCDeco`). -/
theorem ctxDeco (hcl : EnvClosed E) {Γ Γ' : LCtx} {p q T : Expr Nat}
    (hcc : LetAnnCtxConvT E n Γ Γ') (l : ProofLeaf E n Γ p q T) :
    decoOf ((proofLeafIface E n).typed (ctx hcl hcc l)).1 =
      decoOf ((proofLeafIface E n).typed l).1 :=
  decoOf_hasTyT_ctx hcl (letAnnCtxConvT_to_ctxConvT hcc) l.hp

/-! ### the typing-indexed transfer contract -/

set_option linter.unusedVariables false in
/-- Single-step decoration transfer indexed by an actual typing of the source at the
    step's index: the requested decoration is `decoOf h`. -/
def StepDecoTransferT (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b e T : Expr Nat}
    (q : CStep E n PEq Γ b e T) (h : HasTyT E n Γ b T),
    Σ' (q' : CStep E n PEq Γ b e T), stepDeco L q'.step = decoOf h

/-- The existential contract implies the typing-indexed one (the realizer is the typing
    itself). -/
def stepDecoTransferT_of_transfer {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {L : LeafIface E n PEq} (T_deco : StepDecoTransfer E n PEq L) :
    StepDecoTransferT E n PEq L :=
  fun {_} hΓ {_ _ _} q h => T_deco hΓ q (decoOf h) ⟨h, rfl⟩

/-- #7588's bridge `cdiamond_of_cdiamondD_transfer` consumes only the typing-indexed form:
    the realizer it supplies is `p.leftTyped L hΓ`. -/
def cdiamond_of_cdiamondD_transferT {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (L : LeafIface E n PEq) (D_deco : CDiamondD E n PEq L) (T_deco : StepDecoTransferT E n PEq L) :
    CDiamond E n PEq :=
  fun {_} hΓ {_ _ _ _} p q =>
    let ⟨q', hq'⟩ := T_deco hΓ q (p.leftTyped L hΓ)
    D_deco hΓ p q' (by rw [hq', decoOf_leftTyped])

/-- At a `Prop`-sorted index the canonical leaf transfers every step in one leaf step,
    with no premise. -/
def stepDecoTransferT_of_propIndex {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (hT : HasTyT E n Γ T (.sort .zero)) (q : CStep E n (ProofLeaf E n) Γ b e T)
    (h : HasTyT E n Γ b T) :
    Σ' (q' : CStep E n (ProofLeaf E n) Γ b e T),
      stepDeco (proofLeafIface E n) q'.step = decoOf h :=
  ⟨CStep.irr (proofLeafIface E n) hT h (q.rightTyped (proofLeafIface E n) hΓ), rfl⟩

/-! ### peeling a typing to its root node, with the decoration equation -/

/-- An application typing: its root `app` node and the outer chain. -/
def peelApp {Γ : LCtx} {f a : Expr Nat} :
    {T : Expr Nat} → (h : HasTyT E n Γ (.app f a) T) →
    Σ' (A B : Expr Nat) (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A),
      TyConvT E n Γ (instantiate0 a B) T ×' decoOf h = .app f a B (decoOf hf) (decoOf ha)
  | _, .app _ _ _ A B hf ha => ⟨A, B, hf, ha, .refl _ _, rfl⟩
  | _, .conv _ _ A' B' u h hc =>
      let ⟨A, B, hf, ha, c, hd⟩ := peelApp h
      ⟨A, B, hf, ha, .trans _ _ _ _ c (.of _ _ _ u hc), hd⟩

/-- A λ typing: its root `lam` node and the outer chain. -/
def peelLam {Γ : LCtx} {A body : Expr Nat} :
    {T : Expr Nat} → (h : HasTyT E n Γ (.lam A body) T) →
    Σ' (u : Level) (B : Expr Nat) (hA : HasTyT E n Γ A (.sort u))
      (hb : HasTyT E n (.assumption A :: Γ) body B),
      TyConvT E n Γ (.pi A B) T ×' decoOf h = .lam A body u (decoOf hA) (decoOf hb)
  | _, .lam _ _ u _ B hA hb => ⟨u, B, hA, hb, .refl _ _, rfl⟩
  | _, .conv _ _ A' B' w h hc =>
      let ⟨u, B, hA, hb, c, hd⟩ := peelLam h
      ⟨u, B, hA, hb, .trans _ _ _ _ c (.of _ _ _ w hc), hd⟩

/-- A Π typing: its root `pi` node and the outer chain. -/
def peelPi {Γ : LCtx} {A B : Expr Nat} :
    {T : Expr Nat} → (h : HasTyT E n Γ (.pi A B) T) →
    Σ' (u v : Level) (hA : HasTyT E n Γ A (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)),
      TyConvT E n Γ (.sort (.imax u v)) T ×' decoOf h = .pi A B u v (decoOf hA) (decoOf hB)
  | _, .pi _ _ u _ v hA hB => ⟨u, v, hA, hB, .refl _ _, rfl⟩
  | _, .conv _ _ A' B' w h hc =>
      let ⟨u, v, hA, hB, c, hd⟩ := peelPi h
      ⟨u, v, hA, hB, .trans _ _ _ _ c (.of _ _ _ w hc), hd⟩

/-- A `let` typing: its root `letE` node and the outer chain. -/
def peelLetE {Γ : LCtx} {A value body : Expr Nat} :
    {T : Expr Nat} → (h : HasTyT E n Γ (.letE A value body) T) →
    Σ' (u : Level) (B : Expr Nat) (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
      (hb : HasTyT E n (.letBinding A value :: Γ) body B),
      TyConvT E n Γ (instantiate0 value B) T ×'
        decoOf h = .letE A value body u (decoOf hA) (decoOf hv) (decoOf hb)
  | _, .letE _ _ u _ B _ hA hv hb => ⟨u, B, hA, hv, hb, .refl _ _, rfl⟩
  | _, .conv _ _ A' B' w h hc =>
      let ⟨u, B, hA, hv, hb, c, hd⟩ := peelLetE h
      ⟨u, B, hA, hv, hb, .trans _ _ _ _ c (.of _ _ _ w hc), hd⟩

/-! ### the assembler under the canonical leaf -/

/-- Re-present a typing at another index of the same term, keeping its decoration. -/
noncomputable def represent (hW : EnvWfT E) (piInj : PiInj E n) (su : SortUniq E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e T₁ T₂ : Expr Nat} (h : HasTyT E n Γ e T₁) (h₂ : HasTyT E n Γ e T₂) :
    Σ' (h' : HasTyT E n Γ e T₂), decoOf h' = decoOf h :=
  let hc := uniq_of_piInj_sortUniq hW piInj su hΓ h h₂
  ⟨hasTyT_of_tyConvT h hc, decoOf_hasTyT_of_tyConvT h hc⟩

/-- The recursion on the certificate.  The requested typing `h` is peeled at every
    constructor; the recursive calls are on the original sub-certificates, with the
    children's requested typings re-presented at the children's own indices. -/
noncomputable def transferCore (hW : EnvWfT E) (piInj : PiInj E n) (su : SortUniq E n) :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) → {b e T : Expr Nat} →
    {p : ParRedT (ProofLeaf E n) E n Γ b e T} → Certified p → (h : HasTyT E n Γ b T) →
    Σ' (q' : CStep E n (ProofLeaf E n) Γ b e T),
      stepDeco (proofLeafIface E n) q'.step = decoOf h
  | Γ, _, _, _, _, _, @Certified.refl _ _ _ _ b T _ _, h =>
      ⟨⟨.refl Γ b T h, .refl (.refl Γ b T h)⟩, rfl⟩
  | Γ, _, _, _, _, _, @Certified.sortEq _ _ _ _ l₁ l₂ T hq hl hr c, _ =>
      ⟨⟨.sortEq Γ l₁ l₂ T hq hl hr, .sortEq c⟩, deco_subsingleton_sort rfl _ _⟩
  | Γ, _, _, _, _, _, @Certified.consts _ _ _ _ r ls ls' T hq hl hr c, _ =>
      ⟨⟨.consts Γ r ls ls' T hq hl hr, .consts c⟩, deco_subsingleton_const rfl _ _⟩
  | Γ, _, _, _, _, _, @Certified.bvarZeta _ _ _ _ i A v v' T hg hv hl hr c cv, _ =>
      ⟨⟨.bvarZeta Γ i A v v' T hg hv hl hr, .bvarZeta c cv⟩, deco_subsingleton_bvar rfl _ _⟩
  | Γ, _, _, _, _, _,
      @Certified.delta _ _ _ _ r ls m b T hres hbody htr hlen hwf hl hr c, _ =>
      ⟨⟨.delta Γ r ls m b T hres hbody htr hlen hwf hl hr, .delta c⟩,
        deco_subsingleton_const rfl _ _⟩
  | Γ, hΓ, _, _, _, _,
      @Certified.app _ _ _ _ f f' a a' A B T₀ v w hf hc hB hTy ha hr c cf ca, h =>
      let L := proofLeafIface E n
      let ⟨A', B', hf', ha', _, hd⟩ := peelApp h
      let hfL : HasTyT E n Γ f T₀ := parRedT_hasTy_left L.typed hΓ hf
      let haL : HasTyT E n Γ a A := parRedT_hasTy_left L.typed hΓ ha
      let hc' : TyConvT E n Γ T₀ (.pi A' B') := uniq_of_piInj_sortUniq hW piInj su hΓ hfL hf'
      let hf'T₀ := represent hW piInj su hΓ hf' hfL
      let ha'A := represent hW piInj su hΓ ha' haL
      let ⟨_, hPi⟩ := tySort hW hΓ hf'
      let ⟨_, _, hA', hB', _⟩ := hasTyTInv_pi hPi rfl
      let ihf : Σ' (qf' : CStep E n (ProofLeaf E n) Γ f f' T₀), stepDeco L qf'.step = decoOf hf' :=
        let r := transferCore hW piInj su hΓ cf hf'T₀.1
        ⟨r.1, r.2.trans hf'T₀.2⟩
      let iha : Σ' (qa' : CStep E n (ProofLeaf E n) Γ a a' A), stepDeco L qa'.step = decoOf ha' :=
        let r := transferCore hW piInj su hΓ ca ha'A.1
        ⟨r.1, r.2.trans ha'A.2⟩
      let r := stepDecoTransfer_app hW L piInj hΓ hc hc' hA' hB' ihf iha
      ⟨r.1, r.2.trans hd.symm⟩
  | Γ, hΓ, _, _, _, _,
      @Certified.beta _ _ _ _ A body body' arg arg' B u v w hA hB hTy hb ha hred c cb ca, h =>
      let L := proofLeafIface E n
      let ⟨_, B₁, hlam, harg, _, hd⟩ := peelApp h
      let ⟨u₂, B₂, hA₂, hbody₂, cLam, hdLam⟩ := peelLam hlam
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      let hbL : HasTyT E n (.assumption A :: Γ) body B := parRedT_hasTy_left L.typed hΓA hb
      let haL : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha
      let hbody₂B := represent hW piInj su hΓA hbody₂ hbL
      let hargA := represent hW piInj su hΓ harg haL
      let ihb : Σ' (qb₀ : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body' B),
          stepDeco L qb₀.step = decoOf hbody₂ :=
        let r := transferCore hW piInj su hΓA cb hbody₂B.1
        ⟨r.1, r.2.trans hbody₂B.2⟩
      let iha : Σ' (qa' : CStep E n (ProofLeaf E n) Γ arg arg' A), stepDeco L qa'.step = decoOf harg :=
        let r := transferCore hW piInj su hΓ ca hargA.1
        ⟨r.1, r.2.trans hargA.2⟩
      let hcB₂₁ : TyConvT E n (.assumption A :: Γ) B₂ B₁ := (piInj hΓ cLam).2
      let hcB : TyConvT E n (.assumption A :: Γ) B B₁ :=
        .trans _ _ _ _ (uniq_of_piInj_sortUniq hW piInj su hΓA hbL hbody₂) hcB₂₁
      let ⟨_, hB'⟩ := tySort hW hΓA (hasTyT_of_tyConvT hbody₂ hcB₂₁)
      let r := stepDecoTransfer_beta hW L hΓ hA₂ hB' hcB c ihb iha
      ⟨r.1, r.2.trans (by rw [hd, hdLam])⟩
  | Γ, hΓ, _, _, _, _, @Certified.lam _ _ _ _ A A' body body' B u v hc hA hB hb hrt c cb, h =>
      let L := proofLeafIface E n
      let ⟨_, _, hA₂, hbody₂, _, hd⟩ := peelLam h
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      let hbL : HasTyT E n (.assumption A :: Γ) body B := parRedT_hasTy_left L.typed hΓA hb
      let hbody₂B := represent hW piInj su hΓA hbody₂ hbL
      let ihb : Σ' (qb' : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body' B),
          stepDeco L qb'.step = decoOf hbody₂ :=
        let r := transferCore hW piInj su hΓA cb hbody₂B.1
        ⟨r.1, r.2.trans hbody₂B.2⟩
      let r := stepDecoTransfer_lam L su hΓ hc hA hB hrt c hA₂ ihb
      ⟨r.1, r.2.trans hd.symm⟩
  | Γ, hΓ, _, _, _, _, @Certified.pi _ _ _ _ A A' B B' u v hA hc hB hcB hrt _, h =>
      let ⟨_, _, hA₂, hB₂, _, hd⟩ := peelPi h
      let r := stepDecoTransfer_pi (proofLeafIface E n) su hΓ hA hc hB hcB hrt hA₂ hB₂
      ⟨r.1, r.2.trans hd.symm⟩
  | Γ, hΓ, _, _, _, _,
      @Certified.letE _ _ _ _ A A' value value' body body' B u w hc hA hv hB hTy hb hrt c cv cb,
      h =>
      let L := proofLeafIface E n
      let ⟨_, _, hA₂, hv₂, hb₂, _, hd⟩ := peelLetE h
      let hvL : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv
      let hΓL : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓ hA hvL
      let hbL : HasTyT E n (.letBinding A value :: Γ) body B := parRedT_hasTy_left L.typed hΓL hb
      let hb₂B := represent hW piInj su hΓL hb₂ hbL
      let ihv := transferCore hW piInj su hΓ cv hv₂
      let ihb : Σ' (qb' : CStep E n (ProofLeaf E n) (.letBinding A value :: Γ) body body' B),
          stepDeco L qb'.step = decoOf hb₂ :=
        let r := transferCore hW piInj su hΓL cb hb₂B.1
        ⟨r.1, r.2.trans hb₂B.2⟩
      let r := stepDecoTransfer_letE L su hΓ hc hA hB hTy hrt c hA₂ ihv ihb
      ⟨r.1, r.2.trans hd.symm⟩
  | Γ, hΓ, _, _, _, _,
      @Certified.zeta _ _ _ _ A value value' body body' B u w hA hv hB hTy hb hred c cv cb, h =>
      let L := proofLeafIface E n
      let ⟨_, _, hA₂, hv₂, hb₂, _, hd⟩ := peelLetE h
      let hvL : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv
      let hΓL : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓ hA hvL
      let hbL : HasTyT E n (.letBinding A value :: Γ) body B := parRedT_hasTy_left L.typed hΓL hb
      let hb₂B := represent hW piInj su hΓL hb₂ hbL
      let ihv := transferCore hW piInj su hΓ cv hv₂
      let ihb : Σ' (qb' : CStep E n (ProofLeaf E n) (.letBinding A value :: Γ) body body' B),
          stepDeco L qb'.step = decoOf hb₂ :=
        let r := transferCore hW piInj su hΓL cb hb₂B.1
        ⟨r.1, r.2.trans hb₂B.2⟩
      let r := stepDecoTransfer_zeta L hB hTy hred c hA₂ ihv ihb
      ⟨r.1, r.2.trans hd.symm⟩
  | Γ, hΓ, _, _, _, _, @Certified.iotaSpine _ _ _ _ lhs lhs' rhs T hstep hI hred hrhs c cs, h =>
      stepDecoTransfer_iotaSpine (proofLeafIface E n) hΓ hI hrhs c
        (transferCore hW piInj su hΓ cs h)
  | _, _, _, _, _, _, @Certified.lit _ _ _ _ _ _ _ _, h =>
      StepTransferRowsAudit.expansionStepOf_typing (proofLeafIface E n) h
  | Γ, _, _, _, _, _, @Certified.eta _ _ _ _ f f' A B hf _ c cf, h =>
      ⟨⟨.eta Γ f f' A B hf h, .eta c cf⟩, rfl⟩
  | _, _, _, _, _, _, @Certified.peq _ _ _ _ _ _ _ hl _, h =>
      ⟨CStep.irr (proofLeafIface E n) hl.hT h hl.hq, rfl⟩
  | Γ, hΓ, _, _, _, _, @Certified.conv _ _ _ _ a b A A' _ hcT _ ch, h =>
      let hA : HasTyT E n Γ a A := hasTyT_of_tyConvT h hcT.symmT
      let r := stepDecoTransfer_conv (proofLeafIface E n) hcT (transferCore hW piInj su hΓ ch hA)
      ⟨r.1, r.2.trans (decoOf_hasTyT_of_tyConvT h hcT.symmT)⟩

/-- Single-step decoration transfer under the canonical leaf, from `EnvWfT`, `PiInj` and
    `SortUniq`. -/
noncomputable def stepDecoTransferT_proofLeaf (hW : EnvWfT E) (piInj : PiInj E n)
    (su : SortUniq E n) : StepDecoTransferT E n (ProofLeaf E n) (proofLeafIface E n) :=
  fun {_} hΓ {_ _ _} q h => transferCore hW piInj su hΓ q.cert h

/-- With #7588's decorated diamond, the canonical leaf's transfer yields the ordinary
    `CDiamond` (conditional algebra; `CDiamond` itself is refuted modulo `NotProof` by
    `cdiamond_false_of_leaf`, so this records that `CDiamondD (proofLeafIface E n)` inherits
    that obstruction under the same two fronts). -/
noncomputable def cdiamond_of_cdiamondD_proofLeaf (hW : EnvWfT E) (piInj : PiInj E n)
    (su : SortUniq E n) (D_deco : CDiamondD E n (ProofLeaf E n) (proofLeafIface E n)) :
    CDiamond E n (ProofLeaf E n) :=
  cdiamond_of_cdiamondD_transferT (proofLeafIface E n) D_deco
    (stepDecoTransferT_proofLeaf hW piInj su)

end ProofLeafAudit

#print axioms ProofLeaf
#print axioms proofLeafIface
#print axioms ProofLeafAudit.typed_ofIrr
#print axioms ProofLeafAudit.irrDeco
#print axioms ProofLeafAudit.stepDeco_irr
#print axioms ProofLeafAudit.lift
#print axioms ProofLeafAudit.liftDeco
#print axioms ProofLeafAudit.ctx
#print axioms ProofLeafAudit.ctxDeco
#print axioms ProofLeafAudit.StepDecoTransferT
#print axioms ProofLeafAudit.stepDecoTransferT_of_transfer
#print axioms ProofLeafAudit.cdiamond_of_cdiamondD_transferT
#print axioms ProofLeafAudit.stepDecoTransferT_of_propIndex
#print axioms ProofLeafAudit.peelApp
#print axioms ProofLeafAudit.peelLam
#print axioms ProofLeafAudit.peelPi
#print axioms ProofLeafAudit.peelLetE
#print axioms ProofLeafAudit.represent
#print axioms ProofLeafAudit.transferCore
#print axioms ProofLeafAudit.stepDecoTransferT_proofLeaf
#print axioms ProofLeafAudit.cdiamond_of_cdiamondD_proofLeaf

end Rcic.Declarative.NativeValleys
