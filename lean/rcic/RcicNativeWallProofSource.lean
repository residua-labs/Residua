import rcic.RcicNativeValleyCert

/-!
# Native valley proof-source audit

`closure_claim = 0`.

These are local constructions from an EXPLICIT data-valued host-Prop transfer
parameter. This file does not construct that parameter, `ZeroSortCoherence`,
`CDiamond`, `OpenRows`, or `NativeConvValleys`. Its source-centre joins avoid
`retype` and do not manufacture a conversion between independent indices.

Intended dependency pin:
`fable/native-valleys` at `4d3b74e05355f478a03a44166399794a0a68d2a4`.
-/

namespace Rcic.Declarative.NativeValleys.ProofSourceAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A witness representation only; no proofhood decision procedure is asserted. -/
abbrev ProofData (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (b : Expr Nat) : Type :=
  Σ' (P : Expr Nat),
    HasTyT E n Γ P (.sort .zero) ×' HasTyT E n Γ b P

/-- An explicit hypothesis, not a constructed instance. -/
abbrev HostPropData (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} {b T P : Expr Nat},
    CtxWfT E n Γ → HasTyT E n Γ b T →
    HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ b P →
    HasTyT E n Γ T (.sort .zero)

/-- Every independent-index peak whose source is a proof joins AT ITS SOURCE.
The two irrelevance leaves use their own host indices separately. -/
def join_of_proof_source (L : LeafIface E n PEq) (H : HostPropData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hbP : HasTyT E n Γ b P)
    (p : CStep E n PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  let hb₁ := p.leftTyped L hΓ
  let hb₂ := q.leftTyped L hΓ
  let hT₁ := H hΓ hb₁ hP hbP
  let hT₂ := H hΓ hb₂ hP hbP
  ⟨b, CStep.irr L hT₁ (p.rightTyped L hΓ) hb₁,
    CStep.irr L hT₂ (q.rightTyped L hΓ) hb₂⟩

/-- Proofhood moves forwards along a certified step using host-Prop transfer
at that step's own index. -/
def proofData_forward (L : LeafIface E n PEq) (H : HostPropData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (s : CStep E n PEq Γ b e T) (hb : ProofData E n Γ b) :
    ProofData E n Γ e :=
  ⟨T, H hΓ (s.leftTyped L hΓ) hb.2.1 hb.2.2, s.rightTyped L hΓ⟩

/-- Proofhood also moves backwards; no reversal of the operational step is
needed to establish this witness. -/
def proofData_backward (L : LeafIface E n PEq) (H : HostPropData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (s : CStep E n PEq Γ b e T) (he : ProofData E n Γ e) :
    ProofData E n Γ b :=
  ⟨T, H hΓ (s.rightTyped L hΓ) he.2.1 he.2.2, s.leftTyped L hΓ⟩

theorem proofhood_iff (L : LeafIface E n PEq) (H : HostPropData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (s : CStep E n PEq Γ b e T) :
    Nonempty (ProofData E n Γ b) ↔ Nonempty (ProofData E n Γ e) := by
  constructor
  · rintro ⟨hb⟩
    exact ⟨proofData_forward L H hΓ s hb⟩
  · rintro ⟨he⟩
    exact ⟨proofData_backward L H hΓ s he⟩

/-- Specialisation to a proof leaf: only the other input's host needs transfer. -/
def join_peq_source (L : LeafIface E n PEq) (H : HostPropData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (h : PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  let hb₂ := q.leftTyped L hΓ
  let hT₂ := H hΓ hb₂ (L.prop h) (L.typed h).1
  ⟨b, CStep.irr L (L.prop h) (L.typed h).2 (L.typed h).1,
    CStep.irr L hT₂ (q.rightTyped L hΓ) hb₂⟩

/-- Two proof leaves at independent indices join at their common source.
No host-Prop transfer is needed in this special case. -/
def join_peq_peq (L : LeafIface E n PEq)
    {Γ : LCtx} {b d e T₁ T₂ : Expr Nat}
    (h₁ : PEq Γ b d T₁) (h₂ : PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  ⟨b, CStep.irr L (L.prop h₁) (L.typed h₁).2 (L.typed h₁).1,
    CStep.irr L (L.prop h₂) (L.typed h₂).2 (L.typed h₂).1⟩

/-- Reflexivity versus a proof leaf also joins at the source without transfer. -/
def join_refl_peq (L : LeafIface E n PEq)
    {Γ : LCtx} {b e T₁ T₂ : Expr Nat}
    (hb : HasTyT E n Γ b T₁) (h : PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ b f T₁ ×' CStep E n PEq Γ e f T₂ :=
  ⟨b, ⟨.refl Γ b T₁ hb, .refl (.refl Γ b T₁ hb)⟩,
    CStep.irr L (L.prop h) (L.typed h).2 (L.typed h).1⟩

/-- A genuinely supplied index chain is sufficient for the generic reflexive
row. The construction does not obtain such chains for application children. -/
def join_refl_connected (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T₁ T₂ : Expr Nat}
    (chain : TyConvT E n Γ T₁ T₂) (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ b f T₁ ×' CStep E n PEq Γ e f T₂ :=
  ⟨e, q.reindex chain.symmT,
    ⟨.refl Γ e T₂ (q.rightTyped L hΓ), .refl (.refl Γ e T₂ (q.rightTyped L hΓ))⟩⟩

/-- A genuinely supplied index chain is also sufficient for the generic proof
leaf row; only the original leaf index must be Prop-sorted. -/
def join_peq_connected (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (h : PEq Γ b d T₁) (chain : TyConvT E n Γ T₁ T₂)
    (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  let he₁ := hasTyT_of_tyConvT (q.rightTyped L hΓ) chain.symmT
  ⟨e, CStep.irr L (L.prop h) (L.typed h).2 he₁,
    ⟨.refl Γ e T₂ (q.rightTyped L hΓ), .refl (.refl Γ e T₂ (q.rightTyped L hΓ))⟩⟩

/-- A native conversion with an externally certified proof source has a valley
directly, without any diamond input. Host-Prop transfer remains explicit. -/
def valley_of_proof_source (hW : EnvWfT E) (L : LeafIface E n PEq)
    (H : HostPropData E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d T P : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hbP : HasTyT E n Γ b P) (c : ConvT E n Γ b d T) :
    CValley E n PEq Γ b d T :=
  let ends := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ c
  let hT := H hΓ ends.1 hP hbP
  CValley.ofStep L hΓ (CStep.irr L hT ends.1 ends.2.1)

#print axioms join_of_proof_source
#print axioms proofhood_iff
#print axioms join_peq_source
#print axioms join_peq_peq
#print axioms join_refl_peq
#print axioms join_refl_connected
#print axioms join_peq_connected
#print axioms valley_of_proof_source

end Rcic.Declarative.NativeValleys.ProofSourceAudit
