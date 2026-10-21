import rcic.RcicNativeCertifiedK
import rcic.RcicDTMetaTypedSR

/-!
# RcicNativeCertifiedKRows — the plain K certificate and the schema-ι arm

Two of the three boundaries named in `RcicNativeCertifiedK`, made exact.

**1. The plain `iotaStarK` node.**  Its certificate is `recCall rec pre major = (foldApps rec
pre) major ~ (foldApps rec pre) (ctorMajor w) = iotaLhsOf w ~ rhs`: irrelevance on the major,
then ι.  The application congruence needs the irrelevance at the head's DOMAIN `A₀`
(`hasTyTInv_app` on the node's own `hlhs`), while the node supplies it at the family instance
`Tm` (`hmajor`, `hmk`, `hTm0`).  `A₀` and `Tm` are two types of the major; aligning them is
the exact missing statement `IotaKMajorAlign` — an instance of `Uniq` (DT-012's shape), which
the landed tree derives from `PiInj` + `SortUniq`.  Everything else is constructed:
`convT_iotaStarK_of_align`, `cstepK_iotaStarK_of_align`, and `iotaKMajorAlign_of_uniq`.
The recursor's stored telescope does not remove the alignment: `hlhs` is an arbitrary
derivation of the spine's typing, and relating its inverted domain to the telescope's
major domain is Π-injectivity along the spine — the same front.  (For the η-K node the
major is the bound variable and `hasTyTInv_bvar` gives the alignment for free; that is why
`convT_iotaStarKEta` needs no front.)

**2. The schema-ι arm.**  `ConvT.iota` takes legacy `DerivedIota` only.  The landed bridge
(`derivedIotaT_of_derivedIota_envWfT`) runs legacy → schema (`IotaWitness → IotaWitnessS`,
same endpoints, at `EnvWfT`); there is no schema → legacy bridge and no `ConvT` constructor
for `DerivedIotaT` / `DerivedIotaU.ofUS`.  The exact missing object is `SchemaIotaConv`:
a native conversion `iotaLhsOfS w ~ iotaRhsOfS w` from the schema ι's two typings.  With it,
`convT_iotaU` is the union-arm conversion, `convT_iotaStarKEta_of_body` /
`convT_iotaStarKEta_U` the η-K certificate for both arms, and `cstepK_iotaStarKEta_U`,
`cstepK_iotaStarK_U` the nodes.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A recursor call is the spine head applied to the major. -/
theorem recCall_eq_app (rec : Expr Nat) (pre : List (Expr Nat)) (major : Expr Nat) :
    recCall rec pre major = .app (foldApps rec pre) major := by
  unfold recCall
  exact foldApps_snoc _ _ _

/-- The ι redex is the spine head applied to the synthesized major. -/
theorem iotaLhsOf_eq_app (w : IotaWitness E) :
    iotaLhsOf w = .app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w) :=
  recCall_eq_app _ _ _

/-! ### 1. the plain K node -/

/-- The exact missing alignment for a plain K node: two types of its major convert. -/
def IotaKMajorAlign (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {major A₀ Tm : Expr Nat},
    HasTyT E n Γ major A₀ → HasTyT E n Γ major Tm → TyConvT E n Γ A₀ Tm

/-- `Uniq` supplies the alignment. -/
def iotaKMajorAlign_of_uniq (U : Uniq E n) : IotaKMajorAlign E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ => U hΓ h₁ h₂

/-- The plain K certificate from the alignment: irrelevance on the major at the head's
    domain, application congruence, ι. -/
def convT_iotaStarK_of_align (AL : IotaKMajorAlign E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {w : IotaWitness E} {major Tm rhs T : Expr Nat}
    (hmajor : HasTyT E n Γ major Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (ciota : ConvT E n Γ (iotaLhsOf w) rhs T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T) :
    ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T :=
  let inv := hasTyTInv_app hlhs (recCall_eq_app _ _ _)
  let chain : TyConvT E n Γ inv.1 Tm := AL hΓ inv.2.2.2.1 hmajor
  let cirr : ConvT E n Γ major (ctorMajor w) inv.1 :=
    convT_of_tyConv (.irr _ Tm _ _ hTm0 hmajor hmk) chain.symmT
  let capp : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) major)
      (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 major inv.2.1) :=
    .app _ _ _ major (ctorMajor w) inv.1 inv.2.1 (.refl _ _ _ inv.2.2.1) cirr
  let capp' : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) major)
      (iotaLhsOf w) T :=
    (iotaLhsOf_eq_app w).symm ▸ convT_of_tyConv capp inv.2.2.2.2
  (recCall_eq_app _ _ _).symm ▸ ConvT.trans _ _ _ _ _ capp' ciota

/-- The plain K node with its certificate from the alignment (legacy ι arm). -/
def cstepK_iotaStarK_of_align (AL : IotaKMajorAlign E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : IotaWitness E) (major Tm : Expr Nat) (T : Expr Nat) (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n Γ major Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T)
    (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
    CStepK E n PEq Γ (recCall (.const w.recRef w.ls) w.preMajor major) (iotaRhsOf w) T :=
  ⟨.iotaStarK Γ w major Tm (iotaRhsOf w) T rl afs hrl hsel hfam hmajor hmk hTm0 (.ofU w) hlι
      hlhs hrhs,
    .iotaStarK (convT_iotaStarK_of_align AL hΓ hmajor hmk hTm0
      (.iota _ _ _ _ (.of w) hlι hrhs) hlhs)⟩

/-! ### 2. the schema-ι arm -/

/-- The exact missing object for the schema arm: a native conversion along a schema ι
    landing, from its two typings. -/
def SchemaIotaConv (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} (w : IotaWitnessS E) {T : Expr Nat},
    HasTyT E n Γ (iotaLhsOfS w) T → HasTyT E n Γ (iotaRhsOfS w) T →
    ConvT E n Γ (iotaLhsOfS w) (iotaRhsOfS w) T

/-- The union-arm conversion: legacy by `ConvT.iota`, schema by the supplied object. -/
def convT_iotaU (SC : SchemaIotaConv E n) {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hι : DerivedIotaU E lhs rhs) (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T) :
    ConvT E n Γ lhs rhs T :=
  match hι with
  | .ofU w => .iota _ _ _ _ (.of w) hl hr
  | .ofUS w => SC w hl hr

/-- The η-K certificate from a body conversion along the ι landing (any arm): η reversed,
    then λ congruence over irrelevance on the bound major, application congruence and the
    supplied ι conversion. -/
def convT_iotaStarKEta_of_body (hcl : EnvClosed E) {Γ : LCtx} {w : IotaWitness E}
    {f A B Tm rhs : Expr Nat} {u : Level}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B))
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (ciota : ConvT E n (.assumption A :: Γ) (iotaLhsOf w) rhs B) :
    ConvT E n Γ f (.lam A rhs) (.pi A B) :=
  let c₁ : ConvT E n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) :=
    .symm _ _ _ _ (.eta Γ f A B hf)
  let hliftf : HasTyT E n (.assumption A :: Γ) (lift 0 1 f) (.pi (lift 0 1 A) (lift 1 1 B)) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hf
  let cirr : ConvT E n (.assumption A :: Γ) (.bvar 0) (ctorMajor w) Tm :=
    .irr _ Tm _ _ hTm0 hmajor hmk
  let inv := hasTyTInv_bvar hmajor rfl
  let hlk : lift 0 1 A = inv.1 := Option.some.inj inv.2.1
  let chain : TyConvT E n (.assumption A :: Γ) (lift 0 1 A) Tm := hlk ▸ inv.2.2
  let cirr' : ConvT E n (.assumption A :: Γ) (.bvar 0) (ctorMajor w) (lift 0 1 A) :=
    convT_of_tyConv cirr chain.symmT
  let capp : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      (.app (lift 0 1 f) (ctorMajor w)) (instantiate0 (.bvar 0) (lift 1 1 B)) :=
    .app _ (lift 0 1 f) (lift 0 1 f) (.bvar 0) (ctorMajor w) (lift 0 1 A) (lift 1 1 B)
      (.refl _ _ _ hliftf) cirr'
  let capp' : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      (.app (lift 0 1 f) (ctorMajor w)) B :=
    (instantiate_bvar_lift B 0) ▸ capp
  let ciota' : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (ctorMajor w)) rhs B :=
    (etaK_iotaLhs_eq happ) ▸ ciota
  let cbody : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) rhs B :=
    .trans _ _ _ _ _ capp' ciota'
  let c₂ : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A rhs) (.pi A B) :=
    .lam Γ A A _ rhs B u (.refl _ A _ hA) cbody
  .trans _ _ _ _ _ c₁ c₂

/-- The η-K certificate for both ι arms, given the schema object. -/
def convT_iotaStarKEta_U (hcl : EnvClosed E) (SC : SchemaIotaConv E n) {Γ : LCtx}
    {w : IotaWitness E} {f A B Tm rhs : Expr Nat} {u : Level}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B))
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B) :
    ConvT E n Γ f (.lam A rhs) (.pi A B) :=
  convT_iotaStarKEta_of_body hcl happ hA hf hmajor hmk hTm0 (convT_iotaU SC hι hlι hrhs)

/-- The η-K node with its certificate, both ι arms. -/
def cstepK_iotaStarKEta_U (hcl : EnvClosed E) (SC : SchemaIotaConv E n) {Γ : LCtx}
    (w : IotaWitness E) (f A B Tm rhs : Expr Nat) (u rl : Level) (afs : Prop)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ) (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B) :
    CStepK E n PEq Γ f (.lam A rhs) (.pi A B) :=
  ⟨.iotaStarKEta Γ w f A B Tm rhs u rl afs happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs
      hrhs,
    .iotaStarKEta (convT_iotaStarKEta_U hcl SC happ hA hf hmajor hmk hTm0 hι hlι hrhs)⟩

/-- The plain K node with its certificate, both ι arms, from the alignment and the schema
    object. -/
def cstepK_iotaStarK_U (AL : IotaKMajorAlign E n) (SC : SchemaIotaConv E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) (w : IotaWitness E) (major Tm rhs T : Expr Nat) (rl : Level)
    (afs : Prop) (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n Γ major Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero)) (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T)
    (hrhs : HasTyT E n Γ rhs T) :
    CStepK E n PEq Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T :=
  ⟨.iotaStarK Γ w major Tm rhs T rl afs hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs,
    .iotaStarK (convT_iotaStarK_of_align AL hΓ hmajor hmk hTm0 (convT_iotaU SC hι hlι hrhs)
      hlhs)⟩

#print axioms recCall_eq_app
#print axioms iotaLhsOf_eq_app
#print axioms IotaKMajorAlign
#print axioms iotaKMajorAlign_of_uniq
#print axioms convT_iotaStarK_of_align
#print axioms cstepK_iotaStarK_of_align
#print axioms SchemaIotaConv
#print axioms convT_iotaU
#print axioms convT_iotaStarKEta_of_body
#print axioms convT_iotaStarKEta_U
#print axioms cstepK_iotaStarKEta_U
#print axioms cstepK_iotaStarK_U

end Rcic.Declarative.NativeValleys
