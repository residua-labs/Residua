import rcic.RcicEtaKDecide
import rcic.RcicSynPrepaidKeys

/-!
# PiRow wall, piece H — exact native join certificates (spec §6.2)

For a peak carrying `cL : ConvT a b T` and `cR : ConvT a c T` joining at
`c`, the stored certificate is exactly
`ConvT.trans Γ b a c T (ConvT.symm Γ a b T cL) cR`, recorded at exact
context, endpoints, type, occurrence and stage (`ExactJoinCert`).

No `EnvWfT`/`CtxWfT`/uniqueness premise appears anywhere: the peak's own
`ConvT` arms are the entire input, so the generic `parRedT_to_convT`
back-lift (`RcicParRedTConv.lean` L114–125, whose `hUniq` is the retained
typed-alignment demand of §6.1) is never invoked. Composition only —
`ConvT.symm`/`ConvT.trans` and the landed positive-peak package
`positive_peak_joined`; nothing existing is touched.

Coverage, stated precisely (spec §6.2): the mechanism is TOTAL over
endpoint-directed repairs — every pair of `ConvT` arms sharing the source
`a` stores and joins, incl. the positive η/K form (`positiveExactCert`).
It does NOT cover `JoinStage.arbitraryCentre` diamonds (the join centre
is not the peak's right target), `dependentAppIndex` alignment, or
`schemaIota` generated certificates — no constructor here produces a
certificate of those stages. closure_claim = 0.
-/

namespace Rcic.Declarative.PiRowCerts

/-- §6.2's stage tag, recording which diamond class a stored certificate
    belongs to. `endpointDirected` is the only stage this module
    produces; the other three tags exist so the coverage claim can NAME
    what is not covered, per the spec. -/
inductive JoinStage : Type
  | endpointDirected
  | arbitraryCentre
  | dependentAppIndex
  | schemaIota
  deriving DecidableEq

/-- §6.2's exact native certificate. The joined conversion at `b → c` is
    computed (`joined`), never asserted; `left`/`right` are the peak's
    carried `ConvT` arms; `occurrence` is the demand-address code (the
    shared FieldPath stand-in of `RcicSynPrepaidKeys` §1, to be replaced
    when the FieldPath/DRef layer lands); `stage` records the diamond
    class. -/
structure ExactJoinCert (E : ResolvedEnv) (n : Nat) where
  Γ : LCtx
  a : Expr Nat
  b : Expr Nat
  c : Expr Nat
  T : Expr Nat
  left : ConvT E n Γ a b T
  right : ConvT E n Γ a c T
  occurrence : Rcic.Syn.FieldPathStub
  stage : JoinStage

/-- The stored conversion — definitionally
    `ConvT.trans Γ b a c T (ConvT.symm Γ a b T cL) cR`, the spec's term. -/
def ExactJoinCert.joined (c : ExactJoinCert E n) :
    ConvT E n c.Γ c.b c.c c.T :=
  ConvT.trans c.Γ c.b c.a c.c c.T
    (ConvT.symm c.Γ c.a c.b c.T c.left) c.right

/-- `joined` is the exact `trans (symm left) right` object, not any
    other conversion between `b` and `c`. -/
theorem ExactJoinCert.joined_eq_trans_symm (c : ExactJoinCert E n) :
    c.joined = ConvT.trans c.Γ c.b c.a c.c c.T
      (ConvT.symm c.Γ c.a c.b c.T c.left) c.right := rfl

/-- §6.2's certificate constructor — total over endpoint-directed peaks.
    Every `cL : ConvT a b T`, `cR : ConvT a c T` pair stores a
    certificate at the given occurrence address. -/
def exactJoinCert_of_peak (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b c T : Expr Nat) (cL : ConvT E n Γ a b T) (cR : ConvT E n Γ a c T)
    (occurrence : Rcic.Syn.FieldPathStub) : ExactJoinCert E n where
  Γ := Γ
  a := a; b := b; c := c; T := T
  left := cL; right := cR
  occurrence := occurrence
  stage := .endpointDirected

/-- Every certificate built by `exactJoinCert_of_peak` is in the covered
    class. -/
theorem exactJoinCert_of_peak_stage (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b c T : Expr Nat) (cL : ConvT E n Γ a b T) (cR : ConvT E n Γ a c T)
    (occurrence : Rcic.Syn.FieldPathStub) :
    (exactJoinCert_of_peak E n Γ a b c T cL cR occurrence).stage =
      .endpointDirected := rfl

/-- Totality over the covered class: every endpoint-directed peak yields
    the joined `ConvT b c T` — no environment, context or uniqueness
    premise. -/
theorem exactJoin_of_peak (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b c T : Expr Nat) (cL : ConvT E n Γ a b T) (cR : ConvT E n Γ a c T) :
    Nonempty (ConvT E n Γ b c T) :=
  ⟨ConvT.trans Γ b a c T (ConvT.symm Γ a b T cL) cR⟩

/-- The certificate at the positive η/K peak
    (`RcicEtaKDecide.positive_peak_joined`): source `a = partialRec one`
    `b = c = contracted` at `T = commonIndex` in `Γ = positiveContext`.
    The peak package's carried `ConvT` arm (`positive_conversion`, the
    package's third component) supplies BOTH peak legs — it is the only
    landed `ConvT (partialRec one) contracted commonIndex`, and `b = c`
    here, so the join is the self-join `trans (symm cL) cL`. Occurrence
    `[]` is the root address of the peak's own `iotaStarKEta` step. No
    `parRedT_to_convT` is used. -/
def positiveExactCert : ExactJoinCert eqEnvT 2 where
  Γ := F8EtaK.positiveContext
  a := F8EtaK.partialRec F8EtaK.one
  b := F8EtaK.contracted
  c := F8EtaK.contracted
  T := F8EtaK.commonIndex
  left := F8EtaK.positive_peak_joined.2.2
  right := F8EtaK.positive_peak_joined.2.2
  occurrence := []
  stage := .endpointDirected

/-- Exact storage, context: the certificate's context is the peak's own
    `positiveContext`. -/
theorem positiveExactCert_ctx :
    positiveExactCert.Γ = F8EtaK.positiveContext := rfl

/-- Exact storage, endpoints and type: source `partialRec one`, both
    targets `contracted`, at `commonIndex`. -/
theorem positiveExactCert_coords :
    positiveExactCert.a = F8EtaK.partialRec F8EtaK.one ∧
    positiveExactCert.b = F8EtaK.contracted ∧
    positiveExactCert.c = F8EtaK.contracted ∧
    positiveExactCert.T = F8EtaK.commonIndex := ⟨rfl, rfl, rfl, rfl⟩

/-- The positive η/K form is in the covered class. -/
theorem positiveExactCert_stage :
    positiveExactCert.stage = .endpointDirected := rfl

/-- The stored join on the positive peak: a real
    `ConvT eqEnvT 2 positiveContext contracted contracted commonIndex`,
    built by symm+trans from the peak's carried arm only. -/
theorem positiveExactCert_joined :
    Nonempty (ConvT eqEnvT 2 F8EtaK.positiveContext
      F8EtaK.contracted F8EtaK.contracted F8EtaK.commonIndex) :=
  ⟨positiveExactCert.joined⟩

end Rcic.Declarative.PiRowCerts
