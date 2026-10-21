import rcic.RcicCtxConvT
import rcic.RcicStepArmsEnvWf
import rcic.RcicDT0709EnvWf

/-!
# `TelRowInjT` — `PiRowInjT` iterated over a `foldr Expr.pi` telescope

#6293 (plain ruling): `TelRowInjT` is `PiRowInjT`'s *consumption*, not a new
wall — the per-domain extraction DT-019 measured at the ι `hrhs` discharge's
two const-head boundaries. From a `TyConvT` between equal-length Π-telescopes
this row delivers (a) a `CtxConvT` between the two telescope contexts — the
accumulated binder conversion, the piece the substitution kit retypes through
— and (b) the codomains' `TyConvT` under the LEFT telescope, `PiRowInjT`'s
own left-prefix convention (sibling of `ConvArgsT`).

`telRowInjT_of_piRowInj` is the iteration: each step peels the outermost
`pi` off `hrow`, transports the domain conv to the target-side context by
`convT_ctx` (the `CtxConvT` accumulated so far), and extends that `CtxConvT`
by `.assumption` — whose typing fields `DT009T_endpoints_envWfT` supplies at
`EnvWfT` unconditionally. The codomain leg stays on the left context, so the
delivered `TyConvT` is at `telCtx Γ As` and the delivered `CtxConvT` runs
`telCtx Γ As → telCtx Γ As'`.

`PiRowInjT` itself stays a named premise — never discharged at `EnvWfT`
alone (the Loop tooth). `closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- the local context of a `foldr Expr.pi` telescope: the outer-first domain
    list as assumption declarations, last domain innermost. -/
def telCtx (Γ : LCtx) (As : List (Expr Nat)) : LCtx :=
  As.reverse.map LocalDecl.assumption ++ Γ

/-- the outermost domain's declaration sits deepest: peeling a `pi` extends
    the context by it directly. -/
theorem telCtx_cons (Γ : LCtx) (A : Expr Nat) (As : List (Expr Nat)) :
    telCtx Γ (A :: As) = telCtx (.assumption A :: Γ) As := by
  simp only [telCtx, List.reverse_cons, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- ROW (telescope-level Π injectivity, `PiRowInjT`'s iterated consumption):
    a type-level conversion between equal-length Π-telescopes has pointwise-
    convertible binder contexts and type-convertible codomains under the left
    telescope. `Prop`-valued in the `TypedRowsWf` convention (`Nonempty` per
    component); `CtxWfT`-conditioned per call, like the `TypedRowsWf` rows. -/
def TelRowInjT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {As As' : List (Expr Nat)} {B B' : Expr Nat},
    TyConvT E n Γ (As.foldr Expr.pi B) (As'.foldr Expr.pi B') →
    As.length = As'.length →
    Nonempty (CtxConvT E n (telCtx Γ As) (telCtx Γ As')) ∧
    Nonempty (TyConvT E n (telCtx Γ As) B B')

/-- the iteration: `PiRowInjT` peels one `pi`; `convT_ctx` moves the domain
    conversion to the target context (through the `CtxConvT` accumulated so
    far); `CtxConvT.assumption` extends the conversion by it — its typing
    fields read off `DT009T_endpoints_envWfT` at the target, which stays
    well-formed by the same extension. Recursion and codomain stay left.

    Stated at the unfolded row shape (coerces to `TelRowInjT E n` by
    definitional equality wherever a row premise is needed). -/
def telRowInjT_of_piRowInj {E : ResolvedEnv} (hW : EnvWfT E)
    (hrow : PiRowInjT E) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {As As' : List (Expr Nat)} {B B' : Expr Nat}
    (h : TyConvT E n Γ (As.foldr Expr.pi B) (As'.foldr Expr.pi B'))
    (hlen : As.length = As'.length) :
    Nonempty (CtxConvT E n (telCtx Γ As) (telCtx Γ As')) ∧
    Nonempty (TyConvT E n (telCtx Γ As) B B') :=
  have h' := go hW hrow (envClosed_of_envWfT hW) hΓ (ctxConvT_refl Γ) As As' hlen h
  ⟨h'.elim fun p => ⟨p.1⟩, h'.elim fun p => ⟨p.2⟩⟩
where
  go (hW : EnvWfT E) (hrow : PiRowInjT E) (hcl : EnvClosed E) :
      {ΓL ΓR : LCtx} → CtxWfT E n ΓR → CtxConvT E n ΓL ΓR →
      (As As' : List (Expr Nat)) → As.length = As'.length →
      {B B' : Expr Nat} →
      TyConvT E n ΓL (As.foldr Expr.pi B) (As'.foldr Expr.pi B') →
      Nonempty (CtxConvT E n (telCtx ΓL As) (telCtx ΓR As') ×'
                TyConvT E n (telCtx ΓL As) B B')
    | _, _, _, hcc, [], [], _, _, _, h => ⟨⟨hcc, h⟩⟩
    | _, _, _, _, [], _ :: _, hlen, _, _, _ => nomatch hlen
    | _, _, _, _, _ :: _, [], hlen, _, _, _ => nomatch hlen
    | ΓL, ΓR, hΓR, hcc, A :: As, A' :: As', hlen, B, B', h => by
        have hlen' : As.length = As'.length := Nat.succ.inj hlen
        obtain ⟨u, v, ⟨cA⟩, ⟨cB⟩⟩ := hrow h
        have cA' : ConvT E n ΓR A A' (.sort u) := convT_ctx hcl hcc cA
        obtain ⟨tA⟩ := (DT009T_endpoints_envWfT hW hΓR cA').1
        obtain ⟨tA'⟩ := (DT009T_endpoints_envWfT hW hΓR cA').2
        have step : CtxConvT E n (.assumption A :: ΓL) (.assumption A' :: ΓR) :=
          .assumption hcc tA tA' cA'
        have hΓR' : CtxWfT E n (.assumption A' :: ΓR) :=
          .assumption _ _ _ hΓR tA'
        have h' : TyConvT E n (.assumption A :: ΓL)
            (As.foldr Expr.pi B) (As'.foldr Expr.pi B') := .of _ _ _ v cB
        obtain ⟨⟨hcc', hcod⟩⟩ := go hW hrow hcl hΓR' step As As' hlen' h'
        rw [telCtx_cons ΓL A As, telCtx_cons ΓR A' As']
        exact ⟨⟨hcc', hcod⟩⟩

#print axioms Rcic.Declarative.telRowInjT_of_piRowInj

end Rcic.Declarative
