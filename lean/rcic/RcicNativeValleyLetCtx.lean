import rcic.RcicNativeValleyFronts

/-!
# RcicNativeValleyLetCtx — certified transport across a converted `let` annotation
(Wall 1, `NativeConvValleys`, piece 16: `CertLetAnnCtx`)

`CertLetAnnCtx` (`RcicNativeValleyFronts`) is the `let` twin of `CertAssumpCtx`: a certified
step under `letBinding A v :: Γ` is a certified step under `letBinding A' v :: Γ` when
`A ~ A'`, the stored value `v` FIXED (a converted value is not transportable — `bvarZeta`
reads it — which is `LetJoin`'s business). It is the instance of the one transport recursion
`cstep_ctxTransport` (`RcicNativeValleyCtx`) at the relation `LetAnnCtxConvT`: pointwise
conversion of assumption types AND let annotations with every let value kept, i.e. the landed
`F8EtaK.AssumpCtxConvT` extended by the `letAnn` case (`LetAnnCtxConvT.ofAssump` embeds it).
Its `CtxTransport` interface: image in `CtxConvT` (the `letAnn` case is `CtxConvT.letBinding`
with the value conversion `refl` and the value retyped at `A'`), head-sharing, `drop`, and the
`let` lookup — at a `letAnn` binding the annotation moves by the stored conversion, elsewhere by
`refl`.

`certLetAnnCtx_of` discharges `CertLetAnnCtx` under `EnvClosed` and leaf transport along
`LetAnnCtxConvT` (which also yields the `AssumpCtxConvT` leaf transport, `hPEqC_ofAssump`).

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Pointwise context conversion of assumption types and let ANNOTATIONS, every let value kept
    (so `ParRedT.bvarZeta` reads the same stored value on both sides). The conversions are typed
    in the right tail, as in `F8EtaK.AssumpCtxConvT` / `CtxConvT`. -/
inductive LetAnnCtxConvT (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type
  | nil : LetAnnCtxConvT E n [] []
  | same {Γ Γ' : LCtx} (d : LocalDecl) (h : LetAnnCtxConvT E n Γ Γ') :
      LetAnnCtxConvT E n (d :: Γ) (d :: Γ')
  | assumption {Γ Γ' : LCtx} {A A' : Expr Nat} {u : Level} (h : LetAnnCtxConvT E n Γ Γ')
      (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) :
      LetAnnCtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ')
  | letAnn {Γ Γ' : LCtx} {A A' v : Expr Nat} {u : Level} (h : LetAnnCtxConvT E n Γ Γ')
      (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) (hv : HasTyT E n Γ' v A) :
      LetAnnCtxConvT E n (.letBinding A v :: Γ) (.letBinding A' v :: Γ')

/-- Reflexivity. -/
def letAnnCtxConvT_refl : (Γ : LCtx) → LetAnnCtxConvT E n Γ Γ
  | [] => .nil
  | d :: Γ => .same d (letAnnCtxConvT_refl Γ)

/-- `F8EtaK.AssumpCtxConvT` is the fragment without `letAnn`. -/
def LetAnnCtxConvT.ofAssump : {Γ Γ' : LCtx} → F8EtaK.AssumpCtxConvT E n Γ Γ' →
    LetAnnCtxConvT E n Γ Γ'
  | _, _, .nil => .nil
  | _, _, .same d h => .same d (LetAnnCtxConvT.ofAssump h)
  | _, _, .assumption h hA hA' hc => .assumption (LetAnnCtxConvT.ofAssump h) hA hA' hc

/-- The image in `CtxConvT`: the `letAnn` case is `CtxConvT.letBinding` with the value
    conversion `refl` and the value retyped at the converted annotation. -/
def letAnnCtxConvT_to_ctxConvT : {Γ Γ' : LCtx} → LetAnnCtxConvT E n Γ Γ' → CtxConvT E n Γ Γ'
  | _, _, .nil => .nil
  | _, _, .same d h => .same d (letAnnCtxConvT_to_ctxConvT h)
  | _, _, .assumption h hA hA' hc => .assumption (letAnnCtxConvT_to_ctxConvT h) hA hA' hc
  | _, _, @LetAnnCtxConvT.letAnn _ _ _ Γ' A A' v u h hA hA' hc hv =>
      .letBinding (letAnnCtxConvT_to_ctxConvT h) hA hA' hc (.conv Γ' v A A' u hv hc)
        (.refl Γ' v A hv)

/-- Dropping a common prefix. -/
def letAnnCtxConvT_drop : (k : Nat) → {Γ Γ' : LCtx} → LetAnnCtxConvT E n Γ Γ' →
    LetAnnCtxConvT E n (Γ.drop k) (Γ'.drop k)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | k + 1, _, _, .same _ h => letAnnCtxConvT_drop k h
  | k + 1, _, _, .assumption h _ _ _ => letAnnCtxConvT_drop k h
  | k + 1, _, _, .letAnn h _ _ _ _ => letAnnCtxConvT_drop k h

/-- The `let` lookup: the binding is at the same position with the same value; its annotation
    moves by the stored conversion (`letAnn`) or stays (`same`). -/
def letAnnCtxConvT_getLet : {Γ Γ' : LCtx} → LetAnnCtxConvT E n Γ Γ' → {i : Nat} →
    {B w : Expr Nat} → Γ.get? i = some (.letBinding B w) →
    Σ' (B' : Expr Nat), Γ'.get? i = some (.letBinding B' w) ×' TyConvT E n (Γ'.drop (i + 1)) B B'
  | _, _, .nil, _, _, _, h => nomatch h
  | _, _, .same _ _, 0, _, _, h => ⟨_, h, .refl _ _⟩
  | _, _, .same _ hcc, _ + 1, _, _, h => letAnnCtxConvT_getLet hcc h
  | _, _, .assumption .., 0, _, _, h => nomatch h
  | _, _, .assumption hcc _ _ _, _ + 1, _, _, h => letAnnCtxConvT_getLet hcc h
  | _, _, @LetAnnCtxConvT.letAnn _ _ _ Γ' A A' v u _ _ _ hc _, 0, _, _, h => by
      have h' : LocalDecl.letBinding A v = .letBinding _ _ := Option.some.inj h
      cases h'
      exact ⟨A', rfl, .of Γ' A A' u hc⟩
  | _, _, .letAnn hcc _ _ _ _, _ + 1, _, _, h => letAnnCtxConvT_getLet hcc h

/-- `LetAnnCtxConvT` offers the transport interface. -/
def letAnnCtxTransport : CtxTransport E n (LetAnnCtxConvT E n) where
  toCtx := fun h => letAnnCtxConvT_to_ctxConvT h
  same := fun d h => .same d h
  drop := fun k h => letAnnCtxConvT_drop k h
  getLet := fun h hg => letAnnCtxConvT_getLet h hg

/-- Certified context transport along `LetAnnCtxConvT`: the instance of `cstep_ctxTransport`. -/
def cstep_letAnnCtx (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T) :
    {Γ Γ' : LCtx} → LetAnnCtxConvT E n Γ Γ' → {a b T : Expr Nat} →
    {p : ParRedT PEq E n Γ a b T} → Certified p → CStep E n PEq Γ' a b T :=
  fun {_ _} hcc {_ _ _} {_} c =>
    cstep_ctxTransport (PEq := PEq) letAnnCtxTransport hcl (fun hcc' hp => hPEqC hcc' hp) hcc c

/-- `CertLetAnnCtx` discharged: transport under one converted head let annotation, the value
    fixed. -/
def certLetAnnCtx_of (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T) :
    CertLetAnnCtx E n PEq :=
  fun {Γ} {_ _ _} {_} hA hA' hc hv {_ _ _} s =>
    cstep_letAnnCtx (PEq := PEq) hcl (fun hcc hp => hPEqC hcc hp)
      (.letAnn (letAnnCtxConvT_refl Γ) hA hA' hc hv) s.cert

/-- Leaf transport along `LetAnnCtxConvT` gives leaf transport along `AssumpCtxConvT`. -/
def hPEqC_ofAssump
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    {Γ Γ' : LCtx} {p q T : Expr Nat} (hcc : F8EtaK.AssumpCtxConvT E n Γ Γ') (h : PEq Γ p q T) :
    PEq Γ' p q T :=
  hPEqC (LetAnnCtxConvT.ofAssump hcc) h

end Rcic.Declarative.NativeValleys
