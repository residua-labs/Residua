import rcic.RcicNativeValleyRows
import rcic.RcicEtaKDecide

/-!
# RcicNativeValleyCtx — certified transport across a context conversion
(Wall 1, `NativeConvValleys`, piece 6)

The certified twin of the landed `F8EtaK.parRedT_assumpCtx` (`RcicEtaKDecide.lean`), for an
abstract leaf, written ONCE over an abstract context relation `R` through the interface
`CtxTransport`: `R`'s image in `CtxConvT` (every typing moves by the landed `hasTyT_ctx`, every
certificate by `convT_ctx`, every `conv` chain by `F8EtaK.tyConvT_ctx`), closure under a shared
head declaration and under `drop`, and the `let` lookup — a let binding of `Γ` is a let binding
of `Γ'` at the same position with the SAME stored value (`bvarZeta` reads it), its annotation
moved by a type conversion below the binding (the stored value's step is re-indexed there).
The leaf moves by the hypothesis `hPEqC` for `R`. The two K arms are absent because certified
steps are K-free (`Certified.noK`).

`cstep_assumpCtx` is the instance at `F8EtaK.AssumpCtxConvT` (assumption types only, let
annotations fixed: `assumpCtxTransport`); `certAssumpCtx_of` discharges `CertAssumpCtx`
(`RcicNativeValleyRows`), the transport the `lam × lam` row consumes. The instance at the
relation that also converts let ANNOTATIONS is `RcicNativeValleyLetCtx` (`CertLetAnnCtx`).

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the interface a context relation offers the transport -/

/-- What the certified transport reads of a context relation `R`: its image in `CtxConvT`,
    closure under a shared head declaration, closure under `drop`, and the `let` lookup: a let
    binding of `Γ` is a let binding of `Γ'` at the same position with the SAME stored value, its
    annotation moved by a type conversion in the context below the binding. -/
structure CtxTransport (E : ResolvedEnv) (n : Nat) (R : LCtx → LCtx → Type) : Type where
  toCtx : ∀ {Γ Γ' : LCtx}, R Γ Γ' → CtxConvT E n Γ Γ'
  same : ∀ {Γ Γ' : LCtx} (d : LocalDecl), R Γ Γ' → R (d :: Γ) (d :: Γ')
  drop : ∀ {Γ Γ' : LCtx} (k : Nat), R Γ Γ' → R (Γ.drop k) (Γ'.drop k)
  getLet : ∀ {Γ Γ' : LCtx} {i : Nat} {A v : Expr Nat}, R Γ Γ' →
    Γ.get? i = some (.letBinding A v) →
    Σ' (A' : Expr Nat), Γ'.get? i = some (.letBinding A' v) ×' TyConvT E n (Γ'.drop (i + 1)) A A'

/-- Certified context transport along any relation with a `CtxTransport` (the landed
    `F8EtaK.parRedT_assumpCtx`, certificates carried, abstract leaf, abstract relation). -/
def cstep_ctxTransport {R : LCtx → LCtx → Type} (I : CtxTransport E n R) (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat}, R Γ Γ' → PEq Γ p q T → PEq Γ' p q T) :
    {Γ Γ' : LCtx} → R Γ Γ' → {a b T : Expr Nat} →
    {p : ParRedT PEq E n Γ a b T} → Certified p → CStep E n PEq Γ' a b T
  | _, Γ', hcc, _, _, _, _, @Certified.refl _ _ _ _ a A h c₀ =>
      let hccT := I.toCtx hcc
      ⟨.refl Γ' a A (hasTyT_ctx hcl hccT h), .refl (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.sortEq _ _ _ _ l₁ l₂ T h hl hr c₀ =>
      let hccT := I.toCtx hcc
      ⟨.sortEq Γ' l₁ l₂ T h (hasTyT_ctx hcl hccT hl) (hasTyT_ctx hcl hccT hr),
        .sortEq (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.consts _ _ _ _ r ls ls' T h hl hr c₀ =>
      let hccT := I.toCtx hcc
      ⟨.consts Γ' r ls ls' T h (hasTyT_ctx hcl hccT hl) (hasTyT_ctx hcl hccT hr),
        .consts (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.bvarZeta _ _ _ _ i A v v' T hget hv hl hr c₀ cv =>
      let hccT := I.toCtx hcc
      let ⟨A', hget', hcA⟩ := I.getLet hcc hget
      let ihv := cstep_ctxTransport I hcl hPEqC (I.drop (i + 1) hcc) cv
      let ihv' : CStep E n PEq (Γ'.drop (i + 1)) v v' A' := ihv.reindex hcA
      ⟨.bvarZeta Γ' i A' v v' T hget' ihv'.step (hasTyT_ctx hcl hccT hl) (hasTyT_ctx hcl hccT hr),
        .bvarZeta (convT_ctx hcl hccT c₀) ihv'.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.delta _ _ _ _ r ls m b T hres hbody htr hlen hwf hl hr c₀ =>
      let hccT := I.toCtx hcc
      ⟨.delta Γ' r ls m b T hres hbody htr hlen hwf (hasTyT_ctx hcl hccT hl)
        (hasTyT_ctx hcl hccT hr), .delta (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.app _ _ _ _ f f' a a' A B T₀ v w hf hc hB hTy ha hr c₀ cf ca =>
      let hccT := I.toCtx hcc
      let ihf := cstep_ctxTransport I hcl hPEqC hcc cf
      let iha := cstep_ctxTransport I hcl hPEqC hcc ca
      ⟨.app Γ' f f' a a' A B T₀ v w ihf.step (F8EtaK.tyConvT_ctx hcl hccT hc)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB) (hasTyT_ctx hcl hccT hTy)
        iha.step (hasTyT_ctx hcl hccT hr),
        .app (convT_ctx hcl hccT c₀) ihf.cert iha.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.beta _ _ _ _ A body body' arg arg' B u v w hA hB hTy hb ha hred
      c₀ cb ca =>
      let hccT := I.toCtx hcc
      let ihb := cstep_ctxTransport I hcl hPEqC (I.same (.assumption A) hcc) cb
      let iha := cstep_ctxTransport I hcl hPEqC hcc ca
      ⟨.beta Γ' A body body' arg arg' B u v w (hasTyT_ctx hcl hccT hA)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB) (hasTyT_ctx hcl hccT hTy)
        ihb.step iha.step (hasTyT_ctx hcl hccT hred),
        .beta (convT_ctx hcl hccT c₀) ihb.cert iha.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.lam _ _ _ _ A A' b b' B u v hA hA0 hB hb hr c₀ cb =>
      let hccT := I.toCtx hcc
      let ihb := cstep_ctxTransport I hcl hPEqC (I.same (.assumption A) hcc) cb
      ⟨.lam Γ' A A' b b' B u v (convT_ctx hcl hccT hA) (hasTyT_ctx hcl hccT hA0)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB) ihb.step (hasTyT_ctx hcl hccT hr),
        .lam (convT_ctx hcl hccT c₀) ihb.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.pi _ _ _ _ A A' B B' u v hA hc hB hcB hrt c₀ =>
      let hccT := I.toCtx hcc
      ⟨.pi Γ' A A' B B' u v (hasTyT_ctx hcl hccT hA) (convT_ctx hcl hccT hc)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB)
        (convT_ctx hcl (.same (.assumption A) hccT) hcB) (hasTyT_ctx hcl hccT hrt),
        .pi (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.letE _ _ _ _ A A' v v' b b' B u w hc hA hv hB hTy hb hrt
      c₀ cv cb =>
      let hccT := I.toCtx hcc
      let ihv := cstep_ctxTransport I hcl hPEqC hcc cv
      let ihb := cstep_ctxTransport I hcl hPEqC (I.same (.letBinding A v) hcc) cb
      ⟨.letE Γ' A A' v v' b b' B u w (convT_ctx hcl hccT hc) (hasTyT_ctx hcl hccT hA)
        ihv.step (hasTyT_ctx hcl (.same (.letBinding A v) hccT) hB) (hasTyT_ctx hcl hccT hTy)
        ihb.step (hasTyT_ctx hcl hccT hrt),
        .letE (convT_ctx hcl hccT c₀) ihv.cert ihb.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.zeta _ _ _ _ A v v' b b' B u w hA hv hB hTy hb hred c₀ cv cb =>
      let hccT := I.toCtx hcc
      let ihv := cstep_ctxTransport I hcl hPEqC hcc cv
      let ihb := cstep_ctxTransport I hcl hPEqC (I.same (.letBinding A v) hcc) cb
      ⟨.zeta Γ' A v v' b b' B u w (hasTyT_ctx hcl hccT hA) ihv.step
        (hasTyT_ctx hcl (.same (.letBinding A v) hccT) hB) (hasTyT_ctx hcl hccT hTy)
        ihb.step (hasTyT_ctx hcl hccT hred),
        .zeta (convT_ctx hcl hccT c₀) ihv.cert ihb.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.iotaSpine _ _ _ _ lhs lhs' rhs T hstep hι hred hrhs c₀ cs =>
      let hccT := I.toCtx hcc
      let ihs := cstep_ctxTransport I hcl hPEqC hcc cs
      ⟨.iotaSpine Γ' lhs lhs' rhs T ihs.step hι (hasTyT_ctx hcl hccT hred)
        (hasTyT_ctx hcl hccT hrhs), .iotaSpine (convT_ctx hcl hccT c₀) ihs.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.lit _ _ _ _ t T hexp c₀ =>
      let hccT := I.toCtx hcc
      ⟨.lit Γ' t T (hasTyT_ctx hcl hccT hexp), .lit (convT_ctx hcl hccT c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.eta _ _ _ _ f f' A B hf hl c₀ cf =>
      let hccT := I.toCtx hcc
      let ihf := cstep_ctxTransport I hcl hPEqC hcc cf
      ⟨.eta Γ' f f' A B ihf.step (hasTyT_ctx hcl hccT hl), .eta (convT_ctx hcl hccT c₀) ihf.cert⟩
  | _, Γ', hcc, _, _, _, _, @Certified.peq _ _ _ _ p q T h c₀ =>
      ⟨.peq Γ' p q T (hPEqC hcc h), .peq (convT_ctx hcl (I.toCtx hcc) c₀)⟩
  | _, Γ', hcc, _, _, _, _, @Certified.conv _ _ _ _ a b A A' h hc c₀ ch =>
      let hccT := I.toCtx hcc
      let ih := cstep_ctxTransport I hcl hPEqC hcc ch
      ⟨.conv Γ' a b A A' ih.step (F8EtaK.tyConvT_ctx hcl hccT hc),
        .conv (convT_ctx hcl hccT c₀) ih.cert⟩

/-- `F8EtaK.AssumpCtxConvT` offers the interface: let bindings are kept verbatim
    (`assumpCtxConvT_get_letBinding`), so the annotation conversion is `TyConvT.refl`. -/
def assumpCtxTransport : CtxTransport E n (F8EtaK.AssumpCtxConvT E n) where
  toCtx := fun h => F8EtaK.assumpCtxConvT_to_ctxConvT h
  same := fun d h => .same d h
  drop := fun k h => F8EtaK.assumpCtxConvT_drop k h
  getLet := fun h hg => ⟨_, F8EtaK.assumpCtxConvT_get_letBinding h hg, .refl _ _⟩

/-- Certified context transport across assumption conversions (the landed
    `F8EtaK.parRedT_assumpCtx`, certificates carried, abstract leaf): the instance of
    `cstep_ctxTransport` at `assumpCtxTransport`. -/
def cstep_assumpCtx (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        F8EtaK.AssumpCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T) :
    {Γ Γ' : LCtx} → F8EtaK.AssumpCtxConvT E n Γ Γ' → {a b T : Expr Nat} →
    {p : ParRedT PEq E n Γ a b T} → Certified p → CStep E n PEq Γ' a b T :=
  fun {_ _} hcc {_ _ _} {_} c =>
    cstep_ctxTransport (PEq := PEq) assumpCtxTransport hcl (fun hcc' hp => hPEqC hcc' hp) hcc c

/-- `CertAssumpCtx` discharged: transport under one converted head assumption. -/
def certAssumpCtx_of (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        F8EtaK.AssumpCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T) :
    CertAssumpCtx E n PEq :=
  fun {Γ} {_ _} {_} hA hA' hc {_ _ _} s =>
    cstep_assumpCtx (PEq := PEq) hcl (fun hcc hp => hPEqC hcc hp)
      (.assumption (F8EtaK.assumpCtxConvT_refl Γ) hA hA' hc) s.cert

end Rcic.Declarative.NativeValleys
