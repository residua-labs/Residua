import rcic.RcicParRedTPins
import rcic.RcicPEqT

/-!
# `pinLoopT` — the plain Loop fixture for D

The Loop redex `R = rec M m x` at the arbitrary major `x` is D's hardest
test case because its ι★ reduct **re-embeds the redex itself**:
`R = rec M m x ⇒ m x (rec M m x) = m x R` — the minor
`λ (l : Loop) (ih : M l). ih → ih` inserts its recursive-field argument
`ih = rec M m l` back into the head, so the reduct `m x R` contains `R` as
a subterm and `m x R` is itself a redex-class term (its inner `R` fires).

The fixture measures `ParRedT`'s divergent reducts of `R` modulo
`PEqT` (`≈P`, `RcicPEqT` — S3's `∃ d d', d ≈P d'` join conclusion).
`ParRedT`'s `PEq` parameter is type-indexed; `PEqT` is not — the fixture
instantiates the parameter with the T-ignoring adapter `loopPEq`.

* `pinLoopT_inner` — the second contraction `m x R ⇒ m x (m x R)` —
  `ParRedT.app` congruence on `m x □` with `R ⇒ m x R` in the hole —
  **axiom-free**.
* `pinLoopT_join` — `R`'s reducts `m x R` and `m x (m x R)` join at
  `d = d' = m x (m x R)` by `≈P`-`refl`. **Axiom-free.**
* `pinLoopT_join_RS` — `R`'s redex-vs-iota pair `R`/`m x R` join at
  `d = d' = m x R` trivially (the redex is already the join).
* `pinLoopT_shape` — `R ≠ m x R`: the self-embedding is a genuine
  divergence, not a reflexivity.
* `pinLoopT_peq_debt` — the honest negative half: any ≈P-collapse
  `R ≈ m x R` *without* continuing to a common reduct must pass a
  `proof` leaf somewhere on the spine — the `const 62`/`m` heads are
  disjoint shapes so `.app`-congruence recursion ends at
  `PEqT (app (const 62 u) M) (bvar 1)` where only `proof` survives.
  The leaf deposits `⟨s, T', T' : sort 0, s : T'⟩` — a Prop typing a
  Loop subterm — the exact debt `W-F05b-Loop` (the `TypedRowsWf` open
  wall) names.
* `pinLoopCtxWf` — `pinLoopCtx` IS `CtxWfT` (dt025's Γ₀ restatement:
  entries reference later/outer positions; `m`'s stored type legally
  types `M` at its tail). What remains a premise is `TypedRowsWf`
  alone — the `AnnEnvA` supplier is refuted by
  `pinLoop_not_propElimStruct`.

The join is syntactic (`d = d'`): the cyclic class is joinable by
continued contraction — `R`'s equivalence class is a single ≈P-leaf-free
cone. `closure_claim` unchanged (0).
-/

namespace Rcic.Declarative

/-- The `≈P` relation at the Loop env, adapted to `ParRedT`'s
    type-indexed `PEq` parameter — `PEqT` carries no type index, so
    the `T` is ignored (the `peq` leaf never fires in this fixture). -/
private abbrev loopPEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type :=
  fun Γ p q _ => PEqT pinLoopEnvT 1 Γ p q

/-- `R` — the Loop redex `rec M m x` at the arbitrary `pinLoopCtx` major. -/
def loopDR : Expr Nat :=
  recCall pinLoopRecHead [.bvar 2, .bvar 1] (.bvar 0)

/-- `S` — the ι★ reduct `m x (rec M m x)`, re-embedding `R` in the
    recursive-field argument slot. -/
def loopDS : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) loopDR

/-- `wLoopK`'s iota RHS *is* `m x R`. -/
theorem wLoopRhs_eq : wLoopRhs = loopDS := rfl

/-- `S₂` — `S`'s own reduct under the same ι★ step, `m x S`, with `S`
    already in the recursive-field slot. -/
def loopDS2 : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) loopDS

/-- `S`'s typing restated at `loopDS`. -/
def loopDSTy : HasTyT pinLoopEnvT 1 pinLoopCtx loopDS loopMx :=
  wLoopRhs_eq ▸ loopRhsTyT

private def loopAppT2 {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTyT pinLoopEnvT 1 Γ f (.pi A B))
    (ha : HasTyT pinLoopEnvT 1 Γ a A) :
    HasTyT pinLoopEnvT 1 Γ (.app f a) (instantiate0 a B) :=
  .app Γ f a A B hf ha

/-- `m x : Π ih : M x, M (mk x)` — the minor applied to the major. -/
def loopDMxTy : HasTyT pinLoopEnvT 1 pinLoopCtx
    (.app (.bvar 1) (.bvar 0)) loopMxTy := by
  have hm : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have hx : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 0) (.const 60 []) :=
    .bvar _ 0 _ rfl
  exact loopAppT2 hm hx

/-- `S₂ : M x` — the doubly-contracted reduct types at the motive. -/
def loopDS2Ty : HasTyT pinLoopEnvT 1 pinLoopCtx loopDS2 loopMx := by
  have h5 : HasTyT pinLoopEnvT 1 pinLoopCtx loopDS2
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) :=
    loopAppT2 loopDMxTy loopDSTy
  exact .conv _ _ _ _ _ h5 loopIndexConv

/-- `R ⇒ S` — the ι★ contraction, at `loopPEq` as the leaf's relation. -/
def pinLoopT_step :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDR loopDS loopMx :=
  wLoopRhs_eq ▸ pinParRedT_iotaStarK_loop

/-- `S ⇒ S₂` — the second contraction: the embedded `R` fires inside the
    recursive-field slot. `ParRedT.app` congruence on the spine
    `m x □`, then `.conv` back to `M x`. -/
def pinLoopT_inner :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS loopDS2 loopMx := by
  have hM3 : HasTyT pinLoopEnvT 1 (.assumption loopMx :: pinLoopCtx)
      (.bvar 3) loopMotT := .bvar _ 3 _ rfl
  have hx1 : HasTyT pinLoopEnvT 1 (.assumption loopMx :: pinLoopCtx)
      (.bvar 1) (.const 60 []) := .bvar _ 1 _ rfl
  have hmkx : HasTyT pinLoopEnvT 1 (.assumption loopMx :: pinLoopCtx)
      (.app (.const 61 []) (.bvar 1)) (.const 60 []) :=
    .app _ _ _ _ _ (.const _ 61 [] pinLoopMkT rfl rfl rfl) hx1
  have hB : HasTyT pinLoopEnvT 1 (.assumption loopMx :: pinLoopCtx)
      (.app (.bvar 3) (.app (.const 61 []) (.bvar 1))) (.sort (.param 0)) :=
    .app _ _ _ _ _ hM3 hmkx
  have hM2 : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hmkx0 : HasTyT pinLoopEnvT 1 pinLoopCtx
      (.app (.const 61 []) (.bvar 0)) (.const 60 []) :=
    .app _ _ _ _ _ (.const _ 61 [] pinLoopMkT rfl rfl rfl) (.bvar _ 0 _ rfl)
  have hTy : HasTyT pinLoopEnvT 1 pinLoopCtx
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) (.sort (.param 0)) :=
    .app _ _ _ _ _ hM2 hmkx0
  have h5 : HasTyT pinLoopEnvT 1 pinLoopCtx loopDS2
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) :=
    loopAppT2 loopDMxTy loopDSTy
  have step : ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS loopDS2
      (instantiate0 loopDR (.app (.bvar 3) (.app (.const 61 []) (.bvar 1)))) :=
    .app pinLoopCtx (.app (.bvar 1) (.bvar 0)) (.app (.bvar 1) (.bvar 0))
      loopDR loopDS loopMx
      (.app (.bvar 3) (.app (.const 61 []) (.bvar 1))) loopMxTy
      (.param 0) (.param 0)
      (.refl _ _ _ loopDMxTy) (.refl _ _) hB hTy
      pinLoopT_step h5
  exact .conv pinLoopCtx _ _ _ _ step (.of _ _ _ _ loopIndexConv)

/-- `R ⇒* S`. -/
def pinLoopT_star_RS :
    ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDR loopDS loopMx :=
  .tail pinLoopT_step (.refl _ _ _ loopDSTy)

/-- `S ⇒* S₂`. -/
def pinLoopT_star_SS2 :
    ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS loopDS2 loopMx :=
  .tail pinLoopT_inner (.refl _ _ _ loopDS2Ty)

/-- `R ⇒* S₂`. -/
def pinLoopT_star_RS2 :
    ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDR loopDS2 loopMx :=
  .tail pinLoopT_step pinLoopT_star_SS2

/-- **D, positive, for `R`'s redex-vs-iota pair.** `R` and `m x R` —
    the source and its ι★ reduct — join at `d = d' = m x R`. -/
def pinLoopT_join_RS : ∃ d d',
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDR d loopMx) ∧
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS d' loopMx) ∧
    Nonempty (PEqT pinLoopEnvT 1 pinLoopCtx d d') :=
  ⟨loopDS, loopDS, ⟨pinLoopT_star_RS⟩,
    ⟨.refl _ _ _ loopDSTy⟩, ⟨PEqT.refl _⟩⟩

/-- **D, positive, for the divergent pair.** `R ⇒ S` and `S ⇒ S₂`
    (the re-embedded redex firing inside `S`) — the divergent reducts
    `S = m x R` and `S₂ = m x (m x R)` join at `d = d' = S₂` modulo
    `≈P`-`refl`. The Loop cyclic class is joinable by continued
    contraction: every reduct in `R`'s class contracts toward the
    same cone `m x ·`. -/
def pinLoopT_join : ∃ d d',
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS d loopMx) ∧
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx
      loopDS2 d' loopMx) ∧
    Nonempty (PEqT pinLoopEnvT 1 pinLoopCtx d d') :=
  ⟨loopDS2, loopDS2, ⟨pinLoopT_star_SS2⟩,
    ⟨.refl _ _ _ loopDS2Ty⟩, ⟨PEqT.refl _⟩⟩

/-- `R ≠ S` — the self-embedding is a genuine divergence, not `refl`. -/
theorem pinLoopT_shape : loopDR ≠ loopDS := by
  decide

/-- **D, honest negative half.** Any ≈P-collapse of `R` to `m x R`
    *without* continuing to a common reduct must pass a `proof` leaf:
    the `const 62`-headed spine and the `m`-headed spine are disjoint
    shapes, so `.app`-congruence recursion on `PEqT R (m x R)`
    reaches `PEqT (app (const 62 u) M) (bvar 1)` where every clause
    but `proof` is shape-dead. The leaf deposits
    `⟨s, T', T' : sort 0, s : T'⟩` — a Prop `T'` typing a Loop
    subterm. Refuting that deposit needs `sortRow`/`piRow`-scope
    inversion, which is exactly the `W-F05b-Loop` open wall — rows are
    a premise here (`pinLoopCtxWf` supplies the `CtxWfT` leg; the
    `TypedRowsWf` itself is not derivable at `pinLoopEnvT`). -/
theorem pinLoopT_peq_debt
    (h : Nonempty (PEqT pinLoopEnvT 1 pinLoopCtx loopDR loopDS)) :
    ∃ (s T' : Expr Nat),
      Nonempty (HasTyT pinLoopEnvT 1 pinLoopCtx T' (.sort .zero)) ∧
      Nonempty (HasTyT pinLoopEnvT 1 pinLoopCtx s T') := by
  obtain ⟨h⟩ := h
  cases h
  case proof P Q hP hQ hp hq => exact ⟨_, _, ⟨hP⟩, ⟨hp⟩⟩
  case app hf ha =>
    cases hf
    case proof P Q hP hQ hp hq => exact ⟨_, _, ⟨hP⟩, ⟨hp⟩⟩
    case app hf2 ha2 =>
      cases hf2
      case proof P Q hP hQ hp hq => exact ⟨_, _, ⟨hP⟩, ⟨hp⟩⟩

/-- `pinLoopCtx` IS `CtxWfT` — entries reference later (outer) positions:
    `m`'s stored `loopMinorT` types `M` at tail-index 0, `x`'s and `M`'s
    entries are closed/`const`. This is dt025's Γ₀ restatement — the
    fixture needs no reindexing. The `peq_debt` inversion's Prop-deposit
    is the only premise-class rows (`sortRow`/`piRow`, `CtxWfT`-premised)
    would refute; rows themselves remain the `W-F05b-Loop` premise (the
    `AnnEnvA` supplier route is refuted by `pinLoop_not_propElimStruct`). -/
def pinLoopCtxWf : Nonempty (CtxWfT pinLoopEnvT 1 pinLoopCtx) := by
  have h0 : HasTyT pinLoopEnvT 1 [] (.const 60 []) (.sort .zero) :=
    .const _ 60 [] pinLoopFamT rfl rfl rfl
  have hM : HasTyT pinLoopEnvT 1 [] loopMotT
      (.sort (.imax .zero (.succ (.param 0)))) :=
    .pi _ _ _ _ _ h0 (.sort _ _)
  have hMwf : CtxWfT pinLoopEnvT 1 [.assumption loopMotT] :=
    .assumption _ _ _ .nil hM
  have h1 : HasTyT pinLoopEnvT 1 [.assumption loopMotT] (.const 60 [])
      (.sort .zero) :=
    .const _ 60 [] pinLoopFamT rfl rfl rfl
  have h2 : HasTyT pinLoopEnvT 1 [.assumption (.const 60 []), .assumption loopMotT]
      (.bvar 1) loopMotT := .bvar _ 1 _ rfl
  have hMl : HasTyT pinLoopEnvT 1 [.assumption (.const 60 []), .assumption loopMotT]
      (.app (.bvar 1) (.bvar 0)) (.sort (.param 0)) :=
    .app _ _ _ _ _ h2 (.bvar _ 0 _ rfl)
  have h3 : HasTyT pinLoopEnvT 1
      [.assumption (.app (.bvar 1) (.bvar 0)), .assumption (.const 60 []),
        .assumption loopMotT] (.bvar 2) loopMotT := .bvar _ 2 _ rfl
  have h4 : HasTyT pinLoopEnvT 1
      [.assumption (.app (.bvar 1) (.bvar 0)), .assumption (.const 60 []),
        .assumption loopMotT] (.bvar 1) (.const 60 []) := .bvar _ 1 _ rfl
  have h5 : HasTyT pinLoopEnvT 1
      [.assumption (.app (.bvar 1) (.bvar 0)), .assumption (.const 60 []),
        .assumption loopMotT] (.app (.const 61 []) (.bvar 1)) (.const 60 []) :=
    .app _ _ _ _ _ (.const _ 61 [] pinLoopMkT rfl rfl rfl) h4
  have h6 : HasTyT pinLoopEnvT 1
      [.assumption (.app (.bvar 1) (.bvar 0)), .assumption (.const 60 []),
        .assumption loopMotT] (.app (.bvar 2) (.app (.const 61 []) (.bvar 1)))
      (.sort (.param 0)) :=
    .app _ _ _ _ _ h3 h5
  have hMinor : HasTyT pinLoopEnvT 1 [.assumption loopMotT] loopMinorT
      (.sort (.imax .zero (.imax (.param 0) (.param 0)))) :=
    .pi _ _ _ _ _ h1 (.pi _ _ _ _ _ hMl h6)
  have hmwf : CtxWfT pinLoopEnvT 1
      [.assumption loopMinorT, .assumption loopMotT] :=
    .assumption _ _ _ hMwf hMinor
  have hx : HasTyT pinLoopEnvT 1 [.assumption loopMinorT, .assumption loopMotT]
      (.const 60 []) (.sort .zero) :=
    .const _ 60 [] pinLoopFamT rfl rfl rfl
  exact ⟨.assumption _ _ _ hmwf hx⟩

/-! ## (9) the TYPE-LEVEL Loop — `X ⇒* X → X` by `iotaStarK` + 2β

dt025's Γ₀ = `[t : Loop]` (`pinLoopCtx0`). The type-level
`X = erase pinLoopA = rec.{1} (λ_.Prop) (λ l ih. ih→ih) t` is itself a
recursor redex: the SAME `iotaStarK` arm that contracts `rec M m x` fires
on the VARIABLE major `t` with `Tm = Loop`, and because `preMajor`
carries the LITERAL motive/minor (the term-level pin's
`[bvar 2, bvar 1]` were ctx-variables), the reduct `m̂ t X` unfolds by
two `β` steps:

    X  ⇒  m̂ t X                          (ι★K, variable major)
       ⇒  (λ (ih : M̂ t). ih → ih) X      (β — `inst0 t` is the self-subst)
       ⇒  pi X (lift 0 1 X)               (β — the `ih→ih` body)
       =  X → lift X = erase pinLoopArrow

Every step is indexed at `sort 0`: the gate typings conv through the
motive's β (`M̂ a ≡ Prop`, `ConvT.beta`), the β/Π sorts through
`imax 0 0 =ₙ 0` (`ConvT.sorts`).

**DeepSeek-pro's adversarial check answered:** the UNTYPED `ParRed` has
no `iotaStarK`, so `parRedJoinable_pinLoop_false`'s disjoint reduct
classes don't transfer — the TYPED `ParRedT` reaches the self-arrow.
`closure_claim` 0. -/

/-- dt025's Γ₀ — `[t : Loop]`, the type-level Loop's one-binder ctx. -/
def pinLoopCtx0 : LCtx := [.assumption (.const 60 [])]

/-- the erased motive `λ (_ : Loop). Prop`. -/
private def loopMotE : Expr Nat := Ann.erase Ann.pinLoopM
/-- the erased minor `λ (l : Loop) (ih : M l). ih → ih`. -/
private def loopMinE : Expr Nat := Ann.erase Ann.pinLoopm
/-- the inner λ `λ (ih : M l). ih → ih` — `loopMinE`'s body. -/
private def loopIhE : Expr Nat := Ann.erase Ann.pinLoopIhLam
/-- `ih → ih` — the inner λ's body. -/
private def loopBodyE : Expr Nat := Ann.erase Ann.pinLoopBody
/-- `Π (ih : M l). M (mk l)`, erased — `loopIhE`'s type. -/
private def loopIhPiE : Expr Nat := Ann.erase Ann.pinLoopIhPiM
/-- `Π (l : Loop). Π (ih : M l). M (mk l)`, erased — `loopMinE`'s type. -/
private def loopMinDomE : Expr Nat := Ann.erase Ann.pinLoopMinorDomM
/-- `X = rec.{1} M̂ m̂ t` — `erase pinLoopA`. -/
private def loopXE : Expr Nat := Ann.erase Ann.pinLoopA

/-- the `iotaStarK` witness for the TYPE-level Loop — `wLoopK`'s template
    at the redex's literal level `[succ 0]` and with the literal
    motive/minor in `preMajor`. Every premise field re-checks by `rfl`:
    `recDoms`/`hpeelRec`/`hmajorTy` read the RAW polymorphic stored type
    (`ls`-independent, 00 §20.6), `ctorAfterParams`/`instantiateLevels`
    see `mk`'s level-free `Loop → Loop`. -/
def wLoopKA : IotaWitness pinLoopEnvT where
  recRef := 62
  ctorRef := 61
  ls := [.succ .zero]
  lsC := []
  recMember := pinLoopRecT
  ctorMember := pinLoopMkT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [loopMotE, loopMinE]
  fields := [.bvar 0]
  ctorParams := []
  kinds := [.directRec]
  minor := loopMinE
  hlen := rfl
  familyRef := 60
  famMember := pinLoopFamT
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 60 []]
  ctorResult := .const 60 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [loopMotT, loopMinorT, .const 60 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 60 []) (.const 60 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `Loop : sort 0` in Γ₀ — `hTm0`, the `hA`s, and the `irr`-side evidence. -/
private def loopFamTy0 {Γ : LCtx} : HasTyT pinLoopEnvT 1 Γ (.const 60 [])
    (.sort .zero) :=
  .const _ 60 [] pinLoopFamT rfl rfl rfl

/-- `t : Loop` in Γ₀ — `hmajor`. -/
private def loopVarTy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0 (.bvar 0)
    (.const 60 []) :=
  .bvar _ 0 _ rfl

/-- `mk`'s head `const 61 : Loop → Loop` at any ctx. -/
private def loopMkHdTy {Γ : LCtx} : HasTyT pinLoopEnvT 1 Γ (.const 61 [])
    (.pi (.const 60 []) (.const 60 [])) :=
  .const _ 61 [] pinLoopMkT rfl rfl rfl

/-- `mk t : Loop` — the type-level ctor-spine major (`hmk`). -/
private def loopMkAppTy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (.app (.const 61 []) (.bvar 0)) (.const 60 []) :=
  .app _ _ _ _ _ loopMkHdTy loopVarTy0

/-- `M̂ = λ(_:Loop).Prop : Π(_:Loop).Sort 1` at any ctx. -/
private def loopMotTyETy {Γ : LCtx} : HasTyT pinLoopEnvT 1 Γ loopMotE
    (.pi (.const 60 []) (.sort (.succ .zero))) :=
  .lam _ (.const 60 []) .zero (.sort .zero) (.sort (.succ .zero))
    loopFamTy0 (.sort _ .zero)

/-- `M̂ a : sort 1` — the motive application. -/
private def loopMotAppTy {Γ : LCtx} {a : Expr Nat}
    (ha : HasTyT pinLoopEnvT 1 Γ a (.const 60 [])) :
    HasTyT pinLoopEnvT 1 Γ (.app loopMotE a) (.sort (.succ .zero)) :=
  .app _ _ _ _ _ loopMotTyETy ha

/-- `M̂ a ≡ Prop` — the motive β at `ConvT` (index `sort 1`). -/
private def loopMotConvB {Γ : LCtx} {a : Expr Nat}
    (ha : HasTyT pinLoopEnvT 1 Γ a (.const 60 [])) :
    ConvT pinLoopEnvT 1 Γ (.app loopMotE a) (.sort .zero)
      (.sort (.succ .zero)) :=
  .beta _ (.const 60 []) (.sort .zero) a (.sort (.succ .zero)) .zero
    loopFamTy0 (.sort _ .zero) ha

/-- `e : M̂ a` re-typed at `Prop` — the `hlhs`/`hlι`/`hrhs` sort move. -/
private def loopAtProp {Γ : LCtx} {e a : Expr Nat}
    (ha : HasTyT pinLoopEnvT 1 Γ a (.const 60 []))
    (he : HasTyT pinLoopEnvT 1 Γ e (.app loopMotE a)) :
    HasTyT pinLoopEnvT 1 Γ e (.sort .zero) :=
  .conv _ _ _ _ _ he (loopMotConvB ha)

/-- `e : Prop` re-typed at `M̂ a` — the motive-read-back move. -/
private def loopAtM {Γ : LCtx} {e a : Expr Nat}
    (ha : HasTyT pinLoopEnvT 1 Γ a (.const 60 []))
    (he : HasTyT pinLoopEnvT 1 Γ e (.sort .zero)) :
    HasTyT pinLoopEnvT 1 Γ e (.app loopMotE a) :=
  .conv _ _ _ _ _ he (.symm _ _ _ _ (loopMotConvB ha))

/-- `sort (imax 0 0) ≡ sort 0` — `ConvT.sorts`, index `sort (succ (imax 0 0))`. -/
private def loopImaxConv {Γ : LCtx} :
    ConvT pinLoopEnvT 1 Γ (.sort (.imax .zero .zero)) (.sort .zero)
      (.sort (.succ (.imax .zero .zero))) :=
  .sorts _ _ _ (fun _ => rfl)

/-- the same at `TyConvT` — the step-3 index move. -/
private def loopImaxTyConv {Γ : LCtx} :
    TyConvT pinLoopEnvT 1 Γ (.sort (.imax .zero .zero)) (.sort .zero) :=
  .of _ _ _ _ loopImaxConv

/-- `e : sort (imax 0 0)` re-typed at `sort 0`. -/
private def loopAtImax {Γ : LCtx} {e : Expr Nat}
    (he : HasTyT pinLoopEnvT 1 Γ e (.sort (.imax .zero .zero))) :
    HasTyT pinLoopEnvT 1 Γ e (.sort .zero) :=
  .conv _ _ _ _ _ he loopImaxConv

/-- `ih → ih : sort (imax 0 0)` under `[ih : M̂ l, l : Loop] ++ Γ` —
    `pinLoopBodyTy`'s erased twin (bvar-lookups stay in the literal
    prefix, so the tail is free). -/
private def loopBodyTyG {Γ : LCtx} :
    HasTyT pinLoopEnvT 1
      (.assumption (.app loopMotE (.bvar 0)) :: .assumption (.const 60 []) :: Γ)
      loopBodyE (.sort (.imax .zero .zero)) := by
  have hb1 : HasTyT pinLoopEnvT 1
      (.assumption (.bvar 0) :: .assumption (.app loopMotE (.bvar 0)) ::
        .assumption (.const 60 []) :: Γ) (.bvar 1) (.sort .zero) :=
    .conv _ _ _ _ _ (.bvar _ 1 _ rfl) (loopMotConvB (.bvar _ 2 _ rfl))
  exact .pi _ (.bvar 0) .zero (.bvar 1) .zero
    (.conv _ _ _ _ _ (.bvar _ 0 _ rfl) (loopMotConvB (.bvar _ 1 _ rfl))) hb1

/-- `ih → ih : M̂ (mk l)` — the inner-pi codomain typing. -/
private def loopBodyAtMG {Γ : LCtx} :
    HasTyT pinLoopEnvT 1
      (.assumption (.app loopMotE (.bvar 0)) :: .assumption (.const 60 []) :: Γ)
      loopBodyE (.app loopMotE (.app (.const 61 []) (.bvar 1))) :=
  loopAtM (.app _ _ _ _ _ loopMkHdTy (.bvar _ 1 _ rfl)) (loopAtImax loopBodyTyG)

/-- the inner λ `λ(ih:M̂ l). ih→ih : Π(ih:M̂ l). M̂(mk l)` under a `Loop`
    binder — `pinLoopIhLamTy`'s erased twin. -/
private def loopIhLamTyG {Γ : LCtx} :
    HasTyT pinLoopEnvT 1 (.assumption (.const 60 []) :: Γ) loopIhE loopIhPiE :=
  .lam _ (.app loopMotE (.bvar 0)) (.succ .zero) loopBodyE
    (.app loopMotE (.app (.const 61 []) (.bvar 1)))
    (loopMotAppTy (.bvar _ 0 _ rfl)) loopBodyAtMG

/-- the minor `m̂ : Π(l:Loop). Π(ih:M̂ l). M̂(mk l)` at any ctx —
    `pinLoopmTy`'s erased twin. -/
private def loopMinTyG {Γ : LCtx} : HasTyT pinLoopEnvT 1 Γ loopMinE loopMinDomE :=
  .lam _ (.const 60 []) .zero loopIhE loopIhPiE loopFamTy0 loopIhLamTyG

/-- `loopIhPiE`'s sort under a `Loop` binder — `imax (succ 0) (succ 0)`. -/
private def loopIhPiTy0L {Γ : LCtx} : HasTyT pinLoopEnvT 1
    (.assumption (.const 60 []) :: Γ) loopIhPiE
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ (.app loopMotE (.bvar 0)) (.succ .zero)
    (.app loopMotE (.app (.const 61 []) (.bvar 1))) (.succ .zero)
    (loopMotAppTy (.bvar _ 0 _ rfl))
    (loopMotAppTy (.app _ _ _ _ _ loopMkHdTy (.bvar _ 1 _ rfl)))

/-- `loopIhPiE`'s sort at Γ₀. -/
private def loopIhPiTy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0 loopIhPiE
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  loopIhPiTy0L

/-- `rec.{1}`'s head at its `[succ 0]` instance, any ctx. -/
private def loopRecHdTy {Γ : LCtx} : HasTyT pinLoopEnvT 1 Γ
    (.const 62 [.succ .zero]) (instantiateLevels [.succ .zero] pinLoopRecT.mtype) :=
  .const _ 62 [.succ .zero] pinLoopRecT rfl rfl (by decide)

/-- `rec.{1} M̂ m̂ : Π (t : Loop). M̂ t` — the two-arg rec-spine. -/
private def loopFETy {Γ : LCtx} :
    HasTyT pinLoopEnvT 1 Γ (.app (.app (.const 62 [.succ .zero]) loopMotE) loopMinE)
      (.pi (.const 60 []) (.app loopMotE (.bvar 0))) := by
  have h1 : HasTyT pinLoopEnvT 1 Γ (.app (.const 62 [.succ .zero]) loopMotE)
      (.pi loopMinDomE (.pi (.const 60 []) (.app loopMotE (.bvar 0)))) :=
    .app _ _ _ _ _ loopRecHdTy loopMotTyETy
  exact .app _ _ _ _ _ h1 loopMinTyG

/-- `rec.{1} M̂ m̂ a : M̂ a` — the full rec-spine at `a : Loop`. -/
private def loopRecAppTy {Γ : LCtx} {a : Expr Nat}
    (ha : HasTyT pinLoopEnvT 1 Γ a (.const 60 [])) :
    HasTyT pinLoopEnvT 1 Γ
      (recCall (.const 62 [.succ .zero]) [loopMotE, loopMinE] a)
      (.app loopMotE a) := by
  exact .app _ _ _ _ _ loopFETy ha

/-- `X : M̂ t` — the type-level redex, typed. -/
private def loopXTy : HasTyT pinLoopEnvT 1 pinLoopCtx0 loopXE
    (.app loopMotE (.bvar 0)) :=
  loopRecAppTy loopVarTy0

/-- `X : sort 0` — `hlhs` (motive β to `Prop`). -/
private def loopXSort : HasTyT pinLoopEnvT 1 pinLoopCtx0 loopXE (.sort .zero) :=
  loopAtProp loopVarTy0 loopXTy

/-- the synthesized redex `rec M̂ m̂ (mk t) : M̂ (mk t)`. -/
private def loopILhsTy : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (recCall (.const 62 [.succ .zero]) [loopMotE, loopMinE]
      (.app (.const 61 []) (.bvar 0)))
    (.app loopMotE (.app (.const 61 []) (.bvar 0))) :=
  loopRecAppTy loopMkAppTy0

/-- the synthesized redex at `sort 0` — `hlι`. -/
private def loopILhsSort : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (recCall (.const 62 [.succ .zero]) [loopMotE, loopMinE]
      (.app (.const 61 []) (.bvar 0))) (.sort .zero) :=
  loopAtProp loopMkAppTy0 loopILhsTy

/-- `m̂ t X : M̂ (mk t)` — the iota RHS, typed. -/
private def loopRRhsTy : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (.app (.app loopMinE (.bvar 0)) loopXE)
    (.app loopMotE (.app (.const 61 []) (.bvar 0))) := by
  have hmm : HasTyT pinLoopEnvT 1 pinLoopCtx0 (.app loopMinE (.bvar 0))
      (.pi (.app loopMotE (.bvar 0))
        (.app loopMotE (.app (.const 61 []) (.bvar 1)))) :=
    .app _ _ _ _ _ loopMinTyG loopVarTy0
  exact .app _ _ _ _ _ hmm loopXTy

/-- the iota RHS at `sort 0` — `hrhs`. -/
private def loopRRhsSort : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (.app (.app loopMinE (.bvar 0)) loopXE) (.sort .zero) :=
  loopAtProp loopMkAppTy0 loopRRhsTy

/-- `loopIhE`'s Γ₀-typing — `inst0 t` on `loopIhLamTyG` is the
    self-substitution (the `lam`'s free `l` IS `bvar 0`). -/
private def loopIhETy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (instantiate0 (.bvar 0) loopIhE) (instantiate0 (.bvar 0) loopIhPiE) :=
  hasTyT_subst0_of_envWfT pinLoopGroupRecWfT loopIhLamTyG loopVarTy0

/-- STEP 1 — `X ⇒ m̂ t X` — `iotaStarK` on the variable major `t`:
    the typed K-gate lands (`hmajor`/`hmk` at `Tm = Loop`,
    singleton-`Prop` `hsel`, `.ofU` at the synthesized `mk`-spine),
    both endpoints re-typed at `sort 0` through the motive β. -/
private def loopXIotaStep :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      loopXE (.app (.app loopMinE (.bvar 0)) loopXE) (.sort .zero) :=
  .iotaStarK pinLoopCtx0 wLoopKA (.bvar 0) (.const 60 []) _ (.sort .zero)
    .zero True rfl
    (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ loopVarTy0 loopMkAppTy0 loopFamTy0 (.ofU wLoopKA)
    loopILhsSort loopXSort loopRRhsSort

/-- STEP 2a — the inner β: `m̂ t ⇒ (λ ih. ih→ih)` at `Π (ih:M̂ t). M̂ (mk t)`. -/
private def loopInnerBeta :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.app loopMinE (.bvar 0)) loopIhE loopIhPiE :=
  .beta pinLoopCtx0 (.const 60 []) loopIhE loopIhE (.bvar 0) (.bvar 0)
    loopIhPiE .zero
    (.imax (.succ .zero) (.succ .zero)) (.imax (.succ .zero) (.succ .zero))
    loopFamTy0 loopIhPiTy0L loopIhPiTy0
    (.refl _ _ _ loopIhLamTyG) (.refl _ _ _ loopVarTy0) loopIhETy0

/-- `m̂ t`'s β-contracted codomain `M̂ (mk l)`, at the `ih`-binder ctx. -/
private def loopCodMhatTyM : HasTyT pinLoopEnvT 1
    (.assumption (.app loopMotE (.bvar 0)) :: pinLoopCtx0)
    (.app loopMotE (.app (.const 61 []) (.bvar 1))) (.sort (.succ .zero)) :=
  loopMotAppTy (.app _ _ _ _ _ loopMkHdTy (.bvar _ 1 _ rfl))

/-- `inst0 X (M̂ (mk l)) = M̂ (mk t)`'s sort at Γ₀. -/
private def loopInstMhatTy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (instantiate0 loopXE (.app loopMotE (.app (.const 61 []) (.bvar 1))))
    (.sort (.succ .zero)) :=
  loopMotAppTy loopMkAppTy0

/-- `(λ ih. ih→ih) X : M̂ (mk t)` — the step-2 reduct, typed. -/
private def loopIhAppXTy : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (.app loopIhE loopXE)
    (instantiate0 loopXE (.app loopMotE (.app (.const 61 []) (.bvar 1)))) := by
  have hLt : HasTyT pinLoopEnvT 1 pinLoopCtx0 loopIhE loopIhPiE := loopIhETy0
  exact .app _ _ _ _ _ hLt loopXTy

/-- STEP 2 — `m̂ t X ⇒ (λ ih. ih→ih) X` — `ParRedT.app` on the
    `m̂ t □` spine (inner β inside, `X` parallel-refl), then `.conv`
    of the index `M̂ (mk t) ≡ Prop`. -/
private def loopOuterApp :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.app (.app loopMinE (.bvar 0)) loopXE)
      (.app loopIhE loopXE) (.sort .zero) := by
  have step : ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.app (.app loopMinE (.bvar 0)) loopXE) (.app loopIhE loopXE)
      (instantiate0 loopXE (.app loopMotE (.app (.const 61 []) (.bvar 1)))) :=
    .app pinLoopCtx0 (.app loopMinE (.bvar 0)) loopIhE loopXE loopXE
      (.app loopMotE (.bvar 0))
      (.app loopMotE (.app (.const 61 []) (.bvar 1)))
      loopIhPiE (.succ .zero) (.succ .zero)
      loopInnerBeta (.refl _ _) loopCodMhatTyM loopInstMhatTy0
      (.refl _ _ _ loopXTy) loopIhAppXTy
  exact .conv pinLoopCtx0 _ _ _ _ step (.of _ _ _ _ (loopMotConvB loopMkAppTy0))

/-- `ih → ih : sort (imax 0 0)` under `[ih : M̂ t, t : Loop]` — `hb`. -/
private def loopBodyTyM : HasTyT pinLoopEnvT 1
    (.assumption (.app loopMotE (.bvar 0)) :: pinLoopCtx0)
    loopBodyE (.sort (.imax .zero .zero)) :=
  loopBodyTyG

/-- STEP 3 — `(λ ih. ih→ih) X ⇒ X → lift X` — the second β, then
    `.conv` of `sort (imax 0 0) ≡ sort 0`. -/
private def loopIhAppXStep :
    ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.app loopIhE loopXE) (.pi loopXE (lift 0 1 loopXE)) (.sort .zero) := by
  have hb : ParRedT loopPEq pinLoopEnvT 1
      (.assumption (.app loopMotE (.bvar 0)) :: pinLoopCtx0) loopBodyE loopBodyE
      (.sort (.imax .zero .zero)) :=
    .refl _ _ _ loopBodyTyM
  have hred : HasTyT pinLoopEnvT 1 pinLoopCtx0
      (instantiate0 loopXE loopBodyE)
      (instantiate0 loopXE (.sort (.imax .zero .zero))) :=
    hasTyT_subst0_of_envWfT pinLoopGroupRecWfT loopBodyTyM loopXTy
  have step : ParRedT loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.app loopIhE loopXE) (instantiate0 loopXE loopBodyE)
      (instantiate0 loopXE (.sort (.imax .zero .zero))) :=
    .beta pinLoopCtx0 (.app loopMotE (.bvar 0)) loopBodyE loopBodyE
      loopXE loopXE (.sort (.imax .zero .zero))
      (.succ .zero) (.succ (.imax .zero .zero)) (.succ (.imax .zero .zero))
      (loopMotAppTy loopVarTy0) (.sort _ _) (.sort _ _)
      hb (.refl _ _ _ loopXTy) hred
  exact .conv pinLoopCtx0 _ _ _ _ step loopImaxTyConv

/-- `X → lift X : sort 0` — the chain's endpoint typing. -/
private def loopArrowTy0 : HasTyT pinLoopEnvT 1 pinLoopCtx0
    (.pi loopXE (lift 0 1 loopXE)) (.sort .zero) := by
  have hF : HasTyT pinLoopEnvT 1 (.assumption loopXE :: pinLoopCtx0)
      (.app (.app (.const 62 [.succ .zero]) loopMotE) loopMinE)
      (.pi (.const 60 []) (.app loopMotE (.bvar 0))) :=
    loopFETy
  have hB : HasTyT pinLoopEnvT 1 (.assumption loopXE :: pinLoopCtx0)
      (lift 0 1 loopXE) (.sort .zero) :=
    loopAtProp (.bvar _ 1 _ rfl) (.app _ _ _ _ _ hF (.bvar _ 1 _ rfl))
  exact loopAtImax (.pi _ loopXE .zero (lift 0 1 loopXE) .zero loopXSort hB)

/-- **`pinLoopT_typeLevel_reduces` — `ParRedTStar X (X → lift X)` at
    `sort 0`.** The typed route DeepSeek-pro's untyped measurement
    missed: `iotaStarK` on the variable major `t`, then two `β` steps
    through the literal minor `λ l ih. ih→ih`. The endpoint is
    `erase pinLoopArrow` — `X ⇒* X → X`, so J is TRUE at the type-level
    Loop under `ParRedT` (the join is the arrow itself — `PEqT.refl`
    on the target). -/
def pinLoopT_typeLevel_reduces :
    ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx0 loopXE
      (.pi loopXE (lift 0 1 loopXE)) (.sort .zero) := by
  exact .tail loopXIotaStep
    (.tail loopOuterApp (.tail loopIhAppXStep (.refl _ _ _ loopArrowTy0)))

/-- the target IS the erased arrow — `lift` computes through the closed
    `M̂`/`m̂` and lands `app (erase pinLoopF) (bvar 1)`. -/
theorem loopXE_lift_eq : lift 0 1 loopXE = .app (Ann.erase Ann.pinLoopF) (.bvar 1) := rfl

/-- `X ⇒* erase pinLoopArrow`, at the `erase`-spelled endpoint. -/
def pinLoopT_typeLevel_reduces_arrow :
    ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx0
      (Ann.erase Ann.pinLoopA) (Ann.erase Ann.pinLoopArrow) (.sort .zero) :=
  pinLoopT_typeLevel_reduces

/-- the type-level join — `X` and `X→X` meet at `X→X` itself: the typed
    `iotaStarK`+β chain reaches the arrow; the arrow is its own reduct
    (`refl`). So the TYPED `D` holds at the type-level Loop — J is TRUE
    under `ParRedT` (the untyped `ParRed`'s disjoint reduct classes —
    `parRedJoinable_pinLoop_false` — simply have no `iotaStarK` to cross
    the `const 62`/`pi` head boundary). -/
def pinLoopT_typeLevel_join : ∃ d d',
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx0
      loopXE d (.sort .zero)) ∧
    Nonempty (ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.pi loopXE (lift 0 1 loopXE)) d' (.sort .zero)) ∧
    Nonempty (PEqT pinLoopEnvT 1 pinLoopCtx0 d d') :=
  ⟨.pi loopXE (lift 0 1 loopXE), .pi loopXE (lift 0 1 loopXE),
    ⟨pinLoopT_typeLevel_reduces⟩, ⟨.refl _ _ _ loopArrowTy0⟩,
    ⟨PEqT.refl _⟩⟩

/-- `foldApps` on a snoc'd list is `app`-headed. -/
private theorem foldApps_snoc_head (f : Expr Nat) (l : List (Expr Nat)) (x : Expr Nat) :
    ∃ g a, foldApps f (l ++ [x]) = .app g a := by
  induction l generalizing f with
  | nil => exact ⟨f, x, rfl⟩
  | cons y ys ih => exact ih _

/-- `recCall` is `app`-headed. -/
private theorem recCall_app_head (f : Expr Nat) (pm : List (Expr Nat)) (m : Expr Nat) :
    ∃ g a, recCall f pm m = .app g a :=
  foldApps_snoc_head f pm m

/-- `iotaLhsOf` is `app`-headed. -/
private theorem iotaLhsOf_app_head {E : ResolvedEnv} (w : IotaWitness E) :
    ∃ g a, iotaLhsOf w = .app g a :=
  recCall_app_head _ _ _

/-- `iotaLhsOfS` is `app`-headed. -/
private theorem iotaLhsOfS_app_head {E : ResolvedEnv} (w : IotaWitnessS E) :
    ∃ g a, iotaLhsOfS w = .app g a :=
  recCall_app_head _ _ _

/-- `PEqT` at a `pi`-headed left endpoint: `pi`-congruence keeps the
    head, the `proof` leaf deposits `hp : pi A B : P` at `P : sort0` —
    a sort-classed term inhabiting a Prop. Refuting that deposit needs
    sort and `pi` inversion — `sortRow`/`piRow`, the `TypedRowsWf` wall
    (`W-F05b-Loop`). Every other arm is shape-dead. -/
private theorem peqT_pi_head {Γ : LCtx} {A B q : Expr Nat}
    (h : PEqT pinLoopEnvT 1 Γ (.pi A B) q) :
    (∃ A' B', q = .pi A' B') ∨
      ∃ P : Expr Nat,
        Nonempty (HasTyT pinLoopEnvT 1 Γ P (.sort .zero)) ∧
          Nonempty (HasTyT pinLoopEnvT 1 Γ (.pi A B) P) := by
  cases h with
  | pi => exact .inl ⟨_, _, rfl⟩
  | proof _ _ _ P _ hP _ hp _ => exact .inr ⟨P, ⟨hP⟩, ⟨hp⟩⟩

/-- one-step `pi`-head stability: a `ParRedT` step from a `pi`-headed
    source lands `pi`-headed, or a `peq`/`proof` leaf fired at a
    `pi`-headed source into a Prop-membership — the `W-F05b-Loop`
    deposit. `conv` and `iotaSpine`'s nested `hstep` carry the
    recursion; `iotaStarK`'s `recCall`-spine and every literal-headed
    arm are shape-dead. -/
private theorem parRedT_pi_head {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT loopPEq pinLoopEnvT 1 Γ a b T) :
    ∀ {A B : Expr Nat}, a = .pi A B →
    (∃ A' B', b = .pi A' B') ∨
      ∃ A' B' P,
        Nonempty (HasTyT pinLoopEnvT 1 Γ P (.sort .zero)) ∧
          Nonempty (HasTyT pinLoopEnvT 1 Γ (.pi A' B') P) := by
  induction h with
  | refl => intro A B he; exact .inl ⟨A, B, he⟩
  | pi => intro _ _ _; exact .inl ⟨_, _, rfl⟩
  | peq _ _ _ _ h =>
    intro A B he
    cases peqT_pi_head (he ▸ h) with
    | inl hb => exact .inl hb
    | inr dep =>
      obtain ⟨P, hP, hpP⟩ := dep
      exact .inr ⟨A, B, P, hP, hpP⟩
  | conv _ _ _ _ _ _ _ ih => intro _ _ he; exact ih he
  | iotaSpine _ _ _ _ _ _ hI _ _ ih =>
    intro _ _ he
    cases ih he with
    | inl hb =>
      cases hI with
      | ofU w =>
        obtain ⟨g, x, e⟩ := iotaLhsOf_app_head w
        rw [e] at hb
        nomatch hb
      | ofUS w =>
        obtain ⟨g, x, e⟩ := iotaLhsOfS_app_head w
        rw [e] at hb
        nomatch hb
    | inr d => exact .inr d
  | iotaStarK =>
    intro _ _ he
    obtain ⟨g, x, e⟩ := recCall_app_head _ _ _
    rw [e] at he
    nomatch he
  | iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ =>
    intro _ _ he
    obtain ⟨_, _, e⟩ := iotaStarKEta_appParts happ
    rw [e] at he
    nomatch he
  | sortEq => intro _ _ he; nomatch he
  | consts => intro _ _ he; nomatch he
  | bvarZeta => intro _ _ he; nomatch he
  | delta => intro _ _ he; nomatch he
  | app => intro _ _ he; nomatch he
  | beta => intro _ _ he; nomatch he
  | lam => intro _ _ he; nomatch he
  | letE => intro _ _ he; nomatch he
  | zeta => intro _ _ he; nomatch he
  | lit => intro _ _ he; nomatch he
  | eta => intro _ _ he; nomatch he

/-- `pi`-head stability under `ParRedTStar`: every reduct of a
    `pi`-headed source is `pi`-headed, OR somewhere a `peq`/`proof`
    leaf fired from a `pi`-headed term into a Prop-membership — the
    `W-F05b-Loop` deposit. -/
private theorem parRedTStar_pi_head {Γ : LCtx} {a b T : Expr Nat}
    (hs : ParRedTStar loopPEq pinLoopEnvT 1 Γ a b T) :
    (∃ A B, a = .pi A B) →
    (∃ A B, b = .pi A B) ∨
      ∃ A B P,
        Nonempty (HasTyT pinLoopEnvT 1 Γ P (.sort .zero)) ∧
          Nonempty (HasTyT pinLoopEnvT 1 Γ (.pi A B) P) := by
  induction hs with
  | refl => intro hp; exact .inl hp
  | tail h _ ih =>
    intro hp
    obtain ⟨A, B, he⟩ := hp
    cases parRedT_pi_head h he with
    | inl hb =>
      obtain ⟨A', B', rfl⟩ := hb
      exact ih ⟨_, _, rfl⟩
    | inr d => exact .inr d

/-- the reverse direction, measured: `X→X ⇒* b` lands `b` `pi`-headed —
    so `b = X` (`app`/`const`-headed) is reachable ONLY through a `peq`
    leaf whose `proof` arm deposits `hp : pi _ _ : P` at `P : sort0` —
    the same `W-F05b-Loop` debt class as `pinLoopT_peq_debt` (a
    sort-classed term in Prop-membership, refutable only at `sortRow`/
    `TypedRowsWf` scope). The `pi`-head is otherwise stable — no arm
    uncurls it. -/
def pinLoopT_arrow_stable {b : Expr Nat}
    (hs : ParRedTStar loopPEq pinLoopEnvT 1 pinLoopCtx0
      (.pi loopXE (lift 0 1 loopXE)) b (.sort .zero)) :
    (∃ A B, b = .pi A B) ∨
      ∃ A B P,
        Nonempty (HasTyT pinLoopEnvT 1 pinLoopCtx0 P (.sort .zero)) ∧
          Nonempty (HasTyT pinLoopEnvT 1 pinLoopCtx0 (.pi A B) P) :=
  parRedTStar_pi_head hs ⟨_, _, rfl⟩

#print axioms pinLoopT_step
#print axioms pinLoopT_inner
#print axioms pinLoopT_join
#print axioms pinLoopT_join_RS
#print axioms pinLoopT_shape
#print axioms pinLoopT_peq_debt
#print axioms pinLoopCtxWf
#print axioms wLoopKA
#print axioms pinLoopT_typeLevel_reduces
#print axioms pinLoopT_typeLevel_reduces_arrow
#print axioms pinLoopT_typeLevel_join
#print axioms pinLoopT_arrow_stable

end Rcic.Declarative
