import rcic.RcicSynRedexViewElim
import rcic.RcicSynRedexKindPins

/-!
# T13 §6 — β/ζ/δ view-inversion consumers + positive deep-transport reads

Spec: `research/rcic/sortrow/S8_REDEX_KIND_VIEWS.md` §6 (ChatGPT, #7338);
grokR #7351 §6's walled part. Consumers ride the S15 inversions of #7373
(`redexKindView_beta_inv` / `_zeta_inv` / `_delta_inv`,
`RcicSynRedexViewElim.lean`). `closure_claim = 0`.

Additive only — `RedexKindView`, `redexDom` and their producers are untouched;
nothing here is a new producer and no `piInvP` output bound is claimed.

## §1 View-inversion consumers

`betaRead` / `zetaRead` / `deltaRead` dispatch a `RedexKindView` at a β/ζ/δ
node through the index-free inversion and hand back the §6 call-table data:
the `PiGen` of the *original* field the view was built from (`hbody`'s
template under the assumption binder; `hb`'s under `letBinding`; `harg`,
`hv`, `hb`), the displayed-rhs Π equation, and the `hout` pack equation that
keeps the exact producer — ζ-under keeps the raw `TyP.lsub`.

## §2 Positive deep-transport reads

`DeepDomRead outer out`: `outer` is an original `wk`/`esub`/`linst`/`ewk`/
`cctx` node whose inner `CvP` field carries a view; `out` is that view's
produced domain typing transported by the node's *own* fields — never a new
producer, never a borrowed same-judgment field. `redexDom` still records
these outer nodes as `.arm` obligations; `DeepDomRead` is the positive route
behind them, bounded to one transport step (bounded reads of arbitrary
nesting stay a named T13 wall). `fsub`/`trans`/`symm` are not reads here —
`fsub` is a generated rule node, `trans`/`symm` belong to `DomPath`'s
`reverse`/`append` layer. `deepDomRead_inner_child` certifies the viewed
inner is a literal field of the outer node; `deepDomRead_step` lifts that
into `CvPOcc` provenance.

## §3 Kernel pins

The `dpB`/`rkB`/`rkZ` fixtures plus a new ζ-hit fixture `rkZH`
(`let s_U := P in #0` — stored value Π, body the bound variable). Each
`Fields` record is rebuilt from the fixture's own named fields and the
`.node` round-trip is an `rfl` equation; the tag pins report the kernel's
computed case (never an adjusted fixture). ζ-under on `rkZ` is a control by
itself: `rkZ`'s stored value `P` *is* a Π, yet the read stays `.under`
because the body is not `bvar 0` — the stored value is never swapped in.
-/
namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 View-inversion consumers -/

/-- The consumed β view — §6's row, both head splits kept apart. `tpl` is the
    `PiGen` of the *original* `hbody` (β-under: domain `A₀`, codomain `B₀`
    typings under `assumption β.A`); `argPi` is the `PiGen` of the original
    `harg` (β-hit). `hout` keeps the literal producer pack. -/
inductive BetaRead (β : BetaFields) (out : SortTyAny) : Type where
  | under (A₀ B₀ : Expr Nat) (hbodyEq : β.body = .pi A₀ B₀)
      (tpl : PiGen β.E β.n (.assumption β.A :: β.Γ) A₀ B₀)
      (rhsEq : instantiate0 β.arg β.body =
        .pi (instantiate0 β.arg A₀) (instantiate 1 (lift 0 1 β.arg) B₀))
      (hout : out = .mk (k3DomInst tpl.hA β.hA β.harg)) : BetaRead β out
  | hit (A' B' : Expr Nat) (hbodyZero : β.body = .bvar 0)
      (hargPi : β.arg = .pi A' B')
      (argPi : PiGen β.E β.n β.Γ A' B')
      (rhsEq : instantiate0 β.arg β.body = .pi A' B')
      (hout : out = .mk argPi.hA) : BetaRead β out

/-- The β consumer: `redexKindView_beta_inv` splits the view, then each case
    repackages the producer's own `piInvP` as the field's `PiGen`. -/
def betaRead {β : BetaFields} {domT : Expr Nat} {α : Level}
    {p : TyP β.E β.n β.Γ domT (.sort α)} (v : RedexKindView β.node p) :
    BetaRead β (.mk p) :=
  match redexKindView_beta_inv v with
  | .under A₀ B₀ hbodyEq hout =>
      .under A₀ B₀ hbodyEq
        (piInvP (envExt_refl β.E) (tyCast hbodyEq rfl β.hbody) rfl)
        (by rw [hbodyEq]; rfl) hout
  | .hit A' B' hbodyZero hargPi hout =>
      .hit A' B' hbodyZero hargPi
        (piInvP (envExt_refl β.E) (tyCast hargPi rfl β.harg) rfl)
        (by rw [hbodyZero]; exact hargPi) hout

/-- The consumed ζ view — under's `tpl` is the `PiGen` of the original `hb`
    in the *`letBinding`* context (never `.assumption`), and `hout` keeps the
    raw `TyP.lsub` producer at `j = 0` verbatim. -/
inductive ZetaRead (ζ : ZetaFields) (out : SortTyAny) : Type where
  | under (A₀ B₀ : Expr Nat) (hbodyEq : ζ.body = .pi A₀ B₀)
      (tpl : PiGen ζ.E ζ.n (.letBinding ζ.A ζ.value :: ζ.Γ) A₀ B₀)
      (rhsEq : instantiate0 ζ.value ζ.body =
        .pi (instantiate0 ζ.value A₀) (instantiate 1 (lift 0 1 ζ.value) B₀))
      (hout : out = .mk (TyP.lsub ζ.E ζ.n
        (.letBinding ζ.A ζ.value :: ζ.Γ) _ _ ζ.A ζ.value 0 ζ.u
        tpl.hA
        List.getElem?_cons_zero
        (tyCast (lift_zero_idx 0 ζ.value).symm (lift_zero_idx 0 ζ.A).symm ζ.hv)
        (tyCast (lift_zero_idx 0 ζ.A).symm rfl ζ.hA))) : ZetaRead ζ out
  | hit (A' B' : Expr Nat) (hbodyZero : ζ.body = .bvar 0)
      (hvaluePi : ζ.value = .pi A' B')
      (valuePi : PiGen ζ.E ζ.n ζ.Γ A' B')
      (rhsEq : instantiate0 ζ.value ζ.body = .pi A' B')
      (hout : out = .mk valuePi.hA) : ZetaRead ζ out

/-- The ζ consumer. -/
def zetaRead {ζ : ZetaFields} {domT : Expr Nat} {α : Level}
    {p : TyP ζ.E ζ.n ζ.Γ domT (.sort α)} (v : RedexKindView ζ.node p) :
    ZetaRead ζ (.mk p) :=
  match redexKindView_zeta_inv v with
  | .under A₀ B₀ hbodyEq hout =>
      .under A₀ B₀ hbodyEq
        (piInvP (envExt_refl ζ.E) (tyCast hbodyEq rfl ζ.hb) rfl)
        (by rw [hbodyEq]; rfl) hout
  | .hit A' B' hbodyZero hvaluePi hout =>
      .hit A' B' hbodyZero hvaluePi
        (piInvP (envExt_refl ζ.E) (tyCast hvaluePi rfl ζ.hv) rfl)
        (by rw [hbodyZero]; exact hvaluePi) hout

/-- The consumed δ view — the same stored body `b` under the same `ls`
    (`hRhsPi`), `storedPi` the `PiGen` of the original `hb`. Never a second
    unfolding. -/
inductive DeltaRead (δ : DeltaFields) (out : SortTyAny) : Type where
  | mk (A' B' : Expr Nat)
      (hRhsPi : instantiateLevels δ.ls δ.b = .pi A' B')
      (storedPi : PiGen δ.E δ.n δ.Γ A' B')
      (hout : out = .mk storedPi.hA) : DeltaRead δ out

/-- The δ consumer. -/
def deltaRead {δ : DeltaFields} {domT : Expr Nat} {α : Level}
    {p : TyP δ.E δ.n δ.Γ domT (.sort α)} (v : RedexKindView δ.node p) :
    DeltaRead δ (.mk p) :=
  match redexKindView_delta_inv v with
  | .mk A' B' hRhsPi hout =>
      .mk A' B' hRhsPi
        (piInvP (envExt_refl δ.E) (tyCast hRhsPi rfl δ.hb) rfl) hout

/-- Case tag — `true` on the β-hit route. -/
def BetaRead.isHit {β : BetaFields} {out : SortTyAny} : BetaRead β out → Bool
  | .under .. => false
  | .hit .. => true

/-- Case tag — `true` on the ζ-under route. -/
def ZetaRead.isUnder {ζ : ZetaFields} {out : SortTyAny} : ZetaRead ζ out → Bool
  | .under .. => true
  | .hit .. => false

/-! ## §2 Positive deep-transport reads -/

/-- `DeepDomRead c s`: `c` is an *original* transport node (`wk`, `esub`,
    `linst`, `ewk`, `cctx`) whose own `CvP`-typed field `inner` carries a
    `RedexKindView inner p`; `s` is `p` transported by the node's own fields —
    `TyP.wk`/`TyP.esub`/`TyP.linst`/`TyP.ewk`/`TyP.cctx` at the same indices
    the outer node computes. The outer node stays a `.arm` obligation in
    `redexDom`; this is the positive read behind it — one transport step,
    never iterated to a Π. -/
inductive DeepDomRead : CvPAny → SortTyAny → Type where
  | wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T domT : Expr Nat}
      {α : Level} {inner : CvP E n Γ a b T}
      {p : TyP E n Γ domT (.sort α)} (d : LocalDecl) (c : Nat)
      (v : RedexKindView inner p) :
      DeepDomRead (.mk (CvP.wk E n Γ a b T d c inner))
        (.mk (TyP.wk E n Γ domT (.sort α) d c p))
  | esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b T t v domT : Expr Nat} {j : Nat} {u α : Level}
      {inner : CvP E n Γ a b T} {p : TyP E n Γ domT (.sort α)}
      (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (vw : RedexKindView inner p) :
      DeepDomRead (.mk (CvP.esub E n Γ a b T t v j u inner hget hv hvT))
        (.mk (TyP.esub E n Γ domT (.sort α) t v j u p hget hv hvT))
  | linst {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
      {a b T domT : Expr Nat} {ls : List Level} {α : Level}
      {inner : CvP E a' Γ a b T} {p : TyP E a' Γ domT (.sort α)}
      (hls : levelsBounded n ls = true) (hlen : ls.length = a')
      (vw : RedexKindView inner p) :
      DeepDomRead (.mk (CvP.linst E a' n Γ a b T ls hls hlen inner))
        (.mk (TyP.linst E a' n Γ domT (.sort α) ls hls hlen p))
  | ewk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T domT : Expr Nat}
      {α : Level} {inner : CvP E₀ n Γ a b T}
      {p : TyP E₀ n Γ domT (.sort α)} (hext : EnvExt E₀ E)
      (vw : RedexKindView inner p) :
      DeepDomRead (.mk (CvP.ewk E₀ E n Γ a b T hext inner))
        (.mk (TyP.ewk E₀ E n Γ domT (.sort α) hext p))
  | cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b T A A' domT : Expr Nat} {u α : Level}
      {inner : CvP E n (.assumption A :: Γ) a b T}
      {p : TyP E n (.assumption A :: Γ) domT (.sort α)}
      (hA : CvP E n Γ A A' (.sort u))
      (vw : RedexKindView inner p) :
      DeepDomRead (.mk (CvP.cctx E n Γ a b T A A' u inner hA))
        (.mk (TyP.cctx E n Γ domT (.sort α) A A' u p hA))

/-- The produced (transported) domain typing. -/
def deepDomReadOut {c : CvPAny} {s : SortTyAny} (_ : DeepDomRead c s) :
    SortTyAny := s

/-- The viewed inner node is a literal field of the outer transport — the
    read never reaches outside the original node's own fields. -/
theorem deepDomRead_inner_child {c : CvPAny} {s : SortTyAny}
    (r : DeepDomRead c s) : ∃ inner : CvPAny, CvPChild c inner := by
  cases r with
  | wk d k v => exact ⟨.mk _, List.Mem.head _⟩
  | esub hget hv hvT v => exact ⟨.mk _, List.Mem.head _⟩
  | linst hls hlen v => exact ⟨.mk _, List.Mem.head _⟩
  | ewk hext v => exact ⟨.mk _, List.Mem.head _⟩
  | cctx hA v => exact ⟨.mk _, List.Mem.head _⟩

/-- Occurrence provenance: an outer node occurring in `H` places the viewed
    inner in `H` too, along the literal field step. -/
theorem deepDomRead_step {H c : CvPAny} {s : SortTyAny}
    (hocc : CvPOcc H c) (r : DeepDomRead c s) :
    ∃ inner : CvPAny, CvPOcc H inner :=
  let ⟨i, hmem⟩ := deepDomRead_inner_child r
  ⟨i, hocc.step hmem⟩

/-! ## §3 Kernel pins -/

/-- `dpB` as a `BetaFields` — every field is the fixture's own named term. -/
def dpBFields : BetaFields :=
  ⟨emptyEnv, 0, [], dpS1, dpP, dpS0, .sort dpU, .succ (.succ .zero),
    dpTyS1, dpTyPIn, dpTyS0, dpTyR, dpTyPIn⟩

/-- Kernel round-trip: the packed fields rebuild `dpB` itself. -/
theorem dpBFields_node : dpBFields.node = dpB := rfl

/-- `rkB` as a `BetaFields`. -/
def rkBFields : BetaFields :=
  ⟨emptyEnv, 0, [], .sort dpU, .bvar 0, dpP, .sort dpU, .succ dpU,
    rkTyU, rkTyVar, dpTyPIn, rkTyApp, dpTyPIn⟩

theorem rkBFields_node : rkBFields.node = rkB := rfl

/-- `rkZ` as a `ZetaFields`. -/
def rkZFields : ZetaFields :=
  ⟨emptyEnv, 0, [], .sort dpU, dpP, dpP, .sort dpU, .succ dpU,
    rkTyU, dpTyPIn, dpTyPIn, rkTyLet, dpTyPIn⟩

theorem rkZFields_node : rkZFields.node = rkZ := rfl

/-- ζ-hit fixture: `let s_U := P in #0` — the stored value `P` is the Π that
    the `bvar 0` body exposes; the read must be `.hit`, never `.under`. -/
abbrev rkLetH : Expr Nat := .letE (.sort dpU) dpP (.bvar 0)

/-- `#0 : sort s_U` under the `letBinding (sort s_U) P` binder. -/
def rkTyBvarLet : TyP emptyEnv 0 [.letBinding (.sort dpU) dpP] (.bvar 0)
    (.sort dpU) :=
  .bvar _ _ _ _ _ _ rfl rkTyU

/-- `rkLetH : sort s_U` — the `dl` field of `rkZH`. -/
def rkTyLetH : TyP emptyEnv 0 [] rkLetH (.sort dpU) :=
  .letE _ _ _ _ _ _ _ _ _ rkTyU dpTyPIn rkTyBvarLet rkTyU

/-- `rkZH : rkLetH ≡ P : sort s_U` — the original ζ node of the ζ-hit
    fixture. -/
def rkZH : CvP emptyEnv 0 [] rkLetH dpP (.sort dpU) :=
  .zeta _ _ _ (.sort dpU) dpP (.bvar 0) (.sort dpU) _
    rkTyU dpTyPIn rkTyBvarLet rkTyLetH dpTyPIn

/-- `rkZH` as a `ZetaFields`. -/
def rkZHFields : ZetaFields :=
  ⟨emptyEnv, 0, [], .sort dpU, dpP, .bvar 0, .sort dpU, .succ dpU,
    rkTyU, dpTyPIn, rkTyBvarLet, rkTyLetH, dpTyPIn⟩

theorem rkZHFields_node : rkZHFields.node = rkZH := rfl

/-- `betaRead` of a literal `betaUnder` view lands on `.under` — the `hit`
    arm is impossible since `pi ≠ bvar 0`. The case fields carry the read:
    `tpl` is `piInvP` of the original `hbody`, `hout` the producer pack
    equation `out = .mk (k3DomInst tpl.hA β.hA β.harg)`. -/
theorem betaRead_under {β : BetaFields} {A₀ B₀ : Expr Nat}
    (h : β.body = .pi A₀ B₀) :
    ∃ tpl rhsEq hout, betaRead (.betaUnder h : RedexKindView β.node _) =
      .under A₀ B₀ h tpl rhsEq hout := by
  cases hr : betaRead (.betaUnder h : RedexKindView β.node _) with
  | under A₀' B₀' hbodyEq tpl rhsEq hout =>
      have hpi := h.symm.trans hbodyEq
      injection hpi with eA eB
      subst eA; subst eB
      exact ⟨tpl, rhsEq, hout, rfl⟩
  | hit _ _ hbodyZero _ _ _ _ =>
      exact Expr.noConfusion (h.symm.trans hbodyZero)

/-- `betaRead` of a literal `betaHit` view lands on `.hit` — `under` is
    impossible since `bvar 0 ≠ pi`. `argPi` is `piInvP` of the original
    `harg`; `hout : out = .mk argPi.hA`. -/
theorem betaRead_hit {β : BetaFields} {A' B' : Expr Nat}
    (h0 : β.body = .bvar 0) (hPi : β.arg = .pi A' B') :
    ∃ argPi rhsEq hout, betaRead (.betaHit h0 hPi : RedexKindView β.node _) =
      .hit A' B' h0 hPi argPi rhsEq hout := by
  cases hr : betaRead (.betaHit h0 hPi : RedexKindView β.node _) with
  | under _ _ hbodyEq _ _ _ =>
      exact Expr.noConfusion (h0.symm.trans hbodyEq)
  | hit A'' B'' hbodyZero hargPi argPi rhsEq hout =>
      have hpi := hPi.symm.trans hargPi
      injection hpi with eA eB
      subst eA; subst eB
      exact ⟨argPi, rhsEq, hout, rfl⟩

/-- `zetaRead` of a literal `zetaUnder` view lands on `.under` — `tpl` is
    `piInvP` of the original `hb` *in the `letBinding` context* and `hout`
    keeps the raw `TyP.lsub` producer. `hit` impossible: `pi ≠ bvar 0`. -/
theorem zetaRead_under {ζ : ZetaFields} {A₀ B₀ : Expr Nat}
    (h : ζ.body = .pi A₀ B₀) :
    ∃ tpl rhsEq hout, zetaRead (.zetaUnder h : RedexKindView ζ.node _) =
      .under A₀ B₀ h tpl rhsEq hout := by
  cases hr : zetaRead (.zetaUnder h : RedexKindView ζ.node _) with
  | under A₀' B₀' hbodyEq tpl rhsEq hout =>
      have hpi := h.symm.trans hbodyEq
      injection hpi with eA eB
      subst eA; subst eB
      exact ⟨tpl, rhsEq, hout, rfl⟩
  | hit _ _ hbodyZero _ _ _ _ =>
      exact Expr.noConfusion (h.symm.trans hbodyZero)

/-- `zetaRead` of a literal `zetaHit` view lands on `.hit` — `valuePi` is
    `piInvP` of the original `hv`, never the stored-body field. `under` is
    impossible: `bvar 0 ≠ pi`. -/
theorem zetaRead_hit {ζ : ZetaFields} {A' B' : Expr Nat}
    (h0 : ζ.body = .bvar 0) (hPi : ζ.value = .pi A' B') :
    ∃ valuePi rhsEq hout, zetaRead (.zetaHit h0 hPi : RedexKindView ζ.node _) =
      .hit A' B' h0 hPi valuePi rhsEq hout := by
  cases hr : zetaRead (.zetaHit h0 hPi : RedexKindView ζ.node _) with
  | under _ _ hbodyEq _ _ _ =>
      exact Expr.noConfusion (h0.symm.trans hbodyEq)
  | hit A'' B'' hbodyZero hvaluePi valuePi rhsEq hout =>
      have hpi := hPi.symm.trans hvaluePi
      injection hpi with eA eB
      subst eA; subst eB
      exact ⟨valuePi, rhsEq, hout, rfl⟩

/-- `deltaRead` of a literal `deltaRhs` view lands on `.mk` — `storedPi` is
    `piInvP` of the original `hb` at the same `ls`, `hout` its pack. -/
theorem deltaRead_of {δ : DeltaFields} {A' B' : Expr Nat}
    (h : instantiateLevels δ.ls δ.b = .pi A' B') :
    ∃ storedPi hout, deltaRead (.deltaRhs h : RedexKindView δ.node _) =
      .mk A' B' h storedPi hout := by
  cases hr : deltaRead (.deltaRhs h : RedexKindView δ.node _) with
  | mk A'' B'' hRhsPi storedPi hout =>
      have hpi := h.symm.trans hRhsPi
      injection hpi with eA eB
      subst eA; subst eB
      exact ⟨storedPi, hout, rfl⟩

/-- Fixture pin: `dpB` (body `P` literally Π) reads `.under` — kernel route,
    instantiated from `betaRead_under`. -/
theorem dpB_read_under :
    ∃ tpl rhsEq hout,
      betaRead (.betaUnder rfl : RedexKindView dpBFields.node _) =
        .under dpS0 dpS0 rfl tpl rhsEq hout :=
  betaRead_under (β := dpBFields) rfl

/-- Fixture pin: `rkB` (body `#0`, argument `P`) reads `.hit`. -/
theorem rkB_read_hit :
    ∃ argPi rhsEq hout,
      betaRead (.betaHit rfl rfl : RedexKindView rkBFields.node _) =
        .hit dpS0 dpS0 rfl rfl argPi rhsEq hout :=
  betaRead_hit (β := rkBFields) rfl rfl

/-- Fixture pin and §4 control: `rkZ`'s stored value `P` *is* a Π, yet the
    read stays `.under` — the stored value is never swapped for the body. -/
theorem rkZ_read_under :
    ∃ tpl rhsEq hout,
      zetaRead (.zetaUnder rfl : RedexKindView rkZFields.node _) =
        .under dpS0 dpS0 rfl tpl rhsEq hout :=
  zetaRead_under (ζ := rkZFields) rfl

/-- Fixture pin: `rkZH` (body `#0`, value `P`) reads `.hit`. -/
theorem rkZH_read_hit :
    ∃ valuePi rhsEq hout,
      zetaRead (.zetaHit rfl rfl : RedexKindView rkZHFields.node _) =
        .hit dpS0 dpS0 rfl rfl valuePi rhsEq hout :=
  zetaRead_hit (ζ := rkZHFields) rfl rfl

/-- Tag kernel value at `rkB`: the consumed read is the `.hit` case. -/
theorem rkB_isHit :
    (betaRead (.betaHit rfl rfl : RedexKindView rkBFields.node _)).isHit =
      true := by
  obtain ⟨_, _, _, hr⟩ := rkB_read_hit
  rw [hr]
  rfl

/-- Tag kernel value at `dpB`: the consumed read is `.under`, not `.hit`. -/
theorem dpB_isUnder :
    (betaRead (.betaUnder rfl : RedexKindView dpBFields.node _)).isHit =
      false := by
  obtain ⟨_, _, _, hr⟩ := dpB_read_under
  rw [hr]
  rfl

/-- Tag kernel value at `rkZ`: `.under` — the ζ-under route taken even though
    the stored value is literally Π. -/
theorem rkZ_isUnder :
    (zetaRead (.zetaUnder rfl : RedexKindView rkZFields.node _)).isUnder =
      true := by
  obtain ⟨_, _, _, hr⟩ := rkZ_read_under
  rw [hr]
  rfl

/-- Tag kernel value at `rkZH`: `.hit`. -/
theorem rkZH_isHit :
    (zetaRead (.zetaHit rfl rfl : RedexKindView rkZHFields.node _)).isUnder =
      false := by
  obtain ⟨_, _, _, hr⟩ := rkZH_read_hit
  rw [hr]
  rfl

/-- `rkB` under one `wk` — the outer transport node, additive fixture. -/
def rkBWk : CvP emptyEnv 0 (insertAt (.assumption dpS0) 0 [])
    (lift 0 1 rkApp) (lift 0 1 dpP) (lift 0 1 (.sort dpU)) :=
  .wk emptyEnv 0 [] rkApp dpP (.sort dpU) (.assumption dpS0) 0 rkB

/-- The positive deep-transport read of `rkB`'s β-hit view through `rkBWk`:
    `TyP.wk` at the node's own `insertAt`/`lift`. -/
def rkBDeepWk :=
  DeepDomRead.wk (.assumption dpS0) 0
    (.betaHit rfl rfl : RedexKindView rkB _)

/-- The read's viewed inner is literally `rkB`, a field of `rkBWk`. -/
theorem rkBDeepWk_child : CvPChild (.mk rkBWk) (.mk rkB) :=
  List.Mem.head _

/-- The produced domain typing is `rkB`'s `harg`-Π domain `dpS0`, weakened —
    kernel value, reported as computed. -/
theorem rkBDeepWk_out : deepDomReadOut rkBDeepWk =
    .mk (TyP.wk emptyEnv 0 [] dpS0 (.sort (.succ .zero)) (.assumption dpS0) 0
      ((piInvP (envExt_refl emptyEnv)
        (tyCast (rfl : dpP = .pi dpS0 dpS0) rfl dpTyPIn) rfl).hA)) := rfl

end Rcic.Syn

#print axioms Rcic.Syn.betaRead
#print axioms Rcic.Syn.zetaRead
#print axioms Rcic.Syn.deltaRead
#print axioms Rcic.Syn.BetaRead.isHit
#print axioms Rcic.Syn.ZetaRead.isUnder
#print axioms Rcic.Syn.deepDomReadOut
#print axioms Rcic.Syn.deepDomRead_inner_child
#print axioms Rcic.Syn.deepDomRead_step
#print axioms Rcic.Syn.dpBFields
#print axioms Rcic.Syn.dpBFields_node
#print axioms Rcic.Syn.rkBFields
#print axioms Rcic.Syn.rkBFields_node
#print axioms Rcic.Syn.rkZFields
#print axioms Rcic.Syn.rkZFields_node
#print axioms Rcic.Syn.rkLetH
#print axioms Rcic.Syn.rkTyBvarLet
#print axioms Rcic.Syn.rkTyLetH
#print axioms Rcic.Syn.rkZH
#print axioms Rcic.Syn.rkZHFields
#print axioms Rcic.Syn.rkZHFields_node
#print axioms Rcic.Syn.betaRead_under
#print axioms Rcic.Syn.betaRead_hit
#print axioms Rcic.Syn.zetaRead_under
#print axioms Rcic.Syn.zetaRead_hit
#print axioms Rcic.Syn.deltaRead_of
#print axioms Rcic.Syn.dpB_read_under
#print axioms Rcic.Syn.rkB_read_hit
#print axioms Rcic.Syn.rkZ_read_under
#print axioms Rcic.Syn.rkZH_read_hit
#print axioms Rcic.Syn.rkB_isHit
#print axioms Rcic.Syn.dpB_isUnder
#print axioms Rcic.Syn.rkZ_isUnder
#print axioms Rcic.Syn.rkZH_isHit
#print axioms Rcic.Syn.rkBWk
#print axioms Rcic.Syn.rkBDeepWk
#print axioms Rcic.Syn.rkBDeepWk_child
#print axioms Rcic.Syn.rkBDeepWk_out
