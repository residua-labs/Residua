import rcic.RcicNativeValleyDiamond
import rcic.RcicParRedTPiDiamond

/-!
# RcicNativeValleyRows — rows of the core diamond that close natively, and the exact shape of
those that do not (Wall 1, `NativeConvValleys`, piece 4)

`CoreDiamond` (`RcicNativeValleyDiamond`) is the join of two core certified steps out of one
term, at independent indices, each output certified at its own index. Its rows are pairs of
the fifteen structural constructors with a common source. This module

* closes the **reversible** rows by joining AT THE SOURCE — the join certificates are the
  symmetric input certificates, no composition at all: `sortEq × sortEq`, `consts × consts`,
  `pi × pi` (the landed reversal `parRedT_pi_reverse_data`, `RcicParRedTPiDiamond.lean`);
* closes the **deterministic** rows where both targets coincide: `delta × delta`, `lit × lit`;
* closes two **congruence** rows from the joins of their children ("parent from children"):
  `app × app` (dependent index realigned by `convT_inst0_valueSort` from the children's
  certificates; the function's domain sort by regularity) and `eta × eta` (the children's join
  IS the parents');
* states, as explicit `Type`s and without assuming them, the five certified transports the
  remaining rows need: `CertAssumpCtx` (`lam × lam`, `lam × eta`), `CertSubst0` (`beta × beta`,
  `app × beta`), `CertSubstLet` (`zeta × zeta`, `letE × zeta`), `CertLift`
  (`bvarZeta × bvarZeta`), `IotaCommuteT` (`iotaSpine × ·`), and the K-gate alignment
  `KMajorAlign` (`iotaStarK`/`iotaStarKEta` against a leaf on the major — vacuous for
  certified steps, which are K-free, kept as the record of the K-admitting alternative) with
  its trivial family-headed instance. Each is discussed, with the landed uncertified
  counterpart, in `research/rcic/sortrow/NATIVE_VALLEYS_STATUS.md`.

Head-disjoint pairs (e.g. `sortEq × consts`) have no common source and need no row.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A join of two steps out of a common source: the shape of every core row. -/
abbrev Join (E : ResolvedEnv) (n : Nat) (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ : LCtx) (d e T₁ T₂ : Expr Nat) : Type :=
  Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂

/-! ### reversible rows: join at the source -/

/-- `sortEq × sortEq`: both steps reverse (`eqN` is symmetric), the join is the source. -/
def row_sortEq_sortEq {Γ : LCtx} {l₁ l₂ l₃ : Level} {T₁ T₂ : Expr Nat}
    {h₁ : eqN l₁ l₂} {hl₁ : HasTyT E n Γ (.sort l₁) T₁} {hr₁ : HasTyT E n Γ (.sort l₂) T₁}
    {h₂ : eqN l₁ l₃} {hl₂ : HasTyT E n Γ (.sort l₁) T₂} {hr₂ : HasTyT E n Γ (.sort l₃) T₂}
    (cp : Certified (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h₁ hl₁ hr₁))
    (cq : Certified (ParRedT.sortEq (PEq := PEq) Γ l₁ l₃ T₂ h₂ hl₂ hr₂)) :
    Join E n PEq Γ (.sort l₂) (.sort l₃) T₁ T₂ :=
  ⟨.sort l₁,
    ⟨.sortEq Γ l₂ l₁ T₁ (eqN_symm h₁) hr₁ hl₁, .sortEq (.symm _ _ _ _ cp.root)⟩,
    ⟨.sortEq Γ l₃ l₁ T₂ (eqN_symm h₂) hr₂ hl₂, .sortEq (.symm _ _ _ _ cq.root)⟩⟩

/-- `consts × consts`: both steps reverse (`eqNList` is symmetric), the join is the source. -/
def row_consts_consts {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level} {T₁ T₂ : Expr Nat}
    {h₁ : eqNList ls ls₁} {hl₁ : HasTyT E n Γ (.const r ls) T₁}
    {hr₁ : HasTyT E n Γ (.const r ls₁) T₁}
    {h₂ : eqNList ls ls₂} {hl₂ : HasTyT E n Γ (.const r ls) T₂}
    {hr₂ : HasTyT E n Γ (.const r ls₂) T₂}
    (cp : Certified (ParRedT.consts (PEq := PEq) Γ r ls ls₁ T₁ h₁ hl₁ hr₁))
    (cq : Certified (ParRedT.consts (PEq := PEq) Γ r ls ls₂ T₂ h₂ hl₂ hr₂)) :
    Join E n PEq Γ (.const r ls₁) (.const r ls₂) T₁ T₂ :=
  ⟨.const r ls,
    ⟨.consts Γ r ls₁ ls T₁ (eqNList_symm h₁) hr₁ hl₁, .consts (.symm _ _ _ _ cp.root)⟩,
    ⟨.consts Γ r ls₂ ls T₂ (eqNList_symm h₂) hr₂ hl₂, .consts (.symm _ _ _ _ cq.root)⟩⟩

/-- `pi × pi`: both steps reverse (the landed `parRedT_pi_reverse_data`), the join is the
    source; the certificates are the symmetric inputs. -/
def row_pi_pi (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A₁ A₂ B B₁ B₂ : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    {hA₁ : HasTyT E n Γ A (.sort u₁)} {hc₁ : ConvT E n Γ A A₁ (.sort u₁)}
    {hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁)}
    {hcB₁ : ConvT E n (.assumption A :: Γ) B B₁ (.sort v₁)}
    {hrt₁ : HasTyT E n Γ (.pi A₁ B₁) (.sort (.imax u₁ v₁))}
    {hA₂ : HasTyT E n Γ A (.sort u₂)} {hc₂ : ConvT E n Γ A A₂ (.sort u₂)}
    {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂)}
    {hcB₂ : ConvT E n (.assumption A :: Γ) B B₂ (.sort v₂)}
    {hrt₂ : HasTyT E n Γ (.pi A₂ B₂) (.sort (.imax u₂ v₂))}
    (cp : Certified (ParRedT.pi (PEq := PEq) Γ A A₁ B B₁ u₁ v₁ hA₁ hc₁ hB₁ hcB₁ hrt₁))
    (cq : Certified (ParRedT.pi (PEq := PEq) Γ A A₂ B B₂ u₂ v₂ hA₂ hc₂ hB₂ hcB₂ hrt₂)) :
    Join E n PEq Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u₁ v₁)) (.sort (.imax u₂ v₂)) :=
  ⟨.pi A B,
    ⟨parRedT_pi_reverse_data (PEq := PEq) hW hΓ hA₁ hc₁ hB₁ hcB₁, .pi (.symm _ _ _ _ cp.root)⟩,
    ⟨parRedT_pi_reverse_data (PEq := PEq) hW hΓ hA₂ hc₂ hB₂ hcB₂, .pi (.symm _ _ _ _ cq.root)⟩⟩

/-! ### deterministic rows -/

/-- `delta × delta`: the member and its body are determined by the reference, so both targets
    coincide. -/
def row_delta_delta {Γ : LCtx} {r : Nat} {ls : List Level} {m m' : CheckedMember}
    {b b' T₁ T₂ : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hl₁ : HasTyT E n Γ (.const r ls) T₁} {hr₁ : HasTyT E n Γ (instantiateLevels ls b) T₁}
    {hres' : E.members r = some m'} {hbody' : m'.body = some b'}
    {htr' : transparent m'.mclass = true} {hlen' : ls.length = m'.arity}
    {hwf' : levelsBounded n ls = true}
    {hl₂ : HasTyT E n Γ (.const r ls) T₂} {hr₂ : HasTyT E n Γ (instantiateLevels ls b') T₂}
    (_cp : Certified (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl₁ hr₁))
    (_cq : Certified (ParRedT.delta (PEq := PEq) Γ r ls m' b' T₂ hres' hbody' htr' hlen' hwf'
      hl₂ hr₂)) :
    Join E n PEq Γ (instantiateLevels ls b) (instantiateLevels ls b') T₁ T₂ := by
  have hm : m = m' := Option.some.inj (hres.symm.trans hres')
  subst hm
  have hb : b = b' := Option.some.inj (hbody.symm.trans hbody')
  subst hb
  exact ⟨instantiateLevels ls b,
    ⟨.refl Γ _ T₁ hr₁, .refl (.refl Γ _ T₁ hr₁)⟩,
    ⟨.refl Γ _ T₂ hr₂, .refl (.refl Γ _ T₂ hr₂)⟩⟩

/-- `lit × lit`: both targets are the expansion. -/
def row_lit_lit {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    {hexp₁ : HasTyT E n Γ (natExpand t) T₁} {hexp₂ : HasTyT E n Γ (natExpand t) T₂}
    (_cp : Certified (ParRedT.lit (PEq := PEq) Γ t T₁ hexp₁))
    (_cq : Certified (ParRedT.lit (PEq := PEq) Γ t T₂ hexp₂)) :
    Join E n PEq Γ (natExpand t) (natExpand t) T₁ T₂ :=
  ⟨natExpand t,
    ⟨.refl Γ _ T₁ hexp₁, .refl (.refl Γ _ T₁ hexp₁)⟩,
    ⟨.refl Γ _ T₂ hexp₂, .refl (.refl Γ _ T₂ hexp₂)⟩⟩

/-! ### congruence rows: parent from children -/

/-- One side of `app × app`: from the function join and the argument join, the certified step
    `app f₁ a₁ → app g a₃` at the node's own index `instantiate0 a B`. The reduct typing moves
    `instantiate0 a₃ B` to `instantiate0 a₁ B` by the argument join's certificate, the index
    moves `instantiate0 a₁ B` to `instantiate0 a B` by the argument child's certificate; the
    domain's sort comes from regularity of the function's Π type. -/
def appSide (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ g a a₁ a₃ A B T₀ : Expr Nat} {v : Level}
    (hf₁ : ParRedT PEq E n Γ f f₁ T₀) (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ha₁ : ParRedT PEq E n Γ a a₁ A) (ca₁ : Certified ha₁)
    (pf : CStep E n PEq Γ f₁ g T₀) (pa : CStep E n PEq Γ a₁ a₃ A) :
    CStep E n PEq Γ (.app f₁ a₁) (.app g a₃) (instantiate0 a B) :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hfPi : HasTyT E n Γ f (.pi A B) :=
    hasTyT_of_tyConvT (parRedT_hasTy_left L.typed hΓ hf₁) hc
  match hasTyTInv_pi (tySort hW hΓ hfPi).2 rfl with
  | ⟨_, _, hA, _, _⟩ =>
    let ha : HasTyT E n Γ a A := parRedT_hasTy_left L.typed hΓ ha₁
    let ha₁' : HasTyT E n Γ a₁ A := pa.leftTyped L hΓ
    let ha₃ : HasTyT E n Γ a₃ A := pa.rightTyped L hΓ
    let hTy : HasTyT E n Γ (instantiate0 a₁ B) (.sort v) := hasTyT_subst0S hcl hinst hB ha₁'
    let hr : HasTyT E n Γ (.app g a₃) (instantiate0 a₁ B) :=
      .conv Γ _ _ _ v
        (.app Γ g a₃ A B (hasTyT_of_tyConvT (pf.rightTyped L hΓ) hc) ha₃)
        (convT_inst0_valueSort hA hB ha₃ ha₁' (.symm _ _ _ _ pa.toConvT))
    let step : CStep E n PEq Γ (.app f₁ a₁) (.app g a₃) (instantiate0 a₁ B) :=
      ⟨.app Γ f₁ g a₁ a₃ A B T₀ v v pf.step hc hB hTy pa.step hr,
        .app (.app Γ f₁ g a₁ a₃ A B (convT_of_tyConv pf.toConvT hc) pa.toConvT) pf.cert pa.cert⟩
    step.reindex (.of _ _ _ v (convT_inst0_valueSort hA hB ha₁' ha (.symm _ _ _ _ ca₁.root)))

/-- `app × app` from the joins of its children. The input root certificates are not consumed:
    the output certificates are compositional. -/
def row_app_app (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ a a₁ a₂ A₁ B₁ T₀₁ A₂ B₂ T₀₂ : Expr Nat} {v₁ v₂ : Level}
    (hf₁ : ParRedT PEq E n Γ f f₁ T₀₁) (hc₁ : TyConvT E n Γ T₀₁ (.pi A₁ B₁))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (ha₁ : ParRedT PEq E n Γ a a₁ A₁) (ca₁ : Certified ha₁)
    (hf₂ : ParRedT PEq E n Γ f f₂ T₀₂) (hc₂ : TyConvT E n Γ T₀₂ (.pi A₂ B₂))
    (hB₂ : HasTyT E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (ha₂ : ParRedT PEq E n Γ a a₂ A₂) (ca₂ : Certified ha₂)
    (jf : Join E n PEq Γ f₁ f₂ T₀₁ T₀₂) (ja : Join E n PEq Γ a₁ a₂ A₁ A₂) :
    Join E n PEq Γ (.app f₁ a₁) (.app f₂ a₂) (instantiate0 a B₁) (instantiate0 a B₂) :=
  let ⟨g, pf, qf⟩ := jf
  let ⟨a₃, pa, qa⟩ := ja
  ⟨.app g a₃, appSide hW L hΓ hf₁ hc₁ hB₁ ha₁ ca₁ pf pa,
    appSide hW L hΓ hf₂ hc₂ hB₂ ha₂ ca₂ qf qa⟩

/-- `eta × eta`: both steps contract the same expansion of `f`; the join of the two function
    children IS the join of the parents (same indices). -/
def row_eta_eta {Γ : LCtx} {f₁ f₂ A B₁ B₂ : Expr Nat}
    (jf : Join E n PEq Γ f₁ f₂ (.pi A B₁) (.pi A B₂)) :
    Join E n PEq Γ f₁ f₂ (.pi A B₁) (.pi A B₂) :=
  jf

/-! ### the remaining rows, as exact shapes (not assumed) -/

/-- Certified steps transport across an assumption conversion (`lam × lam`, `lam × eta`: the
    body join is under the source domain, the output `ParRedT.lam` needs it under the stepped
    domain). The landed `F8EtaK.parRedT_assumpCtx` (`RcicEtaKDecide.lean`) is this statement
    for `PEqLeafT` without certificates. -/
def CertAssumpCtx (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ A' (.sort u) → ConvT E n Γ A A' (.sort u) →
    ∀ {a b T : Expr Nat}, CStep E n PEq (.assumption A :: Γ) a b T →
      CStep E n PEq (.assumption A' :: Γ) a b T

/-- Certified head substitution with a stepping value, ONE step (`beta × beta`, `app × beta`).
    The landed `parRedT_subst` (`RcicParRedTSubst.lean`) is a two-step star with the back-lift
    `hTC : ParRedT → ConvT` as a hypothesis (the K node's reduct is rigid); for K-free certified
    steps the one-step form holds — discharged by `certSubst0_of` (`RcicNativeValleySubst`)
    under `EnvWfT` and leaf weakening, with `hTC` replaced by the landed `convT_substCongr`. -/
def CertSubst0 (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A v v' body body' B : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) →
    CStep E n PEq (.assumption A :: Γ) body body' B → CStep E n PEq Γ v v' A →
    CStep E n PEq Γ (instantiate0 v body) (instantiate0 v' body') (instantiate0 v B)

/-- Certified `let` substitution with a stepping value (`zeta × zeta`, `letE × zeta`). The
    landed `parRedT_substLet` (`RcicParRedTSubst.lean`) is this statement with `hTC`. -/
def CertSubstLet (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A v v' body body' B : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ v A →
    CStep E n PEq (.letBinding A v :: Γ) body body' B → CStep E n PEq Γ v v' A →
    CStep E n PEq Γ (instantiate0 v body) (instantiate0 v' body') (instantiate0 v B)

/-- Certified weakening by a prefix (`bvarZeta × bvarZeta`: the stored values join below the
    binder, the outputs are the lifted joins). The landed `parRedT_lift_n`
    (`RcicParRedTSubst.lean`) is the uncertified statement. -/
def CertLift (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} (Δ : LCtx) {a b T : Expr Nat}, CStep E n PEq Γ a b T →
    CStep E n PEq (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b) (lift 0 Δ.length T)

/-- Typed ι commutes with a certified step out of the redex (`iotaSpine × ·`): the stepped
    redex still contracts, in zero or one ι steps, to a reduct the original reduct steps to.
    The erased counterparts are the ι rows of `RcicParRedDiamond.lean`. -/
def IotaCommuteT (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {lhs m rhs T : Expr Nat},
    DerivedIotaU E lhs rhs → CStep E n PEq Γ lhs m T → HasTyT E n Γ rhs T →
    Σ' (rhs' : Expr Nat), CStar E n PEq Γ m rhs' T ×' CStep E n PEq Γ rhs rhs' T

/-- The K gate at the irrelevance leaf's type: a `Prop`-sorted `A` inhabited by the
    constructor spine `ctorMajor w` and by the new major `q` yields a FAMILY-HEADED `Tm`
    inhabited by both (what `ParRedT.iotaStarK`'s `hfam`/`hmajor`/`hmk`/`hTm0` need to re-fire
    K at `q`). This is the typed alignment of §6.1 restated at the leaf: type uniqueness for
    the constructor spine `ctorMajor w` between `A` and its family instance.

    NOT CONSUMED by the certified construction: certified steps are K-free
    (`Certified.noK`), so no row of `CoreDiamond` ever re-fires K; the `ι × leaf-on-major`
    pair is the ordinary `iotaSpine × app` row (the reversed leaf `q ⇒ ctorMajor w` under the
    `app`, then `iotaSpine` with `hstep` that step). Kept as the record of what a K-admitting
    certificate family would have needed (`NATIVE_VALLEYS_STATUS.md` §3). -/
def KMajorAlign (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ (w : IotaWitness E) {A q : Expr Nat},
    HasTyT E n Γ A (.sort .zero) → HasTyT E n Γ (ctorMajor w) A → HasTyT E n Γ q A →
    Σ' (Tm : Expr Nat), (∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF) ×'
      HasTyT E n Γ Tm (.sort .zero) ×' HasTyT E n Γ (ctorMajor w) Tm ×' HasTyT E n Γ q Tm

/-- The alignment is trivial when the leaf's type is already family-headed: `Tm := A`. -/
def kMajorAlign_of_famHead {Γ : LCtx} (w : IotaWitness E) {A q : Expr Nat}
    (hfam : ∃ lsF, (appsSpine A).1 = .const w.familyRef lsF)
    (hA : HasTyT E n Γ A (.sort .zero)) (hmk : HasTyT E n Γ (ctorMajor w) A)
    (hq : HasTyT E n Γ q A) :
    Σ' (Tm : Expr Nat), (∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF) ×'
      HasTyT E n Γ Tm (.sort .zero) ×' HasTyT E n Γ (ctorMajor w) Tm ×' HasTyT E n Γ q Tm :=
  ⟨A, hfam, hA, hmk, hq⟩

end Rcic.Declarative.NativeValleys
