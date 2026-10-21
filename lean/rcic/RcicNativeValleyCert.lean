import rcic.RcicParRedTConv
import rcic.RcicTypedInvert
import rcic.RcicTypedValidity
import rcic.RcicDT0709EnvWf
import rcic.RcicCtxConvT

/-!
# RcicNativeValleyCert — typed parallel steps carrying their own native certificates
(Wall 1, `NativeConvValleys`, piece 1: the invariant and the valley algebra)

`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §5.5 names the single sufficient
theorem for the weak Π row: every native `ConvT` has a *valley* of typed parallel stars
(`ParRedTStar`) to a common centre. §6.1 locates the obstruction of the generic route in the
back-lift `parRedT_to_convT` (`RcicParRedTConv.lean`): at a K / η-K node it needs the typed
alignment `major : A0`, i.e. type uniqueness (`hUniq`). §6.2 observes that an *exact* native
certificate stored with a step bypasses that back-lift at endpoint-directed peaks.

This module generalises §6.2 to the K-free fragment of the relation: a step is **certified**
(`Certified`) when every node of its derivation carries a native `ConvT` for its own
conclusion — one constructor per `ParRedT` constructor except the two K nodes, the node's own
certificate plus the certificates of its sub-steps. The K nodes (`iotaStarK`, `iotaStarKEta`)
are excluded, not stored: their reduct is rigid in the witness (no sub-step), which refutes
the one-step mixed substitution and hence the one-step diamond at `beta × beta`
(`NATIVE_VALLEYS_STATUS.md` §2a); the valley producer never emits them (`ConvT` has no K
rule), so a certified step is K-free by construction (`Certified.noK`).
Certificates compose along stars (`CStar.toConvT`), transport along index conversions
(`CStep.reindex`, `CStar.reindex`), and — the point — the certificate of the second joining
leg of a *same-index* diamond is determined by the two input certificates and the FIRST
joining leg's (`rootCert_other`); the generic back-lift is never consulted.

The remaining oracle is the same-index one-step diamond on certified steps, `CDiamond`. From
it, the strip lemma (`strip`) and confluence of certified stars (`confluence`) follow by the
textbook induction, as data, and give `CValley.trans`. Which rows of `CDiamond` go through
natively and which still need the K alignment is the subject of the following modules and of
`research/rcic/sortrow/NATIVE_VALLEYS_STATUS.md`.

The proof-irrelevance leaf is abstract: `LeafIface` is the interface the construction uses
(endpoint typings, the leaf's own conversion, the `Prop` sorting of its type, and leaf
formation from `T : Prop`, `p : T`, `q : T`). The spec's `ProofLeaf` (§5.2) satisfies it by its
three fields and `ConvT.irr`.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the leaf interface -/

/-- What the construction needs of the `peq` leaf: both endpoint typings, the leaf's own
    native conversion, the `Prop` sorting of its type, and formation of a leaf from a
    `Prop`-sorted type and two of its inhabitants (the `ConvT.irr` shape). The spec's
    `ProofLeaf E n` (§5.2) is an instance by its three fields and `ConvT.irr`. -/
structure LeafIface (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) where
  typed : ∀ {Γ : LCtx} {p q T : Expr Nat},
    PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T
  conv : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → ConvT E n Γ p q T
  prop : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → HasTyT E n Γ T (.sort .zero)
  ofIrr : ∀ {Γ : LCtx} {p q T : Expr Nat},
    HasTyT E n Γ T (.sort .zero) → HasTyT E n Γ p T → HasTyT E n Γ q T → PEq Γ p q T

/-! ### the invariant: every node carries its own native certificate -/

/-- A `ParRedT` derivation in which every node carries a native `ConvT` for its own
    conclusion: one constructor per `ParRedT` constructor EXCEPT the two K nodes
    (`iotaStarK`, `iotaStarKEta`), with the node's certificate `c` and the certificates of
    its sub-steps. Nodes without sub-steps (`refl`, `sortEq`, `consts`, `delta`, `pi`, `lit`,
    `peq`) carry only `c`.

    The K nodes have NO constructor: a certified step is K-free by construction
    (`Certified.noK`, `Certified.noKEta`). Reason (`NATIVE_VALLEYS_STATUS.md` §2a): the K
    node's reduct `rhs` is `iotaRhsOf w` of the witness whose `preMajor` is read off the
    source, and the node has no sub-step, so under a mixed substitution `v ⇒ v'` the K
    reduct `rhs[v]` must still step to `rhs[v']` — the one-step mixed substitution and with
    it the one-step diamond FAIL at `beta × beta` for a K body leg (the landed
    `parRedT_subst` packages exactly this as a two-step star). The valley producer never
    emits a K node (`ConvT` has no K rule; its K conversion is `irr` on the major followed
    by `iota`), so nothing is lost: the valleys live in the K-free fragment, where the
    classical one-step theory applies. -/
inductive Certified : {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Type
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A}
      (c : ConvT E n Γ a a A) : Certified (.refl Γ a A h)
  | sortEq {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat} {h : eqN l₁ l₂}
      {hl : HasTyT E n Γ (.sort l₁) T} {hr : HasTyT E n Γ (.sort l₂) T}
      (c : ConvT E n Γ (.sort l₁) (.sort l₂) T) : Certified (.sortEq Γ l₁ l₂ T h hl hr)
  | consts {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat} {h : eqNList ls ls'}
      {hl : HasTyT E n Γ (.const r ls) T} {hr : HasTyT E n Γ (.const r ls') T}
      (c : ConvT E n Γ (.const r ls) (.const r ls') T) :
      Certified (.consts Γ r ls ls' T h hl hr)
  | bvarZeta {Γ : LCtx} {i : Nat} {A v v' T : Expr Nat}
      {h : Γ.get? i = some (.letBinding A v)}
      {hv : ParRedT PEq E n (Γ.drop (i + 1)) v v' A}
      {hl : HasTyT E n Γ (.bvar i) T} {hr : HasTyT E n Γ (lift 0 (i + 1) v') T}
      (c : ConvT E n Γ (.bvar i) (lift 0 (i + 1) v') T) (cv : Certified hv) :
      Certified (.bvarZeta Γ i A v v' T h hv hl hr)
  | delta {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b T : Expr Nat}
      {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hl : HasTyT E n Γ (.const r ls) T} {hr : HasTyT E n Γ (instantiateLevels ls b) T}
      (c : ConvT E n Γ (.const r ls) (instantiateLevels ls b) T) :
      Certified (.delta Γ r ls m b T hres hbody htr hlen hwf hl hr)
  | app {Γ : LCtx} {f f' a a' A B T₀ : Expr Nat} {v w : Level}
      {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
      {ha : ParRedT PEq E n Γ a a' A}
      {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
      (c : ConvT E n Γ (.app f a) (.app f' a') (instantiate0 a B))
      (cf : Certified hf) (ca : Certified ha) :
      Certified (.app Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr)
  | beta {Γ : LCtx} {A body body' arg arg' B : Expr Nat} {u v w : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w)}
      {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
      {ha : ParRedT PEq E n Γ arg arg' A}
      {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
      (c : ConvT E n Γ (.app (.lam A body) arg) (instantiate0 arg' body') (instantiate0 arg B))
      (cb : Certified hb) (ca : Certified ha) :
      Certified (.beta Γ A body body' arg arg' B u v w hA hB hTy hb ha hred)
  | lam {Γ : LCtx} {A A' body body' B : Expr Nat} {u v : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.lam A' body') (.pi A B)}
      (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B)) (cb : Certified hb) :
      Certified (.lam Γ A A' body body' B u v hc hA hB hb hrt)
  | pi {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hc : ConvT E n Γ A A' (.sort u)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
      {hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v))}
      (c : ConvT E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))) :
      Certified (.pi Γ A A' B B' u v hA hc hB hcB hrt)
  | letE {Γ : LCtx} {A A' value value' body body' B : Expr Nat} {u w : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hv : ParRedT PEq E n Γ value value' A}
      {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
      {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
      {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)}
      (c : ConvT E n Γ (.letE A value body) (.letE A' value' body') (instantiate0 value B))
      (cv : Certified hv) (cb : Certified hb) :
      Certified (.letE Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt)
  | zeta {Γ : LCtx} {A value value' body body' B : Expr Nat} {u w : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hv : ParRedT PEq E n Γ value value' A}
      {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
      {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
      {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
      {hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B)}
      (c : ConvT E n Γ (.letE A value body) (instantiate0 value' body') (instantiate0 value B))
      (cv : Certified hv) (cb : Certified hb) :
      Certified (.zeta Γ A value value' body body' B u w hA hv hB hTy hb hred)
  | iotaSpine {Γ : LCtx} {lhs lhs' rhs T : Expr Nat}
      {hstep : ParRedT PEq E n Γ lhs lhs' T} {hI : DerivedIotaU E lhs' rhs}
      {hred : HasTyT E n Γ lhs' T} {hrhs : HasTyT E n Γ rhs T}
      (c : ConvT E n Γ lhs rhs T) (cs : Certified hstep) :
      Certified (.iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs)
  | lit {Γ : LCtx} {t : Nat} {T : Expr Nat} {hexp : HasTyT E n Γ (natExpand t) T}
      (c : ConvT E n Γ (.lit t) (natExpand t) T) : Certified (.lit Γ t T hexp)
  | eta {Γ : LCtx} {f f' A B : Expr Nat} {hf : ParRedT PEq E n Γ f f' (.pi A B)}
      {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
      (c : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B))
      (cf : Certified hf) :
      Certified (.eta Γ f f' A B hf hl)
  | peq {Γ : LCtx} {p q T : Expr Nat} {h : PEq Γ p q T}
      (c : ConvT E n Γ p q T) : Certified (.peq Γ p q T h)
  | conv {Γ : LCtx} {a b A A' : Expr Nat} {h : ParRedT PEq E n Γ a b A}
      {hc : TyConvT E n Γ A A'}
      (c : ConvT E n Γ a b A') (ch : Certified h) : Certified (.conv Γ a b A A' h hc)

/-- The node's own certificate. -/
def Certified.root : {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} →
    Certified p → ConvT E n Γ a b T
  | _, _, _, _, _, .refl c => c
  | _, _, _, _, _, .sortEq c => c
  | _, _, _, _, _, .consts c => c
  | _, _, _, _, _, .bvarZeta c _ => c
  | _, _, _, _, _, .delta c => c
  | _, _, _, _, _, .app c _ _ => c
  | _, _, _, _, _, .beta c _ _ => c
  | _, _, _, _, _, .lam c _ => c
  | _, _, _, _, _, .pi c => c
  | _, _, _, _, _, .letE c _ _ => c
  | _, _, _, _, _, .zeta c _ _ => c
  | _, _, _, _, _, .iotaSpine c _ => c
  | _, _, _, _, _, .lit c => c
  | _, _, _, _, _, .eta c _ => c
  | _, _, _, _, _, .peq c => c
  | _, _, _, _, _, .conv c _ => c

/-- The K discriminator on steps: `true` exactly at `iotaStarK` / `iotaStarKEta` roots. -/
def isK {Γ : LCtx} {a b T : Expr Nat} : ParRedT PEq E n Γ a b T → Bool
  | .iotaStarK .. => true
  | .iotaStarKEta .. => true
  | _ => false

/-- Every certified root is a non-K constructor (one arm per `Certified` constructor; the
    dependent elimination of a certificate at a K index is not available directly because the
    K source `recCall … major` does not unfold to a constructor during index unification). -/
theorem Certified.isK_false : {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} →
    Certified p → isK p = false
  | _, _, _, _, _, .refl _ => rfl
  | _, _, _, _, _, .sortEq _ => rfl
  | _, _, _, _, _, .consts _ => rfl
  | _, _, _, _, _, .bvarZeta _ _ => rfl
  | _, _, _, _, _, .delta _ => rfl
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .beta _ _ _ => rfl
  | _, _, _, _, _, .lam _ _ => rfl
  | _, _, _, _, _, .pi _ => rfl
  | _, _, _, _, _, .letE _ _ _ => rfl
  | _, _, _, _, _, .zeta _ _ _ => rfl
  | _, _, _, _, _, .iotaSpine _ _ => rfl
  | _, _, _, _, _, .lit _ => rfl
  | _, _, _, _, _, .eta _ _ => rfl
  | _, _, _, _, _, .peq _ => rfl
  | _, _, _, _, _, .conv _ _ => rfl

/-- No certificate for a K node: a certified step is K-free. -/
theorem Certified.noK {Γ : LCtx} {w : IotaWitness E} {major Tm rhs T : Expr Nat} {rl : Level}
    {afs : Prop} {hrl : piBody w.famMember.mtype = .sort rl}
    {hsel : EliminationSelection rl w.nMinors afs .anySort}
    {hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF}
    {hmajor : HasTyT E n Γ major Tm} {hmk : HasTyT E n Γ (ctorMajor w) Tm}
    {hTm0 : HasTyT E n Γ Tm (.sort .zero)} {hι : DerivedIotaU E (iotaLhsOf w) rhs}
    {hlι : HasTyT E n Γ (iotaLhsOf w) T}
    {hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T}
    {hrhs : HasTyT E n Γ rhs T}
    (c : Certified (ParRedT.iotaStarK (PEq := PEq) Γ w major Tm rhs T rl afs hrl hsel hfam
      hmajor hmk hTm0 hι hlι hlhs hrhs)) : False := by
  have h := c.isK_false
  simp only [isK] at h
  exact Bool.noConfusion h

/-- No certificate for an η-K node either. -/
theorem Certified.noKEta {Γ : LCtx} {w : IotaWitness E} {f A B Tm rhs : Expr Nat}
    {u rl : Level} {afs : Prop}
    {happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0)}
    {hA : HasTyT E n Γ A (.sort u)} {hf : HasTyT E n Γ f (.pi A B)}
    {hrl : piBody w.famMember.mtype = .sort rl}
    {hsel : EliminationSelection rl w.nMinors afs .anySort}
    {hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF}
    {hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm}
    {hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm}
    {hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero)}
    {hι : DerivedIotaU E (iotaLhsOf w) rhs}
    {hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B}
    {hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B}
    {hrhs : HasTyT E n (.assumption A :: Γ) rhs B}
    (c : Certified (ParRedT.iotaStarKEta (PEq := PEq) Γ w f A B Tm rhs u rl afs happ hA hf
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs)) : False := by
  have h := c.isK_false
  simp only [isK] at h
  exact Bool.noConfusion h

/-- A certified step as a bundle. -/
structure CStep (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ : LCtx) (a b T : Expr Nat) where
  step : ParRedT PEq E n Γ a b T
  cert : Certified step

/-- The step's certificate. -/
def CStep.toConvT {Γ : LCtx} {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) :
    ConvT E n Γ a b T :=
  s.cert.root

/-- The invariant is preserved by the index mover `ParRedT.conv`: the moved node's
    certificate is the child's, moved along the same chain. -/
def CStep.reindex {Γ : LCtx} {a b T T' : Expr Nat} (s : CStep E n PEq Γ a b T)
    (hcT : TyConvT E n Γ T T') : CStep E n PEq Γ a b T' :=
  ⟨.conv Γ a b T T' s.step hcT, .conv (convT_of_tyConv s.cert.root hcT) s.cert⟩

/-- The irrelevance step: two inhabitants of a `Prop`-sorted type are one certified leaf step
    apart, `ConvT.irr` the certificate. -/
def CStep.irr (L : LeafIface E n PEq) {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    CStep E n PEq Γ p q P :=
  ⟨.peq Γ p q P (L.ofIrr hP hp hq), .peq (.irr Γ P p q hP hp hq)⟩

/-- Right endpoint typing of a certified step (the relation's, `parRedT_hasTy_right`). -/
def CStep.rightTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) : HasTyT E n Γ b T :=
  parRedT_hasTy_right L.typed hΓ s.step

/-- Left endpoint typing of a certified step. -/
def CStep.leftTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) : HasTyT E n Γ a T :=
  parRedT_hasTy_left L.typed hΓ s.step

/-! ### certified stars -/

/-- A star of certified steps at a fixed index (the certified `ParRedTStar`). -/
inductive CStar (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (a A : Expr Nat) (h : HasTyT E n Γ a A) : CStar E n PEq Γ a a A
  | tail {Γ : LCtx} {a b c A : Expr Nat}
      (s : CStep E n PEq Γ a b A) (hs : CStar E n PEq Γ b c A) : CStar E n PEq Γ a c A

/-- Forgetting the certificates: the underlying `ParRedTStar`. -/
def CStar.forget : {Γ : LCtx} → {a b A : Expr Nat} → CStar E n PEq Γ a b A →
    ParRedTStar PEq E n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A h
  | _, _, _, _, .tail s hs => .tail s.step hs.forget

/-- The composed certificate of a certified star: `trans` over the steps' certificates. -/
def CStar.toConvT : {Γ : LCtx} → {a b A : Expr Nat} → CStar E n PEq Γ a b A →
    ConvT E n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A h
  | _, _, _, _, .tail s hs => .trans _ _ _ _ _ s.toConvT hs.toConvT

/-- Right endpoint typing of a certified star (off the `refl` tail). -/
def CStar.rightTyped : {Γ : LCtx} → {a b A : Expr Nat} → CStar E n PEq Γ a b A →
    HasTyT E n Γ b A
  | _, _, _, _, .refl _ _ _ h => h
  | _, _, _, _, .tail _ hs => hs.rightTyped

/-- Left endpoint typing of a certified star. -/
def CStar.leftTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b A : Expr Nat} → CStar E n PEq Γ a b A → HasTyT E n Γ a A
  | _, _, _, .refl _ _ _ h => h
  | _, _, _, .tail s _ => s.leftTyped L hΓ

/-- Star transitivity. -/
def CStar.trans : {Γ : LCtx} → {a b c A : Expr Nat} → CStar E n PEq Γ a b A →
    CStar E n PEq Γ b c A → CStar E n PEq Γ a c A
  | _, _, _, _, _, .refl _ _ _ _, t => t
  | _, _, _, _, _, .tail s hs, t => .tail s (hs.trans t)

/-- Index transport of a whole certified star (each step through `CStep.reindex`). -/
def CStar.reindex {Γ : LCtx} {A A' : Expr Nat} (hcT : TyConvT E n Γ A A') :
    {a b : Expr Nat} → CStar E n PEq Γ a b A → CStar E n PEq Γ a b A'
  | _, _, .refl _ a _ h => .refl Γ a A' (hasTyT_of_tyConvT h hcT)
  | _, _, .tail s hs => .tail (s.reindex hcT) (hs.reindex hcT)

/-- One certified step as a certified star. -/
def CStar.ofStep (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (s : CStep E n PEq Γ a b A) : CStar E n PEq Γ a b A :=
  .tail s (.refl Γ b A (s.rightTyped L hΓ))

/-! ### certified valleys -/

/-- A valley of certified stars to a common centre, at one index: the certified form of the
    spec's `NativeValley` (§5.5); `CStar.forget` on both legs gives that structure. -/
structure CValley (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ : LCtx) (a b T : Expr Nat) where
  centre : Expr Nat
  left : CStar E n PEq Γ a centre T
  right : CStar E n PEq Γ b centre T

/-- The valley's own native certificate: down the left leg, up the right. -/
def CValley.toConvT {Γ : LCtx} {a b T : Expr Nat} (v : CValley E n PEq Γ a b T) :
    ConvT E n Γ a b T :=
  .trans _ _ _ _ _ v.left.toConvT (.symm _ _ _ _ v.right.toConvT)

/-- The trivial valley at a typed term. -/
def CValley.refl {Γ : LCtx} {a T : Expr Nat} (h : HasTyT E n Γ a T) :
    CValley E n PEq Γ a a T :=
  ⟨a, .refl Γ a T h, .refl Γ a T h⟩

/-- Valleys are symmetric. -/
def CValley.symm {Γ : LCtx} {a b T : Expr Nat} (v : CValley E n PEq Γ a b T) :
    CValley E n PEq Γ b a T :=
  ⟨v.centre, v.right, v.left⟩

/-- Index transport of a valley. -/
def CValley.reindex {Γ : LCtx} {a b T T' : Expr Nat} (v : CValley E n PEq Γ a b T)
    (hcT : TyConvT E n Γ T T') : CValley E n PEq Γ a b T' :=
  ⟨v.centre, v.left.reindex hcT, v.right.reindex hcT⟩

/-- One certified step is a valley with the step's target as centre. -/
def CValley.ofStep (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) : CValley E n PEq Γ a b T :=
  ⟨b, CStar.ofStep L hΓ s, .refl Γ b T (s.rightTyped L hΓ)⟩

/-- Forgetting the certificates: the spec's valley shape (§5.5), as a proposition. -/
theorem CValley.exists_join {Γ : LCtx} {a b T : Expr Nat} (v : CValley E n PEq Γ a b T) :
    ∃ c : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a c T) ∧ Nonempty (ParRedTStar PEq E n Γ b c T) :=
  ⟨v.centre, ⟨v.left.forget⟩, ⟨v.right.forget⟩⟩

/-! ### the remaining oracle: the same-index certified diamond -/

/-- The one-step diamond on certified steps at a COMMON index: two certified steps out of `b`
    at `T` join by two certified steps at `T`. This is the only hypothesis the valley algebra
    below consumes. Its rows are the subject of the following modules. -/
def CDiamond (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T : Expr Nat},
    CStep E n PEq Γ b d T → CStep E n PEq Γ b e T →
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T ×' CStep E n PEq Γ e f T

/-- The certificate of the second joining leg from the two input certificates and the first
    joining leg's: `e ← b → d → f`. No back-lift of any produced step is read: a diamond's
    certificates are closed under its input certificates plus ONE output certificate. -/
def rootCert_other {Γ : LCtx} {b d e f T : Expr Nat}
    (cp : ConvT E n Γ b d T) (cq : ConvT E n Γ b e T) (cp' : ConvT E n Γ d f T) :
    ConvT E n Γ e f T :=
  .trans _ _ _ _ _ (.symm _ _ _ _ cq) (.trans _ _ _ _ _ cp cp')

/-- The strip lemma for certified stars: a certified step against a certified star joins by a
    certified star and a certified step. Induction on the star; each diamond call is the
    oracle. -/
def strip (D : CDiamond E n PEq) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d T : Expr Nat} (p : CStep E n PEq Γ b d T) :
    {e : Expr Nat} → CStar E n PEq Γ b e T →
    Σ' (f : Expr Nat), CStar E n PEq Γ d f T ×' CStep E n PEq Γ e f T
  | _, .refl _ _ _ _ => ⟨d, .refl Γ d T (p.rightTyped L hΓ), p⟩
  | _, .tail q qs =>
      let ⟨_, p₁, q₁⟩ := D hΓ p q
      let ⟨f, s', q'⟩ := strip D L hΓ q₁ qs
      ⟨f, .tail p₁ s', q'⟩

/-- Confluence of certified stars at a common index, from the oracle: induction on the first
    star, strip at each step. -/
def confluence (D : CDiamond E n PEq) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d T : Expr Nat} :
    CStar E n PEq Γ b d T → {e : Expr Nat} → CStar E n PEq Γ b e T →
    Σ' (f : Expr Nat), CStar E n PEq Γ d f T ×' CStar E n PEq Γ e f T
  | .refl _ _ _ _, e, s₂ => ⟨e, s₂, .refl Γ e T s₂.rightTyped⟩
  | .tail p ps, _, s₂ =>
      let ⟨_, s₂', q₁⟩ := strip D L hΓ p s₂
      let ⟨f, s₁', s₂''⟩ := confluence D L hΓ ps s₂'
      ⟨f, s₁', .tail q₁ s₂''⟩

/-- Valleys compose through the shared middle: confluence of the two stars out of `b`. -/
def CValley.trans (D : CDiamond E n PEq) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (v₁ : CValley E n PEq Γ a b T) (v₂ : CValley E n PEq Γ b c T) :
    CValley E n PEq Γ a c T :=
  let ⟨f, s₁', s₂'⟩ := confluence D L hΓ v₁.right v₂.left
  ⟨f, v₁.left.trans s₁', v₂.right.trans s₂'⟩

end Rcic.Declarative.NativeValleys
