import rcic.RcicNativeValleyCert
import rcic.RcicNativeValleyDecoRows

/-!
# RcicNativeCertifiedK — re-admitting the K and η-K nodes with native certificates

#7606 refutes star confluence for the K-free `Certified` relation (`admitted_unit_no_valley`,
`trueEnvU`): the η-K peak `λp:True. True.rec M (Sort 0) p` has no certified valley of any
length, while the full relation joins it in one `ParRedT.iotaStarKEta` step.  Excluding the
two K nodes from `Certified` was wrong.  `Certified` is landed, so the enlargement is a NEW
additive inductive `CertifiedK` with the sixteen constructors of `Certified` (children in
`CertifiedK`) and the two K nodes, each carrying its own native root certificate.

**The η-K certificate is constructible natively** (`convT_iotaStarKEta`), with no uniqueness
front: the node's major is the bound variable, so `hmajor : bvar 0 : Tm` inverts
(`hasTyTInv_bvar`, `lookupType (A :: Γ) 0 = lift 0 1 A`) to a chain `lift 0 1 A ~ Tm`; the
irrelevance `bvar 0 ~ ctorMajor w` at `Tm` moves to `lift 0 1 A`; application congruence
under the η-expansion body and the legacy ι give the body conversion; η (reversed) and λ
congruence close it: `f ~ λp. (lift f) p ~ λp. (lift f) (ctorMajor w) ~ λp. rhs`.
`cstepK_iotaStarKEta_ofU` is the η-K node with that certificate.

**Two exact boundaries.**  (i) The plain `iotaStarK` node has an arbitrary major; its head's
domain (from `hasTyTInv_app` on `hlhs`) and `Tm` are two types of the major, and aligning
them is the `hUniq` obstruction recorded in `RcicNativeValleyCert`'s header.  That node
therefore STORES its certificate, supplied by the producer or by peak completion
(`NATIVE_VALLEYS_CONTINUATION.md` §1.1: `C_s⁻¹ ; C_t ; C_q`).  (ii) `ConvT.iota` takes the
legacy `DerivedIota` only; for the schema arm `DerivedIotaU.ofUS` no native conversion
constructor exists on the tree, so `convT_iotaStarKEta` takes the legacy witness; the schema
arm's η-K node is `cstepK_iotaStarKEta` with a supplied certificate.  The missing object is
exactly `ConvT E n Γ (iotaLhsOfS w) (iotaRhsOfS w) T` from the schema ι's typings.

`CStepK`, `CStarK` and the embeddings `ofCStep` / `ofCStar` are the carriers the #7604
consumer re-runs over (parametrization of `RStep`/`RStar` by the enlarged step is the next
module; the consumer's recursions never inspect a certificate).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the native η-K certificate (legacy ι arm) -/

/-- The head of an η-K spine is the lifted function. -/
theorem etaK_head_eq {w : IotaWitness E} {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0)) :
    foldApps (.const w.recRef w.ls) w.preMajor = lift 0 1 f := by
  unfold recCall at happ
  rw [foldApps_snoc] at happ
  exact (Expr.app.inj happ).1

/-- The ι redex of an η-K node is the lifted function applied to the synthesized major. -/
theorem etaK_iotaLhs_eq {w : IotaWitness E} {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0)) :
    iotaLhsOf w = .app (lift 0 1 f) (ctorMajor w) := by
  unfold iotaLhsOf recCall
  rw [foldApps_snoc, etaK_head_eq happ]

/-- The native certificate of an η-K node whose ι witness is in the legacy arm. -/
def convT_iotaStarKEta (hcl : EnvClosed E) {Γ : LCtx} {w : IotaWitness E}
    {f A B Tm rhs : Expr Nat} {u : Level}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B))
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIota E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B) :
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
  let ciota : ConvT E n (.assumption A :: Γ) (iotaLhsOf w) rhs B := .iota _ _ _ _ hι hlι hrhs
  let ciota' : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (ctorMajor w)) rhs B :=
    (etaK_iotaLhs_eq happ) ▸ ciota
  let cbody : ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) rhs B :=
    .trans _ _ _ _ _ capp' ciota'
  let c₂ : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A rhs) (.pi A B) :=
    .lam Γ A A _ rhs B u (.refl _ A _ hA) cbody
  .trans _ _ _ _ _ c₁ c₂

/-! ### the enlarged certified relation -/

/-- `Certified` with the two K nodes re-admitted, each carrying its native root
    certificate.  The sixteen other constructors are those of `Certified`, with children in
    `CertifiedK`. -/
inductive CertifiedK : {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Type
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A}
      (c : ConvT E n Γ a a A) : CertifiedK (.refl Γ a A h)
  | sortEq {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat} {h : eqN l₁ l₂}
      {hl : HasTyT E n Γ (.sort l₁) T} {hr : HasTyT E n Γ (.sort l₂) T}
      (c : ConvT E n Γ (.sort l₁) (.sort l₂) T) : CertifiedK (.sortEq Γ l₁ l₂ T h hl hr)
  | consts {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat} {h : eqNList ls ls'}
      {hl : HasTyT E n Γ (.const r ls) T} {hr : HasTyT E n Γ (.const r ls') T}
      (c : ConvT E n Γ (.const r ls) (.const r ls') T) :
      CertifiedK (.consts Γ r ls ls' T h hl hr)
  | bvarZeta {Γ : LCtx} {i : Nat} {A v v' T : Expr Nat}
      {h : Γ.get? i = some (.letBinding A v)}
      {hv : ParRedT PEq E n (Γ.drop (i + 1)) v v' A}
      {hl : HasTyT E n Γ (.bvar i) T} {hr : HasTyT E n Γ (lift 0 (i + 1) v') T}
      (c : ConvT E n Γ (.bvar i) (lift 0 (i + 1) v') T) (cv : CertifiedK hv) :
      CertifiedK (.bvarZeta Γ i A v v' T h hv hl hr)
  | delta {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b T : Expr Nat}
      {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hl : HasTyT E n Γ (.const r ls) T} {hr : HasTyT E n Γ (instantiateLevels ls b) T}
      (c : ConvT E n Γ (.const r ls) (instantiateLevels ls b) T) :
      CertifiedK (.delta Γ r ls m b T hres hbody htr hlen hwf hl hr)
  | app {Γ : LCtx} {f f' a a' A B T₀ : Expr Nat} {v w : Level}
      {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
      {ha : ParRedT PEq E n Γ a a' A}
      {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
      (c : ConvT E n Γ (.app f a) (.app f' a') (instantiate0 a B))
      (cf : CertifiedK hf) (ca : CertifiedK ha) :
      CertifiedK (.app Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr)
  | beta {Γ : LCtx} {A body body' arg arg' B : Expr Nat} {u v w : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w)}
      {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
      {ha : ParRedT PEq E n Γ arg arg' A}
      {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
      (c : ConvT E n Γ (.app (.lam A body) arg) (instantiate0 arg' body') (instantiate0 arg B))
      (cb : CertifiedK hb) (ca : CertifiedK ha) :
      CertifiedK (.beta Γ A body body' arg arg' B u v w hA hB hTy hb ha hred)
  | lam {Γ : LCtx} {A A' body body' B : Expr Nat} {u v : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.lam A' body') (.pi A B)}
      (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B)) (cb : CertifiedK hb) :
      CertifiedK (.lam Γ A A' body body' B u v hc hA hB hb hrt)
  | pi {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hc : ConvT E n Γ A A' (.sort u)}
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      {hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
      {hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v))}
      (c : ConvT E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))) :
      CertifiedK (.pi Γ A A' B B' u v hA hc hB hcB hrt)
  | letE {Γ : LCtx} {A A' value value' body body' B : Expr Nat} {u w : Level}
      {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
      {hv : ParRedT PEq E n Γ value value' A}
      {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
      {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
      {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
      {hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)}
      (c : ConvT E n Γ (.letE A value body) (.letE A' value' body') (instantiate0 value B))
      (cv : CertifiedK hv) (cb : CertifiedK hb) :
      CertifiedK (.letE Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt)
  | zeta {Γ : LCtx} {A value value' body body' B : Expr Nat} {u w : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hv : ParRedT PEq E n Γ value value' A}
      {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
      {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
      {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
      {hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B)}
      (c : ConvT E n Γ (.letE A value body) (instantiate0 value' body') (instantiate0 value B))
      (cv : CertifiedK hv) (cb : CertifiedK hb) :
      CertifiedK (.zeta Γ A value value' body body' B u w hA hv hB hTy hb hred)
  | iotaSpine {Γ : LCtx} {lhs lhs' rhs T : Expr Nat}
      {hstep : ParRedT PEq E n Γ lhs lhs' T} {hI : DerivedIotaU E lhs' rhs}
      {hred : HasTyT E n Γ lhs' T} {hrhs : HasTyT E n Γ rhs T}
      (c : ConvT E n Γ lhs rhs T) (cs : CertifiedK hstep) :
      CertifiedK (.iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs)
  | iotaStarK {Γ : LCtx} {w : IotaWitness E} {major Tm rhs T : Expr Nat} {rl : Level}
      {afs : Prop} {hrl : piBody w.famMember.mtype = .sort rl}
      {hsel : EliminationSelection rl w.nMinors afs .anySort}
      {hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF}
      {hmajor : HasTyT E n Γ major Tm} {hmk : HasTyT E n Γ (ctorMajor w) Tm}
      {hTm0 : HasTyT E n Γ Tm (.sort .zero)} {hι : DerivedIotaU E (iotaLhsOf w) rhs}
      {hlι : HasTyT E n Γ (iotaLhsOf w) T}
      {hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T}
      {hrhs : HasTyT E n Γ rhs T}
      (c : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T) :
      CertifiedK (.iotaStarK Γ w major Tm rhs T rl afs hrl hsel hfam hmajor hmk hTm0 hι hlι
        hlhs hrhs)
  | iotaStarKEta {Γ : LCtx} {w : IotaWitness E} {f A B Tm rhs : Expr Nat} {u rl : Level}
      {afs : Prop}
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
      {hlhs : HasTyT E n (.assumption A :: Γ) (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B}
      {hrhs : HasTyT E n (.assumption A :: Γ) rhs B}
      (c : ConvT E n Γ f (.lam A rhs) (.pi A B)) :
      CertifiedK (.iotaStarKEta Γ w f A B Tm rhs u rl afs happ hA hf hrl hsel hfam hmajor hmk
        hTm0 hι hlι hlhs hrhs)
  | lit {Γ : LCtx} {t : Nat} {T : Expr Nat} {hexp : HasTyT E n Γ (natExpand t) T}
      (c : ConvT E n Γ (.lit t) (natExpand t) T) : CertifiedK (.lit Γ t T hexp)
  | eta {Γ : LCtx} {f f' A B : Expr Nat} {hf : ParRedT PEq E n Γ f f' (.pi A B)}
      {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
      (c : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B))
      (cf : CertifiedK hf) :
      CertifiedK (.eta Γ f f' A B hf hl)
  | peq {Γ : LCtx} {p q T : Expr Nat} {h : PEq Γ p q T}
      (c : ConvT E n Γ p q T) : CertifiedK (.peq Γ p q T h)
  | conv {Γ : LCtx} {a b A A' : Expr Nat} {h : ParRedT PEq E n Γ a b A}
      {hc : TyConvT E n Γ A A'}
      (c : ConvT E n Γ a b A') (ch : CertifiedK h) : CertifiedK (.conv Γ a b A A' h hc)

/-- The node's own certificate. -/
def CertifiedK.root : {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} →
    CertifiedK p → ConvT E n Γ a b T
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
  | _, _, _, _, _, .iotaStarK c => c
  | _, _, _, _, _, .iotaStarKEta c => c
  | _, _, _, _, _, .lit c => c
  | _, _, _, _, _, .eta c _ => c
  | _, _, _, _, _, .peq c => c
  | _, _, _, _, _, .conv c _ => c

/-- Every K-free certificate is a certificate of the enlarged relation. -/
def CertifiedK.ofCertified : {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} →
    Certified p → CertifiedK p
  | _, _, _, _, _, .refl c => .refl c
  | _, _, _, _, _, .sortEq c => .sortEq c
  | _, _, _, _, _, .consts c => .consts c
  | _, _, _, _, _, .bvarZeta c cv => .bvarZeta c (ofCertified cv)
  | _, _, _, _, _, .delta c => .delta c
  | _, _, _, _, _, .app c cf ca => .app c (ofCertified cf) (ofCertified ca)
  | _, _, _, _, _, .beta c cb ca => .beta c (ofCertified cb) (ofCertified ca)
  | _, _, _, _, _, .lam c cb => .lam c (ofCertified cb)
  | _, _, _, _, _, .pi c => .pi c
  | _, _, _, _, _, .letE c cv cb => .letE c (ofCertified cv) (ofCertified cb)
  | _, _, _, _, _, .zeta c cv cb => .zeta c (ofCertified cv) (ofCertified cb)
  | _, _, _, _, _, .iotaSpine c cs => .iotaSpine c (ofCertified cs)
  | _, _, _, _, _, .lit c => .lit c
  | _, _, _, _, _, .eta c cf => .eta c (ofCertified cf)
  | _, _, _, _, _, .peq c => .peq c
  | _, _, _, _, _, .conv c ch => .conv c (ofCertified ch)

/-- The embedding preserves the root certificate. -/
theorem CertifiedK.root_ofCertified : {Γ : LCtx} → {a b T : Expr Nat} →
    {p : ParRedT PEq E n Γ a b T} → (c : Certified p) → (ofCertified c).root = c.root
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

/-! ### carriers over the enlarged relation -/

/-- A step of the enlarged certified relation. -/
structure CStepK (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ : LCtx) (a b T : Expr Nat) where
  step : ParRedT PEq E n Γ a b T
  cert : CertifiedK step

/-- Every K-free certified step. -/
def CStepK.ofCStep {Γ : LCtx} {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) :
    CStepK E n PEq Γ a b T :=
  ⟨s.step, .ofCertified s.cert⟩

/-- The step's certificate. -/
def CStepK.toConvT {Γ : LCtx} {a b T : Expr Nat} (s : CStepK E n PEq Γ a b T) :
    ConvT E n Γ a b T :=
  s.cert.root

/-- Index transport, as for `CStep.reindex`. -/
def CStepK.reindex {Γ : LCtx} {a b T T' : Expr Nat} (s : CStepK E n PEq Γ a b T)
    (hcT : TyConvT E n Γ T T') : CStepK E n PEq Γ a b T' :=
  ⟨.conv Γ a b T T' s.step hcT, .conv (convT_of_tyConv s.cert.root hcT) s.cert⟩

/-- Endpoint typings are the relation's, unchanged. -/
def CStepK.leftTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (s : CStepK E n PEq Γ a b T) : HasTyT E n Γ a T :=
  parRedT_hasTy_left L.typed hΓ s.step

/-- Right endpoint typing. -/
def CStepK.rightTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (s : CStepK E n PEq Γ a b T) : HasTyT E n Γ b T :=
  parRedT_hasTy_right L.typed hΓ s.step

/-- The η-K node with its native certificate (legacy ι arm). -/
def cstepK_iotaStarKEta_ofU (hcl : EnvClosed E) {Γ : LCtx} (w : IotaWitness E)
    (f A B Tm : Expr Nat) (u rl : Level) (afs : Prop)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ) (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) (iotaRhsOf w) B) :
    CStepK E n PEq Γ f (.lam A (iotaRhsOf w)) (.pi A B) :=
  ⟨.iotaStarKEta Γ w f A B Tm (iotaRhsOf w) u rl afs happ hA hf hrl hsel hfam hmajor hmk hTm0
      (.ofU w) hlι hlhs hrhs,
    .iotaStarKEta (convT_iotaStarKEta hcl happ hA hf hmajor hmk hTm0 (.of w) hlι hrhs)⟩

/-- The η-K node with a supplied certificate (any ι arm; the schema arm has no native
    conversion constructor on the tree). -/
def cstepK_iotaStarKEta {Γ : LCtx} (w : IotaWitness E) (f A B Tm rhs : Expr Nat)
    (u rl : Level) (afs : Prop)
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
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (c : ConvT E n Γ f (.lam A rhs) (.pi A B)) :
    CStepK E n PEq Γ f (.lam A rhs) (.pi A B) :=
  ⟨.iotaStarKEta Γ w f A B Tm rhs u rl afs happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs
      hrhs, .iotaStarKEta c⟩

/-- Stars of the enlarged relation. -/
inductive CStarK (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (a A : Expr Nat) (h : HasTyT E n Γ a A) : CStarK E n PEq Γ a a A
  | tail {Γ : LCtx} {a b c A : Expr Nat}
      (s : CStepK E n PEq Γ a b A) (hs : CStarK E n PEq Γ b c A) : CStarK E n PEq Γ a c A

/-- Every K-free certified star. -/
def CStarK.ofCStar : {Γ : LCtx} → {a b A : Expr Nat} → CStar E n PEq Γ a b A →
    CStarK E n PEq Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A h
  | _, _, _, _, .tail s hs => .tail (CStepK.ofCStep s) (ofCStar hs)

/-- The composed certificate. -/
def CStarK.toConvT : {Γ : LCtx} → {a b A : Expr Nat} → CStarK E n PEq Γ a b A →
    ConvT E n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A h
  | _, _, _, _, .tail s hs => .trans _ _ _ _ _ s.toConvT hs.toConvT

/-- Star transitivity. -/
def CStarK.trans : {Γ : LCtx} → {a b c A : Expr Nat} → CStarK E n PEq Γ a b A →
    CStarK E n PEq Γ b c A → CStarK E n PEq Γ a c A
  | _, _, _, _, _, .refl _ _ _ _, t => t
  | _, _, _, _, _, .tail s hs, t => .tail s (hs.trans t)

/-- Forgetting the certificates: the underlying `ParRedTStar`. -/
def CStarK.forget : {Γ : LCtx} → {a b A : Expr Nat} → CStarK E n PEq Γ a b A →
    ParRedTStar PEq E n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A h
  | _, _, _, _, .tail s hs => .tail s.step hs.forget

#print axioms etaK_head_eq
#print axioms etaK_iotaLhs_eq
#print axioms convT_iotaStarKEta
#print axioms CertifiedK
#print axioms CertifiedK.root
#print axioms CertifiedK.ofCertified
#print axioms CertifiedK.root_ofCertified
#print axioms CStepK
#print axioms CStepK.ofCStep
#print axioms CStepK.toConvT
#print axioms CStepK.reindex
#print axioms CStepK.leftTyped
#print axioms CStepK.rightTyped
#print axioms cstepK_iotaStarKEta_ofU
#print axioms cstepK_iotaStarKEta
#print axioms CStarK
#print axioms CStarK.ofCStar
#print axioms CStarK.toConvT
#print axioms CStarK.trans
#print axioms CStarK.forget

end Rcic.Declarative.NativeValleys
