import rcic.RcicParRedT
import rcic.RcicDerivedIotaU
import rcic.RcicParRedSRTyped
import rcic.RcicTypedSubstLet

/-!
# F-07 B — `parRedT_to_convT` + the `ParRedTStar` congruence kit (#6293)

Stacked on `RcicParRedT` (#6454). Two deliverables:

* **the back-lift** `parRedT_to_convT`: every `ParRedT` step lands in
  `ConvT`. The erased precedent is `parRedConvT` (`RcicParRedSRTyped`,
  R-1″), which needs `InScope` throughout because the erased `ParRed`
  carries no endpoint typings. `ParRedT`'s arms carry them (F-ParRedT-3),
  so every arm closes semantically-free — `refl/sorts/consts/zetaLocal/
  delta/app/lam/pi/letE/zeta/lit/iota` are verbatim-constructor landings,
  `bvarZeta` rides `ctxWfT_drop` + the `...LiftPrefix` pair, `beta`/`zeta`
  are the one-step legs bridged by the value-congruence twins, `app`/`conv`
  transport through `convT_of_tyConv`.

  Four leaves stay named hypotheses — none assumed, each pointing at the
  semantic route that discharges it:

  * `hPEq` — the `peq` leaf's endpoint typings; discharged by
    `PEqLeafT`'s bundled `HasTyT`s (`RcicParRedTSR`, #6482:
    `PEqLeafT E n Γ p q T := PEqT E n Γ p q ×' (p : T ×' q : T)` —
    the projections `h.2.1`/`h.2.2`). F-ParRedT-7.
  * `hPEqC` — the `peq` leaf's conversion (main's 3-place `PEqT ⊆
    ConvT` is the follow-up item; rides as a hypothesis until it
    lands).
  * `hIotaS` — `DerivedIotaT → ConvT`: the `.ofUS` (schema-witness)
    landing. `ConvT.iota` takes legacy `DerivedIota` only; the
    `DerivedIotaT`-native conv constructor is the pending rebase
    `RcicDTMetaTypedSR` names (`iotaPreserveT`/`iotaPreserveTT`, :456).
    The legacy `.ofU` half lands through `ConvT.iota` today.
  * `hUniq` — type uniqueness `HasTyT a A → HasTyT a B → TyConvT A B`,
    used exactly once: `iotaStarK`'s leg-1 transports the
    `ConvT.irr`-produced `major ↔ ctorMajor w` from `Tm` to the recursor
    application's domain `A0`. The only producer on this route is
    `DT012T_type_uniqueness` (`RcicDTMetaTypedSR:441`), `InScope`-gated
    and `Nonempty`-valued — the hypothesis is stated at data granularity
    so the consumer bridges at its own boundary.

* **the `ParRedTStar` congruence kit** — the typed siblings of
  `parRedStar_{lam,pi,app,letE}_*` (`RcicParRedDevel`): `refl` is the
  `ParRedTStar.refl` constructor, `trans` is `parRedTStar_trans`
  (shipped), and each former gets its congruence lemma(s). The
  fixed-type-index discipline (F-ParRedT-4) means a leg whose steps drift
  the index — `lam_dom` (`pi Aᵢ B` per step), `app_arg` (`inst aᵢ B`),
  `letE_val` (`inst vᵢ B`) — normalizes each step to the leg's head index
  through `ParRedT.conv`; composite `..._congr` lemmas then move whole
  legs across indices with `parRedTStar_conv`.

  `convT_inst0_valueSort`/`convT_inst0_valueSortLet` are the unconditional
  (premise-explicit) siblings of the InScope-pinned
  `convTInst0ValueSort`/`convTInst0ValueSortLet` — the three-β/three-ζ
  legs need no env front.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ### the unconditional value-congruence twins -/

/-- `instantiate0`-congruence, assumption binder: `v ↔ v' : A` converts the
    substitution instances at the body's own sort. Three β legs. -/
def convT_inst0_valueSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v v' body : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body (.sort w))
    (hv : HasTyT E n Γ v A) (hv' : HasTyT E n Γ v' A)
    (hc : ConvT E n Γ v v' A) :
    ConvT E n Γ (instantiate0 v body) (instantiate0 v' body) (.sort w) :=
  ConvT.trans _ _ _ _ _
    (ConvT.symm _ _ _ _ (ConvT.beta Γ A body v (.sort w) u hA hbody hv))
    (ConvT.trans _ _ _ _ _
      (ConvT.app Γ (.lam A body) (.lam A body) v v' A (.sort w)
        (ConvT.lam Γ A A body body (.sort w) u (ConvT.refl Γ A (.sort u) hA)
          (ConvT.refl _ body (.sort w) hbody))
        hc)
      (ConvT.beta Γ A body v' (.sort w) u hA hbody hv'))

/-- the `letBinding` twin: `v ↔ v' : A` converts the instantiate0s at the
    let's body sort. Three ζ legs around a `ConvT.letE`. -/
def convT_inst0_valueSortLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v v' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A) (hv' : HasTyT E n Γ v' A)
    (hBv : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hBv' : HasTyT E n (.letBinding A v' :: Γ) B (.sort w))
    (hc : ConvT E n Γ v v' A) :
    ConvT E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w) :=
  ConvT.trans _ _ _ _ _
    (ConvT.symm _ _ _ _ (ConvT.zeta Γ A v B (.sort w) u hA hv hBv))
    (ConvT.trans _ _ _ _ _
      (ConvT.letE Γ A A v v' B B (.sort w) u (ConvT.refl Γ A (.sort u) hA) hc
        (ConvT.refl _ B (.sort w) hBv))
      (ConvT.zeta Γ A v' B (.sort w) u hA hv' hBv'))

/-! ### the back-lift -/

/-- F-07 B: one `ParRedT` step is a `ConvT` conversion at the shared index.
    Mirrors `parRedConvT` (R-1″) arm-for-arm at `ParRedT`'s constructor
    set; every endpoint typing the erased route recovered semantically is
    a carried premise here (F-ParRedT-3). The four hypotheses are the
    honest leaves — `PEq` (typing + conv; the typing half is
    `PEqLeafT`'s bundled projections at main's 3-place `PEqT` (#6482),
    the conv half is the pending `PEqT ⊆ ConvT`
    item), `DerivedIotaT→ConvT` (the `.ofUS` landing, pending the
    `ConvT.iotaT` rebase), and type uniqueness (needed only by
    `iotaStarK`'s `Tm`-to-`A0` transport; producer today is
    `DT012T_type_uniqueness` under `InScope`). -/
def parRedT_to_convT {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B) :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → ConvT E n Γ a b T
  | _, _, _, .refl _ _ _ h => .refl _ _ _ h
  | _, _, _, .sortEq _ _ _ _ h hl _ =>
      convT_of_tyConv (.sorts _ _ _ h) (hasTyTInv_sortT hl rfl)
  | _, _, _, .consts _ _ _ _ _ h hl hr => by
      obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const hl rfl
      obtain ⟨_, _, _, hwf', _⟩ := hasTyTInv_const hr rfl
      exact convT_of_tyConv (.consts _ _ _ _ m hres hlen hwf hwf' h) hcv
  | _, _, _, .bvarZeta Γ i A v v' _ h hv hl _ => by
      obtain ⟨A', hlkT, hcv⟩ := hasTyTInv_bvar hl rfl
      have heq : A' = lift 0 (i + 1) A := by
        have h2 := lookupType_getQ_letBinding h
        rw [hlkT] at h2
        injection h2
      subst heq
      have hval : lookupValue Γ i = some (lift 0 (i + 1) v) :=
        lookupValue_getQ_letBinding h
      have hvA : HasTyT E n (Γ.drop (i + 1)) v A :=
        parRedT_hasTy_left hPEq (ctxWfT_drop hΓ (i + 1)) hv
      have hlt : i + 1 ≤ Γ.length := get?_lt_length Γ h
      have hlen : (Γ.take (i + 1)).length = i + 1 := by
        rw [List.length_take]
        exact Nat.min_eq_left hlt
      have hliftv : HasTyT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) A) := by
        have h0 := hasTyTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1)) hvA
        rw [hlen, List.take_append_drop] at h0
        exact h0
      have hliftc : ConvT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) v')
          (lift 0 (i + 1) A) := by
        have h0 := convTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1))
          (parRedT_to_convT hW (ctxWfT_drop hΓ (i + 1)) hPEq hPEqC hIotaS hUniq hv)
        rw [hlen, List.take_append_drop] at h0
        exact h0
      exact convT_of_tyConv
        (ConvT.trans Γ (.bvar i) (lift 0 (i + 1) v) (lift 0 (i + 1) v')
          (lift 0 (i + 1) A)
          (ConvT.zetaLocal Γ i _ _ hval hlkT hliftv) hliftc)
        hcv
  | _, _, _, .delta Γ r ls m b _ hres hbody htr hlen hwf hl _ => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hl rfl
      cases hres.symm.trans hres'
      exact convT_of_tyConv
        (.delta Γ r ls m b hres hbody htr hlen hwf
          (envWfT_bodyTyped hW hres hbody hlen)) hcv
  | _, _, _, .app Γ f f' a a' A B _ _ _ hf hc _ _ ha _ =>
      .app Γ f f' a a' A B
        (convT_of_tyConv
          (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hf) hc)
        (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq ha)
  | _, _, _, .beta Γ A body body' arg arg' B u v _ hA hB _ hb ha _ => by
      let cb := parRedT_to_convT hW (.assumption Γ A u hΓ hA) hPEq hPEqC
        hIotaS hUniq hb
      let ca := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq ha
      have hbody' := parRedT_hasTy_right hPEq (.assumption Γ A u hΓ hA) hb
      have harg := parRedT_hasTy_left hPEq hΓ ha
      have harg' := parRedT_hasTy_right hPEq hΓ ha
      have capp : ConvT E n Γ (.app (.lam A body) arg) (.app (.lam A body') arg')
          (instantiate0 arg B) :=
        .app Γ _ _ arg arg' A B
          (.lam Γ A A body body' B u (.refl Γ A (.sort u) hA) cb) ca
      have cbeta : ConvT E n Γ (.app (.lam A body') arg')
          (instantiate0 arg' body') (instantiate0 arg' B) :=
        .beta Γ A body' arg' B u hA hbody' harg'
      have cval : ConvT E n Γ (instantiate0 arg' B) (instantiate0 arg B)
          (.sort v) :=
        convT_inst0_valueSort hA hB harg' harg (.symm Γ arg arg' A ca)
      exact .trans Γ _ _ _ (instantiate0 arg B) capp
        (convT_of_tyConv cbeta (.of _ _ _ v cval))
  | _, _, _, .lam Γ A A' body body' B u _ hc hA _ hb _ =>
      .lam Γ A A' body body' B u hc
        (parRedT_to_convT hW (.assumption Γ A u hΓ hA) hPEq hPEqC hIotaS
          hUniq hb)
  | _, _, _, .pi Γ A A' B B' u v _ hc _ hcB _ => .pi Γ A A' B B' u v hc hcB
  | _, _, _, .letE Γ A A' value value' body body' B u _ hc hA hv _ _ hb _ =>
      .letE Γ A A' value value' body body' B u hc
        (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hv)
        (parRedT_to_convT hW
          (.letBinding Γ A u value hΓ hA (parRedT_hasTy_left hPEq hΓ hv))
          hPEq hPEqC hIotaS hUniq hb)
  | _, _, _, .zeta Γ A value value' body body' B u w hA hv hB _ hb _ => by
      let cv := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hv
      have hvA := parRedT_hasTy_left hPEq hΓ hv
      have hv'A := parRedT_hasTy_right hPEq hΓ hv
      let cb := parRedT_to_convT hW (.letBinding Γ A u value hΓ hA hvA)
        hPEq hPEqC hIotaS hUniq hb
      have hcl := envClosed_of_envWfT hW
      have hB' : HasTyT E n (.letBinding A value' :: Γ) B (.sort w) :=
        hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
          (.symm Γ value value' A cv) hv'A hB
      have hb' : HasTyT E n (.letBinding A value' :: Γ) body' B :=
        hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
          (.symm Γ value value' A cv) hv'A
          (parRedT_hasTy_right hPEq (.letBinding Γ A u value hΓ hA hvA) hb)
      have leg1 : ConvT E n Γ (.letE A value body) (.letE A value' body')
          (instantiate0 value B) :=
        .letE Γ A A value value' body body' B u (.refl Γ A (.sort u) hA) cv cb
      have leg2 : ConvT E n Γ (.letE A value' body') (instantiate0 value' body')
          (instantiate0 value B) :=
        convT_of_tyConv (.zeta Γ A value' body' B u hA hv'A hb')
          (.of _ _ _ w (convT_inst0_valueSortLet hA hv'A hvA hB' hB
            (.symm Γ value value' A cv)))
      exact .trans Γ _ _ _ _ leg1 leg2
  | _, _, _, .iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs =>
      .trans Γ lhs lhs' rhs T
        (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hstep)
        (match derivedIotaU_elim hI with
         | .inl d => .iota Γ lhs' rhs T d hred hrhs
         | .inr t => hIotaS t hred hrhs)
  | _, _, _, .iotaStarK Γ w major Tm rhs T _ _ _ _ _ hmajor hmk hTm0 hι hlι
        hlhs hrhs => by
      have hlhs' : HasTyT E n Γ
          (.app (foldApps (.const w.recRef w.ls) w.preMajor) major) T := by
        simpa only [recCall, foldApps_snoc] using hlhs
      obtain ⟨A0, B0, hfun, hargM, hcv⟩ := hasTyTInv_app hlhs' rfl
      have cmaj : ConvT E n Γ major (ctorMajor w) A0 :=
        convT_of_tyConv
          (ConvT.irr Γ Tm major (ctorMajor w) hTm0 hmajor hmk)
          (hUniq hΓ hmajor hargM)
      have capp : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major)
          (iotaLhsOf w) (instantiate0 major B0) := by
        simp only [recCall, iotaLhsOf, foldApps_snoc]
        exact .app Γ _ _ major (ctorMajor w) A0 B0
          (.refl Γ _ (.pi A0 B0) hfun) cmaj
      have cl : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major)
          (iotaLhsOf w) T := convT_of_tyConv capp hcv
      have ci : ConvT E n Γ (iotaLhsOf w) rhs T :=
        match derivedIotaU_elim hι with
        | .inl d => .iota Γ (iotaLhsOf w) rhs T d hlι hrhs
        | .inr t => hIotaS t hlι hrhs
      exact .trans Γ _ _ _ T cl ci
  | _, _, _, .iotaStarKEta Γ w f A B Tm rhs u _ _ happ hA hf _ _ _
        hmajor hmk hTm0 hι hlι hlhs hrhs => by
      have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      have hlhs' : HasTyT E n (.assumption A :: Γ)
          (.app (foldApps (.const w.recRef w.ls) w.preMajor) (.bvar 0)) B := by
        simpa only [recCall, foldApps_snoc] using hlhs
      obtain ⟨A0, B0, hfun, hargM, hcv⟩ := hasTyTInv_app hlhs' rfl
      have cmaj : ConvT E n (.assumption A :: Γ) (.bvar 0) (ctorMajor w) A0 :=
        convT_of_tyConv
          (ConvT.irr (.assumption A :: Γ) Tm (.bvar 0) (ctorMajor w) hTm0 hmajor hmk)
          (hUniq hΓ' hmajor hargM)
      have capp : ConvT E n (.assumption A :: Γ)
          (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0))
          (iotaLhsOf w) (instantiate0 (.bvar 0) B0) := by
        simp only [recCall, iotaLhsOf, foldApps_snoc]
        exact .app (.assumption A :: Γ) _ _ (.bvar 0) (ctorMajor w) A0 B0
          (.refl (.assumption A :: Γ) _ (.pi A0 B0) hfun) cmaj
      have cl : ConvT E n (.assumption A :: Γ)
          (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0))
          (iotaLhsOf w) B := convT_of_tyConv capp hcv
      have ci : ConvT E n (.assumption A :: Γ) (iotaLhsOf w) rhs B :=
        match derivedIotaU_elim hι with
        | .inl d => .iota (.assumption A :: Γ) (iotaLhsOf w) rhs B d hlι hrhs
        | .inr t => hIotaS t hlι hrhs
      have cbody : ConvT E n (.assumption A :: Γ)
          (.app (lift 0 1 f) (.bvar 0)) rhs B := by
        rw [← happ]
        exact .trans (.assumption A :: Γ) _ _ _ B cl ci
      exact .trans Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A rhs) (.pi A B)
        (.symm Γ _ _ _ (.eta Γ f A B hf))
        (.lam Γ A A (.app (lift 0 1 f) (.bvar 0)) rhs B u (.refl Γ A (.sort u) hA) cbody)
  | _, _, _, .lit Γ t T hexp => .lit Γ t (natExpand t) T (.of t) hexp
  | _, _, _, .eta Γ f _ A B hf _ =>
      .trans _ _ _ _ _
        (ConvT.eta Γ f A B (parRedT_hasTy_left hPEq hΓ hf))
        (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hf)
  | _, _, _, .peq _ _ _ _ h => hPEqC h
  | _, _, _, .conv _ _ _ _ _ h hc =>
      convT_of_tyConv (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h) hc

/-! ### the `ParRedTStar` congruence kit -/

/-- the star's left endpoint typing (off the first step / the refl tail). -/
def parRedTStar_left_typed {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat} :
    ParRedTStar PEq E n Γ a b A → HasTyT E n Γ a A
  | .refl _ _ _ h => h
  | .tail h _ => parRedT_hasTy_left hPEq hΓ h

/-- the star's right endpoint typing (off the refl tail). -/
def parRedTStar_right_typed {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat} :
    ParRedTStar PEq E n Γ a b A → HasTyT E n Γ b A
  | .refl _ _ _ h => h
  | .tail _ hs => parRedTStar_right_typed hs

/-- the star folded into one `ConvT` — `trans` over per-step back-lifts. -/
def parRedTStar_to_convT {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {a b T : Expr Nat} :
    ParRedTStar PEq E n Γ a b T → ConvT E n Γ a b T
  | .refl _ _ _ h => .refl _ _ _ h
  | .tail h hs =>
      .trans _ _ _ _ _ (parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h)
        (parRedTStar_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hs)

/-- index transport for a whole star — F-ParRedT-4 (`ParRedT.conv`) lifted
    to the multi-step. -/
def parRedTStar_conv {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T T' : Expr Nat}
    (hcT : TyConvT E n Γ T T') :
    ParRedTStar PEq E n Γ a b T → ParRedTStar PEq E n Γ a b T'
  | .refl _ _ _ h => .refl _ _ _ (hasTyT_of_tyConvT h hcT)
  | .tail h hs => .tail (.conv _ _ _ _ _ h hcT) (parRedTStar_conv hcT hs)

/-- λ body congruence — the body star is under the LEFT domain's binder;
    each step's `ParRedT.lam` needs only the reflexive domain conv. -/
def parRedTStar_lam_body {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {A b b' B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    ParRedTStar PEq E n (.assumption A :: Γ) b b' B →
    ParRedTStar PEq E n Γ (.lam A b) (.lam A b') (.pi A B)
  | .refl _ _ _ h => .refl Γ _ _ (.lam Γ A u b B hA h)
  | .tail h hs =>
      .tail (.lam Γ A A _ _ B u v (.refl Γ A (.sort u) hA) hA hB h
          (.lam Γ A u _ B hA
            (parRedT_hasTy_right hPEq (.assumption Γ A u hΓ hA) h)))
        (parRedTStar_lam_body hPEq hΓ hA hB hs)

/-- λ domain congruence — each step `λ Aᵢ.b → λ Aᵢ₊₁.b` lands at
    `pi Aᵢ B` (the domain moved), then `.conv`-normalizes to the chain's
    head index `pi A B`; under-binder typings ride `hasTyTConvAssump`
    along the accumulated domain conversion. -/
def parRedTStar_lam_dom_go {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' b B : Expr Nat} {u v : Level}
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hb : HasTyT E n (.assumption A :: Γ) b B) {Acur : Expr Nat}
    (cacc : ConvT E n Γ A Acur (.sort u)) (hAcur : HasTyT E n Γ Acur (.sort u)) :
    ParRedTStar PEq E n Γ Acur A' (.sort u) →
    ParRedTStar PEq E n Γ (.lam Acur b) (.lam A' b) (.pi A B)
  | .refl _ _ _ _ =>
      .refl Γ _ _
        (HasTyT.conv Γ (.lam Acur b) (.pi Acur B) (.pi A B) (.imax u v)
          (.lam Γ Acur u b B hAcur
            (hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc) hb))
          (.pi Γ Acur A B B u v (.symm _ _ _ _ cacc)
            (.refl _ B (.sort v)
              (hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc)
                hB))))
  | .tail h hs =>
      let cs := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h
      let hAnext := parRedT_hasTy_right hPEq hΓ h
      let cnext := ConvT.trans _ _ _ _ _ cacc cs
      let hBi := hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc) hB
      let hbi := hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc) hb
      let hBi1 := hasTyTConvAssump (envClosed_of_envWfT hW)
        (.symm _ _ _ _ cnext) hB
      let hbi1 := hasTyTConvAssump (envClosed_of_envWfT hW)
        (.symm _ _ _ _ cnext) hb
      .tail
        (.conv Γ _ _ _ _
          (.lam Γ Acur _ b b B u v cs hAcur hBi (.refl _ b B hbi)
            (HasTyT.conv Γ (.lam _ b) (.pi _ B) (.pi Acur B) (.imax u v)
              (.lam Γ _ u b B hAnext hbi1)
              (.pi Γ _ Acur B B u v (.symm _ _ _ _ cs)
                (.refl _ B (.sort v) hBi1))))
          (.of _ _ _ (.imax u v)
            (.pi Γ Acur A B B u v (.symm _ _ _ _ cacc)
              (.refl _ B (.sort v) hBi))))
        (parRedTStar_lam_dom_go hW hΓ hPEq hPEqC hIotaS hUniq hB hb cnext
          hAnext hs)

/-- λ domain congruence, public face. -/
def parRedTStar_lam_dom {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' b B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hb : HasTyT E n (.assumption A :: Γ) b B)
    (hst : ParRedTStar PEq E n Γ A A' (.sort u)) :
    ParRedTStar PEq E n Γ (.lam A b) (.lam A' b) (.pi A B) :=
  parRedTStar_lam_dom_go hW hΓ hPEq hPEqC hIotaS hUniq hB hb
    (.refl Γ A (.sort u) hA) hA hst

/-- λ full congruence: domain star then body star, the body leg at its
    natural `pi A' B` index transported back to `pi A B`. -/
def parRedTStar_lam_congr {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' b b' B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hb : HasTyT E n (.assumption A :: Γ) b B)
    (hsA : ParRedTStar PEq E n Γ A A' (.sort u))
    (hsb : ParRedTStar PEq E n (.assumption A' :: Γ) b b' B) :
    ParRedTStar PEq E n Γ (.lam A b) (.lam A' b') (.pi A B) :=
  let hcl := envClosed_of_envWfT hW
  let cA := parRedTStar_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hsA
  let hA' := parRedTStar_right_typed hsA
  let hB' := hasTyTConvAssump hcl (ConvT.symm _ _ _ _ cA) hB
  parRedTStar_trans
    (parRedTStar_lam_dom hW hΓ hPEq hPEqC hIotaS hUniq hA hB hb hsA)
    (parRedTStar_conv
      (.of _ _ _ (.imax u v)
        (.pi Γ A' A B B u v (ConvT.symm _ _ _ _ cA) (.refl _ B (.sort v) hB')))
      (parRedTStar_lam_body hPEq hΓ hA' hB' hsb))

/-- Π domain congruence — the step index `sort (imax u v)` is constant. -/
def parRedTStar_pi_dom_go {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' B : Expr Nat} {u v : Level}
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) {Acur : Expr Nat}
    (hAcur : HasTyT E n Γ Acur (.sort u))
    (cacc : ConvT E n Γ A Acur (.sort u)) :
    ParRedTStar PEq E n Γ Acur A' (.sort u) →
    ParRedTStar PEq E n Γ (.pi Acur B) (.pi A' B) (.sort (.imax u v))
  | .refl _ _ _ _ =>
      .refl Γ _ _ (.pi Γ Acur u B v hAcur
        (hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc) hB))
  | .tail h hs =>
      let cs := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h
      let hAnext := parRedT_hasTy_right hPEq hΓ h
      let cnext := ConvT.trans _ _ _ _ _ cacc cs
      let hBi := hasTyTConvAssump (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc) hB
      let hBi1 := hasTyTConvAssump (envClosed_of_envWfT hW)
        (.symm _ _ _ _ cnext) hB
      .tail
        (.pi Γ Acur _ B B u v hAcur cs hBi (.refl _ B (.sort v) hBi)
          (.pi Γ _ u B v hAnext hBi1))
        (parRedTStar_pi_dom_go hW hΓ hPEq hPEqC hIotaS hUniq hB hAnext cnext hs)

/-- Π domain congruence, public face. -/
def parRedTStar_pi_dom {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hst : ParRedTStar PEq E n Γ A A' (.sort u)) :
    ParRedTStar PEq E n Γ (.pi A B) (.pi A' B) (.sort (.imax u v)) :=
  parRedTStar_pi_dom_go hW hΓ hPEq hPEqC hIotaS hUniq hB hA
    (.refl Γ A (.sort u) hA) hst

/-- Π body congruence — the codomain star is under the LEFT domain's
    binder; each `hcB` is the back-lift. -/
def parRedTStar_pi_body {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A B B' : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) :
    ParRedTStar PEq E n (.assumption A :: Γ) B B' (.sort v) →
    ParRedTStar PEq E n Γ (.pi A B) (.pi A B') (.sort (.imax u v))
  | .refl _ _ _ h => .refl Γ _ _ (.pi Γ A u B v hA h)
  | .tail h hs =>
      let hBnext := parRedT_hasTy_right hPEq (.assumption Γ A u hΓ hA) h
      .tail (.pi Γ A A _ _ u v hA (.refl Γ A (.sort u) hA)
          (parRedT_hasTy_left hPEq (.assumption Γ A u hΓ hA) h)
          (parRedT_to_convT hW (.assumption Γ A u hΓ hA) hPEq hPEqC hIotaS
            hUniq h)
          (.pi Γ A u _ v hA hBnext))
        (parRedTStar_pi_body hW hΓ hPEq hPEqC hIotaS hUniq hA hs)

/-- Π full congruence — same index `sort (imax u v)` on both legs. -/
def parRedTStar_pi_congr {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hsA : ParRedTStar PEq E n Γ A A' (.sort u))
    (hsB : ParRedTStar PEq E n (.assumption A' :: Γ) B B' (.sort v)) :
    ParRedTStar PEq E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) :=
  parRedTStar_trans
    (parRedTStar_pi_dom hW hΓ hPEq hPEqC hIotaS hUniq hA hB hsA)
    (parRedTStar_pi_body hW hΓ hPEq hPEqC hIotaS hUniq
      (parRedTStar_right_typed hsA) hsB)

/-- app function-position congruence — the fun star is already at the
    `pi A B` index the app-step wants; the argument rides `ParRedT.refl`. -/
def parRedTStar_app_fun {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a A B : Expr Nat} {v w : Level}
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (ha : HasTyT E n Γ a A) :
    ParRedTStar PEq E n Γ f f' (.pi A B) →
    ParRedTStar PEq E n Γ (.app f a) (.app f' a) (instantiate0 a B)
  | .refl _ _ _ h => .refl Γ _ _ (.app Γ f a A B h ha)
  | .tail h hs =>
      .tail (.app Γ _ _ a a A B _ v w h (.refl Γ _) hB hTy (.refl Γ a A ha)
          (.app Γ _ a A B (parRedT_hasTy_right hPEq hΓ h) ha))
        (parRedTStar_app_fun hPEq hΓ hB hTy ha hs)

/-- app argument-position congruence — each step lands at `inst aᵢ B`
    (the left argument's instantiation), then `.conv`-normalizes to the
    chain's head index `inst a B` by the value-congruence twin. -/
def parRedTStar_app_arg_go {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {f a a' A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (ha : HasTyT E n Γ a A) {acur : Expr Nat}
    (hacur : HasTyT E n Γ acur A) (cacc : ConvT E n Γ a acur A) :
    ParRedTStar PEq E n Γ acur a' A →
    ParRedTStar PEq E n Γ (.app f acur) (.app f a') (instantiate0 a B)
  | .refl _ _ _ _ =>
      .refl Γ _ _
        (HasTyT.conv Γ (.app f acur) (instantiate0 acur B) (instantiate0 a B)
          v (.app Γ f acur A B hf hacur)
          (convT_inst0_valueSort hA hB hacur ha (.symm _ _ _ _ cacc)))
  | .tail h hs =>
      let cs := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h
      let hAnext := parRedT_hasTy_right hPEq hΓ h
      let cnext := ConvT.trans _ _ _ _ _ cacc cs
      .tail
        (.conv Γ _ _ _ _
          (.app Γ f f acur _ A B _ v v (.refl Γ f _ hf) (.refl Γ _)
            hB (hasTyT_subst0_of_envWfT hW hB hacur) h
            (HasTyT.conv Γ (.app f _) (instantiate0 _ B) (instantiate0 acur B)
              v (.app Γ f _ A B hf hAnext)
              (convT_inst0_valueSort hA hB hAnext hacur (.symm _ _ _ _ cs))))
          (.of _ _ _ v
            (convT_inst0_valueSort hA hB hacur ha (.symm _ _ _ _ cacc))))
        (parRedTStar_app_arg_go hW hΓ hPEq hPEqC hIotaS hUniq hA hB hf ha
          hAnext cnext hs)

/-- app argument congruence, public face. -/
def parRedTStar_app_arg {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {f a a' A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (ha : HasTyT E n Γ a A)
    (hsa : ParRedTStar PEq E n Γ a a' A) :
    ParRedTStar PEq E n Γ (.app f a) (.app f a') (instantiate0 a B) :=
  parRedTStar_app_arg_go hW hΓ hPEq hPEqC hIotaS hUniq hA hB hf ha ha
    (.refl Γ a A ha) hsa

/-- app full congruence: fun leg then arg leg, both at `inst a B`. -/
def parRedTStar_app_congr {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {f f' a a' A B : Expr Nat} {u v w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (ha : HasTyT E n Γ a A)
    (hsf : ParRedTStar PEq E n Γ f f' (.pi A B))
    (hsa : ParRedTStar PEq E n Γ a a' A) :
    ParRedTStar PEq E n Γ (.app f a) (.app f' a') (instantiate0 a B) :=
  parRedTStar_trans
    (parRedTStar_app_fun hPEq hΓ hB hTy ha hsf)
    (parRedTStar_app_arg hW hΓ hPEq hPEqC hIotaS hUniq hA hB
      (parRedTStar_right_typed hsf) ha hsa)

/-- `letE` annotation congruence — the value/body ride `ParRedT.refl` at
    the moving domain (the value re-typed along the accumulated conv);
    the step index `instantiate0 value B` is constant. -/
def parRedTStar_letE_ty_go {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' v b B : Expr Nat} {u w : Level}
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w))
    (hb : HasTyT E n (.letBinding A v :: Γ) b B) {Acur : Expr Nat}
    (hAcur : HasTyT E n Γ Acur (.sort u))
    (cacc : ConvT E n Γ A Acur (.sort u)) :
    ParRedTStar PEq E n Γ Acur A' (.sort u) →
    ParRedTStar PEq E n Γ (.letE Acur v b) (.letE A' v b)
      (instantiate0 v B)
  | .refl _ _ _ _ =>
      .refl Γ _ _
        (.letE Γ Acur u v B b hAcur
          (HasTyT.conv Γ v A Acur u hv cacc)
          (hasTyTConvLet (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc)
            (.refl Γ v A hv) (HasTyT.conv Γ v A Acur u hv cacc) hb))
  | .tail h hs =>
      let cs := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h
      let hAnext := parRedT_hasTy_right hPEq hΓ h
      let cnext := ConvT.trans _ _ _ _ _ cacc cs
      let hvi : HasTyT E n Γ v Acur := HasTyT.conv Γ v A Acur u hv cacc
      let hvi1 : HasTyT E n Γ v _ := HasTyT.conv Γ v A _ u hv cnext
      .tail
        (.letE Γ Acur _ v v b b B u w cs hAcur (.refl Γ v Acur hvi)
          (hasTyTConvLet (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc)
            (.refl Γ v A hv) hvi hB)
          hTy
          (.refl _ b B
            (hasTyTConvLet (envClosed_of_envWfT hW) (.symm _ _ _ _ cacc)
              (.refl Γ v A hv) hvi hb))
          (.letE Γ _ u v B b hAnext hvi1
            (hasTyTConvLet (envClosed_of_envWfT hW) (.symm _ _ _ _ cnext)
              (.refl Γ v A hv) hvi1 hb)))
        (parRedTStar_letE_ty_go hW hΓ hPEq hPEqC hIotaS hUniq hv hB hTy hb
          hAnext cnext hs)

/-- `letE` annotation congruence, public face. -/
def parRedTStar_letE_ty {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' v b B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w))
    (hb : HasTyT E n (.letBinding A v :: Γ) b B)
    (hsA : ParRedTStar PEq E n Γ A A' (.sort u)) :
    ParRedTStar PEq E n Γ (.letE A v b) (.letE A' v b)
      (instantiate0 v B) :=
  parRedTStar_letE_ty_go hW hΓ hPEq hPEqC hIotaS hUniq hv hB hTy hb hA
    (.refl Γ A (.sort u) hA) hsA

/-- `letE` value congruence — each step lands at `inst vᵢ B`, then
    `.conv`-normalizes to `inst v B` by the let-twin. -/
def parRedTStar_letE_val_go {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A v v' b B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hb : HasTyT E n (.letBinding A v :: Γ) b B) {vcur : Expr Nat}
    (hvcur : HasTyT E n Γ vcur A) (cacc : ConvT E n Γ v vcur A) :
    ParRedTStar PEq E n Γ vcur v' A →
    ParRedTStar PEq E n Γ (.letE A vcur b) (.letE A v' b)
      (instantiate0 v B)
  | .refl _ _ _ _ =>
      let hBi := hasTyTConvLet (envClosed_of_envWfT hW)
        (.refl Γ A (.sort u) hA) (.symm _ _ _ _ cacc) hvcur hB
      .refl Γ _ _
        (HasTyT.conv Γ (.letE A vcur b) (instantiate0 vcur B)
          (instantiate0 v B) w
          (.letE Γ A u vcur B b hA hvcur
            (hasTyTConvLet (envClosed_of_envWfT hW) (.refl Γ A (.sort u) hA)
              (.symm _ _ _ _ cacc) hvcur hb))
          (convT_inst0_valueSortLet hA hvcur hv hBi hB (.symm _ _ _ _ cacc)))
  | .tail h hs =>
      let cs := parRedT_to_convT hW hΓ hPEq hPEqC hIotaS hUniq h
      let hvNext := parRedT_hasTy_right hPEq hΓ h
      let cnext := ConvT.trans _ _ _ _ _ cacc cs
      let hBi := hasTyTConvLet (envClosed_of_envWfT hW) (.refl Γ A (.sort u) hA)
        (.symm _ _ _ _ cacc) hvcur hB
      let hbi := hasTyTConvLet (envClosed_of_envWfT hW) (.refl Γ A (.sort u) hA)
        (.symm _ _ _ _ cacc) hvcur hb
      let hBi1 := hasTyTConvLet (envClosed_of_envWfT hW) (.refl Γ A (.sort u) hA)
        (.symm _ _ _ _ cnext) hvNext hB
      let hbi1 := hasTyTConvLet (envClosed_of_envWfT hW) (.refl Γ A (.sort u) hA)
        (.symm _ _ _ _ cnext) hvNext hb
      .tail
        (.conv Γ _ _ _ _
          (.letE Γ A A vcur _ b b B u w (.refl Γ A (.sort u) hA) hA h
            hBi (hasTyT_substLet0_of_envWfT hW hBi hvcur)
            (.refl _ b B hbi)
            (HasTyT.conv Γ (.letE A _ b) (instantiate0 _ B)
              (instantiate0 vcur B) w
              (.letE Γ A u _ B b hA hvNext hbi1)
              (convT_inst0_valueSortLet hA hvNext hvcur hBi1 hBi
                (.symm _ _ _ _ cs))))
          (.of _ _ _ w
            (convT_inst0_valueSortLet hA hvcur hv hBi hB (.symm _ _ _ _ cacc))))
        (parRedTStar_letE_val_go hW hΓ hPEq hPEqC hIotaS hUniq hA hv hB hb
          hvNext cnext hs)

/-- `letE` value congruence, public face. -/
def parRedTStar_letE_val {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A v v' b B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hb : HasTyT E n (.letBinding A v :: Γ) b B)
    (hsv : ParRedTStar PEq E n Γ v v' A) :
    ParRedTStar PEq E n Γ (.letE A v b) (.letE A v' b)
      (instantiate0 v B) :=
  parRedTStar_letE_val_go hW hΓ hPEq hPEqC hIotaS hUniq hA hv hB hb hv
    (.refl Γ v A hv) hsv

/-- `letE` body congruence — the body star is under the LEFT binding;
    index `instantiate0 value B` constant. -/
def parRedTStar_letE_body {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {A v b b' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w)) :
    ParRedTStar PEq E n (.letBinding A v :: Γ) b b' B →
    ParRedTStar PEq E n Γ (.letE A v b) (.letE A v b') (instantiate0 v B)
  | .refl _ _ _ h => .refl Γ _ _ (.letE Γ A u v B b hA hv h)
  | .tail h hs =>
      .tail (.letE Γ A A v v b _ B u w (.refl Γ A (.sort u) hA) hA
          (.refl Γ v A hv) hB hTy h
          (.letE Γ A u v B _ hA hv
            (parRedT_hasTy_right hPEq (.letBinding Γ A u v hΓ hA hv) h)))
        (parRedTStar_letE_body hPEq hΓ hA hv hB hTy hs)

/-- `letE` full congruence — erased order: body leg, then value leg, then
    type leg. The type leg's natural index `inst v' B` is moved back to
    `inst v B` by `parRedTStar_conv`. -/
def parRedTStar_letE_congr {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {A A' v v' b b' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w))
    (hsA : ParRedTStar PEq E n Γ A A' (.sort u))
    (hsv : ParRedTStar PEq E n Γ v v' A)
    (hsb : ParRedTStar PEq E n (.letBinding A v :: Γ) b b' B) :
    ParRedTStar PEq E n Γ (.letE A v b) (.letE A' v' b')
      (instantiate0 v B) :=
  let hcl := envClosed_of_envWfT hW
  let cvv := parRedTStar_to_convT hW hΓ hPEq hPEqC hIotaS hUniq hsv
  let hv' := parRedTStar_right_typed hsv
  let hb' := parRedTStar_right_typed hsb
  let hBv := hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
    (ConvT.symm _ _ _ _ cvv) hv' hB
  let hbb := hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
    (ConvT.symm _ _ _ _ cvv) hv' hb'
  let hTyv := hasTyT_substLet0_of_envWfT hW hBv hv'
  parRedTStar_trans
    (parRedTStar_letE_body hPEq hΓ hA hv hB hTy hsb)
    (parRedTStar_trans
      (parRedTStar_letE_val hW hΓ hPEq hPEqC hIotaS hUniq hA hv hB hb' hsv)
      (parRedTStar_conv
        (.of _ _ _ w
          (convT_inst0_valueSortLet hA hv' hv hBv hB
            (ConvT.symm _ _ _ _ cvv)))
        (parRedTStar_letE_ty hW hΓ hPEq hPEqC hIotaS hUniq hA hv' hBv hTyv hbb
          hsA)))

end Rcic.Declarative
