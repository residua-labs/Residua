/-
RCIC — SUBJECT REDUCTION FOR PARALLEL REDUCTION (00 §19.3 F-05b,
§19.4; the conditional theorem the wall record's route change names).

WHAT IS HERE. `parRedSR`: every `ParRed` step preserves the subject's
type ON THE NOSE, conditional on the two named §19.2 rows the landed
head-reduction SR already consumes (`PiConvInj`, `FamAppConvInj`) plus
`EnvWf` and `CtxWf`. Thirteen arms, mutual with
`parRedArgsSR` (the n-ary application-spine mover), recursion on
`parRedW` (`RcicParRedWeight` — the diamond measure, reused per 00
§19.4; no second measure is written).

WHAT IS NOT HERE, AND WHY (read before proposing a successor).
`parRedSR` does NOT close the three §19.2 rows and is not stated as if
it did. The ring `characterization → noTypeIsProof → parRedSR →
PiConvInj → characterization` is INTACT: `hpci` still enters at two of
thirteen arms (`beta`, through `hasTyLamInv`'s Π-conversion, exactly
as `oneStepSR.beta` consumes it; and `iotaSpine`, through
`iotaPreserve`). What this file changes is the ring's SHAPE, not its
existence — see the three O-3 corrections recorded in
`RcicConvChar.lean`'s header (C-1 / C-2 / C-3) and 00 §19.3 F-05b.

THREE ROUTES DELIBERATELY NOT TAKEN (each has a compiled reason):
* `NoSortProp` — a single statement through which the three `irr` cuts
  would factor. NOT REFUTED, and NOT CHEAPER: its `.pi` arm is BLOCKED
  on an unlanded row, artifact below (`noSortProp_piArm_witness` /
  `noSortProp_piArm_readout`). `hasTyPiInv` on `Π (Q : Prop). Q : Prop`
  hands back `Conv Γ (.sort (.imax u v)) T`, and at `v = .zero` the
  level equation `eqN (.imax u .zero) .zero` is TRUE (`eqN_imax_zero`),
  with the witness inhabited at EVERY `E`, `n`, `Γ` — no junk
  environment, no junk context, so `EnvWf` and `CtxWf` cannot cut it.
  The typing hypothesis therefore contributes NO contradiction at that
  arm, and the whole burden falls on `Conv Γ (.sort w) (.pi A B) →
  False` — "no sort converts to a Π" — a characterization row of the
  very ring the statement was meant to shortcut. (Corrected 2026-09-05
  after a review finding on #3815: the earlier wording "REFUTED"
  claimed a counterexample this artifact does not construct — it never
  exhibits `Conv Γ (.sort w) (.pi A B)`.)
* Re-opening `parRed_diamond` (sealed, `RcicParRedDiamond`) to add an
  irrelevance step to `ParRed`: that relocates the ring into the
  diamond, which re-opens the confluence face.
* An untyped `Conv → Join` characterization: `Conv.irr` / `Conv.eta`
  are exactly what `RedOnly` excises, and cutting them needs the
  subject's typing moved along a reduction — this file's theorem — at
  INNER `trans` nodes with arbitrary endpoints, where `hasTySortInv` is
  inapplicable.

NO NEW OBLIGATION IS INTRODUCED. Every arm closes on the named set
(`PiConvInj` / `FamAppConvInj` / `EnvWf` / `CtxWf`, plus the six
transport premises `hasTySubst` / `hasTySubstLet` already consume) or
on nothing.

`LitPreserve` LEFT this set (segment 7a, 00 §19.7 E-LitP): the row was
discharged VACUOUSLY — `HasTy` then had no `lit` rule — and O-2
deleted the `hLitP` premise from `parRedSR` / `parRedArgsSR` /
`parRedStarSR`. TRIPWIRE FIRED (DT-017, 00 §20.11): `HasTy.lit` landed
and the row is discharged FOR REAL by the sealed `litPreserve`
(`RcicInvertFamily.lean`), the `lit` arm obtaining the fact from
`litPreserve E n`; `hLitP` is re-carried NOWHERE and this set is
unchanged.
-/
import rcic.RcicDTMeta
import rcic.RcicConvChar
import rcic.RcicParRed

namespace Rcic.Declarative

set_option maxHeartbeats 1000000

/-! ## W0 — infrastructure the congruence arms need

None of the following consumes an open row. Each is a projection or a
transport of a landed judgment, in the idiom of the lemma it mirrors.
-/

/-- MULTI-WEAKENING: a typing in a TAIL of `Γ` transports up into `Γ`,
lifting subject and type by the number of dropped declarations.

This is the second half of what `ParRed.bvarZeta` needs (the first is
`ctxWfLookupValueAt`, `RcicInvertFamily`): the value premise reduces in
`Γ.drop (i+1)`, so the IH's OUTPUT lands there and has to be carried
back. `ctxWfLookupValue` (`RcicDTMeta`) cannot serve — it is this
transport already applied, with no inverse. Fold: `hasTyWeaken` at
cutoff 0 plus `lift_lift_merge`, exactly `convWeaken_lctx`'s shape on
the other judgment. -/
def hasTyWeaken_drop {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    (Γ : LCtx) → (k : Nat) → k ≤ Γ.length → {e A : Expr Nat} →
    HasTy E n (Γ.drop k) e A → HasTy E n Γ (lift 0 k e) (lift 0 k A)
  | _, 0, _, _, _, h => by
      simp only [List.drop_zero] at h
      rw [lift_zero, lift_zero]
      exact h
  | [], _k + 1, hk, _, _, _ => by
      simp only [List.length_nil] at hk
      omega
  | d :: Γ, k + 1, hk, e, A, h => by
      simp only [List.drop_succ_cons] at h
      simp only [List.length_cons] at hk
      have ih := hasTyWeaken_drop hE Γ k (by omega) h
      have hw := hasTyWeaken d hE (c := 0) ih
      simp only [insertAt_zero] at hw
      rw [lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le _) e,
          lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le _) A] at hw
      exact hw

/-- The universe-well-formedness side condition of `HasTy.const`, read
off a const typing. `hasTyConstInv` does not return it (its tuple shape
is sealed, 00 §20.6), so it is read by its own fording recursion; the
`.conv` arm peels, every other arm is source-disjoint. Consumer:
`ParRed.consts`, which must REBUILD a `HasTy.const` at the drifted
level list. -/
theorem hasTyConstWf {E : ResolvedEnv} {n : Nat} {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .const r ls →
    ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n
  | _, _, _, .const _ _ _ _ _ _ hwf, heq => by
      injection heq with h1 h2; subst h1; subst h2; exact hwf
  | _, _, _, .conv _ _ _ _ h _, heq => hasTyConstWf h heq
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `hwf` transports along `=ₙ`: `eqN` is agreement of `eval` at EVERY
valuation, in particular at the empty one, which is the only valuation
`HasTy.const`'s side condition names. -/
theorem eqNList_hwf {n : Nat} :
    {ls ls' : List Level} → eqNList ls ls' →
    (∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n) →
    ∀ l ∈ ls', ∃ k, eval (fun _ => none) l = none ∨ k < n
  | [], [], _, _, _, hl => by simp only [List.not_mem_nil] at hl
  | [], _ :: _, h, _, _, _ => False.elim h
  | _ :: _, [], h, _, _, _ => False.elim h
  | a :: as, b :: bs, h, hwf, l, hl => by
      rcases List.mem_cons.mp hl with hlb | hlbs
      · subst hlb
        have ⟨k, hk⟩ := hwf a (List.mem_cons_self a as)
        refine ⟨k, ?_⟩
        rcases hk with hk1 | hk2
        · exact Or.inl ((h.1 (fun _ => none)).symm.trans hk1)
        · exact Or.inr hk2
      · exact eqNList_hwf h.2 (fun x hx => hwf x (List.mem_cons_of_mem a hx)) l hlbs

/-- HEAD MOVER at a constant: level drift on a `const` head does not
change what the head can be typed at. This is the `f ↦ f'` argument
`parRedArgsSR` takes, at the only two heads `ParRed.iotaSpine` moves
(the recursor's and the constructor's), and it is also `ParRed.consts`'
whole content. -/
def hasTyConstMove {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} (hls : eqNList ls ls') (S : Expr Nat)
    (h : HasTy E n Γ (.const r ls) S) : HasTy E n Γ (.const r ls') S := by
  have ⟨m, hres, hlen, hcv⟩ := hasTyConstInv h rfl
  have hwf := hasTyConstWf h rfl
  have hlen' : ls'.length = m.arity := by
    rw [← eqNList_length ls ls' hls]; exact hlen
  exact .conv _ _ _ _ (.const Γ r ls' m hres hlen' (eqNList_hwf hls hwf))
    (.trans _ _ _ _ (convInstantiateLevels m.mtype (eqNList_symm hls) Γ) hcv)

/-! ### The letBinding-declaration conversion morphism

`hasTyConvAssump` / `convConvAssump` / `stepConvAssump` (`RcicConvChar`)
replace an ASSUMPTION's type. `ParRed.letE` and `ParRed.zeta` reduce a
`letBinding`'s type AND its stored value under the binder, so they need
the letBinding analogue — which does not exist, and is strictly harder
for one measured reason: a `letBinding` is read by TWO lookups.
`lookupType` is repaired by `.conv`, exactly as in the assumption case;
`lookupValue` is NOT insensitive to the replacement
(`lookupValue_replace_assump` has no letBinding analogue, and cannot),
so `Step` does not transport as a `Step`.

SHAPE RULING (recorded before building): the `Step` half DEGRADES to
`Conv`. `Step Γ (.bvar i) (lift 0 (i+1) v)` becomes
`Conv Γ' (.bvar i) (lift 0 (i+1) v)` built as
`.trans (.step (zetaLocal at v')) (lifted hcv)`. That is sound because
`Conv` is what the consumer (`Conv.step`, `HasTy.conv`) actually needs,
and it is the same absorption `convSubstLet`'s `.step` arm already
performs on `stepSubstLet`'s `⊕'` (`RcicSubstLet`). `stepConvLetAt` is
therefore NOT mutual with the pair below; it is a standalone
`Step → Conv` transport. -/

/-- `Step` under a replaced let declaration, degraded to `Conv` (the
shape ruling above). Only the `zetaLocal`-at-the-replaced-index arm is
non-trivial; every other `Step` constructor is context-blind or reads
`lookupValue` away from the replacement. -/
def stepConvLetAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n) (hcv : Conv E n Γ v' v) :
    (Δ : LCtx) → {a b : Expr Nat} →
    Step E n (Δ ++ LocalDecl.letBinding A v :: Γ) a b →
    Conv E n (Δ ++ LocalDecl.letBinding A' v' :: Γ) a b
  | _, _, _, .beta _ A0 body arg => .step _ _ _ (.beta _ A0 body arg)
  | _, _, _, .zeta _ A0 value body => .step _ _ _ (.zeta _ A0 value body)
  | Δ, _, _, .zetaLocal _ i v0 hvl => by
      by_cases hi : i = Δ.length
      · subst hi
        have heq : some v0 = some (lift 0 (Δ.length + 1) v) :=
          hvl.symm.trans (lookupValue_replace_let_zero Δ A v Γ)
        injection heq with hv0
        subst hv0
        exact .trans _ _ _ _
          (.step _ _ _
            (.zetaLocal _ Δ.length (lift 0 (Δ.length + 1) v')
              (lookupValue_replace_let_zero Δ A' v' Γ)))
          (convLift_prefix_decl hE Δ (LocalDecl.letBinding A' v') hcv)
      · exact .step _ _ _
          (.zetaLocal _ i v0
            ((lookupValue_replace_let_ne Δ A v A' v' Γ i hi).symm.trans hvl))
  | _, _, _, .delta _ r ls m b hres hbody htr =>
      .step _ _ _ (.delta _ r ls m b hres hbody htr)
  | _, _, _, .iota _ lhs rhs h => .step _ _ _ (.iota _ lhs rhs h)
  | _, _, _, .lit _ t exp h => .step _ _ _ (.lit _ t exp h)

mutual

/-- `Conv` under a replaced let declaration. Template:
`convConvAssumpAt` (`RcicConvChar`), with the `.step` arm absorbing
`stepConvLetAt`'s already-degraded `Conv`. -/
def convConvLetAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n)
    (hcA : Conv E n Γ A' A) (hcv : Conv E n Γ v' v) :
    (Δ : LCtx) → {a b : Expr Nat} →
    Conv E n (Δ ++ LocalDecl.letBinding A v :: Γ) a b →
    Conv E n (Δ ++ LocalDecl.letBinding A' v' :: Γ) a b
  | _, _, _, .refl _ a => .refl _ a
  | Δ, _, _, .symm _ _ _ h => .symm _ _ _ (convConvLetAt hE hcA hcv Δ h)
  | Δ, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (convConvLetAt hE hcA hcv Δ h1)
        (convConvLetAt hE hcA hcv Δ h2)
  | Δ, _, _, .step _ _ _ hs => stepConvLetAt hE hcv Δ hs
  | Δ, _, _, .app _ _ _ _ _ h1 h2 =>
      .app _ _ _ _ _ (convConvLetAt hE hcA hcv Δ h1)
        (convConvLetAt hE hcA hcv Δ h2)
  | Δ, _, _, .lam _ A0 _ _ _ hA hb =>
      .lam _ _ _ _ _ (convConvLetAt hE hcA hcv Δ hA)
        (convConvLetAt hE hcA hcv (LocalDecl.assumption A0 :: Δ) hb)
  | Δ, _, _, .pi _ A0 _ _ _ hA hb =>
      .pi _ _ _ _ _ (convConvLetAt hE hcA hcv Δ hA)
        (convConvLetAt hE hcA hcv (LocalDecl.assumption A0 :: Δ) hb)
  | Δ, _, _, .letE _ A0 _ v0 _ _ _ hA hv hb =>
      .letE _ _ _ _ _ _ _ (convConvLetAt hE hcA hcv Δ hA)
        (convConvLetAt hE hcA hcv Δ hv)
        (convConvLetAt hE hcA hcv (LocalDecl.letBinding A0 v0 :: Δ) hb)
  | _, _, _, .sorts _ l1 l2 h => .sorts _ l1 l2 h
  | _, _, _, .consts _ r ls ls' h => .consts _ r ls ls' h
  | Δ, _, _, .eta _ f A0 B0 hh =>
      .eta _ f A0 B0 (hasTyConvLetAt hE hcA hcv Δ hh)
  | Δ, _, _, .irr _ P p q hP hp hq =>
      .irr _ P p q (hasTyConvLetAt hE hcA hcv Δ hP)
        (hasTyConvLetAt hE hcA hcv Δ hp) (hasTyConvLetAt hE hcA hcv Δ hq)

/-- `HasTy` under a replaced let declaration. The only non-trivial arm
is `HasTy.bvar` at the replaced index, repaired with `.conv` and the
prefix-weakened `hcA` — the same repair `hasTyConvAssumpAt` makes. -/
def hasTyConvLetAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n)
    (hcA : Conv E n Γ A' A) (hcv : Conv E n Γ v' v) :
    (Δ : LCtx) → {e T : Expr Nat} →
    HasTy E n (Δ ++ LocalDecl.letBinding A v :: Γ) e T →
    HasTy E n (Δ ++ LocalDecl.letBinding A' v' :: Γ) e T
  | _, _, _, .sort _ l => .sort _ l
  | Δ, _, _, .bvar _ i T h => by
      by_cases hi : i = Δ.length
      · subst hi
        have heq : some T = some (lift 0 (Δ.length + 1) A) :=
          h.symm.trans (lookupType_replace_let_zero Δ A v Γ)
        injection heq with hTeq
        subst hTeq
        exact .conv _ _ _ _
          (.bvar _ Δ.length _ (lookupType_replace_let_zero Δ A' v' Γ))
          (convLift_prefix_decl hE Δ (LocalDecl.letBinding A' v') hcA)
      · exact .bvar _ i T
          ((lookupType_replace_let_ne Δ A v A' v' Γ i hi).symm.trans h)
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m hres hlen hwf
  | Δ, _, _, .pi _ A0 u B0 w hA hB =>
      .pi _ _ u _ w (hasTyConvLetAt hE hcA hcv Δ hA)
        (hasTyConvLetAt hE hcA hcv (LocalDecl.assumption A0 :: Δ) hB)
  | Δ, _, _, .lam _ A0 u body B0 hA hbody =>
      .lam _ _ u _ _ (hasTyConvLetAt hE hcA hcv Δ hA)
        (hasTyConvLetAt hE hcA hcv (LocalDecl.assumption A0 :: Δ) hbody)
  | Δ, _, _, .app _ f a A0 B0 hf ha =>
      .app _ _ _ _ _ (hasTyConvLetAt hE hcA hcv Δ hf)
        (hasTyConvLetAt hE hcA hcv Δ ha)
  | Δ, _, _, .letE _ A0 u value B0 hA hv0 hb =>
      .letE _ _ u _ _ (hasTyConvLetAt hE hcA hcv Δ hA)
        (hasTyConvLetAt hE hcA hcv Δ hv0)
        (hasTyConvLetAt hE hcA hcv (LocalDecl.letBinding A0 value :: Δ) hb)
  | Δ, _, _, .conv _ e T1 T2 h hcvv =>
      .conv _ _ _ _ (hasTyConvLetAt hE hcA hcv Δ h)
        (convConvLetAt hE hcA hcv Δ hcvv)
  | Δ, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyConvLetAt hE hcA hcv Δ hexp)

end

/-- The `Δ = []` readings. -/
def stepConvLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n) (hcv : Conv E n Γ v' v)
    {a b : Expr Nat}
    (h : Step E n (LocalDecl.letBinding A v :: Γ) a b) :
    Conv E n (LocalDecl.letBinding A' v' :: Γ) a b :=
  stepConvLetAt (A := A) (A' := A') hE hcv [] h

def convConvLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n)
    (hcA : Conv E n Γ A' A) (hcv : Conv E n Γ v' v) {a b : Expr Nat}
    (h : Conv E n (LocalDecl.letBinding A v :: Γ) a b) :
    Conv E n (LocalDecl.letBinding A' v' :: Γ) a b :=
  convConvLetAt hE hcA hcv [] h

def hasTyConvLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} (hE : EnvWf E n)
    (hcA : Conv E n Γ A' A) (hcv : Conv E n Γ v' v) {e T : Expr Nat}
    (h : HasTy E n (LocalDecl.letBinding A v :: Γ) e T) :
    HasTy E n (LocalDecl.letBinding A' v' :: Γ) e T :=
  hasTyConvLetAt hE hcA hcv [] h

/-! ## W1-W3 — the conditional subject-reduction theorem

NOSE FORM. `parRedSR` concludes `HasTy E n Γ e' A` — the SAME type,
not a `Σ' B, HasTy e' B ×' Conv A B`. The two are interderivable
(`B := A` with `Conv.refl` one way, `HasTy.conv … (Conv.symm)` the
other), so this is not a strengthening; it is the form four of
`oneStepSR`'s six arms already return, and `IotaPreserve` /
`LitPreserve` are already stated in it (`LitPreserve` is no longer a
premise here — segment 7a discharged it vacuously, 00 §19.7 E-LitP,
and DT-017's `HasTy.lit` discharged it for real, `litPreserve`,
00 §20.11).

MEASURE. Structural on the `ParRed` / `ParRedArgs` derivation, in the
mutual block `parRed_to_conv` / `parRedArgs_foldApps_to_conv` already
uses (`RcicParRedCore`) — every recursive call is on a CONSTRUCTOR
PREMISE of its own arm. Per 00 §19.4 no second measure is written;
`parRedW` (`RcicParRedWeight`) remains the one measure for any
`ParRed` recursion that needs a numeric one.

WHERE THE OPEN ROWS ENTER — measured, two of thirteen arms:
* `beta`: `hpci` on `hasTyLamInv`'s `Conv Γ (.pi A B_lam) (.pi A_inv
  B_inv)`, a SUBDERIVATION of the input typing — byte-identical to
  `oneStepSR.beta`'s consumption.
* `iotaSpine`: `iotaPreserve hpci hfaci hE`.
The eleven others consume NOTHING from the §19.2 ledger. In
particular the app-congruence arm does NOT need `PiConvInj`
(correction C-1): `hasTyAppInv` hands back the function's Π-typing
directly, the IH returns AT that Π in nose form, and the argument's
movement is absorbed by `conv_instantiate0_value` — which is
typing-premise-free. The recorded hop-3 diagnosis
("SR knows `Conv Γ (.pi A B) T_f` only as the OUTPUT of its own IH")
named an inversion that is avoidable, not a necessity. -/

mutual

/-- Subject reduction for ONE parallel step (00 §19.3 F-05b,
conditional). Thirteen arms; `hpci` at `beta`, `hpci`+`hfaci` (through
`iotaPreserve`) at `iotaSpine`, nothing at the other eleven.

The body matches on `e, e', hr, h` — the REDUCTION discriminant ahead
of the TYPING one. That order is forced by the elaborator, not chosen:
with the typing discriminant first, the `e` metavariable is already
fixed when the `ParRed` constructor pattern is elaborated, and any
constructor that refines `e` to a shape containing a NAMED pattern
variable (`sortEq`'s `l₁`, `app`'s `f`, `consts`' `r`) fails the scope
check. The binder order of the STATEMENT is unaffected. -/
noncomputable def parRedSR {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) {e A e' : Expr Nat}
    (h : HasTy E n Γ e A) (hr : ParRed E n Γ e e') :
    HasTy E n Γ e' A :=
  match e, e', hr, h with
  | _, _, .refl _ _, h => h
  | _, _, .sortEq Γ l₁ l₂ hl, h => by
      have hcv := hasTySortInv h rfl
      exact .conv _ _ _ _ (.sort Γ l₂)
        (.trans _ _ _ _
          (.sorts Γ (.succ l₂) (.succ l₁) (eqN_succ_congr (eqN_symm hl)))
          hcv)
  | _, _, .consts _ _ _ _ hl, h => hasTyConstMove hl _ h
  | _, _, .bvarZeta Γ i A0 _v _v' hlk hv, h => by
      have ⟨A_lk, hlkT, hcv⟩ := hasTyBvarInv h rfl
      have heq : some A_lk = some (lift 0 (i + 1) A0) :=
        hlkT.symm.trans (lookupType_getQ_letBinding hlk)
      injection heq with hAeq
      subst hAeq
      have hv'ty := parRedSR hpci hfaci hE (ctxWf_drop hΓ (i + 1))
        (ctxWfLookupValueAt hΓ hlk) hv
      have hlen : i + 1 ≤ Γ.length := get?_lt_length Γ hlk
      exact .conv _ _ _ _ (hasTyWeaken_drop hE Γ (i + 1) hlen hv'ty) hcv
  | _, _, .delta Γ r ls m b hres hbody _htr, h => by
      have ⟨m', hres', hlen, hcv⟩ := hasTyConstInv h rfl
      have hmeq : some m = some m' := hres.symm.trans hres'
      injection hmeq with hmeq'
      subst hmeq'
      exact .conv _ _ _ _ (envWf_bodyTyped hE Γ r m b ls hres hbody hlen) hcv
  | _, _, .app Γ _ f' _ a' hf ha, h => by
      have ⟨A0, B0, hf0, ha0, hcv⟩ := hasTyAppInv h rfl
      exact .conv _ _ _ _
        (.app Γ f' a' A0 B0
          (parRedSR hpci hfaci hE hΓ hf0 hf)
          (parRedSR hpci hfaci hE hΓ ha0 ha))
        (.trans _ _ _ _
          (conv_instantiate0_value (B := B0)
            (.symm _ _ _ (parRed_to_conv hE ha)))
          hcv)
  | _, _, .beta Γ A0 _A0' _body _body' arg arg' _hA hb ha, h => by
      have ⟨A_inv, B_inv, hfl, ha0, hcv⟩ := hasTyAppInv h rfl
      have ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyLamInv hfl rfl
      have ⟨hdom, hcod⟩ := hpci hE Γ A0 B_lam A_inv B_inv hΓ hcv_lam
      have ha' : HasTy E n Γ arg A0 := .conv _ _ _ _ ha0 (.symm _ _ _ hdom)
      have harg' := parRedSR hpci hfaci hE hΓ ha' ha
      have hbody' := parRedSR hpci hfaci hE
        (CtxWf.assumption Γ A0 u hΓ hA0ty) hbody hb
      have hget : (LocalDecl.assumption A0 :: Γ)[(0:Nat)]? =
          some (.assumption A0) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove arg' 0 (LocalDecl.assumption A0 :: Γ))
          (lift 0 0 arg') (lift 0 0 A0) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact harg'
      have hty0 := hasTySubst (j := 0) hE arg' A0 hbody' hget hvty
      have hcod0 := convSubst (j := 0) hE arg' A0 hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hty0 hcod0
      exact .conv _ _ _ _ hty0
        (.trans _ _ _ _ hcod0
          (.trans _ _ _ _
            (conv_instantiate0_value (B := B_inv)
              (.symm _ _ _ (parRed_to_conv hE ha)))
            hcv))
  | _, _, .lam Γ A0 A0' _b b' hA hb, h => by
      have ⟨u, B, hA0ty, hbty, hcv⟩ := hasTyLamInv h rfl
      have hA0'ty := parRedSR hpci hfaci hE hΓ hA0ty hA
      have hb'ty := parRedSR hpci hfaci hE
        (CtxWf.assumption Γ A0 u hΓ hA0ty) hbty hb
      exact .conv _ _ _ _
        (.lam Γ A0' u b' B hA0'ty
          (hasTyConvAssump hE (.symm _ _ _ (parRed_to_conv hE hA)) hb'ty))
        (.trans _ _ _ _
          (.pi Γ A0' A0 B B (.symm _ _ _ (parRed_to_conv hE hA))
            (.refl (LocalDecl.assumption A0' :: Γ) B))
          hcv)
  | _, _, .pi Γ A0 A0' _b b' hA hb, h => by
      have ⟨u, w, hA0ty, hbty, hcv⟩ := hasTyPiInv h rfl
      have hA0'ty := parRedSR hpci hfaci hE hΓ hA0ty hA
      have hb'ty := parRedSR hpci hfaci hE
        (CtxWf.assumption Γ A0 u hΓ hA0ty) hbty hb
      exact .conv _ _ _ _
        (.pi Γ A0' u b' w hA0'ty
          (hasTyConvAssump hE (.symm _ _ _ (parRed_to_conv hE hA)) hb'ty))
        hcv
  | _, _, .letE Γ A0 A0' v v' _b b' hA hv hb, h => by
      have ⟨u, B, hA0ty, hvty, hbty, hcv⟩ := hasTyLetInv h rfl
      have hA0'ty := parRedSR hpci hfaci hE hΓ hA0ty hA
      have hv'ty0 := parRedSR hpci hfaci hE hΓ hvty hv
      have hb'ty := parRedSR hpci hfaci hE
        (CtxWf.letBinding Γ A0 u v hΓ hA0ty hvty) hbty hb
      exact .conv _ _ _ _
        (.letE Γ A0' u v' B hA0'ty
          (.conv _ _ _ _ hv'ty0 (parRed_to_conv hE hA))
          (hasTyConvLet hE (.symm _ _ _ (parRed_to_conv hE hA))
            (.symm _ _ _ (parRed_to_conv hE hv)) hb'ty))
        (.trans _ _ _ _
          (conv_instantiate0_value (B := B)
            (.symm _ _ _ (parRed_to_conv hE hv)))
          hcv)
  | _, _, .zeta Γ A0 _A0' v v' _b b' _hA hv hb, h => by
      have ⟨u, B, hA0ty, hvty, hbty, hcv⟩ := hasTyLetInv h rfl
      have hv'ty := parRedSR hpci hfaci hE hΓ hvty hv
      have hb'ty := parRedSR hpci hfaci hE
        (CtxWf.letBinding Γ A0 u v hΓ hA0ty hvty) hbty hb
      have hb'ty' := hasTyConvLet hE (.refl Γ A0)
        (.symm _ _ _ (parRed_to_conv hE hv)) hb'ty
      have hget : (LocalDecl.letBinding A0 v' :: Γ)[(0:Nat)]? =
          some (.letBinding A0 v') := List.getElem?_cons_zero
      have hvty0 : HasTy E n
          (substRemove v' 0 (LocalDecl.letBinding A0 v' :: Γ))
          (lift 0 0 v') (lift 0 0 A0) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hv'ty
      have hty0 := hasTySubstLet (j := 0) hE A0 v' hb'ty' hget hvty0
      rw [substRemove_zero_cons, lift_zero] at hty0
      exact .conv _ _ _ _ hty0
        (.trans _ _ _ _
          (conv_instantiate0_value (B := B)
            (.symm _ _ _ (parRed_to_conv hE hv)))
          hcv)
  | _, _, .iotaSpine Γ w2 lsR lsC hlsR hlsC _pre pre' fields fields'
        hf ha _hpreLen _hfieldsLen hlhs, h => by
      simp only [recCall] at h
      rw [foldApps_snoc] at h
      have ⟨A0, B0, hfun, harg, hcv⟩ := hasTyAppInv h rfl
      have hfun' := parRedArgsSR hpci hfaci hE hΓ hf
        (hasTyConstMove (eqNList_symm hlsR)) hfun
      have harg' := parRedArgsSR hpci hfaci hE hΓ ha
        (hasTyConstMove (eqNList_symm hlsC)) harg
      have hmajconv : Conv E n Γ
          (foldApps (.const w2.ctorRef lsC) fields)
          (foldApps (.const w2.ctorRef w2.lsC) fields') :=
        parRedArgs_foldApps_to_conv hE ha
          (.consts Γ w2.ctorRef lsC w2.lsC (eqNList_symm hlsC))
      have hlhsTy : HasTy E n Γ (iotaLhsOf w2) A := by
        rw [hlhs]
        simp only [recCall]
        rw [foldApps_snoc]
        exact .conv _ _ _ _
          (.app Γ (foldApps (.const w2.recRef w2.ls) pre')
            (foldApps (.const w2.ctorRef w2.lsC) fields') A0 B0 hfun' harg')
          (.trans _ _ _ _
            (conv_instantiate0_value (B := B0) (.symm _ _ _ hmajconv))
            hcv)
      exact iotaPreserve hpci hfaci hE Γ (iotaLhsOf w2) (iotaRhsOf w2) A
        (.of w2) (envWf_iotaTyping hE w2) hΓ hlhsTy
  | _, _, .lit Γ t, h =>
      litPreserve E n Γ t (natExpand t) A (.of t) h

/-- The n-ary application-spine mover: correction C-1 applied along a
whole `ParRedArgs`, with the HEAD's movement supplied as an argument.
`ParRed.iotaSpine` reduces two const-headed spines at once (the
recursor's prefix and the constructor's fields), and each head only
drifts in its level list, so the head argument is `hasTyConstMove` at
both call sites and no `PiConvInj` is consumed here either. -/
noncomputable def parRedArgsSR {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n) :
    {Γ : LCtx} → CtxWf E n Γ → {xs xs' : List (Expr Nat)} →
    ParRedArgs E n Γ xs xs' → {f f' : Expr Nat} →
    ((S : Expr Nat) → HasTy E n Γ f S → HasTy E n Γ f' S) →
    {T : Expr Nat} → HasTy E n Γ (foldApps f xs) T →
    HasTy E n Γ (foldApps f' xs') T
  | _, _, _, _, .nil _, _, _, hmove, _, h => hmove _ h
  | Γ, hΓ, _, _, .cons (x := x) (y := y) hx ht, f, f', hmove, _, h => by
      refine parRedArgsSR hpci hfaci hE hΓ ht
        (f := .app f x) (f' := .app f' y) ?_ h
      intro S hS
      have ⟨A0, B0, hf0, ha0, hcv⟩ := hasTyAppInv hS rfl
      exact .conv _ _ _ _
        (.app Γ f' y A0 B0 (hmove (.pi A0 B0) hf0)
          (parRedSR hpci hfaci hE hΓ ha0 hx))
        (.trans _ _ _ _
          (conv_instantiate0_value (B := B0)
            (.symm _ _ _ (parRed_to_conv hE hx)))
          hcv)

end

/-- Subject reduction along a parallel-reduction CHAIN, by chaining
`parRedSR`. `ParRedStar` does not move the context, so `hΓ` is threaded
unchanged. -/
noncomputable def parRedStarSR {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) {e A e' : Expr Nat}
    (h : HasTy E n Γ e A) (hs : ParRedStar E n Γ e e') :
    HasTy E n Γ e' A :=
  match e, e', hs, h with
  | _, _, .refl _ _, h => h
  | _, _, .tail hr hs, h =>
      parRedStarSR hpci hfaci hE hΓ
        (parRedSR hpci hfaci hE hΓ h hr) hs

/-! ## The type-④ artifact: `NoSortProp` is BLOCKED at its `.pi` arm

CORRECTION C-3, as recorded in `RcicConvChar.lean`'s wall record and
00 §19.3 F-05b. The route this records: a single statement

    NoSortProp E n : ∀ Γ (w : Level) (P : Expr Nat),
      CtxWf E n Γ → Conv E n Γ (.sort w) P →
      HasTy E n Γ P (.sort .zero) → False

through which the `Conv.irr` cut of all three §19.2 rows would factor
(`SortConvChar` at `w := .succ u`, `PiConvInj` at `w := .imax u v`,
`FamAppConvInj` at the family's result universe). Its `.pi` arm does
NOT close from the typing hypothesis, and the reason is three landed
lines:

1. `hasTyPiInv` hands back `Conv Γ (.sort (.imax u v)) T`, so at
   `T = .sort .zero` all the typing hypothesis yields is the level
   equation `eqN (.imax u v) .zero`;
2. `eqN_imax_zero` (`RcicParRedSortWall`) says that equation is TRUE
   at `v = .zero` — `imax _ 0` is lazy and evaluates to `0` at every
   valuation, i.e. "Π into Prop is a Prop" is LEGITIMATE, not junk;
3. the configuration is realized with NO junk environment and NO junk
   context — `noSortProp_piArm_witness` below inhabits it at EVERY
   `E`, `n` and `Γ`, so neither `EnvWf` nor `CtxWf` (§19.2 erratum 2 /
   erratum 3, the conditioning that killed the earlier unconditioned
   refutations) can cut it.

What the arm therefore rests on ENTIRELY is its remaining premise,
`Conv Γ (.sort w) (.pi A B)`: closing the arm means showing that
premise empty — "no sort converts to a Π" — a row that is NEITHER
`SortConvChar` (both endpoints sorts) NOR `PiConvInj` (both endpoints
Π), is not on the §19.2 ledger, is not landed anywhere, and is NOT
introduced here (inventing an obligation to save an arm is growing a
rule out of one's own failure). It is a characterization row of the
same ring `NoSortProp` was meant to shortcut, so the factoring buys
nothing: the three cuts fan out.

CLASSIFICATION, stated exactly (corrected 2026-09-05 after a review
finding on #3815). `NoSortProp` is NOT refuted by this artifact: no
inhabitant of `Conv Γ (.sort w) (.pi A B)` is constructed, and none is
claimed — the statement is very likely TRUE, which is exactly why it
is not cheaper than the rows it would replace. The artifact is
type-④ evidence that the `.pi` arm is NOT CLOSABLE BY INVERSION PLUS
LEVEL ARITHMETIC, i.e. that this route does not shorten the wall. The
earlier wording "REFUTED" over-claimed and is withdrawn (O-3 statement
correction; the two definitions below are unchanged in content, and
`noSortProp_piArm_falsification` is renamed `noSortProp_piArm_readout`
so its name no longer claims a falsification).

Written as LOCAL unconditioned copies per `RcicRefutations`' own
discipline (an artifact that reads its target from a definition
another patch may edit is not evidence). `NoSortProp` is deliberately
NOT defined in the tree — there is nothing to read it from. -/

/-- `Π (Q : Prop). Q : Prop`, at EVERY environment, universe bound and
context. The `.pi` arm's typing hypothesis is satisfiable with no junk
anywhere. -/
def noSortProp_piArm_witness {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ (.pi (.sort .zero) (.bvar 0)) (.sort .zero) :=
  .conv _ _ _ _
    (.pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
      (.sort Γ .zero)
      (.bvar (LocalDecl.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl))
    (.sorts _ _ _ (eqN_imax_zero (.succ .zero)))

/-- The arm's read-out: `hasTyPiInv` on the witness returns the two
domain/codomain typings AND the level conversion
`Conv Γ (.sort (.imax u v)) (.sort .zero)` — which HOLDS. Nothing in
`(hP, hT)` is contradictory at `.pi`, so the whole burden falls on the
`Conv Γ (.sort w) (.pi A B)` premise, a row that does not exist. This
is a READ-OUT, not a falsification: it exhibits no
`Conv Γ (.sort w) (.pi A B)` and refutes nothing. -/
def noSortProp_piArm_readout {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Σ' (u : Level) (v : Level),
      HasTy E n Γ (.sort .zero) (.sort u) ×'
      HasTy E n (LocalDecl.assumption (.sort .zero) :: Γ)
        (.bvar 0) (.sort v) ×'
      Conv E n Γ (.sort (.imax u v)) (.sort .zero) :=
  hasTyPiInv (noSortProp_piArm_witness Γ) rfl

end Rcic.Declarative
