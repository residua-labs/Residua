import rcic.RcicEtaKDecide
import rcic.RcicF8EvInvT
import rcic.RcicF8EvParStar
import rcic.RcicF8XStruct
import rcic.RcicF8CtxConvVar

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# A-2 ηK repair: wrapped root-ηK children and the fieldful pin, from the O-M X handle

The #6951 re-audit (cc 11:52Z / 12:07Z) refused two premises of the general
`eta × lam (iotaStarK)` entries:

1. the step-specific alignments `RootEtaKDomainConv A hf_step` /
   `RootEtaKWrapperAlign A B hf_step` (and the earlier `WrappedPiDomainConv`
   supplier), which for a `.conv`-wrapped root `iotaStarKEta` child with a
   distinct inner binder domain ask for `ConvT A_eta A` — a Π-injectivity fact
   with no supplier;
2. `LoopMkDomainInv` (constructor-domain inversion at `pinLoopEnvT`), the only
   open input of `fieldfulK_pinLoopEnvT_of_mkDomInv`.

Both are Π-injectivity requests on conversion chains that live INSIDE the
original peak inputs. Following cc's 04:15Z/05:40Z rulings (the A.2
annotation reconciliation is an O-M obligation, discharged like B5 via the
landed `XProc`/`XContract` handle, never an imported piRow), this module
discharges them from `X : ∀ R, XProc R` (and its context-conditional sibling
`X : ∀ R, XProcWf R`) applied to requests built ONLY from original
sub-derivations, and discharges the Π-spined Stratum-A region directly via
`ctxConvVar` + `separationAt_of_sortUniq` without any `X` or `SepAll` premise:

* `rootEtaKXReq_build` peels the `.conv` wrappers of the actual child step
  `hf_step` and composes their ORIGINAL `TyConvT` fields lazily
  (`EvTc.trans (EvTc.lit c_i …) …`); nothing is synthesised, no step is
  generated, no materialised composite is admitted as a literal. Its leaves are
  exactly those wrapper fields (`rootEtaKXReq_build_strict`), so the X call is
  an `OM3_edge` strictly below any caller containing `hf_step`
  (`rootEtaKXReq_edge`, `etaInput_rootEtaKXReq_edge`), and under `XContract`
  (or `XContractWf`) so are X's outputs (`rootEtaKX_outputs_edge`,
  `rootEtaKX_outputs_edge_wf`).
* The domain answer is collapsed to a typed `ConvT … (.sort u_eta)` by
  `tyConvT_sort_collapse` (Type-valued; the carried `hA_eta` of the inner
  `iotaStarKEta` node is the sort seed; sort uniqueness is a NAMED premise,
  never imported from `TypedRowsWf` — see the circularity guard in
  `RcicSortUniqueRows`). No codomain sort typing is requested:
  `RootEtaKWrapperAlign` only needs the codomain CHAIN, which is X's second
  component.
* For Π-spined wrapper chains (`piSpinedTcFixed = true`, which holds by `rfl`
  on `wrappedDistinctDomainEtaKChild`), `xTcFixed` runs Stratum A (`RcicF8XStruct`
  with `ctxConvVar` from `RcicF8CtxConvVar`) at the fixed well-formed context `Γ`
  using `sepAt_of_sortUniq`, supplying `RootEtaKDomainConv` and
  `RootEtaKWrapperAlign` (`rootEtaKDomainConv_of_piSpined`,
  `rootEtaKWrapperAlign_of_piSpined`) and the O-M output edge
  (`rootEtaKStratumA_outputs_edge`, `wrappedDistinctDomain_stratumA_edge`)
  from `EnvWfT`, `CtxWfT`, and `hSortUniq` alone — with no `X` or `SepAll`
  premise.
* `loopMkDomainInv_of_X`: `EvTy.invAppT` / `EvTy.invConstT` (B3b lazy
  inversion) on the literal `hmk` typing give a chain from `mk`'s declared
  type `Loop → Loop` to the head's Π type; X's domain component types the
  constructor field at `Loop`. Every request leaf is a strict sub-derivation
  of the original `hmk` (`loopMkRequest_leaves_strict`, `loopMkRequest_edge`,
  `loopMkX_outputs_edge`), itself a child of the `iotaStarKEta` node.

The complete entries (`eta_lamK_general_joins_of_X`,
`eta_lamK_full_joins_of_contract_X`, `eta_lamK_full_joins_of_X`,
`positive_*_of_X`, and their `_of_XWf` siblings) carry NO alignment premise:
only `EnvWfT`, the named sort-uniqueness premise, the O-M handle `X`, and the
provenance of `hf_step` in the caller bundle `R`.

What this does NOT do: it does not implement Stratum-B X, does not prove
`XContract`, and does not prove sort uniqueness. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8EtaK

open Rcic.Declarative.F8Measure

/-! ## 1. Type-valued collapse of a `TyConvT` chain at a sort -/

/-- Collapse any `TyConvT E n Γ a b` chain, given (only) a `Nonempty` sort
    typing of its left endpoint, to either syntactic equality or a typed
    `ConvT E n Γ a b (.sort u)`. Sort uniqueness is used only to produce the
    `eqN` payload of `ConvT.sorts` (a `Prop`), so the result is data. -/
def tyConvT_sort_collapse {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u : Level}
    {a b : Expr Nat} :
    TyConvT E n Γ a b →
    (Nonempty (HasTyT E n Γ a (.sort u)) → PSum (a = b) (ConvT E n Γ a b (.sort u)))
  | .refl _ _, _ => .inl rfl
  | .of _ _ _ v h, hA =>
      have heq : eqN v u := by
        obtain ⟨hA⟩ := hA
        obtain ⟨hav⟩ := (convT_endpoints hW hΓ h).1
        exact hSortUniq hΓ hav hA
      .inr (.tyConv _ _ _ (.sort v) (.sort u) (.succ v) h (.sorts _ v u heq))
  | .trans _ _ _ _ c1 c2, hA =>
      match tyConvT_sort_collapse hW hSortUniq hΓ c1 hA with
      | .inl e =>
          match tyConvT_sort_collapse hW hSortUniq hΓ c2 (e ▸ hA) with
          | .inl e2 => .inl (e.trans e2)
          | .inr k2 => .inr (e.symm ▸ k2)
      | .inr k1 =>
          match tyConvT_sort_collapse hW hSortUniq hΓ c2 (convT_endpoints hW hΓ k1).2 with
          | .inl e => .inr (e ▸ k1)
          | .inr k2 => .inr (.trans _ _ _ _ _ k1 k2)

/-! ## 2. The original-wrapper X request of a (possibly wrapped) root ηK child -/

/-- A child of a judgment certified into `R` is strictly below some `r ∈ R`. -/
theorem rootEtaK_childCert {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {x y : Jd E n} (hs : ∃ r ∈ R, SubEq y r) (hc : Child x y) :
    ∃ r ∈ R, SubOf x r :=
  let ⟨r, hr, hy⟩ := hs
  ⟨r, hr, subOf_trans_subEq (.child hc) hy⟩

/-- Request shape: at a (possibly `.conv`-wrapped) root `iotaStarKEta` node with
    inner Π type `.pi A_eta B_eta`, a provenance chain over `R` to the outer
    `.pi A B`; `PUnit` elsewhere (no X call is made for structural steps). -/
def RootEtaKXReq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (R : List (Jd E n))
    (A B : Expr Nat) {a b T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → Type
  | .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      EvTc R Γ (.pi A_eta B_eta) (.pi A B)
  | .conv _ _ _ _ _ hinner _ => RootEtaKXReq R A B hinner
  | _ => PUnit

/-- Build the request by peeling the ACTUAL `.conv` wrappers of `h`: each
    wrapper field `hc` enters as `EvTc.lit hc` (certified as a child of its own
    original `.conv` node) and is composed lazily with `EvTc.trans`. Starting
    accumulator: a chain from `h`'s index to `.pi A B` (for the η child itself,
    `EvTc.refl`). -/
def rootEtaKXReq_build {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (∃ r ∈ R, SubEq (.pr h) r) → EvTc R Γ T (.pi A B) → RootEtaKXReq R A B h
  | _, _, _, .iotaStarKEta .., _, acc => acc
  | _, _, _, .conv _ _ _ _ _ hinner hc, hs, acc =>
      rootEtaKXReq_build R A B hinner
        (let ⟨r, hr, hsub⟩ := rootEtaK_childCert hs (.head _); ⟨r, hr, .inr hsub⟩)
        (.trans
          (.lit hc (let ⟨r, hr, hsub⟩ := rootEtaK_childCert hs (.tail _ (.head _))
            ⟨r, hr, .inr hsub⟩))
          acc)
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => PUnit.unit

/-- The literal leaves of the request (empty for structural steps). -/
def RootEtaKXReq.leavesOf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {R : List (Jd E n)} {A B : Expr Nat} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → List (Jd E n)
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta .., req =>
      EvTc.leaves (req : EvTc R Γ (.pi A_eta B_eta) (.pi A B))
  | _, _, _, .conv _ _ _ _ _ hinner _, req => RootEtaKXReq.leavesOf hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => []

/-- Strictness: if the accumulator's leaves are strictly below `R`, so are all
    leaves of the built request (each added leaf is a wrapper field, a child of
    a `.conv` node that is `SubEq` some `r ∈ R`). -/
theorem rootEtaKXReq_build_strict {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (hs : ∃ r ∈ R, SubEq (.pr h) r) → (acc : EvTc R Γ T (.pi A B)) →
    (∀ ℓ ∈ acc.leaves, ∃ r ∈ R, SubOf ℓ r) →
    ∀ ℓ ∈ RootEtaKXReq.leavesOf h (rootEtaKXReq_build R A B h hs acc),
      ∃ r ∈ R, SubOf ℓ r
  | _, _, _, .iotaStarKEta .., _, _, hacc => hacc
  | _, _, _, .conv _ _ _ _ _ hinner hc, hs, acc, hacc =>
      rootEtaKXReq_build_strict R A B hinner _ _ (by
        intro ℓ hℓ
        simp only [EvTc.leaves, List.mem_append, List.mem_singleton] at hℓ
        rcases hℓ with rfl | hℓ
        · exact rootEtaK_childCert hs (.tail _ (.head _))
        · exact hacc ℓ hℓ)
  | _, _, _, .refl .., _, _, _ | _, _, _, .sortEq .., _, _, _
  | _, _, _, .consts .., _, _, _ | _, _, _, .bvarZeta .., _, _, _
  | _, _, _, .delta .., _, _, _ | _, _, _, .app .., _, _, _
  | _, _, _, .beta .., _, _, _ | _, _, _, .lam .., _, _, _
  | _, _, _, .pi .., _, _, _ | _, _, _, .letE .., _, _, _
  | _, _, _, .zeta .., _, _, _ | _, _, _, .iotaSpine .., _, _, _
  | _, _, _, .lit .., _, _, _ | _, _, _, .eta .., _, _, _
  | _, _, _, .iotaStarK .., _, _, _ | _, _, _, .peq .., _, _, _ =>
      fun _ hℓ => nomatch hℓ

/-- The request for the η child `hf_step` itself (index `.pi A B`, starting
    accumulator `EvTc.refl`). -/
def rootEtaKXReqOf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (R : List (Jd E n)) {a b A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r) : RootEtaKXReq R A B hf_step :=
  rootEtaKXReq_build R A B hf_step hs (.refl Γ (.pi A B))

theorem rootEtaKXReqOf_strict {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (R : List (Jd E n)) {a b A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r) :
    ∀ ℓ ∈ RootEtaKXReq.leavesOf hf_step (rootEtaKXReqOf R hf_step hs),
      ∃ r ∈ R, SubOf ℓ r :=
  rootEtaKXReq_build_strict R A B hf_step hs _ (fun _ hℓ => nomatch hℓ)

/-- O-M edge of the wrapped-root X request: replacing the caller bundle `R` by
    the request's literal leaves is an `OM3_edge` (kept frame `Z`). -/
theorem rootEtaKXReq_edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (R : List (Jd E n)) (hR : R ≠ []) {a b A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r) (Z : List (Jd E n)) :
    OM3_edge (R ++ Z)
      (RootEtaKXReq.leavesOf hf_step (rootEtaKXReqOf R hf_step hs) ++ Z) :=
  om3_edge_of_strictLeaves hR (rootEtaKXReqOf_strict R hf_step hs)

/-- Certificate for the η child inside the ORIGINAL `ParRedT.eta` input. -/
theorem etaInput_cert {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' A B : Expr Nat} {R : List (Jd E n)}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (hmem : .pr (.eta Γ f f' A B hf_step hl) ∈ R) :
    ∃ r ∈ R, SubEq (.pr hf_step) r :=
  ⟨_, hmem, .inr (.child (eta_child_hf_step hf_step hl))⟩

/-- The X request of the η child is an `OM3_edge` strictly below any caller
    bundle `R` that contains the original `ParRedT.eta` input (e.g. the two
    complete D-fork inputs of the `eta × lam (iotaStarK)` peak). -/
theorem etaInput_rootEtaKXReq_edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' A B : Expr Nat} (R : List (Jd E n))
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (hmem : .pr (.eta Γ f f' A B hf_step hl) ∈ R) (Z : List (Jd E n)) :
    OM3_edge (R ++ Z)
      (RootEtaKXReq.leavesOf hf_step
        (rootEtaKXReqOf R hf_step (etaInput_cert hf_step hl hmem)) ++ Z) :=
  rootEtaKXReq_edge R (List.ne_nil_of_mem hmem) hf_step _ Z

/-- Leaves of X's two answer components on the request (empty when no X call
    is made). -/
def RootEtaKXReq.ansLeaves {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {R : List (Jd E n)} {A B : Expr Nat} (X : ∀ R : List (Jd E n), XProc R) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → List (Jd E n)
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta .., req =>
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      (X R q).1.leaves ++ (X R q).2.leaves
  | _, _, _, .conv _ _ _ _ _ hinner _, req => RootEtaKXReq.ansLeaves X hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => []

theorem rootEtaKX_outputs_strict {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {R : List (Jd E n)} {A B : Expr Nat}
    (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    (∀ ℓ ∈ RootEtaKXReq.leavesOf h req, ∃ r ∈ R, SubOf ℓ r) →
    ∀ ℓ ∈ RootEtaKXReq.ansLeaves X h req, ∃ r ∈ R, SubOf ℓ r
  | _, _, _, .iotaStarKEta .., req, hreq => fun ℓ hℓ =>
      let ⟨ℓ', hm, hs⟩ := hX R req ℓ hℓ
      let ⟨r, hr, ht⟩ := hreq ℓ' hm
      ⟨r, hr, subEq_trans_subOf hs ht⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hreq =>
      rootEtaKX_outputs_strict X hX hinner req hreq
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => fun _ hℓ => nomatch hℓ

/-- Under `XContract`, X's outputs on the η child's request stay strictly
    below the caller bundle: an `OM3_edge`. -/
theorem rootEtaKX_outputs_edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    (R : List (Jd E n)) (hR : R ≠ []) {a b A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r) (Z : List (Jd E n)) :
    OM3_edge (R ++ Z)
      (RootEtaKXReq.ansLeaves X hf_step (rootEtaKXReqOf R hf_step hs) ++ Z) :=
  om3_edge_of_strictLeaves hR
    (rootEtaKX_outputs_strict X hX hf_step _ (rootEtaKXReqOf_strict R hf_step hs))

/-! ## 3. Alignments supplied by X (no alignment premise remains) -/

/-- `RootEtaKDomainConv A h` from X's domain component on the original-wrapper
    request, collapsed at the inner node's own carried `hA_eta`. -/
noncomputable def rootEtaKDomainConv_of_X {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → RootEtaKDomainConv A h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ u_eta _ _ _ hA_eta _ _ _ _ _ _ _ _ _ _ _,
      req => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      dsimp only [RootEtaKDomainConv]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]; exact PUnit.unit
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ ((X R q).1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨hΓ, k⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req =>
      rootEtaKDomainConv_of_X hW hSortUniq X hΓ R A B hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => PUnit.unit

/-- `RootEtaKWrapperAlign A B h` from X on the original-wrapper request: the
    domain component collapsed at the carried `hA_eta`, the codomain component
    used as a chain (no codomain sort typing is requested or produced). -/
noncomputable def rootEtaKWrapperAlign_of_X {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → RootEtaKWrapperAlign A B h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ u_eta _ _ _ hA_eta _ _ _ _ _ _ _ _ _ _ _,
      req => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      dsimp only [RootEtaKWrapperAlign]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]
        by_cases hB_eq : B_eta = B
        · rw [if_pos hB_eq]; exact PUnit.unit
        · rw [if_neg hB_eq]; exact (X R q).2.val hcl hinst
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ ((X R q).1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨k, (X R q).2.val hcl hinst⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req =>
      rootEtaKWrapperAlign_of_X hW hSortUniq X hΓ R A B hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => PUnit.unit

/-! ## 4. Complete entries: no `NoEtaKStep`, no `NoWrappedRootEtaK`, no alignment premise -/

/-- General `eta × lam (iotaStarK)` join for ANY η child `hf_step` (structural,
    bare root ηK, or `.conv`-wrapped root ηK with same OR distinct inner
    domain), field-free singleton (`MinorStepLift`). The domain alignment is
    computed from X on the original wrapper chain of `hf_step`. -/
theorem eta_lamK_general_joins_of_X
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hd : DerivedIota E (iotaLhsOf w) rhs)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hnmin : w.nMinors = 1) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_general_joins hW hΓ w happ hcA hA hB hrl hsel hfam hmajor hmk hTm0
    hd hf_nil hc hf_step hNoPrf hMinorLift hnmin
    (rootEtaKDomainConv_of_X hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-- General `eta × lam (iotaStarK)` join over the full `DerivedIotaU` union,
    consuming the per-peak `FieldfulKPeakContract`, for ANY η child; the
    wrapper alignment is computed from X on the original wrapper chain. -/
theorem eta_lamK_full_joins_of_contract_X
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_full_joins_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc hf_step hNoPrf hContract
    (rootEtaKWrapperAlign_of_X hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-- Field-free specialization of `eta_lamK_full_joins_of_contract_X`. -/
theorem eta_lamK_full_joins_of_X
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_full_joins hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hnmin hf_nil hc hf_step hNoPrf hMinorLift
    (rootEtaKWrapperAlign_of_X hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-! ## 5. Positive A-2 peak: every η child, sort uniqueness + X only -/

/-- At the positive A-2 peak, ANY η child `hf_step` of `partialRec one`
    (structural, bare root ηK, `.conv`-wrapped root ηK with same or distinct
    inner domain) joins `.lam A' (.bvar 1)`; the request bundle is the child
    itself (`R = [.pr hf_step]`). -/
theorem positive_full_eta_lamK_joins_of_X
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProc R)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq hcA hc hf_step
    (rootEtaKWrapperAlign_of_X envWf hSortUniq X (contextWf one positive_levels)
      [.pr hf_step] domain codomain hf_step
      (rootEtaKXReqOf [.pr hf_step] hf_step ⟨_, .head _, .inl rfl⟩))

/-- Stepped (field-free) positive entry for ANY η child, sort uniqueness + X. -/
theorem positive_stepped_eta_lamK_joins_of_X
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProc R)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  positive_stepped_eta_lamK_joins_of_sortUniq hSortUniq hcA hc hf_step
    (rootEtaKDomainConv_of_X envWf hSortUniq X (contextWf one positive_levels)
      [.pr hf_step] domain codomain hf_step
      (rootEtaKXReqOf [.pr hf_step] hf_step ⟨_, .head _, .inl rfl⟩))

/-- Pin: the distinct-domain WRAPPED root ηK child (`domainBeta ≠ domain`,
    which fails both `NoWrappedRootEtaK` and `SameRootEtaKDomain`) is consumed
    by the X-supplied complete entry. -/
theorem positive_wrappedDistinctDomainEtaKChild_joins_of_X
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProc R) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam domainBeta (.bvar 1)) z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_X hSortUniq X
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedDistinctDomainEtaKChild

/-- Pin: the same-domain wrapped child (reflexive index wrapper, the
    ChatGPT-line control) through the X-supplied stepped entry. -/
theorem positive_wrappedNonreflexiveEtaKChild_joins_of_X
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProc R) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_stepped_eta_lamK_joins_of_X hSortUniq X
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedNonreflexiveEtaKChild

/-- Pin: the X request of the distinct-domain wrapped child has exactly ONE
    leaf, the ORIGINAL wrapper field of `wrappedDistinctDomainEtaKChild`
    (nothing synthesised). -/
theorem wrappedDistinctDomain_request_leaves :
    RootEtaKXReq.leavesOf wrappedDistinctDomainEtaKChild
        (rootEtaKXReqOf [.pr wrappedDistinctDomainEtaKChild]
          wrappedDistinctDomainEtaKChild ⟨_, .head _, .inl rfl⟩) =
      [.tc (.of positiveContext (.pi domainBeta codomain) commonIndex (.imax .zero one)
        piDomainBeta_conv_commonIndex)] := rfl

/-! ## 6. `pinLoopEnvT`: constructor-domain inversion and `FIELDFUL_K` from X -/

theorem evTc_cast_left_leaves {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {T₁ T₂ U : Expr Nat} (h : T₁ = T₂) (c : EvTc R Γ T₁ U) :
    (h ▸ c : EvTc R Γ T₂ U).leaves = c.leaves := by
  subst h; rfl

/-- `mk`'s declared type at any level list. -/
theorem pinLoopMk_instType (lsC : List Level) {m : CheckedMember}
    (hres : pinLoopEnvT.members 61 = some m) :
    instantiateLevels lsC m.mtype = .pi (.const 60 []) (.const 60 []) := by
  have hm : m = pinLoopMkT := Option.some.inj (hres.symm.trans rfl)
  subst hm
  rfl

/-- Lazy inversion of an ORIGINAL constructor-major typing
    `hmk : mk t : Tm` over the bundle `[.ty hmk]`: a chain from `mk`'s declared
    type `Loop → Loop` to the head's Π type, and the argument's provenance
    typing at that Π's domain. -/
def loopMkInv {n : Nat} {Δ : LCtx} {lsC : List Level} {t Tm : Expr Nat}
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm) :
    Σ' (A B : Expr Nat),
      EvTc [.ty hmk] Δ (.pi (.const 60 []) (.const 60 [])) (.pi A B) ×'
      EvTy [.ty hmk] Δ t A :=
  let hcl := envClosed_of_envWfT pinLoopGroupRecWfT
  let hinst := envMembersSubstStable_of_envWfT pinLoopGroupRecWfT
  let D : EvTy [.ty hmk] Δ (.app (.const 61 lsC) t) Tm :=
    .lit hmk ⟨_, .head _, .inl rfl⟩
  let inv := D.invAppT rfl
  let invC := inv.hf.invConstT hcl hinst rfl
  ⟨inv.A, inv.B, pinLoopMk_instType lsC invC.hres ▸ invC.hc, inv.ha⟩

/-- Every leaf of the X request `(loopMkInv hmk).2.2.1` is a STRICT
    sub-derivation (`SubOf`) of the original `hmk`. -/
theorem loopMkRequest_leaves_strict {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm) :
    ∀ ℓ ∈ (loopMkInv hmk).2.2.1.leaves, SubOf ℓ (.ty hmk) := by
  intro ℓ hℓ
  let hcl := envClosed_of_envWfT pinLoopGroupRecWfT
  let hinst := envMembersSubstStable_of_envWfT pinLoopGroupRecWfT
  let hsub : ∃ r ∈ ([.ty hmk] : List (Jd pinLoopEnvT n)), SubEq (.ty hmk) r :=
    ⟨_, .head _, .inl rfl⟩
  let D : EvTy [.ty hmk] Δ (.app (.const 61 lsC) t) Tm := .lit hmk hsub
  let inv := D.invAppT rfl
  let invC := inv.hf.invConstT hcl hinst rfl
  have hℓ' : ℓ ∈ invC.hc.leaves := by
    have := evTc_cast_left_leaves (pinLoopMk_instType lsC invC.hres) invC.hc
    simp only [loopMkInv] at hℓ
    rw [this] at hℓ
    exact hℓ
  obtain ⟨ℓ₁, hm₁, hs₁⟩ := EvTy.invConstT_leaves hcl hinst inv.hf rfl ℓ hℓ'
  have hm₁' : ℓ₁ ∈ inv.leaves := by
    simp only [EvInvApp.leaves, List.mem_append]
    exact Or.inl (Or.inl hm₁)
  have hagree : inv = D.invApp rfl rfl :=
    EvTy.invAppT_agree D rfl rfl
  have hm₁_lit : ℓ₁ ∈ (D.invApp rfl rfl).leaves := hagree ▸ hm₁'
  have hstr₁ : SubOf ℓ₁ (.ty hmk) :=
    EvTy.invApp_strict hmk hsub rfl ℓ₁ hm₁_lit
  exact subEq_trans_subOf hs₁ hstr₁

/-- Every leaf of the X request is a sub-derivation of the original `hmk`. -/
theorem loopMkRequest_leaves_subEq {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm) :
    ∀ ℓ ∈ (loopMkInv hmk).2.2.1.leaves, SubEq ℓ (.ty hmk) :=
  fun ℓ hℓ => .inr (loopMkRequest_leaves_strict hmk ℓ hℓ)

/-- O-M call edge for the constructor-domain X request: replacing `[.ty hmk]`
    by `(loopMkInv hmk).2.2.1.leaves` is an `OM3_edge`. -/
theorem loopMkRequest_edge {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm)
    (Z : List (Jd pinLoopEnvT n)) :
    OM3_edge ([.ty hmk] ++ Z) ((loopMkInv hmk).2.2.1.leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ =>
    ⟨.ty hmk, .head _, loopMkRequest_leaves_strict hmk ℓ hℓ⟩)

/-- Under `XContract (X n)`, X's outputs on `(loopMkInv hmk).2.2.1` remain
    strictly `OM3_edge`-below `[.ty hmk] ++ Z`. -/
theorem loopMkX_outputs_edge {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (X : ∀ (n : Nat) (R : List (Jd pinLoopEnvT n)), XProc R)
    (hX : XContract (X n))
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm)
    (Z : List (Jd pinLoopEnvT n)) :
    let q := (loopMkInv hmk).2.2.1
    let ans := X n [.ty hmk] q
    OM3_edge ([.ty hmk] ++ Z) ((ans.1.leaves ++ ans.2.leaves) ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ => by
    obtain ⟨ℓ', hm, hs⟩ := hX [.ty hmk] (loopMkInv hmk).2.2.1 ℓ hℓ
    exact ⟨.ty hmk, .head _,
      subEq_trans_subOf hs (loopMkRequest_leaves_strict hmk ℓ' hm)⟩)

/-- `LoopMkDomainInv` discharged from the O-M handle X on the original `hmk`
    typing: X's domain component relates `Loop` to the head's Π domain, along
    which the argument typing is retyped. -/
def loopMkDomainInv_of_X
    (X : ∀ (n : Nat) (R : List (Jd pinLoopEnvT n)), XProc R) :
    LoopMkDomainInv :=
  fun {n _ _ _ _} hmk =>
    let hcl := envClosed_of_envWfT pinLoopGroupRecWfT
    let hinst := envMembersSubstStable_of_envWfT pinLoopGroupRecWfT
    let ⟨_, _, req, ha⟩ := loopMkInv hmk
    hasTyT_of_tyConvT (ha.val hcl hinst) ((X n [.ty hmk] req).1.val hcl hinst).symmT

/-- `FIELDFUL_K pinLoopEnvT` from the O-M handle X (no `LoopMkDomainInv`
    premise remains). -/
def fieldfulK_pinLoopEnvT_of_X
    (X : ∀ (n : Nat) (R : List (Jd pinLoopEnvT n)), XProc R) :
    FIELDFUL_K pinLoopEnvT :=
  fieldfulK_pinLoopEnvT_of_mkDomInv (loopMkDomainInv_of_X X)

/-! ## 7. Context-conditional `XProcWf` / `XContractWf` entries (Stratum-B sibling) -/

/-- Leaves of `XProcWf`'s two answer components on the η child's request in a
    well-formed context `hΓ : CtxWfT E n Γ`. -/
def RootEtaKXReq.ansLeavesWf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {R : List (Jd E n)} {A B : Expr Nat}
    (X : ∀ R : List (Jd E n), XProcWf R) (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → List (Jd E n)
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta .., req =>
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      (X R hΓ q).1.leaves ++ (X R hΓ q).2.leaves
  | _, _, _, .conv _ _ _ _ _ hinner _, req => RootEtaKXReq.ansLeavesWf X hΓ hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => []

theorem rootEtaKX_outputs_strict_wf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {R : List (Jd E n)} {A B : Expr Nat}
    (X : ∀ R : List (Jd E n), XProcWf R) (hX : XContractWf X)
    (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    (∀ ℓ ∈ RootEtaKXReq.leavesOf h req, ∃ r ∈ R, SubOf ℓ r) →
    ∀ ℓ ∈ RootEtaKXReq.ansLeavesWf X hΓ h req, ∃ r ∈ R, SubOf ℓ r
  | _, _, _, .iotaStarKEta .., req, hreq => fun ℓ hℓ =>
      let ⟨ℓ', hm, hs⟩ := hX R hΓ req ℓ hℓ
      let ⟨r, hr, ht⟩ := hreq ℓ' hm
      ⟨r, hr, subEq_trans_subOf hs ht⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hreq =>
      rootEtaKX_outputs_strict_wf X hX hΓ hinner req hreq
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => fun _ hℓ => nomatch hℓ

/-- Under `XContractWf`, `XProcWf`'s outputs on the η child's request form an
    `OM3_edge` strictly below the caller bundle `R ++ Z`. -/
theorem rootEtaKX_outputs_edge_wf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (X : ∀ R : List (Jd E n), XProcWf R) (hX : XContractWf X)
    (hΓ : CtxWfT E n Γ)
    (R : List (Jd E n)) (hR : R ≠ []) {a b A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r) (Z : List (Jd E n)) :
    OM3_edge (R ++ Z)
      (RootEtaKXReq.ansLeavesWf X hΓ hf_step (rootEtaKXReqOf R hf_step hs) ++ Z) :=
  om3_edge_of_strictLeaves hR
    (rootEtaKX_outputs_strict_wf X hX hΓ hf_step _ (rootEtaKXReqOf_strict R hf_step hs))

/-- `RootEtaKDomainConv A h` from the context-conditional `XProcWf` handle. -/
noncomputable def rootEtaKDomainConv_of_XWf {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProcWf R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → RootEtaKDomainConv A h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ u_eta _ _ _ hA_eta _ _ _ _ _ _ _ _ _ _ _,
      req => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      dsimp only [RootEtaKDomainConv]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]; exact PUnit.unit
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ ((X R hΓ q).1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨hΓ, k⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req =>
      rootEtaKDomainConv_of_XWf hW hSortUniq X hΓ R A B hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => PUnit.unit

/-- `RootEtaKWrapperAlign A B h` from the context-conditional `XProcWf` handle. -/
noncomputable def rootEtaKWrapperAlign_of_XWf {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProcWf R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → RootEtaKWrapperAlign A B h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ u_eta _ _ _ hA_eta _ _ _ _ _ _ _ _ _ _ _,
      req => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      dsimp only [RootEtaKWrapperAlign]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]
        by_cases hB_eq : B_eta = B
        · rw [if_pos hB_eq]; exact PUnit.unit
        · rw [if_neg hB_eq]; exact (X R hΓ q).2.val hcl hinst
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ ((X R hΓ q).1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨k, (X R hΓ q).2.val hcl hinst⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req =>
      rootEtaKWrapperAlign_of_XWf hW hSortUniq X hΓ R A B hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => PUnit.unit

/-- General `eta × lam (iotaStarK)` join consuming `XProcWf`. -/
theorem eta_lamK_general_joins_of_XWf
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProcWf R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hd : DerivedIota E (iotaLhsOf w) rhs)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hnmin : w.nMinors = 1) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_general_joins hW hΓ w happ hcA hA hB hrl hsel hfam hmajor hmk hTm0
    hd hf_nil hc hf_step hNoPrf hMinorLift hnmin
    (rootEtaKDomainConv_of_XWf hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-- General `eta × lam (iotaStarK)` join over `DerivedIotaU` consuming
    `FieldfulKPeakContract` and `XProcWf`. -/
theorem eta_lamK_full_joins_of_contract_XWf
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProcWf R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_full_joins_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc hf_step hNoPrf hContract
    (rootEtaKWrapperAlign_of_XWf hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-- Field-free specialization of `eta_lamK_full_joins_of_contract_XWf`. -/
theorem eta_lamK_full_joins_of_XWf
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProcWf R) (R : List (Jd E n))
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  eta_lamK_full_joins hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hnmin hf_nil hc hf_step hNoPrf hMinorLift
    (rootEtaKWrapperAlign_of_XWf hW hSortUniq X hΓ R A B hf_step
      (rootEtaKXReqOf R hf_step hs))

/-- Positive A-2 peak join for ANY η child consuming `XProcWf`. -/
theorem positive_full_eta_lamK_joins_of_XWf
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProcWf R)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq hcA hc hf_step
    (rootEtaKWrapperAlign_of_XWf envWf hSortUniq X (contextWf one positive_levels)
      [.pr hf_step] domain codomain hf_step
      (rootEtaKXReqOf [.pr hf_step] hf_step ⟨_, .head _, .inl rfl⟩))

/-- Positive stepped entry for ANY η child consuming `XProcWf`. -/
theorem positive_stepped_eta_lamK_joins_of_XWf
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProcWf R)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  positive_stepped_eta_lamK_joins_of_sortUniq hSortUniq hcA hc hf_step
    (rootEtaKDomainConv_of_XWf envWf hSortUniq X (contextWf one positive_levels)
      [.pr hf_step] domain codomain hf_step
      (rootEtaKXReqOf [.pr hf_step] hf_step ⟨_, .head _, .inl rfl⟩))

/-- Pin: `wrappedDistinctDomainEtaKChild` consumed by `positive_full_eta_lamK_joins_of_XWf`. -/
theorem positive_wrappedDistinctDomainEtaKChild_joins_of_XWf
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (X : ∀ R : List (Jd eqEnvT 2), XProcWf R) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam domainBeta (.bvar 1)) z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_XWf hSortUniq X
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedDistinctDomainEtaKChild

/-! ## 8. Stratum-A (`xConvAt` / `xTAt` / `ctxConvVar`) discharge without `X` or `SepAll` -/

/-- Prop/Sort separation at a single context `Γ` (discharged under `CtxWfT E n Γ`
    from sort uniqueness by `sepAt_of_sortUniq`, without the Γ-unconditional
    `SepAll E n`). -/
def SepAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Prop :=
  ∀ {P : Expr Nat} {l : Level},
    HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False

theorem sepAt_of_sortUniq {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) : SepAt E n Γ :=
  fun hP hc => separationAt_of_sortUniq hW hSortUniq hΓ hP hc

/-- Stratum A on a plain conversion `h : ConvT E n Γ a b T` between two Π's at
    a fixed context `Γ` (using `ctxConvVar` from `RcicF8CtxConvVar` and
    `SepAt E n Γ`), with strict leaf bound `SubOf ℓ (.cv h)`. -/
def xConvAt {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}
    (hsep : SepAt E n Γ) :
    {a b T : Expr Nat} → (h : ConvT E n Γ a b T) →
    (∃ r ∈ R, SubEq (.cv h) r) → piSpinedConv h = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.cv h)
  | _, _, _, .refl _ a _ _, _, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .symm _ a b A h, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedConv] using hp
      obtain ⟨r, hr⟩ := xConvAt hsep h (certOfChild (cvChildSymm h) hsub) hp' hb ha
      refine ⟨(.symm r.1, ctxConvVar (.symm r.1) (.symm r.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      have hin : ℓ ∈ r.1.leaves ++ r.2.leaves := by
        rcases hℓ with hℓ | hℓ
        · exact List.mem_append.mpr (.inl hℓ)
        · have := ctxConvVar_contract (.symm r.1) (.symm r.2) ℓ hℓ
          simpa only [EvTc.leaves] using this
      exact .trans (hr ℓ hin) (.child (cvChildSymm h))
  | _, _, _, .trans _ a m c A h1 h2, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedConv, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xConvAt hsep h1 (certOfChild (cvChildTransFst h1 h2) hsub) hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xConvAt hsep h2 (certOfChild (cvChildTransSnd h1 h2) hsub) hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (ctxConvVar r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (cvChildTransFst h1 h2))
      · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (cvChildTransSnd h1 h2))
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inr hℓ))) (.child (cvChildTransFst h1 h2))
      · have hk := ctxConvVar_contract r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hk))) (.child (cvChildTransFst h1 h2))
        · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inr hk))) (.child (cvChildTransSnd h1 h2))
  | _, _, _, .pi _ A A' B B' u v hA hB, hsub, _, A₁, B₁, A₂, B₂, ha, hb => by
      injection ha with h1 h2
      injection hb with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.ofCv u (.lit hA (certOfChild (cvChildPiFst hA hB) hsub)),
        .ofCv v (.lit hB (certOfChild (cvChildPiSnd hA hB) hsub))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvCv.leaves, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl
      · exact .child (cvChildPiFst hA hB)
      · exact .child (cvChildPiSnd hA hB)
  | _, _, _, .irr _ P p q hP hp _, _, _, A₁, B₁, A₂, B₂, ha, _ => by
      subst ha
      obtain ⟨_, _, _, _, hc⟩ := hasTyTInv_pi hp rfl
      exact (hsep hP hc).elim
  | _, _, _, .tyConv _ a b A A' u h hA, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedConv] using hp
      obtain ⟨r, hr⟩ := xConvAt hsep h (certOfChild (cvChildTyConv h hA) hsub) hp' ha hb
      exact ⟨r, fun ℓ hℓ => .trans (hr ℓ hℓ) (.child (cvChildTyConv h hA))⟩
  | _, _, _, .beta .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .zeta .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .zetaLocal .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .delta .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .iota .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .lit .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .app .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .lam .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .letE .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .sorts .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .consts .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, .eta .., _, hp, _, _, _, _, _, _ => nomatch hp

/-- Stratum A on a plain type-conversion chain `d : TyConvT E n Γ A B` between
    two Π's at a fixed context `Γ`, with strict leaf bound `SubOf ℓ (.tc d)`. -/
def xTAt {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}
    (hsep : SepAt E n Γ) :
    {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    (∃ r ∈ R, SubEq (.tc d) r) → piSpinedT d = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.tc d)
  | _, _, .refl _ A, _, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, .of _ A B u h, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedT] using hp
      obtain ⟨r, hr⟩ := xConvAt hsep h (certOfChild (tcChildOf h) hsub) hp' ha hb
      exact ⟨r, fun ℓ hℓ => .trans (hr ℓ hℓ) (.child (tcChildOf h))⟩
  | _, _, .trans _ A M B d₁ d₂, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedT, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xTAt hsep d₁ (certOfChild (tcChildFst d₁ d₂) hsub) hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xTAt hsep d₂ (certOfChild (tcChildSnd d₁ d₂) hsub) hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (ctxConvVar r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (tcChildFst d₁ d₂))
      · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (tcChildSnd d₁ d₂))
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inr hℓ))) (.child (tcChildFst d₁ d₂))
      · have hk := ctxConvVar_contract r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hk))) (.child (tcChildFst d₁ d₂))
        · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inr hk))) (.child (tcChildSnd d₁ d₂))

/-- Predicate on `EvTc R Γ A B` recognizing fixed-context Π-spined provenance
    chains (`.lit`, `.refl`, `.symm`, `.trans` with Π middles — the exact
    fragment produced by `rootEtaKXReq_build`). -/
def piSpinedTcFixed {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx} :
    {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, .lit d _ => piSpinedT d
  | _, _, .refl _ _ => true
  | _, _, .symm c => piSpinedTcFixed c
  | _, _, @EvTc.trans _ _ _ _ _ M _ c₁ c₂ =>
      isPi M && piSpinedTcFixed c₁ && piSpinedTcFixed c₂
  | _, _, .ofCv _ _ | _, _, .piCod _ _ _ | _, _, .subst0 ..
  | _, _, .substLet .. | _, _, .wk .. => false

/-- Stratum A on a fixed-context Π-spined `EvTc R Γ A B` (using `SepAt E n Γ`
    and `ctxConvVar`, with no `X` or `SepAll` premise): every output leaf is
    strictly `SubOf` some literal leaf of `c`. -/
def xTcFixed {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}
    (hsep : SepAt E n Γ) :
    {A B : Expr Nat} → (c : EvTc R Γ A B) → piSpinedTcFixed c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ d ∈ c.leaves, SubOf ℓ d
  | _, _, .lit d hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedT d = true := by simpa only [piSpinedTcFixed] using hp
      obtain ⟨r, hr⟩ := xTAt hsep d hsub hp' ha hb
      exact ⟨r, fun ℓ hℓ => ⟨.tc d, .head _, hr ℓ hℓ⟩⟩
  | _, _, .refl _ A, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, .symm c, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedTcFixed c = true := by simpa only [piSpinedTcFixed] using hp
      obtain ⟨r, hr⟩ := xTcFixed hsep c hp' hb ha
      refine ⟨(.symm r.1, ctxConvVar (.symm r.1) (.symm r.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      have hin : ℓ ∈ r.1.leaves ++ r.2.leaves := by
        rcases hℓ with hℓ | hℓ
        · exact List.mem_append.mpr (.inl hℓ)
        · have := ctxConvVar_contract (.symm r.1) (.symm r.2) ℓ hℓ
          simpa only [EvTc.leaves] using this
      obtain ⟨d, hd, hsd⟩ := hr ℓ hin
      exact ⟨d, by simpa only [EvTc.leaves] using hd, hsd⟩
  | _, _, @EvTc.trans _ _ _ _ A M B c₁ c₂, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedTcFixed, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xTcFixed hsep c₁ hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xTcFixed hsep c₂ hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (ctxConvVar r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨d, hd, hsd⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨d, List.mem_append.mpr (.inl hd), hsd⟩
      · obtain ⟨d, hd, hsd⟩ := hr₂ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨d, List.mem_append.mpr (.inr hd), hsd⟩
      · obtain ⟨d, hd, hsd⟩ := hr₁ ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨d, List.mem_append.mpr (.inl hd), hsd⟩
      · have hk := ctxConvVar_contract r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨d, hd, hsd⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hk))
          exact ⟨d, List.mem_append.mpr (.inl hd), hsd⟩
        · obtain ⟨d, hd, hsd⟩ := hr₂ ℓ (List.mem_append.mpr (.inr hk))
          exact ⟨d, List.mem_append.mpr (.inr hd), hsd⟩
  | _, _, .ofCv _ _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, .piCod _ _ _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, .subst0 .., hp, _, _, _, _, _, _ => nomatch hp
  | _, _, .substLet .., hp, _, _, _, _, _, _ => nomatch hp
  | _, _, .wk .., hp, _, _, _, _, _, _ => nomatch hp

/-- Whether the `RootEtaKXReq` of a step `h` lies in the fixed-context Π-spined
    Stratum-A fragment (`true` for all structural steps and for any root
    `iotaStarKEta` step whose `.conv` wrapper chain is Π-spined). -/
def RootEtaKXReq.isPiSpinedFixed {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} {Γ : LCtx} {A B : Expr Nat} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKXReq R A B h → Bool
  | _, _, _, .iotaStarKEta .., req => piSpinedTcFixed req
  | _, _, _, .conv _ _ _ _ _ hinner _, req =>
      RootEtaKXReq.isPiSpinedFixed hinner req
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => true

/-- Output leaves produced by Stratum A (`xTcFixed`) on a Π-spined
    `RootEtaKXReq`. -/
def RootEtaKXReq.stratumALeaves {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} {Γ : LCtx} (hsep : SepAt E n Γ) {A B : Expr Nat} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    RootEtaKXReq.isPiSpinedFixed h req = true →
    List (Jd E n)
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta .., req, hp =>
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      XOut.leaves (xTcFixed hsep q hp rfl rfl).1
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hp =>
      RootEtaKXReq.stratumALeaves hsep hinner req hp
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => []

/-- Every leaf of Stratum A (`xTcFixed`) on a Π-spined `RootEtaKXReq` is
    strictly `SubOf` some leaf of the request. -/
theorem rootEtaKStratumA_outputs_strict {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} {Γ : LCtx} (hsep : SepAt E n Γ) {A B : Expr Nat} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    (hp : RootEtaKXReq.isPiSpinedFixed h req = true) →
    ∀ ℓ ∈ RootEtaKXReq.stratumALeaves hsep h req hp,
      ∃ d ∈ RootEtaKXReq.leavesOf h req, SubOf ℓ d
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta .., req, hp =>
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      (xTcFixed hsep q hp rfl rfl).2
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hp =>
      rootEtaKStratumA_outputs_strict hsep hinner req hp
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _
  | _, _, _, .consts .., _, _ | _, _, _, .bvarZeta .., _, _
  | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _
  | _, _, _, .pi .., _, _ | _, _, _, .letE .., _, _
  | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _
  | _, _, _, .iotaStarK .., _, _ | _, _, _, .peq .., _, _ => fun _ hℓ => nomatch hℓ

/-- Strict `OM3_edge` for the Stratum-A (`xTcFixed`) outputs of any Π-spined
    `rootEtaKXReqOf R hf_step hs`, with NO `X` or `SepAll` premise. -/
theorem rootEtaKStratumA_outputs_edge {E : ResolvedEnv} {n : Nat}
    (R Z : List (Jd E n)) {Γ : LCtx} (hsep : SepAt E n Γ)
    {f f' A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hs : ∃ r ∈ R, SubEq (.pr hf_step) r)
    (hp : RootEtaKXReq.isPiSpinedFixed hf_step (rootEtaKXReqOf R hf_step hs) = true) :
    OM3_edge (R ++ Z)
      (RootEtaKXReq.stratumALeaves hsep hf_step (rootEtaKXReqOf R hf_step hs) hp ++ Z) := by
  have hne : R ≠ [] := by
    obtain ⟨_, hr, _⟩ := hs
    intro hnil; rw [hnil] at hr; exact nomatch hr
  refine om3_edge_of_strictLeaves hne (fun ℓ hℓ => ?_)
  obtain ⟨d, hd, hsd⟩ :=
    rootEtaKStratumA_outputs_strict hsep hf_step (rootEtaKXReqOf R hf_step hs) hp ℓ hℓ
  obtain ⟨r, hr, hdr⟩ := rootEtaKXReqOf_strict R hf_step hs d hd
  exact ⟨r, hr, .trans hsd hdr⟩

/-- General Stratum-A supplier for `RootEtaKDomainConv A h`: for any step `h`
    whose `RootEtaKXReq` is Π-spined, `xTcFixed` + `tyConvT_sort_collapse`
    produce `RootEtaKDomainConv A h` from `EnvWfT`, `hSortUniq`, and `CtxWfT`
    alone — with NO `X` or `SepAll` premise. -/
noncomputable def rootEtaKDomainConv_of_piSpined {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    RootEtaKXReq.isPiSpinedFixed h req = true →
    RootEtaKDomainConv A h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ hA_eta .., req, hp => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hsep : SepAt E n Γ := sepAt_of_sortUniq hW hSortUniq hΓ
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      let o := (xTcFixed hsep q hp rfl rfl).1
      dsimp only [RootEtaKDomainConv]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]; exact PUnit.unit
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ (o.1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨hΓ, k⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hp =>
      rootEtaKDomainConv_of_piSpined hW hSortUniq hΓ R A B hinner req hp
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => PUnit.unit

/-- General Stratum-A supplier for `RootEtaKWrapperAlign A B h`: for any step
    `h` whose `RootEtaKXReq` is Π-spined, `xTcFixed` + `ctxConvVar` +
    `tyConvT_sort_collapse` produce `RootEtaKWrapperAlign A B h` from `EnvWfT`,
    `hSortUniq`, and `CtxWfT` alone — with NO `X` or `SepAll` premise. -/
noncomputable def rootEtaKWrapperAlign_of_piSpined {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (R : List (Jd E n)) (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (req : RootEtaKXReq R A B h) →
    RootEtaKXReq.isPiSpinedFixed h req = true →
    RootEtaKWrapperAlign A B h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ hA_eta .., req, hp => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hsep : SepAt E n Γ := sepAt_of_sortUniq hW hSortUniq hΓ
      let q : EvTc R Γ (.pi A_eta B_eta) (.pi A B) := req
      let o := (xTcFixed hsep q hp rfl rfl).1
      dsimp only [RootEtaKWrapperAlign]
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]
        by_cases hB_eq : B_eta = B
        · rw [if_pos hB_eq]; exact PUnit.unit
        · rw [if_neg hB_eq]; exact o.2.val hcl hinst
      · rw [if_neg hA_eq]
        match tyConvT_sort_collapse hW hSortUniq hΓ (o.1.val hcl hinst) ⟨hA_eta⟩ with
        | .inl e => exact absurd e hA_eq
        | .inr k => exact ⟨k, o.2.val hcl hinst⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, req, hp =>
      rootEtaKWrapperAlign_of_piSpined hW hSortUniq hΓ R A B hinner req hp
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => PUnit.unit

/-- On `wrappedDistinctDomainEtaKChild`, the `RootEtaKXReq` request is Π-spined
    under both `piSpinedTc` and `piSpinedTcFixed`. -/
theorem wrappedDistinctDomain_request_piSpined :
    piSpinedTc (rootEtaKXReqOf [.pr wrappedDistinctDomainEtaKChild]
      wrappedDistinctDomainEtaKChild ⟨_, .head _, .inl rfl⟩) = true := by
  simp only [rootEtaKXReqOf, rootEtaKXReq_build, wrappedDistinctDomainEtaKChild,
    piDomainBeta_conv_commonIndex, commonIndex, piSpinedTc, piSpinedT,
    piSpinedConv, isPi, Bool.and_self]

theorem wrappedDistinctDomain_request_piSpinedFixed :
    piSpinedTcFixed (rootEtaKXReqOf [.pr wrappedDistinctDomainEtaKChild]
      wrappedDistinctDomainEtaKChild ⟨_, .head _, .inl rfl⟩) = true := by
  simp only [rootEtaKXReqOf, rootEtaKXReq_build, wrappedDistinctDomainEtaKChild,
    piDomainBeta_conv_commonIndex, commonIndex, piSpinedTcFixed, piSpinedT,
    piSpinedConv, isPi, Bool.and_self]

/-- Direct Stratum-A provenance components `(cDom, cCod)` on
    `wrappedDistinctDomainEtaKChild` using `xTcFixed` + `ctxConvVar` +
    `sepAt_of_sortUniq`, with NO `X` or `SepAll` premise. -/
def wrappedDistinctDomain_stratumA_out
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    Σ' o : XOut [.pr wrappedDistinctDomainEtaKChild] positiveContext
        domainBeta codomain domain codomain,
      ∀ ℓ ∈ XOut.leaves o,
        ∃ r ∈ ([.pr wrappedDistinctDomainEtaKChild] : List (Jd eqEnvT 2)),
          SubOf ℓ r := by
  let R : List (Jd eqEnvT 2) := [.pr wrappedDistinctDomainEtaKChild]
  have hs : ∃ r ∈ R, SubEq (.pr wrappedDistinctDomainEtaKChild) r :=
    ⟨_, .head _, .inl rfl⟩
  have hsep : SepAt eqEnvT 2 positiveContext :=
    sepAt_of_sortUniq envWf hSortUniq (contextWf one positive_levels)
  let req : EvTc R positiveContext (.pi domainBeta codomain) (.pi domain codomain) :=
    rootEtaKXReqOf R wrappedDistinctDomainEtaKChild hs
  obtain ⟨o, ho⟩ := xTcFixed hsep req wrappedDistinctDomain_request_piSpinedFixed rfl rfl
  refine ⟨o, fun ℓ hℓ => ?_⟩
  obtain ⟨d, hd, hsd⟩ := ho ℓ hℓ
  obtain ⟨r, hr, hdr⟩ :=
    rootEtaKXReqOf_strict R wrappedDistinctDomainEtaKChild hs d hd
  exact ⟨r, hr, .trans hsd hdr⟩

/-- Concrete O-M output edge for `wrappedDistinctDomain_stratumA_out` under
    `hSortUniq` alone (no `X` or `SepAll` premise). -/
theorem wrappedDistinctDomain_stratumA_edge
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (Z : List (Jd eqEnvT 2)) :
    OM3_edge ([.pr wrappedDistinctDomainEtaKChild] ++ Z)
      (XOut.leaves (wrappedDistinctDomain_stratumA_out hSortUniq).1 ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (wrappedDistinctDomain_stratumA_out hSortUniq).2

/-- Concrete `RootEtaKWrapperAlign` for `wrappedDistinctDomainEtaKChild`
    produced through the Stratum-A O-M provenance pipeline
    (`rootEtaKWrapperAlign_of_piSpined` + `tyConvT_sort_collapse`) under
    `hSortUniq` alone. -/
noncomputable def wrappedDistinctDomain_align_via_stratumA
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    RootEtaKWrapperAlign domain codomain wrappedDistinctDomainEtaKChild :=
  rootEtaKWrapperAlign_of_piSpined envWf hSortUniq (contextWf one positive_levels)
    [.pr wrappedDistinctDomainEtaKChild] domain codomain
    wrappedDistinctDomainEtaKChild
    (rootEtaKXReqOf [.pr wrappedDistinctDomainEtaKChild]
      wrappedDistinctDomainEtaKChild ⟨_, .head _, .inl rfl⟩)
    wrappedDistinctDomain_request_piSpinedFixed

/-- Pin: `wrappedDistinctDomainEtaKChild` joins `contracted` at `commonIndex`
    through the Stratum-A O-M provenance pipeline (`xTcFixed` + `ctxConvVar` +
    `tyConvT_sort_collapse`) under `hSortUniq` alone, with NO `X` or `SepAll`
    premise. -/
theorem positive_wrappedDistinctDomainEtaKChild_joins_via_stratumA_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam domainBeta (.bvar 1)) z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedDistinctDomainEtaKChild
    (wrappedDistinctDomain_align_via_stratumA hSortUniq)

/-- Stratum-A constructor-domain inversion for `mk = .const 61 lsC : Loop → Loop`
    in `pinLoopEnvT`: when the lazy inversion chain `(loopMkInv hmk).2.2.1` is
    Π-spined (`piSpinedTcFixed = true`), `xTcFixed` extracts the domain
    conversion to `Loop = .const 60 []` and retypes the constructor field `t`
    at `Loop` with NO `X` or `SepAll` premise. -/
def loopMkDomainInv_of_piSpined {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (hsep : SepAt pinLoopEnvT n Δ)
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm)
    (hp : piSpinedTcFixed (loopMkInv hmk).2.2.1 = true) :
    HasTyT pinLoopEnvT n Δ t (.const 60 []) :=
  let hcl := envClosed_of_envWfT pinLoopGroupRecWfT
  let hinst := envMembersSubstStable_of_envWfT pinLoopGroupRecWfT
  let inv := loopMkInv hmk
  let o := (xTcFixed hsep inv.2.2.1 hp rfl rfl).1
  hasTyT_of_tyConvT (inv.2.2.2.val hcl hinst) (o.1.val hcl hinst).symmT

/-- Strict `OM3_edge` for the Stratum-A (`xTcFixed`) outputs of `(loopMkInv hmk).2.2.1`
    below `[.ty hmk] ++ Z`, with NO `X` or `SepAll` premise. -/
theorem loopMkStratumA_edge {n : Nat} {Δ : LCtx} {lsC : List Level}
    {t Tm : Expr Nat}
    (hsep : SepAt pinLoopEnvT n Δ)
    (hmk : HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm)
    (hp : piSpinedTcFixed (loopMkInv hmk).2.2.1 = true)
    (Z : List (Jd pinLoopEnvT n)) :
    OM3_edge ([.ty hmk] ++ Z)
      (XOut.leaves (xTcFixed hsep (loopMkInv hmk).2.2.1 hp rfl rfl).1 ++ Z) := by
  refine om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ => ?_)
  obtain ⟨d, hd, hsd⟩ := (xTcFixed hsep (loopMkInv hmk).2.2.1 hp rfl rfl).2 ℓ hℓ
  exact ⟨.ty hmk, .head _, .trans hsd (loopMkRequest_leaves_strict hmk d hd)⟩

end Rcic.Declarative.F8EtaK

#print axioms Rcic.Declarative.F8EtaK.tyConvT_sort_collapse
#print axioms Rcic.Declarative.F8EtaK.rootEtaK_childCert
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq
#print axioms Rcic.Declarative.F8EtaK.rootEtaKXReq_build
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq.leavesOf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKXReq_build_strict
#print axioms Rcic.Declarative.F8EtaK.rootEtaKXReqOf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKXReqOf_strict
#print axioms Rcic.Declarative.F8EtaK.rootEtaKXReq_edge
#print axioms Rcic.Declarative.F8EtaK.etaInput_cert
#print axioms Rcic.Declarative.F8EtaK.etaInput_rootEtaKXReq_edge
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq.ansLeaves
#print axioms Rcic.Declarative.F8EtaK.rootEtaKX_outputs_strict
#print axioms Rcic.Declarative.F8EtaK.rootEtaKX_outputs_edge
#print axioms Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_X
#print axioms Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_X
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_general_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_full_joins_of_contract_X
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_full_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.positive_full_eta_lamK_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.positive_stepped_eta_lamK_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.positive_wrappedDistinctDomainEtaKChild_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.positive_wrappedNonreflexiveEtaKChild_joins_of_X
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_request_leaves
#print axioms Rcic.Declarative.F8EtaK.evTc_cast_left_leaves
#print axioms Rcic.Declarative.F8EtaK.pinLoopMk_instType
#print axioms Rcic.Declarative.F8EtaK.loopMkInv
#print axioms Rcic.Declarative.F8EtaK.loopMkRequest_leaves_strict
#print axioms Rcic.Declarative.F8EtaK.loopMkRequest_leaves_subEq
#print axioms Rcic.Declarative.F8EtaK.loopMkRequest_edge
#print axioms Rcic.Declarative.F8EtaK.loopMkX_outputs_edge
#print axioms Rcic.Declarative.F8EtaK.loopMkDomainInv_of_X
#print axioms Rcic.Declarative.F8EtaK.fieldfulK_pinLoopEnvT_of_X
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq.ansLeavesWf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKX_outputs_strict_wf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKX_outputs_edge_wf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_XWf
#print axioms Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_XWf
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_general_joins_of_XWf
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_full_joins_of_contract_XWf
#print axioms Rcic.Declarative.F8EtaK.eta_lamK_full_joins_of_XWf
#print axioms Rcic.Declarative.F8EtaK.positive_full_eta_lamK_joins_of_XWf
#print axioms Rcic.Declarative.F8EtaK.positive_stepped_eta_lamK_joins_of_XWf
#print axioms Rcic.Declarative.F8EtaK.positive_wrappedDistinctDomainEtaKChild_joins_of_XWf
#print axioms Rcic.Declarative.F8EtaK.SepAt
#print axioms Rcic.Declarative.F8EtaK.sepAt_of_sortUniq
#print axioms Rcic.Declarative.F8EtaK.xConvAt
#print axioms Rcic.Declarative.F8EtaK.xTAt
#print axioms Rcic.Declarative.F8EtaK.piSpinedTcFixed
#print axioms Rcic.Declarative.F8EtaK.xTcFixed
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq.isPiSpinedFixed
#print axioms Rcic.Declarative.F8EtaK.RootEtaKXReq.stratumALeaves
#print axioms Rcic.Declarative.F8EtaK.rootEtaKStratumA_outputs_strict
#print axioms Rcic.Declarative.F8EtaK.rootEtaKStratumA_outputs_edge
#print axioms Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_piSpined
#print axioms Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_piSpined
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_request_piSpined
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_request_piSpinedFixed
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_stratumA_out
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_stratumA_edge
#print axioms Rcic.Declarative.F8EtaK.wrappedDistinctDomain_align_via_stratumA
#print axioms Rcic.Declarative.F8EtaK.positive_wrappedDistinctDomainEtaKChild_joins_via_stratumA_of_sortUniq
#print axioms Rcic.Declarative.F8EtaK.loopMkDomainInv_of_piSpined
#print axioms Rcic.Declarative.F8EtaK.loopMkStratumA_edge
