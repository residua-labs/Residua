import rcic.RcicSynStepSkeleton
import rcic.RcicSynWalkLetAP
import rcic.RcicTypedRowsWf
import rcic.RcicIotaLegacyBridge
import rcic.RcicIotaSRRows
import rcic.RcicDT008Equiv
import rcic.RcicDT021Rows
import rcic.RcicMachineSoundTyped
import rcic.RcicTypedMachineAccept
import rcic.RcicAnnEnvBridgeGroup

/-!
# RcicSynBelowCToRows — the `StepSuppliers → AllBelowScoped → hcoh → census rows` wiring

cc NEW ITEM (2026-10-17): the wiring from the BelowC fixpoint to the census rows.
The map `research/rcic/sortrow/BELOWC_TO_ROWS.md` is the companion inventory; this
module is its machine-checked half.

**Chain shape.** `RcicSynStepSkeleton.allBelowScoped_of_suppliers` already supplies
`AllBelowScoped Eₐ Aw tbl` from `W : StepSuppliers Aw tbl Eₐ` under `TableWF tbl`.
`RcicSynBelowScoped`'s extractors turn each demanded root into `ES`/`CL`/`EUT`/…
answers at a `ScopedCtx`'s canonical disposition `S.can σ` — each gated on
`TyP.AssumpPref`/`CvP.AssumpPref` receipts and `LevelHom σ`.
`RcicSynSortRow.sortRow_of_tyCvP_esChain_id` collapses a `TyCvP.ESChain` over a
`sort–sort` chain into `eqN u v`. What was missing between them — and is built
here — is the **scoped ESChain assembler** `esChain_of_allBelowScoped` (the
`ScopedCtx`/`AssumpPref`-gated analogue of the unscoped `esChain_of_allBelow`,
which needs `DispFor` the scoped pack does not carry).

**Missing links stay named hypotheses** (`BELOWC_TO_ROWS.md` §2): `hMSAP`
(member-sort `AssumpPref` of the `EnvWfT`-fronted pack — an env-induction
obligation not yet on the tree, cf. RcicSynP2Shared:849), `hPi`/`hFam`
(`TyConvT`-level Π- and family-application injectivity — the `PiRowInjT` wall,
present only through the `InScope`/annotated bridge, not through BelowC), and
`hEnv.InScope` for the two PARTIAL rows (orthogonal env-membership evidence —
`StepSuppliers` is kept in those signatures per the requested shape but is not
consumed by them). No `sorry`, no claimed inhabitant of `StepSuppliers`;
`closure_claim = 0`.

Rows wired (all conditional on the stated hypotheses):
DT-010 `dt010_of_suppliers`, DT-011 `dt011_of_suppliers`,
DT-012 `dt012_of_suppliers`, DT-019 `dt019_of_suppliers`,
DT-021 `dt021_of_suppliers`, IA-024 `ia024_of_suppliers`,
RM-014 `rm014_of_suppliers`, RM-017 `rm017_of_suppliers`.
-/

namespace Rcic.Syn

open Rcic.Declarative Rcic.Machine

/-- Per-node `CvP.AssumpPref` along a `TyCvP` chain — the receipt each
    `es_of_allBelowScoped`/`cl_of_allBelowScoped` call needs at `.of` nodes, carried
    through `.trans` pairs. `.refl` nodes hold no `CvP` and need nothing. -/
def TyCvP.AllAP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → TyCvP E n Γ A B → Prop
  | _, _, .refl _ _ => True
  | _, _, .of _ _ _ _ h => h.AssumpPref
  | _, _, .trans _ _ _ _ c₁ c₂ => c₁.AllAP ∧ c₂.AllAP

/-- The chain's right endpoint with its `AssumpPref` receipt: either the chain is
    refl-only (so `A = B` and the caller's own `dA` serves as middle typing), or it
    ends in a `TyP` of `B` at some `.sort uR` — the `.trans` middle. This is the
    AP-carrying right half of `TyCvP.endpoints` (RcicSynSepUnique:221); casts across
    a refl-only right half go through `tyCast`, keeping the receipt via
    `assumpPref_tyCast`. -/
def TyCvP.endpointsR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → (c : TyCvP E n Γ A B) → c.AllAP →
      PSum (A = B) ((uR : Level) × (dR : TyP E n Γ B (.sort uR)) ×' dR.AssumpPref)
  | _, _, .refl _ _, _ => .inl rfl
  | _, _, .of _ _ _ u h, hAP => .inr ⟨u, h.dr, assumpPref_dr hAP⟩
  | _, _, .trans _ _ _ _ c₁ c₂, hc =>
      match c₁.endpointsR hc.1, c₂.endpointsR hc.2 with
      | .inl h₁, .inl h₂ => .inl (h₁.trans h₂)
      | .inl _, .inr q => .inr q
      | .inr ⟨uR₁, dR₁, hd₁⟩, .inl h₂ =>
          .inr ⟨uR₁, tyCast h₂ rfl dR₁, assumpPref_tyCast h₂ rfl hd₁⟩
      | .inr _, .inr q => .inr q

/-- **The scoped ESChain assembler** — the structural link between the landed
    `AllBelowScoped` extractors and `sortRow_of_tyCvP_esChain_id`. `AllBelowScoped`
    answers each `ES`/`CL` demand at disposition `S.can σ`; induction over the chain
    stitches them per node, using `endpointsR` for the `.trans` middle typing. -/
theorem esChain_of_allBelowScoped {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) {σ : Level → Level} (hσ : LevelHom σ) :
    ∀ {A B T₁ T₂ : Expr Nat} (c : TyCvP E n Γ A B), c.AllAP →
      (dA : TyP E n Γ A T₁) → dA.AssumpPref →
      (dB : TyP E n Γ B T₂) → dB.AssumpPref →
      TyCvP.ESChain tbl σ (S.can σ) c dA dB
  | _, _, _, _, .refl _ _, _, dA, hA, dB, hB =>
      .refl dA dB (cl_of_allBelowScoped hBel S hσ dA dB hA hB)
  | _, _, _, _, .of _ _ _ _ h, hAP, dA, hA, dB, hB =>
      .of h dA dB
        (cl_of_allBelowScoped hBel S hσ dA h.dl hA (assumpPref_dl hAP))
        (es_of_allBelowScoped hBel S hσ h hAP)
        (cl_of_allBelowScoped hBel S hσ h.dr dB (assumpPref_dr hAP) hB)
  | _, _, _, _, .trans _ _ _ _ c₁ c₂, hc, dA, hA, dB, hB =>
      match c₁.endpointsR hc.1 with
      | .inl hAB =>
          .trans c₁ c₂ dA (tyCast hAB rfl dA) dB
            (esChain_of_allBelowScoped hBel S hσ c₁ hc.1 dA hA
              (tyCast hAB rfl dA) (assumpPref_tyCast hAB rfl hA))
            (esChain_of_allBelowScoped hBel S hσ c₂ hc.2
              (tyCast hAB rfl dA) (assumpPref_tyCast hAB rfl hA) dB hB)
      | .inr ⟨_, dR₁, hdR₁⟩ =>
          .trans c₁ c₂ dA dR₁ dB
            (esChain_of_allBelowScoped hBel S hσ c₁ hc.1 dA hA dR₁ hdR₁)
            (esChain_of_allBelowScoped hBel S hσ c₂ hc.2 dR₁ hdR₁ dB hB)

/-- `enrichTyConvT` preserves the `AllAP` receipt: each `.of` node's enriched `CvP`
    satisfies `AssumpPref` by `assumpPref_enrichConvT`, given the member-sort and
    let-ctx AP packs plus the context spine's own AP. -/
theorem enrichTyConvT_allAP {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E)
    {hm : MemberSortP E} (hAm : MemberSortP.AssumpPref hm)
    {hlet : LetCtxConvP E n} (hAlet : LetCtxConvP.AssumpPref hlet)
    {Γ : LCtx} (C : CtxP E n Γ) (hAC : C.AssumpPref) :
    ∀ {A B : Expr Nat} (h : TyConvT E₁ n Γ A B),
      (enrichTyConvT hcl hext hm hlet C h).AllAP
  | _, _, .refl _ _ => trivial
  | _, _, .of _ _ _ _ h => assumpPref_enrichConvT hcl hext hAm hAlet C h hAC
  | _, _, .trans _ _ _ _ h₁ h₂ =>
      ⟨enrichTyConvT_allAP hcl hext hAm hAlet C hAC h₁,
        enrichTyConvT_allAP hcl hext hAm hAlet C hAC h₂⟩

/-- `EnvWfT`-fronted `enrichTyConvT_allAP`: the let-ctx AP is discharged by the
    landed `letCtxConvP_ap`; the member-sort AP is the named hypothesis `hMSAP`
    (**missing link L-MSAP** — see `BELOWC_TO_ROWS.md` §2). -/
theorem enrichTyConvT_of_envWfT_allAP {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E)
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (h : TyConvT E n Γ A B) :
    (enrichTyConvT_of_envWfT hEnv hΓ h).AllAP :=
  enrichTyConvT_allAP (envClosed_of_envWfT hEnv) (envExt_refl E) hMSAP
    (letCtxConvP_ap (cvWalkHyp_of_envWfT hEnv)) (enrichCtxWfT_of_envWfT hEnv hΓ)
    (assumpPref_enrichCtxWfT (envClosed_of_envWfT hEnv) (envExt_refl E) hMSAP
      (letCtxConvP_ap (cvWalkHyp_of_envWfT hEnv)) hΓ) h

/-- **hcoh, row-level** (`TypedRowsWf.sortRow` shape): a `TyConvT` chain between two
    sorts collapses to `eqN`, supplied entirely by `StepSuppliers` — enrich the
    chain, assemble its `ESChain` from `AllBelowScoped`, close with
    `sortRow_of_tyCvP_esChain_id` at `σ = id`, `ρ = S.can id`. -/
theorem sortRow_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v :=
  let S : ScopedCtx Eₐ E n Γ := ⟨hEnv, hext, hΓ⟩
  sortRow_of_tyCvP_esChain_id hTbl (enrichTyConvT_of_envWfT hEnv hΓ h) (S.can id)
    (esChain_of_allBelowScoped (allBelowScoped_of_suppliers Aw tbl hTbl W) S levelHom_id _
      (enrichTyConvT_of_envWfT_allAP hEnv hMSAP hΓ h)
      (TyP.sort E n Γ u (.succ u) (eqN_refl _)) trivial
      (TyP.sort E n Γ v (.succ v) (eqN_refl _)) trivial)

/-- **Missing link L-PI** — `TypedRowsWf.piRow`'s field shape, verbatim: native
    Π-injectivity at the `TyConvT` level. Not supplied by the BelowC pack (its
    answers are erasure-level `ConvMod (EStep tbl)`); the only landed producer is
    the `InScope`-fronted annotated bridge `piConvInjT_inScope`, which this route
    does not consume. Stated as a named hypothesis, per the map. -/
abbrev PiRowLink (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- **Missing link L-FAM** — `TypedRowsWf.famAppRow`'s field shape, verbatim:
    family-application injectivity at the `TyConvT` level. Same status as L-PI
    (annotated front `famAppConvInjT_inScope` exists under `InScope`). -/
abbrev FamAppRowLink (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level},
    E.members r = some m → m.mclass = .inductiveM →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') →
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'

/-- `TypedRowsWf` assembled under the BelowC supply: `sortRow` is **proved** through
    `StepSuppliers → AllBelowScoped → ESChain`; `piRow`/`famAppRow` remain the named
    hypotheses `hPi`/`hFam` — BelowC does not answer `TyConvT`-level injectivity. -/
theorem typedRowsWf_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n) : TypedRowsWf E n where
  sortRow := sortRow_of_suppliers hTbl W hEnv hext hMSAP
  piRow := hPi
  famAppRow := hFam

/-- **DT-010** — one-step subject reduction, `StepSuppliers`-supplied rows. -/
theorem dt010_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam) hΓ h hs

/-- **DT-011** — multi-step subject reduction, `StepSuppliers`-supplied rows. -/
theorem dt011_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam) hΓ h hs

/-- **DT-012** — type uniqueness, `StepSuppliers`-supplied rows (`sortRow`/`piRow`;
    `famAppRow` enters only through the assembled `TypedRowsWf` record). -/
theorem dt012_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A : Expr Nat}
    (h : HasTyT E n Γ e A) {B : Expr Nat} (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_typedRowsWf hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam) hΓ h hB

/-- **DT-019** — typed ι subject reduction, `StepSuppliers`-supplied rows. -/
theorem dt019_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam) hΓ hd hlhs

/-- **DT-021** — no-cumulativity, `StepSuppliers`-supplied rows (`sortRow`). -/
theorem dt021_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level} {T : Expr Nat}
    (hc : ConvT E n Γ (.sort u) (.sort v) T) : eqN u v :=
  DT021T_no_cumulativity_of_typedRowsWf hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam) hΓ hc

/-- **IA-024** — `IotaSRTN` supply from the `StepSuppliers`-assembled rows. -/
theorem ia024_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    (hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv))
    (hPi : PiRowLink E n) (hFam : FamAppRowLink E n) : IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hEnv
    (typedRowsWf_of_suppliers hTbl W hEnv hext hMSAP hPi hFam)

/-- **RM-014** — typed whnf-acceptance soundness. The PARTIAL rows' premise is
    `hEnv.InScope` (**missing link L-SCOPE**): env-membership evidence orthogonal to
    `StepSuppliers`, kept here as a named hypothesis — `W` is retained only to fix
    the uniform `StepSuppliers … → carrier` shape and is not consumed. -/
theorem rm014_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (_hTbl : TableWF tbl) (_W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hP : hEnv.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A e w : Expr Nat) (htask : s.task = .whnfAt A e)
    (hty : HasTyT E n Γ e A)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    Nonempty (HasTyT E n Γ w A) :=
  RM014T_whnf_typed hEnv hP hΓ s hamb A e w htask hty hacc

/-- **RM-017** — typed conversion-acceptance soundness. Same L-SCOPE naming as
    `rm014_of_suppliers`: the BelowC fixpoint does not produce `InScope`. -/
theorem rm017_of_suppliers {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (_hTbl : TableWF tbl) (_W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} (hEnv : EnvWfT E) (hP : hEnv.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A l r T : Expr Nat) (htask : s.task = .convAt A l r)
    (htyl : HasTyT E n Γ l T) (htyr : HasTyT E n Γ r T)
    (hacc : kernelStepRaw s = .result (.accepted .conversionConfirmed)) :
    Nonempty (ConvT E n Γ l r T) :=
  RM017T_conversion_confirmed hEnv hP hΓ s hamb A l r T htask htyl htyr hacc

end Rcic.Syn

#print axioms Rcic.Syn.TyCvP.AllAP
#print axioms Rcic.Syn.TyCvP.endpointsR
#print axioms Rcic.Syn.esChain_of_allBelowScoped
#print axioms Rcic.Syn.enrichTyConvT_allAP
#print axioms Rcic.Syn.enrichTyConvT_of_envWfT_allAP
#print axioms Rcic.Syn.sortRow_of_suppliers
#print axioms Rcic.Syn.typedRowsWf_of_suppliers
#print axioms Rcic.Syn.dt010_of_suppliers
#print axioms Rcic.Syn.dt011_of_suppliers
#print axioms Rcic.Syn.dt012_of_suppliers
#print axioms Rcic.Syn.dt019_of_suppliers
#print axioms Rcic.Syn.dt021_of_suppliers
#print axioms Rcic.Syn.ia024_of_suppliers
#print axioms Rcic.Syn.rm014_of_suppliers
#print axioms Rcic.Syn.rm017_of_suppliers
