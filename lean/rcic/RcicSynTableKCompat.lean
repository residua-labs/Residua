import rcic.RcicSynTableK
import rcic.RcicSynTableKMeasure
import rcic.RcicSynTableOfIFull

/-!
# RcicSynTableKCompat — the closer's table retargeted to `tableOfK`

cc 16:45Z item, lane glm/sr4-tablek — branched off `devin/routec-estar`
@22fb258cca (#7843 OPEN when this was written). swe-routec-estar measured:
`ES` at the Eq `ConvT.iota` cell (`eqIotaK`) is FALSE at `tableOfI` (the
only head-65 rule is constructor-major; the erased endpoints are
EStep-normal and LvlEq-distinct) and TRUE at `tableOfK` (`eqK_es`) — the
bare nullary K rule `iotaRulesKOf` emits *instead of* the ctor-major
rules at gated singleton-`Prop` large-eliminating groups. So
`AllBelowScoped E Aw (tableOfI hW)` cannot hold on such environments; the
closer must be instantiated at `tableOfK hW` there.

## What transfers (this module)

`TableOfICompat` is already the right interface — `sup` +
`wf` + `headM`. `tableOfK` satisfies it verbatim:

* `sup` — `mem_tableOfK_of_mem_tableOf` (estar, landed on the branch):
  every δ rule of `tableOf` survives;
* `wf` — `tableWF_tableOfK` (estar) — and `confluent_eStep_tableOfK`
  covers the confluence the erased-step lemmas use;
* `headM` — `tableOfK_headM` below: `tableOfK_head_major` resolves every
  head to `.definitionM` (δ) or `.recursorM` (K/ctor ι emission) — never
  `.inductiveM`, the same shape as `tableOfI_headM`.

Given `tableOfICompat_tableOfK`, every `*_tableI` lemma applies at
`tableOfK` with no further work — `§2` instantiates the canonical
corollaries, `§3` the `es_*` field pins. `§4` is the gated-`iota`
difference: the ctor-major route is absent there by design
(`iotaRulesKOf` emits `[K]` instead), and the Eq `es` cell closes through
the closer's own `CaseStep` shape via `eqK_es` (`eqK_es_caseStep`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.KernelRowsAssembly

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv} {Aw : Nat → Nat}

/-! ## §1 — the compat instance -/

/-- `TableOfICompat.headM` at `tableOfK`: `tableOfK_head_major` resolves
    every rule head to `.definitionM` (δ half, unchanged) or `.recursorM`
    (group emissions — bare K or ctor-major at non-gated groups). -/
theorem tableOfK_headM {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ ρ ∈ tableOfK hW, ∃ m, E.members ρ.head = some m ∧
      m.mclass ≠ .inductiveM :=
  fun ρ hρ =>
    (tableOfK_head_major hW ρ hρ).elim
      (fun ⟨m, hm, hmc, _⟩ =>
        ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩)
      (fun ⟨m, hm, hmc, _⟩ =>
        ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩)

/-- `tableOfK` satisfies the same `TableOfICompat` interface: sup
    (`mem_tableOfK_of_mem_tableOf`), wf (`tableWF_tableOfK`), headM
    (`tableOfK_headM`). Every `*_tableI` transfer lemma then instantiates
    at `tableOfK hW` verbatim. -/
theorem tableOfICompat_tableOfK {E : ResolvedEnv} (hW : EnvWfT E) :
    TableOfICompat hW (tableOfK hW) where
  sup := fun _ρ hρ => mem_tableOfK_of_mem_tableOf hW hρ
  wf := tableWF_tableOfK hW
  headM := tableOfK_headM hW

/-! ## §2 — canonical corollaries at `tableOfK` (`I` discharged by the K instance) -/

/-- `sortRow_of_allBelowScoped_tableI` at `tableOfK hW`. -/
theorem sortRow_of_allBelowScoped_tableOfK {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOfK hW)) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_allBelowScoped_tableI hW (tableOfICompat_tableOfK hW) hBel

/-- `sortRow_of_suppliers_tableI` at `tableOfK hW`. -/
theorem sortRow_of_suppliers_tableOfK {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (W : StepSuppliers Aw (tableOfK hW) E) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_suppliers_tableI hW (tableOfICompat_tableOfK hW) W

/-- `built_no_family_rule_tableI` at `tableOfK hW`: an `.inductiveM`
    member ref is never a `tableOfK` rule head. -/
theorem built_no_family_rule_tableOfK {E : ResolvedEnv} (hW : EnvWfT E)
    {f : Nat} {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) : NoHeadRule (tableOfK hW) f :=
  built_no_family_rule_tableI hW (tableOfICompat_tableOfK hW) hf hclass

/-- `convE_appN_const_inv_tableI` at `tableOfK hW`: erased family
    rigidity. -/
theorem convE_appN_const_inv_tableOfK {E : ResolvedEnv} (hW : EnvWfT E)
    {f : Nat} {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) {ls ls' : List Level}
    {xs ys : List ETm}
    (h : ConvMod (EStep (tableOfK hW)) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep (tableOfK hW)) LvlEq) xs ys :=
  convE_appN_const_inv_tableI hW (tableOfICompat_tableOfK hW) hf hclass h

/-- `deltaRule_mem_tableI` at `tableOfK hW`: δ-rule membership of the K
    table. -/
theorem deltaRule_mem_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    deltaRule r (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr) ∈
      tableOfK hEnv :=
  deltaRule_mem_tableI hEnv (tableOfICompat_tableOfK hEnv) hres hbody htr

/-! ## §3 — the `es_*` field pins at `tableOfK` -/

/-- `es_pi` at `tableOfK` with `TableWF` discharged by `tableWF_tableOfK`:
    the remaining telescope is exactly the row's retained (d) walls. -/
noncomputable def es_pi_tableK_wf (hW : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level} =>
    es_pi_field_of_tableWF (Eₐ := Eₐ) Aw (tableOfK hW)
      (tableWF_tableOfK hW) (E₀ := E₀) (n₀ := n₀) (Γ₀ := Γ₀) (E := E')
      (n := n) (Γ := Γ) (A := A) (A' := A') (B := B) (B' := B') (u := u) (v := v)

/-- `es_letE` at `tableOfK` with `TableWF` discharged. -/
noncomputable def es_letE_tableK_wf (hE : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx}
      {A A' v v' b b' B : Expr Nat} {u : Level} =>
    es_letE_closed (Eₐ := Eₐ) (E₀ := E₀) (n₀ := n₀) (Γ₀ := Γ₀) (E := E)
      (n := n) (Γ := Γ) (A := A) (A' := A') (v := v) (v' := v') (b := b)
      (b' := b') (B := B) (u := u) (hE := hE)
      (hTbl := tableWF_tableOfK hE)

/-- `es_eta` at `tableOfK` with the residuum's `tableWF` field discharged:
    `r`'s remaining fields are the row's retained (d) walls. -/
noncomputable def es_eta_tableK_wf (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E' n Γ f (.pi A B))
    (dl : TyP E' n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E' n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (r : EtaResiduum Aw (tableOfK hW) hf dl σ ρ) :
    CaseStep Aw (tableOfK hW) (.es (CvP.eta E' n Γ f A B hf dl dr) S σ ρ) :=
  es_eta_closed Aw (tableOfK hW) hf dl dr S σ ρ
    { r with tableWF := tableWF_tableOfK hW }

/-- `es_fsub` at `tableOfK` with `TableWF` discharged: retained walls =
    `hL`/`hR` (the `instEnd` composite CLs). -/
noncomputable def es_fsub_tableK_wf (hW : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level} =>
    es_fsub_field_closed (Eₐ := Eₐ) (Aw := Aw) (tbl := tableOfK hW)
      (E₀ := E₀) (n₀ := n₀) (Γ₀ := Γ₀) (E := E') (n := n) (Γ := Γ) (A := A)
      (B := B) (Sx := Sx) (a := a) (b := b) (u := u)
      (hTbl := tableWF_tableOfK hW)

/-- `es_delta` at `tableOfK` with `TableOfICompat` discharged:
    `delta_kept_caseStep_tableI` instantiated at `tblI := tableOfK S.env`,
    `I := tableOfICompat_tableOfK S.env` — retained walls =
    `hu hag hap hL hB`. -/
noncomputable def es_delta_tableK_compat {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat} (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :=
  delta_kept_caseStep_tableI (Aw := Aw) (r := r) (ls := ls) (m := m)
    (b := b) (S := S) (σ := σ) (tblI := tableOfK S.env)
    (I := tableOfICompat_tableOfK S.env)

/-! ## §4 — the gated `iota` cell: the Eq `es` cell closes at `tableOfK`

    `eqK_es` (estar, `RcicSynTableKMeasure` §2) is `ES` at the post-irr
    `ConvT.iota` Eq cell `eqH` under `tableOfK` — and `Goal` of the `.es`
    query is literally that `ES`, so the cell closes through the closer's
    own `CaseStep` shape with no ports. The ctor-major route this
    replaces at `tableOfI` is absent at `tableOfK` by `iotaRulesKOf`'s
    replacement emission. -/

/-- `eqK_es` as a `CaseStep`: `Goal (tableOfK _) (.es eqH _ id _)`
    reduces to `ES (tableOfK _) id (eqScope.can id) eqH` — `eqK_es`
    verbatim. -/
theorem eqK_es_caseStep (Aw : Nat → Nat) :
    CaseStep Aw (tableOfK pinEqGroupWfT)
      (.es eqH eqScope id (eqScope.can id)) :=
  fun _ _ => eqK_es

#print axioms tableOfK_headM
#print axioms tableOfICompat_tableOfK
#print axioms sortRow_of_allBelowScoped_tableOfK
#print axioms sortRow_of_suppliers_tableOfK
#print axioms built_no_family_rule_tableOfK
#print axioms convE_appN_const_inv_tableOfK
#print axioms deltaRule_mem_tableOfK
#print axioms es_pi_tableK_wf
#print axioms es_letE_tableK_wf
#print axioms es_eta_tableK_wf
#print axioms es_fsub_tableK_wf
#print axioms es_delta_tableK_compat
#print axioms eqK_es_caseStep

end Rcic.Syn
