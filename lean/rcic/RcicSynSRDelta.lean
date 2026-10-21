import rcic.RcicSynTableOfIFull
import rcic.RcicSynTableOfITransfer
import rcic.RcicSynStepFieldsDeltaObs
import rcic.RcicSynMSAP
import rcic.RcicSynCensusCorePortRefutations

/-!
# `RcicSynSRDelta` — sr-delta: sortRow row 5 `es_delta` at `tableOfI`

Lane `sr-delta` (sortRow closure, TABLEOFI_SUPPLIER_CENSUS row 5): the kept
branch closer `delta_kept_caseStep_tableI` (`RcicSynTableOfITransfer.lean:340`)
instantiated at `tblI := tableOfI S.env`, `I := tableOfICompat_tableOfI S.env`
(the `es_delta_tableI_compat` pin shape, `RcicSynTableOfIFull.lean:203`).

## Measure

`delta_kept_caseStep_tableI`'s retained telescope:

| premise | disposition |
|---|---|
| `I : TableOfICompat S.env tblI` | discharged — `tableOfICompat_tableOfI S.env` (swe-tableicompat) |
| `hu : levelIsZero (σ hb.reg.1) = false` | branch guard — field data, like row 6's `hrel`; not walled |
| `hap : (defAdm …).hv.AssumpPref` | discharged — `srDelta_defAdm_assumpPref` (§1, unconditional `EnvWfT` induction) |
| `hag : AgreeOn E Aw (enrichEnvWfT S.env).admW` | **(d) wall** — inhabited at the canonical `Aw := (enrichEnvWfT S.env).admW` (the `srDeltaWall_fixture` reflexivity); the `Aw := fun _ ↦ 0` instance is kernel-refuted (`srDelta_agreeOn_zero_refuted` via `agreeOn_zero_admW_refuted`, §5) — the leg is a real constraint on `Aw`, not a per-`Aw` producer |
| `hL : Goal tblI (.cl dl (deltaCanonL …) …)` | **(d) wall** — `delta_canon_cl_L` is a same-subject `eps`-uniqueness obligation: `dl`'s erasure is `.const r (ls.map σ)` or `.star`, gated by the same `levelIsZero (σ ·)` bit as the canonical form — provable only by a missing deep eps-uniqueness theorem; inhabited at `dl := deltaCanonL` by `ConvMod.refl` |
| `hB : Goal tblI (.cl (deltaDbΓ …) hb …)` | **(d) wall** — same shape for the `deltaDbΓ` body surface; inhabited at `hb := deltaDbΓ` |

Deliverable shape (per `swe-sortrow-common`): the exact residual is named
`esDeltaKeptWall` (§2), the conditional field `es_delta_kept_tableOfI`
consumes it at `tableOfI S.env` (§3) with a `tableOfI hW` pin
(`es_delta_kept_tableOfI_pin`), the wall is inhabited on a concrete fixture
(§4, non-vacuity), and the `Aw := fun _ ↦ 0` `AgreeOn` instance is
kernel-refuted (§5) — the `hag` leg is a genuine constraint on the record's
fixed `Aw`, discharged exactly at `Aw := admW`.

**Framing caveat (#7709):** `S : ScopedCtx Eₐ E n Γ` stays at the demanded node
env `E`; nothing here assumes `E₀ = E` — the wall/field are stated at the
closer's own flat telescope.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `defAdm` admission derivations are `AssumpPref` (the `hap` producer) -/

/-- Every transparent admission derivation selected by `(enrichEnvWfT hEnv).defAdm`
    satisfies `TyP.AssumpPref` — the `AssumpPref` analog of `defAdm_closedWf`
    (`RcicSynStepFieldsDeltaIota.lean`), by the same `EnvWfT` tree induction.
    The `.definition` leaf is closed by `assumpPref_enrichHasTyT` fed by the
    L-MSAP proofs and `letCtxConvP_ap`; the preserved-member arms recurse through
    `DefAdm.step`/`DefAdm.lift'`, which keep `.hv` unchanged. -/
theorem srDelta_defAdm_assumpPref : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    {r : Nat} → {m : CheckedMember} → {b : Expr Nat} →
    (hres : E.members r = some m) → (hbody : m.body = some b) →
    (htr : transparent m.mclass = true) →
    ((enrichEnvWfT hEnv).defAdm hres hbody htr).hv.AssumpPref
  | _, .empty, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r' A u hE hfresh hA hcl hlvl, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.axiomM, 0, A, none⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact srDelta_defAdm_assumpPref hE
            ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .definition E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h,
      hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.definitionM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          have hbv : v = b := Option.some.inj hb
          subst hbv
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isTrue rfl hdec]
          simp only [eqRec_self, eqNdrec_self, optNoConf_self]
          exact assumpPref_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
            (memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h'))
            (letCtxConvP_ap (cvWalkHyp_of_envWfT hE)) (.nil E 0) hv trivial
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact srDelta_defAdm_assumpPref hE
            ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .thm E r' A p hE hfresh hA hp hclA hclp hlvlA hlvlp, r, m, b, h, hb,
      htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.theoremM, 0, A, some p⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact srDelta_defAdm_assumpPref hE
            ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .opaque E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h, hb,
      htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.opaqueM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact srDelta_defAdm_assumpPref hE
            ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, m, b, h, hb,
      htr => by
      simp only [enrichEnvWfT, EnvWfP.defAdm, DefAdm.lift']
      exact srDelta_defAdm_assumpPref hE
        ((enrichGroupMembersT (cvWalkHyp_of_envWfT hE)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) hmem).body_old h hb) hb htr

/-! ## §2 the row-5 residual, named -/

/-- ROW 5 RESIDUAL (the named wall, not discharged): `es_delta`'s kept branch at
    `tableOfI S.env` owes exactly these three premises — the `AgreeOn` receipt
    (`hag`), the canonical-left `CL` (`hL`, the `delta_canon_cl_L` wall), and the
    body-surface `CL` (`hB`, the `delta_canon_cl_B` wall). `hu` is the branch
    guard = field data and is NOT in this Prop; `I` and `hap` are discharged
    (`tableOfICompat_tableOfI`, `srDelta_defAdm_assumpPref`). Inhabited on the
    `srDeltaFixture*` fixture at `Aw := admW` (`srDeltaWall_fixture`, §4); the
    `Aw := fun _ ↦ 0` `AgreeOn` instance is refuted in §5 — `hag` constrains
    `Aw`, it is not supplied per-`Aw`. -/
def esDeltaKeptWall {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (Aw : Nat → Nat)
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : Prop :=
  AgreeOn E Aw (enrichEnvWfT S.env).admW
  ∧ Goal (tableOfI S.env)
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ))
  ∧ Goal (tableOfI S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ))

/-! ## §3 the conditional kept-branch field at `tableOfI S.env` -/

/-- `es_delta` (kept branch, `hu = false`) at `tableOfI S.env`, modulo exactly
    `esDeltaKeptWall`: `I` by `tableOfICompat_tableOfI`, `hap` by
    `srDelta_defAdm_assumpPref`, the wall supplies `hag`/`hL`/`hB`. -/
theorem es_delta_kept_tableOfI (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hwall : esDeltaKeptWall Aw hres hbody htr hlen hwf hb dl S σ) :
    CaseStep Aw (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  delta_kept_caseStep_tableI hres hbody htr hlen hwf hb dl dr S σ
    (tableOfICompat_tableOfI S.env) hu hwall.1
    (srDelta_defAdm_assumpPref S.env hres hbody htr) hwall.2.1 hwall.2.2

/-- The `tableOfI hW` pin: for scopes whose `.env` is literally `hW`
    (the flat top-level demanded shape), the conditional field's table IS the
    named `tableOfI hW` — `⟨hW, hext, hctx⟩.env` reduces to `hW`. -/
noncomputable def es_delta_kept_tableOfI_pin {E : ResolvedEnv} (hW : EnvWfT E)
    {Eₐ : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (Aw : Nat → Nat)
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hext : EnvExt E Eₐ) (hctx : CtxWfT E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hwall : esDeltaKeptWall Aw hres hbody htr hlen hwf hb dl
      ⟨hW, hext, hctx⟩ σ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        ⟨hW, hext, hctx⟩ σ
        ((⟨hW, hext, hctx⟩ : ScopedCtx Eₐ E n Γ).can σ)) :=
  es_delta_kept_tableOfI Aw hres hbody htr hlen hwf hb dl dr
    ⟨hW, hext, hctx⟩ σ hu hwall

/-! ## §4 non-vacuity fixture — a concrete admitted member over `emptyEnv`

One 0-arity transparent `.definitionM` member at slot `7`
(`mtype = .sort (.succ .zero)`, `body = .sort .zero`); the wall is inhabited at
`Aw := admW`, `dl := deltaCanonL`, `hb := deltaDbΓ` (both `CL`s by
`ConvMod.refl`), and `hu` computes. -/

/-- The fixture member: a transparent 0-arity definition. -/
def srDeltaFixtureMember : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩

/-- One transparent member over `emptyEnv`. -/
def srDeltaFixtureEnv : ResolvedEnv := extendEnv emptyEnv 7 srDeltaFixtureMember

/-- Its well-formedness: `hA`/`hv` are the two `HasTyT.sort` leaves. -/
def srDeltaFixtureEnvWfT : EnvWfT srDeltaFixtureEnv :=
  .definition emptyEnv 7 (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
    .empty rfl (.sort [] (.succ .zero)) (.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- The node's own flat scope at the fixture env. -/
def srDeltaScope : ScopedCtx srDeltaFixtureEnv srDeltaFixtureEnv 0 [] :=
  ⟨srDeltaFixtureEnvWfT, envExt_refl srDeltaFixtureEnv, .nil⟩

def srDeltaHres : srDeltaFixtureEnv.members 7 = some srDeltaFixtureMember :=
  members_extend_self emptyEnv 7 srDeltaFixtureMember

def srDeltaHbody : srDeltaFixtureMember.body = some (.sort .zero) := rfl

def srDeltaHtr : transparent srDeltaFixtureMember.mclass = true := rfl

def srDeltaHlen : ([] : List Level).length = srDeltaFixtureMember.arity := rfl

def srDeltaHwf : levelsBounded 0 ([] : List Level) = true := rfl

/-- `hb := deltaDbΓ` — the supplier's own closed body surface at `Γ = []`. -/
noncomputable def srDeltaHb :
    TyP srDeltaFixtureEnv 0 [] (instantiateLevels [] (.sort .zero))
      (instantiateLevels [] srDeltaFixtureMember.mtype) :=
  deltaDbΓ srDeltaFixtureEnvWfT [] srDeltaHres srDeltaHbody
    srDeltaHlen srDeltaHwf
    (deltaAdmDb (enrichEnvWfT srDeltaFixtureEnvWfT) srDeltaHres
      srDeltaHbody srDeltaHtr)

/-- `dl := deltaCanonL` — the supplier's canonical left endpoint. -/
noncomputable def srDeltaDl :
    TyP srDeltaFixtureEnv 0 [] (.const 7 [])
      (instantiateLevels [] srDeltaFixtureMember.mtype) :=
  deltaCanonL srDeltaHres srDeltaHlen srDeltaHwf srDeltaHb

/-- The receipt's own admission weights at the fixture env. -/
noncomputable def srDeltaAdmW : Nat → Nat :=
  (enrichEnvWfT srDeltaFixtureEnvWfT).admW

/-- NON-VACUITY: `esDeltaKeptWall` is inhabited on the fixture —
    `hag` at `Aw := admW` by reflexivity, `hL`/`hB` by `ConvMod.refl` at
    `dl := deltaCanonL`, `hb := deltaDbΓ`. -/
theorem srDeltaWall_fixture :
    esDeltaKeptWall srDeltaAdmW srDeltaHres srDeltaHbody srDeltaHtr
      srDeltaHlen srDeltaHwf srDeltaHb srDeltaDl srDeltaScope id :=
  ⟨fun _r _m _ => rfl, ConvMod.refl _, ConvMod.refl _⟩

/-- `hu` (branch guard) inhabited: `srDeltaHb.reg.1` reduces to
    `.succ (.succ .zero)`. -/
theorem srDeltaHu : levelIsZero (id srDeltaHb.reg.1) = false := by
  decide

/-- The conditional field instantiated end-to-end on the fixture:
    `es_delta_kept_tableOfI` discharges a real `CaseStep` at
    `tableOfI srDeltaFixtureEnvWfT`. -/
theorem srDeltaEsKept_tableOfI_fixture :
    CaseStep srDeltaAdmW (tableOfI srDeltaFixtureEnvWfT)
      (.es (CvP.delta srDeltaFixtureEnv 0 [] 7 [] srDeltaFixtureMember
        (.sort .zero) srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
        srDeltaHwf srDeltaHb srDeltaDl srDeltaHb)
        srDeltaScope id (srDeltaScope.can id)) :=
  es_delta_kept_tableOfI srDeltaAdmW srDeltaHres srDeltaHbody srDeltaHtr
    srDeltaHlen srDeltaHwf srDeltaHb srDeltaDl srDeltaHb srDeltaScope id
    srDeltaHu srDeltaWall_fixture

/-! ## §5 kernel refutation of the `Aw := fun _ ↦ 0` `AgreeOn` instance -/

/-- REFUTED at the real instance: `AgreeOn` with `Aw := fun _ ↦ 0` fails at
    the fixture env — `agreeOn_zero_admW_refuted`
    (RcicSynCensusCorePortRefutations) — the admission weights charge
    `r ↦ 1`. So `hag` is a genuine constraint on the record's `Aw` (not an
    automatic discharge); it is inhabited exactly at `Aw := admW`
    (`srDeltaWall_fixture`). -/
theorem srDelta_agreeOn_zero_refuted :
    ¬ AgreeOn srDeltaFixtureEnv (fun _ => 0)
        (enrichEnvWfT srDeltaFixtureEnvWfT).admW :=
  CensusCorePortRefutations.agreeOn_zero_admW_refuted srDeltaFixtureEnvWfT
    srDeltaHres

#print axioms Rcic.Syn.srDelta_defAdm_assumpPref
#print axioms Rcic.Syn.esDeltaKeptWall
#print axioms Rcic.Syn.es_delta_kept_tableOfI
#print axioms Rcic.Syn.es_delta_kept_tableOfI_pin
#print axioms Rcic.Syn.srDeltaFixtureMember
#print axioms Rcic.Syn.srDeltaFixtureEnv
#print axioms Rcic.Syn.srDeltaFixtureEnvWfT
#print axioms Rcic.Syn.srDeltaScope
#print axioms Rcic.Syn.srDeltaHres
#print axioms Rcic.Syn.srDeltaHbody
#print axioms Rcic.Syn.srDeltaHtr
#print axioms Rcic.Syn.srDeltaHlen
#print axioms Rcic.Syn.srDeltaHwf
#print axioms Rcic.Syn.srDeltaHb
#print axioms Rcic.Syn.srDeltaDl
#print axioms Rcic.Syn.srDeltaAdmW
#print axioms Rcic.Syn.srDeltaWall_fixture
#print axioms Rcic.Syn.srDeltaHu
#print axioms Rcic.Syn.srDeltaEsKept_tableOfI_fixture
#print axioms Rcic.Syn.srDelta_agreeOn_zero_refuted

end Rcic.Syn
