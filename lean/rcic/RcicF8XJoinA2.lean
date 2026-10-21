import rcic.RcicEtaKDecide
import rcic.RcicF8XValleyVia

/-!
# RcicF8XJoinA2 — the A.2 JOIN fixture and its A1 payment evidence

cc's A1 ruling on the `W-X-SUBST-JOIN` measure (ChatGPT's spec
`research/rcic/x-tile/S0_W_X_SUBST_JOIN_MEASURE.md` §5): promote the
research probe `research/rcic/x-tile/SUBST2_A2_JOIN_FIXTURE_2026_10_16.lean`
to a sealed module and pin, against the REAL fixture objects, the
kept-cut payment evidence.

**Reachability / shape.** `om_etaK_annot_piChain U X rfl hfA2 hsubA2 hfA2
hsubA2` (RcicEtaKDecide.lean) flattens to three links in ONE segment —
`ofCv u (symm (lit betaRedexConvAt))`, the `subst0` instantiation link
carrying the X-answered codomain chain, and `ofCv u (lit betaRedexConvAt)`
— because both middles are `betaRedex`, not Π. The landed admissions
`Flat.segAdm` (multi-link arm `bLink l && rest.bPrefix`), `xAdm` and
`xAdmW` all refuse it: `bLink`/`bLinkW` refuse `subst0`. That is exactly
the `W-X-SUBST-JOIN` shape.

**A1 payment evidence (spec §5).** With `b := .cv (betaRedexConvAt ΓA2)`,
`k := .ty (piXTy ΓA2)`, `f := .ty a2_fTy` and `Q := (X R c_fn).2.leaves`:
the substitution's `ha_cast` keeps exactly `[k]`, `k` is an immediate
original child of the β atom `b` (the third typing field of
`betaRedexConvAt` IS `piXTy ΓA2`), and the node-counter weights are
`b.wt = 6`, `k.wt = 3`, `f.wt = 1` — so `k.wt < b.wt` by the landed
`child_wt_lt`, and the original input leaves have the exact layout
`L = [b] ++ Q ++ [k] ++ [b]`. The genuinely-present β atom is the payer.

**Not declared here.** The call-edge corollaries `a2_call_below_beta`,
`a2_call_edge`, `a2_no_kept_budget_refusal` consume codex-jvia's A0
(`om3_edge_of_cut_kept`, the highest-differing-weight criterion) once it
lands — the names are reserved in prose, not declared.

**The probe stays research-only.** This module supersedes
`SUBST2_A2_JOIN_FIXTURE_2026_10_16.lean` (which keeps its local
`segJoinS'` stand-in and is not in the seal); here the landed predicates
`segAdm`/`xAdm`/`xAdmW`/`bLinkW` carry the pins.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn
open Rcic.Declarative.F8EtaK

set_option autoImplicit false

section A2JoinFixture

/-- `piX : sX` at an arbitrary context — `pinPiT` lifted off the empty context. -/
def piXTy (Γ : LCtx) : HasTyT emptyEnv 0 Γ piX sX :=
  .pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort Γ .zero) (.sort _ .zero)

/-- `betaRedex ≡ piX` at `sX` in context `Γ` — `betaRedexConv` at an arbitrary Γ.
    The third typing field IS `piXTy Γ`: that is what makes the Π typing the
    β atom's kept original child. -/
def betaRedexConvAt (Γ : LCtx) : ConvT emptyEnv 0 Γ betaRedex piX sX :=
  .beta Γ sX (.bvar 0) piX sX (.succ (.imax (.succ .zero) (.succ .zero)))
    (.sort Γ _) (.bvar (.assumption sX :: Γ) 0 sX rfl) (piXTy Γ)

/-- the context: one variable `f : Π y : sX. betaRedex`. -/
abbrev ΓA2 : LCtx := [.assumption (.pi sX betaRedex)]

/-- the function variable's typing — named so the `f` atom is the real object. -/
def a2_fTy : HasTyT emptyEnv 0 ΓA2 (.bvar 0) (.pi sX betaRedex) :=
  .bvar ΓA2 0 _ rfl

/-- `f piX : piX` in `ΓA2`: the `app` node types it at `instantiate0 piX betaRedex =
    betaRedex`, and ONE `conv` node by `betaRedexConvAt` moves it to `piX`. This one
    `conv` above the `app` is what makes `invᵢ.hc` a one-link chain. -/
def hfA2 : HasTyT emptyEnv 0 ΓA2 (.app (.bvar 0) piX) piX :=
  .conv ΓA2 _ betaRedex piX (.imax (.succ .zero) (.succ .zero))
    (.app ΓA2 (.bvar 0) piX sX betaRedex a2_fTy (piXTy ΓA2))
    (betaRedexConvAt ΓA2)

abbrev RA2 : List (Jd emptyEnv 0) := [.ty hfA2]

def hsubA2 : ∃ r ∈ RA2, SubEq (.ty hfA2) r := ⟨.ty hfA2, .head _, .inl rfl⟩

/-- the inversion record `om_etaK_annot_piChain` builds (both sides). -/
def a2_inv : EvInvApp RA2 ΓA2 (.bvar 0) piX piX :=
  (EvTy.lit hfA2 hsubA2).invApp rfl rfl

/-- `c_fn`: U's alignment chain on the two inverted function typings. -/
def a2_cfn (U : ∀ R : List (Jd emptyEnv 0), UProc R) :
    EvTc RA2 ΓA2 (.pi a2_inv.A a2_inv.B) (.pi a2_inv.A a2_inv.B) :=
  U RA2 a2_inv.hf a2_inv.hf

/-- the chain's actual substituent typing — the `ha_cast` of
    `om_etaK_annot_piChain` (RcicEtaKDecide.lean), the same expression. -/
def a2_haCast : EvTy RA2 (substRemove piX 0 (.assumption a2_inv.A :: ΓA2))
    (lift 0 0 piX) (lift 0 0 a2_inv.A) :=
  EvTy.cast rfl (by simp [lift_zero]) (by simp [lift_zero]) a2_inv.ha

/-- the A.2 annotation chain through the actual call site, on the conv-carrying
    typing — `EvTc RA2 ΓA2 piX piX`, flattened to three links with `betaRedex`
    middles. -/
def chainA2 (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) : EvTc RA2 ΓA2 piX piX :=
  om_etaK_annot_piChain U X rfl hfA2 hsubA2 hfA2 hsubA2

/-- `Q`: the producer leaves of the substituted codomain chain. -/
def a2_Q (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) : List (Jd emptyEnv 0) :=
  (X RA2 (a2_cfn U)).2.leaves

/-- the β atom: the conversion the `conv` node cites. -/
abbrev a2_b : Jd emptyEnv 0 := .cv (betaRedexConvAt ΓA2)

/-- the kept atom: the Π typing — the β conversion's third typing field. -/
abbrev a2_k : Jd emptyEnv 0 := .ty (piXTy ΓA2)

/-- the function atom: the bvar typing returned by the original `invApp`. -/
abbrev a2_f : Jd emptyEnv 0 := .ty a2_fTy

/-! ### payment evidence (S0 §5) -/

/-- the inverted argument typing is exactly the kept Π typing atom. -/
theorem a2_inv_ha_leaves : a2_inv.ha.leaves = [a2_k] := rfl

/-- the inverted function typing is exactly the bvar atom. -/
theorem a2_inv_hf_leaves : a2_inv.hf.leaves = [a2_f] := rfl

/-- the chain's actual substituent typing keeps exactly `[k]`. -/
theorem a2_kept_leaves : a2_haCast.leaves = [a2_k] := by
  unfold a2_haCast
  rw [EvTy.cast_leaves]
  exact a2_inv_ha_leaves

/-- `k` is an immediate original child of `b`: β's children are
    `[.ty hA, .ty hbody, .ty harg]` and the third IS `piXTy ΓA2`. -/
theorem a2_kept_original_child : Child a2_k a2_b := by
  show a2_k ∈ a2_b.children
  exact .tail _ (.tail _ (.head _))

/-- β is `1 + 1 + 1 + 3 = 6` judgment nodes (sort, bvar, and the weight-3
    Π typing). -/
theorem a2_b_wt : a2_b.wt = 6 := rfl

/-- the Π typing is `1 + 1 + 1 = 3` nodes. -/
theorem a2_k_wt : a2_k.wt = 3 := rfl

/-- the bvar typing is one node. -/
theorem a2_f_wt : a2_f.wt = 1 := rfl

/-- the kept atom is strictly lighter than the β atom that pays for it. -/
theorem a2_k_wt_lt_b : a2_k.wt < a2_b.wt := child_wt_lt a2_kept_original_child

/-- the exact original input layout: `L = [b] ++ Q ++ [k] ++ [b]` — the two
    inverted conversions contribute one β atom each, the `subst0` link
    contributes `Q` (the X chain's leaves) followed by the kept `[k]`. -/
theorem a2_layout (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    (chainA2 U X).leaves = [a2_b] ++ a2_Q U X ++ [a2_k] ++ [a2_b] := by
  rw [show (chainA2 U X).leaves = (([a2_b] ++ (a2_Q U X ++ [a2_k])) ++ [a2_b])
      from rfl]
  simp only [List.append_assoc]

/-! ### the JOIN shape, on the landed predicates -/

/-- the flattened A.2 chain has THREE links: `ofCv u (symm (lit betaRedexConvAt))`,
    the `subst0` instantiation link, and `ofCv u (lit betaRedexConvAt)`. -/
theorem a2_three_links (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    (flattenTc (chainA2 U X)).length = 3 := rfl

/-- `splitPi`'s prefix is the WHOLE chain: both middles are `betaRedex`, not Π —
    the three links form ONE segment. -/
theorem a2_one_segment (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    ((flattenTc (chainA2 U X)).splitPi rfl).2.2.1.length = 3 := rfl

/-- the landed `Flat.segAdm` refuses the segment through its multi-link arm:
    the substituted link sits inside (`bLink` refuses `subst0`). -/
theorem a2_segAdm_false (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    ((flattenTc (chainA2 U X)).splitPi rfl).2.2.1.segAdm = false := rfl

/-- the landed admission refuses the chain: W-X-SUBST today. -/
theorem a2_xAdm_false (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    xAdm (chainA2 U X) = false := rfl

/-- the W-fragment admission refuses it too. -/
theorem a2_xAdmW_false (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    xAdmW (chainA2 U X) = false := rfl

/-- the per-link `bLinkW` markers of a flat chain: `true` exactly on the
    W-valley links. -/
def Flat.bLinkWs {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx} :
    {A B : Expr Nat} → Flat R Γ A B → List Bool
  | _, _, .nil _ => []
  | _, _, .cons l _ rest => bLinkW l :: rest.bLinkWs

/-- precisely the substitution link is the non-W one: the JOIN's shape,
    exactly. -/
theorem a2_bLinkWs (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    (flattenTc (chainA2 U X)).bLinkWs = [true, false, true] := rfl

/-! ### control: no conv node → `hc = refl` → the JOIN disappears -/

/-- the control context: `f : Π y : sX. piX`. -/
abbrev ΓC : LCtx := [.assumption (.pi sX piX)]

/-- the control's function variable typing. -/
def c_fTy : HasTyT emptyEnv 0 ΓC (.bvar 0) (.pi sX piX) :=
  .bvar ΓC 0 _ rfl

/-- `f piX : piX` by `app` alone: `instantiate0 piX piX = piX` is already Π — no
    `conv` node, so `invᵢ.hc = .refl` and both `hc`s flatten to `nil`. -/
def hfC : HasTyT emptyEnv 0 ΓC (.app (.bvar 0) piX) piX :=
  .app ΓC (.bvar 0) piX sX piX c_fTy (piXTy ΓC)

abbrev RC : List (Jd emptyEnv 0) := [.ty hfC]

def hsubC : ∃ r ∈ RC, SubEq (.ty hfC) r := ⟨.ty hfC, .head _, .inl rfl⟩

/-- the control chain through the same actual call site. -/
def chainC (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) : EvTc RC ΓC piX piX :=
  om_etaK_annot_piChain U X rfl hfC hsubC hfC hsubC

/-- CONTROL: the control chain flattens to the single `subst0` link — the JOIN
    disappears exactly when the inverted typing has no conv node. -/
theorem pin_C_one_link (U : ∀ R : List (Jd emptyEnv 0), UProc R)
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) :
    (flattenTc (chainC U X)).length = 1 := rfl

end A2JoinFixture

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.piXTy
#print axioms Rcic.Declarative.F8Measure.betaRedexConvAt
#print axioms Rcic.Declarative.F8Measure.ΓA2
#print axioms Rcic.Declarative.F8Measure.a2_fTy
#print axioms Rcic.Declarative.F8Measure.hfA2
#print axioms Rcic.Declarative.F8Measure.RA2
#print axioms Rcic.Declarative.F8Measure.hsubA2
#print axioms Rcic.Declarative.F8Measure.a2_inv
#print axioms Rcic.Declarative.F8Measure.a2_cfn
#print axioms Rcic.Declarative.F8Measure.a2_haCast
#print axioms Rcic.Declarative.F8Measure.chainA2
#print axioms Rcic.Declarative.F8Measure.a2_Q
#print axioms Rcic.Declarative.F8Measure.a2_b
#print axioms Rcic.Declarative.F8Measure.a2_k
#print axioms Rcic.Declarative.F8Measure.a2_f
#print axioms Rcic.Declarative.F8Measure.Flat.bLinkWs
#print axioms Rcic.Declarative.F8Measure.a2_inv_ha_leaves
#print axioms Rcic.Declarative.F8Measure.a2_inv_hf_leaves
#print axioms Rcic.Declarative.F8Measure.a2_kept_leaves
#print axioms Rcic.Declarative.F8Measure.a2_kept_original_child
#print axioms Rcic.Declarative.F8Measure.a2_b_wt
#print axioms Rcic.Declarative.F8Measure.a2_k_wt
#print axioms Rcic.Declarative.F8Measure.a2_f_wt
#print axioms Rcic.Declarative.F8Measure.a2_k_wt_lt_b
#print axioms Rcic.Declarative.F8Measure.a2_layout
#print axioms Rcic.Declarative.F8Measure.a2_three_links
#print axioms Rcic.Declarative.F8Measure.a2_one_segment
#print axioms Rcic.Declarative.F8Measure.a2_segAdm_false
#print axioms Rcic.Declarative.F8Measure.a2_xAdm_false
#print axioms Rcic.Declarative.F8Measure.a2_xAdmW_false
#print axioms Rcic.Declarative.F8Measure.a2_bLinkWs
#print axioms Rcic.Declarative.F8Measure.ΓC
#print axioms Rcic.Declarative.F8Measure.c_fTy
#print axioms Rcic.Declarative.F8Measure.hfC
#print axioms Rcic.Declarative.F8Measure.RC
#print axioms Rcic.Declarative.F8Measure.hsubC
#print axioms Rcic.Declarative.F8Measure.chainC
#print axioms Rcic.Declarative.F8Measure.pin_C_one_link
