import Lean
import rcic.RcicF8OM23
import rcic.RcicOriginSubstPins
import rcic.RcicProofOccurrences

/-!
B5 — the admissible-branch O-M2 instance (S2 §3 and §5; cc order on
#6855 puts this before B3b).

Every prior O-M2 instance (`om2_peak`, `om2_conv`, `om2_iotaSpine`,
`peakTile`) puts only `SiteStatus.answered` into the status map — the
answer is DATA out of #6493's store. This module gives the first
non-vacuity witness for the `admissible` branch, from the real A1
producer `proof_root_subst0` (`RcicOriginSubst`) at the A1 pin fixture
(`RcicOriginSubstPins`).

The emitted `.peq` step `a1Step k` goes out WITHOUT its answer: its only
occurrence is the root `.proof` leaf (`RawOcc` contributes `PUnit`), and
both `Side`s get `.admissible` statuses whose `pos`/`proofTy` are LAZY
`EvTy.esub` re-derivations at `j = 0` — the substituted request is
reconstructed from the PRE-substitution literal typings
(`xAtIndex`/`yAtIndex` for the position at the body index, `xTy`/`yTy`
for the proposition), each of which is a strict `SubOf` sub-derivation of
one of the two removed outer inputs `.pr (betaInput k)` /
`.pr (structuralInput k)`. The `Child` chains are written out
explicitly.

O-M2 then holds with `X` = the two inputs: every literal leaf of the
request's provenance is strictly below a removed atom — the substituted
request is DM-admissible against the original inputs even though its
materialized size (896 vs the outer peak's 1827 in #6493's runtime
observation) is large. `a1Subst_edge` gives the O-M3(b) edge reading:
the left request's leaves are DM-below the removed atoms.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn
open Rcic.Declarative.F8Occurrences
open F8PiSourceOrigin PEqTProofFront F8OriginSubst F8OriginSubst.Pins

private def a1cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def a1si : EnvMembersSubstStable emptyEnv :=
  envWfT_subst_inst EnvWfT.empty

/-- the A1 same-substitution root at the pin fixture (`k` general): the
    emitted `.peq` step, going out WITHOUT its answer. -/
def a1Step (k : Nat) :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 []
      (instantiate0 p x) (instantiate0 p y) (instantiate0 p bodyIndex) :=
  proof_root_subst0 a1cl a1si (P_ty binder) (P_ty binder)
    xTy yTy xAtIndex yAtIndex (paddedN k)

/-- the removed atoms: the A1 peak's two outer inputs. -/
def a1R (k : Nat) : List (Jd emptyEnv 0) :=
  [.pr (betaInput k), .pr (structuralInput k)]

/-! ### `Child` chains — every literal used by the lazy requests is a
field of `betaInput k` or `structuralInput k`. -/

private theorem a1Child_Pty (k : Nat) :
    Child (.ty (P_ty [])) (.pr (betaInput k)) := .head _

private theorem a1Child_xAtIndex_refl :
    Child (.ty xAtIndex) (.pr (.refl binder x bodyIndex xAtIndex)) :=
  .head _

private theorem a1Child_refl_beta (k : Nat) :
    Child (.pr (.refl binder x bodyIndex xAtIndex)) (.pr (betaInput k)) :=
  .tail _ (.tail _ (.tail _ (.head _)))

private theorem a1Child_paddedN_refl (k : Nat) :
    Child (.ty (paddedN k)) (.pr (.refl [] p P (paddedN k))) := .head _

private theorem a1Child_reflP_beta (k : Nat) :
    Child (.pr (.refl [] p P (paddedN k))) (.pr (betaInput k)) :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

private theorem a1Child_xTy_xAtIndex :
    Child (.ty xTy) (.ty xAtIndex) := .head _

private theorem a1Child_yAtIndex_lam :
    Child (.ty yAtIndex)
      (.ty (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex)) :=
  .tail _ (.head _)

private theorem a1Child_lam_app :
    Child (.ty (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex))
      (.ty (.app [] (.lam P y) q P bodyIndex
        (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex) (q_ty []))) :=
  .head _

private theorem a1Child_app_conv :
    Child (.ty (.app [] (.lam P y) q P bodyIndex
        (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex) (q_ty [])))
      (.ty (.conv [] target (instantiate0 q bodyIndex) commonIndex .zero
        (.app [] (.lam P y) q P bodyIndex
          (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex) (q_ty []))
        (.symm _ _ _ _ indexConv))) := .head _

private theorem a1Child_conv_peq (k : Nat) :
    Child (.ty (.conv [] target (instantiate0 q bodyIndex) commonIndex .zero
        (.app [] (.lam P y) q P bodyIndex
          (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex) (q_ty []))
        (.symm _ _ _ _ indexConv)))
      (.pr (structuralInput k)) := .tail _ (.tail _ (.head _))

private theorem a1Child_yTy_yAtIndex :
    Child (.ty yTy) (.ty yAtIndex) := .head _

/-! ### the strict `SubOf` chains into the two removed atoms. -/

private theorem a1Sub_Pty (k : Nat) :
    SubOf (.ty (P_ty [])) (.pr (betaInput k)) :=
  .child (a1Child_Pty k)

private theorem a1Sub_xAtIndex (k : Nat) :
    SubOf (.ty xAtIndex) (.pr (betaInput k)) :=
  .trans (.child a1Child_xAtIndex_refl) (.child (a1Child_refl_beta k))

private theorem a1Sub_paddedN (k : Nat) :
    SubOf (.ty (paddedN k)) (.pr (betaInput k)) :=
  .trans (.child (a1Child_paddedN_refl k)) (.child (a1Child_reflP_beta k))

private theorem a1Sub_xTy (k : Nat) :
    SubOf (.ty xTy) (.pr (betaInput k)) :=
  .trans (.child a1Child_xTy_xAtIndex) (a1Sub_xAtIndex k)

private theorem a1Sub_yAtIndex (k : Nat) :
    SubOf (.ty yAtIndex) (.pr (structuralInput k)) :=
  .trans (.child a1Child_yAtIndex_lam)
    (.trans (.child a1Child_lam_app)
      (.trans (.child a1Child_app_conv) (.child (a1Child_conv_peq k))))

private theorem a1Sub_yTy (k : Nat) :
    SubOf (.ty yTy) (.pr (structuralInput k)) :=
  .trans (.child a1Child_yTy_yAtIndex) (a1Sub_yAtIndex k)

/-! ### the lazy statuses' literal certificates (`SubEq` into `a1R k`). -/

private def a1Cert_xAtIndex (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty xAtIndex) r :=
  ⟨.pr (betaInput k), .head _, .inr (a1Sub_xAtIndex k)⟩
private def a1Cert_paddedN (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty (paddedN k)) r :=
  ⟨.pr (betaInput k), .head _, .inr (a1Sub_paddedN k)⟩
private def a1Cert_Pty (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty (P_ty [])) r :=
  ⟨.pr (betaInput k), .head _, .inr (a1Sub_Pty k)⟩
private def a1Cert_xTy (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty xTy) r :=
  ⟨.pr (betaInput k), .head _, .inr (a1Sub_xTy k)⟩
private def a1Cert_yAtIndex (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty yAtIndex) r :=
  ⟨.pr (structuralInput k), .tail _ (.head _), .inr (a1Sub_yAtIndex k)⟩
private def a1Cert_yTy (k : Nat) :
    ∃ r ∈ a1R k, SubEq (.ty yTy) r :=
  ⟨.pr (structuralInput k), .tail _ (.head _), .inr (a1Sub_yTy k)⟩

/-! ### the lazy `esub` typings for the two request sides. Each is one
`esub` at `j = 0` over the PRE-substitution literal typing, with the
argument typing `paddedN k` and the binder sort typing `P_ty []`; the
`EvTy.cast` bridges `instantiate 0 (lift 0 0 v) e` to `instantiate0 v e`
(`lift_zero`), as `substTy0` does. -/

/-- left position typing at `instantiate0 p bodyIndex`: lazy `esub` over
    the pre-substitution `xAtIndex`. -/
private def a1PosL (k : Nat) :
    EvTy (a1R k) [] (instantiate0 p x) (instantiate0 p bodyIndex) :=
  EvTy.cast rfl rfl rfl
    (EvTy.esub (t := P) (v := p) 0 .zero
      (EvTy.lit xAtIndex (a1Cert_xAtIndex k)) rfl
      (EvTy.lit (paddedN k) (a1Cert_paddedN k))
      (EvTy.lit (P_ty []) (a1Cert_Pty k)))

/-- left proposition typing: the same lazy `esub` over `xTy` (`x : P`). -/
private def a1ProofL (k : Nat) :
    EvTy (a1R k) [] (instantiate0 p x) (instantiate0 p P) :=
  EvTy.cast rfl rfl rfl
    (EvTy.esub (t := P) (v := p) 0 .zero
      (EvTy.lit xTy (a1Cert_xTy k)) rfl
      (EvTy.lit (paddedN k) (a1Cert_paddedN k))
      (EvTy.lit (P_ty []) (a1Cert_Pty k)))

/-- right position typing: lazy `esub` over `yAtIndex`. -/
private def a1PosR (k : Nat) :
    EvTy (a1R k) [] (instantiate0 p y) (instantiate0 p bodyIndex) :=
  EvTy.cast rfl rfl rfl
    (EvTy.esub (t := P) (v := p) 0 .zero
      (EvTy.lit yAtIndex (a1Cert_yAtIndex k)) rfl
      (EvTy.lit (paddedN k) (a1Cert_paddedN k))
      (EvTy.lit (P_ty []) (a1Cert_Pty k)))

/-- right proposition typing: the same lazy `esub` over `yTy` (`y : P`). -/
private def a1ProofR (k : Nat) :
    EvTy (a1R k) [] (instantiate0 p y) (instantiate0 p P) :=
  EvTy.cast rfl rfl rfl
    (EvTy.esub (t := P) (v := p) 0 .zero
      (EvTy.lit yTy (a1Cert_yTy k)) rfl
      (EvTy.lit (paddedN k) (a1Cert_paddedN k))
      (EvTy.lit (P_ty []) (a1Cert_Pty k)))

/-- the A1 same-substitution root's status map with both sides
    ADMISSIBLE via lazy esub. -/
def a1SubstStatus (k : Nat) :
    (o : F8Occurrences.Occ (a1Step k)) → (side : F8Occurrences.Side) →
    SiteStatus (a1R k) (F8Occurrences.site (a1Step k) o) side
  | _, .left => .admissible commonIndex (a1PosL k) (a1ProofL k)
  | _, .right => .admissible commonIndex (a1PosR k) (a1ProofR k)

private theorem a1SubL (k : Nat) :
    ∀ ℓ ∈ (a1PosL k).leaves ++ (a1ProofL k).leaves,
      ∃ x ∈ a1R k, SubOf ℓ x := by
  intro ℓ hℓ
  simp only [a1PosL, a1ProofL, EvTy.cast_leaves, EvTy.leaves,
    List.nil_append, List.cons_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.pr (betaInput k), .head _, a1Sub_xAtIndex k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_paddedN k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_Pty k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_xTy k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_paddedN k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_Pty k⟩

private theorem a1SubR (k : Nat) :
    ∀ ℓ ∈ (a1PosR k).leaves ++ (a1ProofR k).leaves,
      ∃ x ∈ a1R k, SubOf ℓ x := by
  intro ℓ hℓ
  simp only [a1PosR, a1ProofR, EvTy.cast_leaves, EvTy.leaves,
    List.nil_append, List.cons_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.pr (structuralInput k), .tail _ (.head _), a1Sub_yAtIndex k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_paddedN k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_Pty k⟩
  · exact ⟨.pr (structuralInput k), .tail _ (.head _), a1Sub_yTy k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_paddedN k⟩
  · exact ⟨.pr (betaInput k), .head _, a1Sub_Pty k⟩

/-- O-M2 for the A1 status map: every admissible leaf is a strict
    sub-derivation of one of the two removed inputs. -/
theorem a1Subst_om2 (k : Nat) :
    OM2 [.pr (betaInput k), .pr (structuralInput k)] (a1Step k)
      (a1SubstStatus k) := by
  intro o side
  cases side with
  | left => exact a1SubL k
  | right => exact a1SubR k

/-- packaged: the admissible-branch non-vacuity witness. -/
def a1SubstTile (k : Nat) : DTile (a1R k) :=
  ⟨[.pr (betaInput k), .pr (structuralInput k)], a1Step k, a1SubstStatus k,
    a1Subst_om2 k⟩

/-- and the edge reading: the request's leaves are DM-below the removed
    inputs. -/
theorem a1Subst_edge (k : Nat) :
    OM3_edge [.pr (betaInput k), .pr (structuralInput k)]
      ((a1PosL k).leaves ++ (a1ProofL k).leaves) := by
  simpa only [List.append_nil] using
    om3_edge_of_strictLeaves
      (X := [.pr (betaInput k), .pr (structuralInput k)]) (Z := [])
      (L := (a1PosL k).leaves ++ (a1ProofL k).leaves)
      (by simp) (a1SubL k)

#print axioms Rcic.Declarative.F8Measure.a1Step
#print axioms Rcic.Declarative.F8Measure.a1R
#print axioms Rcic.Declarative.F8Measure.a1SubstStatus
#print axioms Rcic.Declarative.F8Measure.a1Subst_om2
#print axioms Rcic.Declarative.F8Measure.a1SubstTile
#print axioms Rcic.Declarative.F8Measure.a1Subst_edge
