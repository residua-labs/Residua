import Lean
import rcic.RcicF8OM1
import rcic.RcicProofOccurrences
import rcic.RcicPiSourceOriginCallsPins

/-!
# `RcicF8OM23` — piRow O-M2, the O-M3(b) edge predicate, §5 pins, contracts

O-M2 (S2 §3) on #6493's complete occurrence domain (`RcicProofOccurrences`):
at an emitted step, each proof-root occurrence and each side is either
ANSWERED (the answer is store data, `#6493`'s `AnsweredOrigins`) or
ADMISSIBLE (its request's position typing and the site's proof typing
carry provenance over `R`, strictly below the removed atoms). `OM2` is
the predicate; `statusOfAnswered`/`om2_of_answered` and the
`om2_peak`/`om2_conv`/`om2_iotaSpine` instances are the checkable part.

`OM3_edge` is the edge predicate of O-M3(b) (S2 §4) — a `DMStep` from the
callee's atom multiset to the caller's; `om3_edge_of_strictLeaves` is
`dm_of_strictLeaves` rewritten along `List.map_append`.

§5 accounting pins are kernel-checked at the padded fixture (k = 32):
the generated request's duplicated leaf IS DM-accepted at the producer
(`pin_416_producer_dm`), while re-asking it at the consumer is NOT
(`pin_416_consumer_negative`) — the answered store is necessary.

Finally the SEALED CONTRACT objects (statements, no proofs) that the
future D/J/X/U tiles must satisfy (cc ruling Q3/Q4): `XProc`/`XContract`,
`UContract`, `DTile` (a D/J tile admissible for the recursion carries its
O-M2 package as a field), `EdgeContract`, and `peakTile` as the
non-vacuity witness. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn
open Rcic.Declarative.F8Occurrences

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### O-M2 -/

/-- per occurrence and side: answered (the answer is DATA, #6493's
    store), or admissible (its request's position typing and the site's
    proof typing carry provenance over `R`). -/
inductive SiteStatus (R : List (Jd E n)) (s : ProofSite E n) (side : Side) :
    Type where
  | answered (r : SiteRequest s side) (ans : r.Answer)
  | admissible (index : Expr Nat) (pos : EvTy R s.context (s.term side) index)
      (proofTy : EvTy R s.context (s.term side) (s.proposition side))

/-- O-M2 at an emitted step `h'` of a D/J call that removed atoms `X`. -/
def OM2 (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (h' : ParRedT (PEqLeafT E n) E n Γ a b T)
    (st : (o : Occ h') → (side : Side) → SiteStatus R (site h' o) side) :
    Prop :=
  ∀ o side, match st o side with
    | .answered _ _ => True
    | .admissible _ pos proofTy =>
        ∀ ℓ ∈ pos.leaves ++ proofTy.leaves, ∃ x ∈ X, SubOf ℓ x

/-- #6493's answered store as a status map. -/
def statusOfAnswered {Γ : LCtx} {a b T : Expr Nat}
    {h' : ParRedT (PEqLeafT E n) E n Γ a b T} (reqs : Requests h')
    (ans : AnsweredOrigins h' reqs) :
    (o : Occ h') → (side : Side) → SiteStatus R (site h' o) side :=
  fun o side => .answered (reqs o side) (ans o side)

/-- O-M2 is immediate when every status is answered. -/
theorem om2_of_answered (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    {h' : ParRedT (PEqLeafT E n) E n Γ a b T} (reqs : Requests h')
    (ans : AnsweredOrigins h' reqs) :
    OM2 X h' (statusOfAnswered (R := R) reqs ans) :=
  fun _ _ => trivial

/-- O-M2 for the common-proposition peak: both side requests are answered
    by the original `hTP` (`peakAnswers`). -/
def om2_peak {Γ : LCtx} {a b c T P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h1 : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h2 : ParRedT (PEqLeafT E n) E n Γ a c T) (X : List (Jd E n)) :
    OM2 X (parRedT_propIndex_diamond_data hP hTP h1 h2).1
      (statusOfAnswered (R := R) (peakRequests hP hTP h1 h2)
        (peakAnswers hP hTP h1 h2)) :=
  om2_of_answered X (peakRequests hP hTP h1 h2) (peakAnswers hP hTP h1 h2)

/-- statuses carried through a `conv` wrapper. -/
def om2_conv (X : List (Jd E n)) {Γ : LCtx} {a b T U : Expr Nat}
    {h : ParRedT (PEqLeafT E n) E n Γ a b T} (hc : TyConvT E n Γ T U)
    (reqs : Requests h) (ans : AnsweredOrigins h reqs) :
    OM2 X (.conv Γ a b T U h hc)
      (statusOfAnswered (R := R) (requests_conv hc reqs)
        (answers_conv hc reqs ans)) :=
  om2_of_answered X (requests_conv hc reqs) (answers_conv hc reqs ans)

/-- statuses carried through an `iotaSpine` wrapper. -/
def om2_iotaSpine (X : List (Jd E n)) {Γ : LCtx} {a b c T : Expr Nat}
    {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hi : DerivedIotaU E b c) (hb : HasTyT E n Γ b T)
    (hc : HasTyT E n Γ c T) (reqs : Requests h)
    (ans : AnsweredOrigins h reqs) :
    OM2 X (.iotaSpine Γ a b c T h hi hb hc)
      (statusOfAnswered (R := R) (requests_iotaSpine hi hb hc reqs)
        (answers_iotaSpine hi hb hc reqs ans)) :=
  om2_of_answered X (requests_iotaSpine hi hb hc reqs)
    (answers_iotaSpine hi hb hc reqs ans)

/-! ### the O-M3(b) edge predicate -/

/-- a call edge is DM-admissible: the callee's atom multiset is a DM step
    below the caller's. -/
def OM3_edge (Rcaller Rcallee : List (Jd E n)) : Prop :=
  DMStep (Rcallee.map Jd.wt) (Rcaller.map Jd.wt)

/-- the strict-leaf condition gives an edge: every added literal leaf is
    strictly below a removed atom; kept atoms `Z` pass through. -/
theorem om3_edge_of_strictLeaves {X Z L : List (Jd E n)} (hX : X ≠ [])
    (h : ∀ ℓ ∈ L, ∃ x ∈ X, SubOf ℓ x) :
    OM3_edge (X ++ Z) (L ++ Z) := by
  unfold OM3_edge
  rw [List.map_append, List.map_append]
  exact dm_of_strictLeaves hX h

/-! ### sealed contracts (statements only; cc Q3/Q4) -/

/-- weak-row X on provenance: components as chains
    (`TypedRowsWf.piRow`'s `TyConvT` shape). -/
abbrev XProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B A' B' : Expr Nat}, EvTc R Γ (.pi A B) (.pi A' B') →
    EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B'

/-- every U-tile satisfies O-M1. -/
def UContract (U : ∀ R : List (Jd E n), UProc R) : Prop := ∀ R, OM1 (U R)

/-- every X-tile's component chains cite only sub-derivations of the
    input chain. -/
def XContract (X : ∀ R : List (Jd E n), XProc R) : Prop :=
  ∀ R {Γ : LCtx} {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')),
    ∀ ℓ ∈ (X R c).1.leaves ++ (X R c).2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'

/-- a D/J tile admissible for the recursion: inputs' removed atoms, the
    emitted step, its status map, and O-M2 as a FIELD — a producer without
    this package cannot enter (cc Q4). -/
structure DTile (R : List (Jd E n)) where
  X : List (Jd E n)
  {Γ : LCtx} {a b T : Expr Nat}
  step : ParRedT (PEqLeafT E n) E n Γ a b T
  status : (o : F8Occurrences.Occ step) → (side : F8Occurrences.Side) →
    SiteStatus R (F8Occurrences.site step o) side
  om2 : OM2 X step status

/-- every recorded call edge is DM-admissible. -/
def EdgeContract (calls : List (List (Jd E n) × List (Jd E n))) : Prop :=
  ∀ p ∈ calls, OM3_edge p.1 p.2

/-! ### §5 accounting pins (k = 32 padded fixture) -/

section Pins
open Rcic.Declarative.F8PiSourceOrigin.CallPins
    Rcic.Declarative.PEqTProofFront Rcic.Declarative.PEqLeafTPropPins

/-- `paddedBeta 32`'s reduct typing is an immediate premise — the last
    `.beta` child. -/
private theorem pin416_child :
    Child (.ty (paddedProof 32)) (.pr (paddedBeta 32)) :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

/-- the generated request's duplicated leaf is accepted by DM at the
    producer: caller = the removed `paddedBeta 32` atom plus the other
    producer inputs; callee = the generated leaf twice plus the same
    kept inputs. -/
theorem pin_416_producer_dm :
    OM3_edge
      ([.pr (paddedBeta 32)] ++
        [.ty (P_ty (E := emptyEnv) (n := 0) []),
          .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
          .pr (peq_branch (n := 0))])
      ([.ty (paddedProof 32), .ty (paddedProof 32)] ++
        [.ty (P_ty (E := emptyEnv) (n := 0) []),
          .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
          .pr (peq_branch (n := 0))]) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ => by
    rcases List.mem_cons.mp hℓ with rfl | hℓ
    · exact ⟨.pr (paddedBeta 32), .head _, .child pin416_child⟩
    · rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact ⟨.pr (paddedBeta 32), .head _, .child pin416_child⟩
      · exact absurd hℓ (List.not_mem_nil _))

/-- re-asking at the consumer is NOT DM-admissible: none of the second
    peak's literal material is strictly above the generated leaf. -/
theorem pin_416_consumer_negative :
    ¬ (∀ ℓ ∈ [.ty (paddedProof 32)],
        ∃ x ∈ ([.ty (paddedProof 32),
                .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
                .ty (P_ty (E := emptyEnv) (n := 0) []),
                .ty (p_ty (E := emptyEnv) (n := 0) [])] :
              List (Jd emptyEnv 0)),
          SubOf ℓ x) := by
  intro h
  obtain ⟨x, hx, hs⟩ := h _ (.head _)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact subOf_irrefl _ hs
  rcases List.mem_cons.mp hx with rfl | hx
  · have hw : Jd.wt (.tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P)) ≤
        Jd.wt (.ty (paddedProof 32)) := by decide
    have := subOf_wt_lt hs
    omega
  rcases List.mem_cons.mp hx with rfl | hx
  · have hw : Jd.wt (.ty (P_ty (E := emptyEnv) (n := 0) [])) ≤
        Jd.wt (.ty (paddedProof 32)) := by decide
    have := subOf_wt_lt hs
    omega
  rcases List.mem_cons.mp hx with rfl | hx
  · have hw : Jd.wt (.ty (p_ty (E := emptyEnv) (n := 0) [])) ≤
        Jd.wt (.ty (paddedProof 32)) := by decide
    have := subOf_wt_lt hs
    omega
  · exact absurd hx (List.not_mem_nil _)

/-- non-vacuity for `DTile`: the common-proposition peak packaged with
    its answered store. `R`/`X` are the producer's input atoms; all
    statuses are `answered`, so O-M2 holds vacuously of `X`. -/
def peakTile : DTile
    [.ty (P_ty (E := emptyEnv) (n := 0) []),
      .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
      .pr (beta_branch (n := 0)), .pr (peq_branch (n := 0))] where
  X := [.ty (P_ty (E := emptyEnv) (n := 0) []),
        .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
        .pr (beta_branch (n := 0)), .pr (peq_branch (n := 0))]
  step := emitted
  status := statusOfAnswered
    (peakRequests (P_ty []) (.refl [] P) beta_branch peq_branch)
    (peakAnswers (P_ty []) (.refl [] P) beta_branch peq_branch)
  om2 := om2_peak (P_ty []) (.refl [] P) beta_branch peq_branch
    [.ty (P_ty (E := emptyEnv) (n := 0) []),
      .tc (TyConvT.refl (E := emptyEnv) (n := 0) [] P),
      .pr (beta_branch (n := 0)), .pr (peq_branch (n := 0))]

end Pins

#print axioms SiteStatus
#print axioms OM2
#print axioms statusOfAnswered
#print axioms om2_of_answered
#print axioms om2_peak
#print axioms om2_conv
#print axioms om2_iotaSpine
#print axioms OM3_edge
#print axioms om3_edge_of_strictLeaves
#print axioms XProc
#print axioms UContract
#print axioms XContract
#print axioms DTile
#print axioms EdgeContract
#print axioms pin_416_producer_dm
#print axioms pin_416_consumer_negative
#print axioms peakTile

end Rcic.Declarative.F8Measure
