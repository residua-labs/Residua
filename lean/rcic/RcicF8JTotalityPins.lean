import rcic.RcicF8JTotalityUX
import rcic.RcicF8UAppDemandPins
import rcic.RcicF8JTrans
import rcic.RcicF8SepAllViaSPins

/-!
# JT-1 controls on the actual supplied-chain U→X path

ChatGPT designed the controls in `S0_J_TOTALITY.md` and
`S0_UX_REENTRY_DEMAND.md` §4. The input here is the exact result of the
original `suppliedChain`, observed by `actualAwait`, with its original
literal certificates. The two-link Stratum-B segment reaches its first
literal before J answers. The same occurrence remains demanded when J
refuses. The positive control uses the actual empty Stratum-A result.

The weak mutant reads only J calls retained by the actual successful X
output. The exact check keeps the independently proved demanded occurrence;
the filter mutant drops that occurrence using J5a's unsupported fragment.
The checks are fixture observations, not global availability theorems.

No closed `SepAll emptyEnv 0` witness is asserted. The weak census
runs the landed `SuppliersViaS.xValleyS?` on `SuppliersViaS.declining`
of `SepAllViaSPins.sep` (`SepAllViaS emptyEnv 0`), with `EnvWfT.empty`
and no `SepAll` premise. Kernel `#reduce` of that census is closed.
The demand and fragment checks also use `#eval`.
Availability, safety and step certification remain separate.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure.JTotality.Pins

open Rcic.Syn
open UAppDemandPins

/-- The direct original U-app invocation, without any X answer premise. -/
def root : UAppRoot emptyEnv 0 :=
  ⟨roots, ctx, .app (.bvar 0) PEqTProofFront.P, .sort .zero, .sort .zero,
    cl, ss, left, right⟩

/-- Independent evidence about the actual supplier result. -/
def actualAdmission : EntryForActualChain root actualAwait :=
  ⟨ctxWf, actual_xAdmW⟩

def actualEntry : XEntryW emptyEnv 0 := actualAdmission.entry

theorem actualEntry_chain : actualEntry.c = cActual := rfl

/-- The first literal selected by the actual two-link segment. It is the
whole symmetric β literal, retaining its original context and certificate. -/
def qBeta : JRequestW actualEntry :=
  JRequestW.at actualEntry [.segmentHere, .linkHere, .ofCv]
    (.id ctx) betaToRedex betaFirstCert

theorem qBeta_source : qBeta.h = betaToRedex := rfl

theorem qBeta_path : qBeta.path = [.segmentHere, .linkHere, .ofCv] := rfl

private def fixtureSegments : Segs roots ctx piX piX :=
  .cons (.cons (.ofCv uX (.lit betaToRedex betaFirstCert)) rfl
    (.cons (.ofCv uX (.lit betaInCtx betaSecondCert)) rfl (.nil piX))) rfl (.nil piX)

private theorem actual_segments :
    (flattenTc actualEntry.c).segment rfl = fixtureSegments := rfl

/-- Demand follows the actual flatten/segment result, without J or X. -/
theorem actual_need : NeedW actualEntry qBeta := by
  change NeedSegsW actualEntry ((flattenTc actualEntry.c).segment rfl) [] qBeta
  rw [actual_segments]
  exact .head (.multiple (.head (.ofCv (NeedCvW.lit (C := actualEntry) betaToRedex betaFirstCert
    (.id ctx) [.segmentHere, .linkHere, .ofCv]))))

/-- The second original X→J occurrence is a whole raw β literal. It has
its own X address; it is not the recursive β child of the first symm
literal. Structural demand does not claim this later call executes after
the first call refuses. -/
def qRawBeta : JRequestW actualEntry :=
  JRequestW.at actualEntry [.segmentHere, .linkNext, .linkHere, .ofCv]
    (.id ctx) betaInCtx betaSecondCert

theorem actual_raw_beta_need : NeedW actualEntry qRawBeta := by
  change NeedSegsW actualEntry ((flattenTc actualEntry.c).segment rfl) [] qRawBeta
  rw [actual_segments]
  exact .head (.multiple (.tail (.head (.ofCv (NeedCvW.lit (C := actualEntry) betaInCtx betaSecondCert
    (.id ctx) [.segmentHere, .linkNext, .linkHere, .ofCv])))))

theorem actual_raw_beta_row : NeedRowW actualEntry qRawBeta .beta :=
  ⟨actual_raw_beta_need, rfl⟩

theorem original_occurrences_distinct : qBeta.path ≠ qRawBeta.path := by
  decide

/-- The same original β evidence also occurs inside the first symm
literal. This address is a child obligation, with no claim of another
issued X→J call. -/
def firstBetaChild : JChildObligationW actualEntry qBeta :=
  ⟨actual_need, ⟨qBeta.path, [.symm]⟩, rfl, ctx, betaRedex, piX, sX,
    betaInCtx, .child (.symm betaInCtx)⟩

theorem child_and_later_request_same_source : firstBetaChild.h = qRawBeta.h := rfl

theorem child_and_later_request_distinct_address :
    firstBetaChild.address.xOccurrence ≠ qRawBeta.path :=
  original_occurrences_distinct

private def NeedLinkRootView (C : XEntryW E n) :
    {Γ₀ : LCtx} → {A B : Expr Nat} → EvTc C.R Γ₀ A B →
    Wk Γ₀ C.Γ → Path → JRequestW C → Prop
  | _, _, _, .ofCv _ c, ρ, p, q => NeedCvW C c ρ (p ++ [.ofCv]) q
  | _, _, _, _, _, _, _ => True

private theorem needLink_rootView {C : XEntryW E n} {Γ₀ A B}
    {l : EvTc C.R Γ₀ A B} {ρ p q} (h : NeedLinkW C l ρ p q) :
    NeedLinkRootView C l ρ p q := by
  cases h with
  | ofCv h => exact h
  | wk _ => trivial

private def NeedLiteralRootView (C : XEntryW E n) :
    {Γ₀ : LCtx} → {a b T : Expr Nat} → EvCv C.R Γ₀ a b T →
    Wk Γ₀ C.Γ → Path → JRequestW C → Prop
  | _, _, _, _, .lit h hs, ρ, p, q => q = JRequestW.at C p ρ h hs
  | _, _, _, _, _, _, _, _ => True

private theorem needLiteral_rootView {C : XEntryW E n} {Γ₀ a b T}
    {c : EvCv C.R Γ₀ a b T} {ρ p q} (h : NeedCvW C c ρ p q) :
    NeedLiteralRootView C c ρ p q := by
  cases h with
  | lit => rfl
  | symm _ => trivial
  | left _ => trivial
  | right _ => trivial
  | tyConv _ => trivial
  | rety _ => trivial
  | wk _ => trivial

/-- Exhaustive structural classification of the actual supplied segment.
There are two original X occurrences even when only the first is reached. -/
theorem actual_need_iff (q : JRequestW actualEntry) :
    NeedW actualEntry q ↔ q = qBeta ∨ q = qRawBeta := by
  constructor
  · intro h
    change NeedSegsW actualEntry ((flattenTc actualEntry.c).segment rfl) [] q at h
    rw [actual_segments] at h
    cases h with
    | head h =>
      cases h with
      | multiple h =>
        cases h with
        | head h =>
          exact Or.inl (needLiteral_rootView (needLink_rootView h))
        | tail h =>
          cases h with
          | head h =>
            exact Or.inr (needLiteral_rootView (needLink_rootView h))
          | tail h => cases h
    | tail h => cases h
  · rintro (rfl | rfl)
    · exact actual_need
    · exact actual_raw_beta_need

/-- Only enters and the pending J call occur before this first answer. -/
def πBeta : PrefixW actualEntry :=
  [.enter [], .enter [.segmentHere], .enter [.segmentHere],
    .enter [.segmentHere, .linkHere], .awaitJ qBeta]

theorem actual_issued (X : SuppliersVia emptyEnv 0) :
    IssuedBeforeAnswer X actualEntry πBeta qBeta := by
  change IssuedSegsW X actualEntry ((flattenTc actualEntry.c).segment rfl) [] πBeta qBeta
  rw [actual_segments]
  exact .head (.multiple (.head (.ofCv (IssuedCvW.lit (X := X) (C := actualEntry) betaToRedex betaFirstCert
    (.id ctx) [.segmentHere, .linkHere, .ofCv]))))

def qUX : UXRequestW root :=
  ⟨actualAwait, actual_pre, actualAdmission, qBeta⟩

theorem actual_needUX : NeedUX root (.uApp [] actualAwait qBeta.path) qUX :=
  .uApp qUX .root actual_need

theorem actual_UX_issued (X : SuppliersVia emptyEnv 0) :
    NeedUX root (.uApp [] actualAwait qBeta.path) qUX ∧
      IssuedBeforeAnswer X actualEntry πBeta qBeta :=
  issued_UX_J_before_J_answer qUX .root X πBeta (actual_issued X)

/-- The executed always-refusing J mutant. -/
def Jnone : ∀ R : List (Jd emptyEnv 0), JProcViaP R :=
  fun _ {_ _ _ _} _ _ _ => none

theorem qBeta_refuses : qBeta.answer Jnone = none := rfl

theorem actual_refusing_prefix (hsep : SepAll emptyEnv 0) :
    NeedW actualEntry qBeta ∧
      qBeta.literalWorker (SuppliersVia.declining hsep) = none :=
  refusing_prefix_keeps_demand (actual_issued (SuppliersVia.declining hsep)) rfl

/-! Stratum A: the actual original supplier result has no J occurrence. -/

def stratumARoot : UAppRoot emptyEnv 0 := { root with r := left }

def stratumAAdmission : EntryForActualChain stratumARoot stratumAAwait :=
  ⟨ctxWf, stratumA_xAdmW⟩

def stratumAEntry : XEntryW emptyEnv 0 := stratumAAdmission.entry

theorem stratumAEntry_chain : stratumAEntry.c = cStratumA := rfl

theorem stratumA_no_demand (e : EntryForActualChain stratumARoot stratumAAwait)
    (q : JRequestW e.entry) : ¬ NeedW e.entry q := by
  intro h
  change NeedSegsW e.entry (.nil piX) [] q at h
  cases h

theorem stratumA_no_phantom_UX (q : UXRequestW stratumARoot)
    (p : UXPath stratumARoot) : ¬ NeedUX stratumARoot p q := by
  intro h
  cases h with
  | uApp q hr hn =>
      have hp : q.await = stratumAAwait :=
        Option.some.inj (q.observed.symm.trans stratumA_pre)
      cases q with
      | mk await observed admission request =>
          dsimp only at hp
          cases hp
          exact stratumA_no_demand admission request hn

/-! Executed fixture census of both original literal occurrences. Its
soundness and completeness proofs are independent of suppliers. -/

def demanded : List (JRequestW actualEntry) := [qBeta, qRawBeta]

theorem demanded_complete (q : JRequestW actualEntry) :
    q ∈ demanded ↔ NeedW actualEntry q := by
  rw [actual_need_iff]
  simp only [demanded, List.mem_cons, List.not_mem_nil, or_false]

theorem demanded_sound (q : JRequestW actualEntry) (hq : q ∈ demanded) :
    NeedW actualEntry q := by
  have h : q = qBeta ∨ q = qRawBeta := by
    simpa only [demanded, List.mem_cons, List.not_mem_nil, or_false] using hq
  rcases h with h | h
  · subst q; exact actual_need
  · subst q; exact actual_raw_beta_need

/-- Only successful original X outputs contribute their retained J census.
The worker is the landed ViaS route. `SepAllViaSPins.sep` inhabits
`SepAllViaS emptyEnv 0`; `toVia` is not used, because it puts `SepAll` back. -/
def successfulOutputJCalls : List (Jd emptyEnv 0) :=
  match SuppliersViaS.xValleyS?
      (SuppliersViaS.declining SepAllViaSPins.sep)
      EnvWfT.empty (.ofWf actualEntry.hΓ)
      actualEntry.c actualEntry.hadm with
  | none => []
  | some out => out.2.2.1

/-- For Jnone every call is unavailable, but the weak output-only census
is empty precisely because the actual X worker refused. -/
def weakComplete : Bool :=
  successfulOutputJCalls.all (fun _ => false)

def exactComplete : Bool := demanded.all (fun q => (q.answer Jnone).isSome)

/-- Total availability over the independently specified demand relation.
The finite check above enumerates precisely this fixture's demand. -/
def ExactComplete {E : ResolvedEnv} {n : Nat} (C : XEntryW E n)
    (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  ∀ q : JRequestW C, NeedW C q → (q.answer J).isSome = true

/-- The defective universal check: unsupported demand has been deleted
from the quantified domain. Its finite representative is `filterComplete`.
This definition is used only as an executed negative control. -/
def FilteredComplete {E : ResolvedEnv} {n : Nat} (C : XEntryW E n)
    (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  ∀ q : JRequestW C, NeedW C q → J5a.fragment q.h = true →
    (q.answer J).isSome = true

theorem not_ExactComplete_actualEntry : ¬ ExactComplete actualEntry Jnone := by
  intro h
  have hq := h qBeta actual_need
  rw [qBeta_refuses] at hq
  cases hq

def filterComplete : Bool :=
  (demanded.filter (fun q => J5a.fragment q.h)).all
    (fun q => (q.answer Jnone).isSome)

/-- Raw-row classification precedes support testing. In particular β
remains in the exact domain even though the current J5a dispatcher refuses
it. Deleting unsupported demand from the whole fixture census is the
global mutant, not a new supplier or an altered traversal. -/
def demandRows : List RawConstructor := demanded.map (fun q => rawConstructor q.h)

theorem actual_demand_rows : demandRows = [.symm, .beta] := rfl

theorem raw_beta_is_unsupported : J5a.fragment qRawBeta.h = false := rfl

theorem actual_successful_census_empty : successfulOutputJCalls = [] := rfl

theorem weak_wrongly_accepts : weakComplete = true := rfl

theorem exact_refuses : exactComplete = false := rfl

theorem qBeta_outside_J5a : J5a.fragment qBeta.h = false := rfl

theorem filter_drops_demand : demanded.filter (fun q => J5a.fragment q.h) = [] := rfl

theorem unsupported_row_is_deleted :
    qRawBeta ∉ demanded.filter (fun q => J5a.fragment q.h) := by
  rw [filter_drops_demand]
  simp only [List.not_mem_nil, not_false_eq_true]

theorem filter_wrongly_accepts : filterComplete = true := rfl

theorem filtered_universal_wrongly_accepts : FilteredComplete actualEntry Jnone := by
  intro q hq hs
  rcases (actual_need_iff q).mp hq with rfl | rfl <;>
    change false = true at hs <;> cases hs

theorem global_unsupported_demand_deletion :
    FilteredComplete actualEntry Jnone ∧ ¬ ExactComplete actualEntry Jnone ∧
      NeedRowW actualEntry qRawBeta .beta ∧
      filterComplete = true ∧ exactComplete = false :=
  ⟨filtered_universal_wrongly_accepts, not_ExactComplete_actualEntry,
    actual_raw_beta_row, rfl, rfl⟩

/-- Exact coverage rejects the actual demanded Jnone request while both
the output-only and fragment-filter mutants accept it. -/
theorem executed_mutant_separation :
    weakComplete = true ∧ exactComplete = false ∧ filterComplete = true :=
  ⟨rfl, rfl, rfl⟩

-- Closed execution: census length 0, weak accepts, exact refuses.
#reduce successfulOutputJCalls.length
#reduce weakComplete
#reduce exactComplete
#reduce filterComplete

-- These checks contain no supplier safety bundle and are closed.
#eval exactComplete
#eval filterComplete
#eval J5a.fragment qBeta.h
#eval demandRows
#eval J5a.fragment qRawBeta.h

end Rcic.Declarative.F8Measure.JTotality.Pins

#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.actual_need
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.actual_issued
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.actual_needUX
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.stratumA_no_phantom_UX
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.not_ExactComplete_actualEntry
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.executed_mutant_separation
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.actual_raw_beta_row
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.unsupported_row_is_deleted
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.actual_need_iff
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.global_unsupported_demand_deletion
