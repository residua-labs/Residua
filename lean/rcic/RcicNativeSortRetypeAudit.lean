import rcic.RcicNativeKProjection
import rcic.RcicSynBelowCProj
import rcic.RcicSynMSAP
import rcic.RcicHostPropScoped

/-!
# Native sort-retyping audit

`SortCoh` reads a native chain between two written sorts.  Producing that
chain from two typings of one term is a separate obligation.  The first
section proves the structural comparison on the fragment where its first
typing has no application node on the comparison spine.  The second typing
and every conversion proof remain unrestricted.  This isolates the exact
application branch without assuming Pi injectivity or a type-uniqueness
supplier.

The second section reads the stronger `CTS` field of the scoped syntactic
Below pack on a reflexive conversion.  This field already compares the
two sorting levels; its consumer needs neither `TableWF` nor `sortRow`.
The native enrichment witnesses' AssumpPref proofs are constructed from
the landed member-sort and let-walk preservation theorems.  Consequently,
the actual scoped pack supplies full `SortRetype` and zero-sort coherence,
leaving only the pack and Pi-valley producers in the Pi-injectivity
consumer.  No Below or CompleteC producer is constructed here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeSortRetypeAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The actual recursive comparison spine contains no application node.
Only children compared by the worker below are inspected.  In particular,
conversion evidence, lambda domains, and let values are unrestricted.
This is a property of a typing derivation, not a new typing judgment. -/
def ComparisonNoApp : {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → Prop
  | _, _, _, .sort _ _ => True
  | _, _, _, .bvar _ _ _ _ => True
  | _, _, _, .const _ _ _ _ _ _ _ => True
  | _, _, _, .pi _ _ _ _ _ hA hB => ComparisonNoApp hA ∧ ComparisonNoApp hB
  | _, _, _, .lam _ _ _ _ _ _ hb => ComparisonNoApp hb
  | _, _, _, .app _ _ _ _ _ _ _ => False
  | _, _, _, .letE _ _ _ _ _ _ _ _ hb => ComparisonNoApp hb
  | _, _, _, .lit _ _ _ he => ComparisonNoApp he
  | _, _, _, .conv _ _ _ _ _ he _ => ComparisonNoApp he

/-- An application that is itself typed at a sort in the empty native
environment: `(fun (_ : Sort 1) => Sort 0) (Sort 0)`. -/
def nativeSortApplication : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)

def nativeSortApplicationTyping :
    HasTyT emptyEnv 0 [] nativeSortApplication (.sort (.succ .zero)) :=
  .app [] _ _ (.sort (.succ .zero)) (.sort (.succ .zero))
    (.lam [] _ (.succ (.succ .zero)) _ _
      (.sort [] (.succ .zero)) (.sort _ .zero))
    (.sort [] .zero)

/-- The excluded case is a real sort-typing case, not an unreachable
constructor ruled out by the target's shape. -/
theorem nativeSortApplication_excluded :
    ¬ ComparisonNoApp nativeSortApplicationTyping :=
  fun h => h

/-- Native comparison with an unrestricted second typing.  `SortCoh` is
used only at the Pi rule, after the two strictly smaller recursive calls
have produced chains between written sorts.  The excluded application
branch is the only branch that would need codomain projection.

All recursive arguments are original `HasTyT` children.  Their measure is
`sizeOf h₁ + sizeOf h₂`; conversion stripping decreases one summand, and
the Pi, lambda, let and literal branches decrease both.  No inversion,
regularity or substitution output is ever used as a recursive subject. -/
noncomputable def typeConv_of_sortCoh_comparisonNoApp (hW : EnvWfT E)
    (sc : SortCoh E n) :
    {Γ : LCtx} → CtxWfT E n Γ → {e T₁ T₂ : Expr Nat} →
    (h₁ : HasTyT E n Γ e T₁) → (h₂ : HasTyT E n Γ e T₂) →
    ComparisonNoApp h₁ → TyConvT E n Γ T₁ T₂
  | _, hΓ, _, _, _, .conv _ _ _ _ u h hc, h₂, hn =>
      .trans _ _ _ _ (.of _ _ _ u (.symm _ _ _ _ hc))
        (typeConv_of_sortCoh_comparisonNoApp hW sc hΓ h h₂ hn)
  | _, hΓ, _, _, _, h₁, .conv _ _ _ _ u h hc, hn =>
      .trans _ _ _ _
        (typeConv_of_sortCoh_comparisonNoApp hW sc hΓ h₁ h hn)
        (.of _ _ _ u hc)
  | _, _, _, _, _, .sort _ _, .sort _ _, _ => .refl _ _
  | _, _, _, _, _, .bvar _ _ _ h, .bvar _ _ _ h', _ => by
      have hA := Option.some.inj (h.symm.trans h')
      subst hA
      exact .refl _ _
  | _, _, _, _, _, .const _ _ _ _ hres _ _, .const _ _ _ _ hres' _ _, _ => by
      have hm := Option.some.inj (hres.symm.trans hres')
      subst hm
      exact .refl _ _
  | Γ, hΓ, _, _, _, .pi _ A u₁ _ v₁ hA₁ hB₁,
      .pi _ _ u₂ _ v₂ hA₂ hB₂, hn =>
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u₁ hΓ hA₁
      let hcA := typeConv_of_sortCoh_comparisonNoApp hW sc hΓ hA₁ hA₂ hn.1
      let hcB := typeConv_of_sortCoh_comparisonNoApp hW sc hΓA hB₁ hB₂ hn.2
      .of Γ (.sort (.imax u₁ v₁)) (.sort (.imax u₂ v₂)) (.succ (.imax u₁ v₁))
        (.sorts Γ (.imax u₁ v₁) (.imax u₂ v₂)
          (eqN_imax_both (sc hΓ hcA) (sc hΓA hcB)))
  | Γ, hΓ, _, _, _, .lam _ A u₁ _ _ hA₁ hb₁,
      .lam _ _ _ _ _ _ hb₂, hn =>
      tyConvT_pi_codom hA₁
        (typeConv_of_sortCoh_comparisonNoApp hW sc
          (.assumption Γ A u₁ hΓ hA₁) hb₁ hb₂ hn)
  | _, _, _, _, _, .app _ _ _ _ _ _ _, .app _ _ _ _ _ _ _, hn =>
      False.elim hn
  | Γ, hΓ, _, _, _, .letE _ A u₁ value _ _ hA₁ hv₁ hb₁,
      .letE _ _ _ _ _ _ _ _ hb₂, hn =>
      tyConvT_substLet0 hW hv₁
        (typeConv_of_sortCoh_comparisonNoApp hW sc
          (.letBinding Γ A u₁ value hΓ hA₁ hv₁) hb₁ hb₂ hn)
  | _, hΓ, _, _, _, .lit _ _ _ he₁, .lit _ _ _ he₂, hn =>
      typeConv_of_sortCoh_comparisonNoApp hW sc hΓ he₁ he₂ hn
termination_by _ _ _ _ _ h₁ h₂ _ => sizeOf h₁ + sizeOf h₂
decreasing_by
  all_goals
    first
    | assumption
    | (simp_wf; assumption)
    | (simp <;> omega)
    | (simp_wf; simp <;> omega)

/-- Sort retyping on the certified comparison fragment.  The target is
the native `TyConvT` data consumed by chain homogenization, and the second
sorting has no fragment restriction. -/
noncomputable def sortRetype_of_comparisonNoApp (hW : EnvWfT E)
    (sc : SortCoh E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u v : Level}
    (h₁ : HasTyT E n Γ A (.sort u)) (h₂ : HasTyT E n Γ A (.sort v))
    (hn : ComparisonNoApp h₁) : TyConvT E n Γ (.sort u) (.sort v) :=
  typeConv_of_sortCoh_comparisonNoApp hW sc hΓ h₁ h₂ hn

/-- The same fragment gives equality of levels, including the zero-sort
case, by reading the chain that the preceding worker actually produced. -/
theorem sortLevels_of_comparisonNoApp (hW : EnvWfT E)
    (sc : SortCoh E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u v : Level}
    (h₁ : HasTyT E n Γ A (.sort u)) (h₂ : HasTyT E n Γ A (.sort v))
    (hn : ComparisonNoApp h₁) : eqN u v :=
  sc hΓ (sortRetype_of_comparisonNoApp hW sc hΓ h₁ h₂ hn)

/-- Under sortRow, the full data-valued retyping interface already entails
same-term sort uniqueness.  It cannot be treated as an automatic sortRow
coercion: the missing native chain is precisely its output. -/
theorem sortUniq_of_sortRetype_sortCoh (sr : SortRetype E n)
    (sc : SortCoh E n) : SortUniq E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ => sc hΓ (sr hΓ h₁ h₂)

/-! ## Reading CTS on a reflexive conversion -/

open Rcic.Syn

/-- A single reflexive CTS query compares two enriched sortings directly.
The exact raw bound for this public BelowScoped query is the successor of
`cvTyMeas Aw (refl D₂ D₂ D₂) D₁`.  Its native conclusion precedes every
level map and does not use TableWF. -/
theorem sortLevels_of_belowScoped_cts
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ) {A : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ A (.sort u)) (D₂ : TyP E n Γ A (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (Bel : BelowScoped Eₐ Aw tbl
      ((cvTyMeas Aw (CvP.refl E n Γ A (.sort v) D₂ D₂ D₂) D₁).1,
       (cvTyMeas Aw (CvP.refl E n Γ A (.sort v) D₂ D₂ D₂) D₁).2 + 1)) :
    eqN u v :=
  Bel.cts (CvP.refl E n Γ A (.sort v) D₂ D₂ D₂) D₁
    ⟨h₂, h₂, h₂⟩ h₁ S
    (lexDM_succ_snd (cvTyMeas Aw (CvP.refl E n Γ A (.sort v) D₂ D₂ D₂) D₁))

/-- The all-bounds scoped pack supplies exactly the public query above.
Its six fields are not identified with sortRow, and both AssumpPref
witnesses are still explicit. -/
theorem sortLevels_of_allBelowScoped_cts
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl)
    {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ) {A : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ A (.sort u)) (D₂ : TyP E n Γ A (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : eqN u v :=
  sortLevels_of_belowScoped_cts S D₁ D₂ h₁ h₂ (hBel _)

/-- The completed scoped pack supplies the same reflexive query.  The
two native-scope and AssumpPref witnesses remain explicit.  Internally,
`cts_of_completeC` calls the pack at this query's own canonical combined
measure and its successor bound; no raw/combined bound coercion occurs. -/
theorem sortLevels_of_completeC_cts
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat),
      CompleteCAt (Eₐ := Eₐ) (Aw := Aw) (tbl := tbl) QueryC.combBound p B)
    {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ) {A : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ A (.sort u)) (D₂ : TyP E n Γ A (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : eqN u v :=
  cts_of_completeC hcomp (CvP.refl E n Γ A (.sort v) D₂ D₂ D₂) D₁
    ⟨h₂, h₂, h₂⟩ h₁ S

/-- A concrete native retyping chain from a supplied scoped CTS query.
This is pointwise in the enriched witnesses and their AssumpPref proofs;
it does not assert the unrestricted `SortRetype E n` interface. -/
def sortRetypeAt_of_allBelowScoped_cts
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl)
    {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ) {A : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ A (.sort u)) (D₂ : TyP E n Γ A (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) :
    TyConvT E n Γ (.sort u) (.sort v) :=
  .of Γ (.sort u) (.sort v) (.succ u) (.sorts Γ u v
    (sortLevels_of_allBelowScoped_cts hBel S D₁ D₂ h₁ h₂))

/-! ## Discharging native enrichment's AssumpPref witnesses -/

/-- Construct the existing admission-adapter interface from the landed
member-sort and let-walk preservation theorems.  The environment witness
is quantified inside each field exactly as in EnrichAPAdapters. -/
def nativeEnrichAPAdapters (E : ResolvedEnv) (n : Nat) : EnrichAPAdapters E n where
  member := fun hW => memberSortP_of_envWfT_ap hW
  letCtx := fun hW => letCtxConvP_ap (cvWalkHyp_of_envWfT hW)

/-- AssumpPref for the actual EnvWfT-fronted typing enrichment.  Member
sorts use `memberSortP_of_envWfT_ap`; the let-context walk uses
`letCtxConvP_ap`.  The existing adapter theorem then supplies context and
term preservation.  No sorting or Pi row enters this proof. -/
theorem enrichHasTyT_native_ap (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e T : Expr Nat}
    (D : HasTyT E n Γ e T) :
    (enrichHasTyT_of_envWfT hW hΓ D).AssumpPref :=
  assumpPref_enrichHasTyT_of_adapters (nativeEnrichAPAdapters E n) hW hΓ D

/-- Reuse the existing scoped BIT projection with actual native adapters.
The native-wall and host-Prop zero-sort interfaces unfold to the same
statement.  This route needs neither CTS nor TableWF. -/
theorem zeroSortCoherence_of_allBelowScoped_bit
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hext : EnvExt E Eₐ) :
    HostPropAudit.ZeroSortCoherence E n :=
  Rcic.Syn.zeroSortCoherence_of_allBelowScoped hBel hext (nativeEnrichAPAdapters E n)

/-- The stronger scoped CTS pack proves same-term sort uniqueness by one
reflexive query.  The scope is the actual native context in its own
environment, and both AP inputs are the preceding preservation theorem.
This is not a derivation from sortRow alone. -/
theorem sortUniq_of_allBelowScoped_cts (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) : SortUniq E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ =>
    sortLevels_of_allBelowScoped_cts hBel ⟨hW, envExt_refl E, hΓ⟩
      (enrichHasTyT_of_envWfT hW hΓ h₁)
      (enrichHasTyT_of_envWfT hW hΓ h₂)
      (enrichHasTyT_native_ap hW hΓ h₁)
      (enrichHasTyT_native_ap hW hΓ h₂)

/-- Full native sort-retyping data from the actual scoped pack.  The
equality supplied by CTS is converted by the existing `ConvT.sorts`
constructor; no `Nonempty` value is selected. -/
def sortRetype_of_allBelowScoped_cts (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) : SortRetype E n :=
  sortRetype_of_sortUniq (sortUniq_of_allBelowScoped_cts hW hBel)

/-- Full zero-sort coherence uses the environment evidence already
present in that interface.  Its only remaining sorting premise is the
actual scoped Below pack. -/
theorem zeroSortCoherence_of_allBelowScoped_cts
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) : HostPropAudit.ZeroSortCoherence E n :=
  fun hW {_ _ _} hΓ h₁ h₂ => sortUniq_of_allBelowScoped_cts hW hBel hΓ h₁ h₂

/-- The existing restricted native Pi-valley consumer now has just the
two genuine producer inputs: the scoped Below pack and Pi-endpoint
valleys.  No separate SortRetype, zero-sort, TableWF, PiRow or type-
uniqueness supplier is assumed. -/
def piInj_of_piValleyData_allBelowScoped_cts (hW : EnvWfT E)
    (join : NativeKProjectionAudit.PiConvValleyData E n)
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) : PiInj E n :=
  NativeKProjectionAudit.piInj_of_piValleyData_sortRetype hW join
    (sortRetype_of_allBelowScoped_cts hW hBel)
    (zeroSortCoherence_of_allBelowScoped_cts hBel)

/-- The same consumer accepts the actual combined-bound CompleteC pack
through its existing scoped projection.  This theorem constructs neither
the CompleteC pack nor the Pi-valley producer. -/
def piInj_of_piValleyData_completeC_cts (hW : EnvWfT E)
    (join : NativeKProjectionAudit.PiConvValleyData E n)
    {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat),
      CompleteCAt (Eₐ := E) (Aw := Aw) (tbl := tbl) QueryC.combBound p B) :
    PiInj E n :=
  piInj_of_piValleyData_allBelowScoped_cts hW join (allBelowScoped_of_completeC hcomp)

#print axioms ComparisonNoApp
#print axioms nativeSortApplication
#print axioms nativeSortApplicationTyping
#print axioms nativeSortApplication_excluded
#print axioms typeConv_of_sortCoh_comparisonNoApp
#print axioms sortRetype_of_comparisonNoApp
#print axioms sortLevels_of_comparisonNoApp
#print axioms sortUniq_of_sortRetype_sortCoh
#print axioms sortLevels_of_belowScoped_cts
#print axioms sortLevels_of_allBelowScoped_cts
#print axioms sortLevels_of_completeC_cts
#print axioms sortRetypeAt_of_allBelowScoped_cts
#print axioms nativeEnrichAPAdapters
#print axioms enrichHasTyT_native_ap
#print axioms zeroSortCoherence_of_allBelowScoped_bit
#print axioms sortUniq_of_allBelowScoped_cts
#print axioms sortRetype_of_allBelowScoped_cts
#print axioms zeroSortCoherence_of_allBelowScoped_cts
#print axioms piInj_of_piValleyData_allBelowScoped_cts
#print axioms piInj_of_piValleyData_completeC_cts

end Rcic.Declarative.NativeValleys.NativeSortRetypeAudit
