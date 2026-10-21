import rcic.RcicNativeTypedModelTyping
import rcic.RcicSubstTTyped

/-!
# RcicNativeTypedModelRelS — the relation over `CptT`, superseding `LRSCoreT` (unified spine clause)

**Why this supersedes the landed `RcicNativeTypedModelRel.LRSCoreT`** (main, #7712).  Two findings
after it landed require a different spine clause, and a landed definition is never edited:

1. **Readback expansion** (segment 7): the landed data-spine clause carries a conversion AT THE
   INDEX (`ConvT … A`) and the type-level clause `TyConvT M M'`; a readback step is not a typed
   step, so neither survives `lrSCore_expand`-style absorption, which the β/ζ/δ/ι links need.
2. **The `app` case at a family spine** (segments 8–9, ruling (b)): when a spine grows from a
   data reading to a saturated type-level reading, the type-level data — `eqNList` of the levels
   and `ConvArgsT` along the DECLARED telescope — must already be present at the unsaturated
   prefix; the landed data clause records only the normal spines.

So `LRSCoreS` has ONE spine clause (`SpineClauseS`): both sides read back to normal same-head
spines, `eqNList` of the levels, `ConvArgsT` along the head's declared type for the available
prefix, lengths, and — conditional on the index reading back to a sort — the family saturation
and sort typings.  Every component is index-free except that condition, so expansion is safe; the
`famAppRow` read-off reads exactly the landed `TypeSpineT.famSpine` data from it.  The sort and
Π/λ clauses are the landed ones verbatim (`SortClauseT` is reused), so `lrSCoreS_prop_iff_sort`
(the audit lemma) is unchanged.

The typed PER (`typedPERS`) is the landed proof re-run against the new clause, with the family
premises generalised to the unified clause: `ConvArgsSymmS`/`ConvArgsTransS` — symmetry and
transitivity of `ConvArgsT` along a member's declared type under a level change, with no typing or
saturation hypotheses (discharged by level-instantiation congruence + `convT_substT_pointwise`,
item 2; `LevelCongrT` is with swe-espi).  All landed helpers (`redR_pi_unique`,
`foldApps_const_ne_sort`, `eqNList_symm''`, the size facts, `lrSCore_sort_iff`) are reused.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the unified spine clause and the relation -/

/-- **The unified spine clause** at head `r` with argument compacts `args`: both sides read back
    to normal spines with head `r`, the levels are `eqNList`, the arguments are pairwise
    convertible along the head's declared type (`ConvArgsT`, left levels) for the available prefix,
    and — when the index reads back to a sort and `r` is a family — both spines are saturated and
    typed at sorts. -/
def SpineClauseS (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (r : Nat)
    (args : List CptT) : Prop :=
  ∃ (m : CheckedMember) (ls₁ ls₂ : List Level) (xs₁ xs₂ : List (Expr Nat)),
    E.members r = some m ∧
    RedR R Γ M (foldApps (.const r ls₁) xs₁) ∧ RedR R Γ M' (foldApps (.const r ls₂) xs₂) ∧
    NormalR R Γ (foldApps (.const r ls₁) xs₁) ∧ NormalR R Γ (foldApps (.const r ls₂) xs₂) ∧
    eqNList ls₁ ls₂ ∧ args.length ≤ xs₁.length ∧ args.length ≤ xs₂.length ∧
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂ ∧
    ((∃ l, RedR R Γ A (.sort l)) → m.mclass = .inductiveM →
      xs₁.length = (piDomsOf m.mtype).length ∧ xs₂.length = (piDomsOf m.mtype).length ∧
      (∃ w, Nonempty (HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.sort w))) ∧
      (∃ w', Nonempty (HasTyT E n Γ (foldApps (.const r ls₂) xs₂) (.sort w'))))

/-- **The relation over `CptT`, superseding `LRSCoreT`.** -/
def LRSCoreS (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    CptT → Prop
  | .bot => True
  | .prop => SortClauseT R Γ M M' A
  | .sort => SortClauseT R Γ M M' A
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat, RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ u₁, LRSCoreS R E n Γ A₁ A₂ (.sort u₁) a) ∧
        ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) →
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreS R E n Γ N N' A₁ u) →
          ∃ v, LRSCoreS R E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort v) s.2
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, RedR R Γ A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreS R E n Γ N N' A₁ u) →
          LRSCoreS R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
  | .spine r args => SpineClauseS R E n Γ M M' A r args
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)

/-- The relation with the top-level proposition collapse. -/
def LRSS (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (c : CptT) : Prop :=
  IsPropTyR R E n Γ A ∨ LRSCoreS R E n Γ M M' A c

theorem lrSCoreS_bot (Γ : LCtx) (M M' A : Expr Nat) : LRSCoreS R E n Γ M M' A .bot := by
  rw [LRSCoreS.eq_def]; trivial

theorem lrSCoreS_prop_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreS R E n Γ M M' A .prop ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreS.eq_def]

theorem lrSCoreS_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreS R E n Γ M M' A .sort ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreS.eq_def]

/-- The audit lemma, unchanged: the two universe codes have one clause, reading only the readback. -/
theorem lrSCoreS_prop_iff_sort (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreS R E n Γ M M' A .prop ↔ LRSCoreS R E n Γ M M' A .sort :=
  (lrSCoreS_prop_iff Γ M M' A).trans (lrSCoreS_sort_iff Γ M M' A).symm

theorem lrSCoreS_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptT) :
    LRSCoreS R E n Γ M M' A (.spine r args) ↔ SpineClauseS R E n Γ M M' A r args := by
  rw [LRSCoreS.eq_def]

/-! ### §2 — the spine clause's algebra -/

/-- Generalised family premises: symmetry and transitivity of `ConvArgsT` along a member's
    declared type under a level change (no typing or saturation hypotheses). -/
def ConvArgsSymmS (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' : List Level} {xs xs' : List (Expr Nat)}, eqNList ls ls' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs

def ConvArgsTransS (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' ls'' : List Level} {xs xs' xs'' : List (Expr Nat)}, eqNList ls ls' → eqNList ls' ls'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs''

/-- Non-vacuity: both premises hold at the empty environment. -/
theorem convArgsSymmS_emptyEnv (n : Nat) : ConvArgsSymmS emptyEnv n := by
  intro Γ hΓ r m hm
  simp [emptyEnv] at hm

theorem convArgsTransS_emptyEnv (n : Nat) : ConvArgsTransS emptyEnv n := by
  intro Γ hΓ r m hm
  simp [emptyEnv] at hm

/-- Neither side of a spine clause reads back to a sort. -/
theorem spineClauseS_not_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {M M' A : Expr Nat} {r : Nat} {args : List CptT} (h : SpineClauseS R E n Γ M M' A r args) :
    (∀ l, ¬ RedR R Γ M (.sort l)) ∧ (∀ l, ¬ RedR R Γ M' (.sort l)) := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, _, h1, h2, hn₁, hn₂, _⟩ := h
  exact ⟨not_redR_sort_of_normal hL hNU h1 hn₁ (foldApps_const_ne_sort xs₁),
    not_redR_sort_of_normal hL hNU h2 hn₂ (foldApps_const_ne_sort xs₂)⟩

/-- The clause depends on the index only through "reads back to a sort". -/
theorem spineClauseS_idx {Γ : LCtx} {M M' A A' : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : (∃ l, RedR R Γ A (.sort l)) → ∃ l, RedR R Γ A' (.sort l))
    (h₂ : (∃ l, RedR R Γ A' (.sort l)) → ∃ l, RedR R Γ A (.sort l))
    (h : SpineClauseS R E n Γ M M' A r args) : SpineClauseS R E n Γ M M' A' r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, hty⟩ := h
  exact ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, fun hs => hty (h₂ hs)⟩

/-- Symmetry of the clause (`ConvArgsSymmS`). -/
theorem spineClauseS_symm (hCAs : ConvArgsSymmS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A A' : Expr Nat} {r : Nat} {args : List CptT}
    (hidx : (∃ l, RedR R Γ A' (.sort l)) → ∃ l, RedR R Γ A (.sort l))
    (h : SpineClauseS R E n Γ M M' A r args) : SpineClauseS R E n Γ M' M A' r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, hty⟩ := h
  refine ⟨m, ls₂, ls₁, xs₂, xs₁, hm, h2, h1, hn₂, hn₁, eqNList_symm'' heq, hl₂, hl₁,
    hCAs hΓ hm heq hca, fun hs hind => ?_⟩
  obtain ⟨e₁, e₂, hw, hw'⟩ := hty (hidx hs) hind
  exact ⟨e₂, e₁, hw', hw⟩

/-- Transitivity of the clause: the middle term's two normal spines coincide. -/
theorem spineClauseS_trans (hNU : NormalUniqueR R) (hCAt : ConvArgsTransS E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M M' M'' A : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : SpineClauseS R E n Γ M M' A r args) (h₂ : SpineClauseS R E n Γ M' M'' A r args) :
    SpineClauseS R E n Γ M M'' A r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, hty⟩ := h₁
  obtain ⟨m', ls₂', ls₃, xs₂', xs₃, hm', h2', h3, hn₂', hn₃, heq', _, hl₃, hca', hty'⟩ := h₂
  rw [hm] at hm'
  injection hm' with hm'
  subst hm'
  have e := hNU Γ h2 hn₂ h2' hn₂'
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
  injection hconst with _ hls
  subst hls; subst hxs
  refine ⟨m, ls₁, ls₃, xs₁, xs₃, hm, h1, h3, hn₁, hn₃, eqNList_trans'' heq heq', hl₁, hl₃,
    hCAt hΓ hm heq heq' hca hca', fun hs hind => ?_⟩
  obtain ⟨e₁, _, hw, _⟩ := hty hs hind
  obtain ⟨_, e₃, _, hw''⟩ := hty' hs hind
  exact ⟨e₁, e₃, hw, hw''⟩

/-- Among indices that read back to sorts, the index is irrelevant. -/
theorem lrSCoreS_sortIdx_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {N N' A A' : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) (hA' : ∃ l, RedR R Γ A' (.sort l)) :
    (c : CptT) → LRSCoreS R E n Γ N N' A c → LRSCoreS R E n Γ N N' A' c
  | .bot, _ => lrSCoreS_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreS_prop_iff] at h
      rw [lrSCoreS_prop_iff]
      exact ⟨hA', h.2⟩
  | .sort, h => by
      rw [lrSCoreS_sort_iff] at h
      rw [lrSCoreS_sort_iff]
      exact ⟨hA', h.2⟩
  | .pi a f, h => by
      rw [LRSCoreS.eq_def] at h
      rw [LRSCoreS.eq_def]
      exact ⟨hA', h.2⟩
  | .lam g, h => by
      rw [LRSCoreS.eq_def] at h
      obtain ⟨A₁, B₁, hr, _⟩ := h
      obtain ⟨l, hl⟩ := hA
      exact (not_redR_pi_of_redR_sort hL hNU hl A₁ B₁ hr).elim
  | .spine r args, h => by
      rw [LRSCoreS.eq_def] at h
      rw [LRSCoreS.eq_def]
      exact spineClauseS_idx (fun _ => hA') (fun _ => hA) h

/-! ### §3 — the typed PER package against the new clause -/

/-- The package's statements. -/
def IrrelAtS (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreS R E n Γ A₁ A₂ (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreS R E n Γ N N' A₁ u → LRSCoreS R E n Γ N N' A₂ u

def SymmTmAtS (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreS R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreS R E n Γ N N' A u → LRSCoreS R E n Γ N' N A u

def TransTmAtS (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreS R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' N'' : Expr Nat}, LRSCoreS R E n Γ N N' A u → LRSCoreS R E n Γ N' N'' A u →
      LRSCoreS R E n Γ N N'' A u

def SymmTyAtS (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreS R E n Γ A₁ A₂ (.sort w) c → LRSCoreS R E n Γ A₂ A₁ (.sort w) c

def TransTyAtS (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ A₃ : Expr Nat} {w : Level},
    LRSCoreS R E n Γ A₁ A₂ (.sort w) c → LRSCoreS R E n Γ A₂ A₃ (.sort w) c →
      LRSCoreS R E n Γ A₁ A₃ (.sort w) c


/-- `SymmTyAtS c` from the package below `c`. -/
theorem symmTy_stepS (hL : ReadbackLaws E R) (hW : EnvWfT E) (hCAs : ConvArgsSymmS E n) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtS R E n c' ∧ TransTyAtS R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtS R E n a u ∧ SymmTmAtS R E n a u ∧ TransTmAtS R E n a u) :
    SymmTyAtS R E n c := by
  intro Γ hΓ A₁ A₂ w h
  cases c with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at h
      rw [lrSCoreS_prop_iff]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreS_sort_iff] at h
      rw [lrSCoreS_sort_iff]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | lam g =>
      rw [LRSCoreS.eq_def] at h
      obtain ⟨A₁', B₁', hr, _⟩ := h
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [LRSCoreS.eq_def] at h
      rw [LRSCoreS.eq_def]
      exact spineClauseS_symm hCAs hΓ (fun _ => ⟨_, .refl _⟩) h
  | pi a f =>
      rw [LRSCoreS.eq_def] at h
      rw [LRSCoreS.eq_def]
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra' : LRSCoreS R E n Γ A₂' A₁' (.sort u₁) a := hsa hΓ hra
      have hself₂ : LRSCoreS R E n Γ A₂' A₂' (.sort u₁) a := hta hΓ hra' hra
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂', B₂', A₁', B₁', h2, h1, ⟨.assumption Γ A₂' v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, hra'⟩, ?_⟩
          intro s hs hty N N' hN hN' hcN hrel
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁' := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁' := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁' := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          have hrel₁ : ∀ u ∈ s.1, LRSCoreS R E n Γ N' N A₁' u := fun u hu =>
            (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).1 hΓ hra' (hty u hu)
              ((ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.1 hΓ hself₂ (hty u hu) (hrel u hu))
          obtain ⟨v', hv'⟩ := hrf s hs hty N' N hN'₁ hN₁ ⟨hc₁⟩ hrel₁
          exact ⟨v', (ihQ s.2 (sizeOf_out_lt_pi hs)).1 hΓ hv'⟩

/-- `TransTyAtS c` from the package below `c`. -/
theorem transTy_stepS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hCAt : ConvArgsTransS E n) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtS R E n c' ∧ TransTyAtS R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtS R E n a u ∧ SymmTmAtS R E n a u ∧ TransTmAtS R E n a u) :
    TransTyAtS R E n c := by
  intro Γ hΓ A₁ A₂ A₃ w h₁ h₂
  cases c with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at h₁ h₂
      rw [lrSCoreS_prop_iff]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreS_sort_iff] at h₁ h₂
      rw [lrSCoreS_sort_iff]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | lam g =>
      rw [LRSCoreS.eq_def] at h₁
      obtain ⟨A₁', B₁', hr, _⟩ := h₁
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [LRSCoreS.eq_def] at h₁ h₂
      rw [LRSCoreS.eq_def]
      exact spineClauseS_trans hNU hCAt hΓ h₁ h₂
  | pi a f =>
      rw [LRSCoreS.eq_def] at h₁ h₂
      rw [LRSCoreS.eq_def]
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom₁⟩, ⟨hcod₁⟩, ⟨u₁, hra₁⟩, hrf₁⟩ := h₁
      obtain ⟨_, A₂'', B₂'', A₃', B₃', h2', h3, _, ⟨hdom₂⟩, ⟨hcod₂⟩, ⟨u₂, hra₂⟩, hrf₂⟩ := h₂
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU h2 h2'
      subst eA; subst eB
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra₂' : LRSCoreS R E n Γ A₂' A₃' (.sort u₁) a :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ a hra₂
      have hself₁ : LRSCoreS R E n Γ A₁' A₁' (.sort u₁) a := hta hΓ hra₁ (hsa hΓ hra₁)
      refine ⟨hA, A₁', B₁', A₃', B₃', h1, h3, ⟨hΓ₁⟩, ⟨TyConvT.trans _ _ _ _ hdom₁ hdom₂⟩,
        ⟨TyConvT.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂)⟩, ⟨u₁, hta hΓ hra₁ hra₂'⟩, ?_⟩
      intro s hs hty N N' hN hN' hcN hrel
      obtain ⟨hcN⟩ := hcN
      have hrelNN : ∀ u ∈ s.1, LRSCoreS R E n Γ N N A₁' u := fun u hu =>
        (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.2 hΓ hself₁ (hty u hu) (hrel u hu)
          ((ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.1 hΓ hself₁ (hty u hu) (hrel u hu))
      obtain ⟨v, hv⟩ := hrf₁ s hs hty N N hN hN ⟨.refl _ _ _ hN⟩ hrelNN
      have hN₂ : HasTyT E n Γ N A₂' := hasTyT_of_tyConvT hN hdom₁
      have hN'₂ : HasTyT E n Γ N' A₂' := hasTyT_of_tyConvT hN' hdom₁
      have hrel₂ : ∀ u ∈ s.1, LRSCoreS R E n Γ N N' A₂' u := fun u hu =>
        (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).1 hΓ hra₁ (hty u hu) (hrel u hu)
      obtain ⟨v', hv'⟩ := hrf₂ s hs hty N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom₁⟩ hrel₂
      exact ⟨v, (ihQ s.2 (sizeOf_out_lt_pi hs)).2 hΓ hv
        (lrSCoreS_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ s.2 hv')⟩

/-- At a spine-coded index neither side reads back to a sort. -/
theorem lrSCoreS_spine_notSort_of_tyIdx (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {A : Expr Nat} {w : Level} {r' : Nat} {args' : List CptT} {A₂ : Expr Nat}
    (h : LRSCoreS R E n Γ A A₂ (.sort w) (.spine r' args')) :
    (∀ l, ¬ RedR R Γ A (.sort l)) ∧ (∀ l, ¬ RedR R Γ A₂ (.sort l)) := by
  rw [LRSCoreS.eq_def] at h
  exact spineClauseS_not_sort hL hNU h

/-- `IrrelAtS a u` from the package below. -/
theorem irrel_stepS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtS R E n c' ∧ TransTyAtS R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtS R E n a' u' ∧ SymmTmAtS R E n a' u' ∧ TransTmAtS R E n a' u') :
    IrrelAtS R E n a u := by
  intro Γ hΓ A₁ A₂ w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | sort =>
      rw [lrSCoreS_sort_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreS_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreS_bot _ _ _ _
      · obtain ⟨hns₁, hns₂⟩ := lrSCoreS_spine_notSort_of_tyIdx hL hNU hAA
        rw [LRSCoreS.eq_def] at h
        rw [LRSCoreS.eq_def]
        exact spineClauseS_idx (fun ⟨l, hl⟩ => (hns₁ l hl).elim) (fun ⟨l, hl⟩ => (hns₂ l hl).elim) h
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreS_bot _ _ _ _
      · rw [LRSCoreS.eq_def] at h
        obtain ⟨A₁₁, B₁₁, hr₁, ⟨hΓ₁₁⟩, hclause⟩ := h
        rw [LRSCoreS.eq_def] at hAA
        obtain ⟨_, A₁₁', B₁₁', A₂₁, B₂₁, hr₁', hr₂, _, ⟨hdomT⟩, ⟨hcodT⟩, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr₁ hr₁'
        subst eA; subst eB
        have hlt_a' : sizeOf a' < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
          have := sizeOf_dom_lt_pi a' g; omega
        obtain ⟨hsa, hta⟩ := ihQ a' hlt_a'
        have hra' : LRSCoreS R E n Γ A₂₁ A₁₁ (.sort u₁) a' := hsa hΓ hra
        have hself₁ : LRSCoreS R E n Γ A₁₁ A₁₁ (.sort u₁) a' := hta hΓ hra hra'
        rw [LRSCoreS.eq_def]
        cases hΓ₁₁ with
        | assumption _ _ u₀ _ hA₁₁ =>
            obtain ⟨v₀, hA₂₁⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdomT hA₁₁
            refine ⟨A₂₁, B₂₁, hr₂, ⟨.assumption Γ A₂₁ v₀ hΓ hA₂₁⟩, ?_⟩
            intro s hs M M' hM hM' hcM hrel
            obtain ⟨hcM⟩ := hcM
            have hM₁ : HasTyT E n Γ M A₁₁ := hasTyT_of_tyConvT hM hdomT.symmT
            have hM'₁ : HasTyT E n Γ M' A₁₁ := hasTyT_of_tyConvT hM' hdomT.symmT
            have hc₁ : ConvT E n Γ M M' A₁₁ := convT_of_tyConv hcM hdomT.symmT
            have hltP : ∀ v ∈ s.1, sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
              fun v hv => by
                have := sizeOf_dom_lt_pi a' g
                have := sizeOf_dem_lt_lam hs hv
                omega
            have hrel₁ : ∀ v ∈ s.1, LRSCoreS R E n Γ M M' A₁₁ v := fun v hv =>
              (ihP a' v (hltP v hv)).1 hΓ hra' (hdom s hs v hv) (hrel v hv)
            have hcore := hclause s hs M M' hM₁ hM'₁ ⟨hc₁⟩ hrel₁
            rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
            · rw [h0]; exact lrSCoreS_bot _ _ _ _
            · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
              have hrelMM : ∀ v ∈ t.1, LRSCoreS R E n Γ M M A₁₁ v := fun v hv =>
                (ihP a' v (hltP v (hcomp v hv))).2.2 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv))
                  ((ihP a' v (hltP v (hcomp v hv))).2.1 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv)))
              obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M M hM₁ hM₁ ⟨.refl _ _ _ hM₁⟩ hrelMM
              have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
                have := sizeOf_out_lt_pi (a := a') ht
                have := sizeOf_out_lt_lam hs
                omega
              exact (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore

/-- `SymmTmAtS a u` from the package below. -/
theorem symmTm_stepS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hCAs : ConvArgsSymmS E n) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtS R E n c' ∧ TransTyAtS R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtS R E n a' u' ∧ SymmTmAtS R E n a' u' ∧ TransTmAtS R E n a' u') :
    SymmTmAtS R E n a u := by
  intro Γ hΓ A w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by have := CptT.sizeOf_pos CptT.prop; omega
      have h' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | sort =>
      rw [lrSCoreS_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by have := CptT.sizeOf_pos CptT.sort; omega
      have h' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreS_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreS_bot _ _ _ _
      · rw [LRSCoreS.eq_def] at h
        rw [LRSCoreS.eq_def]
        exact spineClauseS_symm hCAs hΓ (fun hs => hs) h
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreS_bot _ _ _ _
      · rw [LRSCoreS.eq_def] at h
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hclause⟩ := h
        rw [LRSCoreS.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreS.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrel' : ∀ v ∈ s.1, LRSCoreS R E n Γ M' M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv)
        have hcore := hclause s hs M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrel'
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreS_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          have hrelM'M : ∀ v ∈ t.1, LRSCoreS R E n Γ M' M A₁ v := fun v hv => hrel' v (hcomp v hv)
          have hrelMM : ∀ v ∈ t.1, LRSCoreS R E n Γ M M A₁ v := fun v hv =>
            (ihP a' v (hltP hs v (hcomp v hv))).2.2 hΓ hra (htyt v hv) (hrel v (hcomp v hv))
              (hrelM'M v hv)
          obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrelM'M
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          have hmoved := (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore
          exact (ihP t.2 s.2 hlt_t).2.1 hΓ hv₂ (hcod s hs t ht hcomp) hmoved

/-- `TransTmAtS a u` from the package below. -/
theorem transTm_stepS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hCAt : ConvArgsTransS E n) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtS R E n c' ∧ TransTyAtS R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtS R E n a' u' ∧ SymmTmAtS R E n a' u' ∧ TransTmAtS R E n a' u') :
    TransTmAtS R E n a u := by
  intro Γ hΓ A w hAA hu N N' N'' h₁ h₂
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by have := CptT.sizeOf_pos CptT.prop; omega
      have h₁' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | sort =>
      rw [lrSCoreS_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by have := CptT.sizeOf_pos CptT.sort; omega
      have h₁' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreS_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreS_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreS_bot _ _ _ _
      · rw [LRSCoreS.eq_def] at h₁ h₂
        rw [LRSCoreS.eq_def]
        exact spineClauseS_trans hNU hCAt hΓ h₁ h₂
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreS_bot _ _ _ _
      · rw [LRSCoreS.eq_def] at h₁ h₂
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hcl₁⟩ := h₁
        obtain ⟨A₁', B₁', hr', _, hcl₂⟩ := h₂
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        rw [LRSCoreS.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreS.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrelMM : ∀ v ∈ s.1, LRSCoreS R E n Γ M M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.2 hΓ hra (hdom s hs v hv) (hrel v hv)
            ((ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv))
        have hc₁ := hcl₁ s hs M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
        have hc₂ := hcl₂ s hs M M' hM hM' ⟨hcM⟩ hrel
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreS_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ (fun v hv => hrelMM v (hcomp v hv))
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          exact (ihP t.2 s.2 hlt_t).2.2 hΓ hv₂ (hcod s hs t ht hcomp) hc₁ hc₂

/-- **The typed PER**, by strong induction on size. -/
theorem typedPERS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) :
    ∀ k : Nat,
      (∀ c : CptT, sizeOf c ≤ k → SymmTyAtS R E n c ∧ TransTyAtS R E n c) ∧
      (∀ a u : CptT, sizeOf a + sizeOf u ≤ k →
        IrrelAtS R E n a u ∧ SymmTmAtS R E n a u ∧ TransTmAtS R E n a u) := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · exact absurd hc (Nat.not_le_of_gt (CptT.sizeOf_pos c))
      · exact absurd hau (Nat.not_le_of_gt (Nat.add_pos_left (CptT.sizeOf_pos a) _))
  | succ k ih =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · by_cases hk : sizeOf c ≤ k
        · exact ih.1 c hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtS R E n c' ∧ TransTyAtS R E n c' :=
            fun c' hc' => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf c →
              IrrelAtS R E n a' u' ∧ SymmTmAtS R E n a' u' ∧ TransTmAtS R E n a' u' :=
            fun a' u' h => ih.2 a' u' (by omega)
          exact ⟨symmTy_stepS hL hW hCAs c ihQ ihP, transTy_stepS hL hNU hW hCAt c ihQ ihP⟩
      · by_cases hk : sizeOf a + sizeOf u ≤ k
        · exact ih.2 a u hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtS R E n c' ∧ TransTyAtS R E n c' :=
            fun c' hc' => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
              IrrelAtS R E n a' u' ∧ SymmTmAtS R E n a' u' ∧ TransTmAtS R E n a' u' :=
            fun a' u' h => ih.2 a' u' (by omega)
          exact ⟨irrel_stepS hL hNU hW a u ihQ ihP, symmTm_stepS hL hNU hW hCAs a u ihQ ihP,
            transTm_stepS hL hNU hW hCAt a u ihQ ihP⟩

/-! #### the corollaries -/

/-- **Irrelevance**: a demand typed at the domain code transports across the domain relation. -/
theorem lrSCoreS_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreS R E n Γ A₁ A₂ (.sort w) a) (hu : CTyS E u a) {N N' : Expr Nat}
    (h : LRSCoreS R E n Γ N N' A₁ u) : LRSCoreS R E n Γ N N' A₂ u :=
  ((typedPERS hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).1 hΓ hAA hu h

/-- **Symmetry of the type-level relation at every compact.** -/
theorem lrSCoreS_symm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ : Expr Nat} {w : Level} {c : CptT} (h : LRSCoreS R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreS R E n Γ A₂ A₁ (.sort w) c :=
  ((typedPERS hL hNU hW hCAs hCAt _).1 c (Nat.le_refl _)).1 hΓ h

/-- **Transitivity of the type-level relation at every compact.** -/
theorem lrSCoreS_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSCoreS R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSCoreS R E n Γ A₂ A₃ (.sort w) c) :
    LRSCoreS R E n Γ A₁ A₃ (.sort w) c :=
  ((typedPERS hL hNU hW hCAs hCAt _).1 c (Nat.le_refl _)).2 hΓ h₁ h₂

/-- **Symmetry of the term-level relation** at a demand typed at a self-related type code. -/
theorem lrSCoreS_symm_tm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {w : Level} {a u : CptT} (hAA : LRSCoreS R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSCoreS R E n Γ N N' A u) : LRSCoreS R E n Γ N' N A u :=
  ((typedPERS hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).2.1 hΓ hAA hu h

theorem lrSCoreS_trans_tm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {w : Level} {a u : CptT} (hAA : LRSCoreS R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSCoreS R E n Γ N N' A u) (h₂ : LRSCoreS R E n Γ N' N'' A u) :
    LRSCoreS R E n Γ N N'' A u :=
  ((typedPERS hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).2.2 hΓ hAA hu h₁ h₂


#print axioms SpineClauseS
#print axioms LRSCoreS
#print axioms LRSS
#print axioms lrSCoreS_bot
#print axioms lrSCoreS_prop_iff
#print axioms lrSCoreS_sort_iff
#print axioms lrSCoreS_prop_iff_sort
#print axioms lrSCoreS_spine_iff
#print axioms ConvArgsSymmS
#print axioms ConvArgsTransS
#print axioms convArgsSymmS_emptyEnv
#print axioms convArgsTransS_emptyEnv
#print axioms spineClauseS_not_sort
#print axioms spineClauseS_idx
#print axioms spineClauseS_symm
#print axioms spineClauseS_trans
#print axioms lrSCoreS_sortIdx_irrel
#print axioms IrrelAtS
#print axioms SymmTmAtS
#print axioms TransTmAtS
#print axioms SymmTyAtS
#print axioms TransTyAtS
#print axioms symmTy_stepS
#print axioms transTy_stepS
#print axioms lrSCoreS_spine_notSort_of_tyIdx
#print axioms irrel_stepS
#print axioms symmTm_stepS
#print axioms transTm_stepS
#print axioms typedPERS
#print axioms lrSCoreS_irrel
#print axioms lrSCoreS_symm
#print axioms lrSCoreS_trans
#print axioms lrSCoreS_symm_tm
#print axioms lrSCoreS_trans_tm

end Rcic.Declarative.NativeValleys.TypedModelAudit
