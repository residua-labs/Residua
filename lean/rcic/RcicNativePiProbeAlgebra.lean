import rcic.RcicNativePiCycleProbe

/-!
# Pi-probe algebra without unique readback normal forms

The one-sided `PiProbeLinkT` from #7721 is not by itself an induction
hypothesis for native `symm`: its premise observes the wrong endpoint.
`piProbe_reverse_link_iffT` identifies the exact missing diagonal transport.
Native `tyConv` has a second issue: its old index need not be a syntactic
sort.  The reindexing lemmas expose the additional old-index readback
premise needed by an index-sensitive link.

This module audits a stronger, explicit motive. `ProbeTransportT` transports
sort readback existence and every *specified* Pi readback whose domain
extends the well-formed context. `ProbeEquivT` supplies both directions;
`ConvProbeMotiveT` erases only the conversion's index. Its transitivity passes
the very same middle Pi witness to the next transport. It therefore uses
neither exact normal-form uniqueness nor a global coherence hypothesis.
The next binder context comes from `tyConvT_endTyped`; no typing of a raw
whole Pi reduct is assumed.

The native `refl`, `symm`, `trans`, `pi`, `sorts`, and `tyConv` algebra arms
are proved below. The motive is stronger than the original one-sided link;
its other native constructor arms remain obligations. `ProbeConvLinksT` is
the explicitly named unproved single-link input to the conditional native
`TyConvT` and Pi-row consumers. No all-constructor theorem is supplied.

`closure_claim = 0`. No new axiom, no `sorry`, no `Classical.choice`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ## Exact index and diagonal requirements of the original link -/

/-- At the Pi probe, reindexing needs exactly a sort readback of the new
index. The terms' readback witnesses and component conversions are reused. -/
theorem piProbe_reindexT {Γ : LCtx} {M N I J : Expr Nat}
    (hJ : ∃ u, RedR R Γ J (.sort u))
    (h : LRSCoreT R E n Γ M N I (.pi .bot [])) :
    LRSCoreT R E n Γ M N J (.pi .bot []) := by
  rw [LRSCoreT.eq_def] at h
  rw [LRSCoreT.eq_def]
  exact ⟨hJ, h.2⟩

/-- The same exact index requirement at the sort probe. -/
theorem sortProbe_reindexT {Γ : LCtx} {M N I J : Expr Nat}
    (hJ : ∃ u, RedR R Γ J (.sort u))
    (h : LRSCoreT R E n Γ M N I .sort) :
    LRSCoreT R E n Γ M N J .sort := by
  rw [lrSCoreT_sort_iff] at h
  rw [lrSCoreT_sort_iff]
  exact ⟨hJ, h.2⟩

/-- An index-sensitive Pi observation is the index-erased observation
together with the old index's sort readback. -/
theorem piProbe_index_iffT {Γ : LCtx} {M N I : Expr Nat} :
    LRSCoreT R E n Γ M N I (.pi .bot []) ↔
      (∃ u, RedR R Γ I (.sort u)) ∧
        LRSCoreT R E n Γ M N (.sort .zero) (.pi .bot []) := by
  constructor
  · intro h
    have hi := h
    rw [LRSCoreT.eq_def] at hi
    exact ⟨hi.1, piProbe_reindexT ⟨.zero, .refl _⟩ h⟩
  · rintro ⟨hi, h⟩
    exact piProbe_reindexT hi h

/-- The sort observation has the same index factorization. -/
theorem sortProbe_index_iffT {Γ : LCtx} {M N I : Expr Nat} :
    LRSCoreT R E n Γ M N I .sort ↔
      (∃ u, RedR R Γ I (.sort u)) ∧
        LRSCoreT R E n Γ M N (.sort .zero) .sort := by
  constructor
  · intro h
    have hi := h
    rw [lrSCoreT_sort_iff] at hi
    exact ⟨hi.1, sortProbe_reindexT ⟨.zero, .refl _⟩ h⟩
  · rintro ⟨hi, h⟩
    exact sortProbe_reindexT hi h

/-- The sort clause swaps its readback witnesses without a readback law. -/
theorem sortProbe_symmT {Γ : LCtx} {M N I : Expr Nat}
    (h : LRSCoreT R E n Γ M N I .sort) :
    LRSCoreT R E n Γ N M I .sort := by
  rw [lrSCoreT_sort_iff] at h
  rw [lrSCoreT_sort_iff]
  obtain ⟨hi, u, v, hM, hN⟩ := h
  exact ⟨hi, v, u, hN, hM⟩

/-- Sort-probe transitivity keeps only the outer readback witnesses. -/
theorem sortProbe_transT {Γ : LCtx} {M N P I : Expr Nat}
    (hMN : LRSCoreT R E n Γ M N I .sort)
    (hNP : LRSCoreT R E n Γ N P I .sort) :
    LRSCoreT R E n Γ M P I .sort := by
  rw [lrSCoreT_sort_iff] at hMN hNP
  rw [lrSCoreT_sort_iff]
  obtain ⟨hi, u, _, hM, _⟩ := hMN
  obtain ⟨_, _, v, _, hP⟩ := hNP
  exact ⟨hi, u, v, hM, hP⟩

theorem sortProbe_right_diagonalT {Γ : LCtx} {M N I : Expr Nat}
    (h : LRSCoreT R E n Γ M N I .sort) :
    LRSCoreT R E n Γ N N I .sort :=
  sortProbe_transT (sortProbe_symmT h) h

/-- The one-sided symmetry gap has the same exact diagonal formulation
at the sort probe, here without any well-formedness assumptions. -/
theorem sortProbe_reverse_link_iffT {Γ : LCtx} {M N I : Expr Nat}
    (hforward : LRSCoreT R E n Γ M M I .sort → LRSCoreT R E n Γ M N I .sort) :
    (LRSCoreT R E n Γ N N I .sort → LRSCoreT R E n Γ N M I .sort) ↔
    (LRSCoreT R E n Γ N N I .sort → LRSCoreT R E n Γ M M I .sort) := by
  constructor
  · intro hback hNN
    exact sortProbe_right_diagonalT (hback hNN)
  · intro hdiag hNN
    exact sortProbe_symmT (hforward (hdiag hNN))

/-- The left Pi diagonal reuses one witness twice; it needs no readback
law, environment hypothesis, coherence, or uniqueness premise. -/
theorem piProbe_left_diagonalT {Γ : LCtx} {M N I : Expr Nat}
    (h : LRSCoreT R E n Γ M N I (.pi .bot [])) :
    LRSCoreT R E n Γ M M I (.pi .bot []) := by
  rw [LRSCoreT.eq_def] at h
  rw [LRSCoreT.eq_def]
  obtain ⟨hi, A, B, _, _, hM, _, hΓA, _⟩ := h
  exact ⟨hi, A, B, A, B, hM, hM, hΓA, ⟨.refl _ _⟩,
    ⟨.refl _ _⟩, ⟨.zero, lrSCoreT_bot _ _ _ _⟩,
    fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- The landed symmetry theorem supplies the right binder context. Then
one witness gives the right diagonal without a transitivity theorem. -/
theorem piProbe_right_diagonalT_noUnique (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (h : LRSCoreT R E n Γ M N I (.pi .bot [])) :
    LRSCoreT R E n Γ N N I (.pi .bot []) :=
  piProbe_left_diagonalT (piProbe_symmT hW hΓ h)

/-- Given the one-sided forward link, the missing `symm` arm is equivalent
to transporting a right diagonal back to a left diagonal. This is an exact
local extra premise, not an assumed full fundamental theorem. -/
theorem piProbe_reverse_link_iffT (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hforward : LRSCoreT R E n Γ M M I (.pi .bot []) →
      LRSCoreT R E n Γ M N I (.pi .bot [])) :
    (LRSCoreT R E n Γ N N I (.pi .bot []) →
      LRSCoreT R E n Γ N M I (.pi .bot [])) ↔
    (LRSCoreT R E n Γ N N I (.pi .bot []) →
      LRSCoreT R E n Γ M M I (.pi .bot [])) := by
  constructor
  · intro hback hNN
    exact piProbe_right_diagonalT_noUnique hW hΓ (hback hNN)
  · intro hdiag hNN
    exact piProbe_symmT hW hΓ (hforward (hdiag hNN))

/-- The additional old-index readback suffices to use an index-sensitive
IH in `tyConv` when its resulting index is a sort. -/
theorem piProbe_at_sort_of_old_indexT {Γ : LCtx} {M N I : Expr Nat} {v : Level}
    (hi : ∃ u, RedR R Γ I (.sort u))
    (ih : LRSCoreT R E n Γ M M I (.pi .bot []) →
      LRSCoreT R E n Γ M N I (.pi .bot []))
    (hMM : LRSCoreT R E n Γ M M (.sort v) (.pi .bot [])) :
    LRSCoreT R E n Γ M N (.sort v) (.pi .bot []) :=
  piProbe_reindexT ⟨v, .refl _⟩ (ih (piProbe_reindexT hi hMM))

/-! ## The explicit strengthened motive -/

/-- Transport existence of a sort observation. No universe level is
identified by this probe. -/
def SortReadTransportT (R : Readback) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  (∃ u, RedR R Γ M (.sort u)) → ∃ v, RedR R Γ N (.sort v)

/-- Transport a specified Pi observation and its component conversions.
Only the source domain's well-formed binder context is required. -/
def PiReadTransportT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M N : Expr Nat) : Prop :=
  ∀ {A B : Expr Nat}, RedR R Γ M (.pi A B) →
    CtxWfT E n (.assumption A :: Γ) →
    ∃ A' B', RedR R Γ N (.pi A' B') ∧
      Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- The two probes' explicit forward observation obligations. -/
structure ProbeTransportT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M N : Expr Nat) : Prop where
  sorts : SortReadTransportT R Γ M N
  pis : PiReadTransportT R E n Γ M N

/-- Both conversion directions, required for native `symm`. -/
def ProbeEquivT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M N : Expr Nat) : Prop :=
  ProbeTransportT R E n Γ M N ∧ ProbeTransportT R E n Γ N M

/-- The index-erased native conversion motive. In the native `tyConv` arm
the smaller term-conversion derivation has this same motive even if its
old type is not syntactically a sort. -/
def ConvProbeMotiveT (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {M N A : Expr Nat} (_hc : ConvT E n Γ M N A) : Prop :=
  ProbeEquivT R E n Γ M N

theorem probeTransport_reflT (Γ : LCtx) (M : Expr Nat) :
    ProbeTransportT R E n Γ M M := by
  refine ⟨fun h => h, ?_⟩
  intro A B hM _
  exact ⟨A, B, hM, ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩

/-- Composition uses one shared middle witness. The second codomain chain
is moved from that witness's binder to the original binder. -/
theorem probeTransport_transT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N P : Expr Nat}
    (hMN : ProbeTransportT R E n Γ M N)
    (hNP : ProbeTransportT R E n Γ N P) : ProbeTransportT R E n Γ M P := by
  refine ⟨fun h => hNP.sorts (hMN.sorts h), ?_⟩
  intro A B hM hΓA
  obtain ⟨A', B', hN, ⟨hAA'⟩, ⟨hBB'⟩⟩ := hMN.pis hM hΓA
  have hΓA' : CtxWfT E n (.assumption A' :: Γ) := by
    cases hΓA with
    | assumption _ _ u _ hA =>
        obtain ⟨v, hA'⟩ := tyConvT_endTyped hW hΓ hAA' hA
        exact .assumption Γ A' v hΓ hA'
  obtain ⟨A'', B'', hP, ⟨hA'A''⟩, ⟨hB'B''⟩⟩ := hNP.pis hN hΓA'
  exact ⟨A'', B'', hP, ⟨.trans _ _ _ _ hAA' hA'A''⟩,
    ⟨.trans _ _ _ _ hBB' (tyConvT_assump_dom hW hΓ hAA' hB'B'')⟩⟩

theorem probeEquiv_reflT (Γ : LCtx) (M : Expr Nat) :
    ProbeEquivT R E n Γ M M :=
  ⟨probeTransport_reflT Γ M, probeTransport_reflT Γ M⟩

theorem probeEquiv_symmT {Γ : LCtx} {M N : Expr Nat}
    (h : ProbeEquivT R E n Γ M N) : ProbeEquivT R E n Γ N M :=
  ⟨h.2, h.1⟩

theorem probeEquiv_transT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N P : Expr Nat}
    (hMN : ProbeEquivT R E n Γ M N) (hNP : ProbeEquivT R E n Γ N P) :
    ProbeEquivT R E n Γ M P :=
  ⟨probeTransport_transT hW hΓ hMN.1 hNP.1,
    probeTransport_transT hW hΓ hNP.2 hMN.2⟩

/-- A primitive computation preserving each normal target preserves both
specified probe witnesses, with reflexive component conversions. -/
theorem probeTransport_of_readback_impT (hL : ReadbackLaws E R)
    {Γ : LCtx} {M N : Expr Nat}
    (hread : ∀ X, NormalR R Γ X → RedR R Γ M X → RedR R Γ N X) :
    ProbeTransportT R E n Γ M N := by
  constructor
  · rintro ⟨u, hM⟩
    exact ⟨u, hread _ (fun _ hs => hL.sort_normal _ _ _ hs) hM⟩
  · intro A B hM _
    exact ⟨A, B, hread _ (fun _ hs => hL.pi_normal _ _ _ _ hs) hM,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩

theorem probeEquiv_of_readback_iffT (hL : ReadbackLaws E R)
    {Γ : LCtx} {M N : Expr Nat}
    (hread : ∀ X, NormalR R Γ X → (RedR R Γ M X ↔ RedR R Γ N X)) :
    ProbeEquivT R E n Γ M N :=
  ⟨probeTransport_of_readback_impT hL (fun X hX => (hread X hX).mp),
    probeTransport_of_readback_impT hL (fun X hX => (hread X hX).mpr)⟩

/-- The exact vacuous forward arm: a Pi readback matters only when its
domain supplies the well-formed binder context required by the motive. -/
theorem probeTransport_of_no_wf_probesT {Γ : LCtx} {M N : Expr Nat}
    (hs : ∀ u, ¬ RedR R Γ M (.sort u))
    (hp : ∀ A B, RedR R Γ M (.pi A B) →
      CtxWfT E n (.assumption A :: Γ) → False) : ProbeTransportT R E n Γ M N := by
  constructor
  · rintro ⟨u, h⟩
    exact (hs u h).elim
  · intro A B h hΓA
    exact (hp A B h hΓA).elim

/-- An unguarded absence of Pi readbacks also discharges that arm. -/
theorem probeTransport_of_no_probesT {Γ : LCtx} {M N : Expr Nat}
    (hs : ∀ u, ¬ RedR R Γ M (.sort u))
    (hp : ∀ A B, ¬ RedR R Γ M (.pi A B)) : ProbeTransportT R E n Γ M N :=
  probeTransport_of_no_wf_probesT hs (fun A B h _ => hp A B h)

theorem probeEquiv_of_no_probesT {Γ : LCtx} {M N : Expr Nat}
    (hsM : ∀ u, ¬ RedR R Γ M (.sort u))
    (hpM : ∀ A B, ¬ RedR R Γ M (.pi A B))
    (hsN : ∀ u, ¬ RedR R Γ N (.sort u))
    (hpN : ∀ A B, ¬ RedR R Γ N (.pi A B)) : ProbeEquivT R E n Γ M N :=
  ⟨probeTransport_of_no_probesT hsM hpM, probeTransport_of_no_probesT hsN hpN⟩

/-! ## Native constructor algebra -/

/-- A sort has an actual sort observation, without a normalization premise. -/
theorem sortProbe_diagT (Γ : LCtx) (u v : Level) :
    LRSCoreT R E n Γ (.sort u) (.sort u) (.sort v) .sort := by
  rw [lrSCoreT_sort_iff]
  exact ⟨⟨v, .refl _⟩, u, u, .refl _, .refl _⟩

/-- The root's closed typed Pi pin supplies an actual Pi probe. Together
with the reflexive constructor arm below this makes its antecedent inhabited. -/
theorem pinPiProbeT :
    LRSCoreT R E n [] (.pi (.sort .zero) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) (.pi .bot []) :=
  piProbe_diagT_of_typing .nil (pinPiT E n)

theorem convProbe_reflT {Γ : LCtx} {M A : Expr Nat} (h : HasTyT E n Γ M A) :
    ConvProbeMotiveT R (.refl Γ M A h) := probeEquiv_reflT Γ M

theorem convProbe_symmT {Γ : LCtx} {M N A : Expr Nat}
    (hc : ConvT E n Γ M N A) (ih : ConvProbeMotiveT R hc) :
    ConvProbeMotiveT R (.symm Γ M N A hc) := probeEquiv_symmT ih

theorem convProbe_transT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P A : Expr Nat} (hMN : ConvT E n Γ M N A) (hNP : ConvT E n Γ N P A)
    (ihMN : ConvProbeMotiveT R hMN) (ihNP : ConvProbeMotiveT R hNP) :
    ConvProbeMotiveT R (.trans Γ M N P A hMN hNP) :=
  probeEquiv_transT hW hΓ ihMN ihNP

/-- A syntactic sort has the sort probe and no Pi readback. The observed
sort level is deliberately not equated by this probe. -/
theorem probeTransport_sortsT (hL : ReadbackLaws E R) (Γ : LCtx) (u v : Level) :
    ProbeTransportT R E n Γ (.sort u) (.sort v) := by
  constructor
  · intro _
    exact ⟨v, .refl _⟩
  · intro A B h _
    exact (Expr.noConfusion (redR_sort_eq hL h) : False).elim

theorem convProbe_sortsT (hL : ReadbackLaws E R)
    (Γ : LCtx) (u v : Level) (heq : eqN u v) :
    ConvProbeMotiveT R (ConvT.sorts (E := E) (n := n) Γ u v heq) :=
  ⟨probeTransport_sortsT hL Γ u v, probeTransport_sortsT hL Γ v u⟩

/-- A syntactic Pi's source readback fixes its components. The native
domain/codomain conversion premises supply the requested witness directly. -/
theorem probeTransport_piT (hL : ReadbackLaws E R) {Γ : LCtx}
    {A A' B B' : Expr Nat} (hA : TyConvT E n Γ A A')
    (hB : TyConvT E n (.assumption A :: Γ) B B') :
    ProbeTransportT R E n Γ (.pi A B) (.pi A' B') := by
  constructor
  · rintro ⟨u, h⟩
    exact (Expr.noConfusion (redR_pi_eq hL h) : False).elim
  · intro X Y h _
    rcases Expr.pi.inj (redR_pi_eq hL h) with ⟨rfl, rfl⟩
    exact ⟨A', B', .refl _, ⟨hA⟩, ⟨hB⟩⟩

theorem convProbe_piT (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    ConvProbeMotiveT R (.pi Γ A A' B B' u v hA hB) := by
  let hdom : TyConvT E n Γ A A' := .of _ _ _ _ hA
  let hcod : TyConvT E n (.assumption A :: Γ) B B' := .of _ _ _ _ hB
  exact ⟨probeTransport_piT hL hdom hcod,
    probeTransport_piT hL hdom.symmT
      (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT)⟩

/-- The smaller term-conversion IH survives native `tyConv` definitionally.
The old index is arbitrary; no sort-shape claim about it is made. -/
theorem convProbe_tyConvT {Γ : LCtx} {M N A A' : Expr Nat} {u : Level}
    (hc : ConvT E n Γ M N A) (hA : ConvT E n Γ A A' (.sort u))
    (ih : ConvProbeMotiveT R hc) :
    ConvProbeMotiveT R (.tyConv Γ M N A A' u hc hA) := ih

/-! ## Projection to landed probes and native chain consumers -/

theorem sortProbe_of_transportT {Γ : LCtx} {M N I : Expr Nat}
    (ht : ProbeTransportT R E n Γ M N)
    (hMM : LRSCoreT R E n Γ M M I .sort) :
    LRSCoreT R E n Γ M N I .sort := by
  rw [lrSCoreT_sort_iff] at hMM
  rw [lrSCoreT_sort_iff]
  obtain ⟨hi, u, _, hM, _⟩ := hMM
  obtain ⟨v, hN⟩ := ht.sorts ⟨u, hM⟩
  exact ⟨hi, u, v, hM, hN⟩

theorem piProbe_of_transportT {Γ : LCtx} {M N I : Expr Nat}
    (ht : ProbeTransportT R E n Γ M N)
    (hMM : LRSCoreT R E n Γ M M I (.pi .bot [])) :
    LRSCoreT R E n Γ M N I (.pi .bot []) := by
  rw [LRSCoreT.eq_def] at hMM
  rw [LRSCoreT.eq_def]
  obtain ⟨hi, A, B, _, _, hM, _, ⟨hΓA⟩, _⟩ := hMM
  obtain ⟨A', B', hN, hdom, hcod⟩ := ht.pis hM hΓA
  exact ⟨hi, A, B, A', B', hM, hN, ⟨hΓA⟩, hdom, hcod,
    ⟨.zero, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- The strengthened single-link input at sort-indexed native conversions.
This is a definition of the remaining obligation, not a proof of it. -/
def ProbeConvLinksT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M N : Expr Nat} {u : Level},
    (hc : ConvT E n Γ M N (.sort u)) → ConvProbeMotiveT R hc

theorem piProbeLinkT_of_probeConvLinksT (hlinks : ProbeConvLinksT R E n) :
    PiProbeLinkT R E n := by
  intro Γ hΓ M N u hc hMM
  exact piProbe_of_transportT (hlinks hΓ hc).1 hMM

/-- All three native `TyConvT` constructors compose the specified-witness
motive. No index transport, unique normal forms, or coherence is used. -/
theorem probeEquiv_chainT (hW : EnvWfT E) (hlinks : ProbeConvLinksT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (hc : TyConvT E n Γ A B) :
    ProbeEquivT R E n Γ A B := by
  induction hc with
  | refl => exact probeEquiv_reflT _ _
  | of A B u hc => exact hlinks hΓ hc
  | trans A B C _ _ ih₁ ih₂ => exact probeEquiv_transT hW hΓ ih₁ ih₂

theorem piProbe_chainT_noUnique (hW : EnvWfT E) (hlinks : ProbeConvLinksT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (hc : TyConvT E n Γ A B)
    {u : Level} (hAA : LRSCoreT R E n Γ A A (.sort u) (.pi .bot [])) :
    LRSCoreT R E n Γ A B (.sort u) (.pi .bot []) :=
  piProbe_of_transportT (probeEquiv_chainT hW hlinks hΓ hc).1 hAA

theorem sortProbe_chainT_noUnique (hW : EnvWfT E) (hlinks : ProbeConvLinksT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (hc : TyConvT E n Γ A B)
    {u : Level} (hAA : LRSCoreT R E n Γ A A (.sort u) .sort) :
    LRSCoreT R E n Γ A B (.sort u) .sort :=
  sortProbe_of_transportT (probeEquiv_chainT hW hlinks hΓ hc).1 hAA

/-- The native Pi-row consumer now needs only readback laws and the
specified-witness single links. Its typing seed and read-off are landed
#7721 declarations; the `TyConvT` composition above removes uniqueness. -/
theorem piRowField_of_probeConvLinksT (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : ProbeConvLinksT R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  cases tyConvT_firstOf_data hc with
  | inl heq =>
      rcases Expr.pi.inj heq with ⟨rfl, rfl⟩
      exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  | inr first =>
      obtain ⟨_, u, hfirst, _⟩ := first
      have hPi := (convEnds hW hΓ hfirst).1
      exact lrSCore_pi_components hL (piProbe_typed_iff.mp
        (piProbe_chainT_noUnique hW hlinks hΓ hc (piProbe_diagT_of_typing hΓ hPi)))

-- BEGIN RCIC_PI_PROBE_ALGEBRA_ROOTS
#print axioms piProbe_reindexT
#print axioms sortProbe_reindexT
#print axioms piProbe_index_iffT
#print axioms sortProbe_index_iffT
#print axioms sortProbe_symmT
#print axioms sortProbe_transT
#print axioms sortProbe_right_diagonalT
#print axioms sortProbe_reverse_link_iffT
#print axioms piProbe_left_diagonalT
#print axioms piProbe_right_diagonalT_noUnique
#print axioms piProbe_reverse_link_iffT
#print axioms piProbe_at_sort_of_old_indexT
#print axioms SortReadTransportT
#print axioms PiReadTransportT
#print axioms ProbeTransportT
#print axioms ProbeEquivT
#print axioms ConvProbeMotiveT
#print axioms probeTransport_reflT
#print axioms probeTransport_transT
#print axioms probeEquiv_reflT
#print axioms probeEquiv_symmT
#print axioms probeEquiv_transT
#print axioms probeTransport_of_readback_impT
#print axioms probeEquiv_of_readback_iffT
#print axioms probeTransport_of_no_wf_probesT
#print axioms probeTransport_of_no_probesT
#print axioms probeEquiv_of_no_probesT
#print axioms sortProbe_diagT
#print axioms pinPiProbeT
#print axioms convProbe_reflT
#print axioms convProbe_symmT
#print axioms convProbe_transT
#print axioms probeTransport_sortsT
#print axioms convProbe_sortsT
#print axioms probeTransport_piT
#print axioms convProbe_piT
#print axioms convProbe_tyConvT
#print axioms sortProbe_of_transportT
#print axioms piProbe_of_transportT
#print axioms ProbeConvLinksT
#print axioms piProbeLinkT_of_probeConvLinksT
#print axioms probeEquiv_chainT
#print axioms piProbe_chainT_noUnique
#print axioms sortProbe_chainT_noUnique
#print axioms piRowField_of_probeConvLinksT
-- END RCIC_PI_PROBE_ALGEBRA_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
