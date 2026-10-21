import rcic.RcicF8JTotality
import rcic.RcicF8UAppDemand

/-!
# JT-1: demand at the actual U-app → X boundary

ChatGPT's design in `S0_UX_REENTRY_DEMAND.md` §1–3 extends the J-line
contract of #7194. This module composes the observed original U-app prefix
with an independently admitted entry for its exact supplied chain. The
direct U-app invocation is the root modeled here; no recursive U/D/S
availability or generated-origin theorem is asserted.

Every observed prefix is retained either as an admitted entry or as the
explicit `W-UX-REENTRY-CONTEXT/ADMISSION` gap. In particular, optional entry
evidence is never used to filter the reached-prefix ledger. The later
`appFinish` substitution re-entry remains a separate obligation.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure.JTotality

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- An actual direct literal-app arm invocation, with its original inputs. -/
structure UAppRoot (E : ResolvedEnv) (n : Nat) where
  R : List (Jd E n)
  Γ : LCtx
  a : Expr Nat
  A : Expr Nat
  B : Expr Nat
  hcl : EnvClosed E
  hinst : EnvMembersSubstStable E
  l : EvTy R Γ a A
  r : EvTy R Γ a B

abbrev UAppRoot.Await (root : UAppRoot E n) :=
  UAppAwaitX root.hcl root.hinst root.l root.r

def UAppRoot.pre (root : UAppRoot E n) :=
  uAppPre root.hcl root.hinst root.l root.r

/-- The modeled wrapper starts at this real U-app arm. Deeper wrapper
positions require their own execution-prefix constructors in later slices. -/
inductive ReachedU (root : UAppRoot E n) : List Nat → Prop where
  | root : ReachedU root []

/-- The chain is fixed by the observed original prefix. Neither field is
inferred from the two typings, nor from a successful X answer. -/
structure EntryForActualChain (root : UAppRoot E n) (p : root.Await) where
  context : CtxWfT E n root.Γ
  admission : xAdmW p.chain = true

def EntryForActualChain.entry {root : UAppRoot E n} {p : root.Await}
    (e : EntryForActualChain root p) : XEntryW E n :=
  ⟨root.R, root.Γ, p.left.Adom, p.left.Bcod, p.right.Adom, p.right.Bcod,
    p.chain, e.context, e.admission⟩

/-- A named outstanding obligation, retaining the exact observed prefix.
This is a ledger entry, not a proof that the context is ill formed. -/
structure WUXReentryContextAdmission (root : UAppRoot E n) (p : root.Await) where
  observed : root.pre = some p

def WUXReentryContextAdmission.name : String := "W-UX-REENTRY-CONTEXT/ADMISSION"

/-- No observed re-entry is discarded when independent evidence is absent. -/
inductive ReentryDisposition (root : UAppRoot E n) (p : root.Await) where
  | admitted (entry : EntryForActualChain root p)
  | gap (obligation : WUXReentryContextAdmission root p)

def retainActualReentry (root : UAppRoot E n) (p : root.Await)
    (hp : root.pre = some p) (e : Option (EntryForActualChain root p)) :
    ReentryDisposition root p :=
  match e with
  | some e => .admitted e
  | none => .gap ⟨hp⟩

theorem missing_entry_is_named_gap (root : UAppRoot E n) (p : root.Await)
    (hp : root.pre = some p) :
    retainActualReentry root p hp none = .gap ⟨hp⟩ := rfl

/-- Accounting is total over actual reached prefixes. A caller may record
an unresolved gap, but cannot omit that prefix from this ledger's domain. -/
abbrev ActualReentryLedger (root : UAppRoot E n) :=
  ∀ (α : List Nat) (p : root.Await), ReachedU root α →
    root.pre = some p → ReentryDisposition root p

def actualReentryLedger (root : UAppRoot E n)
    (entries : ∀ (α : List Nat) (p : root.Await), ReachedU root α →
      root.pre = some p → Option (EntryForActualChain root p)) :
    ActualReentryLedger root :=
  fun α p hr hp => retainActualReentry root p hp (entries α p hr hp)

def NoReentryGaps {root : UAppRoot E n} (ledger : ActualReentryLedger root) : Prop :=
  ∀ α p hr hp, ∃ e, ledger α p hr hp = .admitted e

/-- The request keeps the U prefix and the exact inner source identity. -/
structure UXRequestW (root : UAppRoot E n) where
  await : root.Await
  observed : root.pre = some await
  admission : EntryForActualChain root await
  request : JRequestW admission.entry

inductive UXPath (root : UAppRoot E n) where
  | uApp (outer : List Nat) (actualPrefix : root.Await) (inner : Path)

/-- ChatGPT's NeedUX rule, restricted to the actual direct root modeled
above. The actual prefix and the inner occurrence address both survive. -/
inductive NeedUX (root : UAppRoot E n) : UXPath root → UXRequestW root → Prop where
  | uApp {α : List Nat} (q : UXRequestW root) :
      ReachedU root α → NeedW q.admission.entry q.request →
      NeedUX root (.uApp α q.await q.request.path) q

/-- Exact wrapper acceptance includes entry coverage as a separate conjunct.
The demand quantifier alone would vacuously ignore unadmitted re-entries. -/
def ExactCompleteUX {root : UAppRoot E n} (ledger : ActualReentryLedger root)
    (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  NoReentryGaps ledger ∧
    ∀ position q, NeedUX root position q → (q.request.answer J).isSome = true

theorem named_gap_refuses_exactUX {root : UAppRoot E n}
    (ledger : ActualReentryLedger root) (α : List Nat) (p : root.Await)
    (hr : ReachedU root α) (hp : root.pre = some p)
    (gap : WUXReentryContextAdmission root p)
    (hgap : ledger α p hr hp = .gap gap)
    (J : ∀ R : List (Jd E n), JProcViaP R) : ¬ ExactCompleteUX ledger J := by
  intro h
  obtain ⟨e, he⟩ := h.1 α p hr hp
  rw [hgap] at he
  cases he

theorem needUX_before_X_answer {root : UAppRoot E n} {α : List Nat}
    (q : UXRequestW root) (hr : ReachedU root α)
    (hn : NeedW q.admission.entry q.request)
    (X : ∀ R : List (Jd E n), XProcP R) :
    NeedUX root (.uApp α q.await q.request.path) q ∧
      uAppX root.hcl root.hinst X root.l root.r =
        (X root.R q.await.chain).map q.await.finish := by
  refine ⟨.uApp q hr hn, ?_⟩
  exact (uAppAwaitX_independent_of_X root.hcl root.hinst q.await
    q.observed X X).1

theorem needUX_persists_when_X_refuses {root : UAppRoot E n} {α : List Nat}
    (q : UXRequestW root) (hr : ReachedU root α)
    (hn : NeedW q.admission.entry q.request)
    (X : ∀ R : List (Jd E n), XProcP R)
    (hX : X root.R q.await.chain = none) :
    NeedUX root (.uApp α q.await q.request.path) q ∧
      root.pre = some q.await ∧
      uAppX root.hcl root.hinst X root.l root.r = none := by
  obtain ⟨hd, he⟩ := needUX_before_X_answer q hr hn X
  exact ⟨hd, q.observed, by rw [he, hX]; rfl⟩

/-- The same demand boundary belongs to the original UProcX dispatch,
including when its X callback will refuse. The independent recursive U
callback supplies no evidence for the request or the actual chain. -/
theorem needUX_before_original_U_answer {root : UAppRoot E n} {α : List Nat}
    (q : UXRequestW root) (hr : ReachedU root α)
    (hn : NeedW q.admission.entry q.request)
    (X : ∀ R : List (Jd E n), XProcP R)
    (U : ∀ R : List (Jd E n), UProc R) :
    NeedUX root (.uApp α q.await q.request.path) q ∧
      UProcX root.hcl root.hinst X U root.R root.l root.r =
        (X root.R q.await.chain).map q.await.finish :=
  ⟨.uApp q hr hn,
    UProcX_eq_uAppPre_of_await root.hcl root.hinst X U q.await q.observed⟩

theorem needUX_persists_when_original_U_refuses
    {root : UAppRoot E n} {α : List Nat}
    (q : UXRequestW root) (hr : ReachedU root α)
    (hn : NeedW q.admission.entry q.request)
    (X : ∀ R : List (Jd E n), XProcP R)
    (U : ∀ R : List (Jd E n), UProc R)
    (hX : X root.R q.await.chain = none) :
    NeedUX root (.uApp α q.await q.request.path) q ∧
      root.pre = some q.await ∧
      UProcX root.hcl root.hinst X U root.R root.l root.r = none := by
  obtain ⟨hd, he⟩ := needUX_before_original_U_answer q hr hn X U
  exact ⟨hd, q.observed, by rw [he, hX]; rfl⟩

/-- Composition of the real U prefix and the admitted exact-chain X
worker's pre-J prefix. This does not assert arbitrary X callbacks use
this worker; that supplier bridge remains an independent obligation. -/
theorem issued_UX_J_before_J_answer {root : UAppRoot E n} {α : List Nat}
    (q : UXRequestW root) (hr : ReachedU root α)
    (X : SuppliersVia E n) (π : PrefixW q.admission.entry)
    (hi : IssuedBeforeAnswer X q.admission.entry π q.request) :
    NeedUX root (.uApp α q.await q.request.path) q ∧
      IssuedBeforeAnswer X q.admission.entry π q.request :=
  ⟨.uApp q hr (issued_before_answer_is_needed hi), hi⟩

end Rcic.Declarative.F8Measure.JTotality

#print axioms Rcic.Declarative.F8Measure.JTotality.needUX_before_X_answer
#print axioms Rcic.Declarative.F8Measure.JTotality.needUX_persists_when_X_refuses
#print axioms Rcic.Declarative.F8Measure.JTotality.issued_UX_J_before_J_answer
#print axioms Rcic.Declarative.F8Measure.JTotality.named_gap_refuses_exactUX
#print axioms Rcic.Declarative.F8Measure.JTotality.needUX_before_original_U_answer
#print axioms Rcic.Declarative.F8Measure.JTotality.needUX_persists_when_original_U_refuses
