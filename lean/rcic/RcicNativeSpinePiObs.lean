import rcic.RcicNativeSpineHead
import rcic.RcicNativePiCongrAdequacy
import rcic.RcicNativeSpineHeadControl

set_option autoImplicit false

/-!
# Native Pi observations with certified application-spine traces

Only the trace interface is new: native component evidence is the existing
PiHeadObs at literal Pi endpoints. Its symmetry and dependent-binder
composition are reused. Middle heads are aligned by priority-trace
determinism, independently of typing uniqueness or confluence.

The constructions below cover supplied certified expansions and original
native congruence-fragment derivations. They do not turn an arbitrary
semantic equality or common compact into native component evidence.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.NativeSpineHead

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Concatenating original priority traces preserves the priority guard. -/
theorem SortTrace.priority_trans {s t v : Expr Nat}
    (left : SortTrace E n Γ s t) (right : SortTrace E n Γ t v)
    (hl : left.IsPriority) (hr : right.IsPriority) :
    (left.trans right).IsPriority := by
  induction left with
  | refl => exact hr
  | cons level first rest ih =>
      simp only [SortTrace.IsPriority] at hl
      simpa only [SortTrace.trans, SortTrace.IsPriority] using
        And.intro hl.1 (ih right hl.2 hr)

/-- Native endpoint traces with the existing literal-head evidence. -/
structure PiSpineObs (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (s t : Expr Nat) : Type where
  leftDom : Expr Nat
  leftCod : Expr Nat
  rightDom : Expr Nat
  rightCod : Expr Nat
  leftTrace : SortTrace E n Γ s (.pi leftDom leftCod)
  rightTrace : SortTrace E n Γ t (.pi rightDom rightCod)
  leftPriority : leftTrace.IsPriority
  rightPriority : rightTrace.IsPriority
  heads : NativePiHeadObs.PiHeadObs E n Γ
    (.pi leftDom leftCod) (.pi rightDom rightCod)

namespace PiSpineObs

def of_components {A B A' B' : Expr Nat}
    (hA : TyConvT E n Γ A A')
    (hB : TyConvT E n (.assumption A :: Γ) B B') :
    PiSpineObs E n Γ (.pi A B) (.pi A' B') :=
  ⟨A, B, A', B', .refl _, .refl _, True.intro, True.intro,
    NativePiHeadObs.PiHeadObs.of_components hA hB⟩

def refl (A B : Expr Nat) : PiSpineObs E n Γ (.pi A B) (.pi A B) :=
  of_components (.refl _ _) (.refl _ _)

/-- Endpoints' native certificates are computed from actual steps. -/
def leftCert {s t : Expr Nat} (h : PiSpineObs E n Γ s t) :
    TyConvT E n Γ s (.pi h.leftDom h.leftCod) :=
  h.leftTrace.toTyConv

def rightCert {s t : Expr Nat} (h : PiSpineObs E n Γ s t) :
    TyConvT E n Γ t (.pi h.rightDom h.rightCod) :=
  h.rightTrace.toTyConv

def symm (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {s t : Expr Nat}
    (h : PiSpineObs E n Γ s t) : PiSpineObs E n Γ t s :=
  ⟨h.rightDom, h.rightCod, h.leftDom, h.leftCod,
    h.rightTrace, h.leftTrace, h.rightPriority, h.leftPriority,
    h.heads.symm hW hΓ⟩

/-- The middle equality is proved from the two original finite traces;
the existing PiHeadObs.trans pays native codomain context transport. -/
def trans (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {s t u : Expr Nat}
    (left : PiSpineObs E n Γ s t) (right : PiSpineObs E n Γ t u) :
    PiSpineObs E n Γ s u := by
  cases left with
  | mk A B M N hl hm hpl hpm ch =>
      cases right with
      | mk M' N' C D hm' hr hpm' hpr ch' =>
          have he := hm.pi_unique hm' hpm hpm'
          obtain ⟨heA, heB⟩ := Expr.pi.inj he
          cases heA
          cases heB
          exact ⟨A, B, C, D, hl, hr, hpl, hpr, ch.trans hW hΓ ch'⟩

def expand_left {s s' t : Expr Nat} (trace : SortTrace E n Γ s s')
    (hp : trace.IsPriority) (h : PiSpineObs E n Γ s' t) :
    PiSpineObs E n Γ s t :=
  ⟨h.leftDom, h.leftCod, h.rightDom, h.rightCod,
    trace.trans h.leftTrace, h.rightTrace,
    trace.priority_trans h.leftTrace hp h.leftPriority,
    h.rightPriority, h.heads⟩

def expand_right {s t t' : Expr Nat} (trace : SortTrace E n Γ t t')
    (hp : trace.IsPriority) (h : PiSpineObs E n Γ s t') :
    PiSpineObs E n Γ s t :=
  ⟨h.leftDom, h.leftCod, h.rightDom, h.rightCod,
    h.leftTrace, trace.trans h.rightTrace, h.leftPriority,
    trace.priority_trans h.rightTrace hp h.rightPriority, h.heads⟩

/-- A supplied pair of native computations reuses the paid head observation. -/
def of_traces {s t A B A' B' : Expr Nat}
    (hl : SortTrace E n Γ s (.pi A B)) (hr : SortTrace E n Γ t (.pi A' B'))
    (hpl : hl.IsPriority) (hpr : hr.IsPriority)
    (heads : NativePiHeadObs.PiHeadObs E n Γ (.pi A B) (.pi A' B')) :
    PiSpineObs E n Γ s t :=
  ⟨A, B, A', B', hl, hr, hpl, hpr, heads⟩

def components {A B A' B' : Expr Nat}
    (h : PiSpineObs E n Γ (.pi A B) (.pi A' B')) :
    TyConvT E n Γ A A' × TyConvT E n (.assumption A :: Γ) B B' := by
  cases h with
  | mk X Y X' Y' hl hr hpl hpr heads =>
      have heL := (hl.toPriority hpl).eq_of_normal (literalPi_normal A B)
      have heR := (hr.toPriority hpr).eq_of_normal (literalPi_normal A' B')
      obtain ⟨hAX, hBY⟩ := Expr.pi.inj heL
      obtain ⟨hAX', hBY'⟩ := Expr.pi.inj heR
      cases hAX
      cases hBY
      cases hAX'
      cases hBY'
      exact heads.components

/-- The original TyConvT recursion was constructed in the fragment worker;
no semantic reflection supplier is used here. -/
def of_congrChain (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat}
    (c : TyConvT E n Γ (.pi A B) (.pi A' B'))
    (hc : NativePiCongrAdequacy.ChainCongrFrag c) :
    PiSpineObs E n Γ (.pi A B) (.pi A' B') :=
  let pair := NativePiCongrAdequacy.components_of_congrChain hW hΓ c hc
  of_components pair.1 pair.2

end PiSpineObs

/-- The previous root-only obstruction now has a constructed observation. -/
def spineObservation (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    PiSpineObs E n Γ NativeHeadAdequacyObstruction.spineSource NativePiHeadObs.betaPiHead :=
  PiSpineObs.expand_left (spineTrace hW hΓ) (spineTrace_isPriority hW hΓ)
    (PiSpineObs.refl (.sort .zero) (.sort .zero))

def admitted_spineObservation :
    PiSpineObs emptyEnv 0 [] NativeHeadAdequacyObstruction.spineSource NativePiHeadObs.betaPiHead :=
  spineObservation .empty .nil

/-- The context-aware counterpart of the closed beta-spine observation. -/
def localPiObservation (E : ResolvedEnv) (n : Nat) :
    PiSpineObs E n localPiCtx (.bvar 0) NativePiHeadObs.betaPiHead :=
  PiSpineObs.expand_left (localPiTrace E n) (localPiTrace_isPriority E n)
    (PiSpineObs.refl (.sort .zero) (.sort .zero))

end Rcic.Declarative.NativeValleys.NativeSpineHead
