import rcic.RcicNativePiHeadRootCases
import rcic.RcicNativeCertifiedK
import rcic.RcicCoherentCanonical

set_option autoImplicit false

/-!
# Certified head computation with application-spine congruence

Every step has a native certificate. Application descent constructs its
certificate with ConvT.app and a reflexive argument. Supplemental K roots
reuse CStepK, without a raw-to-native lift. The deterministic strategy uses
the existing guarded HeadStepT roots before application descent; it excludes
supplemental K/eta-K roots. No confluence or normalization is claimed.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.NativeSpineHead

/-- Recognizes only the existing two K constructors. -/
def IsKRoot {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {s t T : Expr Nat}
    (p : ParRedT (ProofLeaf E n) E n Γ s t T) : Prop :=
  match p with
  | .iotaStarK .. => True
  | .iotaStarKEta .. => True
  | _ => False

inductive Step (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Type where
  | root {s t T : Expr Nat} (head : HeadStepT E n Γ s t T)
      (cert : ConvT E n Γ s t T) : Step E n Γ s t T
  | appHead {f g a A B : Expr Nat} (fn : Step E n Γ f g (.pi A B))
      (arg : HasTyT E n Γ a A) :
      Step E n Γ (.app f a) (.app g a) (instantiate0 a B)
  | localZeta (i : Nat) (A v : Expr Nat)
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : HasTyT E n Γ v A) : Step E n Γ (.bvar i) v A
  | kRoot {s t T : Expr Nat} (step : CStepK E n (ProofLeaf E n) Γ s t T)
      (kind : IsKRoot step.step) : Step E n Γ s t T

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- The recursive argument is the original function step. -/
def Step.toConv {s t T : Expr Nat} (h : Step E n Γ s t T) :
    ConvT E n Γ s t T :=
  match h with
  | .root _ cert => cert
  | .appHead fn arg => .app Γ _ _ _ _ _ _ fn.toConv (.refl Γ _ _ arg)
  | .localZeta i A v hval hty hv => .zetaLocal Γ i A v hval hty hv
  | .kRoot step _ => step.toConvT

def Step.toTyConv {s t : Expr Nat} {u : Level}
    (h : Step E n Γ s t (.sort u)) : TyConvT E n Γ s t :=
  .of Γ s t u h.toConv

/-- General beta, including a function-valued result index. Extra head
typing fields come from native regularity and native endpoint validity. -/
def Step.beta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (A body arg B : Expr Nat) (u : Level)
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    Step E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B) := by
  let c : ConvT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B) :=
    .beta Γ A body arg B u hA hbody harg
  let hΓA : CtxWfT E n (.assumption A :: Γ) :=
    .assumption Γ A u hΓ hA
  let bodySort := tySort hW hΓA hbody
  let ends := convEnds hW hΓ c
  exact .root (.beta Γ A body arg B u bodySort.1 ends.2.2.1
    hA bodySort.2 ends.2.2.2 hbody harg ends.2.1) c

inductive Trace (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Type where
  | refl {s T : Expr Nat} (typed : HasTyT E n Γ s T) : Trace E n Γ s s T
  | single {s t T : Expr Nat} (step : Step E n Γ s t T) : Trace E n Γ s t T
  | trans {s t v T : Expr Nat} (left : Trace E n Γ s t T)
      (right : Trace E n Γ t v T) : Trace E n Γ s v T

def Trace.toConv {s t T : Expr Nat} (h : Trace E n Γ s t T) :
    ConvT E n Γ s t T :=
  match h with
  | .refl typed => .refl Γ _ _ typed
  | .single step => step.toConv
  | .trans left right => .trans Γ _ _ _ _ left.toConv right.toConv

def Trace.cons {s t v T : Expr Nat} (first : Step E n Γ s t T)
    (rest : Trace E n Γ t v T) : Trace E n Γ s v T :=
  .trans (.single first) rest

/-- Successive type steps retain independent universe levels. -/
inductive SortTrace (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Type where
  | refl (s : Expr Nat) : SortTrace E n Γ s s
  | cons {s t v : Expr Nat} (level : Level)
      (first : Step E n Γ s t (.sort level))
      (rest : SortTrace E n Γ t v) : SortTrace E n Γ s v

def SortTrace.single {s t : Expr Nat} {u : Level}
    (h : Step E n Γ s t (.sort u)) : SortTrace E n Γ s t :=
  .cons u h (.refl t)

def SortTrace.trans {s t v : Expr Nat} (left : SortTrace E n Γ s t)
    (right : SortTrace E n Γ t v) : SortTrace E n Γ s v :=
  match left with
  | .refl _ => right
  | .cons level first rest => .cons level first (rest.trans right)

def SortTrace.toTyConv {s t : Expr Nat} (h : SortTrace E n Γ s t) :
    TyConvT E n Γ s t :=
  match h with
  | .refl s => .refl Γ s
  | .cons level first rest =>
      .trans Γ _ _ _ (.of Γ _ _ level first.toConv) rest.toTyConv

/-- Reuses all already constructed sorting-indexed root packages. -/
def SortTrace.ofSortHeadStep {s t : Expr Nat}
    (h : NativePiHeadObs.SortHeadStep E n Γ s t) : SortTrace E n Γ s t :=
  .single (.root h.step h.cert)

private theorem bvar_no_root {i : Nat} {z T : Expr Nat}
    (h : HeadStepT E n Γ (.bvar i) z T) : False :=
  headStepT_inv_rigid h
    (fun _ _ he => Expr.noConfusion he)
    (fun _ _ he => Expr.noConfusion he)
    (fun _ _ _ he => Expr.noConfusion he)
    (fun _ he => Expr.noConfusion he)

inductive PriorityStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Type where
  | root {s t T : Expr Nat} (head : HeadStepT E n Γ s t T) :
      PriorityStep E n Γ s t
  | localZeta {i : Nat} {v : Expr Nat} (hval : lookupValue Γ i = some v) :
      PriorityStep E n Γ (.bvar i) v
  | appHead {f g a : Expr Nat}
      (none : NativePiHeadObs.HeadNormal E n Γ (.app f a))
      (fn : PriorityStep E n Γ f g) :
      PriorityStep E n Γ (.app f a) (.app g a)

/-- Root comparison uses headStepT_det across independent type indices. -/
theorem PriorityStep.deterministic {s t v : Expr Nat}
    (left : PriorityStep E n Γ s t) (right : PriorityStep E n Γ s v) : t = v := by
  induction left generalizing v with
  | root head =>
      cases right with
      | root other => exact headStepT_det head other
      | localZeta _ => exact (bvar_no_root head).elim
      | appHead none _ => exact (none head).elim
  | localZeta hv =>
      cases right with
      | root other => exact (bvar_no_root other).elim
      | localZeta hw => exact Option.some.inj (hv.symm.trans hw)
  | @appHead f g a none fn ih =>
      cases right with
      | root other => exact (none other).elim
      | appHead _ other => exact congrArg (fun x : Expr Nat => Expr.app x a) (ih other)

def Step.IsPriority {s t T : Expr Nat} (h : Step E n Γ s t T) : Prop :=
  match h with
  | .root _ _ => True
  | .localZeta .. => True
  | .appHead fn _ => NativePiHeadObs.HeadNormal E n Γ s ∧ fn.IsPriority
  | .kRoot _ _ => False

def Step.toPriority {s t T : Expr Nat} (h : Step E n Γ s t T) :
    h.IsPriority → PriorityStep E n Γ s t :=
  match h with
  | .root head _ => fun _ => .root head
  | .localZeta _ _ _ hval _ _ => fun _ => .localZeta hval
  | .appHead fn _ => by
      intro hp
      simp only [Step.IsPriority] at hp
      exact .appHead hp.1 (fn.toPriority hp.2)
  | .kRoot _ _ => by
      intro hp
      exact False.elim (by simpa only [Step.IsPriority] using hp)

inductive PriorityTrace (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Type where
  | refl (s : Expr Nat) : PriorityTrace E n Γ s s
  | cons {s t v : Expr Nat} (first : PriorityStep E n Γ s t)
      (rest : PriorityTrace E n Γ t v) : PriorityTrace E n Γ s v

def Normal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (s : Expr Nat) : Prop :=
  ∀ t, PriorityStep E n Γ s t → False

theorem PriorityTrace.eq_of_normal {s t : Expr Nat}
    (trace : PriorityTrace E n Γ s t) (hs : Normal E n Γ s) : s = t := by
  cases trace with
  | refl => rfl
  | cons step _ => exact (hs _ step).elim

/-- Recursion compares the two original tails, never a produced trace. -/
theorem PriorityTrace.normal_unique {s t : Expr Nat}
    (left : PriorityTrace E n Γ s t) :
    ∀ {v : Expr Nat}, PriorityTrace E n Γ s v →
      Normal E n Γ t → Normal E n Γ v → t = v := by
  induction left with
  | refl =>
      intro v right nt _
      exact right.eq_of_normal nt
  | cons first rest ih =>
      intro v right nt nv
      cases right with
      | refl => exact (nv _ first).elim
      | cons first' rest' =>
          have same := first.deterministic first'
          cases same
          exact ih rest' nt nv

def SortTrace.IsPriority {s t : Expr Nat} (h : SortTrace E n Γ s t) : Prop :=
  match h with
  | .refl _ => True
  | .cons _ first rest => first.IsPriority ∧ rest.IsPriority

def SortTrace.toPriority {s t : Expr Nat} (h : SortTrace E n Γ s t) :
    h.IsPriority → PriorityTrace E n Γ s t :=
  match h with
  | .refl _ => fun _ => .refl _
  | .cons _ first rest => by
      intro hp
      simp only [SortTrace.IsPriority] at hp
      exact .cons (first.toPriority hp.1) (rest.toPriority hp.2)

theorem PriorityStep.no_pi {A B t : Expr Nat}
    (step : PriorityStep E n Γ (.pi A B) t) : False := by
  cases step with
  | root head => exact NativePiHeadObs.pi_headNormal A B head

theorem literalPi_normal (A B : Expr Nat) : Normal E n Γ (.pi A B) :=
  fun _ step => step.no_pi

theorem SortTrace.pi_unique {s A B C D : Expr Nat}
    (left : SortTrace E n Γ s (.pi A B))
    (right : SortTrace E n Γ s (.pi C D))
    (leftPriority : left.IsPriority) (rightPriority : right.IsPriority) :
    Expr.pi A B = Expr.pi C D :=
  (left.toPriority leftPriority).normal_unique
    (right.toPriority rightPriority) (literalPi_normal A B) (literalPi_normal C D)

end Rcic.Declarative.NativeValleys.NativeSpineHead
