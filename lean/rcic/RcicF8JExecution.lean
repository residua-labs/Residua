import rcic.RcicF8DAddresses

/-!
G0 execution inputs and original J call positions.
Design: ChatGPT, `IMPLEMENTATION_D_GENERATED_PROVENANCE.md` (#7203).
Outputs are computed by the landed J5a worker. Positions follow only its
original recursive children; the local trans caller, top caller and ambient
roots remain separate. No generated provenance or total J is asserted.
closure_claim=0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JExecution

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Original input data, independent of worker success or a supplied output. -/
structure JInput (E : ResolvedEnv) (n : Nat) (R : List (Jd E n)) where
  ctx : LCtx
  left : Expr Nat
  right : Expr Nat
  index : Expr Nat
  ctxWf : CtxWfT E n ctx
  literal : ConvT E n ctx left right index
  admitted : J5a.fragment literal = true
  source : ∃ r ∈ R, SubEq (.cv literal) r

/-- The whole result is the actual worker call, with SortUnique explicit. -/
def JInput.result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) : J3.Result hW R i.literal :=
  J5a.buildFragment hW su R i.ctxWf i.literal i.admitted i.source

/-- Addresses of only the recursive original J calls, at one fixed context.
The selected type index can change when entering a tyConv body. -/
inductive JCallPos {Γ : LCtx} {a₀ b₀ T₀ : Expr Nat}
    (h₀ : ConvT E n Γ a₀ b₀ T₀) :
    {a b T : Expr Nat} → ConvT E n Γ a b T → Type where
  | root : JCallPos h₀ h₀
  | symmBody {a b T : Expr Nat} {h : ConvT E n Γ a b T} :
      JCallPos h₀ (.symm Γ a b T h) → JCallPos h₀ h
  | tyConvBody {a b T U : Expr Nat} {u : Level}
      {h : ConvT E n Γ a b T} {hT : ConvT E n Γ T U (.sort u)} :
      JCallPos h₀ (.tyConv Γ a b T U u h hT) → JCallPos h₀ h
  | transLeft {a b c T : Expr Nat}
      {h₁ : ConvT E n Γ a b T} {h₂ : ConvT E n Γ b c T} :
      JCallPos h₀ (.trans Γ a b c T h₁ h₂) → JCallPos h₀ h₁
  | transRight {a b c T : Expr Nat}
      {h₁ : ConvT E n Γ a b T} {h₂ : ConvT E n Γ b c T} :
      JCallPos h₀ (.trans Γ a b c T h₁ h₂) → JCallPos h₀ h₂

namespace JCallPos

variable {Γ : LCtx} {a₀ b₀ T₀ a b T : Expr Nat}
variable {h₀ : ConvT E n Γ a₀ b₀ T₀} {h : ConvT E n Γ a b T}

/-- Fragment membership follows the actual recursive call path. -/
def admitted (p : JCallPos h₀ h) (hf : J5a.fragment h₀ = true) :
    J5a.fragment h = true := by
  induction p with
  | root => exact hf
  | symmBody _ ih => exact ih
  | tyConvBody _ ih => exact ih
  | transLeft _ ih => exact (Bool.and_eq_true_iff.mp ih).1
  | transRight _ ih => exact (Bool.and_eq_true_iff.mp ih).2

/-- Source certificates use the same child inheritance as buildFragment. -/
def source (p : JCallPos h₀ h) (hs : ∃ r ∈ R, SubEq (.cv h₀) r) :
    ∃ r ∈ R, SubEq (.cv h) r := by
  induction p with
  | root => exact hs
  | @symmBody a b T h _ ih =>
      exact certOfChild (y := .cv (.symm Γ a b T h)) (.head _) ih
  | @tyConvBody a b T U u h hT _ ih =>
      exact certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) ih
  | @transLeft a b c T h₁ h₂ _ ih =>
      exact certOfChild (y := .cv (.trans Γ a b c T h₁ h₂)) (.head _) ih
  | @transRight a b c T h₁ h₂ _ ih =>
      exact certOfChild (y := .cv (.trans Γ a b c T h₁ h₂)) (.tail _ (.head _)) ih

/-- The selected literal's certificate to the original top literal. -/
def topSource (p : JCallPos h₀ h) :
    ∃ r ∈ [.cv h₀], SubEq (.cv h) r :=
  p.source ⟨.cv h₀, .head _, .inl rfl⟩

/-- Caller lifting is induced by the real ancestry, independently of ambient R. -/
def callerUp (p : JCallPos h₀ h) :
    ∀ x ∈ [.cv h], ∃ y ∈ [.cv h₀], SubEq x y := by
  intro x hx
  have heq := List.mem_singleton.mp hx
  subst x
  exact p.topSource

/-- Reify the selected original call without accepting any result data. -/
def input (i : JInput E n R) {a b T : Expr Nat}
    {h : ConvT E n i.ctx a b T} (p : JCallPos i.literal h) : JInput E n R where
  ctx := i.ctx
  left := a
  right := b
  index := T
  ctxWf := i.ctxWf
  literal := h
  admitted := p.admitted i.admitted
  source := p.source i.source

/-- The selected call's actual buildFragment output. -/
def result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) {a b T : Expr Nat} {h : ConvT E n i.ctx a b T}
    (p : JCallPos i.literal h) : J3.Result hW R h :=
  (p.input i).result hW su

theorem result_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) {a b T : Expr Nat} {h : ConvT E n i.ctx a b T}
    (p : JCallPos i.literal h) :
    p.result hW su i = J5a.buildFragment hW su R i.ctxWf h
      (p.admitted i.admitted) (p.source i.source) := rfl

end JCallPos

/-- An original trans call selected by its actual J ancestry. -/
structure TransCall (i : JInput E n R) where
  a : Expr Nat
  middle : Expr Nat
  c : Expr Nat
  T : Expr Nat
  h₁ : ConvT E n i.ctx a middle T
  h₂ : ConvT E n i.ctx middle c T
  atCall : JCallPos i.literal (.trans i.ctx a middle c T h₁ h₂)

namespace TransCall

variable {i : JInput E n R}

def literal (F : TransCall i) : ConvT E n i.ctx F.a F.c F.T :=
  .trans i.ctx F.a F.middle F.c F.T F.h₁ F.h₂

def localCaller (F : TransCall i) : List (Jd E n) := [.cv F.literal]

def topCaller (_F : TransCall i) : List (Jd E n) := [.cv i.literal]

def callerUp (F : TransCall i) :
    ∀ x ∈ F.localCaller, ∃ y ∈ F.topCaller, SubEq x y :=
  F.atCall.callerUp

def leftPos (F : TransCall i) : JCallPos i.literal F.h₁ := .transLeft F.atCall

def rightPos (F : TransCall i) : JCallPos i.literal F.h₂ := .transRight F.atCall

def p₁ (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) : J3.Result hW R F.h₁ := F.leftPos.result hW su i

def p₂ (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) : J3.Result hW R F.h₂ := F.rightPos.result hW su i

/-- The first D input starts at the original middle, at the original index. -/
def dLeft (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (F : TransCall i) :
    EvParStar R i.ctx F.middle (F.p₁ hW su).valley.N F.T :=
  (F.p₁ hW su).valley.right

/-- The second D input has the same original source and index. -/
def dRight (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (F : TransCall i) :
    EvParStar R i.ctx F.middle (F.p₂ hW su).valley.N F.T :=
  (F.p₂ hW su).valley.left

/-- D is called by the landed connector on these two computed child results. -/
def K (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (F : TransCall i) :=
  J5a.callD hW su i.ctxWf (F.p₁ hW su) (F.p₂ hW su)

theorem dRoot_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) :
    F.K hW su = dProcWf (R := R) hW su i.ctxWf (F.dLeft hW su) (F.dRight hW su) :=
  J5a.callD_exact hW su i.ctxWf (F.p₁ hW su) (F.p₂ hW su)

/-- The selected trans output is the whole actual transResult, not just its Valley. -/
theorem result_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) :
    F.atCall.result hW su i = J5a.transResult hW su i.ctxWf
      (F.p₁ hW su) (F.p₂ hW su) := by
  rfl

theorem children_edge (F : TransCall i) (Z : List (Jd E n)) :
    OM3_edge (F.localCaller ++ Z) ([.cv F.h₁, .cv F.h₂] ++ Z) :=
  J5a.children_edge F.h₁ F.h₂ Z

theorem d_call_edge (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) (Z : List (Jd E n)) :
    OM3_edge (F.localCaller ++ Z)
      (((F.dLeft hW su).leaves ++ (F.dRight hW su).leaves) ++ Z) :=
  J5a.d_call_edge (F.p₁ hW su) (F.p₂ hW su) Z

end TransCall

open DAddresses

/-- A step position in either leg of the whole actual J result. -/
inductive OutputPos (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) : Type where
  | left (p : StarPos ((i.result hW su).valley.left.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))) :
      OutputPos hW su i
  | right (p : StarPos ((i.result hW su).valley.right.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))) :
      OutputPos hW su i

def OutputPos.selected {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
    {i : JInput E n R} : OutputPos hW su i → MaterialStep E n i.ctx i.index
  | .left p => p.selected
  | .right p => p.selected

/-- Read the certificate stored at this exact final output address. -/
def OutputPos.certificate {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
    {i : JInput E n R} (o : OutputPos hW su i) :
    J3.StepCertificate R [.cv i.literal] o.selected.step :=
  match o with
  | .left p => p.certificate (i.result hW su).leftTiles
  | .right p => p.certificate (i.result hW su).rightTiles

namespace JCallPos

/-- Canonical partial route from a child output to the whole original output.
The other child leg is consumed by D and has no direct ancestor embedding:
left-child right and right-child left return none. G2 must trace those legs
through the actual D execution, rather than assert their final inclusion. -/
def liftOutput (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) :
    {a b T : Expr Nat} → {h : ConvT E n i.ctx a b T} →
    (p : JCallPos i.literal h) → OutputPos hW su (p.input i) →
      Option (OutputPos hW su i)
  | _, _, _, _, .root, o => some o
  | _, _, _, _, .symmBody p, .left o => liftOutput hW su i p (.right o)
  | _, _, _, _, .symmBody p, .right o => liftOutput hW su i p (.left o)
  | _, _, _, _, .tyConvBody (u := u) (hT := hT) p, .left o =>
      liftOutput hW su i p (.left (o.reindex
        ((J3.indexField u hT (p.source i.source)).val
          (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))))
  | _, _, _, _, .tyConvBody (u := u) (hT := hT) p, .right o =>
      liftOutput hW su i p (.right (o.reindex
        ((J3.indexField u hT (p.source i.source)).val
          (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))))
  | _, _, _, _, .transLeft (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .left o =>
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      liftOutput hW su i p (.left (o.spliceLeft
        ((J5a.readOutput (F.K hW su).2.1).val
          (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))))
  | _, _, _, _, .transLeft _, .right _ => none
  | _, _, _, _, .transRight _, .left _ => none
  | _, _, _, _, .transRight (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .right o =>
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      liftOutput hW su i p (.right (o.spliceLeft
        ((J5a.readOutput (F.K hW su).2.2).val
          (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))))

/-- The exact step transformation along original ancestry. Only tyConv adds
an existing ParRedT.conv wrapper; the other surviving branches reposition. -/
def transportStep (hW : EnvWfT E) (i : JInput E n R) :
    {a b T : Expr Nat} → {h : ConvT E n i.ctx a b T} →
    (p : JCallPos i.literal h) → MaterialStep E n i.ctx T →
      MaterialStep E n i.ctx i.index
  | _, _, _, _, .root, s => s
  | _, _, _, _, .symmBody p, s => transportStep hW i p s
  | _, _, _, _, .tyConvBody (u := u) (hT := hT) p, s =>
      transportStep hW i p (s.reindex
        ((J3.indexField u hT (p.source i.source)).val
          (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)))
  | _, _, _, _, .transLeft p, s => transportStep hW i p s
  | _, _, _, _, .transRight p, s => transportStep hW i p s

/-- The actual certificate operations of the original worker, along the same
ancestry as transportStep. Caller changes use the corresponding original
child edge; tyConv uses the existing StepCertificate.reindex operation. -/
def transportCertificate (hW : EnvWfT E) (i : JInput E n R) :
    {a b T : Expr Nat} → {h : ConvT E n i.ctx a b T} →
    (p : JCallPos i.literal h) → (s : MaterialStep E n i.ctx T) →
    J3.StepCertificate R [.cv h] s.step →
      J3.StepCertificate R [.cv i.literal] (p.transportStep hW i s).step
  | _, _, _, _, .root, _, c => c
  | _, _, _, _, .symmBody (a := a) (b := b) (T := T) (h := h) p, s, c =>
      transportCertificate hW i p s (c.recaller
        (J3.callerOfChild (y := .cv (.symm i.ctx a b T h)) (.head _)))
  | _, _, _, _, .tyConvBody (a := a) (b := b) (T := T) (U := U)
      (u := u) (h := h) (hT := hT) p, s, c =>
      let tc := (J3.indexField u hT (p.source i.source)).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      transportCertificate hW i p (s.reindex tc)
        ((c.recaller (J3.callerOfChild
          (y := .cv (.tyConv i.ctx a b T U u h hT)) (.head _))).reindex tc)
  | _, _, _, _, .transLeft (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, s, cert =>
      transportCertificate hW i p s (cert.recaller (J3.callerOfChild
        (y := .cv (.trans i.ctx a b c T h₁ h₂)) (.head _)))
  | _, _, _, _, .transRight (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, s, cert =>
      transportCertificate hW i p s (cert.recaller (J3.callerOfChild
        (y := .cv (.trans i.ctx a b c T h₁ h₂)) (.tail _ (.head _))))

/-- Transport respects equality of a packed step and its exact certificate. -/
theorem transportCertificate_congr (hW : EnvWfT E) (i : JInput E n R)
    {a b T : Expr Nat} {h : ConvT E n i.ctx a b T}
    (p : JCallPos i.literal h) {s t : MaterialStep E n i.ctx T}
    (hs : s = t) {cs : J3.StepCertificate R [.cv h] s.step}
    {ct : J3.StepCertificate R [.cv h] t.step} (hc : HEq cs ct) :
    HEq (p.transportCertificate hW i s cs) (p.transportCertificate hW i t ct) := by
  cases hs
  cases hc
  rfl

/-- Every successful partial route selects precisely the transformed local
proof object in the whole actual output, including every index wrapper. -/
theorem liftOutput_selected (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) :
    {a b T : Expr Nat} → {h : ConvT E n i.ctx a b T} →
    (p : JCallPos i.literal h) → (o : OutputPos hW su (p.input i)) →
    (dst : OutputPos hW su i) → liftOutput hW su i p o = some dst →
      dst.selected = p.transportStep hW i o.selected
  | _, _, _, _, .root, o, dst, heq => by
      cases heq
      rfl
  | _, _, _, _, .symmBody p, .left o, dst, heq =>
      liftOutput_selected hW su i p (.right o) dst heq
  | _, _, _, _, .symmBody p, .right o, dst, heq =>
      liftOutput_selected hW su i p (.left o) dst heq
  | _, _, _, _, .tyConvBody (u := u) (hT := hT) p, .left o, dst, heq => by
      let tc := (J3.indexField u hT (p.source i.source)).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      have hi := liftOutput_selected hW su i p (.left (o.reindex tc)) dst heq
      exact hi.trans (congrArg (p.transportStep hW i) (o.reindex_exact tc))
  | _, _, _, _, .tyConvBody (u := u) (hT := hT) p, .right o, dst, heq => by
      let tc := (J3.indexField u hT (p.source i.source)).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      have hi := liftOutput_selected hW su i p (.right (o.reindex tc)) dst heq
      exact hi.trans (congrArg (p.transportStep hW i) (o.reindex_exact tc))
  | _, _, _, _, .transLeft (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .left o, dst, heq => by
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      let ys := (J5a.readOutput (F.K hW su).2.1).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      have hi := liftOutput_selected hW su i p (.left (o.spliceLeft ys)) dst heq
      exact hi.trans (congrArg (p.transportStep hW i) (o.spliceLeft_exact ys))
  | _, _, _, _, .transLeft _, .right _, _, heq => by cases heq
  | _, _, _, _, .transRight _, .left _, _, heq => by cases heq
  | _, _, _, _, .transRight (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .right o, dst, heq => by
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      let ys := (J5a.readOutput (F.K hW su).2.2).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      have hi := liftOutput_selected hW su i p (.right (o.spliceLeft ys)) dst heq
      exact hi.trans (congrArg (p.transportStep hW i) (o.spliceLeft_exact ys))

/-- A successful output route extracts precisely the certificate transformed
by the actual worker's swap, reindex and surviving trans-prefix operations. -/
theorem liftOutput_certificate_exact (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) (i : JInput E n R) :
    {a b T : Expr Nat} → {h : ConvT E n i.ctx a b T} →
    (p : JCallPos i.literal h) → (o : OutputPos hW su (p.input i)) →
    (dst : OutputPos hW su i) → liftOutput hW su i p o = some dst →
      HEq dst.certificate
        (p.transportCertificate hW i o.selected o.certificate)
  | _, _, _, _, .root, _, _, heq => by
      cases heq
      rfl
  | _, _, _, _, .symmBody (a := a) (b := b) (T := T) (h := h) p,
      .left o, dst, heq => by
      let hXY := J3.callerOfChild (y := .cv (.symm i.ctx a b T h)) (.head _)
      have hi := liftOutput_certificate_exact hW su i p (.right o) dst heq
      have hc := o.recaller_certificate_exact hXY
        (((JCallPos.symmBody p).input i).result hW su).leftTiles
      exact hi.trans (transportCertificate_congr hW i p rfl hc)
  | _, _, _, _, .symmBody (a := a) (b := b) (T := T) (h := h) p,
      .right o, dst, heq => by
      let hXY := J3.callerOfChild (y := .cv (.symm i.ctx a b T h)) (.head _)
      have hi := liftOutput_certificate_exact hW su i p (.left o) dst heq
      have hc := o.recaller_certificate_exact hXY
        (((JCallPos.symmBody p).input i).result hW su).rightTiles
      exact hi.trans (transportCertificate_congr hW i p rfl hc)
  | _, _, _, _, .tyConvBody (a := a) (b := b) (T := T) (U := U)
      (u := u) (h := h) (hT := hT) p, .left o, dst, heq => by
      let tc := (J3.indexField u hT (p.source i.source)).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      let hXY := J3.callerOfChild
        (y := .cv (.tyConv i.ctx a b T U u h hT)) (.head _)
      let child := ((JCallPos.tyConvBody p).input i).result hW su
      have hi := liftOutput_certificate_exact hW su i p (.left (o.reindex tc)) dst heq
      have hc₁ := o.reindex_certificate_exact tc
        (J3.Certified.recaller hXY _ child.leftTiles)
      have hc₂ := o.recaller_certificate_exact hXY child.leftTiles
      have hc := hc₁.trans (heq_of_eq (congrArg (fun c => c.reindex tc) (eq_of_heq hc₂)))
      exact hi.trans (transportCertificate_congr hW i p (o.reindex_exact tc) hc)
  | _, _, _, _, .tyConvBody (a := a) (b := b) (T := T) (U := U)
      (u := u) (h := h) (hT := hT) p, .right o, dst, heq => by
      let tc := (J3.indexField u hT (p.source i.source)).val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
      let hXY := J3.callerOfChild
        (y := .cv (.tyConv i.ctx a b T U u h hT)) (.head _)
      let child := ((JCallPos.tyConvBody p).input i).result hW su
      have hi := liftOutput_certificate_exact hW su i p (.right (o.reindex tc)) dst heq
      have hc₁ := o.reindex_certificate_exact tc
        (J3.Certified.recaller hXY _ child.rightTiles)
      have hc₂ := o.recaller_certificate_exact hXY child.rightTiles
      have hc := hc₁.trans (heq_of_eq (congrArg (fun c => c.reindex tc) (eq_of_heq hc₂)))
      exact hi.trans (transportCertificate_congr hW i p (o.reindex_exact tc) hc)
  | _, _, _, _, .transLeft (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .left o, dst, heq => by
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      let hcl := envClosed_of_envWfT hW
      let hinst := envMembersSubstStable_of_envWfT hW
      let ys := (J5a.readOutput (F.K hW su).2.1).val hcl hinst
      let hXY := J3.callerOfChild (y := .cv F.literal) (.head _)
      have hi := liftOutput_certificate_exact hW su i p (.left (o.spliceLeft ys)) dst heq
      have hc₁ := o.spliceLeft_certificate_exact ys
        (J3.Certified.recaller hXY _ (F.p₁ hW su).leftTiles)
        (J5a.readOutput_certified hcl hinst [.cv F.literal] (F.K hW su).2.1)
      have hc₂ := o.recaller_certificate_exact hXY (F.p₁ hW su).leftTiles
      exact hi.trans (transportCertificate_congr hW i p (o.spliceLeft_exact ys)
        (hc₁.trans hc₂))
  | _, _, _, _, .transLeft _, .right _, _, heq => by cases heq
  | _, _, _, _, .transRight _, .left _, _, heq => by cases heq
  | _, _, _, _, .transRight (a := a) (b := b) (c := c) (T := T)
      (h₁ := h₁) (h₂ := h₂) p, .right o, dst, heq => by
      let F : TransCall i := ⟨a, b, c, T, h₁, h₂, p⟩
      let hcl := envClosed_of_envWfT hW
      let hinst := envMembersSubstStable_of_envWfT hW
      let ys := (J5a.readOutput (F.K hW su).2.2).val hcl hinst
      let hXY := J3.callerOfChild (y := .cv F.literal) (.tail _ (.head _))
      have hi := liftOutput_certificate_exact hW su i p (.right (o.spliceLeft ys)) dst heq
      have hc₁ := o.spliceLeft_certificate_exact ys
        (J3.Certified.recaller hXY _ (F.p₂ hW su).rightTiles)
        (J5a.readOutput_certified hcl hinst [.cv F.literal] (F.K hW su).2.2)
      have hc₂ := o.recaller_certificate_exact hXY (F.p₂ hW su).rightTiles
      exact hi.trans (transportCertificate_congr hW i p (o.spliceLeft_exact ys)
        (hc₁.trans hc₂))

theorem liftOutput_root (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) (o : OutputPos hW su i) :
    liftOutput hW su i .root o = some o := rfl

theorem liftOutput_transLeft_right (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) (i : JInput E n R)
    {a b c T : Expr Nat} {h₁ : ConvT E n i.ctx a b T}
    {h₂ : ConvT E n i.ctx b c T}
    (p : JCallPos i.literal (.trans i.ctx a b c T h₁ h₂))
    (o : StarPos ((((JCallPos.transLeft p).input i).result hW su).valley.right.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))) :
    liftOutput hW su i (.transLeft p) (.right o) = none := rfl

theorem liftOutput_transRight_left (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) (i : JInput E n R)
    {a b c T : Expr Nat} {h₁ : ConvT E n i.ctx a b T}
    {h₂ : ConvT E n i.ctx b c T}
    (p : JCallPos i.literal (.trans i.ctx a b c T h₁ h₂))
    (o : StarPos ((((JCallPos.transRight p).input i).result hW su).valley.left.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))) :
    liftOutput hW su i (.transRight p) (.left o) = none := rfl

end JCallPos

end Rcic.Declarative.F8Measure.JExecution

#print axioms Rcic.Declarative.F8Measure.JExecution.JInput.result
#print axioms Rcic.Declarative.F8Measure.JExecution.JCallPos.source
#print axioms Rcic.Declarative.F8Measure.JExecution.TransCall.dRoot_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.TransCall.result_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.JCallPos.liftOutput_selected
#print axioms Rcic.Declarative.F8Measure.JExecution.JCallPos.liftOutput_certificate_exact
