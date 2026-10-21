import rcic.RcicF8XValleyVia

/-!
# JT-1: demand before a J answer

ChatGPT designed the pre-answer demand contract in `S0_J_TOTALITY.md` (#7194).
Its `JT1_OPEN_ROWS_SUPPLY_MAP.md` supplement (#7213) keeps raw constructor
rows and obligations inside a literal distinct from original X calls.
This additive observation uses the landed WK-1b worker and its actual
`flattenTc`/`Flat.segment`; there is no second executing traversal. Structural
selection and an operational prefix are different relations. In particular,
structural selection can retain a later obligation after an earlier refusal,
whereas the operational right-sibling rules require the existing earlier
worker to have returned. The prefix stops at `awaitJ`, before that answer.

This is JT-1 only. Availability, answer safety, step certification and generated
origins remain distinct obligations. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure.JTotality

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- The actual original `ConvT` root, independent of every J support domain. -/
inductive RawConstructor where
  | refl | symm | trans | beta | zeta | zetaLocal | delta | iota | lit
  | app | lam | pi | letE | sorts | consts | eta | irr | tyConv
  deriving DecidableEq, Repr

/-- Exhaustive raw classification before a supplier answers. -/
def rawConstructor {Γ a b T} : ConvT E n Γ a b T → RawConstructor
  | .refl .. => .refl
  | .symm .. => .symm
  | .trans .. => .trans
  | .beta .. => .beta
  | .zeta .. => .zeta
  | .zetaLocal .. => .zetaLocal
  | .delta .. => .delta
  | .iota .. => .iota
  | .lit .. => .lit
  | .app .. => .app
  | .lam .. => .lam
  | .pi .. => .pi
  | .letE .. => .letE
  | .sorts .. => .sorts
  | .consts .. => .consts
  | .eta .. => .eta
  | .irr .. => .irr
  | .tyConv .. => .tyConv

/-- A fixed independently admitted input of the existing WK-1b X worker. -/
structure XEntryW (E : ResolvedEnv) (n : Nat) where
  R : List (Jd E n)
  Γ : LCtx
  A : Expr Nat
  B : Expr Nat
  A' : Expr Nat
  B' : Expr Nat
  c : EvTc R Γ (.pi A B) (.pi A' B')
  hΓ : CtxWfT E n Γ
  hadm : xAdmW c = true

/-- Addresses in the actual segmented input, then through the wrappers that
remain after the existing flattening. Repeated equal literals stay distinct. -/
inductive PathStep where
  | segmentHere | segmentNext | linkHere | linkNext
  | ofCv | linkWk | cvSymm | cvLeft | cvRight | cvTyConv | cvRety | cvWk
  deriving DecidableEq, Repr

abbrev Path := List PathStep

/-- One source-side invocation. In particular `h` is never a transported
conversion, and `v` is the actual pending weakening into the segment context. -/
structure JRequestW (C : XEntryW E n) where
  Γ₀ : LCtx
  a : Expr Nat
  b : Expr Nat
  T : Expr Nat
  h : ConvT E n Γ₀ a b T
  hs : ∃ r ∈ C.R, SubEq (.cv h) r
  v : CtxWfVia E n Γ₀
  path : Path

def JRequestW.at (C : XEntryW E n) (p : Path) {Γ₀ : LCtx}
    {a b T : Expr Nat} (ρ : Wk Γ₀ C.Γ) (h : ConvT E n Γ₀ a b T)
    (hs : ∃ r ∈ C.R, SubEq (.cv h) r) : JRequestW C :=
  ⟨Γ₀, a, b, T, h, hs, ⟨C.Γ, ρ, C.hΓ⟩, p⟩

def JRequestW.answer {C : XEntryW E n} (q : JRequestW C)
    (J : ∀ R : List (Jd E n), JProcViaP R) :
    Option (Valley C.R q.Γ₀ q.a q.b q.T) :=
  J C.R q.v q.h q.hs

/-- Exactly the existing literal worker, at the request's actual Via. -/
def JRequestW.literalWorker {C : XEntryW E n} (q : JRequestW C)
    (X : SuppliersVia E n) :=
  svalleyCvVia X (EvCv.lit q.h q.hs) q.v.ρ q.v.wf rfl

/-! Structural demand: no supplier, answer, result record or J fragment occurs
in any of these selection rules. -/

inductive NeedCvW (C : XEntryW E n) :
    {Γ₀ : LCtx} → {a b T : Expr Nat} → (c : EvCv C.R Γ₀ a b T) →
    Wk Γ₀ C.Γ → Path → JRequestW C → Prop where
  | lit {Γ₀ a b T} (h : ConvT E n Γ₀ a b T)
      (hs : ∃ r ∈ C.R, SubEq (.cv h) r) (ρ : Wk Γ₀ C.Γ) (p : Path) :
      NeedCvW C (.lit h hs) ρ p (JRequestW.at C p ρ h hs)
  | symm {Γ₀ a b T} {c : EvCv C.R Γ₀ a b T} {ρ p q} :
      NeedCvW C c ρ (p ++ [.cvSymm]) q → NeedCvW C (.symm c) ρ p q
  | left {Γ₀ a b c T} {c₁ : EvCv C.R Γ₀ a b T}
      {c₂ : EvCv C.R Γ₀ b c T} {ρ p q} :
      NeedCvW C c₁ ρ (p ++ [.cvLeft]) q → NeedCvW C (.trans c₁ c₂) ρ p q
  | right {Γ₀ a b c T} {c₁ : EvCv C.R Γ₀ a b T}
      {c₂ : EvCv C.R Γ₀ b c T} {ρ p q} :
      NeedCvW C c₂ ρ (p ++ [.cvRight]) q → NeedCvW C (.trans c₁ c₂) ρ p q
  | tyConv {Γ₀ a b T T'} {u : Level} {c : EvCv C.R Γ₀ a b T}
      {cA : EvCv C.R Γ₀ T T' (.sort u)} {ρ p q} :
      NeedCvW C c ρ (p ++ [.cvTyConv]) q → NeedCvW C (.tyConv u c cA) ρ p q
  | rety {Γ₀ a b T T'} {c : EvCv C.R Γ₀ a b T}
      {cA : EvTc C.R Γ₀ T T'} {ρ p q} :
      NeedCvW C c ρ (p ++ [.cvRety]) q → NeedCvW C (.rety c cA) ρ p q
  | wk {Γ₀ a b T} {d : LocalDecl} {k : Nat}
      {c : EvCv C.R Γ₀ a b T} {ρ : Wk (insertAt d k Γ₀) C.Γ} {p q} :
      NeedCvW C c (.ins d k ρ) (p ++ [.cvWk]) q →
      NeedCvW C (.wk d k c) ρ p q

inductive NeedLinkW (C : XEntryW E n) :
    {Γ₀ : LCtx} → {A B : Expr Nat} → EvTc C.R Γ₀ A B →
    Wk Γ₀ C.Γ → Path → JRequestW C → Prop where
  | ofCv {Γ₀ A B} {u : Level} {c : EvCv C.R Γ₀ A B (.sort u)} {ρ p q} :
      NeedCvW C c ρ (p ++ [.ofCv]) q → NeedLinkW C (.ofCv u c) ρ p q
  | wk {Γ₀ A B} {d : LocalDecl} {k : Nat}
      {l : EvTc C.R Γ₀ A B} {ρ : Wk (insertAt d k Γ₀) C.Γ} {p q} :
      NeedLinkW C l (.ins d k ρ) (p ++ [.linkWk]) q →
      NeedLinkW C (.wk d k l) ρ p q

inductive NeedPrefixW (C : XEntryW E n) :
    {P Q : Expr Nat} → Flat C.R C.Γ P Q → Path → JRequestW C → Prop where
  | head {P M Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {rest : Flat C.R C.Γ M Q} {p q} :
      NeedLinkW C l (.id C.Γ) (p ++ [.linkHere]) q →
      NeedPrefixW C (.cons l hl rest) p q
  | tail {P M Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {rest : Flat C.R C.Γ M Q} {p q} :
      NeedPrefixW C rest (p ++ [.linkNext]) q →
      NeedPrefixW C (.cons l hl rest) p q

inductive NeedSegW (C : XEntryW E n) :
    {P Q : Expr Nat} → Flat C.R C.Γ P Q → Path → JRequestW C → Prop where
  | single {P Q} {l : EvTc C.R C.Γ P Q} {hl : isLink l = true} {p q}
      (hp : piSpinedTc l = false) :
      NeedLinkW C l (.id C.Γ) (p ++ [.linkHere]) q →
      NeedSegW C (.cons l hl (.nil Q)) p q
  | multiple {P M N Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {l' : EvTc C.R C.Γ M N} {hl' : isLink l' = true}
      {rest : Flat C.R C.Γ N Q} {p q} :
      NeedPrefixW C (.cons l hl (.cons l' hl' rest)) p q →
      NeedSegW C (.cons l hl (.cons l' hl' rest)) p q

inductive NeedSegsW (C : XEntryW E n) :
    {P Q : Expr Nat} → Segs C.R C.Γ P Q → Path → JRequestW C → Prop where
  | head {P M Q} {s : Flat C.R C.Γ P M} {hM : isPi M = true}
      {rest : Segs C.R C.Γ M Q} {p q} :
      NeedSegW C s (p ++ [.segmentHere]) q →
      NeedSegsW C (.cons s hM rest) p q
  | tail {P M Q} {s : Flat C.R C.Γ P M} {hM : isPi M = true}
      {rest : Segs C.R C.Γ M Q} {p q} :
      NeedSegsW C rest (p ++ [.segmentNext]) q →
      NeedSegsW C (.cons s hM rest) p q

def NeedW (C : XEntryW E n) (q : JRequestW C) : Prop :=
  NeedSegsW C ((flattenTc C.c).segment rfl) [] q

/-- Row accounting retains all demand, including every currently unanswered
raw constructor. No dispatcher fragment or answer appears in this definition. -/
def NeedRowW (C : XEntryW E n) (q : JRequestW C) (arm : RawConstructor) : Prop :=
  NeedW C q ∧ rawConstructor q.h = arm

theorem needed_has_its_raw_row {C : XEntryW E n} {q : JRequestW C}
    (hq : NeedW C q) : NeedRowW C q (rawConstructor q.h) := ⟨hq, rfl⟩

theorem needRow_is_needed {C : XEntryW E n} {q : JRequestW C}
    {arm : RawConstructor} (hq : NeedRowW C q arm) : NeedW C q := hq.1

/-! Children of the original raw literal have their own address space. These
are structural source obligations, not an assertion that X or recursive J has
called them. In particular there is no coercion into `JRequestW`, `NeedW` or
`IssuedBeforeAnswer`. Typing fields are not relabelled as conversion children. -/

inductive JChildStep where
  | symm | transLeft | transRight | appFun | appArg
  | lamDomain | lamBody | piDomain | piBody
  | letDomain | letValue | letBody | tyConvTerm | tyConvIndex
  deriving DecidableEq, Repr

/-- A direct conversion child, retaining the original child evidence and its
actual binder context and index. -/
inductive OriginalJChildW :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → JChildStep →
    {Γ' : LCtx} → {a' b' T' : Expr Nat} → ConvT E n Γ' a' b' T' → Prop where
  | symm {Γ a b T} (h : ConvT E n Γ a b T) :
      OriginalJChildW (.symm Γ a b T h) .symm h
  | transLeft {Γ a b c T} (h₁ : ConvT E n Γ a b T) (h₂ : ConvT E n Γ b c T) :
      OriginalJChildW (.trans Γ a b c T h₁ h₂) .transLeft h₁
  | transRight {Γ a b c T} (h₁ : ConvT E n Γ a b T) (h₂ : ConvT E n Γ b c T) :
      OriginalJChildW (.trans Γ a b c T h₁ h₂) .transRight h₂
  | appFun {Γ f g a b A B} (h₁ : ConvT E n Γ f g (.pi A B))
      (h₂ : ConvT E n Γ a b A) :
      OriginalJChildW (.app Γ f g a b A B h₁ h₂) .appFun h₁
  | appArg {Γ f g a b A B} (h₁ : ConvT E n Γ f g (.pi A B))
      (h₂ : ConvT E n Γ a b A) :
      OriginalJChildW (.app Γ f g a b A B h₁ h₂) .appArg h₂
  | lamDomain {Γ A A' b b' B} (u : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hb : ConvT E n (.assumption A :: Γ) b b' B) :
      OriginalJChildW (.lam Γ A A' b b' B u hA hb) .lamDomain hA
  | lamBody {Γ A A' b b' B} (u : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hb : ConvT E n (.assumption A :: Γ) b b' B) :
      OriginalJChildW (.lam Γ A A' b b' B u hA hb) .lamBody hb
  | piDomain {Γ A A' B B'} (u v : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
      OriginalJChildW (.pi Γ A A' B B' u v hA hB) .piDomain hA
  | piBody {Γ A A' B B'} (u v : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
      OriginalJChildW (.pi Γ A A' B B' u v hA hB) .piBody hB
  | letDomain {Γ A A' v v' b b' B} (u : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B) :
      OriginalJChildW (.letE Γ A A' v v' b b' B u hA hv hb) .letDomain hA
  | letValue {Γ A A' v v' b b' B} (u : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B) :
      OriginalJChildW (.letE Γ A A' v v' b b' B u hA hv hb) .letValue hv
  | letBody {Γ A A' v v' b b' B} (u : Level) (hA : ConvT E n Γ A A' (.sort u))
      (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B) :
      OriginalJChildW (.letE Γ A A' v v' b b' B u hA hv hb) .letBody hb
  | tyConvTerm {Γ a b A A'} (u : Level) (h : ConvT E n Γ a b A)
      (hA : ConvT E n Γ A A' (.sort u)) :
      OriginalJChildW (.tyConv Γ a b A A' u h hA) .tyConvTerm h
  | tyConvIndex {Γ a b A A'} (u : Level) (h : ConvT E n Γ a b A)
      (hA : ConvT E n Γ A A' (.sort u)) :
      OriginalJChildW (.tyConv Γ a b A A' u h hA) .tyConvIndex hA

/-- A nonempty path strictly inside the original J literal. -/
inductive OriginalJChildAtW :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → List JChildStep →
    {Γ' : LCtx} → {a' b' T' : Expr Nat} → ConvT E n Γ' a' b' T' → Prop where
  | child {Γ a b T Γ' a' b' T'} {h : ConvT E n Γ a b T}
      {h' : ConvT E n Γ' a' b' T'} {step} :
      OriginalJChildW h step h' → OriginalJChildAtW h [step] h'
  | descend {Γ a b T Γ' a' b' T' Γ'' a'' b'' T''}
      {h : ConvT E n Γ a b T} {h' : ConvT E n Γ' a' b' T'}
      {h'' : ConvT E n Γ'' a'' b'' T''} {step steps} :
      OriginalJChildW h step h' → OriginalJChildAtW h' steps h'' →
      OriginalJChildAtW h (step :: steps) h''

structure JChildAddressW where
  xOccurrence : Path
  insideLiteral : List JChildStep

/-- A genuine original conversion child of a demanded literal. It does not
record a second X invocation or claim that any supplier answered this child. -/
structure JChildObligationW (C : XEntryW E n) (q : JRequestW C) where
  parentNeeded : NeedW C q
  address : JChildAddressW
  parentOccurrence : address.xOccurrence = q.path
  Γ₀ : LCtx
  a : Expr Nat
  b : Expr Nat
  T : Expr Nat
  h : ConvT E n Γ₀ a b T
  source : OriginalJChildAtW q.h address.insideLiteral h

theorem OriginalJChildAtW.nonempty {Γ a b T Γ' a' b' T'}
    {h : ConvT E n Γ a b T} {h' : ConvT E n Γ' a' b' T'}
    {steps : List JChildStep} (hs : OriginalJChildAtW h steps h') : steps ≠ [] := by
  cases hs <;> simp

/-! Operational prefixes. `returned` summarizes a completed earlier worker;
its constructor below carries the exact return equation of that existing
worker. No constructor asks for the answer at the terminal `awaitJ`. -/

inductive PrefixEventW (C : XEntryW E n) where
  | enter (p : Path)
  | returned (p : Path)
  | awaitJ (q : JRequestW C)

abbrev PrefixW (C : XEntryW E n) := List (PrefixEventW C)

inductive IssuedCvW (X : SuppliersVia E n) (C : XEntryW E n) :
    {Γ₀ : LCtx} → {a b T : Expr Nat} → (c : EvCv C.R Γ₀ a b T) →
    Wk Γ₀ C.Γ → Path → PrefixW C → JRequestW C → Prop where
  | lit {Γ₀ a b T} (h : ConvT E n Γ₀ a b T)
      (hs : ∃ r ∈ C.R, SubEq (.cv h) r) (ρ : Wk Γ₀ C.Γ) (p : Path) :
      IssuedCvW X C (.lit h hs) ρ p
        [.awaitJ (JRequestW.at C p ρ h hs)] (JRequestW.at C p ρ h hs)
  | symm {Γ₀ a b T} {c : EvCv C.R Γ₀ a b T} {ρ p π q} :
      IssuedCvW X C c ρ (p ++ [.cvSymm]) π q →
      IssuedCvW X C (.symm c) ρ p (.enter p :: π) q
  | left {Γ₀ a b c T} {c₁ : EvCv C.R Γ₀ a b T}
      {c₂ : EvCv C.R Γ₀ b c T} {ρ p π q} :
      IssuedCvW X C c₁ ρ (p ++ [.cvLeft]) π q →
      IssuedCvW X C (.trans c₁ c₂) ρ p (.enter p :: π) q
  | right {Γ₀ a b c T} {c₁ : EvCv C.R Γ₀ a b T}
      {c₂ : EvCv C.R Γ₀ b c T} {ρ p π q}
      (hb₁ : bCvW c₁ = true)
      (r₁ : SOutB C.R C.Γ (ρ.map a) (ρ.map b) (ρ.map T) c₁.leaves)
      (hret : svalleyCvVia X c₁ ρ C.hΓ hb₁ = some r₁) :
      IssuedCvW X C c₂ ρ (p ++ [.cvRight]) π q →
      IssuedCvW X C (.trans c₁ c₂) ρ p
        (.returned (p ++ [.cvLeft]) :: π) q
  | tyConv {Γ₀ a b T T'} {u : Level} {c : EvCv C.R Γ₀ a b T}
      {cA : EvCv C.R Γ₀ T T' (.sort u)} {ρ p π q} :
      IssuedCvW X C c ρ (p ++ [.cvTyConv]) π q →
      IssuedCvW X C (.tyConv u c cA) ρ p (.enter p :: π) q
  | rety {Γ₀ a b T T'} {c : EvCv C.R Γ₀ a b T}
      {cA : EvTc C.R Γ₀ T T'} {ρ p π q} :
      IssuedCvW X C c ρ (p ++ [.cvRety]) π q →
      IssuedCvW X C (.rety c cA) ρ p (.enter p :: π) q
  | wk {Γ₀ a b T} {d : LocalDecl} {k : Nat}
      {c : EvCv C.R Γ₀ a b T} {ρ : Wk (insertAt d k Γ₀) C.Γ} {p π q} :
      IssuedCvW X C c (.ins d k ρ) (p ++ [.cvWk]) π q →
      IssuedCvW X C (.wk d k c) ρ p (.enter p :: π) q

inductive IssuedLinkW (X : SuppliersVia E n) (C : XEntryW E n) :
    {Γ₀ : LCtx} → {A B : Expr Nat} → EvTc C.R Γ₀ A B →
    Wk Γ₀ C.Γ → Path → PrefixW C → JRequestW C → Prop where
  | ofCv {Γ₀ A B} {u : Level} {c : EvCv C.R Γ₀ A B (.sort u)} {ρ p π q} :
      IssuedCvW X C c ρ (p ++ [.ofCv]) π q →
      IssuedLinkW X C (.ofCv u c) ρ p (.enter p :: π) q
  | wk {Γ₀ A B} {d : LocalDecl} {k : Nat}
      {l : EvTc C.R Γ₀ A B} {ρ : Wk (insertAt d k Γ₀) C.Γ} {p π q} :
      IssuedLinkW X C l (.ins d k ρ) (p ++ [.linkWk]) π q →
      IssuedLinkW X C (.wk d k l) ρ p (.enter p :: π) q

inductive IssuedPrefixW (X : SuppliersVia E n) (C : XEntryW E n) :
    {P Q : Expr Nat} → Flat C.R C.Γ P Q → Path → PrefixW C → JRequestW C → Prop where
  | head {P M Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {rest : Flat C.R C.Γ M Q} {p π q} :
      IssuedLinkW X C l (.id C.Γ) (p ++ [.linkHere]) π q →
      IssuedPrefixW X C (.cons l hl rest) p (.enter p :: π) q
  | tail {P M N Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {l' : EvTc C.R C.Γ M N} {hl' : isLink l' = true}
      {rest : Flat C.R C.Γ N Q} {p π q}
      (hb : bLinkW l = true)
      (r : Σ T : Expr Nat, SOutB C.R C.Γ P M T l.leaves)
      (hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb = some r) :
      IssuedPrefixW X C (.cons l' hl' rest) (p ++ [.linkNext]) π q →
      IssuedPrefixW X C (.cons l hl (.cons l' hl' rest)) p
        (.returned (p ++ [.linkHere]) :: π) q

inductive IssuedSegW (X : SuppliersVia E n) (C : XEntryW E n) :
    {P Q : Expr Nat} → Flat C.R C.Γ P Q → Path → PrefixW C → JRequestW C → Prop where
  | single {P Q} {l : EvTc C.R C.Γ P Q} {hl : isLink l = true} {p π q}
      (hp : piSpinedTc l = false) :
      IssuedLinkW X C l (.id C.Γ) (p ++ [.linkHere]) π q →
      IssuedSegW X C (.cons l hl (.nil Q)) p (.enter p :: π) q
  | multiple {P M N Q} {l : EvTc C.R C.Γ P M} {hl : isLink l = true}
      {l' : EvTc C.R C.Γ M N} {hl' : isLink l' = true}
      {rest : Flat C.R C.Γ N Q} {p π q} :
      IssuedPrefixW X C (.cons l hl (.cons l' hl' rest)) p π q →
      IssuedSegW X C (.cons l hl (.cons l' hl' rest)) p (.enter p :: π) q

inductive IssuedSegsW (X : SuppliersVia E n) (C : XEntryW E n) :
    {P Q : Expr Nat} → Segs C.R C.Γ P Q → Path → PrefixW C → JRequestW C → Prop where
  | head {P M Q} {s : Flat C.R C.Γ P M} {hM : isPi M = true}
      {rest : Segs C.R C.Γ M Q} {p π q} :
      IssuedSegW X C s (p ++ [.segmentHere]) π q →
      IssuedSegsW X C (.cons s hM rest) p (.enter p :: π) q
  | tail {P M Q} {s : Flat C.R C.Γ P M} {hM : isPi M = true}
      {rest : Segs C.R C.Γ M Q} {p π q}
      {A B A₁ B₁ : Expr Nat} (hP : P = .pi A B) (hM' : M = .pi A₁ B₁)
      (hadm : s.segAdmW = true) (r : SegOut C.R C.Γ A B A₁ B₁ s.leaves)
      (hret : xSegSVia X C.hΓ s hadm hP hM' = some r) :
      IssuedSegsW X C rest (p ++ [.segmentNext]) π q →
      IssuedSegsW X C (.cons s hM rest) p
        (.returned (p ++ [.segmentHere]) :: π) q

def IssuedBeforeAnswer (X : SuppliersVia E n) (C : XEntryW E n)
    (π : PrefixW C) (q : JRequestW C) : Prop :=
  IssuedSegsW X C ((flattenTc C.c).segment rfl) [] π q

/-! A defunctionalized graph of the existing calls. This is a relation, not
an evaluator: a completed sibling is witnessed by its original worker's
return equation. The generic finite-path relation below has no knowledge of
the syntax of conversions or of demand. -/

inductive WorkerSiteW (C : XEntryW E n) where
  | cv {Γ₀ a b T} (c : EvCv C.R Γ₀ a b T) (ρ : Wk Γ₀ C.Γ) (p : Path)
  | link {Γ₀ A B} (l : EvTc C.R Γ₀ A B) (ρ : Wk Γ₀ C.Γ) (p : Path)
  | prefix {P Q} (s : Flat C.R C.Γ P Q) (p : Path)
  | segment {P Q} (s : Flat C.R C.Γ P Q) (p : Path)
  | segments {P Q} (s : Segs C.R C.Γ P Q) (p : Path)
  | await (q : JRequestW C)

inductive WorkerStepW (X : SuppliersVia E n) (C : XEntryW E n) :
    WorkerSiteW C → PrefixEventW C → WorkerSiteW C → Prop where
  | literal {Γ₀ a b T} (h : ConvT E n Γ₀ a b T)
      (hs : ∃ r ∈ C.R, SubEq (.cv h) r) (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.lit h hs) ρ p)
        (.awaitJ (JRequestW.at C p ρ h hs)) (.await (JRequestW.at C p ρ h hs))
  | cvSymm {Γ₀ a b T} (c : EvCv C.R Γ₀ a b T) (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.symm c) ρ p) (.enter p) (.cv c ρ (p ++ [.cvSymm]))
  | cvLeft {Γ₀ a b c T} (c₁ : EvCv C.R Γ₀ a b T) (c₂ : EvCv C.R Γ₀ b c T)
      (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.trans c₁ c₂) ρ p) (.enter p) (.cv c₁ ρ (p ++ [.cvLeft]))
  | cvRight {Γ₀ a b c T} (c₁ : EvCv C.R Γ₀ a b T) (c₂ : EvCv C.R Γ₀ b c T)
      (ρ : Wk Γ₀ C.Γ) (p : Path) (hb : bCvW c₁ = true)
      (r : SOutB C.R C.Γ (ρ.map a) (ρ.map b) (ρ.map T) c₁.leaves)
      (hr : svalleyCvVia X c₁ ρ C.hΓ hb = some r) :
      WorkerStepW X C (.cv (.trans c₁ c₂) ρ p) (.returned (p ++ [.cvLeft]))
        (.cv c₂ ρ (p ++ [.cvRight]))
  | cvTyConv {Γ₀ a b T T'} (u : Level) (c : EvCv C.R Γ₀ a b T)
      (cA : EvCv C.R Γ₀ T T' (.sort u)) (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.tyConv u c cA) ρ p) (.enter p)
        (.cv c ρ (p ++ [.cvTyConv]))
  | cvRety {Γ₀ a b T T'} (c : EvCv C.R Γ₀ a b T) (cA : EvTc C.R Γ₀ T T')
      (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.rety c cA) ρ p) (.enter p) (.cv c ρ (p ++ [.cvRety]))
  | cvWk {Γ₀ a b T} (d : LocalDecl) (k : Nat) (c : EvCv C.R Γ₀ a b T)
      (ρ : Wk (insertAt d k Γ₀) C.Γ) (p : Path) :
      WorkerStepW X C (.cv (.wk d k c) ρ p) (.enter p)
        (.cv c (.ins d k ρ) (p ++ [.cvWk]))
  | ofCv {Γ₀ A B} (u : Level) (c : EvCv C.R Γ₀ A B (.sort u))
      (ρ : Wk Γ₀ C.Γ) (p : Path) :
      WorkerStepW X C (.link (.ofCv u c) ρ p) (.enter p) (.cv c ρ (p ++ [.ofCv]))
  | linkWk {Γ₀ A B} (d : LocalDecl) (k : Nat) (l : EvTc C.R Γ₀ A B)
      (ρ : Wk (insertAt d k Γ₀) C.Γ) (p : Path) :
      WorkerStepW X C (.link (.wk d k l) ρ p) (.enter p)
        (.link l (.ins d k ρ) (p ++ [.linkWk]))
  | prefixHead {P M Q} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (rest : Flat C.R C.Γ M Q) (p : Path) :
      WorkerStepW X C (.prefix (.cons l hl rest) p) (.enter p)
        (.link l (.id C.Γ) (p ++ [.linkHere]))
  | prefixTail {P M N Q} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (l' : EvTc C.R C.Γ M N) (hl' : isLink l' = true)
      (rest : Flat C.R C.Γ N Q) (p : Path) (hb : bLinkW l = true)
      (r : Σ T : Expr Nat, SOutB C.R C.Γ P M T l.leaves)
      (hr : slinkValleyVia X l (.id C.Γ) C.hΓ hb = some r) :
      WorkerStepW X C (.prefix (.cons l hl (.cons l' hl' rest)) p)
        (.returned (p ++ [.linkHere])) (.prefix (.cons l' hl' rest) (p ++ [.linkNext]))
  | segmentSingle {P Q} (l : EvTc C.R C.Γ P Q) (hl : isLink l = true)
      (hp : piSpinedTc l = false) (p : Path) :
      WorkerStepW X C (.segment (.cons l hl (.nil Q)) p) (.enter p)
        (.link l (.id C.Γ) (p ++ [.linkHere]))
  | segmentMultiple {P M N Q} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (l' : EvTc C.R C.Γ M N) (hl' : isLink l' = true)
      (rest : Flat C.R C.Γ N Q) (p : Path) :
      WorkerStepW X C (.segment (.cons l hl (.cons l' hl' rest)) p) (.enter p)
        (.prefix (.cons l hl (.cons l' hl' rest)) p)
  | segmentsHead {P M Q} (s : Flat C.R C.Γ P M) (hM : isPi M = true)
      (rest : Segs C.R C.Γ M Q) (p : Path) :
      WorkerStepW X C (.segments (.cons s hM rest) p) (.enter p)
        (.segment s (p ++ [.segmentHere]))
  | segmentsTail {P M Q} (s : Flat C.R C.Γ P M) (hM : isPi M = true)
      (rest : Segs C.R C.Γ M Q) (p : Path) {A B A₁ B₁ : Expr Nat}
      (hP : P = .pi A B) (hM' : M = .pi A₁ B₁) (ha : s.segAdmW = true)
      (r : SegOut C.R C.Γ A B A₁ B₁ s.leaves)
      (hr : xSegSVia X C.hΓ s ha hP hM' = some r) :
      WorkerStepW X C (.segments (.cons s hM rest) p)
        (.returned (p ++ [.segmentHere])) (.segments rest (p ++ [.segmentNext]))

/-- Generic finite reduction path, terminated immediately before the literal
answer is consumed. There is no step out of `await`. -/
inductive WorkerTraceW (X : SuppliersVia E n) (C : XEntryW E n) :
    WorkerSiteW C → PrefixW C → JRequestW C → Prop where
  | await (q : JRequestW C) : WorkerTraceW X C (.await q) [] q
  | step {s t : WorkerSiteW C} {ev : PrefixEventW C} {π q} :
      WorkerStepW X C s ev t → WorkerTraceW X C t π q → WorkerTraceW X C s (ev :: π) q

private def IssuedAtW (X : SuppliersVia E n) (C : XEntryW E n)
    (s : WorkerSiteW C) (π : PrefixW C) (q : JRequestW C) : Prop :=
  match s with
  | .cv c ρ p => IssuedCvW X C c ρ p π q
  | .link l ρ p => IssuedLinkW X C l ρ p π q
  | .prefix s p => IssuedPrefixW X C s p π q
  | .segment s p => IssuedSegW X C s p π q
  | .segments s p => IssuedSegsW X C s p π q
  | .await q' => π = [] ∧ q = q'

private theorem WorkerStepW.back {X : SuppliersVia E n} {C : XEntryW E n}
    {s t : WorkerSiteW C} {ev : PrefixEventW C} {π q}
    (hs : WorkerStepW X C s ev t) (hi : IssuedAtW X C t π q) :
    IssuedAtW X C s (ev :: π) q := by
  cases hs with
  | literal h hs ρ p =>
      rcases hi with ⟨rfl, rfl⟩
      exact .lit h hs ρ p
  | cvSymm => exact .symm hi
  | cvLeft => exact .left hi
  | cvRight c₁ c₂ ρ p hb r hr => exact .right hb r hr hi
  | cvTyConv => exact .tyConv hi
  | cvRety => exact .rety hi
  | cvWk => exact .wk hi
  | ofCv => exact .ofCv hi
  | linkWk => exact .wk hi
  | prefixHead => exact .head hi
  | prefixTail l hl l' hl' rest p hb r hr => exact .tail hb r hr hi
  | segmentSingle l hl hp p => exact .single hp hi
  | segmentMultiple => exact .multiple hi
  | segmentsHead => exact .head hi
  | segmentsTail s hM rest p hP hM' ha r hr => exact .tail hP hM' ha r hr hi

private theorem WorkerTraceW.toIssued {X : SuppliersVia E n} {C : XEntryW E n}
    {s : WorkerSiteW C} {π q} (ht : WorkerTraceW X C s π q) : IssuedAtW X C s π q := by
  induction ht with
  | await => exact ⟨rfl, rfl⟩
  | step hs _ ih => exact hs.back ih

theorem IssuedCvW.trace {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ a b T} {c : EvCv C.R Γ₀ a b T} {ρ p π q}
    (hi : IssuedCvW X C c ρ p π q) : WorkerTraceW X C (.cv c ρ p) π q := by
  induction hi with
  | lit h hs ρ p => exact .step (.literal h hs ρ p) (.await _)
  | symm _ ih => exact .step (.cvSymm ..) ih
  | left _ ih => exact .step (.cvLeft ..) ih
  | right hb r hr _ ih => exact .step (.cvRight _ _ _ _ hb r hr) ih
  | tyConv _ ih => exact .step (.cvTyConv ..) ih
  | rety _ ih => exact .step (.cvRety ..) ih
  | wk _ ih => exact .step (.cvWk ..) ih

theorem IssuedLinkW.trace {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ A B} {l : EvTc C.R Γ₀ A B} {ρ p π q}
    (hi : IssuedLinkW X C l ρ p π q) : WorkerTraceW X C (.link l ρ p) π q := by
  induction hi with
  | ofCv h => exact .step (.ofCv ..) h.trace
  | wk _ ih => exact .step (.linkWk ..) ih

theorem IssuedPrefixW.trace {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p π q} (hi : IssuedPrefixW X C s p π q) :
    WorkerTraceW X C (.prefix s p) π q := by
  induction hi with
  | head h => exact .step (.prefixHead ..) h.trace
  | tail hb r hr _ ih => exact .step (.prefixTail _ _ _ _ _ _ hb r hr) ih

theorem IssuedSegW.trace {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p π q} (hi : IssuedSegW X C s p π q) :
    WorkerTraceW X C (.segment s p) π q := by
  cases hi with
  | single hp h => exact .step (.segmentSingle _ _ hp _) h.trace
  | multiple h => exact .step (.segmentMultiple ..) h.trace

theorem IssuedSegsW.trace {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Segs C.R C.Γ P Q} {p π q} (hi : IssuedSegsW X C s p π q) :
    WorkerTraceW X C (.segments s p) π q := by
  induction hi with
  | head h => exact .step (.segmentsHead ..) h.trace
  | tail hP hM ha r hr _ ih => exact .step (.segmentsTail _ _ _ _ hP hM ha r hr) ih

/-- Whole-input correspondence, with the original flattening and segmentation:
issuance is exactly finite reachability in the defunctionalized call graph. -/
theorem issued_iff_existing_worker_trace (X : SuppliersVia E n) (C : XEntryW E n)
    (π : PrefixW C) (q : JRequestW C) :
    IssuedBeforeAnswer X C π q ↔
      WorkerTraceW X C (.segments ((flattenTc C.c).segment rfl) []) π q :=
  ⟨IssuedSegsW.trace, WorkerTraceW.toIssued⟩

/-! The graph's descent and completed-sibling gates are checked against the
actual worker equations. These equations specify reduction of pure Option
terms. They make no claim about an optimizer's evaluation of unused terms. -/

theorem worker_symm_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b T} (c : EvCv C.R Γ₀ a b T) (ρ : Wk Γ₀ C.Γ)
    (hb : bCvW c = true) :
    (svalleyCvVia X (.symm c) ρ C.hΓ hb).isSome =
      (svalleyCvVia X c ρ C.hΓ hb).isSome := by
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS,
    Option.isSome_map']

theorem worker_wk_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b T} (d : LocalDecl) (k : Nat) (c : EvCv C.R Γ₀ a b T)
    (ρ : Wk (insertAt d k Γ₀) C.Γ) (hb : bCvW c = true) :
    svalleyCvVia X (.wk d k c) ρ C.hΓ hb =
      svalleyCvVia X c (.ins d k ρ) C.hΓ hb := by
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS]

theorem worker_tyConv_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b T T'} (u : Level) (c : EvCv C.R Γ₀ a b T)
    (cA : EvCv C.R Γ₀ T T' (.sort u)) (ρ : Wk Γ₀ C.Γ) (hb : bCvW c = true) :
    (svalleyCvVia X (.tyConv u c cA) ρ C.hΓ hb).isSome =
      (svalleyCvVia X c ρ C.hΓ hb).isSome := by
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS,
    Option.isSome_map']

theorem worker_rety_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b T T'} (c : EvCv C.R Γ₀ a b T) (cA : EvTc C.R Γ₀ T T')
    (ρ : Wk Γ₀ C.Γ) (hb : bCvW c = true) :
    (svalleyCvVia X (.rety c cA) ρ C.hΓ hb).isSome =
      (svalleyCvVia X c ρ C.hΓ hb).isSome := by
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS,
    Option.isSome_map']

/-- The left-result gate is precisely the nested reduction of the original
multi-scrutinee match; no new short-circuiting worker is introduced. -/
theorem worker_trans_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b c T} (c₁ : EvCv C.R Γ₀ a b T) (c₂ : EvCv C.R Γ₀ b c T)
    (ρ : Wk Γ₀ C.Γ) (h₁ : bCvW c₁ = true) (h₂ : bCvW c₂ = true) :
    svalleyCvVia X (.trans c₁ c₂) ρ C.hΓ (by simp [bCvW, h₁, h₂]) =
      match svalleyCvVia X c₁ ρ C.hΓ h₁ with
      | none => none
      | some r₁ =>
        match svalleyCvVia X c₂ ρ C.hΓ h₂ with
        | none => none
        | some r₂ =>
          (scombine (X.atSeg C.hΓ) r₁.1 r₁.2 r₂.1 r₂.2).map (fun r =>
            r.elim (fun r => ⟨r.1, SOut.bound_of_eq r.2 (by simp only [EvCv.leaves])⟩)
              (fun r => ⟨r.1, SOut.bound_of_eq r.2 (by simp only [EvCv.leaves])⟩)) := by
  -- The engine rebuilds `h₁`/`h₂` with `simpa`, so the two matches are not
  -- definitionally the same matcher until those scrutinees are identified
  -- and cased. `generalize` names the caller's scrutinees before unfolding.
  generalize hD1 : svalleyCvVia X c₁ ρ C.hΓ h₁ = d1
  generalize hD2 : svalleyCvVia X c₂ ρ C.hΓ h₂ = d2
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS, scombine]
    at hD1 hD2 ⊢
  have hs1 : ∀ p : bCvW c₁ = true,
      ViaSEngine.svalleyCvViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS c₁ ρ
        (CtxWfViaS.ofWf C.hΓ) p =
      ViaSEngine.svalleyCvViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS c₁ ρ
        (CtxWfViaS.ofWf C.hΓ) h₁ :=
    fun p => congrArg _ (Subsingleton.elim p h₁)
  have hs2 : ∀ p : bCvW c₂ = true,
      ViaSEngine.svalleyCvViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS c₂ ρ
        (CtxWfViaS.ofWf C.hΓ) p =
      ViaSEngine.svalleyCvViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS c₂ ρ
        (CtxWfViaS.ofWf C.hΓ) h₂ :=
    fun p => congrArg _ (Subsingleton.elim p h₂)
  simp only [hs1, hs2, hD1, hD2]
  cases d1 <;> cases d2 <;> rfl

theorem worker_ofCv_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ A B} (u : Level) (c : EvCv C.R Γ₀ A B (.sort u))
    (ρ : Wk Γ₀ C.Γ) (hb : bCvW c = true) :
    (slinkValleyVia X (.ofCv u c) ρ C.hΓ hb).isSome =
      (svalleyCvVia X c ρ C.hΓ hb).isSome := by
  simp only [slinkValleyVia, slinkValleyViaS, ViaSEngine.slinkValleyViaS,
    svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS, Option.isSome_map']

theorem worker_link_wk_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ A B} (d : LocalDecl) (k : Nat) (l : EvTc C.R Γ₀ A B)
    (ρ : Wk (insertAt d k Γ₀) C.Γ) (hb : bLinkW l = true) :
    slinkValleyVia X (.wk d k l) ρ C.hΓ hb =
      slinkValleyVia X l (.ins d k ρ) C.hΓ hb := by
  simp only [slinkValleyVia, slinkValleyViaS, ViaSEngine.slinkValleyViaS]

theorem worker_prefix_single_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {P M} (l : EvTc C.R C.Γ P M) (hb : bLinkW l = true) :
    (sprefixValleyVia X C.hΓ l hb (.nil M) rfl).isSome =
      (slinkValleyVia X l (.id C.Γ) C.hΓ hb).isSome := by
  simp only [sprefixValleyVia, sprefixValleyViaS, ViaSEngine.sprefixValleyViaS,
    slinkValleyVia, slinkValleyViaS, ViaSEngine.slinkValleyViaS,
    Option.isSome_map']

theorem worker_prefix_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {P M N Q} (l : EvTc C.R C.Γ P M) (l' : EvTc C.R C.Γ M N)
    (hl' : isLink l' = true) (rest : Flat C.R C.Γ N Q)
    (hb : bLinkW l = true) (hb' : bLinkW l' = true) (hr : rest.bPrefixW = true) :
    sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest)
        (by simp [Flat.bPrefixW, hb', hr]) =
      match slinkValleyVia X l (.id C.Γ) C.hΓ hb with
      | none => none
      | some r₁ =>
        match sprefixValleyVia X C.hΓ l' hb' rest hr with
        | none => none
        | some r₂ =>
          (scombine (X.atSeg C.hΓ) r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2).map (fun r =>
            r.elim (fun r => ⟨r₁.1, r.1, SOut.bound_of_eq r.2
                (by simp only [Flat.leaves])⟩)
              (fun r => ⟨r₂.1, r.1, SOut.bound_of_eq r.2
                (by simp only [Flat.leaves])⟩)) := by
  generalize hL : slinkValleyVia X l (.id C.Γ) C.hΓ hb = dl
  generalize hP : sprefixValleyVia X C.hΓ l' hb' rest hr = dp
  simp only [sprefixValleyVia, sprefixValleyViaS, ViaSEngine.sprefixValleyViaS,
    slinkValleyVia, slinkValleyViaS, scombine] at hL hP ⊢
  have hs : ∀ (p : bLinkW l' = true) (q : rest.bPrefixW = true),
      ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) l' p rest q =
      ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) l' hb' rest hr :=
    fun p q =>
      (congrArg
          (fun p => ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps
            (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
            (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) l' p rest q)
          (Subsingleton.elim p hb')).trans
      (congrArg
          (fun q => ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps
            (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
            (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) l' hb' rest q)
          (Subsingleton.elim q hr))
  simp only [hs, hL, hP]
  cases dl <;> cases dp <;> rfl

theorem worker_segment_single_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {P Q A B A' B'} (l : EvTc C.R C.Γ P Q) (hl : isLink l = true)
    (hp : piSpinedTc l = false) (hb : bLinkW l = true)
    (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    xSegSVia X C.hΓ (.cons l hl (.nil Q)) (by simp [Flat.segAdmW, hp, hb]) hP hQ =
      match slinkValleyVia X l (.id C.Γ) C.hΓ hb with
      | none => none
      | some ⟨_, o, ho⟩ =>
        sread (X.atSeg C.hΓ) o (SOut.bound_of_eq
          (L' := (Flat.cons l hl (.nil Q)).leaves) ho
          (by simp only [Flat.leaves, List.append_nil])) hP hQ := by
  generalize hD : slinkValleyVia X l (.id C.Γ) C.hΓ hb = d
  simp only [xSegSVia, xSegSViaS, ViaSEngine.xSegSViaS, hp, Bool.false_eq_true,
    ↓reduceDIte, slinkValleyVia, slinkValleyViaS, sread] at hD ⊢
  have hs : ∀ p : bLinkW l = true,
      ViaSEngine.slinkValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS l
        (Wk.id C.Γ) (CtxWfViaS.ofWf C.hΓ) p =
      ViaSEngine.slinkValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS l
        (Wk.id C.Γ) (CtxWfViaS.ofWf C.hΓ) hb :=
    fun p => congrArg _ (Subsingleton.elim p hb)
  simp only [hs, hD]
  cases d <;> rfl

theorem worker_segment_multiple_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {P M N Q A B A' B'} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
    (l' : EvTc C.R C.Γ M N) (hl' : isLink l' = true) (rest : Flat C.R C.Γ N Q)
    (hb : bLinkW l = true) (hr : (Flat.cons l' hl' rest).bPrefixW = true)
    (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    xSegSVia X C.hΓ (.cons l hl (.cons l' hl' rest))
        (by simpa only [Flat.segAdmW, Bool.and_eq_true] using And.intro hb hr) hP hQ =
      match sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest) hr with
      | none => none
      | some ⟨_, o, ho⟩ => sread (X.atSeg C.hΓ) o
          (SOut.bound_of_eq (L' := (Flat.cons l hl (.cons l' hl' rest)).leaves)
            ho (by simp only [Flat.leaves])) hP hQ := by
  generalize hD : sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest) hr = d
  simp only [xSegSVia, xSegSViaS, ViaSEngine.xSegSViaS, sprefixValleyVia,
    sprefixValleyViaS, sread] at hD ⊢
  have hs : ∀ (p : bLinkW l = true) (q : (Flat.cons l' hl' rest).bPrefixW = true),
      ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) l p (Flat.cons l' hl' rest) q =
      ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) l hb (Flat.cons l' hl' rest) hr :=
    fun p q =>
      (congrArg
          (fun p => ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps
            (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
            (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) l p
            (Flat.cons l' hl' rest) q)
          (Subsingleton.elim p hb)).trans
      (congrArg
          (fun q => ViaSEngine.sprefixValleyViaS (X.atSeg C.hΓ).toValleyOps
            (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
            (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) l hb
            (Flat.cons l' hl' rest) q)
          (Subsingleton.elim q hr))
  simp only [hs, hD]
  cases d <;> rfl

theorem worker_segments_reduction (X : SuppliersVia E n) (C : XEntryW E n)
    {P Q A B A₁ B₁ A' B'} (s : Flat C.R C.Γ P (.pi A₁ B₁))
    (rest : Segs C.R C.Γ (.pi A₁ B₁) Q) (ha : s.segAdmW = true)
    (hr : rest.admW = true) (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    xSegsSVia X C.hΓ (.cons s rfl rest) (by simp [Segs.admW, ha, hr]) hP hQ =
      match xSegSVia X C.hΓ s ha hP rfl with
      | none => none
      | some r₁ =>
        match xSegsSVia X C.hΓ rest hr rfl hQ with
        | none => none
        | some r₂ => some (SegOut.cast (by simp only [Segs.leaves])
            (SegOut.comp (X.atSeg C.hΓ) r₁ r₂)) := by
  generalize hD1 : xSegSVia X C.hΓ s ha hP rfl = d1
  generalize hD2 : xSegsSVia X C.hΓ rest hr rfl hQ = d2
  simp only [xSegsSVia, xSegsViaS, ViaSEngine.xSegsViaS, xSegSVia, xSegSViaS,
    isPiD, SegOut.comp] at hD1 hD2 ⊢
  have hs1 : ∀ p : s.segAdmW = true,
      ViaSEngine.xSegSViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) s p hP rfl =
      ViaSEngine.xSegSViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) s ha hP rfl :=
    fun p => congrArg
      (fun p => ViaSEngine.xSegSViaS (X.atSeg C.hΓ).toValleyOps
        (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
        (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) s p hP rfl)
      (Subsingleton.elim p ha)
  have hs2 : ∀ p : rest.admW = true,
      ViaSEngine.xSegsViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) rest p rfl hQ =
      ViaSEngine.xSegsViaS (X.atSeg C.hΓ).toValleyOps (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (X.atSeg C.hΓ).structRunnerViaS
        (CtxWfViaS.ofWf C.hΓ) rest hr rfl hQ :=
    fun p => congrArg
      (fun p => ViaSEngine.xSegsViaS (X.atSeg C.hΓ).toValleyOps
        (JProcViaP.toViaSP X.J) (JContractViaP.toViaSP X.hJ)
        (X.atSeg C.hΓ).structRunnerViaS (CtxWfViaS.ofWf C.hΓ) rest p rfl hQ)
      (Subsingleton.elim p hr)
  simp only [hs1, hs2, hD1, hD2]
  cases d1 <;> cases d2 <;> rfl

/-- Admission at the worker site, independent of any supplier answer. The
segment endpoints are retained because their original workers require Π
endpoints in addition to the Boolean fragment check. -/
def WorkerSiteW.Admitted {C : XEntryW E n} : WorkerSiteW C → Prop
  | .cv c _ _ => bCvW c = true
  | .link l _ _ => bLinkW l = true
  | .prefix s _ => s.bPrefixW = true
  | @WorkerSiteW.segment _ _ _ P Q s _ =>
      s.segAdmW = true ∧ isPi P = true ∧ isPi Q = true
  | @WorkerSiteW.segments _ _ _ P Q s _ =>
      s.admW = true ∧ isPi P = true ∧ isPi Q = true
  | .await _ => True

theorem WorkerStepW.admitted {X : SuppliersVia E n} {C : XEntryW E n}
    {s t : WorkerSiteW C} {ev : PrefixEventW C} (hs : WorkerStepW X C s ev t)
    (ha : s.Admitted) : t.Admitted := by
  cases hs with
  | literal => trivial
  | cvSymm => exact ha
  | cvLeft => exact (Bool.and_eq_true_iff.mp ha).1
  | cvRight => exact (Bool.and_eq_true_iff.mp ha).2
  | cvTyConv => exact ha
  | cvRety => exact ha
  | cvWk => exact ha
  | ofCv => exact ha
  | linkWk => exact ha
  | prefixHead => exact (Bool.and_eq_true_iff.mp ha).1
  | prefixTail => exact (Bool.and_eq_true_iff.mp ha).2
  | segmentSingle l hl hp p =>
      have h := ha.1
      simpa only [Flat.segAdmW, hp, Bool.false_or] using h
  | segmentMultiple => exact ha.1
  | segmentsHead s hM rest p =>
      exact ⟨(Bool.and_eq_true_iff.mp ha.1).1, ha.2.1, hM⟩
  | segmentsTail s hM rest p hP hM' hadm r hr =>
      exact ⟨(Bool.and_eq_true_iff.mp ha.1).2, hM, ha.2.2⟩

/-- Actual successful return of the existing worker at this site. No new
execution is defined: the relation mentions precisely its original equation. -/
inductive WorkerReturnsW (X : SuppliersVia E n) (C : XEntryW E n) : WorkerSiteW C → Prop where
  | cv {Γ₀ a b T} (c : EvCv C.R Γ₀ a b T) (ρ : Wk Γ₀ C.Γ) (p : Path)
      (hb : bCvW c = true)
      (hr : (svalleyCvVia X c ρ C.hΓ hb).isSome = true) :
      WorkerReturnsW X C (.cv c ρ p)
  | link {Γ₀ A B} (l : EvTc C.R Γ₀ A B) (ρ : Wk Γ₀ C.Γ) (p : Path)
      (hb : bLinkW l = true)
      (hr : (slinkValleyVia X l ρ C.hΓ hb).isSome = true) :
      WorkerReturnsW X C (.link l ρ p)
  | prefix {P M Q} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (rest : Flat C.R C.Γ M Q) (p : Path)
      (hb : bLinkW l = true) (hrest : rest.bPrefixW = true)
      (hr : (sprefixValleyVia X C.hΓ l hb rest hrest).isSome = true) :
      WorkerReturnsW X C (.prefix (.cons l hl rest) p)
  | segment {P Q A B A' B'} (s : Flat C.R C.Γ P Q) (p : Path)
      (ha : s.segAdmW = true) (hP : P = .pi A B) (hQ : Q = .pi A' B')
      (hr : (xSegSVia X C.hΓ s ha hP hQ).isSome = true) :
      WorkerReturnsW X C (.segment s p)
  | segments {P Q A B A' B'} (s : Segs C.R C.Γ P Q) (p : Path)
      (ha : s.admW = true) (hP : P = .pi A B) (hQ : Q = .pi A' B')
      (hr : (xSegsSVia X C.hΓ s ha hP hQ).isSome = true) :
      WorkerReturnsW X C (.segments s p)
  | await (q : JRequestW C) (hr : (q.answer X.J).isSome = true) :
      WorkerReturnsW X C (.await q)

/-- Worker success on a literal is J success and the `admitSubst` gate.
J returning `none` forces the worker to `none`. The converse is false:
the gate drops a valley that still contains `subst0` or `substLet`.
`split` uses the engine matcher's own splitter, so the payload equation
`he` stays; `cases he :` is rejected because `he` occurs in the `some` arm. -/
private theorem literal_isSome (X : SuppliersVia E n)
    {R : List (Jd E n)} {Γ₀ Γ' : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ₀ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r)
    (ρ : Wk Γ₀ Γ') (hΓ' : CtxWfT E n Γ')
    (hb : bCvW (EvCv.lit h hs) = true) :
    (svalleyCvVia X (.lit h hs) ρ hΓ' hb).isSome = true ↔
      ∃ V, X.J R ⟨Γ', ρ, hΓ'⟩ h hs = some V ∧
        (Valley.admitSubst true V).isSome = true := by
  simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS]
  split
  · next he =>
      have hJ := (JProcViaP.toViaSP_viaS X.J ρ hΓ' h hs).symm.trans he
      constructor
      · intro hnone
        cases hnone
      · rintro ⟨_, hV, _⟩
        rw [hJ] at hV
        cases hV
  · next V he =>
      have hJ := (JProcViaP.toViaSP_viaS X.J ρ hΓ' h hs).symm.trans he
      cases hg : Valley.admitSubst true V with
      | none =>
          constructor
          · intro hnone
            simp [hg] at hnone
          · rintro ⟨_, hV, hs⟩
            rw [hJ] at hV
            cases hV
            rw [hg] at hs
            cases hs
      | some _ =>
          constructor
          · intro _
            exact ⟨V, hJ, by rw [hg]; rfl⟩
          · intro _
            simp [hg]

/-- Every successful parent returns through its selected original child.
The proof uses the original equations, including the completed-left gates,
rather than treating the graph as a callback oracle. -/
theorem WorkerStepW.success {X : SuppliersVia E n} {C : XEntryW E n}
    {s t : WorkerSiteW C} {ev : PrefixEventW C} (hs : WorkerStepW X C s ev t)
    (ha : s.Admitted) (hr : WorkerReturnsW X C s) : WorkerReturnsW X C t := by
  cases hs with
  | literal h hsub ρ p =>
      cases hr with
      | cv _ _ _ hb hr =>
          apply WorkerReturnsW.await
          change (X.J C.R ⟨C.Γ, ρ, C.hΓ⟩ h hsub).isSome = true
          rcases (literal_isSome X h hsub ρ C.hΓ hb).mp hr with ⟨_, hJ, _⟩
          simp [hJ]
  | cvSymm c ρ p =>
      cases hr with
      | cv _ _ _ hb hr =>
          exact .cv c ρ _ ha ((worker_symm_reduction X C c ρ ha) ▸ hr)
  | cvLeft c₁ c₂ ρ p =>
      cases hr with
      | cv _ _ _ hb hr =>
          have h₁ := (Bool.and_eq_true_iff.mp ha).1
          have h₂ := (Bool.and_eq_true_iff.mp ha).2
          rw [worker_trans_reduction X C c₁ c₂ ρ h₁ h₂] at hr
          cases hret : svalleyCvVia X c₁ ρ C.hΓ h₁ with
          | none => simp [hret] at hr
          | some r => exact .cv c₁ ρ _ h₁ (by rw [hret]; rfl)
  | cvRight c₁ c₂ ρ p hb r hret =>
      cases hr with
      | cv _ _ _ hb' hr =>
          have h₁ := (Bool.and_eq_true_iff.mp ha).1
          have h₂ := (Bool.and_eq_true_iff.mp ha).2
          rw [worker_trans_reduction X C c₁ c₂ ρ h₁ h₂, hret] at hr
          cases hret₂ : svalleyCvVia X c₂ ρ C.hΓ h₂ with
          | none => simp [hret₂] at hr
          | some r₂ => exact .cv c₂ ρ _ h₂ (by rw [hret₂]; rfl)
  | cvTyConv u c cA ρ p =>
      cases hr with
      | cv _ _ _ hb hr =>
          exact .cv c ρ _ ha ((worker_tyConv_reduction X C u c cA ρ ha) ▸ hr)
  | cvRety c cA ρ p =>
      cases hr with
      | cv _ _ _ hb hr =>
          exact .cv c ρ _ ha ((worker_rety_reduction X C c cA ρ ha) ▸ hr)
  | cvWk d k c ρ p =>
      cases hr with
      | cv _ _ _ hb hr => exact .cv c (.ins d k ρ) _ ha hr
  | ofCv u c ρ p =>
      cases hr with
      | link _ _ _ hb hr =>
          exact .cv c ρ _ ha ((worker_ofCv_reduction X C u c ρ ha) ▸ hr)
  | linkWk d k l ρ p =>
      cases hr with
      | link _ _ _ hb hr => exact .link l (.ins d k ρ) _ ha hr
  | prefixHead l hl rest p =>
      cases hr with
      | «prefix» _ _ _ _ hb hrest hr =>
          cases rest with
          | nil M =>
              exact .link l (.id C.Γ) _ hb ((worker_prefix_single_reduction X C l hb) ▸ hr)
          | cons l' hl' rest' =>
              have hb' := (Bool.and_eq_true_iff.mp hrest).1
              have hrest' := (Bool.and_eq_true_iff.mp hrest).2
              rw [worker_prefix_reduction X C l l' hl' rest' hb hb' hrest'] at hr
              cases hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
              | none => simp [hret] at hr
              | some r => exact .link l (.id C.Γ) _ hb (by rw [hret]; rfl)
  | prefixTail l hl l' hl' rest p hb r hret =>
      cases hr with
      | «prefix» _ _ _ _ hb₀ hrest hr =>
          have hb' := (Bool.and_eq_true_iff.mp hrest).1
          have hrest' := (Bool.and_eq_true_iff.mp hrest).2
          rw [worker_prefix_reduction X C l l' hl' rest hb hb' hrest', hret] at hr
          cases hret' : sprefixValleyVia X C.hΓ l' hb' rest hrest' with
          | none => simp [hret'] at hr
          | some r' => exact .prefix l' hl' rest _ hb' hrest' (by rw [hret']; rfl)
  | segmentSingle l hl hp p =>
      cases hr with
      | segment _ _ hadm hP hQ hr =>
          have hb : bLinkW l = true := by
            simpa only [Flat.segAdmW, hp, Bool.false_or] using hadm
          rw [worker_segment_single_reduction X C l hl hp hb hP hQ] at hr
          cases hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
          | none => simp [hret] at hr
          | some r => exact .link l (.id C.Γ) _ hb (by rw [hret]; rfl)
  | segmentMultiple l hl l' hl' rest p =>
      cases hr with
      | segment _ _ hadm hP hQ hr =>
          have hb := (Bool.and_eq_true_iff.mp hadm).1
          have hrest := (Bool.and_eq_true_iff.mp hadm).2
          rw [worker_segment_multiple_reduction X C l hl l' hl' rest hb hrest hP hQ] at hr
          cases hret : sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest) hrest with
          | none => simp [hret] at hr
          | some r => exact .prefix l hl (.cons l' hl' rest) _ hb hrest (by rw [hret]; rfl)
  | segmentsHead s hM rest p =>
      cases hr with
      | segments _ _ hadm hP hQ hr =>
          have hseg := (Bool.and_eq_true_iff.mp hadm).1
          have hrest := (Bool.and_eq_true_iff.mp hadm).2
          obtain ⟨A₁, B₁, hM'⟩ := isPiD _ hM
          subst hM'
          rw [worker_segments_reduction X C s rest hseg hrest hP hQ] at hr
          cases hret : xSegSVia X C.hΓ s hseg hP rfl with
          | none => simp [hret] at hr
          | some r => exact .segment s _ hseg hP rfl (by rw [hret]; rfl)
  | segmentsTail s hM rest p hP hM' hadm r hret =>
      cases hr with
      | segments _ _ hadm' hP' hQ hr =>
          have hseg := (Bool.and_eq_true_iff.mp hadm').1
          have hrest := (Bool.and_eq_true_iff.mp hadm').2
          subst hM'
          rw [worker_segments_reduction X C s rest hseg hrest hP' hQ] at hr
          cases hfirst : xSegSVia X C.hΓ s hseg hP' rfl with
          | none => simp [hfirst] at hr
          | some r₁ =>
              cases htail : xSegsSVia X C.hΓ rest hrest rfl hQ with
              | none => simp [hfirst, htail] at hr
              | some r₂ => exact .segments rest _ hrest rfl hQ (by rw [htail]; rfl)

/-- Global simulation: each finite graph path propagates independent admission
and actual successful return all the way to its terminal source-side J call. -/
theorem WorkerTraceW.success {X : SuppliersVia E n} {C : XEntryW E n}
    {s : WorkerSiteW C} {π q} (ht : WorkerTraceW X C s π q)
    (ha : s.Admitted) (hr : WorkerReturnsW X C s) : (q.answer X.J).isSome = true := by
  revert ha hr
  induction ht with
  | await q => intro _ hr; cases hr with | await _ h => exact h
  | step hs _ ih => intro ha hr; exact ih (hs.admitted ha) (hs.success ha hr)

/-- A successful original tile worker answers every source occurrence it
issued. This is the substantive whole-worker direction of correspondence. -/
theorem successful_worker_answers_issued (X : SuppliersVia E n) (C : XEntryW E n)
    {π q} (hi : IssuedBeforeAnswer X C π q)
    (hr : (xValleySVia? X C.hΓ C.c C.hadm).isSome = true) :
    (q.answer X.J).isSome = true := by
  apply hi.trace.success ⟨C.hadm, rfl, rfl⟩
  apply WorkerReturnsW.segments _ [] C.hadm rfl rfl
  simpa only [xValleySVia?, xValleySViaS?, ViaSEngine.xValleySViaS?,
    Option.isSome_map'] using hr

theorem issued_refusal_forces_original_worker_refusal (X : SuppliersVia E n)
    (C : XEntryW E n) {π q} (hi : IssuedBeforeAnswer X C π q)
    (hJ : q.answer X.J = none) : xValleySVia? X C.hΓ C.c C.hadm = none := by
  cases hX : xValleySVia? X C.hΓ C.c C.hadm with
  | none => rfl
  | some r =>
      have h := successful_worker_answers_issued X C hi (by rw [hX]; rfl)
      rw [hJ] at h
      cases h

/-! Exhaustiveness is proved from the supplier-independent demand relation,
not from the trace grammar. Successful original workers provide each actual
earlier return needed by a right/tail operational edge. In particular deleting
such an edge from both operational relations cannot preserve this theorem. -/

theorem NeedCvW.issued_of_return {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ a b T} {c : EvCv C.R Γ₀ a b T} {ρ p q} (hn : NeedCvW C c ρ p q) :
    (WorkerSiteW.cv c ρ p).Admitted → WorkerReturnsW X C (.cv c ρ p) →
      ∃ π, IssuedCvW X C c ρ p π q := by
  induction hn with
  | lit h hs ρ p => intro _ _; exact ⟨_, .lit h hs ρ p⟩
  | symm hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ha (WorkerStepW.success (.cvSymm _ _ _) ha hr)
      exact ⟨_, .symm hi⟩
  | left hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ((Bool.and_eq_true_iff.mp ha).1)
        (WorkerStepW.success (.cvLeft _ _ _ _) ha hr)
      exact ⟨_, .left hi⟩
  | @right Γ₀ a b c T c₁ c₂ ρ p q hn ih =>
      intro ha hr
      have hf := WorkerStepW.success (.cvLeft _ _ _ _) ha hr
      cases hf with
      | cv _ _ _ hb hsome =>
          cases hret : svalleyCvVia X c₁ ρ C.hΓ hb with
          | none => simp [hret] at hsome
          | some r =>
              obtain ⟨π, hi⟩ := ih ((Bool.and_eq_true_iff.mp ha).2)
                (WorkerStepW.success (.cvRight _ _ _ _ hb r hret) ha hr)
              exact ⟨_, .right hb r hret hi⟩
  | tyConv hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ha (WorkerStepW.success (.cvTyConv _ _ _ _ _) ha hr)
      exact ⟨_, .tyConv hi⟩
  | rety hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ha (WorkerStepW.success (.cvRety _ _ _ _) ha hr)
      exact ⟨_, .rety hi⟩
  | wk hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ha (WorkerStepW.success (.cvWk _ _ _ _ _) ha hr)
      exact ⟨_, .wk hi⟩

theorem NeedLinkW.issued_of_return {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ A B} {l : EvTc C.R Γ₀ A B} {ρ p q} (hn : NeedLinkW C l ρ p q) :
    (WorkerSiteW.link l ρ p).Admitted → WorkerReturnsW X C (.link l ρ p) →
      ∃ π, IssuedLinkW X C l ρ p π q := by
  induction hn with
  | ofCv hn =>
      intro ha hr
      obtain ⟨π, hi⟩ := hn.issued_of_return ha (WorkerStepW.success (.ofCv _ _ _ _) ha hr)
      exact ⟨_, .ofCv hi⟩
  | wk hn ih =>
      intro ha hr
      obtain ⟨π, hi⟩ := ih ha (WorkerStepW.success (.linkWk _ _ _ _ _) ha hr)
      exact ⟨_, .wk hi⟩

theorem NeedPrefixW.issued_of_return {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p q} (hn : NeedPrefixW C s p q) :
    (WorkerSiteW.prefix s p).Admitted → WorkerReturnsW X C (.prefix s p) →
      ∃ π, IssuedPrefixW X C s p π q := by
  induction hn with
  | head hn =>
      intro ha hr
      obtain ⟨π, hi⟩ := hn.issued_of_return ((Bool.and_eq_true_iff.mp ha).1)
        (WorkerStepW.success (.prefixHead _ _ _ _) ha hr)
      exact ⟨_, .head hi⟩
  | @tail P M Q l hl rest p q hn ih =>
      intro ha hr
      cases hr with
      | «prefix» _ _ _ _ hb hrest hsome =>
          cases rest with
          | nil M => cases hn
          | cons l' hl' rest' =>
              have hr : WorkerReturnsW X C (.prefix (.cons l hl (.cons l' hl' rest')) p) :=
                .prefix l hl (.cons l' hl' rest') p hb hrest hsome
              have hf := WorkerStepW.success (.prefixHead _ _ _ _) ha hr
              cases hf with
              | link _ _ _ hb hfirst =>
                  cases hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
                  | none => simp [hret] at hfirst
                  | some r =>
                      obtain ⟨π, hi⟩ := ih ((Bool.and_eq_true_iff.mp ha).2)
                        (WorkerStepW.success (.prefixTail _ _ _ _ _ _ hb r hret) ha hr)
                      exact ⟨_, .tail hb r hret hi⟩

theorem NeedSegW.issued_of_return {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p q} (hn : NeedSegW C s p q) :
    (WorkerSiteW.segment s p).Admitted → WorkerReturnsW X C (.segment s p) →
      ∃ π, IssuedSegW X C s p π q := by
  cases hn with
  | single hp hn =>
      intro ha hr
      obtain ⟨π, hi⟩ := hn.issued_of_return
        (WorkerStepW.admitted (X := X) (.segmentSingle _ _ hp _) ha)
        (WorkerStepW.success (.segmentSingle _ _ hp _) ha hr)
      exact ⟨_, .single hp hi⟩
  | multiple hn =>
      intro ha hr
      obtain ⟨π, hi⟩ := hn.issued_of_return
        (WorkerStepW.admitted (X := X) (.segmentMultiple ..) ha)
        (WorkerStepW.success (.segmentMultiple ..) ha hr)
      exact ⟨_, .multiple hi⟩

theorem NeedSegsW.issued_of_return {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Segs C.R C.Γ P Q} {p q} (hn : NeedSegsW C s p q) :
    (WorkerSiteW.segments s p).Admitted → WorkerReturnsW X C (.segments s p) →
      ∃ π, IssuedSegsW X C s p π q := by
  induction hn with
  | @head P M Q s hM rest p q hn =>
      intro ha hr
      have hs : WorkerStepW X C (.segments (.cons s hM rest) p)
          (.enter p) (.segment s (p ++ [.segmentHere])) :=
        .segmentsHead s hM rest p
      obtain ⟨π, hi⟩ := hn.issued_of_return (hs.admitted ha) (hs.success ha hr)
      exact ⟨_, .head hi⟩
  | @tail P M Q s hM rest p q hn ih =>
      intro ha hr
      have hf := WorkerStepW.success (.segmentsHead _ _ _ _) ha hr
      cases hf with
      | segment _ _ hadm hP hM' hfirst =>
          cases hret : xSegSVia X C.hΓ s hadm hP hM' with
          | none => simp [hret] at hfirst
          | some r =>
              have hs : WorkerStepW X C (.segments (.cons s hM rest) p)
                  (.returned (p ++ [.segmentHere])) (.segments rest (p ++ [.segmentNext])) :=
                .segmentsTail s hM rest p hP hM' hadm r hret
              obtain ⟨π, hi⟩ := ih (hs.admitted ha) (hs.success ha hr)
              exact ⟨_, .tail hP hM' hadm r hret hi⟩

/-- Exhaustive demand coverage on every successful execution of the original
worker. The antecedent supplies actual returns for all earlier siblings; the
proof starts from independent structural demand and cannot omit a branch. -/
theorem successful_worker_issues_every_need (X : SuppliersVia E n) (C : XEntryW E n)
    (hr : (xValleySVia? X C.hΓ C.c C.hadm).isSome = true)
    (q : JRequestW C) (hn : NeedW C q) : ∃ π, IssuedBeforeAnswer X C π q := by
  apply NeedSegsW.issued_of_return hn ⟨C.hadm, rfl, rfl⟩
  apply WorkerReturnsW.segments _ [] C.hadm rfl rfl
  simpa only [xValleySVia?, xValleySViaS?, ViaSEngine.xValleySViaS?,
    Option.isSome_map'] using hr

/-- The only admitted refusal boundaries after all relevant J-bearing child
workers have returned: the existing combiner or the existing reader. Each
constructor carries both actual successful child equations and the precise
non-J boundary equation. There is deliberately no arbitrary worker-none arm. -/
inductive NonJRefusalW (X : SuppliersVia E n) (C : XEntryW E n) : WorkerSiteW C → Prop where
  | cvCombine {Γ₀ a b c T} (c₁ : EvCv C.R Γ₀ a b T) (c₂ : EvCv C.R Γ₀ b c T)
      (ρ : Wk Γ₀ C.Γ) (p : Path) (hb₁ : bCvW c₁ = true) (hb₂ : bCvW c₂ = true)
      (r₁ : SOutB C.R C.Γ (ρ.map a) (ρ.map b) (ρ.map T) c₁.leaves)
      (r₂ : SOutB C.R C.Γ (ρ.map b) (ρ.map c) (ρ.map T) c₂.leaves)
      (h₁ : svalleyCvVia X c₁ ρ C.hΓ hb₁ = some r₁)
      (h₂ : svalleyCvVia X c₂ ρ C.hΓ hb₂ = some r₂)
      (hf : scombine (X.atSeg C.hΓ) r₁.1 r₁.2 r₂.1 r₂.2 = none) :
      NonJRefusalW X C (.cv (.trans c₁ c₂) ρ p)
  | prefixCombine {P M N Q} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (l' : EvTc C.R C.Γ M N) (hl' : isLink l' = true) (rest : Flat C.R C.Γ N Q)
      (p : Path) (hb : bLinkW l = true) (hb' : bLinkW l' = true)
      (hr : rest.bPrefixW = true)
      (r₁ : Σ T : Expr Nat, SOutB C.R C.Γ P M T l.leaves)
      (r₂ : Σ T : Expr Nat, SOutB C.R C.Γ M Q T (l'.leaves ++ rest.leaves))
      (h₁ : slinkValleyVia X l (.id C.Γ) C.hΓ hb = some r₁)
      (h₂ : sprefixValleyVia X C.hΓ l' hb' rest hr = some r₂)
      (hf : scombine (X.atSeg C.hΓ) r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2 = none) :
      NonJRefusalW X C (.prefix (.cons l hl (.cons l' hl' rest)) p)
  | singleRead {P Q A B A' B'} (l : EvTc C.R C.Γ P Q) (hl : isLink l = true)
      (p : Path) (hp : piSpinedTc l = false) (hb : bLinkW l = true)
      (hP : P = .pi A B) (hQ : Q = .pi A' B')
      (r : Σ T : Expr Nat, SOutB C.R C.Γ P Q T l.leaves)
      (hr : slinkValleyVia X l (.id C.Γ) C.hΓ hb = some r)
      (hf : sread (X.atSeg C.hΓ) r.2.1
        (SOut.bound_of_eq (L' := (Flat.cons l hl (.nil Q)).leaves) r.2.2
          (by simp only [Flat.leaves, List.append_nil])) hP hQ = none) :
      NonJRefusalW X C (.segment (.cons l hl (.nil Q)) p)
  | multipleRead {P M N Q A B A' B'} (l : EvTc C.R C.Γ P M) (hl : isLink l = true)
      (l' : EvTc C.R C.Γ M N) (hl' : isLink l' = true) (rest : Flat C.R C.Γ N Q)
      (p : Path) (hb : bLinkW l = true) (hrest : (Flat.cons l' hl' rest).bPrefixW = true)
      (hP : P = .pi A B) (hQ : Q = .pi A' B')
      (r : Σ T : Expr Nat, SOutB C.R C.Γ P Q T (l.leaves ++ (Flat.cons l' hl' rest).leaves))
      (hr : sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest) hrest = some r)
      (hf : sread (X.atSeg C.hΓ) r.2.1
        (SOut.bound_of_eq (L' := (Flat.cons l hl (.cons l' hl' rest)).leaves) r.2.2
          (by simp only [Flat.leaves])) hP hQ = none) :
      NonJRefusalW X C (.segment (.cons l hl (.cons l' hl' rest)) p)
  | litGate {Γ₀ a b T} (h : ConvT E n Γ₀ a b T)
      (hs : ∃ r ∈ C.R, SubEq (.cv h) r) (ρ : Wk Γ₀ C.Γ) (p : Path)
      (hb : bCvW (EvCv.lit h hs) = true) (V : Valley C.R Γ₀ a b T)
      (hJ : X.J C.R ⟨C.Γ, ρ, C.hΓ⟩ h hs = some V)
      (hg : Valley.admitSubst true V = none) :
      NonJRefusalW X C (.cv (.lit h hs) ρ p)

inductive WorkerFailureW (X : SuppliersVia E n) (C : XEntryW E n) : WorkerSiteW C → Prop where
  | refused (q : JRequestW C) (hr : q.answer X.J = none) : WorkerFailureW X C (.await q)
  | nonJ {s : WorkerSiteW C} : NonJRefusalW X C s → WorkerFailureW X C s
  | step {s t : WorkerSiteW C} {ev : PrefixEventW C} :
      WorkerStepW X C s ev t → WorkerFailureW X C t → WorkerFailureW X C s

inductive WorkerPathW (X : SuppliersVia E n) (C : XEntryW E n) :
    WorkerSiteW C → PrefixW C → WorkerSiteW C → Prop where
  | refl (s : WorkerSiteW C) : WorkerPathW X C s [] s
  | step {s t u : WorkerSiteW C} {ev : PrefixEventW C} {π} :
      WorkerStepW X C s ev t → WorkerPathW X C t π u → WorkerPathW X C s (ev :: π) u

theorem WorkerFailureW.decompose {X : SuppliersVia E n} {C : XEntryW E n}
    {s : WorkerSiteW C} (hf : WorkerFailureW X C s) :
    (∃ π q, WorkerTraceW X C s π q ∧ q.answer X.J = none) ∨
      (∃ π t, WorkerPathW X C s π t ∧ NonJRefusalW X C t) := by
  induction hf with
  | refused q hr => exact .inl ⟨[], q, .await q, hr⟩
  | nonJ h => exact .inr ⟨[], _, .refl _, h⟩
  | step hs _ ih =>
      rcases ih with ⟨π, q, ht, hr⟩ | ⟨π, t, ht, hr⟩
      · exact .inl ⟨_, q, .step hs ht, hr⟩
      · exact .inr ⟨_, t, .step hs ht, hr⟩

/-- Exhaustive inversion of the original conversion worker, including the
first refusing literal and every refusing right sibling reached after an
actual left return. Native unsupported forms contradict `hb`. -/
theorem cv_failure_complete (X : SuppliersVia E n) (C : XEntryW E n) :
    {Γ₀ : LCtx} → {a b T : Expr Nat} → (c : EvCv C.R Γ₀ a b T) →
    (ρ : Wk Γ₀ C.Γ) → (hb : bCvW c = true) → (p : Path) →
    svalleyCvVia X c ρ C.hΓ hb = none → WorkerFailureW X C (.cv c ρ p)
  | _, _, _, _, .lit h hs, ρ, hb, p, hr => by
      simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS] at hr
      split at hr
      · next he =>
          have hJ : X.J C.R ⟨C.Γ, ρ, C.hΓ⟩ h hs = none :=
            (JProcViaP.toViaSP_viaS X.J ρ C.hΓ h hs).symm.trans he
          exact .step (.literal h hs ρ p)
            (.refused (JRequestW.at C p ρ h hs)
              (by simpa [JRequestW.answer, JRequestW.at] using hJ))
      · next V he =>
          have hJ : X.J C.R ⟨C.Γ, ρ, C.hΓ⟩ h hs = some V :=
            (JProcViaP.toViaSP_viaS X.J ρ C.hΓ h hs).symm.trans he
          cases hg : Valley.admitSubst true V with
          | none => exact .nonJ (.litGate h hs ρ p hb V hJ hg)
          | some _ =>
              simp only [hg] at hr
              cases hr
  | _, _, _, _, .refl D, ρ, hb, p, hr => by
      simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS,
        Option.some_ne_none] at hr
  | _, _, _, _, .symm c, ρ, hb, p, hr => by
      have hc : svalleyCvVia X c ρ C.hΓ hb = none := by
        cases hret : svalleyCvVia X c ρ C.hΓ hb with
        | none => rfl
        | some r =>
            simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS] at hr
            have hret' := hret
            simp only [svalleyCvVia, svalleyCvViaS] at hret'
            simp only [hret', Option.map_some'] at hr
            cases hr
      exact .step (.cvSymm c ρ p) (cv_failure_complete X C c ρ hb _ hc)
  | _, _, _, _, .trans c₁ c₂, ρ, hb, p, hr => by
      have h₁ := (Bool.and_eq_true_iff.mp hb).1
      have h₂ := (Bool.and_eq_true_iff.mp hb).2
      rw [worker_trans_reduction X C c₁ c₂ ρ h₁ h₂] at hr
      cases hr₁ : svalleyCvVia X c₁ ρ C.hΓ h₁ with
      | none => exact .step (.cvLeft c₁ c₂ ρ p) (cv_failure_complete X C c₁ ρ h₁ _ hr₁)
      | some r₁ =>
          cases hr₂ : svalleyCvVia X c₂ ρ C.hΓ h₂ with
          | none =>
              exact .step (.cvRight c₁ c₂ ρ p h₁ r₁ hr₁)
                (cv_failure_complete X C c₂ ρ h₂ _ hr₂)
          | some r₂ =>
              have hf : scombine (X.atSeg C.hΓ) r₁.1 r₁.2 r₂.1 r₂.2 = none := by
                cases hcomb : scombine (X.atSeg C.hΓ) r₁.1 r₁.2 r₂.1 r₂.2 with
                | none => rfl
                | some r => simp only [hr₁, hr₂, hcomb, Option.map_some', Option.some_ne_none] at hr
              exact .nonJ (.cvCombine c₁ c₂ ρ p h₁ h₂ r₁ r₂ hr₁ hr₂ hf)
  | _, _, _, _, .tyConv u c cA, ρ, hb, p, hr => by
      have hc : svalleyCvVia X c ρ C.hΓ hb = none := by
        cases hret : svalleyCvVia X c ρ C.hΓ hb with
        | none => rfl
        | some r =>
            simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS] at hr
            have hret' := hret
            simp only [svalleyCvVia, svalleyCvViaS] at hret'
            simp only [hret', Option.map_some'] at hr
            cases hr
      exact .step (.cvTyConv u c cA ρ p) (cv_failure_complete X C c ρ hb _ hc)
  | _, _, _, _, .wk d k c, ρ, hb, p, hr =>
      .step (.cvWk d k c ρ p) (cv_failure_complete X C c (.ins d k ρ) hb _ hr)
  | _, _, _, _, .esub .., _, hb, _, _ => nomatch hb
  | _, _, _, _, .subst0 .., _, hb, _, _ => nomatch hb
  | _, _, _, _, .substLet .., _, hb, _, _ => nomatch hb
  | _, _, _, _, .sorts .., _, hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., _, hb, _, _ => nomatch hb
  | _, _, _, _, .rety c cA, ρ, hb, p, hr => by
      have hc : svalleyCvVia X c ρ C.hΓ hb = none := by
        cases hret : svalleyCvVia X c ρ C.hΓ hb with
        | none => rfl
        | some r =>
            simp only [svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS] at hr
            have hret' := hret
            simp only [svalleyCvVia, svalleyCvViaS] at hret'
            simp only [hret', Option.map_some'] at hr
            cases hr
      exact .step (.cvRety c cA ρ p) (cv_failure_complete X C c ρ hb _ hc)

theorem link_failure_complete (X : SuppliersVia E n) (C : XEntryW E n) :
    {Γ₀ : LCtx} → {A B : Expr Nat} → (l : EvTc C.R Γ₀ A B) →
    (ρ : Wk Γ₀ C.Γ) → (hb : bLinkW l = true) → (p : Path) →
    slinkValleyVia X l ρ C.hΓ hb = none → WorkerFailureW X C (.link l ρ p)
  | _, _, _, .ofCv u c, ρ, hb, p, hr => by
      have hc : svalleyCvVia X c ρ C.hΓ hb = none := by
        cases hret : svalleyCvVia X c ρ C.hΓ hb with
        | none => rfl
        | some r =>
            simp only [slinkValleyVia, slinkValleyViaS, ViaSEngine.slinkValleyViaS,
              svalleyCvVia, svalleyCvViaS, ViaSEngine.svalleyCvViaS] at hr
            have hret' := hret
            simp only [svalleyCvVia, svalleyCvViaS] at hret'
            simp only [hret', Option.map_some'] at hr
            cases hr
      exact .step (.ofCv u c ρ p) (cv_failure_complete X C c ρ hb _ hc)
  | _, _, _, .wk d k l, ρ, hb, p, hr =>
      .step (.linkWk d k l ρ p) (link_failure_complete X C l (.ins d k ρ) hb _ hr)
  | _, _, _, .piCod .., _, hb, _, _ => nomatch hb
  | _, _, _, .subst0 .., _, hb, _, _ => nomatch hb
  | _, _, _, .substLet .., _, hb, _, _ => nomatch hb
  | _, _, _, .lit .., _, hb, _, _ => nomatch hb
  | _, _, _, .refl .., _, hb, _, _ => nomatch hb
  | _, _, _, .symm .., _, hb, _, _ => nomatch hb
  | _, _, _, .trans .., _, hb, _, _ => nomatch hb

theorem prefix_failure_complete (X : SuppliersVia E n) (C : XEntryW E n) :
    {P M Q : Expr Nat} → (l : EvTc C.R C.Γ P M) → (hl : isLink l = true) →
    (hb : bLinkW l = true) → (rest : Flat C.R C.Γ M Q) →
    (hrest : rest.bPrefixW = true) → (p : Path) →
    sprefixValleyVia X C.hΓ l hb rest hrest = none →
    WorkerFailureW X C (.prefix (.cons l hl rest) p)
  | _, _, _, l, hl, hb, .nil _, hrest, p, hr => by
      cases hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
      | none =>
          exact .step (.prefixHead l hl (.nil _) p)
            (link_failure_complete X C l (.id C.Γ) hb _ hret)
      | some r =>
          simp only [sprefixValleyVia, sprefixValleyViaS, ViaSEngine.sprefixValleyViaS,
            slinkValleyVia, slinkValleyViaS, ViaSEngine.slinkValleyViaS] at hr
          have hret' := hret
          simp only [slinkValleyVia, slinkValleyViaS] at hret'
          simp only [hret', Option.map_some'] at hr
          cases hr
  | _, _, _, l, hl, hb, .cons l' hl' rest, hrest, p, hr => by
      have hb' := (Bool.and_eq_true_iff.mp hrest).1
      have hr' := (Bool.and_eq_true_iff.mp hrest).2
      rw [worker_prefix_reduction X C l l' hl' rest hb hb' hr'] at hr
      cases hr₁ : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
      | none =>
          exact .step (.prefixHead l hl _ p)
            (link_failure_complete X C l (.id C.Γ) hb _ hr₁)
      | some r₁ =>
          cases hr₂ : sprefixValleyVia X C.hΓ l' hb' rest hr' with
          | none =>
              exact .step (.prefixTail l hl l' hl' rest p hb r₁ hr₁)
                (prefix_failure_complete X C l' hl' hb' rest hr' _ hr₂)
          | some r₂ =>
              have hf : scombine (X.atSeg C.hΓ) r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2 = none := by
                cases hcomb : scombine (X.atSeg C.hΓ) r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2 with
                | none => rfl
                | some r => simp only [hr₁, hr₂, hcomb, Option.map_some', Option.some_ne_none] at hr
              exact .nonJ (.prefixCombine l hl l' hl' rest p hb hb' hr' r₁ r₂ hr₁ hr₂ hf)

theorem segment_failure_complete (X : SuppliersVia E n) (C : XEntryW E n) :
    {P Q : Expr Nat} → (s : Flat C.R C.Γ P Q) → (ha : s.segAdmW = true) →
    {A B A' B' : Expr Nat} → (hP : P = .pi A B) → (hQ : Q = .pi A' B') → (p : Path) →
    xSegSVia X C.hΓ s ha hP hQ = none → WorkerFailureW X C (.segment s p)
  | _, _, .nil _, ha, _, _, _, _, hP, hQ, p, hr => by
      simp only [xSegSVia, xSegSViaS, ViaSEngine.xSegSViaS,
        Option.some_ne_none] at hr
  | _, _, .cons l hl (.nil _), ha, _, _, _, _, hP, hQ, p, hr => by
      by_cases hp : piSpinedTc l = true
      · simp only [xSegSVia, xSegSViaS, ViaSEngine.xSegSViaS, dif_pos hp,
          Option.some_ne_none] at hr
      · have hpf : piSpinedTc l = false := Bool.eq_false_iff.mpr hp
        have hb : bLinkW l = true := by
          simpa only [Flat.segAdmW, hpf, Bool.false_or] using ha
        rw [worker_segment_single_reduction X C l hl hpf hb hP hQ] at hr
        cases hret : slinkValleyVia X l (.id C.Γ) C.hΓ hb with
        | none =>
            exact .step (.segmentSingle l hl hpf p)
              (link_failure_complete X C l (.id C.Γ) hb _ hret)
        | some r =>
            have hf : sread (X.atSeg C.hΓ) r.2.1
                (SOut.bound_of_eq (L' := (Flat.cons l hl (.nil _)).leaves) r.2.2
                  (by simp only [Flat.leaves, List.append_nil])) hP hQ = none := by
              simpa only [hret] using hr
            exact .nonJ (.singleRead l hl p hpf hb hP hQ r hret hf)
  | _, _, .cons l hl (.cons l' hl' rest), ha, _, _, _, _, hP, hQ, p, hr => by
      have hb := (Bool.and_eq_true_iff.mp ha).1
      have hrest := (Bool.and_eq_true_iff.mp ha).2
      rw [worker_segment_multiple_reduction X C l hl l' hl' rest hb hrest hP hQ] at hr
      cases hret : sprefixValleyVia X C.hΓ l hb (.cons l' hl' rest) hrest with
      | none =>
          exact .step (.segmentMultiple l hl l' hl' rest p)
            (prefix_failure_complete X C l hl hb (.cons l' hl' rest) hrest _ hret)
      | some r =>
          have hf : sread (X.atSeg C.hΓ) r.2.1
              (SOut.bound_of_eq (L' := (Flat.cons l hl (.cons l' hl' rest)).leaves) r.2.2
                (by simp only [Flat.leaves])) hP hQ = none := by
            simpa only [hret] using hr
          exact .nonJ (.multipleRead l hl l' hl' rest p hb hrest hP hQ r hret hf)

theorem segments_failure_complete (X : SuppliersVia E n) (C : XEntryW E n) :
    {P Q : Expr Nat} → (s : Segs C.R C.Γ P Q) → (ha : s.admW = true) →
    {A B A' B' : Expr Nat} → (hP : P = .pi A B) → (hQ : Q = .pi A' B') → (p : Path) →
    xSegsSVia X C.hΓ s ha hP hQ = none → WorkerFailureW X C (.segments s p) := by
  intro P Q s
  induction s with
  | nil Q =>
      intro ha A B A' B' hP hQ p hr
      simp only [xSegsSVia, xSegsViaS, ViaSEngine.xSegsViaS,
        Option.some_ne_none] at hr
  | @cons P M Q s hM rest ih =>
      intro ha A B A' B' hP hQ p hr
      have hseg := (Bool.and_eq_true_iff.mp ha).1
      have hrest := (Bool.and_eq_true_iff.mp ha).2
      obtain ⟨A₁, B₁, hM'⟩ := isPiD _ hM
      subst hM'
      rw [worker_segments_reduction X C s rest hseg hrest hP hQ] at hr
      cases hr₁ : xSegSVia X C.hΓ s hseg hP rfl with
      | none =>
          exact .step (.segmentsHead s hM rest p)
            (segment_failure_complete X C s hseg hP rfl _ hr₁)
      | some r₁ =>
          cases hr₂ : xSegsSVia X C.hΓ rest hrest rfl hQ with
          | none =>
              exact .step (.segmentsTail s hM rest p hP rfl hseg r₁ hr₁)
                (ih hrest rfl hQ _ hr₂)
          | some r₂ => simp only [hr₁, hr₂, Option.some_ne_none] at hr

/-- Every refusal of the original tile is accounted for by an issued declining
J call, or an explicitly reached original combine/read refusal after its
children returned. This includes failed executions, so a refusing branch
cannot disappear from the operational relation. -/
theorem original_worker_refusal_decomposition (X : SuppliersVia E n) (C : XEntryW E n)
    (hr : xValleySVia? X C.hΓ C.c C.hadm = none) :
    (∃ π q, IssuedBeforeAnswer X C π q ∧ q.answer X.J = none) ∨
      (∃ π t, WorkerPathW X C (.segments ((flattenTc C.c).segment rfl) []) π t ∧
        NonJRefusalW X C t) := by
  have hs : xSegsSVia X C.hΓ ((flattenTc C.c).segment rfl) C.hadm rfl rfl = none := by
    cases hret : xSegsSVia X C.hΓ ((flattenTc C.c).segment rfl) C.hadm rfl rfl with
    | none => rfl
    | some r =>
        simp only [xValleySVia?, xValleySViaS?, ViaSEngine.xValleySViaS?] at hr
        have hret' := hret
        simp only [xSegsSVia, xSegsViaS] at hret'
        simp only [hret', Option.map_some'] at hr
        cases hr
  rcases (segments_failure_complete X C _ C.hadm rfl rfl [] hs).decompose with
    ⟨π, q, ht, hJ⟩ | hnonJ
  · exact .inl ⟨π, q, (issued_iff_existing_worker_trace X C π q).mpr ht, hJ⟩
  · exact .inr hnonJ

/-! Forgetting the operational gates gives structural demand, never the
converse: an earlier refusal can prevent issuance of a later demand. -/

theorem IssuedCvW.need {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ a b T} {c : EvCv C.R Γ₀ a b T} {ρ p π q}
    (h : IssuedCvW X C c ρ p π q) : NeedCvW C c ρ p q := by
  induction h with
  | lit h hs ρ p => exact .lit h hs ρ p
  | symm _ ih => exact .symm ih
  | left _ ih => exact .left ih
  | right hb r hr _ ih => exact .right ih
  | tyConv _ ih => exact .tyConv ih
  | rety _ ih => exact .rety ih
  | wk _ ih => exact .wk ih

theorem IssuedLinkW.need {X : SuppliersVia E n} {C : XEntryW E n}
    {Γ₀ A B} {l : EvTc C.R Γ₀ A B} {ρ p π q}
    (h : IssuedLinkW X C l ρ p π q) : NeedLinkW C l ρ p q := by
  induction h with
  | ofCv h => exact .ofCv h.need
  | wk _ ih => exact .wk ih

theorem IssuedPrefixW.need {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p π q}
    (h : IssuedPrefixW X C s p π q) : NeedPrefixW C s p q := by
  induction h with
  | head h => exact .head h.need
  | tail hb r hr _ ih => exact .tail ih

theorem IssuedSegW.need {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Flat C.R C.Γ P Q} {p π q}
    (h : IssuedSegW X C s p π q) : NeedSegW C s p q := by
  cases h with
  | single hp h => exact .single hp h.need
  | multiple h => exact .multiple h.need

theorem IssuedSegsW.need {X : SuppliersVia E n} {C : XEntryW E n}
    {P Q} {s : Segs C.R C.Γ P Q} {p π q}
    (h : IssuedSegsW X C s p π q) : NeedSegsW C s p q := by
  induction h with
  | head h => exact .head h.need
  | tail hP hM ha r hr _ ih => exact .tail ih

theorem issued_before_answer_is_needed {X : SuppliersVia E n} {C : XEntryW E n}
    {π : PrefixW C} {q : JRequestW C} (h : IssuedBeforeAnswer X C π q) : NeedW C q :=
  h.need

/-- The literal call is exposed before its answer, including a refusing answer.
This applies to every raw ConvT constructor, not just J5a's fragment. -/
theorem every_literal_invocation_is_issued (X : SuppliersVia E n) (C : XEntryW E n)
    {Γ₀ a b T} (h : ConvT E n Γ₀ a b T)
    (hs : ∃ r ∈ C.R, SubEq (.cv h) r) (ρ : Wk Γ₀ C.Γ) (p : Path) :
    IssuedCvW X C (.lit h hs) ρ p
      [.awaitJ (JRequestW.at C p ρ h hs)] (JRequestW.at C p ρ h hs) :=
  .lit h hs ρ p

/-- A successful literal worker implies a successful source-side J call.
The converse `isSome` equality is false: `admitSubst` can refuse a valley
J already returned. -/
theorem literal_worker_answer_correspondence (X : SuppliersVia E n)
    {C : XEntryW E n} (q : JRequestW C) :
    (q.literalWorker X).isSome = true → (q.answer X.J).isSome = true := by
  cases q with
  | mk Γ₀ a b T h hs v p =>
      cases v with
      | mk target ρ wf =>
          intro hr
          rcases (literal_isSome X h hs ρ wf rfl).mp
            (by simpa [JRequestW.literalWorker] using hr) with ⟨_, hJ, _⟩
          simp [JRequestW.answer, hJ]

/-- J refusal implies refusal of the existing literal worker. The converse
is false: the `admitSubst` gate refuses some valleys J returns. -/
theorem literal_worker_refusal_correspondence (X : SuppliersVia E n)
    {C : XEntryW E n} (q : JRequestW C) :
    q.answer X.J = none → q.literalWorker X = none := by
  cases q with
  | mk Γ₀ a b T h hs v p =>
      cases v with
      | mk target ρ wf =>
          intro hJ
          cases hw : svalleyCvVia X (.lit h hs) ρ wf rfl with
          | none => simpa [JRequestW.literalWorker] using hw
          | some _ =>
              rcases (literal_isSome X h hs ρ wf rfl).mp (by simp [hw]) with
                ⟨_, hJV, _⟩
              simp only [JRequestW.answer] at hJ
              rw [hJ] at hJV
              cases hJV

/-- A refused request is still in demand, and this is precisely a refusal of
the existing literal arm. It is not a claim that execution continues. -/
theorem refusing_prefix_keeps_demand {X : SuppliersVia E n} {C : XEntryW E n}
    {π : PrefixW C} {q : JRequestW C} (hi : IssuedBeforeAnswer X C π q)
    (hr : q.answer X.J = none) : NeedW C q ∧ q.literalWorker X = none :=
  ⟨issued_before_answer_is_needed hi,
    literal_worker_refusal_correspondence X q hr⟩

/-! Wrapper-sensitive classification. A raw literal is selected as a whole;
native unsupported forms have no selection constructor. Index and typing
premises are absent from the demand grammar. -/

/-- Inspecting the root before specializing indices avoids requiring
injectivity of the expression operations used by weakening and substitution. -/
private def NeedCvRootView (C : XEntryW E n) :
    {Γ₀ : LCtx} → {a b T : Expr Nat} → (c : EvCv C.R Γ₀ a b T) →
    Wk Γ₀ C.Γ → Path → JRequestW C → Prop
  | _, _, _, _, .wk d k c, ρ, p, q => NeedCvW C c (.ins d k ρ) (p ++ [.cvWk]) q
  | _, _, _, _, .refl _, _, _, _ => False
  | _, _, _, _, .sorts .., _, _, _ => False
  | _, _, _, _, .consts .., _, _, _ => False
  | _, _, _, _, .esub .., _, _, _ => False
  | _, _, _, _, _, _, _, _ => True

private theorem needCv_rootView {C : XEntryW E n} {Γ₀ a b T}
    {c : EvCv C.R Γ₀ a b T} {ρ p q} (h : NeedCvW C c ρ p q) :
    NeedCvRootView C c ρ p q := by
  cases h with
  | lit => trivial
  | symm _ => trivial
  | left _ => trivial
  | right _ => trivial
  | tyConv _ => trivial
  | rety _ => trivial
  | wk h => exact h

theorem literal_has_demand (C : XEntryW E n) {Γ₀ a b T}
    (h : ConvT E n Γ₀ a b T) (hs : ∃ r ∈ C.R, SubEq (.cv h) r)
    (ρ : Wk Γ₀ C.Γ) (p : Path) :
    NeedCvW C (.lit h hs) ρ p (JRequestW.at C p ρ h hs) := .lit h hs ρ p

theorem refl_has_no_demand (C : XEntryW E n) {Γ₀ a T}
    (D : EvTy C.R Γ₀ a T) (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    ¬ NeedCvW C (.refl D) ρ p q := by intro h; exact needCv_rootView h

theorem empty_segment_has_no_demand (C : XEntryW E n) (P : Expr Nat)
    (p : Path) (q : JRequestW C) : ¬ NeedSegW C (.nil P) p q := by
  intro h; cases h

theorem stratumA_has_no_demand (C : XEntryW E n) {P Q}
    (l : EvTc C.R C.Γ P Q) (hl : isLink l = true)
    (hp : piSpinedTc l = true) (p : Path) (q : JRequestW C) :
    ¬ NeedSegW C (.cons l hl (.nil Q)) p q := by
  intro h
  cases h with
  | single hf _ => rw [hp] at hf; cases hf

theorem native_sorts_has_no_demand (C : XEntryW E n) {Γ₀}
    (l₁ l₂ : Level) (h : eqN l₁ l₂) (ρ : Wk Γ₀ C.Γ)
    (p : Path) (q : JRequestW C) :
    ¬ NeedCvW C (EvCv.sorts l₁ l₂ h) ρ p q := by intro hd; exact needCv_rootView hd

theorem symm_demand_iff (C : XEntryW E n) {Γ₀ a b T}
    (c : EvCv C.R Γ₀ a b T) (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    NeedCvW C (.symm c) ρ p q ↔ NeedCvW C c ρ (p ++ [.cvSymm]) q := by
  constructor
  · intro h; cases h with | symm h => exact h
  · exact NeedCvW.symm

theorem trans_demand_iff (C : XEntryW E n) {Γ₀ a b c T}
    (c₁ : EvCv C.R Γ₀ a b T) (c₂ : EvCv C.R Γ₀ b c T)
    (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    NeedCvW C (.trans c₁ c₂) ρ p q ↔
      NeedCvW C c₁ ρ (p ++ [.cvLeft]) q ∨ NeedCvW C c₂ ρ (p ++ [.cvRight]) q := by
  constructor
  · intro h; cases h with
    | left h => exact .inl h
    | right h => exact .inr h
  · intro h; exact h.elim NeedCvW.left NeedCvW.right

/-- The index child contributes no demand, regardless of its own literals. -/
theorem tyConv_demand_iff (C : XEntryW E n) {Γ₀ a b T T'} (u : Level)
    (c : EvCv C.R Γ₀ a b T) (cA : EvCv C.R Γ₀ T T' (.sort u))
    (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    NeedCvW C (.tyConv u c cA) ρ p q ↔ NeedCvW C c ρ (p ++ [.cvTyConv]) q := by
  constructor
  · intro h; cases h with | tyConv h => exact h
  · exact NeedCvW.tyConv

theorem rety_demand_iff (C : XEntryW E n) {Γ₀ a b T T'}
    (c : EvCv C.R Γ₀ a b T) (cA : EvTc C.R Γ₀ T T')
    (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    NeedCvW C (.rety c cA) ρ p q ↔ NeedCvW C c ρ (p ++ [.cvRety]) q := by
  constructor
  · intro h; cases h with | rety h => exact h
  · exact NeedCvW.rety

theorem wk_demand_iff (C : XEntryW E n) {Γ₀ a b T} (d : LocalDecl) (k : Nat)
    (c : EvCv C.R Γ₀ a b T) (ρ : Wk (insertAt d k Γ₀) C.Γ)
    (p : Path) (q : JRequestW C) :
    NeedCvW C (.wk d k c) ρ p q ↔ NeedCvW C c (.ins d k ρ) (p ++ [.cvWk]) q := by
  constructor
  · intro h; exact needCv_rootView h
  · exact NeedCvW.wk

theorem native_consts_has_no_demand (C : XEntryW E n) {Γ₀}
    (r : Nat) (ls ls' : List Level) (m : CheckedMember)
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (heq : eqNList ls ls') (ρ : Wk Γ₀ C.Γ) (p : Path) (q : JRequestW C) :
    ¬ NeedCvW C (EvCv.consts r ls ls' m hres hlen hwf hwf' heq) ρ p q := by
  intro h; exact needCv_rootView h

theorem native_esub_has_no_demand (C : XEntryW E n) {Γ₀ a b T t v}
    (j : Nat) (u : Level) (c : EvCv C.R Γ₀ a b T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy C.R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (hvT : EvTy C.R (substRemove v j Γ₀) (lift 0 j t) (.sort u))
    (ρ : Wk (substRemove v j Γ₀) C.Γ) (p : Path) (q : JRequestW C) :
    ¬ NeedCvW C (EvCv.esub j u c hget hv hvT) ρ p q := by
  intro h; exact needCv_rootView h

end Rcic.Declarative.F8Measure.JTotality

#print axioms Rcic.Declarative.F8Measure.JTotality.issued_before_answer_is_needed
#print axioms Rcic.Declarative.F8Measure.JTotality.literal_worker_answer_correspondence
#print axioms Rcic.Declarative.F8Measure.JTotality.literal_worker_refusal_correspondence
#print axioms Rcic.Declarative.F8Measure.JTotality.refusing_prefix_keeps_demand
#print axioms Rcic.Declarative.F8Measure.JTotality.stratumA_has_no_demand
#print axioms Rcic.Declarative.F8Measure.JTotality.issued_iff_existing_worker_trace
#print axioms Rcic.Declarative.F8Measure.JTotality.successful_worker_answers_issued
#print axioms Rcic.Declarative.F8Measure.JTotality.issued_refusal_forces_original_worker_refusal
#print axioms Rcic.Declarative.F8Measure.JTotality.successful_worker_issues_every_need
#print axioms Rcic.Declarative.F8Measure.JTotality.original_worker_refusal_decomposition
#print axioms Rcic.Declarative.F8Measure.JTotality.needed_has_its_raw_row
#print axioms Rcic.Declarative.F8Measure.JTotality.needRow_is_needed
#print axioms Rcic.Declarative.F8Measure.JTotality.OriginalJChildAtW.nonempty
