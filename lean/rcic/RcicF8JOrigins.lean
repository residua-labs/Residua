import rcic.RcicF8IrrPositions
import rcic.RcicF8JTransport

/-!
J4: the output half of #7056's F8-OCC-POSITION cross-reference.
The shared JContractWf remains unchanged. The additional origin obligation
is explicit and NOT inferred from strict leaves. Proved below only for the
actual J1/J3 fragment, with equality to #7056's original proof-site data.
No translation of HasTyT premises or the tyConv index field; no new carrier,
D supplier, input-classification rewrite, or full J supplier. closure_claim=0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JOrigins
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- The immutable raw proof site; host index and its chain are separate data. -/
def proofSite (s : IrrSite R) : ProofSite E n :=
  ⟨s.ctx, s.p, s.q, s.P, s.P, s.hP, s.hP, s.hp, s.hq⟩

/-- Projection from the EXISTING translated-path classifier, not a new traversal. -/
def core : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrOcc h → ProofSite E n
  | _, _, _, _, _, .irr (Γ := Γ) (P := P) (p := p) (q := q)
      (hP := hP) (hp := hp) (hq := hq) => ⟨Γ,p,q,P,P,hP,hP,hp,hq⟩
  | _, _, _, _, _, .symm o => core o
  | _, _, _, _, _, .transLeft _ o => core o
  | _, _, _, _, _, .transRight _ o => core o
  | _, _, _, _, _, .tyConv _ o => core o
  | _, _, _, _, _, .appFun _ o => core o
  | _, _, _, _, _, .appArg _ o => core o
  | _, _, _, _, _, .lamDom _ o => core o
  | _, _, _, _, _, .lamBody _ o => core o
  | _, _, _, _, _, .piDom _ o => core o
  | _, _, _, _, _, .piCod _ o => core o
  | _, _, _, _, _, .letEAnn _ _ o => core o
  | _, _, _, _, _, .letEVal _ _ o => core o
  | _, _, _, _, _, .letEBody _ _ o => core o

theorem siteAux_core : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → (o : IrrOcc h) → {top : Expr Nat} →
    (acc : IrrChain R Γ top T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    proofSite (IrrOcc.siteAux o acc hs) = core o
  | _, _, _, _, _, .irr, _, _, _ => rfl
  | _, _, _, _, _, .symm o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .transLeft _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .transRight _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .tyConv _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .appFun _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .appArg _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .lamDom _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .lamBody _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .piDom _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .piCod _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .letEAnn _ _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .letEVal _ _ o, _, _, _ => siteAux_core o _ _
  | _, _, _, _, _, .letEBody _ _ o, _, _, _ => siteAux_core o _ _

theorem site_core {Γ : LCtx} {a b T : Expr Nat} {h : ConvT E n Γ a b T}
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (o : IrrOcc h) :
    proofSite (o.site h hs) = core o := siteAux_core o .nil hs

/-- Every actual emitted occurrence has an explicit source, including exact typing data. -/
abbrev AtSource {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T)
    (s : ProofSite E n) : Type := Σ' o : IrrOcc h, PLift (core o = s)

def AtSource.classifiedSite {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} {s : ProofSite E n} (m : AtSource h s)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Σ' o : IrrOcc h, PLift (proofSite (o.site h hs) = s) :=
  ⟨m.1, ⟨(site_core hs m.1).trans m.2.down⟩⟩

variable {Γ : LCtx} {a b T : Expr Nat} {h : ConvT E n Γ a b T}

/-- Output occurrences are enumerated by the EXISTING Occ of each actual step. -/
abbrev StepOrigins (h : ConvT E n Γ a b T) {Δ : LCtx} {x y U : Expr Nat}
    (s : ParRedT (PEqLeafT E n) E n Δ x y U) : Type :=
  (o : Occ s) → AtSource h (site s o)

/-- Proof data indexed by an EXISTING star. No new step/val/leaves relation. -/
def StarOrigins (h : ConvT E n Γ a b T) {Δ : LCtx} {x y U : Expr Nat}
    (s : ParRedTStar (PEqLeafT E n) E n Δ x y U) : Type := by
  induction s with
  | refl => exact PUnit
  | tail t _ ih => exact StepOrigins h t × ih

section Retarget
variable {Γ' : LCtx} {a' b' T' : Expr Nat} {h' : ConvT E n Γ' a' b' T'}

def StarOrigins.retarget (f : IrrOcc h → IrrOcc h')
    (hf : ∀ o, core (f o) = core o) :
    {Δ : LCtx} → {x y U : Expr Nat} →
    (ss : ParRedTStar (PEqLeafT E n) E n Δ x y U) →
    StarOrigins h ss → StarOrigins h' ss
  | _, _, _, _, .refl .., _ => PUnit.unit
  | _, _, _, _, .tail s ss, c =>
    ⟨(fun o => let m := c.1 o
               ⟨f m.1, ⟨(hf m.1).trans m.2.down⟩⟩),
     StarOrigins.retarget f hf ss c.2⟩
end Retarget

def StarOrigins.reindex {Δ : LCtx} {U V : Expr Nat} (tc : TyConvT E n Δ U V) :
    {x y : Expr Nat} → (ss : ParRedTStar (PEqLeafT E n) E n Δ x y U) →
    StarOrigins h ss → StarOrigins h (parRedTStar_conv tc ss)
  | _, _, .refl .., _ => PUnit.unit
  | _, _, .tail _ ss, c => ⟨(fun o => c.1 o), StarOrigins.reindex tc ss c.2⟩

/-- Both legs, not just the nontrivial one. -/
def ValleyOrigins (hW : EnvWfT E) (h : ConvT E n Γ a b T)
    (V : Valley R Γ a b T) : Type :=
  StarOrigins h (V.left.val (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW)) ×
  StarOrigins h (V.right.val (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW))

/-- Named additional obligation for a TOTAL JProcWf. No supplier is asserted here.
For future D-generated or substituted sites, a separate transport/generated-origin
contract may be needed; the literal equality clause is proved for direct J1/J3 only. -/
def JOriginContractWf (hW : EnvWfT E) (J : ∀ R : List (Jd E n), JProcWf R) : Prop :=
  ∀ R {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r),
    Nonempty (ValleyOrigins hW h (J R hΓ h hs))

/-- The shared all-leaf contract is kept, not replaced by occurrence bookkeeping. -/
def JContractWfWithOrigins (hW : EnvWfT E)
    (J : ∀ R : List (Jd E n), JProcWf R) : Prop :=
  JContractWf J ∧ JOriginContractWf hW J

theorem contract_strict (hW : EnvWfT E) (J : ∀ R : List (Jd E n), JProcWf R)
    (c : JContractWfWithOrigins hW J) : JContractWf J := c.1

/-- Actual J1 bases: refl emits nothing even if its HasTyT input contains irr. -/
def refl_origins (hW : EnvWfT E) (ha : HasTyT E n Γ a T)
    (hs : ∃ r ∈ R, SubEq (.cv (.refl Γ a T ha)) r) :
    ValleyOrigins hW (.refl Γ a T ha) (J3.reflResult hW ha hs).valley :=
  ⟨PUnit.unit, PUnit.unit⟩

def irr_origins (hW : EnvWfT E) {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P)
    (hs : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) :
    ValleyOrigins hW (.irr Γ P p q hP hp hq) (J3.irrResult hW hP hp hq hs).valley :=
  ⟨⟨(fun o => by cases o; exact ⟨.irr, ⟨rfl⟩⟩), PUnit.unit⟩, PUnit.unit⟩

def swap_origins {hW : EnvWfT E} (out : J3.Result hW R h)
    (m : ValleyOrigins hW h out.valley) :
    ValleyOrigins hW (.symm Γ a b T h) out.swap.valley :=
  ⟨StarOrigins.retarget IrrOcc.symm (fun o => by simp only [core]) _ m.2,
   StarOrigins.retarget IrrOcc.symm (fun o => by simp only [core]) _ m.1⟩

def reindex_origins {hW : EnvWfT E} {U : Expr Nat} (out : J3.Result hW R h)
    (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r)
    (m : ValleyOrigins hW h out.valley) :
    ValleyOrigins hW (.tyConv Γ a b T U u h hT) (out.reindex u hT hs).valley :=
  ⟨StarOrigins.reindex _ _ (StarOrigins.retarget (IrrOcc.tyConv hT) (fun o => by simp only [core]) _ m.1),
   StarOrigins.reindex _ _ (StarOrigins.retarget (IrrOcc.tyConv hT) (fun o => by simp only [core]) _ m.2)⟩

end Rcic.Declarative.F8Measure.JOrigins

namespace Rcic.Declarative.F8Measure.JOrigins
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Traverses the REAL dispatch result. No occurrence is asserted for a failed call. -/
def dispatch_origins (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (match J3.dispatchWf hW R hΓ h hs with
      | none => PUnit
      | some out => ValleyOrigins hW h out.valley)
  | _, _, _, _, _, .refl _ _ _ ha, hs => refl_origins hW ha hs
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hs => irr_origins hW hP hp hq hs
  | Γ, _, _, _, hΓ, .symm _ a b T h, hs => by
      have ih := dispatch_origins hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      simp only [J3.dispatchWf]
      cases he : J3.dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) with
      | none => exact PUnit.unit
      | some out =>
          simp only [he] at ih
          exact swap_origins out ih
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hs => by
      have ih := dispatch_origins hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      simp only [J3.dispatchWf]
      cases he : J3.dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) with
      | none => exact PUnit.unit
      | some out =>
          simp only [he] at ih
          exact reindex_origins out u hT hs ih
  | _, _, _, _, _, .trans .., _ => PUnit.unit
  | _, _, _, _, _, .beta .., _ => PUnit.unit
  | _, _, _, _, _, .zeta .., _ => PUnit.unit
  | _, _, _, _, _, .zetaLocal .., _ => PUnit.unit
  | _, _, _, _, _, .delta .., _ => PUnit.unit
  | _, _, _, _, _, .iota .., _ => PUnit.unit
  | _, _, _, _, _, .lit .., _ => PUnit.unit
  | _, _, _, _, _, .app .., _ => PUnit.unit
  | _, _, _, _, _, .lam .., _ => PUnit.unit
  | _, _, _, _, _, .pi .., _ => PUnit.unit
  | _, _, _, _, _, .letE .., _ => PUnit.unit
  | _, _, _, _, _, .sorts .., _ => PUnit.unit
  | _, _, _, _, _, .consts .., _ => PUnit.unit
  | _, _, _, _, _, .eta .., _ => PUnit.unit

/-- The exact successful-output clause: strict ALL leaves and classified occurrences. -/
theorem dispatched_contract (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (out : J3.Result hW R h)
    (heq : J3.dispatchWf hW R hΓ h hs = some out) :
    (∀ l ∈ out.valley.leaves, SubOf l (.cv h)) ∧
    Nonempty (ValleyOrigins hW h out.valley) := by
  refine ⟨out.strict, ?_⟩
  have result := dispatch_origins hW R hΓ h hs
  rw [heq] at result
  exact ⟨result⟩

/-- No actual step in the star has a proof-root occurrence. -/
def NoProofOccurrences {Δ : LCtx} {x y U : Expr Nat}
    (ss : ParRedTStar (PEqLeafT E n) E n Δ x y U) : Prop := by
  induction ss with
  | refl => exact True
  | tail s _ ih => exact (∀ _o : Occ s, False) ∧ ih

def StarOrigins.no_source {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (no : ∀ _o : IrrOcc h, False) :
    {Δ : LCtx} → {x y U : Expr Nat} →
    (ss : ParRedTStar (PEqLeafT E n) E n Δ x y U) →
    StarOrigins h ss → NoProofOccurrences ss
  | _, _, _, _, .refl .., _ => True.intro
  | _, _, _, _, .tail _ ss, m =>
      ⟨fun o => no (m.1 o).1, StarOrigins.no_source no ss m.2⟩

/-- Signature-level no-typing-translation consequence. No global J is supplied. -/
theorem JOriginContractWf.no_source (hW : EnvWfT E)
    (J : ∀ R : List (Jd E n), JProcWf R) (hJ : JOriginContractWf hW J)
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r)
    (no : ∀ _o : IrrOcc h, False) :
    NoProofOccurrences ((J R hΓ h hs).left.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)) ∧
    NoProofOccurrences ((J R hΓ h hs).right.val
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)) := by
  obtain ⟨m⟩ := hJ R hΓ h hs
  exact ⟨StarOrigins.no_source no _ m.1, StarOrigins.no_source no _ m.2⟩

/-- Crucially independent of anything that might occur INSIDE the typing. -/
theorem refl_no_source {Γ : LCtx} {a T : Expr Nat}
    (ha : HasTyT E n Γ a T) (o : IrrOcc (ConvT.refl Γ a T ha)) : False := nomatch o

end Rcic.Declarative.F8Measure.JOrigins
