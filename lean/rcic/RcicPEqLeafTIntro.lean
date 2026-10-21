import rcic.RcicPEqLeafTProp
import rcic.RcicDT008Equiv
import rcic.RcicParRedTSubst

/-!
# Source-directed production of a proof-index certificate

The previous proof-index sector consumed `TyConvT T P` as input. Here
that chain is PRODUCED from two actual typings of a subject whose
introduction spine contains only sort/bvar/const/lam/letE constructors.
Annotations, let values, and conversions inside the input typings are
unrestricted. The comparison recurses on the first original HasTyT
premise only; the second derivation may have arbitrary conversion wraps.

At lam, reuse the existing `tyConvT_pi_cod` chain lifting. At letE,
reuse the existing `tyConvT_substLetS`. No sort row, Pi row, uniqueness
supplier, InScope, or semantic-prefix premise is consumed. The needed
environment properties are the existing EnvClosed and substitution
stability predicates, used by the let arm and context transport.

A final constructor builds ACTUAL type-level Pi leaves whose domain is
a type family applied to these proofs. Its codomain is unchanged as an
expression, but its typing is transported into the new domain context.
It returns both directions of PEqLeafT and a ConvT at the original sort.
This is a produced nonempty family of Pi leaves, NOT an inversion of
an arbitrary given Pi-source leaf. The unrestricted Pi proof-head case
still exposes a sort-to-proposition chain through hasTyTInv_pi; no
separation theorem for that chain is asserted. `closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- A classifier on SUBJECT syntax only, not a replacement judgment. -/
def introTypeSpine : Expr Nat → Bool
  | .sort _ | .bvar _ | .const _ _ => true
  | .lam _ body => introTypeSpine body
  | .letE _ _ body => introTypeSpine body
  | .pi _ _ | .app _ _ | .lit _ => false

section Intro
variable {E : ResolvedEnv} {n : Nat}

/-- Compare actual typings on the introduction spine. The recursive
argument is the FIRST input derivation, including at outer conv nodes.
No generated typing is used as that recursive argument. -/
private def introTypeSpineUniqueAux (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A →
    introTypeSpine e = true → {B : Expr Nat} →
    HasTyT E n Γ e B → TyConvT E n Γ A B
  | _, _, _, .sort _ _, _, _, hb => hasTyTInv_sortT hb rfl
  | _, _, _, .bvar _ _ _ hlk, _, _, hb => by
      obtain ⟨_, hlk', hcv⟩ := hasTyTInv_bvar hb rfl
      obtain rfl := Option.some.inj (hlk'.symm.trans hlk)
      exact hcv
  | _, _, _, .const _ _ _ _ hres _ _, _, _, hb => by
      obtain ⟨_, hres', _, _, hcv⟩ := hasTyTInv_const hb rfl
      obtain rfl := Option.some.inj (hres'.symm.trans hres)
      exact hcv
  | _, _, _, .lam _ _ _ body _ hA hbody, hs, _, hb => by
      obtain ⟨_, _, _, hbody', hcv⟩ := hasTyTInv_lam hb rfl
      let cc := introTypeSpineUniqueAux hcl hinst (e := body) hbody hs hbody'
      exact .trans _ _ _ _ (tyConvT_pi_cod hA cc) hcv
  | Γ, _, _, .letE _ dom _ value B0 body _ hv hbody, hs, _, hb => by
      obtain ⟨_, B1, _, _, hbody', hcv⟩ := hasTyTInv_letE hb rfl
      let cc := introTypeSpineUniqueAux hcl hinst (e := body) hbody hs hbody'
      have ci : TyConvT E n Γ (instantiate0 value B0) (instantiate0 value B1) := by
        have c := tyConvT_substLetS hcl hinst dom value (j := 0) cc (by simp)
          (by simpa only [lift_zero] using hv)
        simpa only [lift_zero] using c
      exact .trans _ _ _ _ ci hcv
  | _, _, _, .conv _ _ _ _ _ ha hc, hs, _, hb =>
      .trans _ _ _ _ (TyConvT.of _ _ _ _ hc).symmT
        (introTypeSpineUniqueAux hcl hinst ha hs hb)
  | _, _, _, .pi .., hs, _, _ => nomatch hs
  | _, _, _, .app .., hs, _, _ => nomatch hs
  | _, _, _, .lit .., hs, _, _ => nomatch hs

/-- Public type-chain comparison with the syntax condition stated first. -/
def introTypeSpine_unique (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {e A B : Expr Nat} (hs : introTypeSpine e = true)
    (ha : HasTyT E n Γ e A) (hb : HasTyT E n Γ e B) : TyConvT E n Γ A B :=
  introTypeSpineUniqueAux hcl hinst ha hs hb

/-- Produce the index chain from original typing witnesses; unlike the
previous proof-sector API, no type chain is an input. -/
def proofIndex_of_introSpine (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a P T : Expr Nat} (hs : introTypeSpine a = true)
    (_hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ a P) (ht : HasTyT E n Γ a T) :
    TyConvT E n Γ T P :=
  introTypeSpine_unique hcl hinst hs ht hp

/-- Inspect an actual typed leaf. A proof ROOT with an introduction
spine produces its certificate; other roots/spines return none. The
Some payload is typed evidence, not an unverified success Boolean. -/
def peqLeafT_introProofIndex? (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (h : PEqLeafT E n Γ a b T) :
    Option (Σ' P : Expr Nat, HasTyT E n Γ P (.sort .zero) ×'
      TyConvT E n Γ T P) :=
  match h with
  | ⟨.proof _ a _ P _ hP _ hp _, ht, _⟩ =>
      if hs : introTypeSpine a = true then
        some ⟨P, hP, proofIndex_of_introSpine hcl hinst hs hP hp ht⟩
      else none
  | _ => none

/-- Actual leaf and ConvT, with the chain generated rather than assumed.
Only the source must have an introduction spine; the target is arbitrary. -/
def peqLeafT_reconcile_introSpine (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T P : Expr Nat} (hs : introTypeSpine a = true)
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ a P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
    PEqLeafT E n Γ a b T ×' ConvT E n Γ a b T :=
  peqLeafT_reconcile_propIndex hP
    (proofIndex_of_introSpine hcl hinst hs hP hp ha) ha hb

/-- An arbitrary actual peak from an introduction-shaped proof. Its
original source typing and its independent proof typing produce hTP.
No conditions are imposed on the shapes of either input reduction. -/
def parRedT_introProof_diamond_data (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {a b c T P : Expr Nat}
    (hs : introTypeSpine a = true) (hΓ : CtxWfT E n Γ)
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ a P)
    (hab : ParRedT (PEqLeafT E n) E n Γ a b T)
    (hac : ParRedT (PEqLeafT E n) E n Γ a c T) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  let ht := parRedT_hasTy_left (fun h => ⟨h.2.1, h.2.2⟩) hΓ hab
  parRedT_propIndex_diamond_data hP
    (proofIndex_of_introSpine hcl hinst hs hP hp ht) hab hac

/-- Type-level Pi leaves above a proof-indexed family. C may depend on
its bound variable: the same expression is retyped under app f b by
actual CtxConvT transport. Neither a domain ConvT nor a proof-index
chain is assumed; both are generated from the original witnesses. -/
def pi_proofFamily_leaf_data (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T P f C : Expr Nat} {u v : Level}
    (hs : introTypeSpine a = true)
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ a P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T)
    (hf : HasTyT E n Γ f (.pi T (.sort u)))
    (hC : HasTyT E n (.assumption (.app f a) :: Γ) C (.sort v)) :
    PEqLeafT E n Γ (.pi (.app f a) C) (.pi (.app f b) C) (.sort (.imax u v)) ×'
      (PEqLeafT E n Γ (.pi (.app f b) C) (.pi (.app f a) C) (.sort (.imax u v)) ×'
        ConvT E n Γ (.pi (.app f a) C) (.pi (.app f b) C) (.sort (.imax u v))) :=
  let hTP := proofIndex_of_introSpine hcl hinst hs hP hp ha
  let ⟨leaf, cab⟩ := peqLeafT_reconcile_propIndex hP hTP ha hb
  let back := peqLeafT_symm_of_propIndex hP hTP leaf
  let hfa : HasTyT E n Γ (.app f a) (.sort u) := .app Γ f a T (.sort u) hf ha
  let hfb : HasTyT E n Γ (.app f b) (.sort u) := .app Γ f b T (.sort u) hf hb
  let cdom : ConvT E n Γ (.app f a) (.app f b) (.sort u) :=
    .app Γ f f a b T (.sort u) (.refl Γ f (.pi T (.sort u)) hf) cab
  let hcc : CtxConvT E n (.assumption (.app f a) :: Γ)
      (.assumption (.app f b) :: Γ) :=
    .assumption (ctxConvT_refl Γ) hfa hfb cdom
  let hC' := hasTyT_ctx hcl hcc hC
  let hpi := HasTyT.pi Γ (.app f a) u C v hfa hC
  let hpi' := HasTyT.pi Γ (.app f b) u C v hfb hC'
  ⟨⟨.pi Γ (.app f a) (.app f b) C C
       (.app Γ f f a b (PEqT.refl f) leaf.1) (PEqT.refl C), hpi, hpi'⟩,
   ⟨.pi Γ (.app f b) (.app f a) C C
       (.app Γ f f b a (PEqT.refl f) back.1) (PEqT.refl C), hpi', hpi⟩,
   .pi Γ (.app f a) (.app f b) C C u v cdom
     (.refl (.assumption (.app f a) :: Γ) C (.sort v) hC)⟩

end Intro
end Rcic.Declarative
