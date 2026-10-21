import rcic.RcicF8EvInvT
import rcic.RcicF8OM23
import rcic.RcicA2SortSupport
import rcic.RcicEtaKDecide

/-!
SP-1: exact original PEqT.pi input and B3b request extraction.
No raw transitivity, global P/U/X, new reduction rule, or endpoints3-to-lit.
The right binder transport is a scoped lazy request view, not an additional
EvTy constructor and not a reconstructed literal. P replies stay explicit.
Reference: Devin #7007, 791c16f39ab16f04931da594b3b3bfa69df17b9a.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.SP1
variable {E : ResolvedEnv} {n : Nat}

/-- Original constructor fields; source below names the COMPLETE D/J input. -/
structure Input (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A B A' B' T : Expr Nat) where
  domRaw : PEqT E n Γ A A'
  codRaw : PEqT E n (.assumption A :: Γ) B B'
  leftTy : HasTyT E n Γ (.pi A B) T
  rightTy : HasTyT E n Γ (.pi A' B') T

variable {Γ : LCtx} {A B A' B' T : Expr Nat}

def Input.source (p : Input E n Γ A B A' B' T) :
    ParRedT (PEqLeafT E n) E n Γ (.pi A B) (.pi A' B') T :=
  .peq Γ (.pi A B) (.pi A' B') T
    ⟨.pi Γ A A' B B' p.domRaw p.codRaw, p.leftTy, p.rightTy⟩

def Input.removed (p : Input E n Γ A B A' B' T) : List (Jd E n) := [.pr p.source]

theorem Input.left_child (p : Input E n Γ A B A' B' T) :
    Child (.ty p.leftTy) (.pr p.source) := .tail _ (.head _)

theorem Input.right_child (p : Input E n Γ A B A' B' T) :
    Child (.ty p.rightTy) (.pr p.source) := .tail _ (.tail _ (.head _))

theorem Input.dom_sub (p : Input E n Γ A B A' B' T) :
    SubOf (.pe p.domRaw) (.pr p.source) :=
  .trans (y := .pe (.pi Γ A A' B B' p.domRaw p.codRaw))
    (.child (.head _)) (.child (.head _))

theorem Input.cod_sub (p : Input E n Γ A B A' B' T) :
    SubOf (.pe p.codRaw) (.pr p.source) :=
  .trans (y := .pe (.pi Γ A A' B B' p.domRaw p.codRaw))
    (.child (.tail _ (.head _))) (.child (.head _))

def Input.leftOriginal (p : Input E n Γ A B A' B' T) :
    EvTy p.removed Γ (.pi A B) T :=
  .lit p.leftTy ⟨_, .head _, .inr (.child p.left_child)⟩

def Input.rightOriginal (p : Input E n Γ A B A' B' T) :
    EvTy p.removed Γ (.pi A' B') T :=
  .lit p.rightTy ⟨_, .head _, .inr (.child p.right_child)⟩

/-- B3b handles every EvTy root; no new inversion or materialize/reinvert. -/
def extract {R : List (Jd E n)}
    (l : EvTy R Γ (.pi A B) T) (r : EvTy R Γ (.pi A' B') T) :
    EvInvPi R Γ A B T × EvInvPi R Γ A' B' T :=
  ⟨l.invPiT rfl, r.invPiT rfl⟩

theorem extract_leaves {R : List (Jd E n)}
    (l : EvTy R Γ (.pi A B) T) (r : EvTy R Γ (.pi A' B') T)
    (x : Jd E n) (hx : x ∈ (extract l r).1.leaves ++ (extract l r).2.leaves) :
    ∃ y ∈ l.leaves ++ r.leaves, SubEq x y := by
  rcases List.mem_append.mp hx with hl | hr
  · obtain ⟨y, hy, hs⟩ := l.invPiT_leaves rfl x hl
    exact ⟨y, List.mem_append.mpr (.inl hy), hs⟩
  · obtain ⟨y, hy, hs⟩ := r.invPiT_leaves rfl x hr
    exact ⟨y, List.mem_append.mpr (.inr hy), hs⟩

def Input.leftView (p : Input E n Γ A B A' B' T) :=
  (extract p.leftOriginal p.rightOriginal).1

def Input.rightView (p : Input E n Γ A B A' B' T) :=
  (extract p.leftOriginal p.rightOriginal).2

theorem Input.leftView_strict (p : Input E n Γ A B A' B' T)
    (x : Jd E n) (hx : x ∈ p.leftView.leaves) : SubOf x (.pr p.source) := by
  obtain ⟨y, hy, hs⟩ := p.leftOriginal.invPiT_leaves rfl x hx
  have he : y = .ty p.leftTy := List.mem_singleton.mp hy
  subst y
  exact subEq_trans_subOf hs (.child p.left_child)

theorem Input.rightView_strict (p : Input E n Γ A B A' B' T)
    (x : Jd E n) (hx : x ∈ p.rightView.leaves) : SubOf x (.pr p.source) := by
  obtain ⟨y, hy, hs⟩ := p.rightOriginal.invPiT_leaves rfl x hx
  have he : y = .ty p.rightTy := List.mem_singleton.mp hy
  subst y
  exact subEq_trans_subOf hs (.child p.right_child)

/-- Support is about original judgment atoms, not equality of conclusions. -/
def Supported (out inp : List (Jd E n)) : Prop :=
  ∀ x ∈ out, ∃ y ∈ inp, SubEq x y

theorem supported_strict {out inp : List (Jd E n)} {root : Jd E n}
    (h : Supported out inp) (hi : ∀ y ∈ inp, SubOf y root) :
    ∀ x ∈ out, SubOf x root := by
  intro x hx
  obtain ⟨y, hy, hs⟩ := h x hx
  exact subEq_trans_subOf hs (hi y hy)

/-- H4 may have a different right universe. P must answer at the LEFT sort. -/
structure SortRequest (R : List (Jd E n)) (Γ : LCtx) (a b : Expr Nat) where
  u : Level
  v : Level
  raw : PEqT E n Γ a b
  rawSub : ∃ root ∈ R, SubEq (.pe raw) root
  left : EvTy R Γ a (.sort u)
  right : EvTy R Γ b (.sort v)

def SortRequest.leaves {R : List (Jd E n)} {a b : Expr Nat}
    (q : SortRequest R Γ a b) : List (Jd E n) :=
  [.pe q.raw] ++ (q.left.leaves ++ q.right.leaves)

def domainRequest (p : Input E n Γ A B A' B' T) :
    SortRequest p.removed Γ A A' where
  u := p.leftView.u
  v := p.rightView.u
  raw := p.domRaw
  rawSub := ⟨_, .head _, .inr p.dom_sub⟩
  left := p.leftView.hA
  right := p.rightView.hA

theorem domainRequest_strict (p : Input E n Γ A B A' B' T)
    (x : Jd E n) (hx : x ∈ (domainRequest p).leaves) :
    SubOf x (.pr p.source) := by
  rcases List.mem_append.mp hx with hx | hx
  · have he : x = .pe p.domRaw := List.mem_singleton.mp hx
    subst x; exact p.dom_sub
  · rcases List.mem_append.mp hx with hl | hr
    · apply p.leftView_strict x
      simp only [EvInvPi.leaves, List.mem_append]
      exact .inl (.inl hl)
    · apply p.rightView_strict x
      simp only [EvInvPi.leaves, List.mem_append]
      exact .inl (.inl hr)

/-- Scoped binder-alignment view. Only the stored right typing is transported;
    the output is never admitted into EvTy.lit. The right universe is retained. -/
structure BinderRequest (R : List (Jd E n)) (Γ : LCtx)
    (A A' b b' : Expr Nat) where
  u : Level
  v : Level
  vRight : Level
  raw : PEqT E n (.assumption A :: Γ) b b'
  rawSub : ∃ root ∈ R, SubEq (.pe raw) root
  left : EvTy R (.assumption A :: Γ) b (.sort v)
  domain : EvCv R Γ A A' (.sort u)
  right : EvTy R (.assumption A' :: Γ) b' (.sort vRight)

def BinderRequest.leaves {R : List (Jd E n)} {a a' b b' : Expr Nat}
    (q : BinderRequest R Γ a a' b b') : List (Jd E n) :=
  [.pe q.raw] ++ (q.left.leaves ++ (q.domain.leaves ++ q.right.leaves))

/-- The actual right seed at the LEFT binder; no choice, re-inversion or U. -/
def BinderRequest.rightAligned {R : List (Jd E n)} {a a' b b' : Expr Nat}
    (q : BinderRequest R Γ a a' b b')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    HasTyT E n (.assumption a :: Γ) b' (.sort q.vRight) :=
  hasTyTConvAssump hcl (q.domain.val hcl hinst) (q.right.val hcl hinst)

theorem BinderRequest.rightAligned_exact {R : List (Jd E n)}
    {a a' b b' : Expr Nat} (q : BinderRequest R Γ a a' b b')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    q.rightAligned hcl hinst =
      hasTyTConvAssump hcl (q.domain.val hcl hinst) (q.right.val hcl hinst) := rfl

def codomainRequest (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u)) :
    BinderRequest p.removed Γ A A' B B' where
  u := p.leftView.u
  v := p.leftView.v
  vRight := p.rightView.v
  raw := p.codRaw
  rawSub := ⟨_, .head _, .inr p.cod_sub⟩
  left := p.leftView.hB
  domain := dom
  right := p.rightView.hB

theorem codomainRequest_strict (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (hdom : Supported dom.leaves (domainRequest p).leaves)
    (x : Jd E n) (hx : x ∈ (codomainRequest p dom).leaves) :
    SubOf x (.pr p.source) := by
  rcases List.mem_append.mp hx with hx | hx
  · have he : x = .pe p.codRaw := List.mem_singleton.mp hx
    subst x; exact p.cod_sub
  · rcases List.mem_append.mp hx with hl | hx
    · apply p.leftView_strict x
      simp only [EvInvPi.leaves, List.mem_append]
      exact .inl (.inr hl)
    · rcases List.mem_append.mp hx with hd | hr
      · exact supported_strict hdom (domainRequest_strict p) x hd
      · apply p.rightView_strict x
        simp only [EvInvPi.leaves, List.mem_append]
        exact .inl (.inr hr)

/-- Named P-at-left-sort processor at an admitted env and well-formed context.
    NOT provided by this module. -/
abbrev PAtSort (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b : Expr Nat}, EnvWfT E → CtxWfT E n Γ →
    (q : SortRequest R Γ a b) → EvCv R Γ a b (.sort q.u)

def PAtSortContract {R : List (Jd E n)} (P : PAtSort R) : Prop :=
  ∀ {Γ : LCtx} {a b : Expr Nat} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (q : SortRequest R Γ a b), Supported (P hW hΓ q).leaves q.leaves

/-- P after binder alignment, guarded at BOTH actual binder contexts.
    H4 reconciliation remains part of this named processor. -/
abbrev PAtBinder (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A A' b b' : Expr Nat}, EnvWfT E →
    CtxWfT E n (.assumption A :: Γ) → CtxWfT E n (.assumption A' :: Γ) →
    (q : BinderRequest R Γ A A' b b') →
    EvCv R (.assumption A :: Γ) b b' (.sort q.v)

def PAtBinderContract {R : List (Jd E n)} (P : PAtBinder R) : Prop :=
  ∀ {Γ : LCtx} {A A' b b' : Expr Nat} (hW : EnvWfT E)
    (hL : CtxWfT E n (.assumption A :: Γ))
    (hR : CtxWfT E n (.assumption A' :: Γ))
    (q : BinderRequest R Γ A A' b b'), Supported (P hW hL hR q).leaves q.leaves

theorem domain_edge (p : Input E n Γ A B A' B' T) (Z : List (Jd E n)) :
    OM3_edge (p.removed ++ Z) ((domainRequest p).leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun x hx => ⟨_, .head _, domainRequest_strict p x hx⟩)

theorem codomain_edge (p : Input E n Γ A B A' B' T)
    (dom : EvCv p.removed Γ A A' (.sort p.leftView.u))
    (hdom : Supported dom.leaves (domainRequest p).leaves) (Z : List (Jd E n)) :
    OM3_edge (p.removed ++ Z) ((codomainRequest p dom).leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun x hx => ⟨_, .head _, codomainRequest_strict p dom hdom x hx⟩)

/-- Π-source proof exclusion uses EXACTLY the named sort uniqueness supply. -/
theorem piProofRoot_false (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ (.pi A B) P) : False := by
  obtain ⟨u, v, _hA, _hB, hc⟩ := hasTyTInv_pi hp rfl
  exact F8EtaK.separationAt_of_sortUniq hW (su hW) hΓ hP hc

end Rcic.Declarative.F8Measure.SP1

#print axioms Rcic.Declarative.F8Measure.SP1.Input
#print axioms Rcic.Declarative.F8Measure.SP1.Input.source
#print axioms Rcic.Declarative.F8Measure.SP1.Input.removed
#print axioms Rcic.Declarative.F8Measure.SP1.Input.left_child
#print axioms Rcic.Declarative.F8Measure.SP1.Input.right_child
#print axioms Rcic.Declarative.F8Measure.SP1.Input.dom_sub
#print axioms Rcic.Declarative.F8Measure.SP1.Input.cod_sub
#print axioms Rcic.Declarative.F8Measure.SP1.Input.leftOriginal
#print axioms Rcic.Declarative.F8Measure.SP1.Input.rightOriginal
#print axioms Rcic.Declarative.F8Measure.SP1.extract
#print axioms Rcic.Declarative.F8Measure.SP1.extract_leaves
#print axioms Rcic.Declarative.F8Measure.SP1.Input.leftView
#print axioms Rcic.Declarative.F8Measure.SP1.Input.rightView
#print axioms Rcic.Declarative.F8Measure.SP1.Input.leftView_strict
#print axioms Rcic.Declarative.F8Measure.SP1.Input.rightView_strict
#print axioms Rcic.Declarative.F8Measure.SP1.Supported
#print axioms Rcic.Declarative.F8Measure.SP1.supported_strict
#print axioms Rcic.Declarative.F8Measure.SP1.SortRequest
#print axioms Rcic.Declarative.F8Measure.SP1.SortRequest.leaves
#print axioms Rcic.Declarative.F8Measure.SP1.domainRequest
#print axioms Rcic.Declarative.F8Measure.SP1.domainRequest_strict
#print axioms Rcic.Declarative.F8Measure.SP1.BinderRequest
#print axioms Rcic.Declarative.F8Measure.SP1.BinderRequest.leaves
#print axioms Rcic.Declarative.F8Measure.SP1.BinderRequest.rightAligned
#print axioms Rcic.Declarative.F8Measure.SP1.BinderRequest.rightAligned_exact
#print axioms Rcic.Declarative.F8Measure.SP1.codomainRequest
#print axioms Rcic.Declarative.F8Measure.SP1.codomainRequest_strict
#print axioms Rcic.Declarative.F8Measure.SP1.PAtSort
#print axioms Rcic.Declarative.F8Measure.SP1.PAtSortContract
#print axioms Rcic.Declarative.F8Measure.SP1.PAtBinder
#print axioms Rcic.Declarative.F8Measure.SP1.PAtBinderContract
#print axioms Rcic.Declarative.F8Measure.SP1.domain_edge
#print axioms Rcic.Declarative.F8Measure.SP1.codomain_edge
#print axioms Rcic.Declarative.F8Measure.SP1.piProofRoot_false
