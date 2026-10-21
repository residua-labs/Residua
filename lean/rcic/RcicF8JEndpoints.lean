import rcic.RcicF8EvInv
import rcic.RcicF8OM23
import rcic.RcicTypedEnvEntry

/-!
# J2: strictly supported endpoint typings for an explicit partial literal domain

Original refl/irr/iota/local-zeta endpoints, composed through original
symm/trans/tyConv. No endpoint theorem is materialized and reboxed as lit.
The D-VAR left local-zeta typing has no judgment leaves. Retyping retains the
original type-conversion field on BOTH endpoints. No new carrier or reduction
producer, no Valley, no global J supplier. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JEndpoints
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- A packet is indexed by the exact ORIGINAL conversion derivation. -/
structure Packet (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) where
  left : EvTy R Γ a T
  right : EvTy R Γ b T
  strict : ∀ x ∈ left.leaves ++ right.leaves, SubOf x (.cv h)

variable {Γ : LCtx} {a b c T U : Expr Nat}

def Packet.leaves {h : ConvT E n Γ a b T} (p : Packet R h) : List (Jd E n) :=
  p.left.leaves ++ p.right.leaves

/-- Expose the original parent from its caller certificate before checking membership. -/
def originalChildCert {x y : Jd E n} (hs : ∃ r ∈ R, SubEq y r)
    (hc : Child x y) : ∃ r ∈ R, SubEq x r := certOfChild hc hs

/-- Only actual immediate typing fields may be injected here. -/
def typedPair (h : ConvT E n Γ a b T)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T)
    (hca : Child (.ty ha) (.cv h)) (hcb : Child (.ty hb) (.cv h))
    (hs : ∃ r ∈ R, SubEq (.cv h) r) : Packet R h where
  left := .lit ha (certOfChild hca hs)
  right := .lit hb (certOfChild hcb hs)
  strict := by
    intro x hx
    change x ∈ [Jd.ty ha] ++ [Jd.ty hb] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have heq := List.mem_singleton.mp hx
      subst x; exact .child hca
    · have heq := List.mem_singleton.mp hx
      subst x; exact .child hcb

def reflPacket (ha : HasTyT E n Γ a T)
    (hs : ∃ r ∈ R, SubEq (.cv (.refl Γ a T ha)) r) :
    Packet R (.refl Γ a T ha) :=
  typedPair _ ha ha (.head _) (.head _) hs

def irrPacket {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P)
    (hs : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) :
    Packet R (.irr Γ P p q hP hp hq) :=
  typedPair _ hp hq (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) hs

/-- The exact scope of raw ConvT.iota: legacy DerivedIota, not DerivedIotaU. -/
def iotaPacket (d : DerivedIota E a b)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T)
    (hs : ∃ r ∈ R, SubEq (.cv (.iota Γ a b T d ha hb)) r) :
    Packet R (.iota Γ a b T d ha hb) :=
  typedPair _ ha hb (.head _) (.tail _ (.head _)) hs

def zetaLocalPacket (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    Packet R (.zetaLocal Γ i A v hval hty hv) where
  left := .var i A hty
  right := .lit hv (originalChildCert hs (.head _))
  strict := by
    intro x hx
    change x ∈ [Jd.ty hv] at hx
    have heq := List.mem_singleton.mp hx
    subst x; exact .child (.head _)

theorem zetaLocalPacket_leaves (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    (zetaLocalPacket i A v hval hty hv hs).leaves = [.ty hv] := rfl

theorem zetaLocalPacket_left_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    (zetaLocalPacket i A v hval hty hv hs).left.val hcl hinst =
      HasTyT.bvar Γ i A hty := rfl

theorem iotaPacket_left_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (d : DerivedIota E a b)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T)
    (hs : ∃ r ∈ R, SubEq (.cv (.iota Γ a b T d ha hb)) r) :
    (iotaPacket d ha hb hs).left.val hcl hinst = ha := rfl

theorem iotaPacket_right_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (d : DerivedIota E a b)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T)
    (hs : ∃ r ∈ R, SubEq (.cv (.iota Γ a b T d ha hb)) r) :
    (iotaPacket d ha hb hs).right.val hcl hinst = hb := rfl

def Packet.swap {h : ConvT E n Γ a b T} (p : Packet R h) :
    Packet R (.symm Γ a b T h) where
  left := p.right
  right := p.left
  strict := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact .trans (p.strict x (List.mem_append.mpr (.inr hx))) (.child (.head _))
    · exact .trans (p.strict x (List.mem_append.mpr (.inl hx))) (.child (.head _))

def Packet.compose {h1 : ConvT E n Γ a b T} {h2 : ConvT E n Γ b c T}
    (p : Packet R h1) (q : Packet R h2) : Packet R (.trans Γ a b c T h1 h2) where
  left := p.left
  right := q.right
  strict := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact .trans (p.strict x (List.mem_append.mpr (.inl hx))) (.child (.head _))
    · exact .trans (q.strict x (List.mem_append.mpr (.inr hx)))
        (.child (.tail _ (.head _)))

/-- Index change is an ORIGINAL child, retained lazily twice, not normalized away. -/
def Packet.reindex {h : ConvT E n Γ a b T} (p : Packet R h)
    (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    Packet R (.tyConv Γ a b T U u h hT) where
  left := .rety p.left (.ofCv u (.lit hT (originalChildCert hs (.tail _ (.head _)))))
  right := .rety p.right (.ofCv u (.lit hT (originalChildCert hs (.tail _ (.head _)))))
  strict := by
    intro x hx
    change x ∈ (p.left.leaves ++ [Jd.cv hT]) ++
      (p.right.leaves ++ [Jd.cv hT]) at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact .trans (p.strict x (List.mem_append.mpr (.inl hx))) (.child (.head _))
    · subst x; exact .child (.tail _ (.head _))
    · exact .trans (p.strict x (List.mem_append.mpr (.inr hx))) (.child (.head _))
    · subst x; exact .child (.tail _ (.head _))

theorem Packet.reindex_leaves {h : ConvT E n Γ a b T} (p : Packet R h)
    (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    (p.reindex u hT hs).leaves =
      (p.left.leaves ++ [.cv hT]) ++ (p.right.leaves ++ [.cv hT]) := rfl

theorem Packet.reindex_left_exact {h : ConvT E n Γ a b T} (p : Packet R h)
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    (p.reindex u hT hs).left.val hcl hinst =
      HasTyT.conv Γ a T U u (p.left.val hcl hinst) hT := rfl

/-- Exact supported syntax. tyConv consumes its original index field, not its endpoints. -/
def supported : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .refl .. => true
  | _, _, _, _, .irr .. => true
  | _, _, _, _, .iota .. => true
  | _, _, _, _, .zetaLocal .. => true
  | _, _, _, _, .symm _ _ _ _ h => supported h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => supported h1 && supported h2
  | _, _, _, _, .tyConv _ _ _ _ _ _ h _ => supported h
  | _, _, _, _, .beta .. => false
  | _, _, _, _, .zeta .. => false
  | _, _, _, _, .delta .. => false
  | _, _, _, _, .lit .. => false
  | _, _, _, _, .app .. => false
  | _, _, _, _, .lam .. => false
  | _, _, _, _, .pi .. => false
  | _, _, _, _, .letE .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
  | _, _, _, _, .eta .. => false

/-- Internal structural extraction: no guarantee outside the explicit supported domain. -/
def extract : {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E n Γ a b T) →
    (∃ r ∈ R, SubEq (.cv h) r) → Option (Packet R h)
  | _, _, _, _, .refl _ _ _ ha, hs => some (reflPacket ha hs)
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hs => some (irrPacket hP hp hq hs)
  | _, _, _, _, .iota _ _ _ _ d ha hb, hs => some (iotaPacket d ha hb hs)
  | _, _, _, _, .zetaLocal _ i A v hv ht hd, hs => some (zetaLocalPacket i A v hv ht hd hs)
  | _, _, _, _, .symm _ _ _ _ h, hs =>
      match extract h (originalChildCert hs (.head _)) with
      | none => none
      | some p => some p.swap
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hs =>
      match extract h1 (originalChildCert hs (.head _)),
        extract h2 (originalChildCert hs (.tail _ (.head _))) with
      | some p, some q => some (p.compose q)
      | _, _ => none
  | _, _, _, _, .tyConv _ _ _ _ _ u h hT, hs =>
      match extract h (originalChildCert hs (.head _)) with
      | none => none
      | some p => some (p.reindex u hT hs)
  | _, _, _, _, .beta .., _ => none
  | _, _, _, _, .zeta .., _ => none
  | _, _, _, _, .delta .., _ => none
  | _, _, _, _, .lit .., _ => none
  | _, _, _, _, .app .., _ => none
  | _, _, _, _, .lam .., _ => none
  | _, _, _, _, .pi .., _ => none
  | _, _, _, _, .letE .., _ => none
  | _, _, _, _, .sorts .., _ => none
  | _, _, _, _, .consts .., _ => none
  | _, _, _, _, .eta .., _ => none

/-- Public J-facing front: explicit well-formed environment and context. -/
def extractWf (_hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (_hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option (Packet R h) := extract h hs

/-- The caller replaced here is the literal, NOT the ambient support bundle R. -/
theorem Packet.edge {h : ConvT E n Γ a b T} (p : Packet R h) (Z : List (Jd E n)) :
    OM3_edge ([.cv h] ++ Z) (p.leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun x hx => ⟨.cv h, .head _, p.strict x hx⟩)

/-- Exhaustive recursive coverage: no successful output is claimed for the other arms. -/
theorem extract_coverage : {Γ : LCtx} → {a b T : Expr Nat} →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (extract h hs).isSome = supported h
  | _, _, _, _, .symm _ _ _ _ h, hs => by
      have ih := extract_coverage h (originalChildCert hs (.head _))
      simp only [extract, supported]
      cases he : extract h (originalChildCert hs (.head _)) <;>
        simpa only [he, Option.isSome] using ih
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hs => by
      have ih1 := extract_coverage h1 (originalChildCert hs (.head _))
      have ih2 := extract_coverage h2 (originalChildCert hs (.tail _ (.head _)))
      simp only [extract, supported]
      rw [← ih1, ← ih2]
      cases extract h1 (originalChildCert hs (.head _)) <;>
        cases extract h2 (originalChildCert hs (.tail _ (.head _))) <;> rfl
  | _, _, _, _, .tyConv _ _ _ _ _ u h hT, hs => by
      have ih := extract_coverage h (originalChildCert hs (.head _))
      simp only [extract, supported]
      cases he : extract h (originalChildCert hs (.head _)) <;>
        simpa only [he, Option.isSome] using ih
  | _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, .irr .., _ => rfl
  | _, _, _, _, .iota .., _ => rfl
  | _, _, _, _, .zetaLocal .., _ => rfl
  | _, _, _, _, .beta .., _ => rfl
  | _, _, _, _, .zeta .., _ => rfl
  | _, _, _, _, .delta .., _ => rfl
  | _, _, _, _, .lit .., _ => rfl
  | _, _, _, _, .app .., _ => rfl
  | _, _, _, _, .lam .., _ => rfl
  | _, _, _, _, .pi .., _ => rfl
  | _, _, _, _, .letE .., _ => rfl
  | _, _, _, _, .sorts .., _ => rfl
  | _, _, _, _, .consts .., _ => rfl
  | _, _, _, _, .eta .., _ => rfl

theorem extractWf_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (extractWf hW R hΓ h hs).isSome = supported h := extract_coverage h hs

/-- Widening changes only the admitted support bundle, not the original caller. -/
def Packet.widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    {h : ConvT E n Γ a b T} (p : Packet R h) : Packet R' h where
  left := p.left.widen hr
  right := p.right.widen hr
  strict := by
    simpa only [EvTy.leaves_widen] using p.strict

theorem Packet.widen_leaves {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    {h : ConvT E n Γ a b T} (p : Packet R h) :
    (p.widen hr).leaves = p.leaves := by
  simp only [Packet.widen, Packet.leaves, EvTy.leaves_widen]

end Rcic.Declarative.F8Measure.JEndpoints
