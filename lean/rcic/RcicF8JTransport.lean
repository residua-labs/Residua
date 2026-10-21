import rcic.RcicF8JBase

/-!
J3: symmetry and type-index transport of existing J1 Valleys.
No new reduction producer, carrier, D solver, or total J. The actual output
is the shared Valley.symm/conv, with lazy EvParStar.conv. Certificates are
proof data indexed by existing materialized stars, not a second star relation.
Original J1 code and contracts are not edited. closure_claim=0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J3
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- An index-specific view of the UNCHANGED DTile status/OM2 fields. -/
structure StepCertificate (R X : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat}
    (s : ParRedT (PEqLeafT E n) E n Γ a b T) where
  status : (o : Occ s) → (side : Side) → SiteStatus R (site s o) side
  om2 : OM2 X s status

variable {X Y : List (Jd E n)}

def StepCertificate.tile {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s) : DTile R where
  X := X
  step := s
  status := c.status
  om2 := c.om2

theorem StepCertificate.tile_exact {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s) : c.tile.step = s := rfl

theorem StepCertificate.tile_removed {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s) : c.tile.X = X := rfl

/-- Moving a caller is licensed by original ancestry, not ambient-root membership. -/
def StepCertificate.recaller {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s)
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, SubEq x y) : StepCertificate R Y s where
  status := c.status
  om2 := by
    intro o side
    have hv := c.om2 o side
    cases hs : c.status o side with
    | answered req ans => trivial
    | admissible idx pos proofTy =>
        simp only [hs] at hv ⊢
        intro l hl
        obtain ⟨x, hx, hsub⟩ := hv l hl
        obtain ⟨y, hy, hxy⟩ := hXY x hx
        exact ⟨y, hy, subOf_trans_subEq hsub hxy⟩

/-- A conv wrapper preserves the SAME inner occurrence, request index and answer.
The raw chain here is only for certifying materialization; provenance is retained
by the calling Valley.conv's EvTc field and its all-leaf strict clause. -/
def StepCertificate.reindex {Γ : LCtx} {a b T U : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s) (tc : TyConvT E n Γ T U) :
    StepCertificate R X (.conv Γ a b T U s tc) where
  status := c.status
  om2 := by
    intro o side
    have hv := c.om2 o side
    cases hs : c.status o side with
    | answered req ans => trivial
    | admissible idx pos proofTy =>
        simp only [hs] at hv ⊢
        exact hv

/-- Certificate family over an EXISTING plain star. No new val/leaves or transitions. -/
def Certified (R X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (ss : ParRedTStar (PEqLeafT E n) E n Γ a b T) : Type := by
  induction ss with
  | refl => exact PUnit
  | tail s _ ih => exact StepCertificate R X s × ih

def Certified.recaller (hXY : ∀ x ∈ X, ∃ y ∈ Y, SubEq x y) :
    {Γ : LCtx} → {a b T : Expr Nat} →
    (ss : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    Certified R X ss → Certified R Y ss
  | _, _, _, _, .refl .., _ => PUnit.unit
  | _, _, _, _, .tail _ ss, c =>
      ⟨c.1.recaller hXY, Certified.recaller hXY ss c.2⟩

def Certified.reindex {Γ : LCtx} {T U : Expr Nat}
    (tc : TyConvT E n Γ T U) : {a b : Expr Nat} →
    (ss : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    Certified R X ss → Certified R X (parRedTStar_conv tc ss)
  | _, _, .refl .., _ => PUnit.unit
  | _, _, .tail _ ss, c => ⟨c.1.reindex tc, Certified.reindex tc ss c.2⟩

structure Result (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T) where
  valley : Valley R Γ a b T
  leftTiles : Certified R [.cv h]
    (valley.left.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  rightTiles : Certified R [.cv h]
    (valley.right.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  strict : ∀ l ∈ valley.leaves, SubOf l (.cv h)

/-- Consume J1's actual base Valley without changing its base-only dispatcher. -/
def reflResult (hW : EnvWfT E) {Γ : LCtx} {a T : Expr Nat}
    (ha : HasTyT E n Γ a T)
    (hs : ∃ r ∈ R, SubEq (.cv (.refl Γ a T ha)) r) :
    Result hW R (.refl Γ a T ha) where
  valley := J1.reflValley ha hs
  leftTiles := PUnit.unit
  rightTiles := PUnit.unit
  strict := J1.reflValley_strict ha hs

/-- The only step is J1's exact original irr DTile. -/
def irrResult (hW : EnvWfT E) {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P)
    (hs : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) :
    Result hW R (.irr Γ P p q hP hp hq) where
  valley := J1.irrValley hP hp hq hs
  leftTiles :=
    let t := J1.irrTile (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) hP hp hq hs
    ⟨⟨t.status, t.om2⟩, PUnit.unit⟩
  rightTiles := PUnit.unit
  strict := J1.irrValley_strict hP hp hq hs

def callerOfChild {x y : Jd E n} (hc : Child x y) :
    ∀ t ∈ [x], ∃ u ∈ [y], SubEq t u := by
  intro t ht
  have heq := List.mem_singleton.mp ht
  subst t
  exact ⟨y, .head _, .inr (.child hc)⟩

variable {Γ : LCtx} {a b T U : Expr Nat}

def Result.swap {hW : EnvWfT E} {h : ConvT E n Γ a b T}
    (p : Result hW R h) : Result hW R (.symm Γ a b T h) where
  valley := p.valley.symm
  leftTiles := Certified.recaller
    (callerOfChild (y := .cv (.symm Γ a b T h)) (.head _)) _ p.rightTiles
  rightTiles := Certified.recaller
    (callerOfChild (y := .cv (.symm Γ a b T h)) (.head _)) _ p.leftTiles
  strict := fun l hl => .trans
    (p.strict l (p.valley.symm_leaves l hl)) (.child (.head _))

/-- Only the actual type-index field of the original ConvT.tyConv is literal. -/
def indexField {h : ConvT E n Γ a b T} (u : Level)
    (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) : EvTc R Γ T U :=
  .ofCv u (.lit hT
    (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.tail _ (.head _)) hs))

theorem indexField_leaves {h : ConvT E n Γ a b T} (u : Level)
    (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    (indexField u hT hs).leaves = [.cv hT] := rfl

def Result.reindex {hW : EnvWfT E} {h : ConvT E n Γ a b T}
    (p : Result hW R h) (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    Result hW R (.tyConv Γ a b T U u h hT) where
  valley := p.valley.conv (indexField u hT hs)
  leftTiles := Certified.reindex
    ((indexField u hT hs).val (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW)) _
    (Certified.recaller (callerOfChild
      (y := .cv (.tyConv Γ a b T U u h hT)) (.head _)) _ p.leftTiles)
  rightTiles := Certified.reindex
    ((indexField u hT hs).val (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW)) _
    (Certified.recaller (callerOfChild
      (y := .cv (.tyConv Γ a b T U u h hT)) (.head _)) _ p.rightTiles)
  strict := by
    intro l hl
    have hm := p.valley.conv_leaves (indexField u hT hs) l hl
    rcases List.mem_append.mp hm with hp | ht
    · exact .trans (p.strict l hp) (.child (.head _))
    · have heq := List.mem_singleton.mp ht
      subst l
      exact .child (.tail _ (.head _))

/-- Exact multiplicity: the original index field appears on all four outputs. -/
theorem Result.reindex_leaves {hW : EnvWfT E} {h : ConvT E n Γ a b T}
    (p : Result hW R h) (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    (p.reindex u hT hs).valley.leaves =
      ((p.valley.left.leaves ++ [.cv hT]) ++
        (p.valley.right.leaves ++ [.cv hT]) ++
        (p.valley.ty₁.leaves ++ [.cv hT])) ++
        (p.valley.ty₂.leaves ++ [.cv hT]) := rfl

theorem Result.reindex_left_exact {hW : EnvWfT E} {h : ConvT E n Γ a b T}
    (p : Result hW R h) (u : Level) (hT : ConvT E n Γ T U (.sort u))
    (hs : ∃ r ∈ R, SubEq (.cv (.tyConv Γ a b T U u h hT)) r) :
    (p.reindex u hT hs).valley.left.val (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) =
      parRedTStar_conv (.of Γ T U u hT)
        (p.valley.left.val (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW)) := rfl

/-- Strict input-call edge; neither a generated result nor ambient R is the caller. -/
theorem original_child_edge {x y : Jd E n} (hc : Child x y) (Z : List (Jd E n)) :
    OM3_edge ([y] ++ Z) ([x] ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun l hl => by
      have heq := List.mem_singleton.mp hl
      subst l
      exact ⟨y, .head _, .child hc⟩)

theorem result_edge {hW : EnvWfT E} {h : ConvT E n Γ a b T}
    (p : Result hW R h) (Z : List (Jd E n)) :
    OM3_edge ([.cv h] ++ Z) (p.valley.leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun l hl => ⟨.cv h, .head _, p.strict l hl⟩)
end Rcic.Declarative.F8Measure.J3

namespace Rcic.Declarative.F8Measure.J3
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R X Y : List (Jd E n)}

theorem StepCertificate.reindex_status {Γ : LCtx} {a b T U : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s) (tc : TyConvT E n Γ T U)
    (o : Occ s) (side : Side) :
    HEq ((c.reindex tc).status o side) (c.status o side) := HEq.rfl

theorem StepCertificate.recaller_status {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T}
    (c : StepCertificate R X s)
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, SubEq x y) (o : Occ s) (side : Side) :
    (c.recaller hXY).status o side = c.status o side := rfl

/-- Base literals closed under symmetry and term-index transport only. -/
def supported : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .refl .. => true
  | _, _, _, _, .irr .. => true
  | _, _, _, _, .symm _ _ _ _ h => supported h
  | _, _, _, _, .tyConv _ _ _ _ _ _ h _ => supported h
  | _, _, _, _, .trans .. => false
  | _, _, _, _, .beta .. => false
  | _, _, _, _, .zeta .. => false
  | _, _, _, _, .zetaLocal .. => false
  | _, _, _, _, .delta .. => false
  | _, _, _, _, .iota .. => false
  | _, _, _, _, .lit .. => false
  | _, _, _, _, .app .. => false
  | _, _, _, _, .lam .. => false
  | _, _, _, _, .pi .. => false
  | _, _, _, _, .letE .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
  | _, _, _, _, .eta .. => false

/-- Public partial J front; original child calls keep the same well-formed Γ. -/
def dispatchWf (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfT E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hs => some (reflResult hW ha hs)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hs => some (irrResult hW hP hp hq hs)
  | Γ, _, _, _, hΓ, .symm _ a b T h, hs =>
      match dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) with
      | none => none
      | some p => some p.swap
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hs =>
      match dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) with
      | none => none
      | some p => some (p.reindex u hT hs)
  | _, _, _, _, _, .trans .., _ => none
  | _, _, _, _, _, .beta .., _ => none
  | _, _, _, _, _, .zeta .., _ => none
  | _, _, _, _, _, .zetaLocal .., _ => none
  | _, _, _, _, _, .delta .., _ => none
  | _, _, _, _, _, .iota .., _ => none
  | _, _, _, _, _, .lit .., _ => none
  | _, _, _, _, _, .app .., _ => none
  | _, _, _, _, _, .lam .., _ => none
  | _, _, _, _, _, .pi .., _ => none
  | _, _, _, _, _, .letE .., _ => none
  | _, _, _, _, _, .sorts .., _ => none
  | _, _, _, _, _, .consts .., _ => none
  | _, _, _, _, _, .eta .., _ => none

/-- Exact recursive domain; no bound on the number of original wrappers. -/
theorem dispatchWf_coverage (hW : EnvWfT E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (dispatchWf hW R hΓ h hs).isSome = supported h
  | Γ, _, _, _, hΓ, .symm _ a b T h, hs => by
      have ih := dispatchWf_coverage hW hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      simp only [dispatchWf, supported]
      cases he : dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) <;>
        simpa only [he, Option.isSome] using ih
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hs => by
      have ih := dispatchWf_coverage hW hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      simp only [dispatchWf, supported]
      cases he : dispatchWf hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) <;>
        simpa only [he, Option.isSome] using ih
  | _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, .irr .., _ => rfl
  | _, _, _, _, _, .trans .., _ => rfl
  | _, _, _, _, _, .beta .., _ => rfl
  | _, _, _, _, _, .zeta .., _ => rfl
  | _, _, _, _, _, .zetaLocal .., _ => rfl
  | _, _, _, _, _, .delta .., _ => rfl
  | _, _, _, _, _, .iota .., _ => rfl
  | _, _, _, _, _, .lit .., _ => rfl
  | _, _, _, _, _, .app .., _ => rfl
  | _, _, _, _, _, .lam .., _ => rfl
  | _, _, _, _, _, .pi .., _ => rfl
  | _, _, _, _, _, .letE .., _ => rfl
  | _, _, _, _, _, .sorts .., _ => rfl
  | _, _, _, _, _, .consts .., _ => rfl
  | _, _, _, _, _, .eta .., _ => rfl

end Rcic.Declarative.F8Measure.J3
