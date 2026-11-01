import rcic.RcicF3RecFieldMaskRelation
import rcic.RcicF3ReaderSupport
import rcic.RcicCtxMorph

/-!
# A local masking relation with supported, separately fitted captures

The two original assignments may differ at unused captures. Agreement and
lookup origins are required only at allowed slots, and actual syntactic
support proves that a clean subject reads only those slots. The source
assignment is compared with an arbitrary masked assignment; the latter
is never asserted to fit. Existing fixed syntactic modes and Origin are
reused unchanged.

These are internal typing-induction definitions and capture-extension
rules. Actual reader provenance must produce the support and the two
original fits. No condition is added to the checked apex.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskSupport
open Rcic.Declarative RawFamily RecFieldOrigin
open RecFieldMask (Marks ordinary mode Value)

abbrev Allowed := Nat → Prop

def allowCons (a : Prop) (allowed : Allowed) : Allowed
  | 0 => a
  | i + 1 => allowed i

def markCons (q : Option Nat) (marks : Marks) : Marks
  | 0 => q
  | i + 1 => marks i

def Agree (allowed : Allowed) (ρC ρD : Nat → PSet.{4}) : Prop :=
  ∀ i, allowed i → Equiv (ρC i) (ρD i)

def Supported (allowed : Allowed) (e : Expr Nat) : Prop :=
  ∀ i, freeBvarRef i 0 e = true → allowed i

theorem agree_cons {allowed : Allowed} {ρC ρD : Nat → PSet.{4}}
    (h : Agree allowed ρC ρD) {a : Prop} {x y : PSet.{4}}
    (hxy : a → Equiv x y) : Agree (allowCons a allowed) (vcons x ρC) (vcons y ρD)
  | 0, ha => hxy ha
  | i + 1, hi => h i hi

private theorem supported_under {allowed : Allowed} {e : Expr Nat}
    (h : ∀ i, freeBvarRef i 1 e = true → allowed i) :
    Supported (allowCons True allowed) e := by
  intro i hi
  cases i with
  | zero => exact True.intro
  | succ i =>
      apply h i
      rw [freeBvarRef_succ i 0 e] at hi
      exact hi

theorem Supported.app {allowed : Allowed} {f a : Expr Nat}
    (h : Supported allowed (.app f a)) : Supported allowed f ∧ Supported allowed a :=
  ⟨fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)),
    fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi))⟩

theorem Supported.pi {allowed : Allowed} {A B : Expr Nat}
    (h : Supported allowed (.pi A B)) :
    Supported allowed A ∧ Supported (allowCons True allowed) B :=
  ⟨fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)),
    supported_under (fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi)))⟩

theorem Supported.lam {allowed : Allowed} {A b : Expr Nat}
    (h : Supported allowed (.lam A b)) :
    Supported allowed A ∧ Supported (allowCons True allowed) b :=
  ⟨fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)),
    supported_under (fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi)))⟩

theorem Supported.letE {allowed : Allowed} {A v b : Expr Nat}
    (h : Supported allowed (.letE A v b)) :
    Supported allowed A ∧ Supported allowed v ∧ Supported (allowCons True allowed) b :=
  ⟨fun i hi => h i (Bool.or_eq_true_iff.mpr
      (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hi)))),
    fun i hi => h i (Bool.or_eq_true_iff.mpr
      (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hi)))),
    supported_under (fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi)))⟩

/-- Only the local support of this actual clean expression is compared. -/
theorem models_agree (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (allowed : Allowed) (ρC ρD : Nat → PSet.{4}) (ha : Agree allowed ρC ρD)
    (e : Expr Nat) (hf : occursConst fd.fref e = false) (hs : Supported allowed e) :
    Equiv (den (mkM P (table P μ fd C)) σ ρC e)
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρD e) :=
  ReaderSupport.den_free_supported P μ fd.fref (ofFrame P μ fd C)
    (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ e hf ρC ρD
    (fun i hi => ha i (hs i hi))

def Holds (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (ρC ρD η : Nat → PSet.{4}) (e A : Expr Nat) : Prop :=
  Value (mkM P μ) fd C (mode marks e)
    (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρC A))
    (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρD A))
    (den (mkM P (table P μ fd C)) σ ρC e)
    (den (mkM P (table P μ fd C)) σ η e)

def Context (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (allowed : Allowed) (Γ : LCtx)
    (ρC ρD η : Nat → PSet.{4}) : Prop :=
  ∀ i A, allowed i → lookupType Γ i = some A →
    Value (mkM P μ) fd C (marks i)
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρC A))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρD A))
      (ρC i) (η i)

/-- The actual constructor-prefix relation initializes the supported
relation with every slot allowed and identical original assignments. -/
theorem context_of_same (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4})
    (h : RecFieldMask.Context P μ fd C σ marks Γ ρ η) :
    Context P μ fd C σ marks (fun _ => True) Γ ρ ρ η :=
  fun i A _ hi => h i A hi

/-- This is the exact capture value relation supplied by a typing
induction hypothesis. Unused opaque captures need no such relation. -/
theorem context_capture (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (allowed : Allowed) (Γ : LCtx) (ρC ρD η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks allowed Γ ρC ρD η)
    (decl : LocalDecl) (q : Option Nat) (a : Prop) (x x' y : PSet.{4})
    (hv : a → Value (mkM P μ) fd C q
      (Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρC (declType decl)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
          σ ρD (declType decl))) x y) :
    Context P μ fd C σ (markCons q marks) (allowCons a allowed) (decl :: Γ)
      (vcons x ρC) (vcons x' ρD) (vcons y η) := by
  intro i A ha hi
  cases i with
  | zero =>
      have hlook : some (Declarative.lift 0 1 (declType decl)) = some A := by
        cases decl <;> exact hi
      cases hlook
      simpa only [markCons, vcons, den_lift, liftρ_zero, shiftρ_one_cons] using hv ha
  | succ i =>
      rw [lookupType_cons_succ] at hi
      cases ht : lookupType Γ i with
      | none => rw [ht] at hi; cases hi
      | some B =>
          rw [ht] at hi
          cases hi
          change Value (mkM P μ) fd C (marks i)
            (Ed (mkM P (table P μ fd C))
              (den (mkM P (table P μ fd C)) σ (vcons x ρC) (Declarative.lift 0 1 B)))
            (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
                σ (vcons x' ρD) (Declarative.lift 0 1 B))) (ρC i) (η i)
          simpa only [den_lift, liftρ_zero, shiftρ_one_cons] using h i B ha ht

theorem context_ordinary (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (allowed : Allowed) (Γ : LCtx) (ρC ρD η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks allowed Γ ρC ρD η)
    (decl : LocalDecl) (x x' y : PSet.{4}) (hxy : Equiv x y) :
    Context P μ fd C σ (ordinary marks) (allowCons True allowed) (decl :: Γ)
      (vcons x ρC) (vcons x' ρD) (vcons y η) :=
  context_capture P μ fd C σ marks allowed Γ ρC ρD η h decl none True x x' y
    (fun _ => hxy)

theorem context_opaque (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (allowed : Allowed) (Γ : LCtx) (ρC ρD η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks allowed Γ ρC ρD η)
    (decl : LocalDecl) (q : Option Nat) (x x' y : PSet.{4}) :
    Context P μ fd C σ (markCons q marks) (allowCons False allowed) (decl :: Γ)
      (vcons x ρC) (vcons x' ρD) (vcons y η) :=
  context_capture P μ fd C σ marks allowed Γ ρC ρD η h decl q False x x' y
    (fun hf => hf.elim)

theorem typed_type (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (marks : Marks) (ρC ρD η : Nat → PSet.{4})
    (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    {e : Expr Nat} {l : Level}
    (d : HasTyT E n Γ e (.sort l)) (hd : LOKt σ 4 K d)
    (h : Holds P μ fd C σ marks ρC ρD η e (.sort l)) :
    Equiv (den (mkM P (table P μ fd C)) σ ρC e)
      (den (mkM P (table P μ fd C)) σ η e) := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      simp only [Holds, Value, hm] at h
      have hz := RecFieldOrigin.separator h.2
        (sound_ty (P.good _ rfl) hE d hd ρC hρ) Equiv.rfl
      exact (den_type_ne_pempty (mkM P (table P μ fd C)) σ
        (fun k => pempty_not_mem_U4 P k) ρC
        (sound_ty (P.good _ rfl) hE d hd ρC hρ) hz).elim

end Rcic.F3.PSet.RecFieldMaskSupport
