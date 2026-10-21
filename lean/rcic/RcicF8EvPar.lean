import rcic.RcicF8ProofIndexPayload
import rcic.RcicF8StructPiPayload

/-!
# Single owner-side parallel provenance: proofIndex and structural Pi
No alternate EvPar, unrestricted literal output, global J, or reconstructed
endpoint-to-lit admission is introduced. All judgment inputs are the B2 Ev
objects in ProofIndexPayload. The structural constructor follows Devin reference-only #7007 (791c16f39a);
the SP-1 extractor supplies its original-index payload. No reference branch merged.
Future producers extend this same carrier and its traversals.
closure_claim=0.
-/
namespace Rcic.Declarative.F8Measure
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R R' : List (Jd E n)}

/-! Widening changes only root-membership evidence. These laws concern the
existing B2 transports, not a new source of literal atoms. -/
mutual
 theorem evTyVal_widen (hr : ∀ x ∈ R, x ∈ R')
     (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
     {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
       (D.widen hr).val hcl hinst = D.val hcl hinst
   | _, _, _, .lit .. => rfl
   | _, _, _, .wk _ _ D => by
       simp only [EvTy.widen, EvTy.val, evTyVal_widen hr hcl hinst D]
   | _, _, _, .esub _ _ D _ hv _ => by
       simp only [EvTy.widen, EvTy.val, evTyVal_widen hr hcl hinst D,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, .subst0 _ D _ hv => by
       simp only [EvTy.widen, EvTy.val, evTyVal_widen hr hcl hinst D,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, .substLet _ D _ hv => by
       simp only [EvTy.widen, EvTy.val, evTyVal_widen hr hcl hinst D,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, .var .. => rfl
   | _, _, _, .sort .. => rfl
   | _, _, _, .const .. => rfl
   | _, _, _, .rety D c => by
       simp only [EvTy.widen, EvTy.val, evTyVal_widen hr hcl hinst D,
         evTcVal_widen hr hcl hinst c]
 theorem evTcVal_widen (hr : ∀ x ∈ R, x ∈ R')
     (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
     {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
       (c.widen hr).val hcl hinst = c.val hcl hinst
   | _, _, _, .lit .. => rfl
   | _, _, _, .ofCv _ c => by
       simp only [EvTc.widen, EvTc.val, evCvVal_widen hr hcl hinst c]
   | _, _, _, .refl .. => rfl
   | _, _, _, .wk _ _ c => by
       simp only [EvTc.widen, EvTc.val, evTcVal_widen hr hcl hinst c]
   | _, _, _, .symm c => by
       simp only [EvTc.widen, EvTc.val, evTcVal_widen hr hcl hinst c]
   | _, _, _, .trans c₁ c₂ => by
       simp only [EvTc.widen, EvTc.val, evTcVal_widen hr hcl hinst c₁,
         evTcVal_widen hr hcl hinst c₂]
   | _, _, _, .piCod _ hA c => by
       simp only [EvTc.widen, EvTc.val, evTyVal_widen hr hcl hinst hA,
         evTcVal_widen hr hcl hinst c]
   | _, _, _, .subst0 _ c _ hv => by
       simp only [EvTc.widen, EvTc.val, evTcVal_widen hr hcl hinst c,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, .substLet _ c _ hv => by
       simp only [EvTc.widen, EvTc.val, evTcVal_widen hr hcl hinst c,
         evTyVal_widen hr hcl hinst hv]
 theorem evCvVal_widen (hr : ∀ x ∈ R, x ∈ R')
     (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
     {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
       (c.widen hr).val hcl hinst = c.val hcl hinst
   | _, _, _, _, .lit .. => rfl
   | _, _, _, _, .refl D => by
       simp only [EvCv.widen, EvCv.val, evTyVal_widen hr hcl hinst D]
   | _, _, _, _, .symm c => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c]
   | _, _, _, _, .trans c₁ c₂ => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c₁,
         evCvVal_widen hr hcl hinst c₂]
   | _, _, _, _, .tyConv _ c cA => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c,
         evCvVal_widen hr hcl hinst cA]
   | _, _, _, _, .wk _ _ c => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c]
   | _, _, _, _, .esub _ _ c _ hv _ => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, _, .subst0 _ c _ hv => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, _, .substLet _ c _ hv => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c,
         evTyVal_widen hr hcl hinst hv]
   | _, _, _, _, .sorts .. => rfl
   | _, _, _, _, .consts .. => rfl
   | _, _, _, _, .rety c ct => by
       simp only [EvCv.widen, EvCv.val, evCvVal_widen hr hcl hinst c,
         evTcVal_widen hr hcl hinst ct]
end

mutual
 theorem evTySize_widen (hr : ∀ x ∈ R, x ∈ R') :
     {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
       (D.widen hr).size = D.size
   | _, _, _, .lit .. => rfl
   | _, _, _, .wk _ _ D => by
       simp only [EvTy.widen, EvTy.size, evTySize_widen hr D]
   | _, _, _, .esub _ _ D _ hv hvT => by
       simp only [EvTy.widen, EvTy.size, evTySize_widen hr D,
         evTySize_widen hr hv, evTySize_widen hr hvT]
   | _, _, _, .subst0 _ D _ hv => by
       simp only [EvTy.widen, EvTy.size, evTySize_widen hr D, evTySize_widen hr hv]
   | _, _, _, .substLet _ D _ hv => by
       simp only [EvTy.widen, EvTy.size, evTySize_widen hr D, evTySize_widen hr hv]
   | _, _, _, .var .. => rfl
   | _, _, _, .sort .. => rfl
   | _, _, _, .const .. => rfl
   | _, _, _, .rety D c => by
       simp only [EvTy.widen, EvTy.size, evTySize_widen hr D, evTcSize_widen hr c]
 theorem evTcSize_widen (hr : ∀ x ∈ R, x ∈ R') :
     {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
       (c.widen hr).size = c.size
   | _, _, _, .lit .. => rfl
   | _, _, _, .ofCv _ c => by
       simp only [EvTc.widen, EvTc.size, evCvSize_widen hr c]
   | _, _, _, .refl .. => rfl
   | _, _, _, .wk _ _ c => by
       simp only [EvTc.widen, EvTc.size, evTcSize_widen hr c]
   | _, _, _, .symm c => by
       simp only [EvTc.widen, EvTc.size, evTcSize_widen hr c]
   | _, _, _, .trans c₁ c₂ => by
       simp only [EvTc.widen, EvTc.size, evTcSize_widen hr c₁, evTcSize_widen hr c₂]
   | _, _, _, .piCod _ hA c => by
       simp only [EvTc.widen, EvTc.size, evTySize_widen hr hA, evTcSize_widen hr c]
   | _, _, _, .subst0 _ c _ hv => by
       simp only [EvTc.widen, EvTc.size, evTcSize_widen hr c, evTySize_widen hr hv]
   | _, _, _, .substLet _ c _ hv => by
       simp only [EvTc.widen, EvTc.size, evTcSize_widen hr c, evTySize_widen hr hv]
 theorem evCvSize_widen (hr : ∀ x ∈ R, x ∈ R') :
     {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
       (c.widen hr).size = c.size
   | _, _, _, _, .lit .. => rfl
   | _, _, _, _, .refl D => by
       simp only [EvCv.widen, EvCv.size, evTySize_widen hr D]
   | _, _, _, _, .symm c => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c]
   | _, _, _, _, .trans c₁ c₂ => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c₁, evCvSize_widen hr c₂]
   | _, _, _, _, .tyConv _ c cA => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c, evCvSize_widen hr cA]
   | _, _, _, _, .wk _ _ c => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c]
   | _, _, _, _, .esub _ _ c _ hv hvT => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c,
         evTySize_widen hr hv, evTySize_widen hr hvT]
   | _, _, _, _, .subst0 _ c _ hv => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c, evTySize_widen hr hv]
   | _, _, _, _, .substLet _ c _ hv => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c, evTySize_widen hr hv]
   | _, _, _, _, .sorts .. => rfl
   | _, _, _, _, .consts .. => rfl
   | _, _, _, _, .rety c ct => by
       simp only [EvCv.widen, EvCv.size, evCvSize_widen hr c, evTcSize_widen hr ct]
end

/-! ### Atomic producer payloads (`sortEq`, `consts`, `lit`) and per-producer `substVal` -/

/-- Provenance payload of `EvPar.sortEq`: `=ₙ`-related sorts step in parallel
    at `T₀`, re-indexed to `T` by one `conv` wrapper `idx : EvTc R Γ T₀ T`. -/
structure SortEqPayload (R : List (Jd E n)) (Γ : LCtx) (l₁ l₂ : Level) (T : Expr Nat) where
  T₀ : Expr Nat
  h : eqN l₁ l₂
  hl : EvTy R Γ (.sort l₁) T₀
  hr : EvTy R Γ (.sort l₂) T₀
  idx : EvTc R Γ T₀ T

def SortEqPayload.leaves {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat}
    (p : SortEqPayload R Γ l₁ l₂ T) : List (Jd E n) :=
  p.hl.leaves ++ p.hr.leaves ++ p.idx.leaves

def SortEqPayload.size {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat}
    (p : SortEqPayload R Γ l₁ l₂ T) : Nat :=
  1 + p.hl.size + p.hr.size + p.idx.size

theorem SortEqPayload.leaves_root {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat}
    (p : SortEqPayload R Γ l₁ l₂ T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r ∈ R, SubEq x r := by
  simp only [SortEqPayload.leaves, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact p.hl.leaves_root x hx
  · exact p.hr.leaves_root x hx
  · exact p.idx.leaves_root x hx

def SortEqPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat}
    (p : SortEqPayload R Γ l₁ l₂ T) : SortEqPayload R' Γ l₁ l₂ T where
  T₀ := p.T₀
  h := p.h
  hl := p.hl.widen hr
  hr := p.hr.widen hr
  idx := p.idx.widen hr

theorem SortEqPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat}
    (p : SortEqPayload R Γ l₁ l₂ T) : (p.widen hr).leaves = p.leaves := by
  simp only [SortEqPayload.widen, SortEqPayload.leaves, EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `EvPar.sortEq`: `ParRedT.sortEq` under one `conv`. -/
def sortEqStep {Γ : LCtx} {l₁ l₂ : Level} {T₀ T : Expr Nat}
    (h : eqN l₁ l₂) (hl : HasTyT E n Γ (.sort l₁) T₀) (hr : HasTyT E n Γ (.sort l₂) T₀)
    (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ (.sort l₁) (.sort l₂) T :=
  .conv Γ (.sort l₁) (.sort l₂) T₀ T (.sortEq Γ l₁ l₂ T₀ h hl hr) idx

def SortEqPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat} (p : SortEqPayload R Γ l₁ l₂ T) :
    ParRedT (PEqLeafT E n) E n Γ (.sort l₁) (.sort l₂) T :=
  sortEqStep p.h (p.hl.val hcl hinst) (p.hr.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `SortEqPayload` (`hcl`/`hinst` only, #7107). -/
def SortEqPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {l₁ l₂ : Level} {T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : SortEqPayload R Γ l₁ l₂ T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.sort l₁))
      (instantiate j (lift 0 j v) (.sort l₂))
      (instantiate j (lift 0 j v) T) :=
  sortEqStep p.h
    (hasTyT_substS hcl hinst v t (p.hl.val hcl hinst) hget hv)
    (hasTyT_substS hcl hinst v t (p.hr.val hcl hinst) hget hv)
    (tyConvT_substS hcl hinst v t (p.idx.val hcl hinst) hget hv)

def SortEqPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {l₁ l₂ : Level} {T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : SortEqPayload R Γ l₁ l₂ T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.sort l₁))
      (instantiate j (lift 0 j w) (.sort l₂))
      (instantiate j (lift 0 j w) T) :=
  sortEqStep p.h
    (hasTyT_substLetS hcl hinst t w (p.hl.val hcl hinst) hget hv)
    (hasTyT_substLetS hcl hinst t w (p.hr.val hcl hinst) hget hv)
    (tyConvT_substLetS hcl hinst t w (p.idx.val hcl hinst) hget hv)

/-- Leaf-less `SortEqPayload` for a `ConvT.sorts` literal (`leaves = []`). -/
def SortEqPayload.ofSorts (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    SortEqPayload R Γ l₁ l₂ (.sort (.succ l₁)) where
  T₀ := .sort (.succ l₁)
  h := h
  hl := .sortsLeft (Γ := Γ) l₁ l₂ h
  hr := .sortsRight (Γ := Γ) l₁ l₂ h
  idx := .refl Γ (.sort (.succ l₁))

theorem SortEqPayload.ofSorts_leaves (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    (SortEqPayload.ofSorts (R := R) Γ l₁ l₂ h).leaves = [] := rfl

/-- Provenance payload of `EvPar.consts`: `=ₙ`-related universe arguments on a
    constant step in parallel at `T₀`, re-indexed to `T` by `idx : EvTc R Γ T₀ T`. -/
structure ConstsPayload (R : List (Jd E n)) (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (T : Expr Nat) where
  T₀ : Expr Nat
  h : eqNList ls ls'
  hl : EvTy R Γ (.const r ls) T₀
  hr : EvTy R Γ (.const r ls') T₀
  idx : EvTc R Γ T₀ T

def ConstsPayload.leaves {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) : List (Jd E n) :=
  p.hl.leaves ++ p.hr.leaves ++ p.idx.leaves

def ConstsPayload.size {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) : Nat :=
  1 + p.hl.size + p.hr.size + p.idx.size

theorem ConstsPayload.leaves_root {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [ConstsPayload.leaves, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact p.hl.leaves_root x hx
  · exact p.hr.leaves_root x hx
  · exact p.idx.leaves_root x hx

def ConstsPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {T : Expr Nat} (p : ConstsPayload R Γ r ls ls' T) : ConstsPayload R' Γ r ls ls' T where
  T₀ := p.T₀
  h := p.h
  hl := p.hl.widen hr
  hr := p.hr.widen hr
  idx := p.idx.widen hr

theorem ConstsPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {T : Expr Nat} (p : ConstsPayload R Γ r ls ls' T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [ConstsPayload.widen, ConstsPayload.leaves, EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `EvPar.consts`: `ParRedT.consts` under one `conv`. -/
def constsStep {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T₀ T : Expr Nat}
    (h : eqNList ls ls') (hl : HasTyT E n Γ (.const r ls) T₀)
    (hr : HasTyT E n Γ (.const r ls') T₀) (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ (.const r ls) (.const r ls') T :=
  .conv Γ (.const r ls) (.const r ls') T₀ T (.consts Γ r ls ls' T₀ h hl hr) idx

def ConstsPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) :
    ParRedT (PEqLeafT E n) E n Γ (.const r ls) (.const r ls') T :=
  constsStep p.h (p.hl.val hcl hinst) (p.hr.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `ConstsPayload` (`hcl`/`hinst` only, #7107). -/
def ConstsPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : ConstsPayload R Γ r ls ls' T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.const r ls))
      (instantiate j (lift 0 j v) (.const r ls'))
      (instantiate j (lift 0 j v) T) :=
  constsStep p.h
    (hasTyT_substS hcl hinst v t (p.hl.val hcl hinst) hget hv)
    (hasTyT_substS hcl hinst v t (p.hr.val hcl hinst) hget hv)
    (tyConvT_substS hcl hinst v t (p.idx.val hcl hinst) hget hv)

def ConstsPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : ConstsPayload R Γ r ls ls' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.const r ls))
      (instantiate j (lift 0 j w) (.const r ls'))
      (instantiate j (lift 0 j w) T) :=
  constsStep p.h
    (hasTyT_substLetS hcl hinst t w (p.hl.val hcl hinst) hget hv)
    (hasTyT_substLetS hcl hinst t w (p.hr.val hcl hinst) hget hv)
    (tyConvT_substLetS hcl hinst t w (p.idx.val hcl hinst) hget hv)

/-- `ConstsPayload` for a `ConvT.consts` literal with retyping chain `tc` (`leaves = tc.leaves`,
    using `EvTy.constsRightWith`, cc ruling 12:34Z). -/
def ConstsPayload.ofConstsWith (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    ConstsPayload R Γ r ls ls' (instantiateLevels ls m.mtype) where
  T₀ := instantiateLevels ls m.mtype
  h := heq
  hl := .constsLeft (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq
  hr := .constsRightWith (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq tc
  idx := .refl Γ (instantiateLevels ls m.mtype)

theorem ConstsPayload.ofConstsWith_leaves (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    (ConstsPayload.ofConstsWith (R := R) Γ r ls ls' m hres hlen hwf hwf' heq tc).leaves =
      tc.leaves := by
  simp only [ConstsPayload.ofConstsWith, ConstsPayload.leaves, EvTy.constsLeft_leaves,
    EvTy.constsRightWith_leaves, EvTc.leaves, List.nil_append, List.append_nil]

/-- Provenance payload of `EvPar.lit`: a literal `t` expands to `natExpand t`
    at `T₀`, re-indexed to `T` by `idx : EvTc R Γ T₀ T`. -/
structure LitPayload (R : List (Jd E n)) (Γ : LCtx) (t : Nat) (T : Expr Nat) where
  T₀ : Expr Nat
  hexp : EvTy R Γ (natExpand t) T₀
  idx : EvTc R Γ T₀ T

def LitPayload.leaves {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (p : LitPayload R Γ t T) : List (Jd E n) :=
  p.hexp.leaves ++ p.idx.leaves

def LitPayload.size {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (p : LitPayload R Γ t T) : Nat :=
  1 + p.hexp.size + p.idx.size

theorem LitPayload.leaves_root {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (p : LitPayload R Γ t T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r ∈ R, SubEq x r := by
  simp only [LitPayload.leaves, List.mem_append] at hx
  rcases hx with hx | hx
  · exact p.hexp.leaves_root x hx
  · exact p.idx.leaves_root x hx

def LitPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (p : LitPayload R Γ t T) : LitPayload R' Γ t T where
  T₀ := p.T₀
  hexp := p.hexp.widen hr
  idx := p.idx.widen hr

theorem LitPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (p : LitPayload R Γ t T) : (p.widen hr).leaves = p.leaves := by
  simp only [LitPayload.widen, LitPayload.leaves, EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `EvPar.lit`: `ParRedT.lit` under one `conv`. -/
def litStep {Γ : LCtx} {t : Nat} {T₀ T : Expr Nat}
    (hexp : HasTyT E n Γ (natExpand t) T₀) (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ (.lit t) (natExpand t) T :=
  .conv Γ (.lit t) (natExpand t) T₀ T (.lit Γ t T₀ hexp) idx

def LitPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {t : Nat} {T : Expr Nat} (p : LitPayload R Γ t T) :
    ParRedT (PEqLeafT E n) E n Γ (.lit t) (natExpand t) T :=
  litStep (p.hexp.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `LitPayload` (`hcl`/`hinst` only, #7107). -/
def LitPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {t : Nat} {T t₀ v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t₀))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t₀))
    (p : LitPayload R Γ t T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.lit t))
      (instantiate j (lift 0 j v) (natExpand t))
      (instantiate j (lift 0 j v) T) := by
  have hexp' := hasTyT_substS hcl hinst v t₀ (p.hexp.val hcl hinst) hget hv
  rw [natExpand_instantiate j (lift 0 j v) t] at hexp' ⊢
  exact litStep hexp' (tyConvT_substS hcl hinst v t₀ (p.idx.val hcl hinst) hget hv)

def LitPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {t : Nat} {T t₀ w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t₀ w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t₀))
    (p : LitPayload R Γ t T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.lit t))
      (instantiate j (lift 0 j w) (natExpand t))
      (instantiate j (lift 0 j w) T) := by
  have hexp' := hasTyT_substLetS hcl hinst t₀ w (p.hexp.val hcl hinst) hget hv
  rw [natExpand_instantiate j (lift 0 j w) t] at hexp' ⊢
  exact litStep hexp' (tyConvT_substLetS hcl hinst t₀ w (p.idx.val hcl hinst) hget hv)

/-- Provenance payload of `EvPar.refl`: a typed term steps to itself at `T₀`,
    re-indexed to `T` by `idx : EvTc R Γ T₀ T`. -/
structure ReflPayload (R : List (Jd E n)) (Γ : LCtx) (a T : Expr Nat) where
  T₀ : Expr Nat
  h : EvTy R Γ a T₀
  idx : EvTc R Γ T₀ T

def ReflPayload.leaves {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) : List (Jd E n) :=
  p.h.leaves ++ p.idx.leaves

def ReflPayload.size {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) : Nat :=
  1 + p.h.size + p.idx.size

theorem ReflPayload.leaves_root {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r ∈ R, SubEq x r := by
  simp only [ReflPayload.leaves, List.mem_append] at hx
  rcases hx with hx | hx
  · exact p.h.leaves_root x hx
  · exact p.idx.leaves_root x hx

def ReflPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) : ReflPayload R' Γ a T where
  T₀ := p.T₀
  h := p.h.widen hr
  idx := p.idx.widen hr

theorem ReflPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) : (p.widen hr).leaves = p.leaves := by
  simp only [ReflPayload.widen, ReflPayload.leaves, EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `EvPar.refl`: `ParRedT.refl` under one `conv`. -/
def reflStep {Γ : LCtx} {a T₀ T : Expr Nat}
    (h : HasTyT E n Γ a T₀) (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ a a T :=
  .conv Γ a a T₀ T (.refl Γ a T₀ h) idx

def ReflPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a T : Expr Nat} (p : ReflPayload R Γ a T) :
    ParRedT (PEqLeafT E n) E n Γ a a T :=
  reflStep (p.h.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `ReflPayload` (`hcl`/`hinst` only, #7107). -/
def ReflPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a T t₀ v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t₀))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t₀))
    (p : ReflPayload R Γ a T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) T) :=
  reflStep
    (hasTyT_substS hcl hinst v t₀ (p.h.val hcl hinst) hget hv)
    (tyConvT_substS hcl hinst v t₀ (p.idx.val hcl hinst) hget hv)

def ReflPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a T t₀ w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t₀ w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t₀))
    (p : ReflPayload R Γ a T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) a)
      (instantiate j (lift 0 j w) a)
      (instantiate j (lift 0 j w) T) :=
  reflStep
    (hasTyT_substLetS hcl hinst t₀ w (p.h.val hcl hinst) hget hv)
    (tyConvT_substLetS hcl hinst t₀ w (p.idx.val hcl hinst) hget hv)

/-- Canonical `ReflPayload` from a provenance typing `h : EvTy R Γ a T`. -/
def ReflPayload.ofTy {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) :
    ReflPayload R Γ a T where
  T₀ := T
  h := h
  idx := .refl Γ T

theorem ReflPayload.ofTy_leaves {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) :
    (ReflPayload.ofTy h).leaves = h.leaves := by
  simp only [ReflPayload.ofTy, ReflPayload.leaves, EvTc.leaves, List.append_nil]

/-- Substituted materializers for `ProofIndexPayload` and `StructPiPayload` (`hcl`/`hinst` only). -/
def ProofIndexPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : ProofIndexPayload R Γ a b T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T) :=
  .peq _ _ _ _
    (peqLeafT_reconcile_propIndex
      (hasTyT_substS hcl hinst v t (p.propTy.val hcl hinst) hget hv)
      (tyConvT_substS hcl hinst v t (p.chain.val hcl hinst) hget hv)
      (hasTyT_substS hcl hinst v t (p.leftTy.val hcl hinst) hget hv)
      (hasTyT_substS hcl hinst v t (p.rightTy.val hcl hinst) hget hv)).1

def ProofIndexPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : ProofIndexPayload R Γ a b T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) a) (instantiate j (lift 0 j w) b)
      (instantiate j (lift 0 j w) T) :=
  .peq _ _ _ _
    (peqLeafT_reconcile_propIndex
      (hasTyT_substLetS hcl hinst t w (p.propTy.val hcl hinst) hget hv)
      (tyConvT_substLetS hcl hinst t w (p.chain.val hcl hinst) hget hv)
      (hasTyT_substLetS hcl hinst t w (p.leftTy.val hcl hinst) hget hv)
      (hasTyT_substLetS hcl hinst t w (p.rightTy.val hcl hinst) hget hv)).1

def StructPiPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A B A' B' T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : StructPiPayload R Γ A B A' B' T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.pi A B))
      (instantiate j (lift 0 j v) (.pi A' B'))
      (instantiate j (lift 0 j v) T) := by
  have hget' := subst_arg_get_succ (.assumption A) hget
  have hv' := subst_hvty_wk (.assumption A) hcl hv
  have hA' := hasTyT_substS hcl hinst v t (p.hA.val hcl hinst) hget hv
  have hc' := convT_substS hcl hinst v t (p.hc.val hcl hinst) hget hv
  have hB' := hasTyT_substS hcl hinst v t (p.hB.val hcl hinst) hget' hv'
  have hcB' := convT_substS hcl hinst v t (p.hcB.val hcl hinst) hget' hv'
  have hrt' := hasTyT_substS hcl hinst v t (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substS hcl hinst v t (p.idx.val hcl hinst) hget hv
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hcB' hrt' idx' ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hrt' ⊢
  exact structPiStep hA' hc' hB' hcB' hrt' idx'

def StructPiPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A B A' B' T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : StructPiPayload R Γ A B A' B' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.pi A B))
      (instantiate j (lift 0 j w) (.pi A' B'))
      (instantiate j (lift 0 j w) T) := by
  have hget' := substLet_get_succ (.assumption A) hget
  have hv' := subst_hvty_wk (.assumption A) hcl hv
  have hA' := hasTyT_substLetS hcl hinst t w (p.hA.val hcl hinst) hget hv
  have hc' := convT_substLetS hcl hinst t w (p.hc.val hcl hinst) hget hv
  have hB' := hasTyT_substLetS hcl hinst t w (p.hB.val hcl hinst) hget' hv'
  have hcB' := convT_substLetS hcl hinst t w (p.hcB.val hcl hinst) hget' hv'
  have hrt' := hasTyT_substLetS hcl hinst t w (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substLetS hcl hinst t w (p.idx.val hcl hinst) hget hv
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hcB' hrt' idx' ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w] at hrt' ⊢
  exact structPiStep hA' hc' hB' hcB' hrt' idx'

/-- The single owner carrier. Includes `proofIndex`, `structPi`, the D2a atomic
producers (`sortEq`, `consts`, `lit`), and `refl`. There is no unrestricted ParRedT-to-lit constructor. -/
inductive EvPar (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | proofIndex {Γ a b T} (p : ProofIndexPayload R Γ a b T) : EvPar R Γ a b T
  | structPi {Γ A B A' B' T} (p : StructPiPayload R Γ A B A' B' T) :
      EvPar R Γ (.pi A B) (.pi A' B') T
  | sortEq {Γ l₁ l₂ T} (p : SortEqPayload R Γ l₁ l₂ T) :
      EvPar R Γ (.sort l₁) (.sort l₂) T
  | consts {Γ r ls ls' T} (p : ConstsPayload R Γ r ls ls' T) :
      EvPar R Γ (.const r ls) (.const r ls') T
  | lit {Γ t T} (p : LitPayload R Γ t T) :
      EvPar R Γ (.lit t) (natExpand t) T
  | refl {Γ a T} (p : ReflPayload R Γ a T) :
      EvPar R Γ a a T

/-- EXACT original producer output, not merely the same endpoints. -/
def EvPar.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T →
      ParRedT (PEqLeafT E n) E n Γ a b T
  | Γ, a, b, T, .proofIndex p => .peq Γ a b T
      (peqLeafT_reconcile_propIndex (p.propTy.val hcl hinst)
        (p.chain.val hcl hinst) (p.leftTy.val hcl hinst)
        (p.rightTy.val hcl hinst)).1
  | _, _, _, _, .structPi p =>
      structPiStep (p.hA.val hcl hinst) (p.hc.val hcl hinst)
        (p.hB.val hcl hinst) (p.hcB.val hcl hinst) (p.hrt.val hcl hinst)
        (p.idx.val hcl hinst)
  | _, _, _, _, .sortEq p => p.val hcl hinst
  | _, _, _, _, .consts p => p.val hcl hinst
  | _, _, _, _, .lit p => p.val hcl hinst
  | _, _, _, _, .refl p => p.val hcl hinst

/-- Substituted materializer for any `EvPar` producer (`hcl`/`hinst` only, #7107). -/
def EvPar.substVal0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    (D : EvPar R Γ a b T) →
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | .proofIndex p => p.substVal hcl hinst j hget hv
  | .structPi p => p.substVal hcl hinst j hget hv
  | .sortEq p => p.substVal hcl hinst j hget hv
  | .consts p => p.substVal hcl hinst j hget hv
  | .lit p => p.substVal hcl hinst j hget hv
  | .refl p => p.substVal hcl hinst j hget hv

/-- Let-substituted materializer for any `EvPar` producer (`hcl`/`hinst` only, #7107). -/
def EvPar.substLetVal0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
    (D : EvPar R Γ a b T) →
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) a) (instantiate j (lift 0 j w) b)
      (instantiate j (lift 0 j w) T)
  | .proofIndex p => p.substLetVal hcl hinst j hget hv
  | .structPi p => p.substLetVal hcl hinst j hget hv
  | .sortEq p => p.substLetVal hcl hinst j hget hv
  | .consts p => p.substLetVal hcl hinst j hget hv
  | .lit p => p.substLetVal hcl hinst j hget hv
  | .refl p => p.substLetVal hcl hinst j hget hv

def EvPar.leaves : {Γ : LCtx} → {a b T : Expr Nat} →
    EvPar R Γ a b T → List (Jd E n)
  | _, _, _, _, .proofIndex p => p.leaves
  | _, _, _, _, .structPi p => p.leaves
  | _, _, _, _, .sortEq p => p.leaves
  | _, _, _, _, .consts p => p.leaves
  | _, _, _, _, .lit p => p.leaves
  | _, _, _, _, .refl p => p.leaves

def EvPar.size : {Γ : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T → Nat
  | _, _, _, _, .proofIndex p => p.size
  | _, _, _, _, .structPi p => p.size
  | _, _, _, _, .sortEq p => p.size
  | _, _, _, _, .consts p => p.size
  | _, _, _, _, .lit p => p.size
  | _, _, _, _, .refl p => p.size

/-- Exact answers are an interface of THIS terminal constructor, not a
requirement that every future EvPar has a single outer proposition or index. -/
def EvPar.proofIndexLazyAnswer {Γ : LCtx} {a b T : Expr Nat}
    (p : ProofIndexPayload R Γ a b T) (side : Side) : EvTc R Γ T p.proposition :=
  p.lazyAnswer side

def EvPar.proofIndexRequests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) :
    Requests ((EvPar.proofIndex p).val hcl hinst) := p.requests hcl hinst

def EvPar.proofIndexAnswers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) :
    AnsweredOrigins ((EvPar.proofIndex p).val hcl hinst)
      (EvPar.proofIndexRequests hcl hinst p) := p.answers hcl hinst

theorem EvPar.leaves_root {Γ : LCtx} {a b T : Expr Nat} (D : EvPar R Γ a b T)
    (x : Jd E n) (hx : x ∈ D.leaves) : ∃ r ∈ R, SubEq x r := by
  cases D with
  | proofIndex p => exact p.leaves_root x hx
  | structPi p => exact p.leaves_root x hx
  | sortEq p => exact p.leaves_root x hx
  | consts p => exact p.leaves_root x hx
  | lit p => exact p.leaves_root x hx
  | refl p => exact p.leaves_root x hx

def EvPar.widen (hr : ∀ x ∈ R, x ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T → EvPar R' Γ a b T
  | _, _, _, _, .proofIndex p => .proofIndex (p.widen hr)
  | _, _, _, _, .structPi p => .structPi (p.widen hr)
  | _, _, _, _, .sortEq p => .sortEq (p.widen hr)
  | _, _, _, _, .consts p => .consts (p.widen hr)
  | _, _, _, _, .lit p => .lit (p.widen hr)
  | _, _, _, _, .refl p => .refl (p.widen hr)

theorem EvPar.leaves_widen (hr : ∀ x ∈ R, x ∈ R')
    {Γ : LCtx} {a b T : Expr Nat} (D : EvPar R Γ a b T) :
    (D.widen hr).leaves = D.leaves := by
  cases D with
  | proofIndex p => exact p.leaves_widen hr
  | structPi p => exact p.leaves_widen hr
  | sortEq p => exact p.leaves_widen hr
  | consts p => exact p.leaves_widen hr
  | lit p => exact p.leaves_widen hr
  | refl p => exact p.leaves_widen hr

theorem EvPar.val_widen (hr : ∀ x ∈ R, x ∈ R')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (D : EvPar R Γ a b T) :
    (D.widen hr).val hcl hinst = D.val hcl hinst := by
  cases D with
  | proofIndex p =>
      simp only [EvPar.widen, EvPar.val, ProofIndexPayload.widen,
        evTyVal_widen, evTcVal_widen]
  | structPi p =>
      simp only [EvPar.widen, EvPar.val, StructPiPayload.widen,
        evTyVal_widen, evCvVal_widen, evTcVal_widen]
  | sortEq p =>
      simp only [EvPar.widen, EvPar.val, SortEqPayload.widen, SortEqPayload.val,
        evTyVal_widen, evTcVal_widen]
  | consts p =>
      simp only [EvPar.widen, EvPar.val, ConstsPayload.widen, ConstsPayload.val,
        evTyVal_widen, evTcVal_widen]
  | lit p =>
      simp only [EvPar.widen, EvPar.val, LitPayload.widen, LitPayload.val,
        evTyVal_widen, evTcVal_widen]
  | refl p =>
      simp only [EvPar.widen, EvPar.val, ReflPayload.widen, ReflPayload.val,
        evTyVal_widen, evTcVal_widen]

theorem EvPar.size_widen (hr : ∀ x ∈ R, x ∈ R')
    {Γ : LCtx} {a b T : Expr Nat} (D : EvPar R Γ a b T) :
    (D.widen hr).size = D.size := by
  cases D with
  | proofIndex p =>
      simp only [EvPar.widen, EvPar.size, ProofIndexPayload.widen,
        ProofIndexPayload.size, evTySize_widen, evTcSize_widen]
  | structPi p =>
      simp only [EvPar.widen, EvPar.size, StructPiPayload.widen,
        StructPiPayload.size, evTySize_widen, evCvSize_widen, evTcSize_widen]
  | sortEq p =>
      simp only [EvPar.widen, EvPar.size, SortEqPayload.widen,
        SortEqPayload.size, evTySize_widen, evTcSize_widen]
  | consts p =>
      simp only [EvPar.widen, EvPar.size, ConstsPayload.widen,
        ConstsPayload.size, evTySize_widen, evTcSize_widen]
  | lit p =>
      simp only [EvPar.widen, EvPar.size, LitPayload.widen,
        LitPayload.size, evTySize_widen, evTcSize_widen]
  | refl p =>
      simp only [EvPar.widen, EvPar.size, ReflPayload.widen,
        ReflPayload.size, evTySize_widen, evTcSize_widen]

theorem EvPar.proofIndex_request_index (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {a b T : Expr Nat}
    (p : ProofIndexPayload R Γ a b T)
    (o : Occ ((EvPar.proofIndex p).val hcl hinst)) (side : Side) :
    (EvPar.proofIndexRequests hcl hinst p o side).index = T := by
  cases o; cases side <;> rfl

theorem EvPar.proofIndex_answer_materializes (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {a b T : Expr Nat}
    (p : ProofIndexPayload R Γ a b T)
    (o : Occ ((EvPar.proofIndex p).val hcl hinst)) (side : Side) :
    HEq (EvPar.proofIndexAnswers hcl hinst p o side)
      ((EvPar.proofIndexLazyAnswer p side).val hcl hinst) := by
  cases o; cases side <;> rfl

theorem EvPar.val_proofIndex (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) :
    (EvPar.proofIndex p).val hcl hinst =
      ParRedT.peq Γ a b T (peqLeafT_reconcile_propIndex (p.propTy.val hcl hinst)
        (p.chain.val hcl hinst) (p.leftTy.val hcl hinst)
        (p.rightTy.val hcl hinst)).1 := rfl

/-- The structural-Pi constructor's materialization is exactly `structPiStep`. -/
theorem EvPar.val_structPi (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T) :
    (EvPar.structPi p).val hcl hinst =
      structPiStep (p.hA.val hcl hinst) (p.hc.val hcl hinst)
        (p.hB.val hcl hinst) (p.hcB.val hcl hinst) (p.hrt.val hcl hinst)
        (p.idx.val hcl hinst) := rfl

theorem EvPar.val_sortEq (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {l₁ l₂ : Level} {T : Expr Nat} (p : SortEqPayload R Γ l₁ l₂ T) :
    (EvPar.sortEq p).val hcl hinst = p.val hcl hinst := rfl

theorem EvPar.val_consts (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) :
    (EvPar.consts p).val hcl hinst = p.val hcl hinst := rfl

theorem EvPar.val_lit (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {t : Nat} {T : Expr Nat} (p : LitPayload R Γ t T) :
    (EvPar.lit p).val hcl hinst = p.val hcl hinst := rfl

theorem EvPar.val_refl (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a T : Expr Nat} (p : ReflPayload R Γ a T) :
    (EvPar.refl p).val hcl hinst = p.val hcl hinst := rfl

/-- Canonical `EvPar.refl` from a provenance typing `h : EvTy R Γ a T`. -/
def EvPar.ofTy {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) :
    EvPar R Γ a a T :=
  .refl (.ofTy h)

theorem EvPar.ofTy_leaves {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) :
    (EvPar.ofTy h).leaves = h.leaves :=
  ReflPayload.ofTy_leaves h

/-! ### D2b structural/congruence producer payloads (`delta`, `bvarZeta`, `lam`, `app`, `letE`) -/

/-- Provenance payload of `delta`: a transparent constant unfolds to `instantiateLevels ls body`
    at `T₀`, re-indexed to `T` by `idx : EvTc R Γ T₀ T`. -/
structure DeltaPayload (R : List (Jd E n)) (Γ : LCtx) (r : Nat) (ls : List Level)
    (body T : Expr Nat) where
  m : CheckedMember
  T₀ : Expr Nat
  hres : E.members r = some m
  hbody : m.body = some body
  htr : transparent m.mclass = true
  hlen : ls.length = m.arity
  hwf : levelsBounded n ls = true
  hl : EvTy R Γ (.const r ls) T₀
  hr : EvTy R Γ (instantiateLevels ls body) T₀
  idx : EvTc R Γ T₀ T

def DeltaPayload.leaves {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : List (Jd E n) :=
  p.hl.leaves ++ p.hr.leaves ++ p.idx.leaves

def DeltaPayload.size {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : Nat :=
  1 + p.hl.size + p.hr.size + p.idx.size

theorem DeltaPayload.leaves_root {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [DeltaPayload.leaves, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact p.hl.leaves_root x hx
  · exact p.hr.leaves_root x hx
  · exact p.idx.leaves_root x hx

def DeltaPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {r : Nat} {ls : List Level}
    {body T : Expr Nat} (p : DeltaPayload R Γ r ls body T) :
    DeltaPayload R' Γ r ls body T where
  m := p.m
  T₀ := p.T₀
  hres := p.hres
  hbody := p.hbody
  htr := p.htr
  hlen := p.hlen
  hwf := p.hwf
  hl := p.hl.widen hr
  hr := p.hr.widen hr
  idx := p.idx.widen hr

theorem DeltaPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {r : Nat} {ls : List Level}
    {body T : Expr Nat} (p : DeltaPayload R Γ r ls body T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [DeltaPayload.widen, DeltaPayload.leaves, EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `DeltaPayload`: `ParRedT.delta` under one `conv`. -/
def deltaStep {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {body T₀ T : Expr Nat} (hres : E.members r = some m) (hbody : m.body = some body)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hl : HasTyT E n Γ (.const r ls) T₀)
    (hr : HasTyT E n Γ (instantiateLevels ls body) T₀) (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ (.const r ls) (instantiateLevels ls body) T :=
  .conv Γ (.const r ls) (instantiateLevels ls body) T₀ T
    (.delta Γ r ls m body T₀ hres hbody htr hlen hwf hl hr) idx

def DeltaPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) :
    ParRedT (PEqLeafT E n) E n Γ (.const r ls) (instantiateLevels ls body) T :=
  deltaStep p.hres p.hbody p.htr p.hlen p.hwf
    (p.hl.val hcl hinst) (p.hr.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `DeltaPayload` (`hcl`/`hinst` only, #7107). -/
def DeltaPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {body T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : DeltaPayload R Γ r ls body T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.const r ls))
      (instantiate j (lift 0 j v) (instantiateLevels ls body))
      (instantiate j (lift 0 j v) T) := by
  have hid := (hinst r p.m p.hres).2 body p.hbody ls (lift 0 j v) j
  have hl' := hasTyT_substS hcl hinst v t (p.hl.val hcl hinst) hget hv
  have hr' := hasTyT_substS hcl hinst v t (p.hr.val hcl hinst) hget hv
  have idx' := tyConvT_substS hcl hinst v t (p.idx.val hcl hinst) hget hv
  simp only [instantiate] at hl' ⊢
  rw [hid] at hr' ⊢
  exact deltaStep p.hres p.hbody p.htr p.hlen p.hwf hl' hr' idx'

def DeltaPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {body T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : DeltaPayload R Γ r ls body T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.const r ls))
      (instantiate j (lift 0 j w) (instantiateLevels ls body))
      (instantiate j (lift 0 j w) T) := by
  have hid := (hinst r p.m p.hres).2 body p.hbody ls (lift 0 j w) j
  have hl' := hasTyT_substLetS hcl hinst t w (p.hl.val hcl hinst) hget hv
  have hr' := hasTyT_substLetS hcl hinst t w (p.hr.val hcl hinst) hget hv
  have idx' := tyConvT_substLetS hcl hinst t w (p.idx.val hcl hinst) hget hv
  simp only [instantiate] at hl' ⊢
  rw [hid] at hr' ⊢
  exact deltaStep p.hres p.hbody p.htr p.hlen p.hwf hl' hr' idx'

/-- Provenance payload of `bvarZeta`: a `let`-bound variable `i` steps to `lift 0 (i + 1) v'`
    at `T₀`, re-indexed to `T` by `idx : EvTc R Γ T₀ T`. -/
structure BVarZetaPayload (R : List (Jd E n)) (Γ : LCtx) (i : Nat) (v' T : Expr Nat) where
  A : Expr Nat
  v : Expr Nat
  T₀ : Expr Nat
  h : Γ.get? i = some (.letBinding A v)
  hv : EvPar R (Γ.drop (i + 1)) v v' A
  hl : EvTy R Γ (.bvar i) T₀
  hr : EvTy R Γ (lift 0 (i + 1) v') T₀
  idx : EvTc R Γ T₀ T

def BVarZetaPayload.leaves {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : List (Jd E n) :=
  p.hv.leaves ++ p.hl.leaves ++ p.hr.leaves ++ p.idx.leaves

def BVarZetaPayload.size {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : Nat :=
  1 + p.hv.size + p.hl.size + p.hr.size + p.idx.size

theorem BVarZetaPayload.leaves_root {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [BVarZetaPayload.leaves, List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact p.hv.leaves_root x hx
  · exact p.hl.leaves_root x hx
  · exact p.hr.leaves_root x hx
  · exact p.idx.leaves_root x hx

def BVarZetaPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : BVarZetaPayload R' Γ i v' T where
  A := p.A
  v := p.v
  T₀ := p.T₀
  h := p.h
  hv := p.hv.widen hr
  hl := p.hl.widen hr
  hr := p.hr.widen hr
  idx := p.idx.widen hr

theorem BVarZetaPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {i : Nat}
    {v' T : Expr Nat} (p : BVarZetaPayload R Γ i v' T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [BVarZetaPayload.widen, BVarZetaPayload.leaves, EvPar.leaves_widen,
    EvTy.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `BVarZetaPayload`: `ParRedT.bvarZeta` under one `conv`. -/
def bvarZetaStep {Γ : LCtx} {i : Nat} {A v v' T₀ T : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v))
    (hv : ParRedT (PEqLeafT E n) E n (Γ.drop (i + 1)) v v' A)
    (hl : HasTyT E n Γ (.bvar i) T₀) (hr : HasTyT E n Γ (lift 0 (i + 1) v') T₀)
    (idx : TyConvT E n Γ T₀ T) :
    ParRedT (PEqLeafT E n) E n Γ (.bvar i) (lift 0 (i + 1) v') T :=
  .conv Γ (.bvar i) (lift 0 (i + 1) v') T₀ T
    (.bvarZeta Γ i A v v' T₀ h hv hl hr) idx

def BVarZetaPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {i : Nat} {v' T : Expr Nat} (p : BVarZetaPayload R Γ i v' T) :
    ParRedT (PEqLeafT E n) E n Γ (.bvar i) (lift 0 (i + 1) v') T :=
  bvarZetaStep p.h (p.hv.val hcl hinst)
    (p.hl.val hcl hinst) (p.hr.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `BVarZetaPayload` at `j` (`hcl`/`hinst` only, #7107). -/
def BVarZetaPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {i : Nat} {v' T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) w t)
    (p : BVarZetaPayload R Γ i v' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.bvar i))
      (instantiate j (lift 0 j w) (lift 0 (i + 1) v'))
      (instantiate j (lift 0 j w) T) := by
  have idx' := tyConvT_substS hcl hinst w t (p.idx.val hcl hinst) hget hvty
  by_cases hij : i = j
  · subst hij
    have h' : Γ[i]? = some (.letBinding p.A p.v) :=
      (List.get?_eq_getElem? Γ i).symm ▸ p.h
    rw [h'] at hget
    exact nomatch hget
  · by_cases hlt : i < j
    · simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
      have hlkV := lookupValue_of_get?_let p.h
      have hmap := lookupValue_substRemove_lt (v := w) hlt hlkV
      obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
      have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) w) = lift 0 j w := by
        have hc := lift_zero_comp (i + 1) (j - i - 1) w
        rw [show i + 1 + (j - i - 1) = j from by omega] at hc
        exact hc
      have hcomm (e : Expr Nat) :
          instantiate j (lift 0 j w) (lift 0 (i + 1) e) =
            lift 0 (i + 1) (instantiate (j - i - 1) (lift 0 (j - i - 1) w) e) := by
        have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1)
          (lift 0 (j - i - 1) w) (Nat.zero_le _) e
        rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
        exact h1.symm
      have hstored : stored = instantiate (j - i - 1) (lift 0 (j - i - 1) w) p.v :=
        lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm p.v))
      have hdrop : (substRemove w j Γ).drop (i + 1) =
          substRemove w (j - i - 1) (Γ.drop (i + 1)) := by
        rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
        congr 1
      have hgetD : (Γ.drop (i + 1))[j - i - 1]? = some (.assumption t) := by
        rw [← List.get?_eq_getElem?, get?_drop, show j - i - 1 + (i + 1) = j from by omega]
        exact (List.get?_eq_getElem? Γ j).symm ▸ hget
      have hvtD : HasTyT E n ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) w t := by
        have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) = Γ.drop (j + 1) := by
          rw [List.drop_drop]; congr 1; omega
        rw [hd]; exact hvt
      have hvtyD := subst_hvty_of_drop hcl hgetD hvtD
      have hv' := p.hv.substVal0 hcl hinst (j - i - 1) hgetD hvtyD
      rw [← hdrop] at hv'
      have hA' : A' = instantiate (j - i - 1) (lift 0 (j - i - 1) w) p.A := by
        have hsrc : lookupType Γ i = some (lift 0 (i + 1) p.A) := by simp only [lookupType, p.h]
        have hltTy := lookupType_substRemove_lt (v := w) hlt hsrc
        have hsrcTy : lookupType (substRemove w j Γ) i = some (lift 0 (i + 1) A') := by
          simp only [lookupType, hg']
        rw [hsrcTy] at hltTy
        exact lift_zero_amount_inj (i + 1) ((Option.some.inj hltTy).trans (hcomm p.A))
      rw [← hstored, ← hA'] at hv'
      have hl' := hasTyT_substS hcl hinst w t (p.hl.val hcl hinst) hget hvty
      have hr' := hasTyT_substS hcl hinst w t (p.hr.val hcl hinst) hget hvty
      simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)] at hl' hr'
      rw [hcomm v'] at hr'
      exact (hcomm v') ▸ bvarZetaStep hg' hv' hl' hr' idx'
    · have hgt : j < i := by omega
      simp only [instantiate, if_neg hij, if_pos hgt]
      have hlkV := lookupValue_of_get?_let p.h
      have hmap := lookupValue_substRemove_gt (v := w) hgt hlkV
      obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
      have hcan (e : Expr Nat) :
          instantiate j (lift 0 j w) (lift 0 (i + 1) e) = lift 0 i e :=
        instantiate_lift_cancel (i + 1) 0 j (lift 0 j w) (Nat.zero_le j) (by omega) e
      have hi1 : i - 1 + 1 = i := by omega
      have hstored : stored = p.v := by
        have heq' : lift 0 i stored = lift 0 i p.v := by
          have h1 := heq.symm.trans (hcan p.v); rwa [hi1] at h1
        exact lift_zero_amount_inj i heq'
      have hA' : A' = p.A := by
        have hsrc : lookupType Γ i = some (lift 0 (i + 1) p.A) := by simp only [lookupType, p.h]
        have hltTy := lookupType_substRemove_gt (v := w) hgt hsrc
        have hsrcTy : lookupType (substRemove w j Γ) (i - 1) =
            some (lift 0 ((i - 1) + 1) A') := by simp only [lookupType, hg']
        rw [hsrcTy] at hltTy
        have heq' : lift 0 i A' = lift 0 i p.A := by
          have h1 := (Option.some.inj hltTy).trans (hcan p.A); rwa [hi1] at h1
        exact lift_zero_amount_inj i heq'
      have hdrop : (substRemove w j Γ).drop i = Γ.drop (i + 1) := by
        rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
      have hv' : ParRedT (PEqLeafT E n) E n
          ((substRemove w j Γ).drop (i - 1 + 1)) p.v v' p.A := by
        rw [hi1]; exact hdrop ▸ (p.hv.val hcl hinst)
      have hl' := hasTyT_substS hcl hinst w t (p.hl.val hcl hinst) hget hvty
      have hr' := hasTyT_substS hcl hinst w t (p.hr.val hcl hinst) hget hvty
      simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr'
      rw [hcan v'] at hr'
      have hr'' : HasTyT E n (substRemove w j Γ)
          (lift 0 (i - 1 + 1) v') (instantiate j (lift 0 j w) p.T₀) := by
        rw [hi1]; exact hr'
      have htgt : lift 0 i v' = instantiate j (lift 0 j w) (lift 0 (i + 1) v') :=
        (hcan v').symm
      rw [← hstored, ← hA'] at hv'
      exact htgt ▸ (hi1 ▸ bvarZetaStep hg' hv' hl' hr'' idx')

/-- Provenance payload of `lam`: domain converts at `.sort u`, body steps in `.assumption A :: Γ`
    at `B`, re-indexed from `.pi A B` to `T` by `idx : EvTc R Γ (.pi A B) T`. -/
structure LamPayload (R : List (Jd E n)) (Γ : LCtx) (A body A' body' T : Expr Nat) where
  B : Expr Nat
  u : Level
  v : Level
  hc : EvCv R Γ A A' (.sort u)
  hA : EvTy R Γ A (.sort u)
  hB : EvTy R (.assumption A :: Γ) B (.sort v)
  hb : EvPar R (.assumption A :: Γ) body body' B
  hrt : EvTy R Γ (.lam A' body') (.pi A B)
  idx : EvTc R Γ (.pi A B) T

def LamPayload.leaves {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : List (Jd E n) :=
  p.hc.leaves ++ p.hA.leaves ++ p.hB.leaves ++ p.hb.leaves ++ p.hrt.leaves ++ p.idx.leaves

def LamPayload.size {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : Nat :=
  1 + p.hc.size + p.hA.size + p.hB.size + p.hb.size + p.hrt.size + p.idx.size

theorem LamPayload.leaves_root {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [LamPayload.leaves, List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · exact p.hc.leaves_root x hx
  · exact p.hA.leaves_root x hx
  · exact p.hB.leaves_root x hx
  · exact p.hb.leaves_root x hx
  · exact p.hrt.leaves_root x hx
  · exact p.idx.leaves_root x hx

def LamPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : LamPayload R' Γ A body A' body' T where
  B := p.B
  u := p.u
  v := p.v
  hc := p.hc.widen hr
  hA := p.hA.widen hr
  hB := p.hB.widen hr
  hb := p.hb.widen hr
  hrt := p.hrt.widen hr
  idx := p.idx.widen hr

theorem LamPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx}
    {A body A' body' T : Expr Nat} (p : LamPayload R Γ A body A' body' T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [LamPayload.widen, LamPayload.leaves, EvCv.leaves_widen, EvTy.leaves_widen,
    EvPar.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `LamPayload`: `ParRedT.lam` under one `conv`. -/
def lamStep {Γ : LCtx} {A A' body body' B T : Expr Nat} {u v : Level}
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hb : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) body body' B)
    (hrt : HasTyT E n Γ (.lam A' body') (.pi A B))
    (idx : TyConvT E n Γ (.pi A B) T) :
    ParRedT (PEqLeafT E n) E n Γ (.lam A body) (.lam A' body') T :=
  .conv Γ (.lam A body) (.lam A' body') (.pi A B) T
    (.lam Γ A A' body body' B u v hc hA hB hb hrt) idx

def LamPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) :
    ParRedT (PEqLeafT E n) E n Γ (.lam A body) (.lam A' body') T :=
  lamStep (p.hc.val hcl hinst) (p.hA.val hcl hinst) (p.hB.val hcl hinst)
    (p.hb.val hcl hinst) (p.hrt.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `LamPayload` (`hcl`/`hinst` only, #7107). -/
def LamPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A body A' body' T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : LamPayload R Γ A body A' body' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.lam A body))
      (instantiate j (lift 0 j w) (.lam A' body'))
      (instantiate j (lift 0 j w) T) := by
  have hget' := subst_arg_get_succ (.assumption A) hget
  have hv' := subst_hvty_wk (.assumption A) hcl hv
  have hc' := convT_substS hcl hinst w t (p.hc.val hcl hinst) hget hv
  have hA' := hasTyT_substS hcl hinst w t (p.hA.val hcl hinst) hget hv
  have hB' := hasTyT_substS hcl hinst w t (p.hB.val hcl hinst) hget' hv'
  have hb' := p.hb.substVal0 hcl hinst (j + 1) hget' hv'
  have hrt' := hasTyT_substS hcl hinst w t (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substS hcl hinst w t (p.idx.val hcl hinst) hget hv
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hb' hrt' idx' ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w] at hrt' idx' ⊢
  exact lamStep hc' hA' hB' hb' hrt' idx'

def LamPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A body A' body' T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (p : LamPayload R Γ A body A' body' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.lam A body))
      (instantiate j (lift 0 j w) (.lam A' body'))
      (instantiate j (lift 0 j w) T) := by
  have hget' := substLet_get_succ (.assumption A) hget
  have hv' := subst_hvty_wk (.assumption A) hcl hv
  have hc' := convT_substLetS hcl hinst t w (p.hc.val hcl hinst) hget hv
  have hA' := hasTyT_substLetS hcl hinst t w (p.hA.val hcl hinst) hget hv
  have hB' := hasTyT_substLetS hcl hinst t w (p.hB.val hcl hinst) hget' hv'
  have hb' := p.hb.substLetVal0 hcl hinst (j + 1) hget' hv'
  have hrt' := hasTyT_substLetS hcl hinst t w (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substLetS hcl hinst t w (p.idx.val hcl hinst) hget hv
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hb' hrt' idx' ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w] at hrt' idx' ⊢
  exact lamStep hc' hA' hB' hb' hrt' idx'

/-- Provenance payload of `app`: carries `hPi : EvTy R Γ (.pi A B) (.sort (.imax u v))`
    per #7107 rule 3 so substitution and diamond inversion need no regularity `hS`. -/
structure AppPayload (R : List (Jd E n)) (Γ : LCtx) (f a f' a' T : Expr Nat) where
  T₀ : Expr Nat
  A : Expr Nat
  B : Expr Nat
  u : Level
  v : Level
  w : Level
  hf : EvPar R Γ f f' T₀
  hc : EvTc R Γ T₀ (.pi A B)
  hPi : EvTy R Γ (.pi A B) (.sort (.imax u v))
  hB : EvTy R (.assumption A :: Γ) B (.sort v)
  hTy : EvTy R Γ (instantiate0 a B) (.sort w)
  ha : EvPar R Γ a a' A
  hr : EvTy R Γ (.app f' a') (instantiate0 a B)
  idx : EvTc R Γ (instantiate0 a B) T

def AppPayload.leaves {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : List (Jd E n) :=
  p.hf.leaves ++ p.hc.leaves ++ p.hPi.leaves ++ p.hB.leaves ++
    p.hTy.leaves ++ p.ha.leaves ++ p.hr.leaves ++ p.idx.leaves

def AppPayload.size {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : Nat :=
  1 + p.hf.size + p.hc.size + p.hPi.size + p.hB.size +
    p.hTy.size + p.ha.size + p.hr.size + p.idx.size

theorem AppPayload.leaves_root {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [AppPayload.leaves, List.mem_append] at hx
  rcases hx with ((((((hx | hx) | hx) | hx) | hx) | hx) | hx) | hx
  · exact p.hf.leaves_root x hx
  · exact p.hc.leaves_root x hx
  · exact p.hPi.leaves_root x hx
  · exact p.hB.leaves_root x hx
  · exact p.hTy.leaves_root x hx
  · exact p.ha.leaves_root x hx
  · exact p.hr.leaves_root x hx
  · exact p.idx.leaves_root x hx

def AppPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : AppPayload R' Γ f a f' a' T where
  T₀ := p.T₀
  A := p.A
  B := p.B
  u := p.u
  v := p.v
  w := p.w
  hf := p.hf.widen hr
  hc := p.hc.widen hr
  hPi := p.hPi.widen hr
  hB := p.hB.widen hr
  hTy := p.hTy.widen hr
  ha := p.ha.widen hr
  hr := p.hr.widen hr
  idx := p.idx.widen hr

theorem AppPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : (p.widen hr).leaves = p.leaves := by
  simp only [AppPayload.widen, AppPayload.leaves, EvPar.leaves_widen, EvTc.leaves_widen,
    EvTy.leaves_widen]

/-- Plain step output of `AppPayload`: `ParRedT.app` under one `conv`. -/
def appStep {Γ : LCtx} {f f' a a' A B T₀ T : Expr Nat} {v w : Level}
    (hf : ParRedT (PEqLeafT E n) E n Γ f f' T₀)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (ha : ParRedT (PEqLeafT E n) E n Γ a a' A)
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 a B))
    (idx : TyConvT E n Γ (instantiate0 a B) T) :
    ParRedT (PEqLeafT E n) E n Γ (.app f a) (.app f' a') T :=
  .conv Γ (.app f a) (.app f' a') (instantiate0 a B) T
    (.app Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) idx

def AppPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f a f' a' T : Expr Nat} (p : AppPayload R Γ f a f' a' T) :
    ParRedT (PEqLeafT E n) E n Γ (.app f a) (.app f' a') T :=
  appStep (p.hf.val hcl hinst) (p.hc.val hcl hinst) (p.hB.val hcl hinst)
    (p.hTy.val hcl hinst) (p.ha.val hcl hinst) (p.hr.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `AppPayload` (`hcl`/`hinst` only, zero `hS`, #7107). -/
def AppPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f a f' a' T t w₀ : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove w₀ j Γ) (lift 0 j w₀) (lift 0 j t))
    (p : AppPayload R Γ f a f' a' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w₀ j Γ)
      (instantiate j (lift 0 j w₀) (.app f a))
      (instantiate j (lift 0 j w₀) (.app f' a'))
      (instantiate j (lift 0 j w₀) T) := by
  have hget' := subst_arg_get_succ (.assumption p.A) hget
  have hv' := subst_hvty_wk (.assumption p.A) hcl hv
  have hf' := p.hf.substVal0 hcl hinst j hget hv
  have ha' := p.ha.substVal0 hcl hinst j hget hv
  have hc' := tyConvT_substS hcl hinst w₀ t (p.hc.val hcl hinst) hget hv
  have hB' := hasTyT_substS hcl hinst w₀ t (p.hB.val hcl hinst) hget' hv'
  have hTy' := hasTyT_substS hcl hinst w₀ t (p.hTy.val hcl hinst) hget hv
  have hr' := hasTyT_substS hcl hinst w₀ t (p.hr.val hcl hinst) hget hv
  have idx' := tyConvT_substS hcl hinst w₀ t (p.idx.val hcl hinst) hget hv
  have hcomm : instantiate j (lift 0 j w₀) (instantiate0 a p.B) =
      instantiate0 (instantiate j (lift 0 j w₀) a)
        (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) p.B) := by
    unfold instantiate0
    exact instantiate_instantiate 0 j a (lift 0 j w₀) (Nat.zero_le j) p.B
  simp only [instantiate, substRemove_succ_cons, instDecl] at hc' hB' hTy' hr' idx' ⊢
  rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hTy' hr' idx'
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hc'
  exact appStep hf' hc' hB' hTy' ha' hr' idx'

def AppPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f a f' a' T t w₀ : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w₀))
    (hv : HasTyT E n (substRemove w₀ j Γ) (lift 0 j w₀) (lift 0 j t))
    (p : AppPayload R Γ f a f' a' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w₀ j Γ)
      (instantiate j (lift 0 j w₀) (.app f a))
      (instantiate j (lift 0 j w₀) (.app f' a'))
      (instantiate j (lift 0 j w₀) T) := by
  have hget' := substLet_get_succ (.assumption p.A) hget
  have hv' := subst_hvty_wk (.assumption p.A) hcl hv
  have hf' := p.hf.substLetVal0 hcl hinst j hget hv
  have ha' := p.ha.substLetVal0 hcl hinst j hget hv
  have hc' := tyConvT_substLetS hcl hinst t w₀ (p.hc.val hcl hinst) hget hv
  have hB' := hasTyT_substLetS hcl hinst t w₀ (p.hB.val hcl hinst) hget' hv'
  have hTy' := hasTyT_substLetS hcl hinst t w₀ (p.hTy.val hcl hinst) hget hv
  have hr' := hasTyT_substLetS hcl hinst t w₀ (p.hr.val hcl hinst) hget hv
  have idx' := tyConvT_substLetS hcl hinst t w₀ (p.idx.val hcl hinst) hget hv
  have hcomm : instantiate j (lift 0 j w₀) (instantiate0 a p.B) =
      instantiate0 (instantiate j (lift 0 j w₀) a)
        (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) p.B) := by
    unfold instantiate0
    exact instantiate_instantiate 0 j a (lift 0 j w₀) (Nat.zero_le j) p.B
  simp only [instantiate, substRemove_succ_cons, instDecl] at hc' hB' hTy' hr' idx' ⊢
  rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hTy' hr' idx'
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hc'
  exact appStep hf' hc' hB' hTy' ha' hr' idx'

/-- Provenance payload of `letE`: domain converts at `.sort u`, value steps at `A`,
    body steps in `.letBinding A value :: Γ` at `B`, re-indexed from `instantiate0 value B`
    to `T` by `idx : EvTc R Γ (instantiate0 value B) T`. -/
structure LetEPayload (R : List (Jd E n)) (Γ : LCtx)
    (A value body A' value' body' T : Expr Nat) where
  B : Expr Nat
  u : Level
  w : Level
  hc : EvCv R Γ A A' (.sort u)
  hA : EvTy R Γ A (.sort u)
  hv : EvPar R Γ value value' A
  hB : EvTy R (.letBinding A value :: Γ) B (.sort w)
  hTy : EvTy R Γ (instantiate0 value B) (.sort w)
  hb : EvPar R (.letBinding A value :: Γ) body body' B
  hrt : EvTy R Γ (.letE A' value' body') (instantiate0 value B)
  idx : EvTc R Γ (instantiate0 value B) T

def LetEPayload.leaves {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) : List (Jd E n) :=
  p.hc.leaves ++ p.hA.leaves ++ p.hv.leaves ++ p.hB.leaves ++
    p.hTy.leaves ++ p.hb.leaves ++ p.hrt.leaves ++ p.idx.leaves

def LetEPayload.size {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) : Nat :=
  1 + p.hc.size + p.hA.size + p.hv.size + p.hB.size +
    p.hTy.size + p.hb.size + p.hrt.size + p.idx.size

theorem LetEPayload.leaves_root {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) (x : Jd E n) (hx : x ∈ p.leaves) :
    ∃ r₀ ∈ R, SubEq x r₀ := by
  simp only [LetEPayload.leaves, List.mem_append] at hx
  rcases hx with ((((((hx | hx) | hx) | hx) | hx) | hx) | hx) | hx
  · exact p.hc.leaves_root x hx
  · exact p.hA.leaves_root x hx
  · exact p.hv.leaves_root x hx
  · exact p.hB.leaves_root x hx
  · exact p.hTy.leaves_root x hx
  · exact p.hb.leaves_root x hx
  · exact p.hrt.leaves_root x hx
  · exact p.idx.leaves_root x hx

def LetEPayload.widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    LetEPayload R' Γ A value body A' value' body' T where
  B := p.B
  u := p.u
  w := p.w
  hc := p.hc.widen hr
  hA := p.hA.widen hr
  hv := p.hv.widen hr
  hB := p.hB.widen hr
  hTy := p.hTy.widen hr
  hb := p.hb.widen hr
  hrt := p.hrt.widen hr
  idx := p.idx.widen hr

theorem LetEPayload.leaves_widen (hr : ∀ x ∈ R, x ∈ R') {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [LetEPayload.widen, LetEPayload.leaves, EvCv.leaves_widen, EvTy.leaves_widen,
    EvPar.leaves_widen, EvTc.leaves_widen]

/-- Plain step output of `LetEPayload`: `ParRedT.letE` under one `conv`. -/
def letEStep {Γ : LCtx} {A A' value value' body body' B T : Expr Nat} {u w : Level}
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hv : ParRedT (PEqLeafT E n) E n Γ value value' A)
    (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
    (hb : ParRedT (PEqLeafT E n) E n (.letBinding A value :: Γ) body body' B)
    (hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B))
    (idx : TyConvT E n Γ (instantiate0 value B) T) :
    ParRedT (PEqLeafT E n) E n Γ (.letE A value body) (.letE A' value' body') T :=
  .conv Γ (.letE A value body) (.letE A' value' body') (instantiate0 value B) T
    (.letE Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt) idx

def LetEPayload.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    ParRedT (PEqLeafT E n) E n Γ (.letE A value body) (.letE A' value' body') T :=
  letEStep (p.hc.val hcl hinst) (p.hA.val hcl hinst) (p.hv.val hcl hinst)
    (p.hB.val hcl hinst) (p.hTy.val hcl hinst) (p.hb.val hcl hinst)
    (p.hrt.val hcl hinst) (p.idx.val hcl hinst)

/-- Substituted materializer for `LetEPayload` (`hcl`/`hinst` only, #7107). -/
def LetEPayload.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value body A' value' body' T t w₀ : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove w₀ j Γ) (lift 0 j w₀) (lift 0 j t))
    (p : LetEPayload R Γ A value body A' value' body' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w₀ j Γ)
      (instantiate j (lift 0 j w₀) (.letE A value body))
      (instantiate j (lift 0 j w₀) (.letE A' value' body'))
      (instantiate j (lift 0 j w₀) T) := by
  have hget' := subst_arg_get_succ (.letBinding A value) hget
  have hv' := subst_hvty_wk (.letBinding A value) hcl hv
  have hc' := convT_substS hcl hinst w₀ t (p.hc.val hcl hinst) hget hv
  have hA' := hasTyT_substS hcl hinst w₀ t (p.hA.val hcl hinst) hget hv
  have hvStep := p.hv.substVal0 hcl hinst j hget hv
  have hB' := hasTyT_substS hcl hinst w₀ t (p.hB.val hcl hinst) hget' hv'
  have hTy' := hasTyT_substS hcl hinst w₀ t (p.hTy.val hcl hinst) hget hv
  have hb' := p.hb.substVal0 hcl hinst (j + 1) hget' hv'
  have hrt' := hasTyT_substS hcl hinst w₀ t (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substS hcl hinst w₀ t (p.idx.val hcl hinst) hget hv
  have hcomm : instantiate j (lift 0 j w₀) (instantiate0 value p.B) =
      instantiate0 (instantiate j (lift 0 j w₀) value)
        (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) p.B) := by
    unfold instantiate0
    exact instantiate_instantiate 0 j value (lift 0 j w₀) (Nat.zero_le j) p.B
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hTy' hb' hrt' idx' ⊢
  rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hTy' hrt' idx'
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀]
  exact letEStep hc' hA' hvStep hB' hTy' hb' hrt' idx'

def LetEPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value body A' value' body' T t w₀ : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w₀))
    (hv : HasTyT E n (substRemove w₀ j Γ) (lift 0 j w₀) (lift 0 j t))
    (p : LetEPayload R Γ A value body A' value' body' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w₀ j Γ)
      (instantiate j (lift 0 j w₀) (.letE A value body))
      (instantiate j (lift 0 j w₀) (.letE A' value' body'))
      (instantiate j (lift 0 j w₀) T) := by
  have hget' := substLet_get_succ (.letBinding A value) hget
  have hv' := subst_hvty_wk (.letBinding A value) hcl hv
  have hc' := convT_substLetS hcl hinst t w₀ (p.hc.val hcl hinst) hget hv
  have hA' := hasTyT_substLetS hcl hinst t w₀ (p.hA.val hcl hinst) hget hv
  have hvStep := p.hv.substLetVal0 hcl hinst j hget hv
  have hB' := hasTyT_substLetS hcl hinst t w₀ (p.hB.val hcl hinst) hget' hv'
  have hTy' := hasTyT_substLetS hcl hinst t w₀ (p.hTy.val hcl hinst) hget hv
  have hb' := p.hb.substLetVal0 hcl hinst (j + 1) hget' hv'
  have hrt' := hasTyT_substLetS hcl hinst t w₀ (p.hrt.val hcl hinst) hget hv
  have idx' := tyConvT_substLetS hcl hinst t w₀ (p.idx.val hcl hinst) hget hv
  have hcomm : instantiate j (lift 0 j w₀) (instantiate0 value p.B) =
      instantiate0 (instantiate j (lift 0 j w₀) value)
        (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) p.B) := by
    unfold instantiate0
    exact instantiate_instantiate 0 j value (lift 0 j w₀) (Nat.zero_le j) p.B
  simp only [instantiate, substRemove_succ_cons, instDecl] at hB' hTy' hb' hrt' idx' ⊢
  rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀] at hTy' hrt' idx'
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w₀]
  exact letEStep hc' hA' hvStep hB' hTy' hb' hrt' idx'

/-- Leaf-less `EvPar` producer for `ConvT.sorts` (`leaves = []`, W-X-LEVELS). -/
def EvPar.ofSorts (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    EvPar R Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) :=
  .sortEq (.ofSorts Γ l₁ l₂ h)

theorem EvPar.ofSorts_leaves (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    (EvPar.ofSorts (R := R) Γ l₁ l₂ h).leaves = [] := rfl

/-- `EvPar` producer for `ConvT.consts` (`leaves = tc.leaves`, W-X-LEVELS). -/
def EvPar.ofConstsWith (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    EvPar R Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) :=
  .consts (.ofConstsWith Γ r ls ls' m hres hlen hwf hwf' heq tc)

theorem EvPar.ofConstsWith_leaves (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    (EvPar.ofConstsWith (R := R) Γ r ls ls' m hres hlen hwf hwf' heq tc).leaves = tc.leaves :=
  ConstsPayload.ofConstsWith_leaves Γ r ls ls' m hres hlen hwf hwf' heq tc

/-- Widening transports the original lazy chain, rather than making new atoms. -/
theorem EvPar.proofIndex_lazy_widen (hr : ∀ x ∈ R, x ∈ R')
    {Γ : LCtx} {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) (side : Side) :
    EvPar.proofIndexLazyAnswer (p.widen hr) side =
      (EvPar.proofIndexLazyAnswer p side).widen hr := rfl

theorem EvPar.proofIndex_answer_widen (hr : ∀ x ∈ R, x ∈ R')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) (side : Side) :
    HEq (EvPar.proofIndexAnswers hcl hinst (p.widen hr) PUnit.unit side)
      (EvPar.proofIndexAnswers hcl hinst p PUnit.unit side) := by
  cases side <;> exact heq_of_eq (evTcVal_widen hr hcl hinst p.chain)

section LiteralIrr
variable {Γ : LCtx} {P p q : Expr Nat}

/-- The J(irr) base case, with no U callback and no reconstructed endpoint. -/
def literalIrrProducer (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    EvPar [Jd.cv (.irr Γ P p q hP hp hq)] Γ p q P :=
  .proofIndex (literalIrrPayload hP hp hq)

theorem literalIrrProducer_val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (literalIrrProducer hP hp hq).val hcl hinst =
      ParRedT.peq Γ p q P (peqLeafT_reconcile_propIndex hP (.refl Γ P) hp hq).1 := rfl

theorem literalIrrProducer_leaves (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (literalIrrProducer hP hp hq).leaves = [Jd.ty hP, Jd.ty hp, Jd.ty hq] := rfl

theorem literalIrrProducer_dm (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    Rcic.Syn.DMStep ((literalIrrProducer hP hp hq).leaves.map Jd.wt)
      ([Jd.cv (.irr Γ P p q hP hp hq)].map Jd.wt) :=
  literalIrrPayload_dm hP hp hq

/-- The same actual root replacement, with an untouched surrounding bundle. -/
theorem literalIrrProducer_dm_frame (Z : List (Jd E n))
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    Rcic.Syn.DMStep ((literalIrrProducer hP hp hq).leaves.map Jd.wt ++ Z.map Jd.wt)
      ([Jd.cv (.irr Γ P p q hP hp hq)].map Jd.wt ++ Z.map Jd.wt) :=
  dm_of_strictLeaves (X := [Jd.cv (.irr Γ P p q hP hp hq)])
    (Z := Z) (L := (literalIrrProducer hP hp hq).leaves)
    (List.cons_ne_nil _ _) (fun x hx =>
      ⟨_, .head _, literalIrrPayload_strict hP hp hq x hx⟩)

theorem literalIrrProducer_answer_refl (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) (side : Side) :
    EvPar.proofIndexLazyAnswer (literalIrrPayload hP hp hq) side = EvTc.refl Γ P := rfl

theorem literalIrrProducer_answer_leaves (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) (side : Side) :
    (EvPar.proofIndexLazyAnswer (literalIrrPayload hP hp hq) side).leaves = [] := rfl

/-- The old producer's accompanying ConvT is the original irr itself. -/
theorem literalIrrProducer_conv_exact (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (peqLeafT_reconcile_propIndex hP (.refl Γ P) hp hq).2 =
      ConvT.irr Γ P p q hP hp hq := by
  simp [peqLeafT_reconcile_propIndex, convT_of_tyConv, TyConvT.symmT, hasTyT_of_tyConvT]
end LiteralIrr
end Rcic.Declarative.F8Measure
