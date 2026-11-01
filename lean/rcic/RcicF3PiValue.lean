import rcic.RcicF3PiIndex
/-! Actual Prop-valued family tables indexed by extensional argument lists.
Fitting application, full family-type membership and the complete proof face
are proved for the constructed value. Admitted raw-field transport retains
ordinary environment/body obligations; no raw group model or universal A
producer is claimed. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiValue
open Rcic.Declarative PiIndex
universe u

def endValue (φ : Index.{u} → Prop) (q : Nat) (ρ : Nat → PSet.{u}) : PSet.{u} :=
  tyv (fibre φ (lastVals q ρ))

theorem endValue_resp (φ : Index.{u} → Prop) (q : Nat) : EnvResp (endValue φ q) := by
  intro ρ ρ' h
  unfold endValue
  rw [fibre_congr φ (lastVals_congr q h)]
  exact Equiv.rfl

def value (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) : PSet.{u} :=
  piLam M σ (endValue φ ds.length) ρ (policyPi ds (.sort .zero))

theorem endValue_empty (M : Interp.{u}) (φ : Index.{u} → Prop) (q : Nat)
    (ρ : Nat → PSet.{u}) {z : PSet.{u}} (hz : z ∈ Ed M (endValue φ q ρ)) :
    Equiv z pempty := by
  exact (mem_tv.mp (mem_congr_right (ed_tyv M
    (dich_tv (φ (key (lastVals q ρ))))) hz)).2

/-- Proof erasure is derived at every complete spine, including invalid arguments. -/
theorem complete_empty (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hl : xs.length = ds.length) {z : PSet.{u}}
    (hz : z ∈ Ed M (fapps (value M σ φ ds ρ) xs)) : Equiv z pempty := by
  exact PiPropField.application_empty M σ _ (endValue_resp φ ds.length)
    (fun ρ z hz => endValue_empty M φ ds.length ρ hz) ds ρ xs hl hz

/-- At fitting complete arguments, the value computes to the exact quotient fibre. -/
theorem apply_value (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hx : TelFits M σ ds ρ xs) :
    Equiv (fapps (value M σ φ ds ρ) xs) (tyv (fibre φ xs)) := by
  have he := fapps_piLam M σ (endValue_resp φ ds.length) (.sort .zero) ds ρ xs hx
  change Equiv (fapps (value M σ φ ds ρ) xs)
    (tyv (fibre φ (lastVals ds.length (push xs ρ)))) at he
  rw [← hx.length, lastVals_push] at he
  exact he

/-- Elementary composition: exact element set at complete fitting arguments; invalid arguments are not assumed fitting. -/
theorem apply_ed (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hx : TelFits M σ ds ρ xs) :
    Equiv (Ed M (fapps (value M σ φ ds ρ) xs)) (fibre φ xs) := by
  exact (ed_congr M (apply_value M σ φ ds ρ xs hx)).trans
    (ed_tyv M (dich_tv (φ (key xs))))

/-- The actual value inhabits its entire declared Prop-valued family type. -/
theorem value_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (φ : Index.{4} → Prop) (ds : List (Expr Nat))
    (ρ : Nat → PSet.{4}) :
    value (mkM P μ) σ φ ds ρ ∈
      Ed (mkM P μ) (den (mkM P μ) σ ρ (policyPi ds (.sort .zero))) := by
  refine piLam_mem (mkM P μ) σ (endValue_resp φ ds.length) _ ρ ?_
  apply piGood_policyPi
  intro ρ'
  change tyv (fibre φ (lastVals ds.length ρ')) ∈ Ed (mkM P μ) (tyv (U W4 0))
  apply mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm
  exact (mem_sImage_tyv).mpr ⟨_, mem_propSets.mpr (fun _ h => (mem_tv.mp h).2),
    Equiv.rfl⟩

/-- Clean family binder domains make the entire value independent of its own table entry. -/
theorem value_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (φ : Index.{4} → Prop)
    (ds : List (Expr Nat)) (h : ∀ A ∈ ds, occursConst f A = false)
    (ρ : Nat → PSet.{4}) :
    value (mkM P (upd μ f X₁)) σ φ ds ρ =
      value (mkM P (upd μ f X₂)) σ φ ds ρ := by
  have clean : ∀ ts : List (Expr Nat), (∀ A ∈ ts, occursConst f A = false) →
      occursConst f (policyPi ts (.sort .zero)) = false := by
    intro ts
    induction ts with
    | nil => intro _; rfl
    | cons A ts ih =>
      intro ht
      change (occursConst f A || occursConst f (policyPi ts (.sort .zero))) = false
      rw [ht A (List.mem_cons_self _ _), ih (fun B hB => ht B (List.mem_cons_of_mem _ hB))]
      rfl
  have hf := clean ds h
  unfold value
  rw [mkM_eq_withμ, mkM_eq_withμ]
  apply piLam_agree
  intro r hr ls
  have hrn : r ≠ f := by
    intro he
    subst r
    have ht := (PiIndependent.expr_refs f _).mp hr
    rw [hf] at ht
    cases ht
  rw [upd_ne μ f X₁ hrn, upd_ne μ f X₂ hrn]

/-- Exact complete-application membership also recovers fitting arguments. -/
theorem apply_mem_iff (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hl : xs.length = ds.length) (z : PSet.{u}) :
    z ∈ Ed M (fapps (value M σ φ ds ρ) xs) ↔
      TelFits M σ ds ρ xs ∧ φ (key xs) ∧ Equiv z pempty := by
  constructor
  · intro hz
    have hn : ¬ Equiv (fapps (value M σ φ ds ρ) xs) pempty := by
      intro he
      exact not_mem_pempty (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hz)
    have hx := fits_of_fapps_ne M σ (endValue_resp φ ds.length) (.sort .zero)
      ds ρ xs hl hn
    exact ⟨hx, mem_tv.mp (mem_congr_right (apply_ed M σ φ ds ρ xs hx) hz)⟩
  · rintro ⟨hx, hφ, hz⟩
    exact mem_congr_right (apply_ed M σ φ ds ρ xs hx).symm (mem_tv.mpr ⟨hφ, hz⟩)

def table (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (φ : List Nat → Index.{4} → Prop) (ds : List (Expr Nat)) :
    List Nat → PSet.{4} := fun vs => value (mkM P μ) (σOf vs) (φ vs) ds ρ0

/-- The normalized recursive-field comparison derives its complete proof face
from the constructed family value. No proof-face wall is supplied. -/
theorem recursiveField_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (σ : Nat → Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false)
    (hl : args.length = famDs.length) (ρ : Nat → PSet.{4}) :
    let X := table P μ φ famDs
    let M := mkM P (upd μ f X)
    Equiv (Ed M ((PiIndex.tel (mkM P μ) σ ds args ρ).erasedType
      M (proofFibre M (X (ls.map (evalTotal σ))))))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) := by
  exact PiIndex.recursiveField_ed P μ f (table P μ φ famDs) σ ls ds args hd ha
    (fun xs hx z hz => complete_empty (mkM P μ) (σOf (ls.map (evalTotal σ)))
      (φ (ls.map (evalTotal σ))) famDs ρ0 xs (hx.trans hl) hz) ρ

/-- Elementary admission composition using the constructed family table.
Only ordinary environment/body obligations remain; the proof face is internal. -/
theorem admitted_field (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat)) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) (hI : InstOK E σ K T)
    (hfamily : famDs.length = np + ni)
    (hE : EnvSound (mkM P (upd μ f (table P μ φ famDs))) σ K E n)
    (hb : BodiesOK E σ K) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      (∀ X₁ X₂ ρ, PiIndex.tel (mkM P (upd μ f X₁)) σ ds args ρ =
        PiIndex.tel (mkM P (upd μ f X₂)) σ ds args ρ) ∧
      ∀ ρ x, x ∈ Ed (mkM P (upd μ f (table P μ φ famDs)))
        (den (mkM P (upd μ f (table P μ φ famDs))) σ ρ T) →
      x ∈ Ed (mkM P (upd μ f (table P μ φ famDs)))
        ((PiIndex.tel (mkM P μ) σ ds args ρ).erasedType
          (mkM P (upd μ f (table P μ φ famDs)))
          (proofFibre (mkM P (upd μ f (table P μ φ famDs)))
            (table P μ φ famDs (((List.range nu).map Level.param).map (evalTotal σ))))) := by
  obtain ⟨ds, args, hl, ha, hf, hm⟩ := PiIndex.admitted_field P μ σ K h hscope hI
  refine ⟨ds, args, hl, ha, hf, ?_⟩
  exact hm (table P μ φ famDs) hE hb
    (fun xs hx z hz => complete_empty (mkM P μ)
      (σOf (((List.range nu).map Level.param).map (evalTotal σ)))
      (φ (((List.range nu).map Level.param).map (evalTotal σ))) famDs ρ0 xs
      (hx.trans hfamily.symm) hz)

/-- The family member's soundness follows from the actual value-type proof.
The closed-level facts are the ordinary member facts; no constructor closure
or complete proof-face premise occurs here. -/
theorem member_sound (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) (f : Nat) (m : CheckedMember)
    (φ : List Nat → Index.{4} → Prop) (ds : List (Expr Nat))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hlevels : exprLevelsBounded m.arity m.mtype = true)
    (ht : m.mtype = policyPi ds (.sort .zero)) (hbody : m.body = none)
    (hval : ∀ vs, Equiv (μ f vs) (value (mkM P μ) (σOf vs) (φ vs) ds ρ0)) :
    MemberSound P μ K f m := by
  intro σ ls ρ hlen _
  refine ⟨?_, ?_⟩
  · rw [den_inst_canon (mkM P μ) σ ls ρ m.mtype hcl (hlen ▸ hlevels), ht]
    exact mem_congr_left (hval (ls.map (evalTotal σ))).symm
      (value_mem P μ (σOf (ls.map (evalTotal σ))) (φ (ls.map (evalTotal σ))) ds ρ0)
  · intro b hb
    rw [hbody] at hb
    cases hb

end Rcic.F3.PSet.PiValue
