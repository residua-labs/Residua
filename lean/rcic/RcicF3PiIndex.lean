import rcic.RcicF3PiPropPrefix
/-! Extensional quotient indices for proof-valued recursive signatures.
Complete applications descend without representative choice; successful
admission supplies candidate-independent normalized telescopes. Raw
group assembly and reverse normalization remain unpaid. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndex
open Rcic.Declarative
universe u

def argumentSetoid : Setoid (List PSet.{u}) where
  r := LEq
  iseqv := ⟨LEq.refl, LEq.symm, LEq.trans⟩
abbrev Index := Quotient argumentSetoid.{u}
def key (xs : List PSet.{u}) : Index.{u} := Quotient.mk _ xs

theorem key_eq_iff (xs ys : List PSet.{u}) : key xs = key ys ↔ LEq xs ys := by
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

def arity : Index.{u} → Nat :=
  Quotient.lift List.length (fun _ _ h => LEq.length h)

/-- Elementary computation: the quotient retains the entire argument list. -/
theorem arity_key (xs : List PSet.{u}) : arity (key xs) = xs.length := by
  rfl

def fibre (φ : Index.{u} → Prop) (xs : List PSet.{u}) : PSet.{u} := tv (φ (key xs))

/-- Equivalent raw lists have the same proof fibre, with no representative choice. -/
theorem fibre_congr (φ : Index.{u} → Prop) {xs ys : List PSet.{u}} (h : LEq xs ys) :
    fibre φ xs = fibre φ ys := by
  unfold fibre
  rw [(key_eq_iff xs ys).mpr h]

def read (M : Interp.{u}) (σ : Nat → Nat) (es : List (Expr Nat))
    (ρ : Nat → PSet.{u}) : Index.{u} := key (es.map (den M σ ρ))

/-- Reading an index list is extensional in the entire dependent context. -/
theorem read_congr (M : Interp.{u}) (σ : Nat → Nat) (es : List (Expr Nat))
    {ρ ρ' : Nat → PSet.{u}} (h : ∀ i, Equiv (ρ i) (ρ' i)) :
    read M σ es ρ = read M σ es ρ' := by
  exact (key_eq_iff _ _).mpr (LEq_map_den M σ h es)

/-- Proof-slot canonicalization preserves the exact quotient-valued result label.
This is elementary composition with dependent tuple transport. -/
theorem canonical_result (M : Interp.{u}) (σ : Nat → Nat)
    (ss : List FieldShape) (ds : List (Expr Nat)) (h : PiPropPrefix.Erases M σ ss ds)
    (ρ : Nat → PSet.{u}) (xs : List PSet.{u}) (hx : TelFits M σ ds ρ xs)
    (es : List (Expr Nat)) :
    read M σ es (push xs ρ) = read M σ es (push (PiPropPrefix.erase ss xs) ρ) := by
  exact (key_eq_iff _ _).mpr ((PiPropPrefix.canonical_tuple M σ ss ds h ρ xs hx).2.2 es)

/-- Family replacement does not change a clean quotient label, including literal aliases. -/
theorem read_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (es : List (Expr Nat))
    (h : ∀ e ∈ es, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    read (mkM P (upd μ f X₁)) σ es ρ = read (mkM P (upd μ f X₂)) σ es ρ := by
  exact congrArg key (PiIndependent.leafArgs_free P μ f X₁ X₂ σ es h ρ)

/-- A quotient fibre can be defined propositionally without selecting a list representative. -/
def proofFibre (M : Interp.{u}) (F : PSet.{u}) (i : Index.{u}) : PSet.{u} :=
  tv (∃ xs : List PSet.{u}, key xs = i ∧ pempty ∈ Ed M (fapps F xs))

/-- Complete proof applications descend to the quotient. No choice of representative is used. -/
theorem proofFibre_key (M : Interp.{u}) (F : PSet.{u})
    (xs : List PSet.{u})
    (hF : ∀ ys, ys.length = xs.length → ∀ z, z ∈ Ed M (fapps F ys) → Equiv z pempty) :
    Equiv (proofFibre M F (key xs)) (Ed M (fapps F xs)) := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨⟨ys, hys, hy⟩, hz⟩ := mem_tv.mp hz
    have hl : LEq ys xs := (key_eq_iff ys xs).mp hys
    have he := ed_congr M (fapps_congr_args F hl)
    exact mem_congr_left hz.symm (mem_congr_right he hy)
  · intro hz
    have he := hF xs rfl z hz
    exact mem_tv.mpr ⟨⟨xs, rfl, mem_congr_left he hz⟩, he⟩

/-- The leaf truth-set has the proof face even at unused index arities. -/
theorem proofFibre_dich (M : Interp.{u}) (F : PSet.{u}) (i : Index.{u}) :
    Dich (proofFibre M F i) := by
  exact Or.inl (fun _ h => (mem_tv.mp h).2)

/-- Full ambient domains are retained; no branch smallness premise occurs. -/
def tel (M : Interp.{u}) (σ : Nat → Nat) (ds args : List (Expr Nat))
    (ρ : Nat → PSet.{u}) : RecTel.{u,u+1} Index.{u} ds.length :=
  PiSyntaxCompile.compile M σ (read M σ args) ds ρ

/-- Both the domains and quotient labels are independent of the candidate family. -/
theorem tel_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    tel (mkM P (upd μ f X₁)) σ ds args ρ = tel (mkM P (upd μ f X₂)) σ ds args ρ := by
  unfold tel
  have hl := funext (read_free P μ f X₁ X₂ σ args ha)
  rw [hl]
  exact PiIndependent.compile_free P μ f X₁ X₂ σ _ ds ρ hd

/-- Exact element sets for the normalized recursive field. The proof face
is required only at complete applications, not at partial spines. -/
theorem recursiveField_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false)
    (hF : ∀ xs, xs.length = args.length → ∀ z,
      z ∈ Ed (mkM P (upd μ f X)) (fapps (X (ls.map (evalTotal σ))) xs) →
      Equiv z pempty) (ρ : Nat → PSet.{4}) :
    let M := mkM P (upd μ f X)
    Equiv (Ed M ((tel (mkM P μ) σ ds args ρ).erasedType
      M (proofFibre M (X (ls.map (evalTotal σ))))))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) := by
  dsimp only
  have he := tel_free P μ f (μ f) X σ ds args hd ha ρ
  rw [PiIndependent.upd_self] at he
  rw [he]
  unfold tel
  apply PiIndependent.compile_ed (mkM P (upd μ f X)) σ
    (read (mkM P (upd μ f X)) σ args)
    (proofFibre (mkM P (upd μ f X)) (X (ls.map (evalTotal σ))))
    (proofFibre_dich _ _) (foldApps (.const f ls) args)
  intro ρ'
  rw [PiIndependent.leaf_read P μ f X σ ls args ha ρ']
  have hr := read_free P μ f X (μ f) σ args ha ρ'
  rw [PiIndependent.upd_self] at hr
  rw [hr]
  apply proofFibre_key
  intro ys hl z hz
  exact hF ys (hl.trans (List.length_map _ _)) z hz

/-- Forward raw-field transport into a quotient-labelled signature.
Normalization retains ordinary environment and bounded-instance obligations. -/
theorem normalized_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P (upd μ f X)) σ K E n) (hb : BodiesOK E σ K)
    (fuel : Nat) (T : Expr Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel T = some (ds, foldApps (.const f ls) args))
    (hI : InstOK E σ K T) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false)
    (hF : ∀ xs, xs.length = args.length → ∀ z,
      z ∈ Ed (mkM P (upd μ f X)) (fapps (X (ls.map (evalTotal σ))) xs) →
      Equiv z pempty) (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T)) :
    let M := mkM P (upd μ f X)
    x ∈ Ed M ((tel (mkM P μ) σ ds args ρ).erasedType
      M (proofFibre M (X (ls.map (evalTotal σ))))) := by
  dsimp only
  have hn := den_piTelescope_of_mem (mkM P (upd μ f X)) σ K hE hb
    fuel T ds (foldApps (.const f ls) args) ρ x hw hI hx
  exact mem_congr_right ((recursiveField_ed P μ f X σ ls ds args hd ha hF ρ).trans
    (ed_congr (mkM P (upd μ f X)) hn)).symm hx

/-- Elementary admission composition. All argument lengths, family-free scans
and the candidate-independent telescope are produced by the successful read. -/
theorem admitted_field (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) (hI : InstOK E σ K T) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      (∀ X₁ X₂ ρ, tel (mkM P (upd μ f X₁)) σ ds args ρ =
        tel (mkM P (upd μ f X₂)) σ ds args ρ) ∧
      ∀ X, EnvSound (mkM P (upd μ f X)) σ K E n → BodiesOK E σ K →
      (∀ xs, xs.length = np + ni → ∀ z, z ∈ Ed (mkM P (upd μ f X))
        (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs) →
        Equiv z pempty) →
      ∀ ρ x, x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ f X)) ((tel (mkM P μ) σ ds args ρ).erasedType
        (mkM P (upd μ f X)) (proofFibre (mkM P (upd μ f X))
          (X (((List.range nu).map Level.param).map (evalTotal σ))))) := by
  obtain ⟨ds, args, hl, ha, hr, hd, hf⟩ := PiIndependent.admitted_shape h hscope
  refine ⟨ds, args, hl, ha, ?_, ?_⟩
  · intro X₁ X₂ ρ
    exact tel_free P μ f X₁ X₂ σ ds args hd hf ρ
  · intro X hE hb hX ρ x hx
    exact normalized_mem P μ f X σ K hE hb (fuel - 1) T _ ds args hr hI hd hf
      (fun xs hxs => hX xs (hxs.trans ha)) ρ x hx

end Rcic.F3.PSet.PiIndex
