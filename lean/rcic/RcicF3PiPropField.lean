import rcic.RcicF3PiPropProducer
import rcic.RcicF3PiAdmission
/-! Proof-valued recursive fields erase through arbitrary dependent Pi
spines. Complete family applications preserve the proof face; admission
supplies the complete spine length. Ordinary environment semantics and
body bounds remain explicit in the raw normalization helper. No raw-group
producer or universal StepAG is asserted. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropField
open Rcic.Declarative
universe u v

theorem encode_empty {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich)
    (f : PiTel.Value.{u,u+1} t.tel (fun _ => PSet.{u}))
    (hf : ∀ p, Equiv (t.tel.flatten f p) pempty) :
    Equiv (t.erasedEncode M f) pempty := by
  induction t with
  | ret i => exact hf .unit
  | pi A B ih =>
    have hL : LamProof M (tyv A)
        (classFiber A (fun q => (B q).erasedEncode M (f q))) := by
      intro a ha
      obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
      exact ((classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)).trans
        (ih (Quotient.mk (FSetoid A) i) (ht.2 _) _ (fun p => hf ⟨_, p⟩))
    change Equiv (lamVal M (tyv A) _) pempty
    unfold lamVal
    rw [cond_pos hL]
    exact Equiv.rfl
theorem member_empty {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i z, z ∈ X i → Equiv z pempty) {f : PSet.{u}}
    (hf : f ∈ Ed M (t.erasedType M X)) : Equiv f pempty := by
  have hr := t.erasedRead_spec M ht X (fun i => Or.inl (hX i)) hf
  exact hr.2.trans (encode_empty M t ht _ (fun p =>
    hX _ _ ((PiTel.all_iff _ _ _).mp hr.1 p)))
theorem member_iff {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (φ : I → Prop) (f : PSet.{u}) :
    f ∈ Ed M (t.erasedType M (fun i => tv (φ i))) ↔
      Equiv f pempty ∧ ∀ p, φ (t.result p) := by
  have hX : ∀ i, Dich (tv (φ i) : PSet.{u}) :=
    fun _ => Or.inl (fun _ h => (mem_tv.mp h).2)
  constructor
  · intro hf
    have hr := t.erasedRead_spec M ht _ hX hf
    exact ⟨member_empty M t ht _ (fun _ _ h => (mem_tv.mp h).2) hf,
      fun p => (mem_tv.mp ((PiTel.all_iff _ _ _).mp hr.1 p)).1⟩
  · rintro ⟨he, hp⟩
    let v : PiTel.Value.{u,u+1} t.tel (fun _ => PSet.{u}) :=
      t.tel.unflatten (fun _ => pempty)
    have hrel : t.Rel (fun i => tv (φ i)) v := by
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v = t.tel.unflatten (fun _ => pempty) from rfl,
        PiTel.flatten_unflatten]
      exact mem_tv.mpr ⟨hp p, Equiv.rfl⟩
    have hv := t.erasedEncode_mem M ht _ hX v hrel
    have hz := encode_empty M t ht v (fun p => by
      rw [show v = t.tel.unflatten (fun _ => pempty) from rfl,
        PiTel.flatten_unflatten]
      exact Equiv.rfl)
    exact mem_congr_left (hz.trans he.symm) hv
theorem compile_result_property {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (Q : I → Prop) (h : ∀ ρ, Q (R ρ)) :
    ∀ ds ρ p, Q ((PiSyntaxCompile.compile M σ R ds ρ).result p) := by
  intro ds
  induction ds with
  | nil => intro ρ p; exact h ρ
  | cons A ds ih => intro ρ p; exact ih _ p.2
/-- Elementary composition. The proof face is required only after a
complete admitted family spine, not at partial applications. -/
theorem admitted_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) (hI : InstOK E σ K T)
    (hE : EnvSound (mkM P (upd μ f X)) σ K E n) (hb : BodiesOK E σ K)
    (hX : ∀ xs, xs.length = np + ni → ∀ z, z ∈ Ed (mkM P (upd μ f X))
      (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs) →
      Equiv z pempty)
    (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T)) :
    Equiv x pempty := by
  obtain ⟨ds, args, _, ha, _, hm⟩ := PiIndependent.admitted_field P μ σ K h hscope hI
  let M := mkM P (upd μ f X)
  let t := PiSyntaxCompile.compile (mkM P μ) σ (PiIndependent.leafArgs P μ σ args) ds ρ
  have ht := PiSyntaxCompile.compile_domains (mkM P μ) σ
    (PiIndependent.leafArgs P μ σ args) ds ρ
  have hr := t.erasedRead_spec M ht _ (fun _ => dich_ed M _) (hm X hE hb ρ x hx)
  have he : ∀ p, Equiv (t.tel.flatten (t.erasedRead M x) p) pempty := by
    intro p
    apply hX (t.result p)
    · exact compile_result_property (mkM P μ) σ (PiIndependent.leafArgs P μ σ args)
        (fun xs => xs.length = np + ni)
        (fun _ => (List.length_map _ _).trans ha) ds ρ p
    · exact (PiTel.all_iff _ _ _).mp hr.1 p
  exact hr.2.trans (encode_empty M t ht _ he)
/-- Complete family applications preserve the proof face, including
arguments outside the family telescope (whose application is empty). -/
theorem application_empty (M : Interp.{u}) (σ : Nat → Nat)
    (g : (Nat → PSet.{u}) → PSet.{u}) (hg : EnvResp g)
    (hp : ∀ ρ z, z ∈ Ed M (g ρ) → Equiv z pempty)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hl : xs.length = ds.length) {z : PSet.{u}}
    (hz : z ∈ Ed M (fapps (piLam M σ g ρ (policyPi ds (.sort .zero))) xs)) :
    Equiv z pempty := by
  cases M.dec (Equiv (fapps (piLam M σ g ρ (policyPi ds (.sort .zero))) xs) pempty) with
  | isTrue he =>
    exact (not_mem_pempty (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hz)).elim
  | isFalse hn =>
    have hf := fits_of_fapps_ne M σ hg (.sort .zero) ds ρ xs hl hn
    have he := fapps_piLam M σ hg (.sort .zero) ds ρ xs hf
    exact hp (push xs ρ) z (mem_congr_right (ed_congr M he) hz)
end Rcic.F3.PSet.PiPropField
