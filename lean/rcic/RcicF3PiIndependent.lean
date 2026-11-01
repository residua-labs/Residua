import rcic.RcicF3PiNormalize
import rcic.RcicF3PiSmallCompile
import rcic.RcicF3WhnfSyn
import rcic.RcicF3Agree
/-! Admission-scan independence of semantic telescopes. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
open Rcic.Model.PS (denRefs denRefsLit)
universe v

/-- Literal aliases have exactly the references recorded by the scanner. -/
theorem literal_refs (f t : Nat) : f ∈ denRefsLit t ↔ litOccurs f t = true := by
  induction t with
  | zero => simp [denRefsLit, litOccurs]
  | succ t ih =>
      cases t with
      | zero => simp [denRefsLit, litOccurs, or_comm]
      | succ t => simpa [denRefsLit, litOccurs, or_comm, or_left_comm, or_assoc] using
          (show f = 2 ∨ f ∈ denRefsLit (t + 1) ↔ f = 2 ∨ litOccurs f (t + 1) = true from
            or_congr Iff.rfl ih)


/-- Exact syntactic occurrence agrees with every reference denotation reads. -/
theorem expr_refs (f : Nat) (e : Expr Nat) : f ∈ denRefs e ↔ occursConst f e = true := by
  induction e with
  | bvar _ => simp [denRefs, occursConst]
  | sort _ => simp [denRefs, occursConst]
  | const r ls => simp [denRefs, occursConst, eq_comm]
  | app a b iha ihb => simp [denRefs, occursConst, iha, ihb]
  | lam a b iha ihb => simp [denRefs, occursConst, iha, ihb]
  | pi a b iha ihb => simp [denRefs, occursConst, iha, ihb]
  | letE a x b iha ihx ihb => simp [denRefs, occursConst, iha, ihx, ihb, or_assoc]
  | lit t => exact literal_refs f t


/-- Replacement-family independence includes refs 1/2; literal aliases are
excluded by the scan itself, not by a numbering premise. -/
theorem den_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (e : Expr Nat)
    (he : occursConst f e = false) (ρ : Nat → PSet.{4}) :
    den (mkM P (upd μ f X₁)) σ ρ e = den (mkM P (upd μ f X₂)) σ ρ e := by
  refine den_agreeOn P (μ₁ := upd μ f X₁) (μ₂ := upd μ f X₂)
    (S := fun r => r ≠ f) (fun r hr ls => ?_) σ e ?_ ρ
  · rw [upd_ne μ f X₁ hr, upd_ne μ f X₂ hr]
  · intro r hr hrf
    subst r
    have ht := (expr_refs f e).mp hr
    rw [he] at ht
    cases ht


/-- All scanned binder domains are family-free. -/
theorem domains_free {E : ResolvedEnv} {f : Nat} : (fuel : Nat) → (ds : List (Expr Nat)) →
    domainsContainFuel E f fuel ds = some false → ∀ A ∈ ds, occursConst f A = false
  | _, [], _, _, h => (List.not_mem_nil _ h).elim
  | 0, _ :: _, h, _, _ => by cases h
  | fuel + 1, A :: ds, h, B, hB => by
      simp only [domainsContainFuel] at h
      cases hc : containsFamilyFuel E f fuel A with
      | none => rw [hc] at h; cases h
      | some b =>
          cases b with
          | true => rw [hc] at h; cases h
          | false =>
              rw [hc] at h
              rcases List.mem_cons.mp hB with rfl | hB
              · exact occursConst_false_of_contains fuel B hc
              · exact domains_free fuel ds h B hB


/-- Literal equality of the complete compiled telescope under arbitrary
replacement families. The independent result label is held fixed. -/
theorem compile_free {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (f : Nat) (X₁ X₂ : List Nat → PSet.{4})
    (σ : Nat → Nat) (R : (Nat → PSet.{4}) → I) : ∀ ds ρ,
    (∀ A ∈ ds, occursConst f A = false) →
    PiSyntaxCompile.compile (mkM P (upd μ f X₁)) σ R ds ρ =
      PiSyntaxCompile.compile (mkM P (upd μ f X₂)) σ R ds ρ := by
  intro ds
  induction ds with
  | nil => intro ρ h; rfl
  | cons A ds ih =>
      intro ρ h
      have he := den_free P μ f X₁ X₂ σ A (h A (List.mem_cons_self _ _)) ρ
      simp only [PiSyntaxCompile.compile]
      rw [he]
      apply congrArg (fun B => RecTel.pi _ B)
      funext q
      exact ih _ (fun B hB => h B (List.mem_cons_of_mem _ hB))


/-- The small-domain compiler is equally independent. Its representation
choice sees the same Ed domain on both sides, including empty domains. -/
theorem smallCompile_free {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (f : Nat) (X₁ X₂ : List Nat → PSet.{4})
    (σ : Nat → Nat) (R : (Nat → PSet.{4}) → I) : ∀ ds ρ,
    (∀ A ∈ ds, occursConst f A = false) →
    PiSmallCompile.compile P (upd μ f X₁) σ R ds ρ =
      PiSmallCompile.compile P (upd μ f X₂) σ R ds ρ := by
  intro ds
  induction ds with
  | nil => intro ρ h; rfl
  | cons A ds ih =>
      intro ρ h
      have he := den_free P μ f X₁ X₂ σ A (h A (List.mem_cons_self _ _)) ρ
      simp only [PiSmallCompile.compile]
      rw [he]
      apply congrArg (fun B => RecTel.pi _ B)
      funext q
      exact ih _ (fun B hB => h B (List.mem_cons_of_mem _ hB))


/-- A successful recursive verdict supplies the scans used for independence,
not only a normalized shape. This is elementary inversion of admission. -/
theorem recursive_scans {E : ResolvedEnv}
    {fuel f nu np ni depth inner : Nat} {T : Expr Nat} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx) :
    ∃ ds b, piTelescopeFuel E (fuel - 1) T = some (ds, b) ∧
      ds.length = inner ∧ idx = familyIdx np b ∧
      domainsContainFuel E f (fuel - 1) ds = some false ∧
      properFamilyFuel E (fuel - 1) f nu np ni (ds.length + depth - 1) b = some true := by
  obtain ⟨ds, b, hr, hl, hi, hp⟩ := fieldAnalyze_recursive_out h
  refine ⟨ds, b, hr, hl, hi, ?_, hp⟩
  cases fuel with
  | zero => cases h
  | succ fuel =>
      simp only [Nat.add_sub_cancel] at hr hp ⊢
      cases hd : domainsContainFuel E f fuel ds with
      | none => simp [fieldAnalyze, hr, hd] at h
      | some c =>
          cases c with
          | true => simp [fieldAnalyze, hr, hd] at h
          | false => rfl


/-- Recursive leaf labels are the actual family arguments, computed in a
base table. They do not contain a candidate family denotation. -/
def leafArgs (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (args : List (Expr Nat)) (ρ : Nat → PSet.{4}) : List PSet.{4} :=
  args.map (den (mkM P μ) σ ρ)

/-- Clean arguments retain exactly the same label for every replacement. -/
theorem leafArgs_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (args : List (Expr Nat))
    (h : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    leafArgs P (upd μ f X₁) σ args ρ = leafArgs P (upd μ f X₂) σ args ρ := by
  exact List.map_congr_left (fun e he => den_free P μ f X₁ X₂ σ e (h e he) ρ)


/-- The complete recursive telescope carries argument labels rather than
current family element sets. This definition does not assert smallness. -/
def recursiveTel (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ds args : List (Expr Nat)) (ρ : Nat → PSet.{4}) :
    RecTel.{3,5} (List PSet.{4}) ds.length :=
  PiSmallCompile.compile P μ σ (leafArgs P μ σ args) ds ρ

/-- The whole telescope, including dependent leaf indices, is independent
of the candidate family table. -/
theorem recursiveTel_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    recursiveTel P (upd μ f X₁) σ ds args ρ = recursiveTel P (upd μ f X₂) σ ds args ρ := by
  unfold recursiveTel
  have hl : leafArgs P (upd μ f X₁) σ args = leafArgs P (upd μ f X₂) σ args :=
    funext (leafArgs_free P μ f X₁ X₂ σ args ha)
  rw [hl]
  exact smallCompile_free P μ f X₁ X₂ σ _ ds ρ hd


/-- Admission produces a candidate-independent telescope at every recursive
verdict. The arithmetic premise is the actual parameter-local scope. -/
theorem admitted_recursive {E : ResolvedEnv}
    {fuel f nu np ni depth inner : Nat} {T : Expr Nat} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth)
    (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    ∃ ds args,
      ds.length = inner ∧ args.length = np + ni ∧
      piTelescopeFuel E (fuel - 1) T =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      ∀ X₁ X₂ ρ, recursiveTel P (upd μ f X₁) σ ds args ρ =
        recursiveTel P (upd μ f X₂) σ ds args ρ := by
  obtain ⟨ds, b, hr, hl, hi, hd, hp⟩ := recursive_scans h
  have hs : np ≤ ds.length + depth - 1 + 1 := by rw [hl]; omega
  obtain ⟨ix, hb, hix, hfree⟩ := properFamilyFuel_shape hs hp
  refine ⟨ds, policyParameterLocals np (ds.length + depth - 1 + 1 - np) ++ ix,
    hl, ?_, ?_, ?_⟩
  · simp only [List.length_append, policyParameterLocals_length, hix]
  · rw [← hb]; exact hr
  · intro X₁ X₂ ρ
    apply recursiveTel_free P μ f X₁ X₂ σ _ _ (domains_free _ _ hd) _ ρ
    intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [policyParameterLocals, List.mem_map] at he
      obtain ⟨i, _, rfl⟩ := he
      rfl
    · exact hfree e he


/-- Updating an entry by its current function is the original table.
Elementary extensional identity. -/
theorem upd_self (μ : Nat → List Nat → PSet.{4}) (f : Nat) : upd μ f (μ f) = μ := by
  funext r vs
  by_cases hr : r = f
  · subst r; exact upd_eq μ f (μ f) vs
  · exact upd_ne μ f (μ f) hr vs


/-- Canonical recursive leaves read candidate family values at labels
computed solely in the base table. Elementary denotation composition. -/
theorem leaf_read (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level) (args : List (Expr Nat))
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    den (mkM P (upd μ f X)) σ ρ (foldApps (.const f ls) args) =
      fapps (X (ls.map (evalTotal σ))) (leafArgs P μ σ args ρ) := by
  rw [den_foldApps]
  change fapps ((upd μ f X) f (ls.map (evalTotal σ)))
    (leafArgs P (upd μ f X) σ args ρ) = _
  rw [upd_eq]
  have he := leafArgs_free P μ f X (μ f) σ args ha ρ
  rw [upd_self] at he
  rw [he]

end Rcic.F3.PSet.PiIndependent
