import rcic.RcicF3KTWFamFit
import rcic.RcicF3RecValRec

/-!
# F3 S7 KT-2b-3c-3b: the family entry built from a data-set function

The family entry built from a data-set function, the class of function-recursive
fields, and the piVal reading: `ed_piVal_of_noEmpty` says that when no fibre of
`piVal`'s codomain contains `∅`, `Ed` of it is the dependent function space on
the truncated domain.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

/-- `Ed` of a `tyv` whose set has the dichotomy property. -/
theorem ed_tyv_of_dich (M : Interp.{T}) {S : PSet.{T}} (hS : Dich S) :
    Equiv (Ed M (tyv S)) S := by
  rw [ed_of_dich M ((dich_congr el_tyv).mpr hS)]
  exact el_tyv

/-- `Ed` of a `piVal` whose fibres never contain `∅` is the dependent function
space on the truncated domain. -/
theorem ed_piVal_of_noEmpty (M : Interp.{T}) {A : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (h : ∀ x, x ∈ Ed M A → ¬ pempty ∈ Ed M (B x)) :
    Equiv (Ed M (piVal M A B)) (piSet (Ed M A) (fun x => Ed M (B x))) := by
  unfold piVal
  cases M.dec (PiProp M A B) with
  | isTrue hp =>
      rw [cond_pos hp]
      have hBE : ∀ x x', Equiv x x' → Equiv (Ed M (B x)) (Ed M (B x')) :=
        fun x x' hx => ed_congr M (hB x x' hx)
      -- every fibre is empty
      have hfib : ∀ x ∈ Ed M A, ∀ y, ¬ y ∈ Ed M (B x) := fun x hx y hy =>
        h x hx (mem_congr_left (hp x hx y hy) hy)
      refine (ed_tyv_of_dich M (dich_tv _)).trans (ext fun g => ⟨fun hg => ?_, fun hg => ?_⟩)
      · obtain ⟨hφ, hgE⟩ := mem_tv.mp hg
        -- Ed A is empty: a member would put ∅ in a fibre, contradicting emptiness
        have hAe : ∀ a, ¬ a ∈ Ed M A := fun a ha => hfib a ha _ (hφ a ha)
        have hfun : isFuncOnDep (Ed M A) (fun x => Ed M (B x)) pempty :=
          ⟨fun a ha => absurd ha (hAe a), fun p hp => absurd hp not_mem_pempty,
           fun a b b' h₁ => absurd h₁ not_mem_pempty⟩
        exact mem_congr_left hgE.symm (mem_piSet_of_dep hBE hfun)
      · have hgd := isFuncOnDep_of_mem_piSet hBE hg
        -- totality: any a ∈ Ed A would need a member of an empty fibre
        have hAe : ∀ a, ¬ a ∈ Ed M A := fun a ha => by
          obtain ⟨b, hb, _⟩ := hgd.1 a ha
          exact hfib a ha b hb
        refine mem_tv.mpr ⟨fun x hx => absurd hx (hAe x), ?_⟩
        apply ext; intro y; constructor
        · intro hy
          obtain ⟨a, ha, _, _⟩ := hgd.2.1 y hy
          exact absurd ha (hAe a)
        · intro hy; exact absurd hy not_mem_pempty
  | isFalse hp =>
      rw [cond_neg hp]
      exact ed_tyv_of_dich M (dich_piSet M.dec
        (fun x x' hx => ed_congr M (hB x x' hx)))

/-- A function-recursive field at depth `d`: `Π (y : D'), F ps (idx y)`. -/
def FnRec (f ar np nq d : Nat) (A : Expr Nat) : Prop :=
  ∃ (D' : Expr Nat) (idx : List (Expr Nat)),
    A = .pi D' (foldApps (.const f (canonL ar)) (policyParameterLocals np (d + 1) ++ idx)) ∧
    idx.length = nq ∧ occursConst f D' = false ∧ ∀ e, e ∈ idx → occursConst f e = false

/-- Fields of a class-A constructor: family-free, directly recursive, or
function-recursive. -/
def FieldsClassA (f ar np nq : Nat) : List (Expr Nat) → Nat → Prop
  | [], _ => True
  | A :: Fs, d =>
      (occursConst f A = false ∨ DirectRec f ar np nq d A ∨ FnRec f ar np nq d A) ∧
        FieldsClassA f ar np nq Fs (d + 1)

/-- `f` occurs under a `foldApps` whose head already mentions `f`. -/
theorem occursConst_foldApps {f : Nat} {e : Expr Nat} (he : occursConst f e = true) :
    (as : List (Expr Nat)) → occursConst f (foldApps e as) = true
  | [] => he
  | a :: as => by
      show occursConst f (foldApps (.app e a) as) = true
      exact occursConst_foldApps (e := .app e a)
        (by simp only [occursConst, he, Bool.true_or]) as

theorem kindOf_free {f : Nat} {A : Expr Nat} (h : occursConst f A = false) :
    kindOf f A = .plain := by
  cases A <;> simp [kindOf, h]

theorem kindOf_directRec {f ar np nq d : Nat} {A : Expr Nat}
    (h : DirectRec f ar np nq d A) : kindOf f A = .direct := by
  obtain ⟨idx, hA, _, _⟩ := h
  rw [hA]
  suffices ∀ (e : Expr Nat) (as : List (Expr Nat)),
      (∀ A B, e ≠ .pi A B) → occursConst f e = true →
      kindOf f (foldApps e as) = .direct from
    this _ _ (fun A B hh => Expr.noConfusion hh) (by simp [occursConst])
  intro e as he hocc
  induction as generalizing e with
  | nil =>
      show kindOf f e = .direct
      unfold kindOf
      split
      · exact absurd rfl (he _ _)
      · rw [if_pos hocc]
  | cons a as ih =>
      show kindOf f (foldApps (.app e a) as) = .direct
      exact ih _ (fun A B hh => Expr.noConfusion hh)
        (by simp only [occursConst, hocc, Bool.true_or])

theorem kindOf_fnRec {f ar np nq d : Nat} {A : Expr Nat}
    (h : FnRec f ar np nq d A) : kindOf f A = .fn := by
  obtain ⟨D', idx, hA, _, hD', _⟩ := h
  rw [hA]
  show (if occursConst f (.pi D' (foldApps (.const f (canonL ar))
      (policyParameterLocals np (d + 1) ++ idx))) = true
      then PKind.fn else PKind.plain) = PKind.fn
  rw [if_pos]
  simp only [occursConst, Bool.or_eq_true]
  exact Or.inr (occursConst_foldApps (e := .const f (canonL ar)) (by simp [occursConst]) _)

/-- The `some` index of `findIdx` is below the bound. -/
theorem findIdx_lt (M : Interp.{T}) (p : Nat → Prop) :
    ∀ {j n}, findIdx M p n = some j → j < n
  | _, 0, h => Option.noConfusion h
  | _, k + 1, h => by
      rw [findIdx] at h
      split at h
      · rename_i i hi
        exact Nat.lt_succ_of_lt (Option.some.inj h ▸ findIdx_lt M p hi)
      · rename_i hk
        unfold findIdx.cond' at h
        split at h
        · rw [Option.some.inj h]; exact Nat.lt_succ_self _
        · exact Option.noConfusion h

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)

/-- The spine of `foldApps (.const f ls) args` is just `args`. -/
theorem argsFitF_directRec (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (f : Nat) (ls : List Level) (args : List (Expr Nat)) :
    argsFitF P μ fd σ ρ (foldApps (.const f ls) args) ↔
      TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
        (args.map (den (mkM P μ) σ ρ)) := by
  unfold argsFitF
  rw [appsSpine_foldApps]
  exact Iff.rfl

/-- The fibre of a data-set function `D` at the result-index tuple `is`. -/
def fibAt (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}) (σ : Nat → Nat)
    (ρp : Nat → PSet.{4}) (is : List PSet.{4}) : PSet.{4} :=
  sep (fun z => Equiv (resTupF P μ fd σ ρp z) (ordPair pempty (tup is))) (D σ ρp)

/-- The family end-map built from `D`. -/
def famEndD (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) : PSet.{4} :=
  tyv (fibAt P μ fd D σ (shiftρ fd.indices.length ρ) (lastVals fd.indices.length ρ))

/-- The family value built from `D`. -/
def famOfD (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}) : List Nat → PSet.{4} :=
  fun vs => piLam (mkM P μ) (σOf vs) (famEndD P μ fd D (σOf vs)) ρ0 (famType fd)

/-- `fibAt` respects `≈` in the parameter environment and `LEq` in `is`. -/
theorem fibAt_congr (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
    (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (hρ : ∀ i, Equiv (ρp i) (ρp' i))
    {is is' : List PSet.{4}} (his : LEq is is') :
    Equiv (fibAt P μ fd D σ ρp is) (fibAt P μ fd D σ ρp' is') :=
  sep_congr
    (fun a b hab h =>
      ((resTupF_env P μ fd σ hρ b).symm.trans
        ((resTupF_congr P μ fd σ ρp hab.symm).trans h)).trans
        (ordPair_congr Equiv.rfl (tup_congr his)))
    (fun a b hab h =>
      ((resTupF_env P μ fd σ hρ b).trans
        ((resTupF_congr P μ fd σ ρp' hab.symm).trans h)).trans
        (ordPair_congr Equiv.rfl (tup_congr his.symm)))
    (hD1 σ ρp ρp' hρ)

/-- `famEndD` is environment-respecting. -/
theorem famEndD_envResp (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
    (σ : Nat → Nat) : EnvResp (famEndD P μ fd D σ) :=
  fun ρ ρ' h => tyv_congr (fibAt_congr P μ fd D hD1 σ
    (fun i => h (i + fd.indices.length)) (lastVals_congr fd.indices.length h))

/-- `resTupF` only sees level parameters below `ar`. -/
theorem resTupF_levels {ar : Nat} (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρp : Nat → PSet.{4}) (z : PSet.{4}) :
    Equiv (resTupF P μ fd σ ρp z) (resTupF P μ fd σ' ρp z) := by
  unfold resTupF
  cases hf : findIdx (mkM P μ) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | none => exact Equiv.rfl
  | some j =>
      have hjlt : j < fd.ctors.length := findIdx_lt (mkM P μ) _ hf
      have hmem : fd.ctors.getD j ([], []) ∈ fd.ctors := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
        exact List.getElem_mem hjlt
      refine ordPair_congr Equiv.rfl (tup_congr ?_)
      rw [map_den_levels (mkM P μ) hσ _ (hB.ctors _ hmem).2]
      exact LEq.refl _

/-- `famEndD` only sees level parameters below `ar`. -/
theorem famEndD_levels {ar : Nat} (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hB : FamBounded fd ar)
    (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
    (hD2 : ∀ σ σ', (∀ i, i < ar → σ i = σ' i) → ∀ ρ, Equiv (D σ ρ) (D σ' ρ)) :
    ∀ σ σ', (∀ i, i < ar → σ i = σ' i) → ∀ ρ,
      Equiv (famEndD P μ fd D σ ρ) (famEndD P μ fd D σ' ρ) := by
  intro σ σ' hσ ρ
  exact tyv_congr (sep_congr
    (fun a b hab h => ((resTupF_levels P μ fd hB hσ _ b).symm.trans
      ((resTupF_congr P μ fd σ _ hab.symm).trans h)))
    (fun a b hab h => (resTupF_levels P μ fd hB hσ _ b).trans
      ((resTupF_congr P μ fd σ' _ hab.symm).trans h))
    (hD2 σ σ' hσ _))

/-- `fibAt` never contains `∅`. -/
theorem fibAt_dich (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hD3 : ∀ σ ρ z, z ∈ D σ ρ → ¬ Equiv z pempty)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (is : List PSet.{4}) :
    Dich (fibAt P μ fd D σ ρp is) :=
  Or.inr fun hm => by
    obtain ⟨i, _, hi⟩ := mem_sep.mp hm
    exact hD3 σ ρp _ ⟨i, Equiv.refl _⟩ hi

/-- `Ed` of `famEndD` is the underlying `fibAt`, for any `μ'` (only `dec` is used). -/
theorem ed_famEndD (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hD3 : ∀ σ ρ z, z ∈ D σ ρ → ¬ Equiv z pempty)
    (μ' : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (mkM P μ') (famEndD P μ fd D σ ρ))
      (fibAt P μ fd D σ (shiftρ fd.indices.length ρ) (lastVals fd.indices.length ρ)) :=
  ed_tyv_of_dich (mkM P μ')
    (fibAt_dich P μ fd D hD3 σ _ _)

/-- `fibAt` stays inside its stage. -/
theorem fibAt_mem_W4 (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (hD4 : ∀ σ ρ, D σ ρ ∈ W4 (evalTotal σ fd.resLevel))
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (is : List PSet.{4}) :
    fibAt P μ fd D σ ρp is ∈ W4 (evalTotal σ fd.resLevel) :=
  (stageW4 P _).subset (hD4 σ ρp) (fun _ hx => mem_sep_subset hx)

end

end PSet

end Rcic.F3
