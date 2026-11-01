import rcic.RcicF3PiValueExtract
/-! Raw admitted proof-family constructor abstraction. The original bounded
type derivation supplies result typehood; parameters remain ordinary plain
slots. Raw group assembly and universal StepAG are unpaid. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawCtor
open Rcic.Declarative PiValueRule PiValueExtract

/-- Family-free constructor parameters prefix the extracted fields. -/
theorem prefix_views {E : ResolvedEnv} {fuel f nu ar : Nat} :
    ∀ (Ps : List (Expr Nat)), (∀ A ∈ Ps, occursConst f A = false) →
    ∀ {As fs}, Views E fuel f nu ar As fs →
    Views E fuel f nu ar (Ps ++ As) ((Ps.map FieldSpec.plain) ++ fs) := by
  intro Ps
  induction Ps with
  | nil => intro _ As fs hv; exact hv
  | cons A Ps ih =>
      intro hP As fs hv
      exact .cons ⟨rfl, hP A (List.mem_cons_self _ _)⟩
        (ih (fun B hB => hP B (List.mem_cons_of_mem _ hB)) hv)

/-- An admitted raw constructor abstraction inhabits its entire stored type,
including its family-free parameter prefix. Original typing and ordinary
bounds supply hereditary result typehood internally. -/
theorem constructor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) {E : ResolvedEnv} {n fuel ni : Nat}
    (Ps As : List (Expr Nat)) (fs : List FieldSpec) {ss : List FieldShape}
    (hP : ∀ A ∈ Ps, occursConst f A = false)
    (ha : fieldShapesFuel E fuel f vs.length Ps.length ni Ps.length As = some ss)
    (har : Ps.length + ni = famDs.length)
    (hf : fields E fuel f vs.length Ps.length ni Ps.length As = some fs)
    (hc : (cs[c]).fields = Ps.map FieldSpec.plain ++ fs)
    (hr : ∀ a ∈ (cs[c]).result, occursConst f a = false)
    (hl : (cs[c]).result.length = famDs.length)
    (K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hI : ∀ A ∈ Ps ++ As, InstOK E (σOf vs) K A)
    {u : Level}
    (d : HasTyT E n [] (policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) (.sort u))
    (hd : LOKt (σOf vs) 4 K d) :
    let M := mkM P (upd μ f (PiValue.table P μ (predicate P μ famDs cs) famDs))
    let T := policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)
    piLam M (σOf vs) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf vs) ρ0 T) := by
  dsimp only
  let φ := predicate P μ famDs cs
  let X := PiValue.table P μ φ famDs
  let M := mkM P (upd μ f X)
  obtain ⟨fs', hfs, hv⟩ := fields_of_admitted As Ps.length ss ha (Nat.le_refl _)
  have hfs' : fs' = fs := Option.some.inj (hfs.symm.trans hf)
  subst fs'
  have hv' := prefix_views Ps hP hv
  rw [← hc] at hv'
  have hclean := hv'.clean
  rw [har] at hclean
  have hsd := hsound_ty (P.good M rfl) hE d hd
  refine piLam_mem M (σOf vs) (envResp_const pempty) _ ρ0 ?_
  refine piGood_policyPi_fits M (σOf vs) (fun _ => pempty) _ (Ps ++ As) ρ0 ?_
  intro xs hx
  refine piGood_foldApps M (σOf vs) (fun _ => pempty) _
    (.const f ((List.range vs.length).map Level.param))
    (fun _ _ h => Expr.noConfusion h) (cs[c]).result ?_
  obtain ⟨v, hv⟩ := tel_end_type _ (Ps ++ As) d hsd ρ0 xs True.intro hx
  let ys := PiIndependent.leafArgs P μ (σOf vs) (cs[c]).result (push xs ρ0)
  have he := PiIndependent.leaf_read P μ f X (σOf vs)
    ((List.range vs.length).map Level.param) (cs[c]).result hr (push xs ρ0)
  rw [map_param_σOf] at he
  have hn : ¬ Equiv (fapps (X vs) ys) pempty := by
    rw [← he]
    exact ne_of_mem_sort rfl hv
  have hy : ys.length = famDs.length := (List.length_map _ _).trans hl
  have hfit := fits_of_fapps_ne (mkM P μ) (σOf vs)
    (PiValue.endValue_resp (φ vs) famDs.length) (.sort .zero) famDs ρ0 ys hy hn
  have hp := close_tuple P μ f famDs cs vs c hclean xs
    (hv'.mem M (σOf vs) K hE hb hI ρ0 xs hx)
  rw [he]
  exact (PiValue.apply_mem_iff (mkM P μ) (σOf vs) (φ vs) famDs ρ0 ys hy pempty).mpr
    ⟨hfit, hp, Equiv.rfl⟩


end Rcic.F3.PSet.PiRawCtor
