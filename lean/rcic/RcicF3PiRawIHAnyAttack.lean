import rcic.RcicF3PiRawIHAny
import rcic.RcicF3PiRawIHAttack
import rcic.RcicF3PiRawRenameAttack
/-! Data-valued depth-three IH non-vacuity, complete keys, binder insertion,
and hidden-syntax attacks. Premises4 is retained; this is not a full raw
recursor group. Numeric labels are arbitrary. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawIHAnyAttack
open Rcic.Declarative PiIndex PiRawIH
open PiRawIHAttack (model dom ds args field major)

def datum : PSet.{4} := dataVal 17 []
def domain : PSet.{4} := singleton datum
def σ : Nat → Nat := σOf [1]
def v : Level := .param 0

theorem domain_dich : Dich domain :=
  Or.inr (fun h => dataVal_ne_pempty 17 [] (mem_singleton.mp h).symm)

theorem type_mem (P : Premises4) : tyv domain ∈ U W4 1 := by
  have hd : datum ∈ W4 1 := dataVal_mem_stage (stageW4 P 1) 17 []
    (fun _ h => (List.not_mem_nil _ h).elim)
  obtain ⟨i, hi⟩ := (stageW4 P 1).singleton_mem hd
  exact mem_sImage_tyv.mpr ⟨domain, mem_sep.mpr ⟨i,
    (dich_congr hi.symm).mp domain_dich, hi⟩, Equiv.rfl⟩

def motive (P : Premises4) (f : Nat) : PSet.{4} :=
  piLam (model P f) σ (fun _ => tyv domain) ρ0
    (policyPi [dom f, major f] (.sort v))
def assignment (P : Premises4) (f : Nat) : Nat → PSet.{4} :=
  vcons pempty (vcons (motive P f) ρ0)

theorem motive_mem (P : Premises4) (f : Nat) :
    motive P f ∈ Ed (model P f) (den (model P f) σ ρ0
      (policyPi [dom f, major f] (.sort v))) := by
  refine piLam_mem (model P f) σ (envResp_const _) _ ρ0 ?_
  apply piGood_policyPi
  intro ρ
  exact mem_congr_right (ed_tyv (model P f) (U4_dich 1)).symm (type_mem P)

theorem motive_apply (P : Premises4) (f : Nat) (is : List PSet.{4}) (z : PSet.{4})
    (hf : TelFits (model P f) σ [dom f, major f] ρ0 (is ++ [z])) :
    Equiv (fapps (motive P f) (is ++ [z])) (tyv domain) :=
  fapps_piLam (model P f) σ (envResp_const _) (.sort v) _ ρ0 _ hf

theorem field_mem (P : Premises4) (f : Nat) (ρ : Nat → PSet.{4}) :
    pempty ∈ Ed (model P f) (den (model P f) σ ρ (field f)) := by
  let M := model P f
  let t := tel M σ (ds f) args ρ
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ _ (ds f) ρ
  have hx := (PiPropField.member_iff M t ht (fun _ => True) pempty).mpr
    ⟨Equiv.rfl, fun _ => True.intro⟩
  exact mem_congr_right (ed_congr M (PiRawIHAttack.field_equiv P f ρ)) hx

/-- The raw typed motive and actual field recover the data-valued leaf. -/
theorem leaf (P : Premises4) (f : Nat) (xs : List PSet.{4})
    (hf : TelFits (model P f) σ (ds f) (assignment P f) xs) :
    Equiv (den (model P f) σ (push xs (assignment P f))
      (foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
        (args ++ [fieldApp (ds f).length]))) (tyv domain) := by
  let M := model P f
  let ρ := assignment P f
  let is := args.map (den M σ (push xs ρ))
  let z := fapps pempty xs
  have hz : z ∈ Ed M (fapps (M.μ f []) is) := by
    have h := mem_fapps M σ (foldApps (.const f []) args) (ds f) ρ pempty xs
      (field_mem P f ρ) hf
    rw [den_foldApps] at h
    exact h
  have his := ((PiValue.apply_mem_iff M σ (fun _ => True) [dom f] ρ0 is
    (by simp [is, args]) z).mp
      (mem_congr_right (ed_congr M (fapps_congr (PiRawIHAttack.family P f) is)) hz)).1
  have hden := Fapp_den M σ f [] [] is ρ0
  rw [his.length] at hden
  change den M σ (push is ρ0) (major f) = fapps (M.μ f []) is at hden
  have hmajor : z ∈ Ed M (den M σ (push is ρ0) (major f)) := by
    rw [hden]; exact hz
  have hm := motive_apply P f is z (TelFits.append his ⟨hmajor, True.intro⟩)
  have he : den M σ (push xs ρ)
      (foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
        (args ++ [fieldApp (ds f).length])) = fapps (motive P f) (is ++ [z]) := by
    rw [den_foldApps, ← hf.length, den_lift0_push,
      List.map_append, List.map_cons, List.map_nil, den_fieldApp]
    rfl
  rw [he]; exact hm

/-- A positive universe parameter, inhabited domains, a real recursive field,
exact any-sort IH fidelity, and an IH returning nonempty data at depth three. -/
theorem inhabited (P : Premises4) (f : Nat) :
    let M := model P f
    let ρ := assignment P f
    let xs := [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]
    motive P f ∈ Ed M (den M σ ρ0 (policyPi [dom f, major f] (.sort v))) ∧
    TelFits M σ (ds f) ρ xs ∧ pempty ∈ Ed M (den M σ ρ (field f)) ∧
    Equiv ((tel M σ (ds f) args ρ).erasedIHType M
      (PiRawMotiveAny.guarded M σ 1 (M.μ f []) (motive P f) [] [dom f] ρ0) pempty)
      (den M σ ρ (PiRawIHAttack.ihExpr f)) ∧
    ∃ ih, ih ∈ Ed M (den M σ ρ (PiRawIHAttack.ihExpr f)) ∧
      ¬ Equiv (fapps ih xs) pempty := by
  dsimp only
  let M := model P f
  let ρ := assignment P f
  have hx := field_mem P f ρ
  have he := PiRawIHAny.normalized_spec M rfl σ f []
    (PiValue.endValue (fun _ => True) 1) (PiValue.endValue_resp _ _) .zero v
    [] [dom f] [] rfl (PiRawIHAttack.family P f) (motive P f) (motive_mem P f)
    (ds f) args rfl ρ (fun _ _ => rfl) (.bvar 1) rfl hx
  have hdatum : PiPropPrefixAttack.datum ∈ Ed M (tyv PiPropPrefixAttack.domain) :=
    mem_congr_right (ed_tyv M (Or.inr (fun h => dataVal_ne_pempty 7 []
      (mem_singleton.mp h).symm))).symm (mem_singleton.mpr Equiv.rfl)
  have hd : ∀ τ, PiPropPrefixAttack.datum ∈ Ed M (den M σ τ (dom f)) := by
    intro τ
    change PiPropPrefixAttack.datum ∈ Ed M ((upd PiRawIHAttack.base f
      (PiValue.table P PiRawIHAttack.base (fun _ _ => True) [dom f])) (f + 1) [])
    rw [upd_ne _ _ _ (show f + 1 ≠ f by omega)]; exact hdatum
  have hfit : TelFits M σ (ds f) ρ
      [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum] :=
    ⟨hd _, hd _, hd _, True.intro⟩
  let g : (Nat → PSet.{4}) → PSet.{4} := fun _ => datum
  let ih := piLam M σ g ρ (PiRawIHAttack.ihExpr f)
  have hih : ih ∈ Ed M (den M σ ρ (PiRawIHAttack.ihExpr f)) := by
    refine piLam_mem M σ (envResp_const _) _ ρ ?_
    refine piGood_policyPi_fits M σ g _ (ds f) ρ ?_
    intro xs hf
    apply piGood_foldApps M σ g _ _ (fun _ _ h => Expr.noConfusion h)
    exact mem_congr_right (ed_congr M (leaf P f xs hf)).symm
      (mem_congr_right (ed_tyv M domain_dich).symm (mem_singleton.mpr Equiv.rfl))
  have hi := fapps_piLam M σ (envResp_const datum)
    (foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
      (args ++ [fieldApp (ds f).length])) (ds f) ρ _ hfit
  refine ⟨motive_mem P f, hfit, hx, he, ih, hih, ?_⟩
  intro hn
  exact dataVal_ne_pempty 17 [] (hi.symm.trans hn)

/-- Even without a fitting tuple, the empty-arity key has an exact empty guard. -/
theorem unused_arity (P : Premises4) (f : Nat) (z : PSet.{4}) :
    Equiv (PiRawMotiveAny.guarded (model P f) σ 1 ((model P f).μ f [])
      (motive P f) [] [dom f] ρ0 (key []) z) pempty := by
  apply PiRawMotiveAny.guarded_unused
  rintro ⟨is, hi, hf, _⟩
  have hl := LEq.length ((key_eq_iff _ _).mp hi)
  have hf' := hf.length
  simp only [List.nil_append, List.length_nil, List.length_cons] at hl hf'
  omega

/-- An out-of-domain data index cannot contribute to the bounded guard. -/
theorem invalid_index_guard (P : Premises4) (f : Nat) (z : PSet.{4}) :
    Equiv (PiRawMotiveAny.guarded (model P f) σ 1 ((model P f).μ f [])
      (motive P f) [] [dom f] ρ0 (key [dataVal 8 []]) z) pempty := by
  apply PiRawMotiveAny.guarded_unused
  rintro ⟨is, hi, _, hz⟩
  have he := (key_eq_iff _ _).mp hi
  have hm := mem_congr_right (ed_congr (model P f)
    (fapps_congr_args ((model P f).μ f []) he)) hz
  exact PiRawIHAttack.invalid_index P f z hm

/-- The valid complete key retains a nonempty data motive at the fitting major. -/
theorem used_key (P : Premises4) (f : Nat) :
    Equiv (PiRawMotiveAny.guarded (model P f) σ 1 ((model P f).μ f [])
      (motive P f) [] [dom f] ρ0 (key [PiPropPrefixAttack.datum]) pempty) domain := by
  let M := model P f
  have hf : TelFits M σ [dom f] ρ0 [PiPropPrefixAttack.datum] := by
    refine ⟨?_, True.intro⟩
    change PiPropPrefixAttack.datum ∈ Ed M ((upd PiRawIHAttack.base f
      (PiValue.table P PiRawIHAttack.base (fun _ _ => True) [dom f])) (f + 1) [])
    rw [upd_ne _ _ _ (show f + 1 ≠ f by omega)]
    exact mem_congr_right (ed_tyv M (Or.inr (fun h => dataVal_ne_pempty 7 []
      (mem_singleton.mp h).symm))).symm (mem_singleton.mpr Equiv.rfl)
  have hz : pempty ∈ Ed M (fapps (M.μ f []) [PiPropPrefixAttack.datum]) := by
    apply mem_congr_right (ed_congr M ((fapps_congr (PiRawIHAttack.family P f) _).trans
      (PiValue.apply_value M σ (fun _ => True) [dom f] ρ0 _ hf))).symm
    exact mem_congr_right (ed_tyv M (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have ht := PiRawMotiveAny.motive_mem_U M rfl σ f [] [] [dom f] []
    [PiPropPrefixAttack.datum] rfl (motive P f) pempty v (motive_mem P f) hf hz
  have he := PiRawMotiveAny.guarded_key M σ 1 (M.μ f []) (motive P f) []
    [dom f] ρ0 [PiPropPrefixAttack.datum] pempty hf hz ht
  have hden := Fapp_den M σ f [] [] [PiPropPrefixAttack.datum] ρ0
  change den M σ (push [PiPropPrefixAttack.datum] ρ0) (major f) =
    fapps (M.μ f []) [PiPropPrefixAttack.datum] at hden
  have hm := motive_apply P f [PiPropPrefixAttack.datum] pempty
    (TelFits.append hf ⟨by rw [hden]; exact hz, True.intro⟩)
  exact he.trans ((ed_congr M hm).trans (ed_tyv M domain_dich))

/-- Dropping or replacing the dependent index changes the actual data-valued guard. -/
theorem complete_key_required (P : Premises4) (f : Nat) :
    let C := PiRawMotiveAny.guarded (model P f) σ 1 ((model P f).μ f [])
      (motive P f) [] [dom f] ρ0
    ¬ Equiv (C (key [PiPropPrefixAttack.datum]) pempty) (C (key []) pempty) ∧
    ¬ Equiv (C (key [PiPropPrefixAttack.datum]) pempty) (C (key [dataVal 8 []]) pempty) := by
  have hn : ¬ Equiv domain pempty := by
    intro h
    exact not_mem_pempty (mem_congr_right h (mem_singleton.mpr (Equiv.refl datum)))
  exact ⟨fun h => hn ((used_key P f).symm.trans (h.trans (unused_arity P f pempty))),
    fun h => hn ((used_key P f).symm.trans (h.trans (invalid_index_guard P f pempty)))⟩

/-- Hidden readers and numeric relabelling retain executable success together
with the new data-valued semantics. The delta arm is a reader fixture only. -/
theorem hidden_data_builders (P : Premises4) : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, PiRawIHAttack.beta f, PiRawIHAttack.delta f, PiRawIHAttack.zeta f],
      funIHType (PiRawIHAttack.env f) 32 0 A (.bvar 0) 3 = some (PiRawIHAttack.ihExpr f) ∧
      ∃ ih, ih ∈ Ed (model P f) (den (model P f) σ (assignment P f) (PiRawIHAttack.ihExpr f)) ∧
        ¬ Equiv (fapps ih [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum,
          PiPropPrefixAttack.datum]) pempty := by
  intro f hf A hA
  exact ⟨PiRawIHAttack.hidden_builders f hf A hA, (inhabited P f).2.2.2.2⟩

/-- The original dependent-index admission and inserted-binder attack remain
valid while the any-sort fixture has a nonempty, universe-1 IH. -/
theorem indexed_data_insertion (P : Premises4) : ∀ f ∈ [1, 2, 987],
    fieldAnalyze (PiRawCtorAttack.paramEnv f) 32 f 0 1 1 3 (PiRawRenameAttack.indexed f) =
      .permitted (.recursive 3) [.bvar 0] ∧
    piTelescopeFuel (PiRawCtorAttack.paramEnv f) 31
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 3 (PiRawRenameAttack.indexed f))) =
        some ([.bvar 1, .bvar 2, .bvar 3], foldApps (.const f []) [.bvar 9, .bvar 0]) ∧
    ∃ ih, ih ∈ Ed (model P f) (den (model P f) σ (assignment P f) (PiRawIHAttack.ihExpr f)) ∧
      ¬ Equiv (fapps ih [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum,
        PiPropPrefixAttack.datum]) pempty := by
  intro f hf
  have h := PiRawRenameAttack.indexed_insertion f hf
  exact ⟨h.1, h.2.1, (inhabited P f).2.2.2.2⟩

/-- An ordinary parameterized motive whose codomain is data in universe 1. -/
def param_motive (P : Premises4) (f : Nat) : PSet.{4} :=
  piLam (PiRawParamsAttack.model P f) (σOf []) (fun _ => tyv domain)
    (push [tyv pempty] ρ0) (policyPi [PiRawParamsAttack.major f] (.sort (.succ .zero)))
def param_before (P : Premises4) (f : Nat) :=
  vcons (param_motive P f) (push [tyv pempty] ρ0)
def param_value (P : Premises4) (f : Nat) :=
  piLam (PiRawParamsAttack.model P f) (σOf []) (fun _ => pempty)
    (param_before P f) (PiRawParamsAttack.field f)
def param_context (P : Premises4) (f : Nat) :=
  vcons (param_value P f) (param_before P f)

/-- Original field admission, inserted motive, and executable success all
compose with the data-valued motive. These recursive domains are empty;
the separate `inhabited` theorem pays nonempty domains. -/
theorem original_data_builder (P : Premises4) (f : Nat) :
    let M := PiRawParamsAttack.model P f
    let ρ := param_context P f
    param_motive P f ∈ Ed M (den M (σOf []) (push [tyv pempty] ρ0)
      (policyPi [PiRawParamsAttack.major f] (.sort (.succ .zero)))) ∧
    ∃ ds args ih, ds.length = 3 ∧ args.length = 1 ∧
      piTelescopeFuel (PiRawCtorAttack.paramEnv f) 15
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 (PiRawRenameAttack.original f))) =
        some (ds, foldApps (.const f []) args) ∧
      funIHType (PiRawCtorAttack.paramEnv f) 15 1
        (Rcic.Declarative.lift 0 1 (PiRawRenameAttack.original f)) (.bvar 0) 3 = some ih ∧
      Equiv ((tel M (σOf []) ds args ρ).erasedIHType M
        (PiRawMotiveAny.guarded M (σOf []) 1 (M.μ f []) (param_motive P f)
          [tyv pempty] [] (push [tyv pempty] ρ0)) (ρ 0))
        (den M (σOf []) ρ ih) := by
  dsimp only
  let M := PiRawParamsAttack.model P f
  have hmo : param_motive P f ∈ Ed M (den M (σOf []) (push [tyv pempty] ρ0)
      (policyPi [PiRawParamsAttack.major f] (.sort (.succ .zero)))) := by
    refine piLam_mem M (σOf []) (envResp_const _) _ _ ?_
    apply piGood_policyPi
    intro ρ
    exact mem_congr_right (ed_tyv M (U4_dich 1)).symm (type_mem P)
  have hx : param_value P f ∈ Ed M (den M (σOf []) (param_context P f)
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 (PiRawRenameAttack.original f)))) := by
    change param_value P f ∈ Ed M (den M (σOf [])
      (push [param_value P f] (param_before P f))
      (Rcic.Declarative.lift 0 1 (PiRawParamsAttack.field f)))
    have hd : den M (σOf []) (push [param_value P f] (param_before P f))
        (Rcic.Declarative.lift 0 1 (PiRawParamsAttack.field f)) =
        den M (σOf []) (param_before P f) (PiRawParamsAttack.field f) :=
      den_lift0_push M (σOf []) [param_value P f] (param_before P f) (PiRawParamsAttack.field f)
    rw [hd]
    apply piLam_mem M (σOf []) (envResp_const pempty)
    intro x hx
    change x ∈ Ed M (tyv pempty) at hx
    exact (not_mem_pempty (mem_congr_right
      (ed_tyv M (Or.inl (fun _ h => (not_mem_pempty h).elim))) hx)).elim
  obtain ⟨_, _, _, hb, _⟩ := PiRawCtorAttack.param_checks f
  have he := PiRawIHAny.builder_original M rfl (σOf []) (fun _ => 0) f 0
    (PiValue.endValue (PiRawCtorAttack.paramPred P []) 1)
    (PiValue.endValue_resp _ _) .zero (.succ .zero)
    PiRawCtorAttack.params [] [tyv pempty] [param_motive P f] rfl
    (PiRawParamsAttack.family P f) (param_motive P f) (param_value P f) hmo
    (PiRawRenameAttack.type_facts f)
    (PiRawCtorAttack.paramSound P f (σOf []) (fun _ => 0)) hb
    16 3 0 0 1 (PiRawRenameAttack.original f) (.bvar 0) [] (Nat.le_refl 0) rfl
    (PiRawRenameAttack.admission f) (PiRawParamsAttack.checks f).2 rfl hx
  exact ⟨hmo, he⟩

/-- The data type used above cannot be silently lowered to Prop. -/
theorem type_not_prop (P : Premises4) : tyv domain ∉ U W4 0 := by
  intro h
  let M := mkM P (fun _ _ => pempty)
  have hm : datum ∈ Ed M (tyv domain) :=
    mem_congr_right (ed_tyv M domain_dich).symm (mem_singleton.mpr Equiv.rfl)
  exact dataVal_ne_pempty 17 [] (ed_of_mem_U0 M h hm)

/-- Reusing the old proof-only guard would lose the actual data-valued motive. -/
theorem old_guard_refuted (P : Premises4) (f : Nat) :
    ¬ Equiv (PiRawMotiveAny.guarded (model P f) σ 1 ((model P f).μ f [])
      (motive P f) [] [dom f] ρ0 (key [PiPropPrefixAttack.datum]) pempty)
      (PiRawMotive.guarded (model P f) σ ((model P f).μ f [])
        (motive P f) [] [dom f] ρ0 (key [PiPropPrefixAttack.datum]) pempty) := by
  intro h
  have hm := mem_congr_right (used_key P f).symm
    (mem_singleton.mpr (Equiv.refl datum))
  have hp := PiRawMotive.guarded_prop (model P f) σ ((model P f).μ f [])
    (motive P f) [] [dom f] ρ0 (key [PiPropPrefixAttack.datum]) pempty datum
    (mem_congr_right h hm)
  exact dataVal_ne_pempty 17 [] hp

end Rcic.F3.PSet.PiRawIHAnyAttack
