import rcic.RcicF3PropEvalIH
import rcic.RcicF3PropEvalAttack
import rcic.RcicF3PiLeafParams

/-!
# Nonempty-domain composition of extraction, indexed IHs and actual evaluations

An auxiliary normalized proof field ranges over propositions. Its full leaf
key is the actual AccR empty-parameter key. The produced IH returns the
nonempty data value justified by that admitted group's evaluation relation.
This is a semantic IH composition witness, not a claim that this auxiliary
field is the AccR constructor field or that general evaluation is total.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalIHAttack
open Rcic.Declarative PiIndex PlanPropEndAttack

def domains : List (Expr Nat) := [.sort .zero]
def arguments : List (Expr Nat) := [.bvar 1]
def assignment : Nat → PSet.{4} := vcons parameter ρ0

noncomputable def ctx (P : Premises4) : PropEval.Context :=
  PropEvalAttack.context P (installed P)

noncomputable def telescope (P : Premises4) : RecTel.{4,5} Index.{4} domains.length :=
  tel (ctx P).M (ctx P).σ domains arguments assignment

noncomputable def leaf (P : Premises4) (i : Index.{4}) (_ : PSet.{4}) : PSet.{4} :=
  PropEvalExtract.value domain (PropEval.Eval (ctx P) i)

noncomputable def ihValue (P : Premises4) : PSet.{4} :=
  (telescope P).indexedIH (ctx P).M (leaf P) pempty

theorem reached_key (P : Premises4) (zs : List PSet.{4})
    (hzs : TelFits (ctx P).M (ctx P).σ domains assignment zs) :
    key (arguments.map (den (ctx P).M (ctx P).σ (push zs assignment))) = key [parameter] := by
  cases zs with
  | nil => exact False.elim hzs
  | cons z zs =>
      cases zs with
      | nil => rfl
      | cons z' zs => exact False.elim hzs.2

theorem inhabited_domain (P : Premises4) :
    TelFits (ctx P).M (ctx P).σ domains assignment [parameter] := by
  exact PropEvalAttack.parameters_fit P (installed P)

/-- Bounded existence is paid at every reached key by the actual AccR evaluation. -/
theorem bounded_exists (P : Premises4) (zs : List PSet.{4})
    (hzs : TelFits (ctx P).M (ctx P).σ domains assignment zs) :
    let i := key (arguments.map (den (ctx P).M (ctx P).σ (push zs assignment)))
    ∃ z, z ∈ domain ∧ PropEval.Eval (ctx P) i z := by
  dsimp only
  rw [reached_key P zs hzs]
  exact ⟨PropEvalAttack.canonical P, (PropEvalAttack.canonical_spec P).1,
    (PropEvalAttack.canonical_spec P).2⟩

/-- Extraction plus the generic IH computation theorem produces literal child evaluations. -/
theorem children (P : Premises4) (zs : List PSet.{4})
    (hzs : TelFits (ctx P).M (ctx P).σ domains assignment zs) :
    PropEval.Eval (ctx P)
      (key (arguments.map (den (ctx P).M (ctx P).σ (push zs assignment))))
      (fapps (ihValue P) zs) := by
  exact PropEval.indexed_children_of_bounded (ctx P) domains arguments assignment
    (fun _ => domain) pempty (bounded_exists P)
    (fun _ _ _ _ _ _ h h' => PropEvalAttack.functional P h h') zs hzs

/-- The ordinary proof field is accepted, and the generated data IH has its actual semantic type. -/
theorem typed_ih (P : Premises4) :
    pempty ∈ Ed (ctx P).M ((telescope P).erasedType (ctx P).M (fun _ => tv True)) ∧
      ihValue P ∈ Ed (ctx P).M
        ((telescope P).erasedIHType (ctx P).M (fun _ _ => domain) pempty) := by
  let M := (ctx P).M
  let t := telescope P
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M (ctx P).σ _ domains assignment
  have hx : pempty ∈ Ed M (t.erasedType M (fun _ => tv True)) :=
    (PiPropField.member_iff M t ht (fun _ => True) pempty).mpr
      ⟨Equiv.rfl, fun _ => True.intro⟩
  refine ⟨hx, ?_⟩
  apply t.indexedIH_mem_scoped M ht (fun _ => tv True) (fun _ => dich_tv True)
    (fun _ _ => domain) (fun _ _ => PiRawIHAnyAttack.domain_dich)
    (leaf P) (fun i => i = key [parameter]) ?_ ?_ hx
  · intro p
    obtain ⟨zs, hzs, he⟩ := PiSyntaxCompile.result_fits M (ctx P).σ
      (read M (ctx P).σ arguments) domains assignment p
    exact he.trans (reached_key P zs hzs)
  · intro i x hi _
    rw [hi]
    exact (PropEvalAttack.canonical_spec P).1

/-- The component has an inhabited application domain and a nonempty evaluated output. -/
theorem component_witness (P : Premises4) :
    TelFits (ctx P).M (ctx P).σ domains assignment [parameter] ∧
      ihValue P ∈ Ed (ctx P).M
        ((telescope P).erasedIHType (ctx P).M (fun _ _ => domain) pempty) ∧
      PropEval.Eval (ctx P) (key [parameter]) (fapp (ihValue P) parameter) ∧
      ¬ Equiv (fapp (ihValue P) parameter) pempty := by
  have he := children P [parameter] (inhabited_domain P)
  have ht := PropEvalAttack.eval_typed P he
  refine ⟨inhabited_domain P, (typed_ih P).2, he, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans h)

/-- The witness and conclusion have the same literal conjunction. -/
theorem component_nonrefutable (P : Premises4) :
    ¬ ((TelFits (ctx P).M (ctx P).σ domains assignment [parameter] ∧
      ihValue P ∈ Ed (ctx P).M
        ((telescope P).erasedIHType (ctx P).M (fun _ _ => domain) pempty) ∧
      PropEval.Eval (ctx P) (key [parameter]) (fapp (ihValue P) parameter) ∧
      ¬ Equiv (fapp (ihValue P) parameter) pempty) → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalIHAttack
