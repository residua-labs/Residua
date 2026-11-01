import rcic.RcicF3PropEval
import rcic.RcicF3PiTypedExt

/-!
# Functionality of the indexed singleton-Prop evaluation relation

The mutual comparison aligns actual typed IHs by telescope extensionality
and recursive child evaluations. The input-spine comparison needs equivalence
of its ordinary fields, but no proof-field restriction. At roots, a
singleton constructor census and a comparison of the original fields at equal
full result keys supply that equivalence. A PropTel corollary pays the field
comparison on the existing proof-field face. Root production from general
admission and evaluation existence remain separate. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Fitting proof-field tuples agree after transport of their parameters. -/
theorem fields_equiv_of_propTel (C : Context)
    (hprop : ∀ (j : Fin C.node.a.constructors.length) ps,
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      LEq ps C.parameters → PropTel C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0))
    (j : Fin C.node.a.constructors.length) (ps ps' xs xs' : List PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 ps)
    (hparameters : LEq ps C.parameters)
    (heps : LEq ps ps')
    (hx : TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs)
    (hx' : TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps' ρ0) xs') :
    LEq xs xs' := by
  have ht := TelFits_congr C.M C.σ (C.node.a.constructorViews j).fields
    (push_congr heps.symm (fun _ => Equiv.rfl)) (LEq.refl xs') hx'
  have he := propTel_fits C.M C.σ _ _ xs (hprop j ps hps hparameters) hx
  have he' := propTel_fits C.M C.σ _ _ xs' (hprop j ps hps hparameters) ht
  have hl : xs.map (fun _ => pempty) = xs'.map (fun _ => pempty) := by
    simp only [List.map_const', hx.length, hx'.length]
  rw [hl] at he
  exact he.trans he'.symm

/-- Actual root-field comparison and recursive IH comparison produce functionality.
The full result key is available to a data-revealed-index comparator. -/
theorem Eval.functional_of_field_comparison (C : Context)
    (hone : C.node.a.constructors.length ≤ 1)
    (hcompare : ∀ (j : Fin C.node.a.constructors.length) ps ps' xs xs',
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps' →
      LEq ps C.parameters → LEq ps' C.parameters →
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs →
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps' ρ0) xs' →
      key (ps ++ (C.node.a.constructorViews j).resultIndices.map
        (den C.M C.σ (push xs (push ps ρ0)))) =
        key (ps' ++ (C.node.a.constructorViews j).resultIndices.map
          (den C.M C.σ (push xs' (push ps' ρ0)))) → LEq xs xs')
    {i : Index.{4}} {z z' : PSet.{4}}
    (h : Eval C i z) (h' : Eval C i z') : Equiv z z' := by
  suffices H : ∀ i z (h : Eval C i z),
      ∀ i' z', i = i' → Eval C i' z' → Equiv z z' from H i z h i z' rfl h'
  intro i z h
  induction h using Eval.rec
    (motive_2 := fun fuel Mx acc ss T ρ xs ys out _ =>
      ∀ (fuel' : Nat) (ρ' : Nat → PSet.{4})
        (xs' ys' : List PSet.{4}) (out' : PSet.{4}),
        (∀ n, Equiv (ρ n) (ρ' n)) → LEq xs xs' →
        Inputs C fuel' Mx acc ss T ρ' xs' ys' out' → LEq ys ys') with
  | root j ps xs ys fuel R out z hps hp hx hs hst hd hm hi hr ih =>
      intro i' z' hkey h'
      cases h' with
      | root j' ps' xs' ys' fuel' R' out' z' hps' hp' hx' hs' hst' hd' hm' hi' hr' =>
          have hj : j = j' := Fin.ext (by have := j.isLt; have := j'.isLt; omega)
          subst j'
          have heps : LEq ps ps' := hp.trans hp'.symm
          have hexs := hcompare j ps ps' xs xs' hps hps' hp hp' hx hx' hkey
          have heρ : ∀ n, Equiv (C.rootCtx j ps n) (C.rootCtx j ps' n) :=
            push_congr (LEq.refl (C.prefix j))
              (push_congr heps (fun _ => Equiv.rfl))
          have heys := ih fuel' (C.rootCtx j ps') xs' ys' out' heρ hexs hi'
          exact hr.trans ((fapps_congr_args _ heys).trans hr'.symm)
  | done fuel Mx acc T ρ =>
      rename_i fuel' ρ' xs' ys' out' hρ hxs hother
      cases hother
      trivial
  | @plain fuel Mx acc A B ss ρ xs ys out x hx tail ih =>
      rename_i fuel' ρ' xs' ys' out' hρ hxs hother
      cases hother with
      | plain x' hx' tail' =>
          exact ⟨hxs.1, ih _ _ _ _ _ (vcons_congr hxs.1 hρ) hxs.2 tail'⟩
  | @recursive fuel Mx acc A B ss ρ xs ys out inner ihT hread x ih hx hih
      ds args hscan hdepth hargc hchildren tail ihChildren ihTail =>
      rename_i fuel' ρ' xs' ys' out' hρ hxs hother
      cases hother with
      | recursive _ ihT' hread' x' ih' hx' hih' ds' args' hscan' hdepth' hargc' hchildren' tail' =>
          have hd : ds = ds' := (PiTypedExt.read_unique C.node.E0 hscan hscan').1
          subst ds'
          have hb : ihT = ihT' := PiTypedExt.builder_unique C.node.E0 hread hread'
          subst ihT'
          have heρ : ∀ n, Equiv (vcons x ρ n) (vcons x' ρ' n) :=
            vcons_congr hxs.1 hρ
          have hiht : ih' ∈ Ed C.M (den C.M C.σ (vcons x ρ) ihT) :=
            mem_congr_right (ed_congr C.M (den_congr C.M C.σ ihT heρ)).symm hih'
          have ha : args = args' := by
            have he := congrArg appsSpine (PiTypedExt.read_unique C.node.E0 hscan hscan').2
            simpa only [appsSpine_foldApps, appsSpine, List.nil_append] using congrArg Prod.snd he
          subst args'
          have heih : Equiv ih ih' := by
            apply PiTypedExt.builder_ext C.M C.σ C.node.E0 fuel
              C.node.a.family.parameters.length A Mx ds args C.node.a.family.ref
              (canonL C.node.a.family.member.arity) hscan ihT
              (by simpa only [hdepth] using hread) (vcons x ρ) hih hiht
            intro zs hzs
            have hzs' := TelFits_congr C.M C.σ ds heρ (LEq.refl zs) hzs
            have hk : key (args.map (den C.M C.σ (push zs (vcons x ρ)))) =
                key (args.map (den C.M C.σ (push zs (vcons x' ρ')))) :=
              read_congr C.M C.σ args (push_congr (LEq.refl zs) heρ)
            exact ihChildren zs hzs _ _ hk (hchildren' zs hzs')
          exact ⟨hxs.1, heih,
            ihTail _ _ _ _ _ (vcons_congr heih heρ) hxs.2 tail'⟩

/-- The existing proof-field consequence supplies the root comparison without erasing IHs. -/
theorem Eval.functional_of_proof_fields (C : Context)
    (hone : C.node.a.constructors.length ≤ 1)
    (hprop : ∀ (j : Fin C.node.a.constructors.length) ps,
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      LEq ps C.parameters →
      PropTel C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0))
    {i : Index.{4}} {z z' : PSet.{4}}
    (h : Eval C i z) (h' : Eval C i z') : Equiv z z' := by
  exact h.functional_of_field_comparison C hone
    (fun j ps ps' xs xs' hps _ hp hp' hx hx' _ =>
      fields_equiv_of_propTel C hprop j ps ps' xs xs' hps hp
        (hp.trans hp'.symm) hx hx') h'

end Rcic.F3.PSet.PropEval
