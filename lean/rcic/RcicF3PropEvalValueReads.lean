import rcic.RcicF3PropEvalReads
import rcic.RcicF3PropEvalValue

/-!
# Produced read congruence of the bounded indexed value

The bounded carrier reads the actual family value and the actual dependent
index types. Its semantic inputs retain the complete parameter slice, full
universe valuation and policy motive level. Those reads, together with the
actual evaluation reads, pay both inputs of the extractor's congruence law.
No evaluation existence, functionality or bound-congruence callback is a
premise of the resulting read law. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet
open Rcic.Declarative PiIndex

namespace PiRawMotiveAny

/-- All semantic inputs of the guarded bound respect extensional equality.
The complete key is preserved by equivalence of the parameter prefix. -/
theorem guarded_inputs_congr (M : Interp.{4}) (σ : Nat → Nat) (k : Nat)
    (F F' mo mo' : PSet.{4}) (ps ps' : List PSet.{4})
    (ds : List (Expr Nat)) (ρ ρ' : Nat → PSet.{4}) (i : Index.{4})
    (z z' : PSet.{4}) (hF : Equiv F F') (hmo : Equiv mo mo')
    (hps : LEq ps ps') (hρ : ∀ n, Equiv (ρ n) (ρ' n)) (hz : Equiv z z') :
    Equiv (guarded M σ k F mo ps ds ρ i z)
      (guarded M σ k F' mo' ps' ds ρ' i z') := by
  apply ed_congr M
  apply tyv_congr
  apply sep_congr
  · intro a b hab
    rintro ⟨is, hi, hfit, hmajor, ha⟩
    have hkey : key (ps ++ is) = key (ps' ++ is) :=
      (key_eq_iff _ _).mpr (LEq_append hps (LEq.refl is))
    have hfamily := (fapps_congr hF (ps ++ is)).trans
      (fapps_congr_args F' (LEq_append hps (LEq.refl is)))
    have hmotive := (fapps_congr hmo (is ++ [z])).trans
      (fapps_congr_args mo' (LEq_append (LEq.refl is)
        (show LEq [z] [z'] from ⟨hz, True.intro⟩)))
    exact ⟨is, hkey.symm.trans hi, TelFits_congr M σ ds hρ (LEq.refl is) hfit,
      mem_congr_left hz (mem_congr_right (ed_congr M hfamily) hmajor),
      mem_congr_left hab (mem_congr_right (ed_congr M hmotive) ha)⟩
  · intro a b hab
    rintro ⟨is, hi, hfit, hmajor, ha⟩
    have hkey : key (ps' ++ is) = key (ps ++ is) :=
      (key_eq_iff _ _).mpr (LEq_append hps.symm (LEq.refl is))
    have hfamily := (fapps_congr hF.symm (ps' ++ is)).trans
      (fapps_congr_args F (LEq_append hps.symm (LEq.refl is)))
    have hmotive := (fapps_congr hmo.symm (is ++ [z'])).trans
      (fapps_congr_args mo (LEq_append (LEq.refl is)
        (show LEq [z'] [z] from ⟨hz.symm, True.intro⟩)))
    exact ⟨is, hkey.symm.trans hi,
      TelFits_congr M σ ds (fun n => (hρ n).symm) (LEq.refl is) hfit,
      mem_congr_left hz.symm (mem_congr_right (ed_congr M hfamily) hmajor),
      mem_congr_left hab (mem_congr_right (ed_congr M hmotive) ha)⟩
  · exact Equiv.rfl

/-- With the family value held fixed, the bound's only table-dependent
operation is fitting the actual index telescope. -/
theorem guarded_agreeOn (P : Premises4)
    {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ₁ μ₂ S) (σ : Nat → Nat) (k : Nat)
    (F mo : PSet.{4}) (ps : List PSet.{4}) (ds : List (Expr Nat))
    (hds : RefsIn S ds) (ρ : Nat → PSet.{4}) (i : Index.{4}) (z : PSet.{4}) :
    Equiv (guarded (mkM P μ₁) σ k F mo ps ds ρ i z)
      (guarded (mkM P μ₂) σ k F mo ps ds ρ i z) := by
  apply ed_congr (mkM P μ₂)
  apply tyv_congr
  apply sep_congr
  · intro a b hab
    rintro ⟨is, hi, hfit, hmajor, ha⟩
    exact ⟨is, hi, (TelFits_agreeOn P h σ ds hds ρ is).mp hfit,
      hmajor, mem_congr_left hab ha⟩
  · intro a b hab
    rintro ⟨is, hi, hfit, hmajor, ha⟩
    exact ⟨is, hi, (TelFits_agreeOn P h σ ds hds ρ is).mpr hfit,
      hmajor, mem_congr_left hab ha⟩
  · exact Equiv.rfl

end PiRawMotiveAny

namespace PropEval

/-- The complete value reads the family and its index types in addition
to the actual mutual evaluation syntax. -/
structure EndpointReads (S : Nat → Prop) (C : Context) extends NodeReads S C : Prop where
  family : S C.node.a.family.ref
  indexTypes : RefsIn S C.node.a.family.indices

theorem EndpointReads.withModel {S : Nat → Prop} {C : Context}
    (h : EndpointReads S C) (M : Interp.{4}) : EndpointReads S (C.withModel M) :=
  ⟨h.toNodeReads.withModel M, h.family, h.indexTypes⟩

theorem EndpointReads.withValues {S : Nat → Prop} {C : Context}
    (h : EndpointReads S C) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms : List PSet.{4}) (hms : ms.length = C.node.a.constructors.length) :
    EndpointReads S (C.withValues ps mo ms hms) :=
  ⟨h.toNodeReads.withValues ps mo ms hms, h.family, h.indexTypes⟩

/-- The guard is responsive to semantic parameters and motive. Minor values
are deliberately absent from this particular bound. -/
theorem childCarrier_values_congr (C : Context) (v : Level) (i : Index.{4})
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps : LEq C.parameters ps') (hmo : Equiv C.motive mo') :
    Equiv (childCarrier C v i) (childCarrier (C.withValues ps' mo' ms' hms') v i) := by
  exact PiRawMotiveAny.guarded_inputs_congr C.M C.σ (evalTotal C.σ v)
    _ _ C.motive mo' C.parameters ps' C.node.a.family.indices
    (push C.parameters ρ0) (push ps' ρ0) i pempty pempty
    Equiv.rfl hmo hps (push_congr hps (fun _ => Equiv.rfl)) Equiv.rfl

/-- The bound reads exactly the family table entry and actual index types;
the recursor's extra motive universe slot remains unchanged. -/
theorem childCarrier_model_congr {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S)
    (hFamily : S C.node.a.family.ref) (hIndices : RefsIn S C.node.a.family.indices)
    (v : Level) (i : Index.{4}) :
    Equiv (childCarrier C v i) (childCarrier (C.withModel (mkM P μ₂)) v i) := by
  unfold childCarrier
  change Equiv
    (PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
      (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty)
    (PiRawMotiveAny.guarded (mkM P μ₂) C.σ (evalTotal C.σ v)
      (μ₂ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty)
  rw [hM]
  change Equiv
    (PiRawMotiveAny.guarded (mkM P μ₁) C.σ (evalTotal C.σ v)
      (μ₁ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty)
    (PiRawMotiveAny.guarded (mkM P μ₂) C.σ (evalTotal C.σ v)
      (μ₂ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty)
  rw [hAgree C.node.a.family.ref hFamily]
  exact PiRawMotiveAny.guarded_agreeOn P hAgree C.σ (evalTotal C.σ v)
    _ C.motive C.parameters C.node.a.family.indices hIndices (push C.parameters ρ0) i pempty

end PropEval

namespace PropEvalValue
open PropEval

/-- Produced semantic-input congruence of the actual bounded value. -/
theorem result_values_congr (C : Context) (v : Level) (i : Index.{4})
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps : LEq C.parameters ps') (hmo : Equiv C.motive mo')
    (hminors : LEq C.minors ms') :
    Equiv (result C v i) (result (C.withValues ps' mo' ms' hms') v i) :=
  result_congr C (C.withValues ps' mo' ms' hms') v v i i
    (childCarrier_values_congr C v i ps' mo' ms' hms' hps hmo)
    (fun z => Eval.values_iff (C := C) ps' mo' ms' hms' hps hmo hminors i z)

/-- Produced table-read congruence, with no bound-congruence or evaluation
comparison callback left for the caller. -/
theorem result_model_congr {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S)
    (hReads : EndpointReads S C) (v : Level) (i : Index.{4}) :
    Equiv (result C v i) (result (C.withModel (mkM P μ₂)) v i) :=
  result_congr C (C.withModel (mkM P μ₂)) v v i i
    (childCarrier_model_congr (C := C) P μ₁ μ₂ S hM hAgree hReads.family hReads.indexTypes v i)
    (fun z => Eval.model_iff (C := C) P μ₁ μ₂ S hM hAgree hReads.toNodeReads i z)

/-- The full scalar read law composes table agreement and equivalent actual
semantic inputs while preserving the complete key. -/
theorem result_read_congr {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S) (hReads : EndpointReads S C)
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps : LEq C.parameters ps') (hmo : Equiv C.motive mo')
    (hminors : LEq C.minors ms') (v : Level) (i : Index.{4}) :
    Equiv (result C v i)
      (result ((C.withModel (mkM P μ₂)).withValues ps' mo' ms' hms') v i) :=
  (result_model_congr (C := C) P μ₁ μ₂ S hM hAgree hReads v i).trans
    (result_values_congr (C.withModel (mkM P μ₂)) v i ps' mo' ms' hms' hps hmo hminors)

/-- Installing the recursor at its own fresh slot does not change its value.
The actual node supplies freshness; the read certificate names its reader
prefix rather than requiring agreement on the entire constant table. -/
theorem result_fresh_update {C : Context} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (hM : C.M = mkM P μ)
    (hReads : EndpointReads (Dom C.node.E0) C) (X : List Nat → PSet.{4})
    (v : Level) (i : Index.{4}) :
    Equiv (result C v i)
      (result (C.withModel (mkM P (upd μ C.rr X))) v i) :=
  result_model_congr (C := C) P μ (upd μ C.rr X) (Dom C.node.E0) hM
    (agreeOn_upd C.node.fresh μ X) hReads v i

/-- Equivalent input tuples preserve the complete key as well as the result. -/
theorem result_values_key_congr (C : Context) (v : Level)
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps : LEq C.parameters ps') (hmo : Equiv C.motive mo')
    (hminors : LEq C.minors ms') (is is' : List PSet.{4}) (his : LEq is is') :
    Equiv (result C v (key (C.parameters ++ is)))
      (result (C.withValues ps' mo' ms' hms') v (key (ps' ++ is'))) := by
  have hi : key (C.parameters ++ is) = key (ps' ++ is') :=
    (key_eq_iff _ _).mpr (LEq_append hps his)
  rw [← hi]
  exact result_values_congr C v _ ps' mo' ms' hms' hps hmo hminors

end PropEvalValue
end Rcic.F3.PSet
