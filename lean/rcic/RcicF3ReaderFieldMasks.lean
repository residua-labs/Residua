import rcic.RcicF3ReaderTelescopeProvenance
import rcic.RcicF3RecFieldMaskFields
import rcic.RcicF3PiSmallMaskShape
import rcic.RcicF3EvalPlanNormal

/-!
# Actual bounded constructor fields produce the complete tuple mask

The induction follows the admitted field cache and its original bounded
field derivations. Both original assignments fit; the topology assignment
does not need to fit. A plain field uses the complete supported typing
induction and permits every equivalent ordinary representative. A recursive
field uses the executable reader's produced domain provenance, then its
actual cached Origin extends the masking context.

The complete normalized domains and child arguments remain in the cache.
Only the ordinary and recursive-domain denotations are compared. No child
key, result index, or recursive value is required to be independent of
earlier recursive values. This is a bounded theorem at the supplied full
valuation; its group wrapper supplies every semantic and typing input.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderFieldMasks
open Rcic.Declarative RawFamily RecFieldMask

/-- Original bounded field typings, at their literal ordinary prefixes,
produce the tuple mask. The successful reader is carried by the actual
cache; neither domain provenance nor a mask is an input. -/
theorem fields_mask (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (σ K : Nat → Nat)
    {R E : ResolvedEnv} {n fuel ar : Nat}
    (W : ReaderPacket.World P μ fd C σ K R)
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hb : BodiesOK E σ K)
    (hbody : ∀ r ls, transparentBody R r ls = transparentBody E r ls)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0) :
    {prior : Nat} → {ss : List FieldShape} → {Fs : List (Expr Nat)} →
    (p : EvalPlan.Fields R fuel fd.fref ar fd.params.length fd.indices.length prior ss Fs) →
    (∀ A ∈ Fs, InstOK E σ K A) →
    (Γ : LCtx) →
    (∀ k : Fin Fs.length, ∃ u : Level,
      ∃ d : HasTyT E n (BoundedPiSpine.context Γ (Fs.take k.val))
        (Fs[k]) (.sort u), LOKt σ 4 K d) →
    (marks : Marks) → (ρ η : Nat → PSet.{4}) →
    Context P μ fd C σ marks Γ ρ η →
    Fits (mkM P (table P μ fd C)) σ Γ ρ →
    Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ →
    (xs : List PSet.{4}) →
    TelFits (mkM P (table P μ fd C)) σ Fs ρ xs →
    TelFits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Fs ρ xs →
    PiSmallMaskShape.TupleMask (mkM P (table P μ fd C)) (mkM P μ) σ
      (EvalPlanNormal.specs p) ρ η xs := by
  intro prior ss Fs p
  induction p with
  | nil prior =>
      intro _ Γ _ marks ρ η _ _ _ xs hxs _
      cases xs with
      | nil => exact True.intro
      | cons => exact hxs.elim
  | @cons prior s A ss Fs head tail ih =>
      intro hI Γ htypes marks ρ η hctx hρC hρD xs hxsC hxsD
      cases xs with
      | nil => exact hxsC.elim
      | cons x xs =>
          obtain ⟨u, d, hd⟩ := htypes ⟨0, Nat.zero_lt_succ _⟩
          have htail : ∀ k : Fin Fs.length, ∃ v : Level,
              ∃ d' : HasTyT E n
                (BoundedPiSpine.context (.assumption A :: Γ) (Fs.take k.val))
                (Fs[k]) (.sort v), LOKt σ 4 K d' := by
            intro k
            have ht := htypes ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            simpa only [List.take_succ_cons, List.getElem_cons_succ,
              BoundedPiSpine.context] using ht
          have hIC : ∀ B ∈ Fs, InstOK E σ K B :=
            fun B hB => hI B (List.mem_cons_of_mem A hB)
          have hfC : Fits (mkM P (table P μ fd C)) σ
              (.assumption A :: Γ) (vcons x ρ) := ⟨hρC, hxsC.1⟩
          have hfD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ
              (.assumption A :: Γ) (vcons x ρ) := ⟨hρD, hxsD.1⟩
          cases head with
          | plain hfree =>
              change PiSmallMaskShape.TupleMask (mkM P (table P μ fd C)) (mkM P μ) σ
                (.plain A :: EvalPlanNormal.specs tail) ρ η (x :: xs)
              have he := RecFieldMaskSupport.domain_eq P μ fd C σ K hEC hED
                marks (fun _ => True) ρ ρ η (fun _ _ => Equiv.rfl) hρC hρD
                (RecFieldMaskSupport.context_of_same P μ fd C σ marks Γ ρ η hctx)
                hfree (fun _ _ => True.intro) d hd
              have hdom := ed_congr (mkM P (table P μ fd C)) he
              have hoff := den_off P μ fd.fref (ofFrame P μ fd C) σ η hfree
              change den (mkM P (table P μ fd C)) σ η A =
                den (mkM P μ) σ η A at hoff
              have hbase : Equiv
                  (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ η A))
                  (Ed (mkM P μ) (den (mkM P μ) σ η A)) := by
                rw [hoff, ed_mkM P (table P μ fd C) μ]
                exact Equiv.rfl
              refine ⟨hdom.trans hbase, ?_⟩
              intro y hxy
              exact ih hIC (.assumption A :: Γ) htail (ordinary marks)
                (vcons x ρ) (vcons y η)
                (context_ordinary P μ fd C σ marks Γ ρ η hctx
                  (.assumption A) x y hxy)
                hfC hfD xs hxsC.2 hxsD.2
          | recursive r =>
              change PiSmallMaskShape.TupleMask (mkM P (table P μ fd C)) (mkM P μ) σ
                (.recursive r.domains r.arguments :: EvalPlanNormal.specs tail) ρ η (x :: xs)
              have hdomains := ReaderPacket.domains_base_of_typing W hEC hED
                marks ρ η hρC hρD hctx d hd fuel r.domains
                (foldApps (.const fd.fref (canonL ar)) r.arguments) r.read r.domains_free
              have ho := cached_origin P μ fd C hC σ K hEC hED hb hbody r
                (hI A (List.mem_cons_self _ _)) h0 ρ x hxsC.1 hxsD.1
              refine ⟨hdomains, ?_⟩
              exact ih hIC (.assumption A :: Γ) htail (recursive _ marks)
                (vcons x ρ) (vcons pempty η)
                (context_recursive P μ fd C σ marks Γ ρ η hctx A x _ ho)
                hfC hfD xs hxsC.2 hxsD.2

end Rcic.F3.PSet.ReaderFieldMasks
