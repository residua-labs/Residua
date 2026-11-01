import rcic.RcicF3RecFieldMaskTyping
import rcic.RcicF3EvalPlan
import rcic.RcicF3CandidateScope
import rcic.RcicF3BoundedPiSpine

/-!
# Cached constructor fields produce the local masking relation

The two original fitting tuples supply membership of each original field
in the source and enlarged models. Each recursive cache supplies its
actual reader, all normalized domains and the full family argument list.
Inhabited normalization and the produced telescope Origin pay the new
recursive local; ordinary locals retain their original value. Earlier
lookup facts are transported through the literal binder lifts.

The resulting Context holds at every ordinary constructor prefix. No
masked prefix is asserted to fit, no normalized-domain typing is assumed,
and no candidate closure is needed. Reader-environment transport is the
literal transparent-body equality supplied by an actual admitted group.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMask
open Rcic.Declarative RawFamily RecFieldOrigin

def recursive (m : Nat) (marks : Marks) : Marks
  | 0 => some m
  | i + 1 => marks i

def fieldMarks (s : FieldShape) (marks : Marks) : Marks :=
  match s with
  | .nonrecursive => ordinary marks
  | .recursive m => recursive m marks

def fieldValue (s : FieldShape) (x : PSet.{4}) : PSet.{4} :=
  match s with
  | .nonrecursive => x
  | .recursive _ => pempty

def extendMarks : List FieldShape → Marks → Marks
  | [], marks => marks
  | s :: ss, marks => extendMarks ss (fieldMarks s marks)

def maskedPush : List FieldShape → List PSet.{4} → (Nat → PSet.{4}) → Nat → PSet.{4}
  | [], _, η => η
  | _ :: _, [], η => η
  | s :: ss, x :: xs, η => maskedPush ss xs (vcons (fieldValue s x) η)

/-- A recursive binder is justified by its actual field Origin. Its
earlier local types still denote their original values after the lift. -/
theorem context_recursive (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks Γ ρ η) (A : Expr Nat) (x : PSet.{4}) (m : Nat)
    (hx : Origin (mkM P μ) fd C m
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A)) x) :
    Context P μ fd C σ (recursive m marks) (.assumption A :: Γ)
      (vcons x ρ) (vcons pempty η) := by
  intro i B hi
  cases i with
  | zero =>
      change some (Declarative.lift 0 1 A) = some B at hi
      cases hi
      change Equiv pempty pempty ∧ Origin (mkM P μ) fd C m
        (Ed (mkM P (table P μ fd C))
          (den (mkM P (table P μ fd C)) σ (vcons x ρ) (Declarative.lift 0 1 A)))
        (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
          (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
            σ (vcons x ρ) (Declarative.lift 0 1 A))) x
      simpa only [den_lift, liftρ_zero, shiftρ_one_cons] using And.intro Equiv.rfl hx
  | succ i =>
      rw [lookupType_cons_succ] at hi
      cases ht : lookupType Γ i with
      | none => rw [ht] at hi; cases hi
      | some T =>
          rw [ht] at hi
          cases hi
          change Value (mkM P μ) fd C (marks i)
            (Ed (mkM P (table P μ fd C))
              (den (mkM P (table P μ fd C)) σ (vcons x ρ) (Declarative.lift 0 1 T)))
            (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
                σ (vcons x ρ) (Declarative.lift 0 1 T))) (ρ i) (η i)
          simpa only [den_lift, liftρ_zero, shiftρ_one_cons] using h i T ht

private theorem field_normalized (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (X : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P (table P μ fd X)) σ K E n) (hb : BodiesOK E σ K)
    (ar fuel : Nat) (A : Expr Nat) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel A = some (ds, foldApps (.const fd.fref (canonL ar)) args))
    (hI : InstOK E σ K A) (hds : ∀ e ∈ ds, occursConst fd.fref e = false)
    (hargs : ∀ e ∈ args, occursConst fd.fref e = false)
    (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (table P μ fd X)) (den (mkM P (table P μ fd X)) σ ρ A)) :
    let t := PiSyntaxCompile.compile (mkM P μ) σ (PiIndependent.leafArgs P μ σ args) ds ρ
    Equiv (Ed (mkM P μ) (t.erasedType (mkM P μ)
      (RecFieldSeparation.leaf P μ fd X ((canonL ar).map (evalTotal σ)))))
      (Ed (mkM P (table P μ fd X)) (den (mkM P (table P μ fd X)) σ ρ A)) := by
  dsimp only
  let M := mkM P μ
  let MX := mkM P (table P μ fd X)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ args) ds ρ
  have hn := den_piTelescope_of_mem MX σ K hE hb fuel A ds
    (foldApps (.const fd.fref (canonL ar)) args) ρ x hw hI hx
  have hc := PiIndependent.recursiveField_ed P μ fd.fref (ofFrame P μ fd X) σ
    (canonL ar) ds args hds hargs ρ
  change Equiv (Ed M (t.erasedType MX
      (RecFieldSeparation.leaf P μ fd X ((canonL ar).map (evalTotal σ)))))
    (Ed MX (den MX σ ρ (policyPi ds (foldApps (.const fd.fref (canonL ar)) args)))) at hc
  rw [RecFieldSeparation.erasedType_table P (table P μ fd X) μ t] at hc
  exact hc.trans (ed_congr MX hn)

/-- At the supplied positive DATA stage, the original field member supplies
both normalizations with the cache's parameter/index key retained. -/
theorem cached_origin (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (σ K : Nat → Nat)
    {R E : ResolvedEnv} {n fuel ar prior inner : Nat} {A : Expr Nat}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hb : BodiesOK E σ K)
    (hbody : ∀ r ls, transparentBody R r ls = transparentBody E r ls)
    (r : EvalPlan.Recursive R fuel fd.fref ar fd.params.length fd.indices.length prior A inner)
    (hI : InstOK E σ K A)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hxC : x ∈ Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
    (hxD : x ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A)) :
    Origin (mkM P μ) fd C inner
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A)) x := by
  let M := mkM P μ
  let vs := (canonL ar).map (evalTotal σ)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ r.arguments) r.domains ρ
  have hr := (CandidateScope.piTelescopeFuel_of_transparentBody_eq hbody fuel A).symm.trans r.read
  have hNC := field_normalized P μ fd C σ K hEC hb ar fuel A r.domains r.arguments
    hr hI r.domains_free r.arguments_free ρ x hxC
  have hND := field_normalized P μ fd (RawFamilyEnlarge.enlarge fd C) σ K hED hb
    ar fuel A r.domains r.arguments hr hI r.domains_free r.arguments_free ρ x hxD
  dsimp only at hNC hND
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ
    (PiIndependent.leafArgs P μ σ r.arguments) r.domains ρ
  have hl : ∀ p, (t.result p).length = (fd.params ++ fd.indices).length :=
    PiPropField.compile_result_property M σ (PiIndependent.leafArgs P μ σ r.arguments)
      (fun xs => xs.length = (fd.params ++ fd.indices).length)
      (fun _ => (List.length_map _ _).trans
        (r.argument_count.trans (List.length_append fd.params fd.indices).symm)) r.domains ρ
  have ho := (RecFieldOriginSyntax.of_telescope P μ fd C hC vs h0 t ht hl x
    (mem_congr_right hNC.symm hxC)).transport hNC hND Equiv.rfl
  simpa only [r.depth] using ho

/-- The field certificate determines the local mode and erased value.
The recursive branch's Origin is produced from the actual cache. -/
theorem cached_field (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (σ K : Nat → Nat)
    {R E : ResolvedEnv} {n fuel ar prior : Nat} {A : Expr Nat} {s : FieldShape}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hb : BodiesOK E σ K)
    (hbody : ∀ r ls, transparentBody R r ls = transparentBody E r ls)
    (p : EvalPlan.Field R fuel fd.fref ar fd.params.length fd.indices.length prior A s)
    (hI : InstOK E σ K A)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4})
    (hctx : Context P μ fd C σ marks Γ ρ η) (x : PSet.{4})
    (hxC : x ∈ Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
    (hxD : x ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A)) :
    Context P μ fd C σ (fieldMarks s marks) (.assumption A :: Γ)
      (vcons x ρ) (vcons (fieldValue s x) η) := by
  cases p with
  | plain hfree =>
      exact context_ordinary P μ fd C σ marks Γ ρ η hctx
        (.assumption A) x x Equiv.rfl
  | recursive r =>
      exact context_recursive P μ fd C σ marks Γ ρ η hctx A x _
        (cached_origin P μ fd C hC σ K hEC hED hb hbody r hI h0 ρ x hxC hxD)

/-- At the supplied positive DATA stage, the cached fields and two original
fitting tuples produce the relation at the requested prefix. -/
theorem fields_contexts (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (σ K : Nat → Nat)
    {R E : ResolvedEnv} {n fuel ar : Nat}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hb : BodiesOK E σ K)
    (hbody : ∀ r ls, transparentBody R r ls = transparentBody E r ls)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0) :
    {prior : Nat} → {ss : List FieldShape} → {Fs : List (Expr Nat)} →
    EvalPlan.Fields R fuel fd.fref ar fd.params.length fd.indices.length prior ss Fs →
    (∀ A ∈ Fs, InstOK E σ K A) →
    (marks : Marks) → (Γ : LCtx) → (ρ η : Nat → PSet.{4}) →
    Context P μ fd C σ marks Γ ρ η → (xs : List PSet.{4}) →
    TelFits (mkM P (table P μ fd C)) σ Fs ρ xs →
    TelFits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Fs ρ xs →
    ∀ k, k ≤ Fs.length →
      Context P μ fd C σ (extendMarks (ss.take k) marks)
        (BoundedPiSpine.context Γ (Fs.take k)) (push (xs.take k) ρ)
        (maskedPush (ss.take k) (xs.take k) η)
  | _, _, _, .nil _, _, marks, Γ, ρ, η, hctx, xs, hxs, _, k, hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hctx
  | _, _, _, .cons head tail, hI, marks, Γ, ρ, η, hctx, [], hxs, _, _, _ => by cases hxs
  | _, s :: ss, A :: Fs, .cons head tail, hI, marks, Γ, ρ, η, hctx, x :: xs, hxs, hys, k, hk => by
      cases k with
      | zero => exact hctx
      | succ k =>
          have hctx' := cached_field P μ fd C hC σ K hEC hED hb hbody
            head (hI A (List.mem_cons_self _ _)) h0 marks Γ ρ η hctx x hxs.1 hys.1
          exact fields_contexts P μ fd C hC σ K hEC hED hb hbody h0 tail
            (fun B hB => hI B (List.mem_cons_of_mem _ hB))
            (fieldMarks s marks) (.assumption A :: Γ) (vcons x ρ)
            (vcons (fieldValue s x) η) hctx' xs hxs.2 hys.2 k (Nat.le_of_succ_le_succ hk)

end Rcic.F3.PSet.RecFieldMask
