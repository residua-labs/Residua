import rcic.RcicF3PropEval
import rcic.RcicF3Agree

/-!
# Reads of the actual indexed evaluation relation

The actual RecNode and the complete universe valuation stay fixed. Changing
equivalent parameters, motive and minor values transports the mutual
evaluation judgment. Changing the constant table transports it on the
references of the original fields, stored minors and actual normalized
recursive domains and full argument lists.

The read certificate below is syntactic. Its production from the admitted
reader environment is separate; neither evaluation totality nor functionality
is a premise of the transport proof. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex
open Rcic.Model.PS (denRefs)

/-- Replace only the interpretation, retaining the actual node and full σ. -/
noncomputable def Context.withModel (C : Context) (M : Interp.{4}) : Context :=
  { C with M := M }

/-- Replace only semantic inputs, retaining their actual constructor census. -/
noncomputable def Context.withValues (C : Context) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms : List PSet.{4}) (hms : ms.length = C.node.a.constructors.length) : Context :=
  { C with parameters := ps, motive := mo, minors := ms, minor_length := hms }

namespace ReadTransport

theorem leq_take : (n : Nat) → {xs ys : List PSet.{4}} → LEq xs ys →
    LEq (xs.take n) (ys.take n)
  | 0, _, _, _ => True.intro
  | _ + 1, [], [], _ => True.intro
  | _ + 1, [], _ :: _, h => False.elim h
  | _ + 1, _ :: _, [], h => False.elim h
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, leq_take n h.2⟩

theorem leq_getD : (n : Nat) → {xs ys : List PSet.{4}} → LEq xs ys →
    Equiv (xs.getD n pempty) (ys.getD n pempty)
  | _, [], [], _ => Equiv.rfl
  | _, [], _ :: _, h => False.elim h
  | _, _ :: _, [], h => False.elim h
  | 0, _ :: _, _ :: _, h => h.1
  | n + 1, _ :: _, _ :: _, h => leq_getD n h.2

end ReadTransport

/-- Environment responsiveness of evaluation, including the actual typed IH
spine. Recursive children retain the complete normalized argument key. -/
theorem Eval.values_transport {C : Context}
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps' : LEq C.parameters ps') (hmo' : Equiv C.motive mo')
    (hminors : LEq C.minors ms') {i : Index.{4}} {z : PSet.{4}}
    (h : Eval C i z) : Eval (C.withValues ps' mo' ms' hms') i z := by
  let D := C.withValues ps' mo' ms' hms'
  change Eval D i z
  induction h using Eval.rec
    (motive_2 := fun fuel Mx acc ss T ρ xs ys out _ =>
      ∀ ρ' : Nat → PSet.{4}, (∀ n, Equiv (ρ n) (ρ' n)) →
        ∃ out', Inputs D fuel Mx acc ss T ρ' xs ys out' ∧ Equiv out out') with
  | root j ps xs ys fuel R out z hps hp hx hs hst hd hm hi hr ih =>
      have hpre : LEq (C.prefix j) (D.prefix j) :=
        ⟨hmo', ReadTransport.leq_take j.val hminors⟩
      have hρ : ∀ n, Equiv (C.rootCtx j ps n) (D.rootCtx j ps n) :=
        push_congr hpre (fun _ => Equiv.rfl)
      have hm' : D.minors.getD j.val pempty ∈
          Ed D.M (den D.M D.σ (D.rootCtx j ps) R) :=
        mem_congr_left (ReadTransport.leq_getD j.val hminors)
          (mem_congr_right (ed_congr C.M (den_congr C.M C.σ R hρ)) hm)
      obtain ⟨out', hi', _⟩ := ih (D.rootCtx j ps) hρ
      exact Eval.root (C := D) j ps xs ys fuel R out' z hps (hp.trans hps') hx hs hst hd hm' hi'
        (hr.trans (fapps_congr (ReadTransport.leq_getD j.val hminors) ys))
  | done fuel Mx acc T ρ =>
      rename_i ρ' hρ
      exact ⟨_, Inputs.done (C := D) fuel Mx acc T ρ', den_congr C.M C.σ _ hρ⟩
  | @plain fuel Mx acc A B ss ρ xs ys out x hx tail ih =>
      rename_i ρ' hρ
      have hx' := mem_congr_right (ed_congr C.M (den_congr C.M C.σ A hρ)) hx
      obtain ⟨out', ht, he⟩ := ih (vcons x ρ') (vcons_congr Equiv.rfl hρ)
      exact ⟨out', Inputs.plain (C := D) x hx' ht, he⟩
  | @recursive fuel Mx acc A B ss ρ xs ys out inner ihT hread x ih hx hih
      ds args hscan hdepth hargc hchildren tail ihChildren ihTail =>
      rename_i ρ' hρ
      have hρx : ∀ n, Equiv (vcons x ρ n) (vcons x ρ' n) :=
        vcons_congr Equiv.rfl hρ
      have hx' := mem_congr_right (ed_congr C.M (den_congr C.M C.σ A hρ)) hx
      have hih' := mem_congr_right (ed_congr C.M (den_congr C.M C.σ ihT hρx)) hih
      have hc : ∀ zs, TelFits D.M D.σ ds (vcons x ρ') zs →
          Eval D (key (args.map (den D.M D.σ (push zs (vcons x ρ')))))
            (fapps ih zs) := by
        intro zs hzs
        have hzs₀ := TelFits_congr C.M C.σ ds (fun n => (hρx n).symm)
          (LEq.refl zs) hzs
        have hk := read_congr C.M C.σ args (push_congr (LEq.refl zs) hρx)
        change Eval D (PiIndex.read C.M C.σ args (push zs (vcons x ρ')))
          (fapps ih zs)
        rw [← hk]
        exact ihChildren zs hzs₀
      obtain ⟨out', ht, he⟩ := ihTail (vcons ih (vcons x ρ'))
        (vcons_congr Equiv.rfl hρx)
      exact ⟨out', Inputs.recursive (C := D) inner ihT hread x ih hx' hih' ds args hscan hdepth hargc
        hc ht, he⟩

/-- The relation is invariant under equivalent semantic inputs. -/
theorem Eval.values_iff {C : Context}
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps' : LEq C.parameters ps') (hmo' : Equiv C.motive mo')
    (hminors : LEq C.minors ms') (i : Index.{4}) (z : PSet.{4}) :
    Eval C i z ↔ Eval (C.withValues ps' mo' ms' hms') i z := by
  constructor
  · exact fun h => Eval.values_transport (C := C) ps' mo' ms' hms' hps' hmo' hminors h
  · intro h
    exact Eval.values_transport (C := C.withValues ps' mo' ms' hms')
      C.parameters C.motive C.minors C.minor_length hps'.symm hmo'.symm hminors.symm h

/-- Denotation-aware expression support, including implicit literal aliases. -/
def ExprReads (S : Nat → Prop) (e : Expr Nat) : Prop :=
  ∀ r, r ∈ denRefs e → S r

namespace ReadTransport

/-- Syntax-only core of the input-spine support certificate. -/
def spineReads (S : Nat → Prop) (E0 : ResolvedEnv) (f nu np fuel : Nat) :
    Expr Nat → Expr Nat → List FieldShape → Expr Nat → Prop
  | Mx, acc, [], T =>
      ExprReads S (.app (foldApps Mx (familyIdx np T)) acc)
  | Mx, acc, .nonrecursive :: ss, .pi A B =>
      ExprReads S A ∧
      spineReads S E0 f nu np fuel (Rcic.Declarative.lift 0 1 Mx)
        (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss B
  | Mx, acc, .recursive inner :: ss, .pi A B =>
      ExprReads S A ∧
      (∀ ihT, funIHType E0 fuel np A Mx inner =
        some ihT → ExprReads S ihT) ∧
      (∀ ds args, piTelescopeFuel E0 fuel (Rcic.Declarative.lift 0 1 A) =
        some (ds, foldApps (.const f (canonL nu)) args) → RefsIn S ds ∧ RefsIn S args) ∧
      spineReads S E0 f nu np fuel (Rcic.Declarative.lift 0 2 Mx)
        (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss (Rcic.Declarative.lift 0 1 B)
  | _, _, _ :: _, _ => True

end ReadTransport

/-- Exactly the reads performed by any successful typed input spine with
this syntax. Failed reader calls make no semantic read obligation. The
definition projects only syntax, so semantic-context changes preserve it. -/
abbrev SpineReads (S : Nat → Prop) (C : Context) (fuel : Nat)
    (Mx acc : Expr Nat) (ss : List FieldShape) (T : Expr Nat) : Prop :=
  ReadTransport.spineReads S C.node.E0 C.node.a.family.ref
    C.node.a.family.member.arity C.node.a.family.parameters.length fuel Mx acc ss T

/-- Static support of the actual original syntax and every successful root
spine. This certificate contains no Eval, Inputs, semantic totality or
functionality premise. -/
structure NodeReads (S : Nat → Prop) (C : Context) : Prop where
  parameters : RefsIn S C.node.a.family.parameters
  fields : ∀ j, RefsIn S (C.node.a.constructorViews j).fields
  indices : ∀ j, RefsIn S (C.node.a.constructorViews j).resultIndices
  minors : RefsIn S C.node.a.minorTypes
  spines : ∀ j fuel,
    fieldShapesFuel C.node.E0 fuel C.node.a.family.ref C.node.a.family.member.arity
      C.node.a.family.parameters.length C.node.a.family.indices.length
      C.node.a.family.parameters.length (C.node.a.constructorViews j).fields =
      some (C.node.h14.shapesAt j) →
    SpineReads S C fuel (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j) (C.rootT j)

theorem NodeReads.withModel {S : Nat → Prop} {C : Context}
    (h : NodeReads S C) (M : Interp.{4}) : NodeReads S (C.withModel M) :=
  ⟨h.parameters, h.fields, h.indices, h.minors, h.spines⟩

theorem NodeReads.withValues {S : Nat → Prop} {C : Context}
    (h : NodeReads S C) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms : List PSet.{4}) (hms : ms.length = C.node.a.constructors.length) :
    NodeReads S (C.withValues ps mo ms hms) :=
  ⟨h.parameters, h.fields, h.indices, h.minors, h.spines⟩

namespace ReadTransport

theorem mem_den {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (h : AgreeOn μ₁ μ₂ S)
    (e : Expr Nat) (he : ExprReads S e) (ρ : Nat → PSet.{4})
    {x : PSet.{4}} (hx : x ∈ Ed C.M (den C.M C.σ ρ e)) :
    x ∈ Ed (mkM P μ₂) (den (mkM P μ₂) C.σ ρ e) := by
  rw [hM, den_agreeOn P h C.σ e he ρ] at hx
  exact hx

end ReadTransport

/-- The mutual relation reads only the explicitly recorded syntax. Literal
outputs and complete parameter/index keys are preserved by table transport. -/
theorem Eval.model_transport {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S) (hReads : NodeReads S C)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z) :
    Eval (C.withModel (mkM P μ₂)) i z := by
  let D := C.withModel (mkM P μ₂)
  change Eval D i z
  induction h using Eval.rec
    (motive_2 := fun fuel Mx acc ss T ρ xs ys out _ =>
      SpineReads S C fuel Mx acc ss T → Inputs D fuel Mx acc ss T ρ xs ys out) with
  | root j ps xs ys fuel R out z hps hp hx hs hst hd hm hi hr ih =>
      have hps' : TelFits D.M D.σ D.node.a.family.parameters ρ0 ps := by
        rw [hM] at hps
        exact (TelFits_agreeOn P hAgree C.σ _ hReads.parameters ρ0 ps).mp hps
      have hx' : TelFits D.M D.σ (D.node.a.constructorViews j).fields (push ps ρ0) xs := by
        rw [hM] at hx
        exact (TelFits_agreeOn P hAgree C.σ _ (hReads.fields j) (push ps ρ0) xs).mp hx
      have hm' : D.minors.getD j.val pempty ∈ Ed D.M (den D.M D.σ (D.rootCtx j ps) R) :=
        ReadTransport.mem_den P μ₁ μ₂ S hM hAgree R
          (hReads.minors R (List.getElem?_mem hst)) (C.rootCtx j ps) hm
      have hi' := ih (hReads.spines j fuel hs)
      have ht : Eval D (key (ps ++ (D.node.a.constructorViews j).resultIndices.map
          (den D.M D.σ (push xs (push ps ρ0))))) z :=
        Eval.root (C := D) j ps xs ys fuel R out z hps' hp hx' hs hst hd hm' hi' hr
      have he := map_den_agreeOn P hAgree C.σ _ (hReads.indices j) (push xs (push ps ρ0))
      rw [← hM] at he
      rw [he]
      exact ht
  | done fuel Mx acc T ρ =>
      rename_i hs
      have he := den_agreeOn P hAgree C.σ _ hs ρ
      rw [← hM] at he
      rw [he]
      exact Inputs.done (C := D) fuel Mx acc T ρ
  | @plain fuel Mx acc A B ss ρ xs ys out x hx tail ih =>
      rename_i hs
      obtain ⟨hA, htail⟩ := hs
      exact Inputs.plain (C := D) x
        (ReadTransport.mem_den P μ₁ μ₂ S hM hAgree A hA ρ hx) (ih htail)
  | @recursive fuel Mx acc A B ss ρ xs ys out inner ihT hread x ih hx hih
      ds args hscan hdepth hargc hchildren tail ihChildren ihTail =>
      rename_i hs
      obtain ⟨hA, hIH, hscanReads, htail⟩ := hs
      obtain ⟨hds, hargs⟩ := hscanReads ds args hscan
      have hc : ∀ zs, TelFits D.M D.σ ds (vcons x ρ) zs →
          Eval D (key (args.map (den D.M D.σ (push zs (vcons x ρ)))))
            (fapps ih zs) := by
        intro zs hzs
        have hzs₀ : TelFits C.M C.σ ds (vcons x ρ) zs := by
          rw [hM]
          exact (TelFits_agreeOn P hAgree C.σ ds hds (vcons x ρ) zs).mpr hzs
        have he := map_den_agreeOn P hAgree C.σ args hargs (push zs (vcons x ρ))
        rw [← hM] at he
        change Eval D (key (args.map (den (mkM P μ₂) C.σ (push zs (vcons x ρ)))))
          (fapps ih zs)
        rw [← he]
        exact ihChildren zs hzs₀
      exact Inputs.recursive (C := D) inner ihT hread x ih
        (ReadTransport.mem_den P μ₁ μ₂ S hM hAgree A hA ρ hx)
        (ReadTransport.mem_den P μ₁ μ₂ S hM hAgree ihT (hIH ihT hread) (vcons x ρ) hih)
        ds args hscan hdepth hargc hc (ihTail htail)

/-- Bidirectional read congruence under the same actual normalized descriptor. -/
theorem Eval.model_iff {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S) (hReads : NodeReads S C)
    (i : Index.{4}) (z : PSet.{4}) :
    Eval C i z ↔ Eval (C.withModel (mkM P μ₂)) i z := by
  constructor
  · exact fun h => h.model_transport P μ₁ μ₂ S hM hAgree hReads
  · intro h
    have ht := Eval.model_transport (C := C.withModel (mkM P μ₂)) P μ₂ μ₁ S rfl
      (fun r hr ls => (hAgree r hr ls).symm) (hReads.withModel (mkM P μ₂)) h
    have he : (C.withModel (mkM P μ₂)).withModel (mkM P μ₁) = C := by
      rw [← hM]
      rfl
    rw [he] at ht
    exact ht

/-- Checked composition of semantic-input responsiveness with the actual
syntax read law. The complete key and result are identical on both sides. -/
theorem Eval.read_iff {C : Context} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hM : C.M = mkM P μ₁) (hAgree : AgreeOn μ₁ μ₂ S) (hReads : NodeReads S C)
    (ps' : List PSet.{4}) (mo' : PSet.{4}) (ms' : List PSet.{4})
    (hms' : ms'.length = C.node.a.constructors.length)
    (hps' : LEq C.parameters ps') (hmo' : Equiv C.motive mo')
    (hminors : LEq C.minors ms') (i : Index.{4}) (z : PSet.{4}) :
    Eval C i z ↔
      Eval ((C.withModel (mkM P μ₂)).withValues ps' mo' ms' hms') i z :=
  (Eval.model_iff P μ₁ μ₂ S hM hAgree hReads i z).trans
    (Eval.values_iff (C := C.withModel (mkM P μ₂)) ps' mo' ms' hms' hps' hmo' hminors i z)

end Rcic.F3.PSet.PropEval
