import rcic.RcicF3PiPropProducer
import rcic.RcicF3PiRecBridge
/-!
# Recursor soundness for the constructed proof family

Proof erasure identifies both a proof major and its recursive fields with
`pempty`, so membership descent is unavailable. Induction on `Valid` instead
constructs a joint family of validity and motive truth. The dependent IH is
then typed on this joint family, without assuming global mapping soundness.

The motive must be proof-valued, extensional in the actual major, and the
semantic minors must be typed. Deriving these conditions from admitted raw
syntax, the `anySort` case, and universal group production remain separate.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v w
theorem RecTel.erasedIH_read {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (hD : t.DomainsDich)
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i z, Dich (C i z))
    (x y : PSet.{u}) (hy : y ∈ Ed M (t.erasedIHType M C x)) :
    t.tel.All (fun p r => r ∈ C (t.result p)
      (t.tel.flatten (t.erasedRead M x) p)) (t.erasedRead M y) := by
  induction t generalizing x y with
  | ret i => exact mem_congr_right (ed_tyv M (hC i x)) hy
  | pi A B ih =>
    intro q
    have ha : PiCompile.classValue A q ∈ Ed M (tyv A) :=
      mem_congr_right (ed_tyv M hD.1).symm (PiCompile.classValue_mem A q)
    have hm := app_mem M (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hy ha
    have hv := mem_congr_right (ed_classFiber_classValue M A
      (fun q => Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q))))
      (fun _ => dich_ed M _) q) hm
    exact ih q (hD.2 q) _ _ hv
/-- A major-independent motive has the ordinary erased telescope type. -/
theorem RecTel.erasedIHType_const {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (C : I → PSet.{u}) (x : PSet.{u}) :
    t.erasedIHType M (fun i _ => C i) x = t.erasedType M C := by
  induction t generalizing x with
  | ret i => rfl
  | pi A B ih =>
    exact congrArg
      (fun F => piVal M (tyv A) (fun a => tyv (classFiber A F a)))
      (funext (fun q => congrArg (Ed M) (ih q (fapp x (PiCompile.classValue A q)))))
namespace PiPropRec
theorem produce {I : Type v} (M : Interp.{u}) (S : PiPropProducer.Sig.{u,v,w} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i z, Dich (C i z))
    (hresp : ∀ i x y, Equiv x y → Equiv (C i x) (C i y))
    (hProp : ∀ i x y, y ∈ C i x → Equiv y pempty)
    (minor : (s : S.Sh) → (S.Field s → PSet.{u}) →
      (S.Field s → PSet.{u}) → PSet.{u})
    (hminor : ∀ s f ih,
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (PiPropProducer.family S))) →
      (∀ k, ih k ∈ Ed M ((S.tel s k).erasedIHType M C (f k))) →
      minor s f ih ∈ C (S.out s) pempty) :
    ∀ i z, z ∈ PiPropProducer.family S i → pempty ∈ C i z := by
  have key : ∀ i, PiPropProducer.Valid S i → pempty ∈ C i pempty := by
    intro i hi
    induction hi with
    | sup s hg ih =>
      let X : I → PSet.{u} := fun j =>
        tv (PiPropProducer.Valid S j ∧ pempty ∈ C j pempty)
      have hX : ∀ j, Dich (X j) := fun _ =>
        Or.inl (fun _ h => (mem_tv.mp h).2)
      let v : (k : S.Field s) → PiTel.Value.{u,u+1}
          (S.tel s k).tel (fun _ => PSet.{u}) :=
        fun k => (S.tel s k).tel.unflatten (fun _ => pempty)
      let f : S.Field s → PSet.{u} :=
        fun k => (S.tel s k).erasedEncode M (v k)
      have hfX : ∀ k, f k ∈ Ed M ((S.tel s k).erasedType M X) := by
        intro k
        apply (S.tel s k).erasedEncode_mem M (hD s k) X hX
        apply (PiTel.all_iff _ _ _).mpr
        intro p
        rw [show v k = (S.tel s k).tel.unflatten (fun _ => pempty) from rfl,
          PiTel.flatten_unflatten]
        exact mem_tv.mpr ⟨⟨hg k p, ih k p⟩, Equiv.rfl⟩
      have hf : ∀ k, f k ∈ Ed M
          ((S.tel s k).erasedType M (PiPropProducer.family S)) := by
        intro k
        apply (S.tel s k).erasedEncode_mem M (hD s k)
          (PiPropProducer.family S) (PiPropProducer.family_dich S)
        apply (PiTel.all_iff _ _ _).mpr
        intro p
        rw [show v k = (S.tel s k).tel.unflatten (fun _ => pempty) from rfl,
          PiTel.flatten_unflatten]
        exact (PiPropProducer.family_iff S _ _).mpr ⟨hg k p, Equiv.rfl⟩
      have hmap : ∀ j y, y ∈ X j → pempty ∈ C j y := by
        intro j y hy
        obtain ⟨⟨_, hm⟩, he⟩ := mem_tv.mp hy
        exact mem_congr_right (hresp j pempty y he.symm) hm
      have hih : ∀ k, (S.tel s k).erasedIH M (fun _ => pempty) (f k) ∈
          Ed M ((S.tel s k).erasedIHType M C (f k)) := by
        intro k
        exact (S.tel s k).erasedIH_mem M (hD s k) X hX C hC
          (fun _ => pempty) hmap (hfX k)
      have hm := hminor s f
        (fun k => (S.tel s k).erasedIH M (fun _ => pempty) (f k)) hf hih
      exact mem_congr_left (hProp (S.out s) pempty _ hm) hm
  intro i z hz
  obtain ⟨hi, he⟩ := (PiPropProducer.family_iff S i z).mp hz
  exact mem_congr_right (hresp i pempty z he.symm) (key i hi)
end PiPropRec
end Rcic.F3.PSet
