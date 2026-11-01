import rcic.RcicF3PiRecBridge
import rcic.RcicF3PiEraseFixture
import rcic.RcicF3RoleAttacks
import rcic.RcicF3PiEraseCompileAttack
import rcic.RcicF3PiSmallAttack

/-! Adversarial fixtures for the dependent recursor bridge. Actual field
membership is inhabited; motives retain result indices and actual majors.
These tests do not discharge normalized extraction or the raw group theorem.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRecAttack
open Rcic.Declarative
open PiEraseFixture

/-- The output code observes both the result tag and the entire major. -/
def keep (z : PSet.{0}) : PSet.{0} := dataVal 29 [tagOf z, z]
def motive (i : Nat) (z : PSet.{0}) : PSet.{0} := singleton (dataVal 29 [ord i, z])
def depth3 : Expr Nat := .pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)))

/-- Depth three, varying indices and every numeric relabelling. -/
theorem dependent_major (M : Interp.{0}) (offset : Nat) :
    ∃ f, f ∈ Ed M ((nestedTel offset).erasedType M nestedFibre) ∧
      ihAtN keep 3 f ∈ Ed M ((nestedTel offset).erasedIHType M motive f) ∧
      Equiv ((nestedTel offset).erasedIH M keep f) (ihAtN keep 3 f) ∧
      ihChild (dataVal 12 [f]) depth3 f := by
  obtain ⟨f, hf⟩ := nested_product M offset
  have hg : ∀ a b, Equiv a b → Equiv (keep a) (keep b) :=
    fun _ _ h => dataVal_congr 29 ⟨tagOf_congr h, ⟨h, trivial⟩⟩
  have hC : ∀ i z, Dich (motive i z) :=
    fun i z => Or.inr (fun h => dataVal_ne_pempty 29 [ord i, z]
      (mem_singleton.mp h).symm)
  have hm : ∀ i z, z ∈ nestedFibre i → keep z ∈ motive i z := by
    intro i z hz
    have he := mem_singleton.mp hz
    exact mem_singleton.mpr (dataVal_congr 29
      ⟨(tagOf_congr he).trans (tagOf_dataVal i []), ⟨Equiv.rfl, trivial⟩⟩)
  have hp : ∀ i, pempty ∈ nestedFibre i → Equiv (keep pempty) pempty :=
    fun i hi => (dataVal_ne_pempty i [] (mem_singleton.mp hi).symm).elim
  exact ⟨f, hf,
    (nestedTel offset).ihAtN_mem M (nestedDomainsDich offset) nestedFibre
      nestedFibre_dich motive hC keep hg hm hp hf,
    (nestedTel offset).erasedIH_eq_ihAtN M (nestedDomainsDich offset)
      nestedFibre nestedFibre_dich keep hg hp hf,
    (nestedTel offset).ihChild_of_erased_mem M (nestedDomainsDich offset)
      nestedFibre hf (memT_dataVal (by simp)) depth3 rfl⟩

/-- A proof field erased to pempty cannot support arbitrary data IHs. -/
def proofTel : RecTel.{0,0} Nat 1 := .pi natDom (fun _ => .ret 0)
def proofFamily (_ : Nat) : PSet.{0} := tv True
def dataIH (_ : PSet.{0}) : PSet.{0} := dataVal 8 []

theorem proof_compatibility_necessary (M : Interp.{0}) :
    ∃ f, f ∈ Ed M (proofTel.erasedType M proofFamily) ∧
      ¬ Equiv (proofTel.erasedIH M dataIH f) (ihAtN dataIH 1 f) ∧
      ¬ (∀ i, pempty ∈ proofFamily i → Equiv (dataIH pempty) pempty) := by
  let f := proofTel.erasedEncode M (fun _ => pempty)
  have hf : f ∈ Ed M (proofTel.erasedType M proofFamily) :=
    proofTel.erasedEncode_mem M ⟨natDom_dich, fun _ => trivial⟩ proofFamily
      (fun _ => dich_tv True) (fun _ => pempty)
      (fun _ => mem_tv.mpr ⟨trivial, Equiv.rfl⟩)
  have hL : LamProof M (tyv natDom)
      (classFiber natDom (fun _ => pempty)) := by
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M natDom_dich) ha
    exact (classFiber_congr natDom _ hi.symm).trans (classFiber_at natDom _ i)
  have he : Equiv f pempty := by
    change Equiv (lamVal M (tyv natDom) (classFiber natDom (fun _ => pempty))) pempty
    unfold lamVal
    rw [cond_pos hL]
    exact Equiv.rfl
  have old : Equiv (ihAtN dataIH 1 f) pempty := ihAtN_empty_succ dataIH 0 he
  refine ⟨f, hf, ?_, ?_⟩
  · intro h
    let q := natCls 0
    have ha : PiCompile.classValue natDom q ∈ Ed M (tyv natDom) :=
      mem_congr_right (ed_tyv M natDom_dich).symm (PiCompile.classValue_mem natDom q)
    have hb : Equiv (fapp (proofTel.erasedIH M dataIH f)
        (PiCompile.classValue natDom q)) (dataVal 8 []) :=
      (beta_val M (fun _ _ h => classFiber_congr natDom _ h) ha).trans
        (classFiber_classValue natDom (fun _ => dataVal 8 []) q)
    exact dataVal_ne_pempty 8 [] (hb.symm.trans
      ((fapp_congr (h.trans old) Equiv.rfl).trans (fapp_pempty _)))
  · intro hp
    exact dataVal_ne_pempty 8 [] (hp 0 (mem_tv.mpr ⟨trivial, Equiv.rfl⟩))

/-- The actual mixed-universe Acc producer supplies the bridge inputs.
This is elementary composition with the landed Nat.lt fixture. -/
theorem acc_natLt (P : Premises4) (M : Interp.{4}) (x : Nat) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M ((PiSmallCompile.widen ((PiSmallAttack.accSig Nat.lt).tel ⟨x⟩ k)).erasedType M
        (PiSmallProducer.family M (PiSmallAttack.accSig Nat.lt)))) ∧
      (PiSmallAttack.accSig Nat.lt).code ⟨x⟩ f ∈
        PiSmallProducer.family M (PiSmallAttack.accSig Nat.lt) x ∧
      ∀ k, Equiv ((PiSmallCompile.widen ((PiSmallAttack.accSig Nat.lt).tel ⟨x⟩ k)).erasedIH M (fun _ => pempty) (f k))
          (ihAtN (fun _ => pempty) 2 (f k)) ∧
        ihAtN (fun _ => pempty) 2 (f k) ∈
          Ed M ((PiSmallCompile.widen ((PiSmallAttack.accSig Nat.lt).tel ⟨x⟩ k)).erasedIHType M
            (fun _ _ => tv True) (f k)) := by
  obtain ⟨f, hf, hc⟩ := PiSmallAttack.natLt_produced P M x
  refine ⟨f, hf, hc, fun k => ?_⟩
  let t := PiSmallCompile.widen ((PiSmallAttack.accSig Nat.lt).tel ⟨x⟩ k)
  have ht := PiSmallField.widen_dich ((PiSmallAttack.accSig Nat.lt).tel ⟨x⟩ k)
    ((PiSmallAttack.accInvariants Nat.lt).2 ⟨x⟩ k)
  have hX := PiSmallProducer.family_dich M (PiSmallAttack.accSig Nat.lt)
    (PiSmallAttack.accInvariants Nat.lt).1
  exact ⟨t.erasedIH_eq_ihAtN M ht _ hX (fun _ => pempty)
    (fun _ _ _ => Equiv.rfl) (fun _ _ => Equiv.rfl) (hf k),
    t.ihAtN_mem M ht _ hX (fun _ _ => tv True) (fun _ _ => dich_tv True)
      (fun _ => pempty) (fun _ _ _ => Equiv.rfl)
      (fun _ _ _ => mem_tv.mpr ⟨trivial, Equiv.rfl⟩)
      (fun _ _ => Equiv.rfl) (hf k)⟩

/-- The unbounded W producer pays actual product and constructor membership.
This is elementary composition; the representation has no finite height bound. -/
theorem w_bridge (P : Premises4) (M : Interp.{4}) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M ((PiSmallCompile.widen (PiSmallAttack.wSig.tel ⟨.node⟩ k)).erasedType M
        (PiSmallProducer.family M PiSmallAttack.wSig))) ∧
      PiSmallAttack.wSig.code ⟨.node⟩ f ∈ PiSmallProducer.family M PiSmallAttack.wSig .unit ∧
      ∀ k, Equiv ((PiSmallCompile.widen (PiSmallAttack.wSig.tel ⟨.node⟩ k)).erasedIH M id (f k))
          (ihAtN id 1 (f k)) ∧
        ihAtN id 1 (f k) ∈ Ed M ((PiSmallCompile.widen (PiSmallAttack.wSig.tel ⟨.node⟩ k)).erasedIHType M
          (fun i _ => PiSmallProducer.family M PiSmallAttack.wSig i) (f k)) ∧
        ihChild (PiSmallAttack.wSig.code ⟨.node⟩ f) (.pi (.sort .zero) (.sort .zero)) (f k) := by
  obtain ⟨f, hf, hc, _⟩ := PiSmallAttack.w_produced P M
  refine ⟨f, hf, hc, fun k => ?_⟩
  let t := PiSmallCompile.widen (PiSmallAttack.wSig.tel ⟨.node⟩ k)
  have ht := PiSmallField.widen_dich (PiSmallAttack.wSig.tel ⟨.node⟩ k)
    (PiSmallAttack.wInvariants.2 ⟨.node⟩ k)
  have hX := PiSmallProducer.family_dich M PiSmallAttack.wSig
    PiSmallAttack.wInvariants.1
  refine ⟨t.erasedIH_eq_ihAtN M ht _ hX id (fun _ _ h => h)
    (fun _ _ => Equiv.rfl) (hf k),
    t.ihAtN_mem M ht _ hX _ (fun i _ => hX i) id (fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ => Equiv.rfl) (hf k), ?_⟩
  apply t.ihChild_of_erased_mem M ht _ (hf k) ?_ (.pi (.sort .zero) (.sort .zero)) rfl
  cases k
  exact memT_dataVal (by simp)

/-- Empty dependent domains remain admitted, even for non-erased leaf IHs.
No inhabited-domain assumption is introduced. -/
theorem empty_domains (M : Interp.{4}) :
    ∃ f, f ∈ Ed M ((PiSmallCompile.widen PiSmallAttack.emptyTel).erasedType M PiSmallAttack.emptyFibre) ∧
      Equiv ((PiSmallCompile.widen PiSmallAttack.emptyTel).erasedIH M (fun _ => tyv pempty) f)
        (ihAtN (fun _ => tyv pempty) 2 f) ∧
      ihAtN (fun _ => tyv pempty) 2 f ∈
        Ed M ((PiSmallCompile.widen PiSmallAttack.emptyTel).erasedIHType M
          (fun i _ => PiSmallAttack.emptyFibre i) f) ∧
      ¬ Equiv (tyv (pempty : PSet.{4})) pempty := by
  obtain ⟨f, hf⟩ := PiSmallAttack.empty_product M
  have hd : PiSmallAttack.emptyTel.DomainsDich :=
    ⟨Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm),
      fun _ => ⟨Or.inr not_mem_pempty, fun _ => trivial⟩⟩
  have ht := PiSmallField.widen_dich PiSmallAttack.emptyTel hd
  have hX : ∀ i, Dich (PiSmallAttack.emptyFibre i) := fun _ =>
    Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm)
  have hp : ∀ i, pempty ∈ PiSmallAttack.emptyFibre i → Equiv (tyv pempty) pempty :=
    fun i hi => (tyv_ne_pempty _ (mem_singleton.mp hi).symm).elim
  let t := PiSmallCompile.widen PiSmallAttack.emptyTel
  exact ⟨f, hf, t.erasedIH_eq_ihAtN M ht _ hX (fun _ => tyv pempty)
    (fun _ _ _ => Equiv.rfl) hp hf,
    t.ihAtN_mem M ht _ hX _ (fun i _ => hX i) (fun _ => tyv pempty)
      (fun _ _ _ => Equiv.rfl) (fun _ _ _ => mem_singleton.mpr Equiv.rfl) hp hf,
    tyv_ne_pempty pempty⟩

/-- Elementary kernel computation: raw hidden syntax has depth zero,
while admission's normalized reader (RoleAttacks.*Read) has depth two.
The bridge cannot silently replace one depth by the other. -/
theorem hidden_depth_gap :
    (ihDepth Rcic.Declarative.Ann.paFieldDom,
      ihDepth PiSyntaxAttack.betaField,
      ihDepth PiSyntaxAttack.deltaField,
      ihDepth PiSyntaxAttack.zetaField) = (2, 0, 0, 0) := by
  decide

/-- Actual erased field membership and an IH disagreement for each typed hidden presentation.
The semantic empty-domain field is not identified with raw Acc's denotation. -/
theorem hidden_ih_disagreement (M : Interp.{0}) :
    pempty ∈ PiErasureAttack.raw M ∧
    ∀ T ∈ [PiSyntaxAttack.betaField, PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
      ¬ Equiv (ihAt (fun _ => tyv pempty) T pempty)
        (ihAt (fun _ => tyv pempty) Rcic.Declarative.Ann.paFieldDom pempty) := by
  refine ⟨(PiErasureAttack.nested_empty_domain.{0,0} M).1, ?_⟩
  intro T hT h
  have hd : ihDepth T = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with he | he | he <;> rw [he] <;> rfl
  rw [ihAt_eq_ihAtN, hd, ihAt_eq_ihAtN] at h
  change Equiv (tyv pempty) (ihAtN (fun _ => tyv pempty) 2 pempty) at h
  exact tyv_ne_pempty pempty (h.trans (ihAtN_empty_succ (fun _ => tyv pempty) 1 Equiv.rfl))

/-- A dependent depth-three field whose result indices are all positive. -/
def localField (M : Interp.{0}) (offset : Nat) : PSet.{0} :=
  (nestedTel (offset + 1)).erasedEncode M
    (fun q _ r => dataVal (offset + 1 + natOf q + natOf r) [])
/-- The surrounding constructor has an arbitrary tag. -/
def localMajor (M : Interp.{0}) (offset tag : Nat) : PSet.{0} :=
  dataVal tag [localField M offset]
/-- Index zero includes the surrounding major, outside its own descendants. -/
def localFamily (M : Interp.{0}) (offset tag i : Nat) : PSet.{0} :=
  if i = 0 then singleton (localMajor M offset tag) else nestedFibre i
/-- The candidate is deliberately wrong outside the current major's descendants. -/
def localMap (M : Interp.{0}) (offset tag : Nat) (y : PSet.{0}) : PSet.{0} :=
  cond M.dec (MemT y (localMajor M offset tag)) (keep y) pempty

/-- Genuine local membership with a refutation of the global mapping premise,
at depth three, varying indices, and arbitrary numeric constructor labels. -/
theorem local_soundness_strictly_weaker (M : Interp.{0}) (offset tag : Nat) :
    localField M offset ∈ Ed M ((nestedTel (offset + 1)).erasedType M (localFamily M offset tag)) ∧
      (∀ i y, MemT y (localMajor M offset tag) → y ∈ localFamily M offset tag i →
        localMap M offset tag y ∈ motive i y) ∧
      ihAtN (localMap M offset tag) 3 (localField M offset) ∈
        Ed M ((nestedTel (offset + 1)).erasedIHType M motive (localField M offset)) ∧
      ¬ (∀ i y, y ∈ localFamily M offset tag i → localMap M offset tag y ∈ motive i y) := by
  have hself : ∀ z : PSet.{0}, ¬ MemT z z := by
    intro z
    exact memT_wf.induction (C := fun y => ¬ MemT y y) z (fun y ih h => ih y h h)
  have hne : ∀ i, pempty ∉ localFamily M offset tag i := by
    intro i hx
    unfold localFamily at hx
    by_cases hi : i = 0
    · rw [if_pos hi] at hx
      exact dataVal_ne_pempty tag [localField M offset] (mem_singleton.mp hx).symm
    · rw [if_neg hi] at hx
      exact dataVal_ne_pempty i [] (mem_singleton.mp hx).symm
  have hX : ∀ i, Dich (localFamily M offset tag i) := fun i => Or.inr (hne i)
  have hf : localField M offset ∈
      Ed M ((nestedTel (offset + 1)).erasedType M (localFamily M offset tag)) := by
    apply (nestedTel (offset + 1)).erasedEncode_mem M (nestedDomainsDich (offset + 1))
      _ hX
    intro q _ r
    change dataVal (offset + 1 + natOf q + natOf r) [] ∈
      localFamily M offset tag (offset + 1 + natOf q + natOf r)
    unfold localFamily
    rw [if_neg (by omega : offset + 1 + natOf q + natOf r ≠ 0)]
    exact mem_singleton.mpr Equiv.rfl
  have hg : ∀ a b, Equiv a b →
      Equiv (localMap M offset tag a) (localMap M offset tag b) := by
    intro a b hab
    exact cond_congr
      ⟨fun h => MemT.congr_left hab h, fun h => MemT.congr_left hab.symm h⟩
      (dataVal_congr 29 ⟨tagOf_congr hab, ⟨hab, trivial⟩⟩) Equiv.rfl
  have hC : ∀ i y, Dich (motive i y) :=
    fun i y => Or.inr (fun h => dataVal_ne_pempty 29 [ord i, y]
      (mem_singleton.mp h).symm)
  have hm : ∀ i y, MemT y (localMajor M offset tag) →
      y ∈ localFamily M offset tag i → localMap M offset tag y ∈ motive i y := by
    intro i y hyz hy
    unfold localMap
    rw [cond_pos hyz]
    unfold localFamily at hy
    by_cases hi : i = 0
    · rw [if_pos hi] at hy
      exact (hself (localMajor M offset tag)
        (MemT.congr_left (mem_singleton.mp hy) hyz)).elim
    · rw [if_neg hi] at hy
      have he := mem_singleton.mp hy
      exact mem_singleton.mpr (dataVal_congr 29
        ⟨(tagOf_congr he).trans (tagOf_dataVal i []), ⟨Equiv.rfl, trivial⟩⟩)
  have hp : ∀ i, pempty ∈ localFamily M offset tag i →
      Equiv (localMap M offset tag pempty) pempty := fun i hi => (hne i hi).elim
  refine ⟨hf, hm, (nestedTel (offset + 1)).ihAtN_mem_below M
    (nestedDomainsDich (offset + 1)) _ hX motive hC _ hg
    (localMajor M offset tag) hm hp hf (memT_dataVal (by simp)), ?_⟩
  intro hglobal
  have hz : localMajor M offset tag ∈ localFamily M offset tag 0 := by
    unfold localFamily
    rw [if_pos rfl]
    exact mem_singleton.mpr Equiv.rfl
  have hb := hglobal 0 (localMajor M offset tag) hz
  unfold localMap at hb
  rw [cond_neg (hself (localMajor M offset tag))] at hb
  exact dataVal_ne_pempty 29 [ord 0, localMajor M offset tag] (mem_singleton.mp hb).symm

end Rcic.F3.PSet.PiRecAttack
