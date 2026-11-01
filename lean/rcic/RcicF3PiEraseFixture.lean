import rcic.RcicF3PiEraseProducer
import rcic.RcicF3PiFieldFixture

/-!
# Non-vacuity and attacks for the proof-erasing indexed construction

These semantic fixtures use Ed-compatible domains. Accessibility retains
both dependent binders and proof-valued constructor erasure. The mixed
accessibility attack tests result indices before value erasure.
No raw syntax or universal StepAG bridge is claimed. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiEraseFixture
open PiFieldFixture

/-- Positive ordinals supply infinitely many nonproof arguments. -/
def natDom : PSet.{0} := mk (ULift.{0} Nat) (fun n => ord (n.down + 1))

def natOf : FBr natDom → Nat :=
  Quotient.lift (fun n => n.down) (fun _ _ h => Nat.succ.inj (ord_inj h))

def natCls (n : Nat) : FBr natDom := Quotient.mk (FSetoid natDom) ⟨n⟩

/-- The older literal-product domain cannot be substituted for an Ed
argument domain: it mixes a proof value with nonproof values. -/
theorem literalNat_not_dich : ¬ Dich fnDom.{0} := by
  intro h
  rcases h with h | h
  · have he : Equiv (ord 1 : PSet.{0}) (ord 0) := h _ ⟨⟨1⟩, Equiv.rfl⟩
    exact Nat.noConfusion (ord_inj he)
  · exact h ⟨⟨0⟩, Equiv.rfl⟩

/-- The replacement argument domain has the model's dichotomy invariant. -/
theorem natDom_dich : Dich natDom := by
  apply Or.inr
  intro ⟨n, hn⟩
  have h : n.down + 1 = 0 := ord_inj hn
  exact (Nat.noConfusion h)

/-- Actual Acc constructor field: Π y, R y x → Acc R y. -/
def accTel (R : Nat → Nat → Prop) (x : Nat) : RecTel Nat 2 :=
  .pi natDom (fun q => .pi (proofDom (R (natOf q) x)) (fun _ => .ret (natOf q)))

/-- Proof-valued codes deliberately do not carry a value-level index tag.
IndexedValid supplies the independent result-index discipline. -/
def accSig (R : Nat → Nat → Prop) : RecSig Nat where
  Sh := Nat
  Field := fun _ => PUnit
  depth := fun _ _ => 2
  tel := fun x _ => accTel R x
  out := id
  code := fun _ _ => pempty
  tag := fun _ _ => True
  tag_congr := fun _ _ _ _ h => h
  code_tag := fun _ _ => trivial
  code_congr := fun _ _ _ _ => Equiv.rfl

/-- All constructor codes are proofs; this is immediate from the definition. -/
theorem accCodeDich (R : Nat → Nat → Prop) : (accSig R).CodeDich :=
  Or.inl (fun _ _ => Equiv.rfl)

/-- Every argument domain is dichotomous, including false proof domains. -/
theorem accDomainsDich (R : Nat → Nat → Prop) :
    ∀ s k, ((accSig R).tel s k).DomainsDich :=
  fun _ _ => ⟨natDom_dich, fun _ => ⟨Or.inl (fun _ h =>
    let ⟨_, he⟩ := h; he.symm), fun _ => trivial⟩⟩

noncomputable def accTree (M : Interp.{0}) (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    GT ((accSig R).erasedPiSig M).toGSig :=
  Acc.ndrec (C := fun _ => GT ((accSig R).erasedPiSig M).toGSig)
    (fun x _ ih => .sup x (fun p => ih (natOf p.2.1) (proofOf _ p.2.2.1))) h

/-- Accessibility supplies all children of the index-correct tree. -/
theorem accTree_valid (M : Interp.{0}) (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    (accSig R).IndexedValid M x (accTree M R x h) := by
  induction h with
  | intro x hx ih =>
    apply RecSig.IndexedValid.sup
    intro k p
    exact ih (natOf p.1) (proofOf _ p.2.1)

/-- Conversely, no inaccessible index acquires a valid erased tree. -/
theorem accTree_accessible (M : Interp.{0}) (R : Nat → Nat → Prop) (x : Nat)
    (w : GT ((accSig R).erasedPiSig M).toGSig)
    (hw : (accSig R).IndexedValid M x w) : Acc R x := by
  induction hw with
  | sup s g hg ih =>
    exact Acc.intro s (fun y hy => ih .unit
      ⟨natCls y, ⟨Quotient.mk _ ⟨hy⟩, .unit⟩⟩)

/-- Exact proof-fibre truth, for arbitrary relations, survives erasure. -/
theorem acc_exact (M : Interp.{0}) (R : Nat → Nat → Prop) (x : Nat) :
    pempty ∈ (accSig R).erasedFamily M x ↔ Acc R x := by
  constructor
  · intro ⟨⟨w, hw⟩, _⟩
    exact accTree_accessible M R x w hw
  · intro h
    refine ⟨⟨accTree M R x h, accTree_valid M R x h⟩, ?_⟩
    cases h
    exact Equiv.rfl

/-- All premises of the general producer are paid on each accessible
point, including dependent proof arguments and their possible emptiness. -/
theorem acc_produced (M : Interp.{0}) (ch : Choice.{0})
    (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((accSig R).tel x k).erasedType M ((accSig R).erasedFamily M))) ∧
      (accSig R).code x f ∈ (accSig R).erasedFamily M x := by
  let v : PiTel.Value.{0, 1} (accTel R x).tel (fun _ => PSet.{0}) :=
    fun _ _ => pempty
  have hr : (accTel R x).Rel ((accSig R).erasedFamily M) v :=
    fun q r => (acc_exact M R (natOf q)).mpr (Acc.inv h (proofOf _ r))
  let f : PUnit → PSet.{0} := fun _ => (accTel R x).erasedEncode M v
  have hf := fun k => ((accSig R).tel x k).erasedEncode_mem M
    (accDomainsDich R x k) _ ((accSig R).erasedFamily_dich M (accCodeDich R)) v hr
  exact ⟨f, hf, (accSig R).erasedProduce_of_mem M ch (accCodeDich R)
    (accDomainsDich R) x f hf⟩

/-- The well-founded Nat.lt instance is an immediate producer application. -/
theorem natLt_produced (M : Interp.{0}) (ch : Choice.{0}) (x : Nat) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((accSig Nat.lt).tel x k).erasedType M
        ((accSig Nat.lt).erasedFamily M))) ∧
      (accSig Nat.lt).code x f ∈ (accSig Nat.lt).erasedFamily M x :=
  acc_produced M ch Nat.lt x (Nat.lt_wfRel.wf.apply x)

/-- One point loops while every other point has no predecessors. -/
def loopRel (y x : Nat) : Prop := y = 0 ∧ x = 0

/-- A loop cannot acquire accessibility through erased result codes. -/
theorem loop_not_accessible : ¬ Acc loopRel 0 := by
  intro h
  exact Acc.ndrec (C := fun x => x = 0 → False)
    (fun _ _ ih he => ih 0 ⟨rfl, he⟩ rfl) h rfl

/-- The same erased proof code inhabits the accessible fibre only.
A value-only result-index guard would lose this distinction. -/
theorem mixed_indices_refused (M : Interp.{0}) :
    pempty ∈ (accSig loopRel).erasedFamily M 1 ∧
      pempty ∉ (accSig loopRel).erasedFamily M 0 := by
  constructor
  · apply (acc_exact M loopRel 1).mpr
    exact Acc.intro 1 (fun _ h => Nat.noConfusion h.2)
  · intro h
    exact loop_not_accessible ((acc_exact M loopRel 0).mp h)

/-- A W field with infinitely many Ed-compatible arguments. -/
def wTel : RecTel.{0, 0} PUnit.{1} 1 := .pi natDom (fun _ => .ret .unit)

def wSig : RecSig.{0, 0} PUnit.{1} where
  Sh := Fn2Sh
  Field := PiW.Field
  depth := fun _ _ => 1
  tel := fun s k => match s with
    | .leaf => PEmpty.elim k
    | .node => wTel
  out := fun _ => .unit
  code := fun s f => match s with
    | .leaf => dataVal 0 []
    | .node => dataVal 1 [f .unit]
  tag := fun _ _ => True
  tag_congr := fun _ _ _ _ h => h
  code_tag := fun _ _ => trivial
  code_congr := by
    intro s f g h
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨h .unit, trivial⟩

/-- Data constructors stay nonproof at both shapes. -/
theorem wCodeDich : wSig.CodeDich :=
  Or.inr (fun s _ => by cases s <;> exact dataVal_ne_pempty _ _)

/-- All W argument domains are dichotomous; none is required to be finite. -/
theorem wDomainsDich : ∀ s k, (wSig.tel s k).DomainsDich := by
  intro s k
  cases s with
  | leaf => exact PEmpty.elim k
  | node => exact ⟨natDom_dich, fun _ => trivial⟩

/-- Transport the finite-depth trees, retaining the branch number rather
than substituting the old mixed literal domain into Ed. -/
def wTree (M : Interp.{0}) : GT Fn2GSig.{0} → GT (wSig.erasedPiSig M).toGSig
  | .sup .leaf _ => .sup .leaf (fun p => PEmpty.elim p.1)
  | .sup .node g => .sup .node (fun p => wTree M (g (fnCls (natOf p.2.1))))

/-- The unbounded W tree branches to a depth-n tree at argument n. -/
def wOmega (M : Interp.{0}) : GT (wSig.erasedPiSig M).toGSig :=
  .sup .node (fun p => wTree M (fnT (natOf p.2.1)))

/-- Transported trees retain every recursive child and its result index. -/
theorem wTree_valid (M : Interp.{0}) (w : GT Fn2GSig.{0}) :
    wSig.IndexedValid M .unit (wTree M w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf =>
      apply RecSig.IndexedValid.sup
      intro k
      exact PEmpty.elim k
    | node =>
      exact RecSig.IndexedValid.sup (S := wSig) (M := M) Fn2Sh.node _ (fun _ p => ih (fnCls (natOf p.1)))

/-- The height-omega tree is index correct, by the finite-child proof. -/
theorem wOmega_valid (M : Interp.{0}) : wSig.IndexedValid M .unit (wOmega M) :=
  RecSig.IndexedValid.sup (S := wSig) (M := M) Fn2Sh.node _ (fun _ p => wTree_valid M (fnT (natOf p.1)))

/-- The actual erased W field and its constructor are accepted together. -/
theorem w_produced (M : Interp.{0}) (ch : Choice.{0}) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M ((wSig.tel .node k).erasedType M (wSig.erasedFamily M))) ∧
      wSig.code .node f ∈ wSig.erasedFamily M .unit ∧
      Equiv (wSig.code .node f) (decG (wSig.erasedPiSig M).toGSig (wOmega M)) := by
  let v : PiTel.Value.{0, 1} wTel.tel (fun _ => PSet.{0}) :=
    fun q => decG (wSig.erasedPiSig M).toGSig (wTree M (fnT (natOf q)))
  have hr : wTel.Rel (wSig.erasedFamily M) v :=
    fun q => ⟨⟨wTree M (fnT (natOf q)), wTree_valid M _⟩, Equiv.rfl⟩
  let f : PUnit → PSet.{0} := fun _ => wTel.erasedEncode M v
  have hf : ∀ k, f k ∈ Ed M ((wSig.tel .node k).erasedType M (wSig.erasedFamily M)) := by
    intro k
    cases k
    exact wTel.erasedEncode_mem M (wDomainsDich .node .unit) _
      (wSig.erasedFamily_dich M wCodeDich) v hr
  exact ⟨f, hf, wSig.erasedProduce_of_mem M ch wCodeDich wDomainsDich .node f hf,
    Equiv.rfl⟩

/-- A finite height bound on the representation tree, independent of
its possibly proof-erased decoding. -/
def wBound (M : Interp.{0}) : Nat → GT (wSig.erasedPiSig M).toGSig → Prop
  | 0, _ => False
  | n + 1, .sup _ g => ∀ p, wBound M n (g p)

/-- Finite child n already defeats height bound n. -/
theorem wTree_bound_refuted (M : Interp.{0}) (n : Nat) :
    ¬ wBound M n (wTree M (fnT n)) := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (h ⟨.unit, ⟨natCls 0, .unit⟩⟩)

/-- No finite height bounds the actual representation used by w_produced.
This concerns trees; the exact raw W value's finite-stage exclusion is
proved separately by PendARoleW.canonicalHeightOmega. -/
theorem wOmega_bound_refuted (M : Interp.{0}) (n : Nat) :
    ¬ wBound M n (wOmega M) := by
  cases n with
  | zero => exact fun h => h
  | succ n => exact fun h => wTree_bound_refuted M n (h ⟨.unit, ⟨natCls n, .unit⟩⟩)

/-- Three dependent binders and a result varying in both data arguments.
The numeric offset is arbitrary, so label zero is not privileged. -/
def nestedTel (offset : Nat) : RecTel Nat 3 :=
  .pi natDom (fun q => .pi (proofDom (natOf q < natOf q + 1))
    (fun _ => .pi natDom (fun r => .ret (offset + natOf q + natOf r))))

def nestedFibre (i : Nat) : PSet.{0} := singleton (dataVal i [])

/-- These are elementary domain and result-face invariant witnesses. -/
theorem nestedDomainsDich (offset : Nat) : (nestedTel offset).DomainsDich :=
  ⟨natDom_dich, fun _ => ⟨Or.inl (fun _ h => let ⟨_, he⟩ := h; he.symm),
    fun _ => ⟨natDom_dich, fun _ => trivial⟩⟩⟩

theorem nestedFibre_dich (i : Nat) : Dich (nestedFibre i) :=
  Or.inr (fun h => dataVal_ne_pempty i [] (mem_singleton.mp h).symm)

/-- The complete depth-three dependent field is inhabited in the actual
proof-erased product, at every numeric relabelling. -/
theorem nested_product (M : Interp.{0}) (offset : Nat) :
    ∃ f, f ∈ Ed M ((nestedTel offset).erasedType M nestedFibre) := by
  let v : PiTel.Value.{0, 1} (nestedTel offset).tel (fun _ => PSet.{0}) :=
    fun q _ r => dataVal (offset + natOf q + natOf r) []
  exact ⟨_, (nestedTel offset).erasedEncode_mem M (nestedDomainsDich offset)
    nestedFibre nestedFibre_dich v (fun _ _ _ => mem_singleton.mpr Equiv.rfl)⟩

/-- A wrong result index is refused by actual Ed membership, after
encoding and proof erasure, at every numeric relabelling. -/
theorem nested_bad_index_refused (M : Interp.{0}) (offset : Nat) :
    (nestedTel offset).erasedEncode M (fun _ _ _ => dataVal offset []) ∉
      Ed M ((nestedTel offset).erasedType M nestedFibre) := by
  intro h
  have hr := ((nestedTel offset).erasedEncode_mem_iff M (nestedDomainsDich offset)
    nestedFibre nestedFibre_dich _).mp h
  have he : Equiv (dataVal offset [] : PSet.{0}) (dataVal (offset + 1) []) :=
    mem_singleton.mp (hr (natCls 0)
      (Quotient.mk _ ⟨Nat.lt_succ_self 0⟩) (natCls 1))
  have hn := (dataVal_inj (by rfl) he).1
  omega

end Rcic.F3.PSet.PiEraseFixture
