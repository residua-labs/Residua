import rcic.RcicF3PiSmallProducer
import rcic.RcicF3PiEraseFixture
import rcic.RcicF3PiTypedCompileAttack
/-!
# Mixed-universe constructor and presentation attacks

Small domains feed actual large erased products. The Acc family retains
indices before erasure. Presentation helpers retain their explicit ordinary
EnvSound premise; they do not inhabit a raw Acc environment.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallAttack
open PiSmallCompile PiSmallField PiSmallProducer PiFieldFixture
open Rcic.Declarative Rcic.Declarative.Ann

def natDom : PSet.{3} := mk (ULift.{3} Nat) (fun n => ord (n.down + 1))
def natOf : FBr natDom → Nat :=
  Quotient.lift (fun n => n.down) (fun _ _ h => Nat.succ.inj (ord_inj h))
def natCls (n : Nat) : FBr natDom := Quotient.mk (FSetoid natDom) ⟨n⟩

theorem natDom_dich : Dich natDom := by
  apply Or.inr
  intro ⟨n, hn⟩
  have h : n.down + 1 = 0 := ord_inj hn
  exact Nat.noConfusion h


def proofDom (p : Prop) : PSet.{3} := mk (ULift.{3} (PLift p)) (fun _ => pempty)
def proofOf (p : Prop) (q : FBr (proofDom p)) : p :=
  Quotient.inductionOn q (fun h => h.down.down)

def accTel (R : Nat → Nat → Prop) (x : Nat) : RecTel.{3,0} Nat 2 :=
  .pi natDom (fun q => .pi (proofDom (R (natOf q) x)) (fun _ => .ret (natOf q)))

def accSig (R : Nat → Nat → Prop) : Sig Nat where
  Sh := ULift.{3} Nat
  Field := fun _ => PUnit.{4}
  depth := fun _ _ => 2
  tel := fun x _ => accTel R x.down
  out := fun x => x.down
  code := fun _ _ => pempty
  code_congr := fun _ _ _ _ => Equiv.rfl

/-- Elementary code/domain invariant witnesses, not raw extraction. -/
theorem accInvariants (R : Nat → Nat → Prop) :
    CodeDich (accSig R) ∧ ∀ s k, ((accSig R).tel s k).DomainsDich := by
  exact ⟨Or.inl (fun _ _ => Equiv.rfl), fun _ _ =>
    ⟨natDom_dich, fun _ => ⟨Or.inl (fun _ h => let ⟨_, he⟩ := h; he.symm),
      fun _ => trivial⟩⟩⟩

noncomputable def accTree (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) : Tree (accSig R) :=
  Acc.ndrec (C := fun _ => Tree (accSig R))
    (fun x _ ih => .sup ⟨x⟩ (fun p => ih (natOf p.2.1) (proofOf _ p.2.2.1))) h

theorem accTree_valid (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    Valid (accSig R) x (accTree R x h) := by
  induction h with
  | intro x hx ih =>
    apply Valid.sup
    intro k p
    exact ih (natOf p.1) (proofOf _ p.2.1)

/-- Indices are checked before proof erasure. -/
theorem accTree_accessible (R : Nat → Nat → Prop) (x : Nat)
    (w : Tree (accSig R)) (hw : Valid (accSig R) x w) : Acc R x := by
  induction hw with
  | sup s g hg ih =>
    exact Acc.intro s.down (fun y hy => ih .unit
      ⟨natCls y, ⟨Quotient.mk _ ⟨⟨hy⟩⟩, .unit⟩⟩)

theorem acc_exact (M : Interp.{4}) (R : Nat → Nat → Prop) (x : Nat) :
    pempty ∈ family M (accSig R) x ↔ Acc R x := by
  constructor
  · intro ⟨⟨⟨w, hw⟩⟩, _⟩
    exact accTree_accessible R x w hw
  · intro h
    refine ⟨⟨⟨accTree R x h, accTree_valid R x h⟩⟩, ?_⟩
    cases h
    exact Equiv.rfl

/-- Actual large product members, not just the child relation. -/
theorem acc_produced (P : Premises4) (M : Interp.{4})
    (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M ((widen ((accSig R).tel ⟨x⟩ k)).erasedType M
        (family M (accSig R)))) ∧
      (accSig R).code ⟨x⟩ f ∈ family M (accSig R) x := by
  let v : PiTel.Value.{3,5} (accTel R x).tel (fun _ => PSet.{4}) := fun _ _ => pempty
  have hr : Related (accTel R x) (family M (accSig R)) v :=
    fun q r => (acc_exact M R (natOf q)).mpr (Acc.inv h (proofOf _ r))
  let f : PUnit.{4} → PSet.{4} := fun _ => encode M (accTel R x) v
  have hf := fun k => encode_mem M ((accSig R).tel ⟨x⟩ k)
    ((accInvariants R).2 ⟨x⟩ k) _ (family_dich M (accSig R) (accInvariants R).1) v hr
  exact ⟨f, hf, produce M P.c3 (accSig R) (accInvariants R).1
    (accInvariants R).2 ⟨x⟩ f hf⟩

/-- Elementary well-founded instance of the actual product producer. -/
theorem natLt_produced (P : Premises4) (M : Interp.{4}) (x : Nat) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M ((widen ((accSig Nat.lt).tel ⟨x⟩ k)).erasedType M
        (family M (accSig Nat.lt)))) ∧
      (accSig Nat.lt).code ⟨x⟩ f ∈ family M (accSig Nat.lt) x := by
  exact acc_produced P M Nat.lt x (Nat.lt_wfRel.wf.apply x)

/-- Equal erased codes cannot cross the accessible/inaccessible fibres. -/
theorem mixed_indices_refused (M : Interp.{4}) :
    pempty ∈ family M (accSig PiEraseFixture.loopRel) 1 ∧
      pempty ∉ family M (accSig PiEraseFixture.loopRel) 0 := by
  constructor
  · apply (acc_exact M PiEraseFixture.loopRel 1).mpr
    exact Acc.intro 1 (fun _ h => Nat.noConfusion h.2)
  · intro h
    exact PiEraseFixture.loop_not_accessible ((acc_exact M PiEraseFixture.loopRel 0).mp h)

def nestedTel (offset : Nat) : RecTel.{3,0} Nat 3 :=
  .pi natDom (fun q => .pi (proofDom (natOf q < natOf q + 1))
    (fun _ => .pi natDom (fun r => .ret (offset + natOf q + natOf r))))
def nestedFibre (i : Nat) : PSet.{4} := singleton (dataVal i [])

/-- Elementary domain/result invariant witnesses. -/
theorem nestedInvariants (offset : Nat) :
    (nestedTel offset).DomainsDich ∧ ∀ i, Dich (nestedFibre i) := by
  exact ⟨⟨natDom_dich, fun _ => ⟨Or.inl (fun _ h => let ⟨_, he⟩ := h; he.symm),
    fun _ => ⟨natDom_dich, fun _ => trivial⟩⟩⟩,
    fun i => Or.inr (fun h => dataVal_ne_pempty i [] (mem_singleton.mp h).symm)⟩

theorem nested_product (M : Interp.{4}) (offset : Nat) :
    ∃ f, f ∈ Ed M ((widen (nestedTel offset)).erasedType M nestedFibre) := by
  let v : PiTel.Value.{3,5} (nestedTel offset).tel (fun _ => PSet.{4}) :=
    fun q _ r => dataVal (offset + natOf q + natOf r) []
  exact ⟨_, encode_mem M (nestedTel offset) (nestedInvariants offset).1
    nestedFibre (nestedInvariants offset).2 v (fun _ _ _ => mem_singleton.mpr Equiv.rfl)⟩

/-- Wrong result indices are refused after widening, at every numeric offset. -/
theorem nested_bad_index_refused (M : Interp.{4}) (offset : Nat) :
    encode M (nestedTel offset) (fun _ _ _ => dataVal offset []) ∉
      Ed M ((widen (nestedTel offset)).erasedType M nestedFibre) := by
  intro h
  have hr := (encode_mem_iff M (nestedTel offset) (nestedInvariants offset).1
    nestedFibre (nestedInvariants offset).2 _).mp h
  have he : Equiv (dataVal offset [] : PSet.{4}) (dataVal (offset + 1) []) :=
    mem_singleton.mp (hr (natCls 0)
      (Quotient.mk _ ⟨⟨Nat.lt_succ_self 0⟩⟩) (natCls 1))
  have hn := (dataVal_inj (by rfl) he).1
  omega

/-- Compiled current-denotation field, not an independent family fixed point. -/
def compiledField (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) : PSet.{4} :=
  (widen (compile P μ σ
    (PiTypedCompile.leafIndex (mkM P μ) σ RoleAttacks.accResult)
    RoleAttacks.accDomains ρ)).erasedType (mkM P μ) (fun i => i.1)

/-- Conditional presentation transport, an elementary composition.
EnvSound/Fits are retained explicitly; no inhabitance claim. -/
theorem presentations (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat)
    (hE : EnvSound (mkM P μ) σ K PiSyntaxAttack.env 0)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ PiSyntaxAttack.ctx ρ) :
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ paFieldDom) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.betaField) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.deltaField) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.zetaField) := by
  have e := compile_spec P μ σ K hE RoleAttacks.accDomains
    RoleAttacks.accResult PiSyntaxAttack.fieldTy (PiTypedCompileAttack.fieldBound σ K) ρ hρ
  obtain ⟨hβ, hδ, hζ⟩ := PiTypedCompileAttack.presentationBounds σ K
  exact ⟨e, e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.betaConversion hβ ρ hρ).1.symm,
    e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.deltaConversion hδ ρ hρ).1.symm,
    e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.zetaConversion hζ ρ hρ).1.symm⟩

def wTel : RecTel.{3,0} PUnit.{1} 1 := .pi natDom (fun _ => .ret .unit)
def wField : ULift.{3} Fn2Sh.{0} → Type 3
  | ⟨.leaf⟩ => PEmpty.{4}
  | ⟨.node⟩ => PUnit.{4}
def wSig : Sig PUnit.{1} where
  Sh := ULift.{3} Fn2Sh.{0}
  Field := wField
  depth := fun _ _ => 1
  tel := fun s => match s with
    | ⟨.leaf⟩ => fun k => PEmpty.elim k
    | ⟨.node⟩ => fun _ => wTel
  out := fun _ => .unit
  code := fun s => match s with
    | ⟨.leaf⟩ => fun _ => dataVal 0 []
    | ⟨.node⟩ => fun f => dataVal 1 [f .unit]
  code_congr := fun s f g h => by
    rcases s with ⟨s⟩
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨h .unit, trivial⟩

/-- Elementary invariants for the concrete two-constructor signature. -/
theorem wInvariants : CodeDich wSig ∧ ∀ s k, (wSig.tel s k).DomainsDich := by
  constructor
  · apply Or.inr
    intro ⟨s⟩ f
    cases s <;> exact dataVal_ne_pempty _ _
  · intro ⟨s⟩ k
    cases s with
    | leaf => exact PEmpty.elim k
    | node => exact ⟨natDom_dich, fun _ => trivial⟩

def wTree : GT Fn2GSig.{0} → Tree wSig
  | .sup .leaf _ => .sup ⟨.leaf⟩ (fun p => PEmpty.elim p.1)
  | .sup .node g => .sup ⟨.node⟩ (fun p => wTree (g (fnCls (natOf p.2.1))))
def wOmega : Tree wSig := .sup ⟨.node⟩ (fun p => wTree (fnT (natOf p.2.1)))

theorem wTree_valid (w : GT Fn2GSig.{0}) : Valid wSig .unit (wTree w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf =>
      apply Valid.sup
      intro k
      exact PEmpty.elim k
    | node =>
      exact Valid.sup (S := wSig) ⟨.node⟩ _ (fun _ p => ih (fnCls (natOf p.1)))

/-- Elementary assembly from each checked child. -/
theorem wOmega_valid : Valid wSig .unit wOmega := by
  exact Valid.sup (S := wSig) ⟨.node⟩ _ (fun _ p => wTree_valid (fnT (natOf p.1)))

/-- Actual large W product, closure, and the unbounded representation agree. -/
theorem w_produced (P : Premises4) (M : Interp.{4}) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M ((widen (wSig.tel ⟨.node⟩ k)).erasedType M (family M wSig))) ∧
      wSig.code ⟨.node⟩ f ∈ family M wSig .unit ∧
      Equiv (wSig.code ⟨.node⟩ f) (decode M wSig wOmega) := by
  let v : PiTel.Value.{3,5} wTel.tel (fun _ => PSet.{4}) :=
    fun q => decode M wSig (wTree (fnT (natOf q)))
  have hr : Related wTel (family M wSig) v :=
    fun q => ⟨⟨⟨wTree (fnT (natOf q)), wTree_valid _⟩⟩, Equiv.rfl⟩
  let f : PUnit.{4} → PSet.{4} := fun _ => encode M wTel v
  have hf : ∀ k, f k ∈ Ed M ((widen (wSig.tel ⟨.node⟩ k)).erasedType M (family M wSig)) := by
    intro k
    cases k
    exact encode_mem M wTel (wInvariants.2 ⟨.node⟩ .unit) _
      (family_dich M wSig wInvariants.1) v hr
  exact ⟨f, hf, produce M P.c3 wSig wInvariants.1 wInvariants.2 ⟨.node⟩ f hf, Equiv.rfl⟩

def wBound : Nat → Tree wSig → Prop
  | 0, _ => False
  | n+1, .sup _ g => ∀ p, wBound n (g p)

theorem wTree_bound_refuted (n : Nat) : ¬ wBound n (wTree (fnT n)) := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (h ⟨.unit, ⟨natCls 0, .unit⟩⟩)

/-- Representation height, not a new raw-value finite-stage theorem. -/
theorem wOmega_bound_refuted (n : Nat) : ¬ wBound n wOmega := by
  cases n with
  | zero => exact fun h => h
  | succ n => exact fun h => wTree_bound_refuted n (h ⟨.unit, ⟨natCls n, .unit⟩⟩)

def emptyTel : RecTel.{3,0} PUnit.{1} 2 :=
  .pi (singleton (tyv pempty)) (fun _ => .pi pempty (fun _ => .ret .unit))
def emptyFibre (_ : PUnit.{1}) : PSet.{4} := singleton (tyv pempty)

/-- Empty recursive argument domains stay allowed after widening. -/
theorem empty_product (M : Interp.{4}) :
    ∃ f, f ∈ Ed M ((widen emptyTel).erasedType M emptyFibre) := by
  have hd : emptyTel.DomainsDich :=
    ⟨Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm),
      fun _ => ⟨Or.inr not_mem_pempty, fun _ => trivial⟩⟩
  have hx : ∀ i, Dich (emptyFibre i) := fun _ =>
    Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm)
  let v : PiTel.Value.{3,5} emptyTel.tel (fun _ => PSet.{4}) :=
    fun _ r => Quotient.lift (fun i => PEmpty.elim i)
      (fun i => PEmpty.elim i) r
  have hr : Related emptyTel emptyFibre v := by
    intro q r
    exact Quotient.inductionOn r (fun i => PEmpty.elim i)
  exact ⟨_, encode_mem M emptyTel hd emptyFibre hx v hr⟩

end Rcic.F3.PSet.PiSmallAttack
