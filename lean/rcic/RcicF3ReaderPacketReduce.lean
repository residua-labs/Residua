import rcic.RcicF3ReaderSpine

/-!
# Beta and zeta transitions of original typed reader packets

These transitions construct the next packet from the actual source body
derivation. Beta uses the pending argument's produced value relation and
the nonempty common function to recover the literal annotation. Zeta uses
the literal stored-value derivation. Both retain the separately evaluated
original captures and the exact parallel substitution of the body.

The masked capture is only an input of the logical relation. No masked
typing or common original capture is introduced. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open RecFieldMask (Value)
open RecFieldMaskSupport (allowCons markCons)
open ReaderSubstitution (capture Levels)
universe u

theorem capture_cons (M : Interp.{u}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) (a : Expr Nat) (s : SubstT) :
    capture M σ ρ (SubstT.cons a s) =
      vcons (den M σ ρ a) (capture M σ ρ s) := by
  funext i
  cases i <;> rfl

theorem allowed_cons (fd : FamData) (a : Expr Nat) (s : SubstT) :
    allowed fd (SubstT.cons a s) =
      allowCons (occursConst fd.fref a = false) (allowed fd s) := by
  funext i
  cases i <;> rfl

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {ρ η : Nat → PSet.{4}}

/-- The actual argument's semantic relation is retagged at the literal
lambda annotation; its two original values are left distinct. -/
theorem beta_packet (L : Local P μ fd C σ K ρ η)
    {A body B : Expr Nat}
    (db : HasTyT L.E L.n (.assumption A :: L.Γ) body B)
    (hb : LOKt L.τ 4 K db) (hlA : Levels σ L.τ A) (hlb : Levels σ L.τ body)
    (hcaps : ∀ i, Provenance P μ fd C σ K ρ η (L.s i))
    (a : Argument P μ fd C σ K ρ η)
    (BC BD : PSet.{4} → PSet.{4})
    (hBC : ∀ x y, Equiv x y → Equiv (BC x) (BC y))
    (hBD : ∀ x y, Equiv x y → Equiv (BD x) (BD y))
    (hfunC : den (mkM P (table P μ fd C)) σ ρ (substT L.s (.lam A body)) ∈
      Ed (mkM P (table P μ fd C))
        (piVal (mkM P (table P μ fd C)) a.packet.typeC BC))
    (hfunD : den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
        (substT L.s (.lam A body)) ∈
      Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (piVal (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) a.packet.typeD BD))
    (hneC : ¬ Equiv (fapp
      (den (mkM P (table P μ fd C)) σ ρ (substT L.s (.lam A body)))
      (den (mkM P (table P μ fd C)) σ ρ a.packet.code)) pempty)
    (hneD : ¬ Equiv (fapp
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
        (substT L.s (.lam A body)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ a.packet.code)) pempty) :
    ∃ p : Packet P μ fd C σ K ρ η,
      p.code = instantiate0 a.packet.code (substT L.s.up body) ∧
      (∀ i, Provenance P μ fd C σ K ρ η (p.s i)) ∧
      Equiv (fapp
        (den (mkM P (table P μ fd C)) σ ρ (substT L.s (.lam A body)))
        (den (mkM P (table P μ fd C)) σ ρ a.packet.code))
        (den (mkM P (table P μ fd C)) σ ρ p.code) ∧
      Equiv (fapp
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
          (substT L.s (.lam A body)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ a.packet.code))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.code) := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  let ρC := capture MC σ ρ L.s
  let ρD := capture MD σ ρ L.s
  let ηC := capture MC σ η L.s
  let xC := den MC σ ρ a.packet.code
  let xD := den MD σ ρ a.packet.code
  let y := den MC σ η a.packet.code
  have hfunC' : den MC L.τ ρC (.lam A body) ∈
      Ed (mkM P μ) (piVal (mkM P μ) a.packet.typeC BC) := by
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ,
      piVal_dec_eq P (table P μ fd C) μ,
      ed_mkM P (table P μ fd C) μ] at hfunC
    exact hfunC
  have hfunD' : den MD L.τ ρD (.lam A body) ∈
      Ed (mkM P μ) (piVal (mkM P μ) a.packet.typeD BD) := by
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ,
      piVal_dec_eq P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ,
      ed_mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ] at hfunD
    exact hfunD
  have hnC : ¬ Equiv (fapp (den MC L.τ ρC (.lam A body)) xC) pempty := by
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ] at hneC
    exact hneC
  have hnD : ¬ Equiv (fapp (den MD L.τ ρD (.lam A body)) xD) pempty := by
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ] at hneD
    exact hneD
  have hx : occursConst fd.fref a.packet.code = false → Equiv xC xD := by
    intro hclean
    have he := PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
      (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ a.packet.code hclean ρ
    change den MC σ ρ a.packet.code = den MD σ ρ a.packet.code at he
    change Equiv (den MC σ ρ a.packet.code) (den MD σ ρ a.packet.code)
    rw [he]
    exact Equiv.rfl
  have hv : occursConst fd.fref a.packet.code = false →
      Value (mkM P μ) fd C a.packet.q (Ed (mkM P μ) a.packet.typeC)
        (Ed (mkM P μ) a.packet.typeD) xC y := by
    intro hclean
    have h := a.packet.value hclean
    rw [ed_mkM P (table P μ fd C) μ,
      ed_mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ] at h
    exact h
  have ht := ReaderCapture.beta P μ fd C L.τ K L.soundC L.soundD db hb
    L.marks (allowed fd L.s) ρC ρD ηC L.fitsC L.fitsD L.context L.agree
    a.packet.typeC a.packet.typeD BC BD hBC hBD hfunC' hfunD'
    xC xD y a.packet.q (occursConst fd.fref a.packet.code = false) hnC hnD hx hv
  let Lb : Local P μ fd C σ K ρ η :=
    { E := L.E, n := L.n, Γ := .assumption A :: L.Γ, τ := L.τ,
      s := SubstT.cons a.packet.code L.s, marks := markCons a.packet.q L.marks,
      soundC := L.soundC, soundD := L.soundD,
      fitsC := by rw [capture_cons]; exact ht.1,
      fitsD := by rw [capture_cons]; exact ht.2.1,
      context := by rw [allowed_cons, capture_cons, capture_cons, capture_cons]; exact ht.2.2.2 }
  let p := Lb.term db hb hlb
  refine ⟨p, (instantiate0_substT_up L.s a.packet.code body).symm, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | zero => exact Provenance.typed a.packet a.captures
    | succ i => exact hcaps i
  · change Equiv (fapp (den MC σ ρ (substT L.s (.lam A body))) xC)
      (den MC σ ρ (substT (SubstT.cons a.packet.code L.s) body))
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ,
      ReaderSubstitution.den_closure _ σ L.τ body hlb _ ρ, capture_cons]
    exact beta_val MC (den_resp MC L.τ ρC body) ht.1.2
  · change Equiv (fapp (den MD σ ρ (substT L.s (.lam A body))) xD)
      (den MD σ ρ (substT (SubstT.cons a.packet.code L.s) body))
    rw [ReaderSubstitution.den_closure _ σ L.τ (.lam A body) ⟨hlA, hlb⟩ L.s ρ,
      ReaderSubstitution.den_closure _ σ L.τ body hlb _ ρ, capture_cons]
    exact beta_val MD (den_resp MD L.τ ρD body) ht.2.1.2

/-- Zeta retains the original let declaration, separately fitted at its
actual source and enlarged values. It needs no nonempty-value premise. -/
theorem zeta_packet (L : Local P μ fd C σ K ρ η)
    {A value body B : Expr Nat}
    (dv : HasTyT L.E L.n L.Γ value A)
    (db : HasTyT L.E L.n (.letBinding A value :: L.Γ) body B)
    (hv : LOKt L.τ 4 K dv) (hb : LOKt L.τ 4 K db)
    (hlv : Levels σ L.τ value) (hlb : Levels σ L.τ body)
    (hcaps : ∀ i, Provenance P μ fd C σ K ρ η (L.s i)) :
    ∃ p : Packet P μ fd C σ K ρ η,
      p.code = instantiate0 (substT L.s value) (substT L.s.up body) ∧
      (∀ i, Provenance P μ fd C σ K ρ η (p.s i)) := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  let pv := L.term dv hv hlv
  let ρC := capture MC σ ρ L.s
  let ρD := capture MD σ ρ L.s
  let ηC := capture MC σ η L.s
  let xC := den MC σ ρ pv.code
  let xD := den MD σ ρ pv.code
  let y := den MC σ η pv.code
  have evC : xC = den MC L.τ ρC value :=
    ReaderSubstitution.den_closure MC σ L.τ value hlv L.s ρ
  have evD : xD = den MD L.τ ρD value :=
    ReaderSubstitution.den_closure MD σ L.τ value hlv L.s ρ
  have hfC : Fits MC L.τ (.letBinding A value :: L.Γ) (vcons xC ρC) := by
    refine ⟨L.fitsC, pv.memberC, ?_⟩
    rw [evC]
    exact Equiv.rfl
  have hfD : Fits MD L.τ (.letBinding A value :: L.Γ) (vcons xD ρD) := by
    refine ⟨L.fitsD, pv.memberD, ?_⟩
    rw [evD]
    exact Equiv.rfl
  have hctx := RecFieldMaskSupport.context_capture P μ fd C L.τ L.marks
    (allowed fd L.s) L.Γ ρC ρD ηC L.context (.letBinding A value) pv.q
    (occursConst fd.fref pv.code = false) xC xD y (fun hf => pv.value hf)
  let Lb : Local P μ fd C σ K ρ η :=
    { E := L.E, n := L.n, Γ := .letBinding A value :: L.Γ, τ := L.τ,
      s := SubstT.cons pv.code L.s, marks := markCons pv.q L.marks,
      soundC := L.soundC, soundD := L.soundD,
      fitsC := by rw [capture_cons]; exact hfC,
      fitsD := by rw [capture_cons]; exact hfD,
      context := by rw [allowed_cons, capture_cons, capture_cons, capture_cons]; exact hctx }
  let p := Lb.term db hb hlb
  refine ⟨p, (instantiate0_substT_up L.s pv.code body).symm, ?_⟩
  intro i
  cases i with
  | zero => exact Provenance.typed pv hcaps
  | succ i => exact hcaps i

end Rcic.F3.PSet.ReaderPacket
