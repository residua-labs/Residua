import rcic.RcicF3PiRawIH
/-! Bounded raw motives at the actual motive universe. Complete extensional
keys retain dependent indices; no tuple representative is selected. Ordinary
motive typing supplies the bound only at fitting majors. This is an IH
component, not an A producer. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawMotiveAny
open Rcic.Declarative PiIndex
universe u

/-- Elements of all types in the selected motive universe. -/
def carrier (M : Interp.{u}) (k : Nat) : PSet.{u} :=
  sUnion (sImage (Ed M) (M.U k))

/-- Only an actual fitting major can contribute an element. -/
def elements (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u}) : PSet.{u} :=
  sep (fun y => ∃ is : List PSet.{u}, key (ps ++ is) = i ∧
    TelFits M σ ds ρ is ∧ z ∈ Ed M (fapps F (ps ++ is)) ∧
    y ∈ Ed M (fapps mo (is ++ [z]))) (carrier M k)

/-- Ed supplies dichotomy also at unused keys, without a motive wall. -/
def guarded (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u}) : PSet.{u} :=
  Ed M (tyv (elements M σ k F mo ps ds ρ i z))

theorem guarded_dich (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u}) : Dich (guarded M σ k F mo ps ds ρ i z) :=
  dich_ed M _

theorem mem_carrier (M : Interp.{u}) (k : Nat) {T y : PSet.{u}}
    (hT : T ∈ M.U k) (hy : y ∈ Ed M T) : y ∈ carrier M k := by
  exact mem_sUnion.mpr ⟨Ed M T,
    mem_sImage_of (fun _ _ h => ed_congr M h) hT, hy⟩

theorem elements_key (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (is : List PSet.{u}) (z : PSet.{u})
    (hf : TelFits M σ ds ρ is) (hz : z ∈ Ed M (fapps F (ps ++ is)))
    (hT : fapps mo (is ++ [z]) ∈ M.U k) :
    Equiv (elements M σ k F mo ps ds ρ (key (ps ++ is)) z)
      (Ed M (fapps mo (is ++ [z]))) := by
  apply ext
  intro y
  constructor
  · intro hy
    obtain ⟨j, ⟨js, hj, _, _, hmem⟩, he⟩ := mem_sep.mp hy
    have ht := PiRawMotive.same_prefix_tail ps ((key_eq_iff _ _).mp hj)
    have ha := ed_congr M (fapps_congr_args mo
      (LEq_append ht (show LEq [z] [z] from ⟨Equiv.rfl, True.intro⟩)))
    exact mem_congr_left he (mem_congr_right ha hmem)
  · intro hy
    obtain ⟨j, he⟩ := mem_carrier M k hT hy
    exact mem_sep.mpr ⟨j, ⟨is, rfl, hf, hz, mem_congr_left he.symm hy⟩, he⟩

theorem guarded_key (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (is : List PSet.{u}) (z : PSet.{u})
    (hf : TelFits M σ ds ρ is) (hz : z ∈ Ed M (fapps F (ps ++ is)))
    (hT : fapps mo (is ++ [z]) ∈ M.U k) :
    Equiv (guarded M σ k F mo ps ds ρ (key (ps ++ is)) z)
      (Ed M (fapps mo (is ++ [z]))) := by
  exact (ed_congr M (tyv_congr
    (elements_key M σ k F mo ps ds ρ is z hf hz hT))).trans
      (ed_tyv M (dich_ed M _))

theorem guarded_resp (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) {x y : PSet.{u}} (h : Equiv x y) :
    Equiv (guarded M σ k F mo ps ds ρ i x)
      (guarded M σ k F mo ps ds ρ i y) := by
  apply ed_congr M
  apply tyv_congr
  apply sep_congr
  · intro a b hab
    rintro ⟨is, hi, hf, hx, ha⟩
    exact ⟨is, hi, hf, mem_congr_left h hx,
      mem_congr_left hab (mem_congr_right (ed_congr M (fapps_congr_args mo
        (LEq_append (LEq.refl is) (show LEq [x] [y] from ⟨h, True.intro⟩)))) ha)⟩
  · intro a b hab
    rintro ⟨is, hi, hf, hy, ha⟩
    exact ⟨is, hi, hf, mem_congr_left h.symm hy,
      mem_congr_left hab (mem_congr_right (ed_congr M (fapps_congr_args mo
        (LEq_append (LEq.refl is) (show LEq [y] [x] from ⟨h.symm, True.intro⟩)))) ha)⟩
  · exact Equiv.rfl

/-- No matching fitting major means the empty set, including unused arities. -/
theorem guarded_unused (M : Interp.{u}) (σ : Nat → Nat) (k : Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u})
    (hn : ¬ ∃ is, key (ps ++ is) = i ∧ TelFits M σ ds ρ is ∧
      z ∈ Ed M (fapps F (ps ++ is))) :
    Equiv (guarded M σ k F mo ps ds ρ i z) pempty := by
  have he : Equiv (elements M σ k F mo ps ds ρ i z) pempty := by
    apply ext
    intro y
    constructor
    · intro hy
      obtain ⟨j, ⟨is, hi, hf, hz, _⟩, _⟩ := mem_sep.mp hy
      exact (hn ⟨is, hi, hf, hz⟩).elim
    · intro hy; exact (not_mem_pempty hy).elim
  exact (ed_congr M (tyv_congr he)).trans
    (ed_tyv M (Or.inl (fun _ h => (not_mem_pempty h).elim)))

/-- Ordinary typed motive application at the actual dependent index/major. -/
theorem motive_mem_U (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (Ps Is : List (Expr Nat))
    (ps is : List PSet.{4}) (hps : ps.length = Ps.length)
    (mo z : PSet.{4}) (v : Level)
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))
        (.sort v)))))
    (his : TelFits M σ Is (push ps ρ0) is)
    (hz : z ∈ Ed M (fapps (M.μ f (ls.map (evalTotal σ))) (ps ++ is))) :
    fapps mo (is ++ [z]) ∈ M.U (evalTotal σ v) := by
  have hmo' : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi (Is ++ [foldApps (.const f ls) (policyLocals (Ps.length + Is.length))])
        (.sort v))) := by rw [policyPi_append]; exact hmo
  have hzF : z ∈ Ed M (den M σ (push is (push ps ρ0))
      (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))) := by
    have hF := Fapp_den M σ f ls ps is ρ0
    rw [hps, his.length] at hF
    rw [hF]; exact hz
  have ht := mem_fapps M σ (.sort v) _ (push ps ρ0) mo (is ++ [z]) hmo'
    (TelFits.append his ⟨hzF, True.intro⟩)
  change fapps mo (is ++ [z]) ∈ Ed M (tyv (M.U (evalTotal σ v))) at ht
  have hd : Dich (M.U (evalTotal σ v)) := by rw [hU]; exact U4_dich _
  exact mem_congr_right (ed_tyv M hd) ht

/-- The actual admitted policy chooses the bound; anySort reads its own level
parameter, and propOnly reads zero. No new motive-tag premise is supplied. -/
theorem policy_key {M : Interp.{4}} (hU : M.U = U W4)
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (ps is : List PSet.{4}) (mo z : PSet.{4})
    (hps : ps.length = a.family.parameters.length)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (his : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (hz : z ∈ Ed M (fapps
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ is))) :
    Equiv (guarded M (σOf vs)
      (evalTotal (σOf vs) (policyMotiveLevel a.family.member.arity a.policy))
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      mo ps a.family.indices (push ps ρ0) (key (ps ++ is)) z)
      (Ed M (fapps mo (is ++ [z]))) := by
  exact guarded_key M (σOf vs) _ _ mo ps a.family.indices (push ps ρ0) is z his hz
    (motive_mem_U M hU (σOf vs) a.family.ref (policyFamilyLevels a.family)
      a.family.parameters a.family.indices ps is hps mo z _ hmo his hz)

end Rcic.F3.PSet.PiRawMotiveAny
