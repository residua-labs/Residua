import rcic.RcicF3PiPropRec
import rcic.RcicF3PiValueRule
import rcic.RcicF3RecMem
/-! Guarded raw motives over extensional complete argument labels.
Only fitting majors enter the raw motive obligation; other labels are retained.
This component pays motive truth/extension/proof-face obligations, not raw
minor extraction or universal group production. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawMotive
open Rcic.Declarative PiIndex
universe u

def guarded (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u}) : PSet.{u} :=
  tv (∀ is : List PSet.{u}, key (ps ++ is) = i → TelFits M σ ds ρ is →
    z ∈ Ed M (fapps F (ps ++ is)) → pempty ∈ Ed M (fapps mo (is ++ [z])))

theorem guarded_dich (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z : PSet.{u}) : Dich (guarded M σ F mo ps ds ρ i z) :=
  dich_tv _

theorem guarded_prop (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) (z y : PSet.{u})
    (hy : y ∈ guarded M σ F mo ps ds ρ i z) : Equiv y pempty :=
  (mem_tv.mp hy).2

theorem guarded_resp (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (i : Index.{u}) {x y : PSet.{u}} (h : Equiv x y) :
    Equiv (guarded M σ F mo ps ds ρ i x) (guarded M σ F mo ps ds ρ i y) := by
  apply ext
  intro z
  simp only [guarded, mem_tv]
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨?_, hz⟩
    intro is hi hf hy
    have hh := hx is hi hf (mem_congr_left h.symm hy)
    exact mem_congr_right (ed_congr M (fapps_congr_args mo
      (LEq_append (LEq.refl is) (show LEq [x] [y] from ⟨h, True.intro⟩)))) hh
  · rintro ⟨hy, hz⟩
    refine ⟨?_, hz⟩
    intro is hi hf hx
    have hh := hy is hi hf (mem_congr_left h hx)
    exact mem_congr_right (ed_congr M (fapps_congr_args mo
      (LEq_append (LEq.refl is) (show LEq [y] [x] from ⟨h.symm, True.intro⟩)))) hh

theorem same_prefix_tail (ps : List PSet.{u}) {xs ys : List PSet.{u}}
    (h : LEq (ps ++ xs) (ps ++ ys)) : LEq xs ys := by
  induction ps with
  | nil => exact h
  | cons p ps ih => exact ih h.2

/-- At a fitting actual major the guarded motive has exactly the raw element
set. Proof-valuedness is required only at this actual raw application. -/
theorem guarded_key (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (is : List PSet.{u}) (z : PSet.{u})
    (hf : TelFits M σ ds ρ is) (hz : z ∈ Ed M (fapps F (ps ++ is)))
    (hProp : ∀ y, y ∈ Ed M (fapps mo (is ++ [z])) → Equiv y pempty) :
    Equiv (guarded M σ F mo ps ds ρ (key (ps ++ is)) z)
      (Ed M (fapps mo (is ++ [z]))) := by
  apply ext
  intro y
  constructor
  · intro hy
    obtain ⟨hg, he⟩ := mem_tv.mp hy
    exact mem_congr_left he.symm (hg is rfl hf hz)
  · intro hy
    have he := hProp y hy
    apply mem_tv.mpr
    refine ⟨?_, he⟩
    intro js hj _ _
    have ht := same_prefix_tail ps ((key_eq_iff _ _).mp hj)
    have ha := ed_congr M (fapps_congr_args mo
      (LEq_append ht (show LEq [z] [z] from ⟨Equiv.rfl, True.intro⟩)))
    exact mem_congr_right ha.symm (mem_congr_left he hy)

/-- The admitted propOnly motive type pays the proof-face premise at each
fitting actual application; no global premise over unused labels is added. -/
theorem guarded_policy {M : Interp.{4}} (hU : M.U = U W4)
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (ps is : List PSet.{4}) (mo z : PSet.{4})
    (hps : ps.length = a.family.parameters.length)
    (hpol : a.policy = .propOnly)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (his : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (hz : z ∈ Ed M (fapps
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ is))) :
    Equiv (guarded M (σOf vs)
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      mo ps a.family.indices (push ps ρ0) (key (ps ++ is)) z)
      (Ed M (fapps mo (is ++ [z]))) := by
  exact guarded_key M (σOf vs) _ mo ps a.family.indices (push ps ρ0) is z his hz
    (motive_prop_elem hU a vs ps mo is z hps his.length hpol hmo his hz)

/-- Actual dependent IH values read back into the raw motive at every
matching fitting branch, preserving the actual recursive child major. -/
theorem guarded_ih_read (M : Interp.{u}) (σ : Nat → Nat) (F mo : PSet.{u})
    (ps : List PSet.{u}) (ds : List (Expr Nat)) (ρ : Nat → PSet.{u})
    {depth : Nat} (t : RecTel.{u,u+1} Index.{u} depth) (hD : t.DomainsDich)
    (x ih : PSet.{u})
    (hih : ih ∈ Ed M (t.erasedIHType M (guarded M σ F mo ps ds ρ) x)) :
    ∀ p is, key (ps ++ is) = t.result p → TelFits M σ ds ρ is →
      t.tel.flatten (t.erasedRead M x) p ∈ Ed M (fapps F (ps ++ is)) →
      t.tel.flatten (t.erasedRead M ih) p ∈ Ed M
        (fapps mo (is ++ [t.tel.flatten (t.erasedRead M x) p])) := by
  have hr := t.erasedIH_read M hD (guarded M σ F mo ps ds ρ)
    (guarded_dich M σ F mo ps ds ρ) x ih hih
  have hp := (PiTel.all_iff _ _ _).mp hr
  intro p is hi hf hz
  obtain ⟨hg, he⟩ := mem_tv.mp (hp p)
  exact mem_congr_left he.symm (hg is hi hf hz)

/-- Semantic validity plus raw minor typing produces the raw motive result.
The admitted motive type pays proof erasure only where raw typing applies.
The remaining minor hypothesis is a construction obligation, not an apex wall. -/
theorem produce_policy {M : Interp.{4}} (hU : M.U = U W4)
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (ps is : List PSet.{4}) (mo z : PSet.{4})
    (hps : ps.length = a.family.parameters.length) (hpol : a.policy = .propOnly)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (his : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (hz : z ∈ Ed M (fapps
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ is)))
    (S : PiPropProducer.Sig.{4,5,5} Index.{4})
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hv : z ∈ PiPropProducer.family S (key (ps ++ is)))
    (minor : (s : S.Sh) → (S.Field s → PSet.{4}) →
      (S.Field s → PSet.{4}) → PSet.{4})
    (hminor : ∀ s f ih,
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (PiPropProducer.family S))) →
      (∀ k, ih k ∈ Ed M ((S.tel s k).erasedIHType M
        (guarded M (σOf vs)
          (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
          mo ps a.family.indices (push ps ρ0)) (f k))) →
      ∀ js, key (ps ++ js) = S.out s →
        TelFits M (σOf vs) a.family.indices (push ps ρ0) js →
        pempty ∈ Ed M (fapps
          (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ js)) →
        minor s f ih ∈ Ed M (fapps mo (js ++ [pempty]))) :
    pempty ∈ Ed M (fapps mo (is ++ [z])) := by
  let F := M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))
  let C := guarded M (σOf vs) F mo ps a.family.indices (push ps ρ0)
  have hm : ∀ (s : S.Sh) (f ih : S.Field s → PSet.{4}),
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (PiPropProducer.family S))) →
      (∀ k, ih k ∈ Ed M ((S.tel s k).erasedIHType M C (f k))) →
      pempty ∈ C (S.out s) pempty := by
    intro s f ih hf hi
    apply mem_tv.mpr
    refine ⟨?_, Equiv.rfl⟩
    intro js hj hfit hmaj
    have hr := hminor s f ih hf hi js hj hfit hmaj
    have he := motive_prop_elem hU a vs ps mo js pempty hps hfit.length
      hpol hmo hfit hmaj _ hr
    exact mem_congr_left he hr
  have hp := PiPropRec.produce M S hD C
    (guarded_dich M (σOf vs) F mo ps a.family.indices (push ps ρ0))
    (fun i _ _ h => guarded_resp M (σOf vs) F mo ps a.family.indices (push ps ρ0) i h)
    (guarded_prop M (σOf vs) F mo ps a.family.indices (push ps ρ0))
    (fun _ _ _ => pempty) hm (key (ps ++ is)) z hv
  exact (mem_tv.mp hp).1 is rfl his hz

end Rcic.F3.PSet.PiRawMotive
