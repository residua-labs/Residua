import rcic.RcicF3Inv

/-!
# F3 S5a-4: constructors

- `ctorEnd` / `ctorVal`: constructor `j` denotes the telescope abstraction
  over its stored type whose end value is the data value of its fields
  (`∅` for a `Prop` family);
- `ctorVal_mem`: the constructor's value is an element of its type, given
  the family's value at the same instance, a hereditarily sound typing of
  the stored type (which makes the result type a non-`∅` type value, hence
  its arguments fit the family's telescope), and, for a `Type` family, that
  the field types lie in the family's stage (`SmallAlong`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- The end value of constructor `j` with `nf` fields. -/
def ctorEnd (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (j nf : Nat) (ρ : Nat → PSet.{T}) :
    PSet.{T} :=
  cond M.dec (evalTotal σ fd.resLevel = 0) pempty (dataVal j (lastVals nf ρ))

theorem ctorEnd_resp (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (j nf : Nat) :
    EnvResp (ctorEnd M σ fd j nf) := fun _ _ h =>
  cond_congr Iff.rfl Equiv.rfl (dataVal_congr j (lastVals_congr nf h))

/-- The field sets along fitting values lie in the stage `W`. -/
def SmallAlong (M : Interp.{T}) (σ : Nat → Nat) (W : PSet.{T}) :
    List (Expr Nat) → (Nat → PSet.{T}) → List PSet.{T} → Prop
  | [], _, _ => True
  | A :: Ds, ρ, x :: xs => Ed M (den M σ ρ A) ∈ W ∧ SmallAlong M σ W Ds (vcons x ρ) xs
  | _ :: _, _, [] => True

theorem mem_FitSetT (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (xs : List PSet.{T}) →
    TelFits M σ Ds ρ xs → SmallAlong M σ (W k) Ds ρ xs → tup xs ∈ FitSetT M W k σ Ds ρ
  | [], _, [], _, _ => mem_singleton.mpr Equiv.rfl
  | A :: Ds, ρ, x :: xs, ⟨hx, hfs⟩, ⟨hW, hsm⟩ => by
      have htr : truncW M W k (Ed M (den M σ ρ A)) = Ed M (den M σ ρ A) := by
        unfold truncW cond
        cases M.dec (Ed M (den M σ ρ A) ∈ W k) with
        | isTrue _ => rfl
        | isFalse h => exact absurd hW h
      refine mem_sUnion.mpr ⟨sImage (fun t => ordPair x t) (FitSetT M W k σ Ds (vcons x ρ)), ?_, ?_⟩
      · show _ ∈ sImage _ (truncW M W k (Ed M (den M σ ρ A)))
        rw [htr]
        exact mem_sImage_of (fun y y' hy => sImage_congr (fun t t' ht => ordPair_congr hy ht)
          (FitSetT_congr M W k σ Ds (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl)))) hx
      · exact mem_sImage_of (fun t t' ht => ordPair_congr Equiv.rfl ht)
          (mem_FitSetT M W k σ Ds (vcons x ρ) xs hfs hsm)

theorem mem_BoundT (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{T})
    {t : PSet.{T}} : (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) → (i : Nat) →
    (c : List (Expr Nat) × List (Expr Nat)) → cs[i]? = some c → t ∈ FitSetT M W k σ c.1 ρp →
      dataOfTup (j + i) t ∈ BoundT M W k σ ρp j cs
  | _, [], _, _, h, _ => by simp at h
  | j, c' :: cs, 0, c, h, ht => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact mem_sUnion.mpr ⟨_, mem_pair.mpr (Or.inl Equiv.rfl),
        mem_sImage_of (fun _ _ h => dataOfTup_congr j h) ht⟩
  | j, c' :: cs, i + 1, c, h, ht => by
      simp only [List.getElem?_cons_succ] at h
      have := mem_BoundT M W k σ ρp (j + 1) cs i c h ht
      rw [show j + 1 + i = j + (i + 1) by omega] at this
      exact mem_sUnion.mpr ⟨_, mem_pair.mpr (Or.inr Equiv.rfl), this⟩

/-- `PiGood` through a telescope, needed only at fitting values. -/
theorem piGood_policyPi_fits (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T})
    (b : Expr Nat) : (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (∀ xs, TelFits M σ Ds ρ xs → PiGood M σ g (push xs ρ) b) → PiGood M σ g ρ (policyPi Ds b)
  | [], ρ, h => h [] trivial
  | A :: Ds, ρ, h => fun x hx =>
      piGood_policyPi_fits M σ g b Ds (vcons x ρ) fun xs hxs => h (x :: xs) ⟨hx, hxs⟩

theorem piGood_foldApps (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T})
    (ρ : Nat → PSet.{T}) : (f : Expr Nat) → (hf : ∀ A B, f ≠ .pi A B) → (as : List (Expr Nat)) →
    g ρ ∈ Ed M (den M σ ρ (foldApps f as)) → PiGood M σ g ρ (foldApps f as)
  | .bvar _, _, [], h => h
  | .sort _, _, [], h => h
  | .const _ _, _, [], h => h
  | .app _ _, _, [], h => h
  | .lam _ _, _, [], h => h
  | .letE _ _ _, _, [], h => h
  | .lit _, _, [], h => h
  | .pi A B, hf, [], _ => absurd rfl (hf A B)
  | f, _, a :: as, h => piGood_foldApps M σ g ρ (.app f a) (fun _ _ h => Expr.noConfusion h) as h

theorem TelFits_split {M : Interp.{T}} {σ : Nat → Nat} :
    (Ds Ds' : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (zs : List PSet.{T}) →
    TelFits M σ (Ds ++ Ds') ρ zs →
      ∃ xs ys, zs = xs ++ ys ∧ TelFits M σ Ds ρ xs ∧ TelFits M σ Ds' (push xs ρ) ys
  | [], _, _, zs, h => ⟨[], zs, rfl, trivial, h⟩
  | A :: Ds, Ds', ρ, z :: zs, ⟨hz, h⟩ => by
      obtain ⟨xs, ys, he, h1, h2⟩ := TelFits_split Ds Ds' (vcons z ρ) zs h
      exact ⟨z :: xs, ys, by rw [he]; rfl, ⟨hz, h1⟩, h2⟩

theorem den_paramLocals (M : Interp.{T}) (σ : Nat → Nat) (ps xs : List PSet.{T}) (ρ : Nat → PSet.{T}) :
    (policyParameterLocals ps.length xs.length).map (den M σ (push (ps ++ xs) ρ)) = ps := by
  have h : ∀ i, den M σ (push (ps ++ xs) ρ) (.bvar (i + xs.length)) = push ps ρ i := by
    intro i
    show push (ps ++ xs) ρ (i + xs.length) = _
    rw [push_append, push_ge]
  have : (policyParameterLocals ps.length xs.length).map (den M σ (push (ps ++ xs) ρ)) =
      lastVals ps.length (push ps ρ) := by
    unfold policyParameterLocals lastVals
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => h i)
  rw [this, lastVals_push]

theorem map_param_σOf (vs : List Nat) :
    ((List.range vs.length).map Level.param).map (evalTotal (σOf vs)) = vs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, evalTotal, σOf]
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- **The constructor's value is an element of its type.** -/
theorem ctorVal_mem {M : Interp.{4}} (hU : M.U = U W4) (vs : List Nat) (fd : FamData) (j : Nat)
    (cps fs ri : List (Expr Nat)) (hj : fd.ctors[j]? = some (fs, ri))
    (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hfam : Equiv (M.μ fd.fref vs) (piLam M (σOf vs) (famEnd M W4 (σOf vs) fd) (fun _ => pempty) (famType fd)))
    (htyp : ∀ zs, TelFits M (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den M (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed M (den M (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits M (σOf vs) cps ρ0 ps →
      TelFits M (σOf vs) fs (push ps ρ0) xs →
      SmallAlong M (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    piLam M (σOf vs) (ctorEnd M (σOf vs) fd j fs.length) ρ0
        (policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
          (policyParameterLocals cps.length fs.length ++ ri))) ∈
      Ed M (den M (σOf vs) ρ0 (policyPi (cps ++ fs) (foldApps (.const fd.fref
        ((List.range vs.length).map Level.param)) (policyParameterLocals cps.length fs.length ++ ri)))) := by
  refine piLam_mem M _ (ctorEnd_resp M _ fd j fs.length) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, xs, rfl, hps, hxs⟩ := TelFits_split cps fs ρ0 zs hz
  have hpl : ps.length = cps.length := hps.length
  have hxl : xs.length = fs.length := hxs.length
  -- the result type's value
  have hR : Equiv (den M (σOf vs) (push (ps ++ xs) ρ0) (foldApps (.const fd.fref
      ((List.range vs.length).map Level.param)) (policyParameterLocals cps.length fs.length ++ ri)))
      (fapps (famVal M W4 (σOf vs) fd) (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0))))) := by
    rw [den_foldApps, List.map_append, ← hpl, ← hxl, den_paramLocals]
    show Equiv (fapps (M.μ fd.fref (((List.range vs.length).map Level.param).map (evalTotal (σOf vs)))) _) _
    rw [map_param_σOf, push_append]
    exact fapps_congr hfam _
  obtain ⟨v, hv0⟩ := htyp (ps ++ xs) hz
  have hv : fapps (famVal M W4 (σOf vs) fd) (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0)))) ∈
      Ed M (den M (σOf vs) (push (ps ++ xs) ρ0) (.sort v)) := mem_congr_left hR hv0
  refine mem_congr_right (ed_congr M hR).symm ?_
  have hne := ne_of_mem_sort hU hv
  have hisl : (ri.map (den M (σOf vs) (push xs (push ps ρ0)))).length = fd.indices.length := by
    rw [List.length_map, hq]
  have hcf : CtorFits M (σOf vs) fd.ctors (push ps ρ0) (ri.map (den M (σOf vs) (push xs (push ps ρ0))))
      j xs := ⟨(fs, ri), hj, hxs, LEq.refl _⟩
  generalize ri.map (den M (σOf vs) (push xs (push ps ρ0))) = is at hv hne hisl hcf ⊢
  have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 (ps ++ is) :=
    fits_of_fapps_ne M (σOf vs) (famEnd_resp M W4 (σOf vs) fd) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 (ps ++ is)
      (by rw [List.length_append, List.length_append, hisl, hpl, hnp]) hne
  have he := fapps_piLam M (σOf vs) (famEnd_resp M W4 (σOf vs) fd) (.sort fd.resLevel)
    (fd.params ++ fd.indices) ρ0 (ps ++ is) hfit
  refine mem_congr_right (ed_congr M he).symm ?_
  have hshift : shiftρ fd.indices.length (push (ps ++ is) ρ0) = push ps ρ0 := by
    rw [push_append, ← hisl, shiftρ_push]
  have hlast : lastVals fd.indices.length (push (ps ++ is) ρ0) = is := by
    rw [push_append, ← hisl, lastVals_push]
  show ctorEnd M (σOf vs) fd j fs.length (push (ps ++ xs) ρ0) ∈
    Ed M (famEnd M W4 (σOf vs) fd (push (ps ++ is) ρ0))
  unfold ctorEnd famEnd cond
  rw [hshift, hlast]
  cases hd : M.dec (evalTotal (σOf vs) fd.resLevel = 0) with
  | isTrue h0 =>
      refine mem_congr_right (ed_tyv M (dich_tv _)).symm ?_
      exact mem_tv.mpr ⟨⟨j, xs, hcf⟩, Equiv.rfl⟩
  | isFalse h0 =>
      refine mem_congr_right (ed_tyv M (TypeFib_dich M W4 _ _ _ _ _)).symm ?_
      have hlx : lastVals fs.length (push (ps ++ xs) ρ0) = xs := by
        rw [push_append, ← hxl, lastVals_push]
      rw [hlx]
      have ht := mem_FitSetT M W4 _ _ fs (push ps ρ0) xs hxs (hsmall h0 ps xs hps hxs)
      have hb := mem_BoundT M W4 _ (σOf vs) (push ps ρ0) 0 fd.ctors j (fs, ri) hj ht
      rw [Nat.zero_add] at hb
      obtain ⟨i, hi⟩ := hb
      exact mem_sep.mpr ⟨i, ⟨j, xs, hcf, hi⟩, hi⟩

end PSet

end Rcic.F3
