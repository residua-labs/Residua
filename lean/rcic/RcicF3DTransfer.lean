import rcic.RcicF3WhnfSyn
import rcic.RcicF3FamLim
import rcic.RcicF3RecCore
import rcic.RcicF3Rec
import rcic.RcicF3Ctor
import rcic.RcicF3FieldSmall

/-!
# F3 D-3: transfer between a group's fields and their normal forms

The model of a group with δ-hidden fields is built from the **normalized**
fields (`normField`); the environment's syntax carries the original ones. The
two agree at the final table, at every environment fitting the context the
field is typed in:

- `TelAgree`: two telescopes denote the same types along fitting prefixes;
  fitting (`telFits_iff_of_agree`), smallness and constructor fitting transfer;
- `CtorsAgree` / `famEnd_agree` / `famVal_agree`: a group's fibre and value
  are the same for agreeing constructor lists. `famVal` is a telescope
  abstraction, so only the fitting environments matter (`piLam_congr_fits`,
  from a congruence of `lamVal` on its domain);
- `telAgree_of_pointwise` / `telAgree_of_typings`: the fields and their
  weak-head normal forms agree, from sound typings of the fields
  (`den_whnf_typed4`);
- `whnfFuel_congr_env`: normalization reads only the transparent bodies, so
  the admission environment and a constructor's walk environment agree;
- `RecDataAgree.recEnd_eq`: the recursor's value reads a group's data only
  through counts, result indices and the occurrence of the family in each
  field, so it is the same for the normalized data.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-! ### congruences on the domain -/

/-- `sImage` congruence, pointwise on the elements of the set. -/
theorem sImage_congr_mem {h h' : PSet.{T} → PSet.{T}} {s : PSet.{T}}
    (hh : ∀ a, a ∈ s → Equiv (h a) (h' a)) : Equiv (sImage h s) (sImage h' s) := by
  apply ext; intro x; constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hh _ ⟨i, Equiv.rfl⟩).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hh _ ⟨i, Equiv.rfl⟩).trans hi⟩

/-- `mkLam` congruence, pointwise on the domain. -/
theorem mkLam_congr_dom {g g' : PSet.{T} → PSet.{T}} {A : PSet.{T}} (hg : ∀ a, a ∈ A → Equiv (g a) (g' a)) :
    Equiv (mkLam g A) (mkLam g' A) :=
  sImage_congr_mem fun a ha => ordPair_congr Equiv.rfl (hg a ha)

/-- `lamVal` congruence, pointwise on the domain: the value of an abstraction
reads its body only at the elements of its domain. -/
theorem lamVal_congr_dom (M : Interp.{T}) {A : PSet.{T}} {b b' : PSet.{T} → PSet.{T}}
    (hb : ∀ x, x ∈ Ed M A → Equiv (b x) (b' x)) : Equiv (lamVal M A b) (lamVal M A b') :=
  cond_congr ⟨fun h x hx => (hb x hx).symm.trans (h x hx), fun h x hx => (hb x hx).trans (h x hx)⟩
    Equiv.rfl (mkLam_congr_dom hb)

/-- `piLam` congruence along a telescope, for end values agreeing at the
fitting environments. -/
theorem piLam_congr_fits (M : Interp.{T}) (σ : Nat → Nat) {g g' : (Nat → PSet.{T}) → PSet.{T}} (b : Expr Nat)
    (hb : ∀ A B, b ≠ .pi A B) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (∀ xs, TelFits M σ Ds ρ xs → Equiv (g (push xs ρ)) (g' (push xs ρ))) →
    Equiv (piLam M σ g ρ (policyPi Ds b)) (piLam M σ g' ρ (policyPi Ds b))
  | [], ρ, h => by
      have h0 : Equiv (g ρ) (g' ρ) := h [] trivial
      cases b with
      | pi A B => exact absurd rfl (hb A B)
      | bvar _ => exact h0
      | sort _ => exact h0
      | const _ _ => exact h0
      | app _ _ => exact h0
      | lam _ _ => exact h0
      | letE _ _ _ => exact h0
      | lit _ => exact h0
  | A :: Ds, ρ, h => by
      show Equiv (lamVal M (den M σ ρ A) fun x => piLam M σ g (vcons x ρ) (policyPi Ds b))
        (lamVal M (den M σ ρ A) fun x => piLam M σ g' (vcons x ρ) (policyPi Ds b))
      exact lamVal_congr_dom M fun x hx =>
        piLam_congr_fits M σ b hb Ds (vcons x ρ) fun xs hxs => h (x :: xs) ⟨hx, hxs⟩

/-! ### telescope agreement -/

/-- Two telescopes denote the same types along every fitting prefix. -/
def TelAgree (M : Interp.{T}) (σ : Nat → Nat) : List (Expr Nat) → List (Expr Nat) → (Nat → PSet.{T}) → Prop
  | [], [], _ => True
  | A :: Fs, A' :: Fs', ρ =>
      Equiv (den M σ ρ A) (den M σ ρ A') ∧ ∀ x, x ∈ Ed M (den M σ ρ A) → TelAgree M σ Fs Fs' (vcons x ρ)
  | _, _, _ => False

theorem TelAgree.refl (M : Interp.{T}) (σ : Nat → Nat) : (Fs : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    TelAgree M σ Fs Fs ρ
  | [], _ => trivial
  | _ :: Fs, ρ => ⟨Equiv.rfl, fun x _ => TelAgree.refl M σ Fs (vcons x ρ)⟩

/-- Fitting transfers along agreeing telescopes. -/
theorem telFits_iff_of_agree (M : Interp.{T}) (σ : Nat → Nat) : {Fs Fs' : List (Expr Nat)} → {ρ : Nat → PSet.{T}} →
    TelAgree M σ Fs Fs' ρ → ∀ xs, TelFits M σ Fs ρ xs ↔ TelFits M σ Fs' ρ xs
  | [], [], _, _, [] => Iff.rfl
  | [], [], _, _, _ :: _ => Iff.rfl
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, _, _, [] => Iff.rfl
  | A :: Fs, A' :: Fs', ρ, ⟨hA, hr⟩, x :: xs => by
      show (x ∈ Ed M (den M σ ρ A) ∧ TelFits M σ Fs (vcons x ρ) xs) ↔
        (x ∈ Ed M (den M σ ρ A') ∧ TelFits M σ Fs' (vcons x ρ) xs)
      constructor
      · rintro ⟨hx, hxs⟩
        exact ⟨mem_congr_right (ed_congr M hA) hx, (telFits_iff_of_agree M σ (hr x hx) xs).mp hxs⟩
      · rintro ⟨hx, hxs⟩
        have hx' := mem_congr_right (ed_congr M hA.symm) hx
        exact ⟨hx', (telFits_iff_of_agree M σ (hr x hx') xs).mpr hxs⟩

/-- Smallness along fitting values transfers along agreeing telescopes. -/
theorem smallAlong_iff_of_agree (M : Interp.{T}) (σ : Nat → Nat) (W : PSet.{T}) :
    {Fs Fs' : List (Expr Nat)} → {ρ : Nat → PSet.{T}} → TelAgree M σ Fs Fs' ρ → ∀ xs, TelFits M σ Fs ρ xs →
      (SmallAlong M σ W Fs ρ xs ↔ SmallAlong M σ W Fs' ρ xs)
  | [], [], _, _, _, _ => Iff.rfl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, _, _, [], hf => hf.elim
  | A :: Fs, A' :: Fs', ρ, ⟨hA, hr⟩, x :: xs, ⟨hx, hxs⟩ => by
      show (Ed M (den M σ ρ A) ∈ W ∧ SmallAlong M σ W Fs (vcons x ρ) xs) ↔
        (Ed M (den M σ ρ A') ∈ W ∧ SmallAlong M σ W Fs' (vcons x ρ) xs)
      have e := ed_congr M hA
      constructor
      · rintro ⟨hW, hs⟩
        exact ⟨mem_congr_left e hW, (smallAlong_iff_of_agree M σ W (hr x hx) xs hxs).mp hs⟩
      · rintro ⟨hW, hs⟩
        exact ⟨mem_congr_left e.symm hW, (smallAlong_iff_of_agree M σ W (hr x hx) xs hxs).mpr hs⟩

/-- Agreeing telescopes from pointwise agreement of the fields at fitting prefixes. -/
theorem telAgree_of_pointwise (M : Interp.{T}) (σ : Nat → Nat) :
    (Fs Fs' : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → Fs'.length = Fs.length →
    (∀ k (hk : k < Fs.length) (hk' : k < Fs'.length) xs, TelFits M σ (Fs.take k) ρ xs →
      Equiv (den M σ (push xs ρ) (Fs[k]'hk)) (den M σ (push xs ρ) (Fs'[k]'hk'))) →
    TelAgree M σ Fs Fs' ρ
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | _ :: _, [], _, hl, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | A :: Fs, A' :: Fs', ρ, hl, h => by
      refine ⟨h 0 (Nat.succ_pos _) (Nat.succ_pos _) [] trivial, fun x hx => ?_⟩
      refine telAgree_of_pointwise M σ Fs Fs' (vcons x ρ) (Nat.succ.inj hl) fun k hk hk' xs hxs => ?_
      exact h (k + 1) (Nat.succ_lt_succ hk) (Nat.succ_lt_succ hk') (x :: xs) ⟨hx, hxs⟩

/-! ### agreeing constructor lists -/

/-- Constructor lists agreeing at a parameter environment: same length, same
result indices, agreeing field telescopes. -/
structure CtorsAgree (M : Interp.{T}) (σ : Nat → Nat) (cs cs' : List (List (Expr Nat) × List (Expr Nat)))
    (ρp : Nat → PSet.{T}) : Prop where
  len : cs'.length = cs.length
  agree : ∀ (j : Nat) (c c' : List (Expr Nat) × List (Expr Nat)), cs[j]? = some c → cs'[j]? = some c' →
    TelAgree M σ c.1 c'.1 ρp ∧ c'.2 = c.2

theorem CtorsAgree.get {M : Interp.{T}} {σ : Nat → Nat} {cs cs' : List (List (Expr Nat) × List (Expr Nat))}
    {ρp : Nat → PSet.{T}} (h : CtorsAgree M σ cs cs' ρp) {j : Nat} {c : List (Expr Nat) × List (Expr Nat)}
    (hc : cs[j]? = some c) : ∃ c', cs'[j]? = some c' ∧ TelAgree M σ c.1 c'.1 ρp ∧ c'.2 = c.2 := by
  have hj : j < cs'.length := by rw [h.len]; exact (List.getElem?_eq_some_iff.mp hc).1
  exact ⟨cs'[j], List.getElem?_eq_getElem hj, h.agree j c _ hc (List.getElem?_eq_getElem hj)⟩

theorem CtorsAgree.get' {M : Interp.{T}} {σ : Nat → Nat} {cs cs' : List (List (Expr Nat) × List (Expr Nat))}
    {ρp : Nat → PSet.{T}} (h : CtorsAgree M σ cs cs' ρp) {j : Nat} {c' : List (Expr Nat) × List (Expr Nat)}
    (hc' : cs'[j]? = some c') : ∃ c, cs[j]? = some c ∧ TelAgree M σ c.1 c'.1 ρp ∧ c'.2 = c.2 := by
  have hj : j < cs.length := by rw [← h.len]; exact (List.getElem?_eq_some_iff.mp hc').1
  exact ⟨cs[j], List.getElem?_eq_getElem hj, h.agree j _ c' (List.getElem?_eq_getElem hj) hc'⟩

/-- Constructor fitting transfers. -/
theorem ctorFits_iff_of_agree (M : Interp.{T}) (σ : Nat → Nat) {cs cs' : List (List (Expr Nat) × List (Expr Nat))}
    {ρp : Nat → PSet.{T}} (h : CtorsAgree M σ cs cs' ρp) (is : List PSet.{T}) (j : Nat) (xs : List PSet.{T}) :
    CtorFits M σ cs ρp is j xs ↔ CtorFits M σ cs' ρp is j xs := by
  constructor
  · rintro ⟨c, hc, hf, hi⟩
    obtain ⟨c', hc', hag, hri⟩ := h.get hc
    refine ⟨c', hc', (telFits_iff_of_agree M σ hag xs).mp hf, ?_⟩
    rw [hri]; exact hi
  · rintro ⟨c', hc', hf, hi⟩
    obtain ⟨c, hc, hag, hri⟩ := h.get' hc'
    refine ⟨c, hc, (telFits_iff_of_agree M σ hag xs).mpr hf, ?_⟩
    rw [← hri]; exact hi

/-- A `Type` fibre is the same for agreeing constructor lists. -/
theorem typeFib_agree (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    {cs cs' : List (List (Expr Nat) × List (Expr Nat))} {ρp : Nat → PSet.{T}} (h : CtorsAgree M σ cs cs' ρp)
    (is : List PSet.{T}) : Equiv (TypeFib M W k σ cs ρp is) (TypeFib M W k σ cs' ρp is) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨j, xs, c, hc, hcf, he, hsm⟩ := mem_TypeFib.mp hz
    obtain ⟨c', hc', hag, _⟩ := h.get hc
    have hf : TelFits M σ c.1 ρp xs := by
      rcases id hcf with ⟨c0, hc0, hf0, _⟩
      rw [hc] at hc0
      cases Option.some.inj hc0
      exact hf0
    exact mem_TypeFib.mpr ⟨j, xs, c', hc', (ctorFits_iff_of_agree M σ h is j xs).mp hcf, he,
      (smallAlong_iff_of_agree M σ (W k) hag xs hf).mp hsm⟩
  · intro hz
    obtain ⟨j, xs, c', hc', hcf, he, hsm⟩ := mem_TypeFib.mp hz
    obtain ⟨c, hc, hag, _⟩ := h.get' hc'
    have hcf0 := (ctorFits_iff_of_agree M σ h is j xs).mpr hcf
    have hf : TelFits M σ c.1 ρp xs := by
      rcases id hcf0 with ⟨c0, hc0, hf0, _⟩
      rw [hc] at hc0
      cases Option.some.inj hc0
      exact hf0
    exact mem_TypeFib.mpr ⟨j, xs, c, hc, hcf0, he, (smallAlong_iff_of_agree M σ (W k) hag xs hf).mpr hsm⟩

/-- A `Prop` fibre is the same for agreeing constructor lists. -/
theorem propFib_agree (M : Interp.{T}) (σ : Nat → Nat) {cs cs' : List (List (Expr Nat) × List (Expr Nat))}
    {ρp : Nat → PSet.{T}} (h : CtorsAgree M σ cs cs' ρp) (is : List PSet.{T}) :
    Equiv (PropFib M σ cs ρp is) (PropFib M σ cs' ρp is) :=
  tv_congr ⟨fun ⟨j, xs, hc⟩ => ⟨j, xs, (ctorFits_iff_of_agree M σ h is j xs).mp hc⟩,
    fun ⟨j, xs, hc⟩ => ⟨j, xs, (ctorFits_iff_of_agree M σ h is j xs).mpr hc⟩⟩

/-- The family's end value is the same for agreeing constructor lists. -/
theorem famEnd_agree (M : Interp.{T}) (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (cs' : List (List (Expr Nat) × List (Expr Nat))) (ρ : Nat → PSet.{T})
    (h : CtorsAgree M σ fd.ctors cs' (shiftρ fd.indices.length ρ)) :
    Equiv (famEnd M W σ fd ρ) (famEnd M W σ { fd with ctors := cs' } ρ) := by
  unfold famEnd
  exact cond_congr Iff.rfl (tyv_congr (propFib_agree M σ h _)) (tyv_congr (typeFib_agree M W _ σ h _))

/-- **The family's value is the same for constructor lists agreeing at every
fitting parameter environment.** -/
theorem famVal_agree (M : Interp.{T}) (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (cs' : List (List (Expr Nat) × List (Expr Nat)))
    (h : ∀ ps, TelFits M σ fd.params (fun _ => pempty) ps →
      CtorsAgree M σ fd.ctors cs' (push ps (fun _ => pempty))) :
    Equiv (famVal M W σ fd) (famVal M W σ { fd with ctors := cs' }) := by
  show Equiv (piLam M σ (famEnd M W σ fd) (fun _ => pempty) (policyPi (fd.params ++ fd.indices) (.sort fd.resLevel)))
    (piLam M σ (famEnd M W σ { fd with ctors := cs' }) (fun _ => pempty)
      (policyPi (fd.params ++ fd.indices) (.sort fd.resLevel)))
  refine piLam_congr_fits M σ (.sort fd.resLevel) (fun _ _ h => Expr.noConfusion h) _ _ fun xs hxs => ?_
  obtain ⟨ps, is, rfl, hps, his⟩ := TelFits_split fd.params fd.indices _ xs hxs
  have hl : is.length = fd.indices.length := his.length
  refine famEnd_agree M W σ fd cs' _ ?_
  rw [push_append, ← hl, shiftρ_push]
  exact h ps hps

/-! ### agreement from typings -/

/-- A typed field and its weak-head normal form agree at the fitting prefixes
of its telescope: the typed source of `TelAgree`. -/
theorem telAgree_of_typings (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound (mkM P μ) σ K E n) (hbodies : BodiesOK E σ K)
    (D : List (Expr Nat)) (zs : List PSet.{4}) (hz : TelFits (mkM P μ) σ D ρ0 zs)
    (Fs Fs' : List (Expr Nat)) (hl : Fs'.length = Fs.length)
    (hty : ∀ k (hk : k < Fs.length), ∃ l : Level,
      ∃ d : HasTyT E n (policyPrefixContext (D ++ Fs) (D.length + k)) (Fs[k]'hk) (.sort l), LOKt σ 4 K d)
    (hw : ∀ k (hk : k < Fs.length) (hk' : k < Fs'.length),
      Fs'[k]'hk' = Fs[k]'hk ∨ ∃ fuel, whnfFuel E fuel (Fs[k]'hk) = some (Fs'[k]'hk')) :
    TelAgree (mkM P μ) σ Fs Fs' (push zs ρ0) := by
  refine telAgree_of_pointwise (mkM P μ) σ Fs Fs' (push zs ρ0) hl fun k hk hk' xs hxs => ?_
  rcases hw k hk hk' with he | ⟨fuel, hwf⟩
  · rw [he]; exact Equiv.rfl
  · obtain ⟨l, d, hd⟩ := hty k hk
    have hzx : TelFits (mkM P μ) σ (D ++ Fs.take k) ρ0 (zs ++ xs) := TelFits.append hz hxs
    have hzl : zs.length = D.length := hz.length
    have hxl : xs.length = (Fs.take k).length := hxs.length
    have hfits := fits_prefixContext (mkM P μ) σ (D ++ Fs.take k) ρ0 (zs ++ xs) hzx (D ++ Fs.take k).length
      (Nat.le_refl _)
    have hctx : policyPrefixContext (D ++ Fs) (D.length + k) =
        ((D ++ Fs.take k).take (D ++ Fs.take k).length).reverse.map LocalDecl.assumption := by
      unfold policyPrefixContext
      rw [List.take_length, List.take_append_eq_append_take, List.take_of_length_le (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
    have hzs : (zs ++ xs).take (D ++ Fs.take k).length = zs ++ xs := by
      rw [List.take_of_length_le]
      rw [List.length_append, List.length_append, hzl, hxl]
      exact Nat.le_refl _
    rw [hzs, ← hctx, push_append] at hfits
    exact (den_whnf_typed4 P μ σ K hE hbodies d hd hwf _ hfits).symm

/-! ### normalization reads only the transparent bodies -/

/-- Two environments with the same transparent bodies normalize alike. -/
theorem whnfFuel_congr_env {E₁ E₂ : ResolvedEnv} (h : ∀ r ls, transparentBody E₁ r ls = transparentBody E₂ r ls) :
    (fuel : Nat) → (e : Expr Nat) → whnfFuel E₁ fuel e = whnfFuel E₂ fuel e
  | 0, _ => rfl
  | fuel + 1, e => by
      simp only [whnfFuel]
      cases hs : appsSpine e with
      | mk hd args =>
        cases hd with
        | lam A b =>
            cases args with
            | nil => rfl
            | cons a args => exact whnfFuel_congr_env h fuel _
        | letE A v b => exact whnfFuel_congr_env h fuel _
        | const r ls =>
            show (match transparentBody E₁ r ls with
                | some body => whnfFuel E₁ fuel (foldApps body args)
                | none => some e) =
              (match transparentBody E₂ r ls with
                | some body => whnfFuel E₂ fuel (foldApps body args)
                | none => some e)
            rw [h r ls]
            cases ht : transparentBody E₂ r ls with
            | none => rfl
            | some body => exact whnfFuel_congr_env h fuel _
        | bvar _ => rfl
        | sort _ => rfl
        | app _ _ => rfl
        | pi _ _ => rfl
        | lit _ => rfl

/-- An environment and an extension by body-less members have the same
transparent bodies. -/
theorem transparentBody_eq_of_sub {E₁ E₂ : ResolvedEnv}
    (hsub : ∀ r m, E₁.members r = some m → E₂.members r = some m)
    (hnew : ∀ r m, E₂.members r = some m → E₁.members r = none → m.body = none) (r : Nat) (ls : List Level) :
    transparentBody E₁ r ls = transparentBody E₂ r ls := by
  unfold transparentBody
  cases h1 : E₁.members r with
  | some m => rw [hsub r m h1]
  | none =>
      cases h2 : E₂.members r with
      | none => rfl
      | some m =>
          show none = (if transparent m.mclass = true then
            (match m.body with | some b => some (instantiateLevels ls b) | none => none) else none)
          rw [hnew r m h2 h1]
          split <;> rfl

/-! ### the recursor's value reads only counts, result indices and occurrences -/

/-- The minor's arguments depend on the fields only through the occurrence of
the family. -/
theorem ihArgs_congr_occ (f : Nat) (g : PSet.{T} → PSet.{T}) :
    (As As' : List (Expr Nat)) → (xs : List PSet.{T}) → As'.length = As.length →
    (∀ k (hk : k < As.length) (hk' : k < As'.length), occursConst f (As'[k]'hk') = occursConst f (As[k]'hk)) →
    ihArgs f g As xs = ihArgs f g As' xs
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, _ => rfl
  | [], _ :: _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | _ :: _, [], _, hl, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, [], _, _ => rfl
  | A :: As, A' :: As', x :: xs, hl, h => by
      have h0 : occursConst f A' = occursConst f A := h 0 (Nat.succ_pos _) (Nat.succ_pos _)
      have ih := ihArgs_congr_occ f g As As' xs (Nat.succ.inj hl)
        (fun k hk hk' => h (k + 1) (Nat.succ_lt_succ hk) (Nat.succ_lt_succ hk'))
      show (if occursConst f A = true then x :: g x :: ihArgs f g As xs else x :: ihArgs f g As xs) =
        (if occursConst f A' = true then x :: g x :: ihArgs f g As' xs else x :: ihArgs f g As' xs)
      rw [h0, ih]

theorem ctorFieldsOf_of_get {fd : FamData} {j : Nat} {c : List (Expr Nat) × List (Expr Nat)}
    (hc : fd.ctors[j]? = some c) : ctorFieldsOf fd j = c.1 := by
  unfold ctorFieldsOf
  rw [List.getD_eq_getElem?_getD, hc]
  rfl

theorem ctorFieldsOf_of_none {fd : FamData} {j : Nat} (hc : fd.ctors[j]? = none) : ctorFieldsOf fd j = [] := by
  unfold ctorFieldsOf
  rw [List.getD_eq_getElem?_getD, hc]
  rfl

/-- Group data agreeing in everything the recursor's value reads. -/
structure RecDataAgree (fd fd' : FamData) : Prop where
  fref : fd'.fref = fd.fref
  indices : fd'.indices = fd.indices
  resLevel : fd'.resLevel = fd.resLevel
  policy : fd'.policy = fd.policy
  len : fd'.ctors.length = fd.ctors.length
  ctor : ∀ (j : Nat) (c c' : List (Expr Nat) × List (Expr Nat)), fd.ctors[j]? = some c → fd'.ctors[j]? = some c' →
    c'.1.length = c.1.length ∧ c'.2 = c.2 ∧
    ∀ k (hk : k < c.1.length) (hk' : k < c'.1.length),
      occursConst fd.fref (c'.1[k]'hk') = occursConst fd.fref (c.1[k]'hk)

theorem RecDataAgree.get {fd fd' : FamData} (h : RecDataAgree fd fd') {j : Nat}
    {c : List (Expr Nat) × List (Expr Nat)} (hc : fd.ctors[j]? = some c) :
    ∃ c', fd'.ctors[j]? = some c' ∧ c'.1.length = c.1.length ∧ c'.2 = c.2 ∧
      ∀ k (hk : k < c.1.length) (hk' : k < c'.1.length),
        occursConst fd.fref (c'.1[k]'hk') = occursConst fd.fref (c.1[k]'hk) := by
  have hj : j < fd'.ctors.length := by rw [h.len]; exact (List.getElem?_eq_some_iff.mp hc).1
  exact ⟨_, List.getElem?_eq_getElem hj, h.ctor j c _ hc (List.getElem?_eq_getElem hj)⟩

theorem RecDataAgree.get_none {fd fd' : FamData} (h : RecDataAgree fd fd') {j : Nat} (hc : fd.ctors[j]? = none) :
    fd'.ctors[j]? = none := by
  rw [List.getElem?_eq_none_iff] at hc ⊢
  rw [h.len]; exact hc

theorem RecDataAgree.ihArgs_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (g : PSet.{T} → PSet.{T}) (j : Nat)
    (xs : List PSet.{T}) : ihArgs fd.fref g (ctorFieldsOf fd' j) xs = ihArgs fd.fref g (ctorFieldsOf fd j) xs := by
  cases hc : fd.ctors[j]? with
  | none => rw [ctorFieldsOf_of_none hc, ctorFieldsOf_of_none (h.get_none hc)]
  | some c =>
      obtain ⟨c', hc', hl, _, hocc⟩ := h.get hc
      rw [ctorFieldsOf_of_get hc, ctorFieldsOf_of_get hc']
      exact (ihArgs_congr_occ fd.fref g c.1 c'.1 xs hl hocc).symm

theorem RecDataAgree.nfOf_agree {fd fd' : FamData} (h : RecDataAgree fd fd') (j : Nat) : nfOf fd' j = nfOf fd j := by
  rw [PSet.nfOf_eq, PSet.nfOf_eq]
  cases hc : fd.ctors[j]? with
  | none => rw [ctorFieldsOf_of_none hc, ctorFieldsOf_of_none (h.get_none hc)]
  | some c =>
      obtain ⟨c', hc', hl, _, _⟩ := h.get hc
      rw [ctorFieldsOf_of_get hc, ctorFieldsOf_of_get hc', hl]

theorem RecDataAgree.recBody_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (M : Interp.{T}) (ms : List PSet.{T})
    (z : PSet.{T}) (g : PSet.{T} → PSet.{T}) : recBody M fd' ms z g = recBody M fd ms z g := by
  unfold recBody
  rw [h.len]
  cases findIdx M (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | none => rfl
  | some j =>
      show fapps (ms.getD j pempty) (ihArgs fd'.fref g (ctorFieldsOf fd' j) (untup (nfOf fd' j) (payload z))) =
        fapps (ms.getD j pempty) (ihArgs fd.fref g (ctorFieldsOf fd j) (untup (nfOf fd j) (payload z)))
      rw [h.fref, h.nfOf_agree, h.ihArgs_eq]

theorem RecDataAgree.recCore_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (M : Interp.{T}) (ms : List PSet.{T}) :
    recCore M fd' ms = recCore M fd ms := by
  show WellFounded.fix memT_wf (fun z IH => recBody M fd' ms z fun x =>
      @dite _ (MemT x z) (M.dec _) (fun h => IH x h) (fun _ => pempty)) =
    WellFounded.fix memT_wf (fun z IH => recBody M fd ms z fun x =>
      @dite _ (MemT x z) (M.dec _) (fun h => IH x h) (fun _ => pempty))
  exact congrArg (WellFounded.fix memT_wf) (funext fun z => funext fun IH => h.recBody_eq M ms z _)

theorem RecDataAgree.recon_eq {fd fd' : FamData} (h : RecDataAgree fd fd') {c c' : List (Expr Nat) × List (Expr Nat)}
    (hc : fd.ctors[0]? = some c) (hc' : fd'.ctors[0]? = some c') (is : List PSet.{T}) : recon c' is = recon c is := by
  obtain ⟨hl, hri, _⟩ := h.ctor 0 c c' hc hc'
  unfold recon
  rw [hl, hri]

theorem RecDataAgree.propRecEnd_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (m0 : PSet.{T})
    (is : List PSet.{T}) : propRecEnd fd' m0 is = propRecEnd fd m0 is := by
  unfold propRecEnd
  rw [h.policy]
  have hlen := h.len
  cases hp : fd.policy with
  | propOnly =>
      cases fd'.ctors with
      | nil => cases fd.ctors with
        | nil => rfl
        | cons _ rest => cases rest <;> rfl
      | cons _ rest' =>
          cases rest' with
          | nil => cases fd.ctors with
            | nil => rfl
            | cons _ rest => cases rest <;> rfl
          | cons _ _ => cases fd.ctors with
            | nil => rfl
            | cons _ rest => cases rest <;> rfl
  | anySort =>
      cases hc' : fd'.ctors with
      | nil =>
          have hnil : fd.ctors = [] := by
            rw [hc'] at hlen
            exact List.eq_nil_of_length_eq_zero hlen.symm
          rw [hnil]
      | cons c' rest' =>
          cases rest' with
          | nil =>
              cases hc : fd.ctors with
              | nil =>
                  rw [hc', hc] at hlen
                  exact absurd hlen (Nat.succ_ne_zero _)
              | cons c rest =>
                  cases rest with
                  | nil =>
                      show fapps m0 (recon c' is) = fapps m0 (recon c is)
                      rw [h.recon_eq (c := c) (c' := c') (by rw [hc]; rfl) (by rw [hc']; rfl) is]
                  | cons _ _ =>
                      rw [hc', hc] at hlen
                      exact absurd (Nat.succ.inj hlen).symm (Nat.succ_ne_zero _)
          | cons _ _ =>
              cases hc : fd.ctors with
              | nil => rfl
              | cons c rest =>
                  cases rest with
                  | nil =>
                      rw [hc', hc] at hlen
                      exact absurd (Nat.succ.inj hlen) (Nat.succ_ne_zero _)
                  | cons _ _ => rfl

/-- A constructor's end value is the same for agreeing group data. -/
theorem RecDataAgree.ctorEnd_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (M : Interp.{T}) (σ : Nat → Nat)
    (j nf : Nat) : ctorEnd M σ fd' j nf = ctorEnd M σ fd j nf := by
  unfold ctorEnd
  rw [h.resLevel]

/-- **The recursor's value is the same for agreeing group data.** -/
theorem RecDataAgree.recEnd_eq {fd fd' : FamData} (h : RecDataAgree fd fd') (M : Interp.{T}) (σ : Nat → Nat) :
    recEnd M σ fd' = recEnd M σ fd := by
  funext ρ
  unfold recEnd
  rw [h.resLevel, h.indices, h.len, h.recCore_eq, h.propRecEnd_eq]

/-! ### agreement is invariant under instances agreeing on the data's levels -/

/-- Telescope agreement transports between instances agreeing below `k`, for
telescopes whose levels are bounded by `k`. -/
theorem TelAgree_levels (M : Interp.{T}) {σ σ' : Nat → Nat} {k : Nat} (h : ∀ i, i < k → σ i = σ' i) :
    (Fs Fs' : List (Expr Nat)) → ExprsBounded k Fs → ExprsBounded k Fs' → (ρ : Nat → PSet.{T}) →
    TelAgree M σ Fs Fs' ρ → TelAgree M σ' Fs Fs' ρ
  | [], [], _, _, _, hA => hA
  | [], _ :: _, _, _, _, hA => hA
  | _ :: _, [], _, _, _, hA => hA
  | A :: Fs, A' :: Fs', hb, hb', ρ, hA => by
      obtain ⟨h1, h2⟩ := hA
      refine ⟨?_, fun x hx => ?_⟩
      · rw [← den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ,
          ← den_levels_agree M h A' (hb' A' (List.mem_cons_self _ _)) ρ]
        exact h1
      · rw [← den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ] at hx
        exact TelAgree_levels M h Fs Fs' (fun e he => hb e (List.mem_cons_of_mem _ he))
          (fun e he => hb' e (List.mem_cons_of_mem _ he)) (vcons x ρ) (h2 x hx)

/-- Constructor-list agreement transports likewise. -/
theorem CtorsAgree_levels (M : Interp.{T}) {σ σ' : Nat → Nat} {k : Nat} (h : ∀ i, i < k → σ i = σ' i)
    (cs cs' : List (List (Expr Nat) × List (Expr Nat))) (hb : ∀ c, c ∈ cs → ExprsBounded k c.1)
    (hb' : ∀ c, c ∈ cs' → ExprsBounded k c.1) (ρp : Nat → PSet.{T}) (hA : CtorsAgree M σ cs cs' ρp) :
    CtorsAgree M σ' cs cs' ρp :=
  ⟨hA.len, fun j c c' hc hc' =>
    ⟨TelAgree_levels M h c.1 c'.1 (hb c (List.getElem?_mem hc)) (hb' c' (List.getElem?_mem hc')) ρp
      (hA.agree j c c' hc hc').1, (hA.agree j c c' hc hc').2⟩⟩

end PSet

end Rcic.F3
