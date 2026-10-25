import rcic.RcicF3Layout

/-!
# F3 S5a-16: the fields of a `Type` family lie in its stage

`field_small`: at a constructor instance, every field type of a constructor
view denotes a type whose element set lies in the stage of the family's
level, given a sound reading of the view's field typings at their recorded
levels (`CtorTypedT`) and the field universe clause (`FieldUniverseAdmitted`).
The group step applies it to each constructor's own admission, at the real
table, in the environment the constructor is admitted in.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs)

namespace PSet

theorem push_take_succ (zs : List PSet.{4}) (k : Nat) (hk : k < zs.length) (ρ : Nat → PSet.{4}) :
    push (zs.take (k + 1)) ρ = vcons (zs[k]) (push (zs.take k) ρ) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, push_append]
  rfl

/-- An environment fitting a telescope realizes its prefix contexts. -/
theorem fits_prefixContext (M : Interp.{4}) (σ : Nat → Nat) (D : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (zs : List PSet.{4}) (hz : TelFits M σ D ρ zs) :
    ∀ k, k ≤ D.length → Fits M σ ((D.take k).reverse.map LocalDecl.assumption) (push (zs.take k) ρ)
  | 0, _ => by simp [Fits]
  | k + 1, hk => by
      have hzl : zs.length = D.length := hz.length
      have hkD : k < D.length := by omega
      have ih := fits_prefixContext M σ D ρ zs hz k (by omega)
      rw [List.take_succ, List.getElem?_eq_getElem hkD, List.reverse_append, push_take_succ zs k (by omega)]
      refine ⟨ih, ?_⟩
      have := TelFits_get D ρ zs hz k hkD
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < zs.length by omega)] using this

theorem leN_evalTotal {l l' : Level} (h : leN l l') (σ : Nat → Nat) : evalTotal σ l ≤ evalTotal σ l' :=
  h _ _ _ (eval_some σ l) (eval_some σ l')

theorem smallAlong_of_pointwise (M : Interp.{4}) (σ : Nat → Nat) (W : PSet.{4}) :
    (fs : List (Expr Nat)) → (ρ : Nat → PSet.{4}) → (xs : List PSet.{4}) →
    (∀ j (hj : j < fs.length), Ed M (den M σ (push (xs.take j) ρ) (fs[j]'hj)) ∈ W) → SmallAlong M σ W fs ρ xs
  | [], _, _, _ => trivial
  | _ :: _, _, [], _ => trivial
  | A :: fs, ρ, x :: xs, h => ⟨h 0 (Nat.succ_pos _), smallAlong_of_pointwise M σ W fs (vcons x ρ) xs fun j hj =>
      h (j + 1) (by simp; omega)⟩

/-- **The fields of a `Type` family lie in its stage.** -/
theorem field_small (P : Premises4) (μ μs : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {Epre E0 : ResolvedEnv}
    {fam : PolicyFamilyView E0} {cmem : CheckedMember} (cv : PolicyConstructorView E0 fam cmem)
    (vs : List Nat) (h07 : FieldUniverseAdmitted cv)
    (hES0 : EnvSound (mkM P μs) (σOf vs) K E0 fam.member.arity)
    (hB2 : ∀ k : Fin (cv.parameters ++ cv.fields).length,
      ∃ d : HasTyT E0 fam.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
        ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d)
    (hag : AgreeOn μs μ (Dom Epre)) (hD : RefsIn (Dom Epre) (cv.parameters ++ cv.fields))
    (h0 : evalTotal (σOf vs) fam.resultLevel ≠ 0) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) cv.parameters ρ0 ps)
    (hxs : TelFits (mkM P μ) (σOf vs) cv.fields (push ps ρ0) xs) :
    SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fam.resultLevel)) cv.fields (push ps ρ0) xs := by
  have hzs : TelFits (mkM P μ) (σOf vs) (cv.parameters ++ cv.fields) ρ0 (ps ++ xs) := TelFits.append hps hxs
  have hzs' : TelFits (mkM P μs) (σOf vs) (cv.parameters ++ cv.fields) ρ0 (ps ++ xs) :=
    (TelFits_agreeOn P hag (σOf vs) _ hD ρ0 _).mpr hzs
  have hpl : ps.length = cv.parameters.length := hps.length
  refine smallAlong_of_pointwise _ _ _ _ _ _ fun j hj => ?_
  let jF : Fin cv.fields.length := ⟨j, hj⟩
  obtain ⟨d, hd⟩ := hB2 (cv.fieldIndex jF)
  have hidx : (cv.fieldIndex jF).val = cv.parameters.length + j := rfl
  have hk : cv.parameters.length + j ≤ (cv.parameters ++ cv.fields).length := by simp; omega
  have hfits := fits_prefixContext (mkM P μs) (σOf vs) _ ρ0 _ hzs' (cv.fieldIndex jF).val (by rw [hidx]; exact hk)
  have hs := sound_ty (P.good _ rfl) hES0 d hd _ hfits
  have hget : (cv.parameters ++ cv.fields)[(cv.fieldIndex jF).val]'(cv.fieldIndex jF).isLt = cv.fields[j] := by
    have h1 : cv.parameters.length ≤ (cv.fieldIndex jF).val := by rw [hidx]; omega
    rw [List.getElem_append_right h1]
    congr 1
    rw [hidx]; omega
  have henv : push ((ps ++ xs).take (cv.fieldIndex jF).val) ρ0 = push (xs.take j) (push ps ρ0) := by
    rw [hidx, ← hpl, List.take_append_eq_append_take, List.take_of_length_le (by omega), push_append,
      Nat.add_sub_cancel_left]
  rw [hget, henv] at hs
  -- the field's level is bounded by the family's
  have hlev : evalTotal (σOf vs) (cv.domainsTyped.levels (cv.fieldIndex jF)) ≤ evalTotal (σOf vs) fam.resultLevel := by
    rcases h07 jF with hp | ⟨_, hle⟩
    · exact absurd (hp _) h0
    · exact leN_evalTotal hle _
  -- the element set lies in the stage
  have hx : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) cv.fields[j] ∈
      U W4 (evalTotal (σOf vs) (cv.domainsTyped.levels (cv.fieldIndex jF))) := by
    have : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) (.sort (cv.domainsTyped.levels (cv.fieldIndex jF))) =
        tyv (U W4 (evalTotal (σOf vs) (cv.domainsTyped.levels (cv.fieldIndex jF)))) := rfl
    rw [this] at hs
    exact mem_congr_right (ed_tyv _ (U4_dich _)) hs
  have hW := ed_mem_W4_of_mem_U P (mkM P μs) hlev (Nat.pos_of_ne_zero h0) hx
  have hden : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) cv.fields[j] =
      den (mkM P μ) (σOf vs) (push (xs.take j) (push ps ρ0)) cv.fields[j] :=
    den_agreeOn P hag _ _ (hD _ (List.mem_append_right _ (List.getElem_mem _))) _
  rw [hden] at hW
  exact hW

/-- **Proof fields denote propositions**: fields typed at levels that evaluate
to `0`, by bounded derivations sound at the model, form a telescope of
propositions at fitting parameters. -/
theorem propTel_of_typings (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S : ResolvedEnv}
    {ar : Nat} (vs : List Nat) (Ps Fs : List (Expr Nat))
    (hES : EnvSound (mkM P μ) (σOf vs) K S ar)
    (hB : ∀ k : Fin Fs.length, ∃ l : Level, evalTotal (σOf vs) l = 0 ∧
      ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val)) (Fs[k]) (.sort l), LOKt (σOf vs) 4 K d)
    (ps : List PSet.{4}) (hps : TelFits (mkM P μ) (σOf vs) Ps ρ0 ps) :
    PropTel (mkM P μ) (σOf vs) Fs (push ps ρ0) := by
  have hpl : ps.length = Ps.length := hps.length
  suffices H : ∀ (d m : Nat), Fs.length - m = d → ∀ zs : List PSet.{4}, zs.length = m →
      TelFits (mkM P μ) (σOf vs) (Ps ++ Fs.take m) ρ0 (ps ++ zs) →
      PropTel (mkM P μ) (σOf vs) (Fs.drop m) (push zs (push ps ρ0)) by
    have := H Fs.length 0 (Nat.sub_zero _) [] rfl (by simpa using hps)
    simpa using this
  intro d
  induction d with
  | zero =>
      intro m hd zs _ _
      rw [List.drop_eq_nil_of_le (by omega)]
      trivial
  | succ d ih =>
      intro m hd zs hzl hz
      have hm : m < Fs.length := by omega
      rw [List.drop_eq_getElem_cons hm]
      have henv : push zs (push ps ρ0) = push (ps ++ zs) ρ0 := (push_append ps zs ρ0).symm
      -- the field's type denotes a proposition
      have hprop : ∀ y, y ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs (push ps ρ0)) Fs[m]) →
          Equiv y pempty := by
        intro y hy
        obtain ⟨l, h0, dd, hdd⟩ := hB ⟨m, hm⟩
        have hctx : policyPrefixContext (Ps ++ Fs) (Ps.length + m) =
            ((Ps ++ Fs.take m).take (Ps ++ Fs.take m).length).reverse.map LocalDecl.assumption := by
          unfold policyPrefixContext
          rw [List.take_length, List.take_append_eq_append_take, List.take_of_length_le (by omega),
            Nat.add_sub_cancel_left]
        have hfits := fits_prefixContext (mkM P μ) (σOf vs) _ ρ0 _ hz (Ps ++ Fs.take m).length (Nat.le_refl _)
        rw [← hctx, List.take_of_length_le (Nat.le_of_eq hz.length)] at hfits
        have hs := sound_ty (P.good _ rfl) hES dd hdd _ hfits
        have e : den (mkM P μ) (σOf vs) (push (ps ++ zs) ρ0) (.sort l) = tyv (U W4 0) := by
          show tyv (U W4 (evalTotal (σOf vs) l)) = _
          rw [h0]
        rw [e] at hs
        have hX := mem_congr_right (ed_tyv _ (U4_dich _)) hs
        rw [henv] at hy
        exact ed_of_mem_U0 _ hX hy
      refine ⟨hprop, fun hin => ?_⟩
      have hz' : TelFits (mkM P μ) (σOf vs) (Ps ++ Fs.take (m + 1)) ρ0 (ps ++ (zs ++ [pempty])) := by
        rw [List.take_succ, List.getElem?_eq_getElem hm, ← List.append_assoc, ← List.append_assoc]
        refine TelFits.append hz ⟨?_, trivial⟩
        rw [← henv]; exact hin
      have := ih (m + 1) (by omega) (zs ++ [pempty]) (by simp [hzl]) hz'
      rw [push_append] at this
      exact this

/-- `field_small` at an arbitrary cut `Ps ++ Fs` of a typed telescope: the fields `Fs` lie in the
stage of the family's level, from a sound bounded typing of every entry (at the levels `lev`) and the
level bound `hlevF` on the entries after the cut. -/
theorem field_small_gen (P : Premises4) (μ μs : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {Epre E0 : ResolvedEnv}
    (ar : Nat) (L Ps Fs : List (Expr Nat)) (hL : Ps ++ Fs = L) (lev : Fin L.length → Level) (resL : Level) (vs : List Nat)
    (hES0 : EnvSound (mkM P μs) (σOf vs) K E0 ar)
    (hB2 : ∀ k : Fin L.length,
      ∃ d : HasTyT E0 ar (policyPrefixContext L k.val) (L[k.val]) (.sort (lev k)),
        LOKt (σOf vs) 4 K d)
    (hag : AgreeOn μs μ (Dom Epre)) (hD : RefsIn (Dom Epre) L)
    (h0 : evalTotal (σOf vs) resL ≠ 0)
    (hlevF : ∀ (j : Fin Fs.length) (hk : Ps.length + j.val < L.length),
      evalTotal (σOf vs) (lev ⟨Ps.length + j.val, hk⟩) ≤ evalTotal (σOf vs) resL)
    (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) Ps ρ0 ps)
    (hxs : TelFits (mkM P μ) (σOf vs) Fs (push ps ρ0) xs) :
    SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) resL)) Fs (push ps ρ0) xs := by
  subst hL
  have hzs : TelFits (mkM P μ) (σOf vs) (Ps ++ Fs) ρ0 (ps ++ xs) := TelFits.append hps hxs
  have hzs' : TelFits (mkM P μs) (σOf vs) (Ps ++ Fs) ρ0 (ps ++ xs) :=
    (TelFits_agreeOn P hag (σOf vs) _ hD ρ0 _).mpr hzs
  have hpl : ps.length = Ps.length := hps.length
  refine smallAlong_of_pointwise _ _ _ _ _ _ fun j hj => ?_
  let jF : Fin Fs.length := ⟨j, hj⟩
  let kF : Fin (Ps ++ Fs).length := ⟨Ps.length + j, by simp only [List.length_append]; omega⟩
  obtain ⟨d, hd⟩ := hB2 kF
  have hidx : kF.val = Ps.length + j := rfl
  have hk : Ps.length + j ≤ (Ps ++ Fs).length := by simp; omega
  have hfits := fits_prefixContext (mkM P μs) (σOf vs) _ ρ0 _ hzs' kF.val (by rw [hidx]; exact hk)
  have hs := sound_ty (P.good _ rfl) hES0 d hd _ hfits
  have hget : (Ps ++ Fs)[kF.val]'kF.isLt = Fs[j] := by
    have h1 : Ps.length ≤ kF.val := by rw [hidx]; omega
    rw [List.getElem_append_right h1]
    congr 1
    rw [hidx]; omega
  have henv : push ((ps ++ xs).take kF.val) ρ0 = push (xs.take j) (push ps ρ0) := by
    rw [hidx, ← hpl, List.take_append_eq_append_take, List.take_of_length_le (by omega), push_append,
      Nat.add_sub_cancel_left]
  rw [hget, henv] at hs
  have hlev : evalTotal (σOf vs) (lev kF) ≤ evalTotal (σOf vs) resL := hlevF jF kF.isLt
  have hx : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) Fs[j] ∈
      U W4 (evalTotal (σOf vs) (lev kF)) := by
    have : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) (.sort (lev kF)) =
        tyv (U W4 (evalTotal (σOf vs) (lev kF))) := rfl
    rw [this] at hs
    exact mem_congr_right (ed_tyv _ (U4_dich _)) hs
  have hW := ed_mem_W4_of_mem_U P (mkM P μs) hlev (Nat.pos_of_ne_zero h0) hx
  have hden : den (mkM P μs) (σOf vs) (push (xs.take j) (push ps ρ0)) Fs[j] =
      den (mkM P μ) (σOf vs) (push (xs.take j) (push ps ρ0)) Fs[j] :=
    den_agreeOn P hag _ _ (hD _ (List.mem_append_right _ (List.getElem_mem _))) _
  rw [hden] at hW
  exact hW


/-! ### the class and the group layout from `WalkRec` -/

end PSet

end Rcic.F3
