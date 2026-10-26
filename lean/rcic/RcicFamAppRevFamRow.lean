import rcic.RcicFamAppRevPiRow
import rcic.RcicFamAppLeftInst
import rcic.RcicNativeFamilyProjection
import rcic.RcicIotaSRRowsTel
import rcic.RcicIATypedMinor
import rcic.RcicIARecIH
import rcic.RcicNativeValleyOf
import rcic.RcicDTRowFields
import rcic.RcicEtaKDecide
import rcic.RcicNativeFamModelTyped

/-!
# RcicFamAppRevFamRow — THE FAMILY ROW of ANY revealed singleton's environment (cc's item 2)

`RcicFamAppRevPiRow` gave rows 1 and 2 of `R.E` for every `R : RevEnv` (the tier's generic B1 shape: an
in-scope base below `f`, a closed level-free index type `I`, `F : Π (i : I), Sort 0` at `f`, `mk` at `f+1`,
the AnySort recursor at `f+2`). This module gives ROW 3 — `TypedRowsWf.famAppRow`'s exact field — for
EVERY inductive member of `R.E` (the base's families and `F` alike), hence **`RevEnv.revTypedRowsWf :
TypedRowsWf R.E n`**.

**Route.** The landed §7.4 reduction `famAppRow_of_piRow_saturation_slotConv` (`RcicFamAppLeftInst`)
builds the row's conclusion from the Π row (`revPiRow`), a saturation package (telescope data) and the
relevant-slot port (a native conversion of the two arguments at every non-Prop slot). Both inputs are read
in the twin: the chain is carried into `R.twin₁` by `trTyConvW`, the twin's own family row (`twin₁Rows`)
gives the level relation, the equal lengths and the pointwise conversions of the `tr`-images along the
stored telescope; each slot's conversion comes back by the identity transport (`bkConv`), is retyped at the
original domain by the round trip of the domain (`trConv_self`), and the two arguments are identified with
their images by the round trip of each argument (`trConv_self`, typed by the Π-row spine inversion of both
spines; the right argument's domain is moved to the left one by DT-012 at `R.E`, which rows 1–2 supply).
The saturation package is the stored type's own telescope (landed: `piResult_mtype_of_inductiveM`, an
inductive member's type is an arity over `inductiveSortLevel`; `instantiateLevels_policyPi_piDomsOf_piTailOf`),
cut at the application's length — the twin's `ConvArgsT` bounds that length by the telescope's (landed
`convArgsT_length_le_piDoms_of_isArity`), so no sort/Π disjointness is needed (under-application is handled
by the residual body). The only telescope facts proved here are about `tr` (`piDomsOf_tr`, `tr_instPrefix`).

**Results.** `RevEnv.revFamAppRow`, `RevEnv.revTypedRowsWf`; the fixture instance in `RcicFamAppRevFixture`.
Axioms ⊆ {propext, Quot.sound}. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin

/-! ## §1 `tr` against telescopes (no environment) -/

section Telescope

variable {f : Nat} {I : Expr Nat}

/-- `tr` commutes with `piDomsOf`: the image of a constant is never a Π. -/
theorem piDomsOf_tr : (e : Expr Nat) → piDomsOf (tr f I e) = (piDomsOf e).map (tr f I)
  | .pi A B => by simp only [tr, piDomsOf, List.map, piDomsOf_tr B]
  | .const r ls => by
      simp only [tr, piDomsOf, List.map]
      generalize hc : trC f I r ls = e'
      cases e' <;> first | rfl | exact absurd hc (trC_not_pi r ls _ _)
  | .bvar _ => rfl
  | .sort _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- `tr` commutes with the prefix instantiation. -/
theorem tr_instPrefix (hclI : ∀ k, lift k 1 I = I) : (as : List (Expr Nat)) → (e : Expr Nat) →
    tr f I (instPrefix as e) = instPrefix (as.map (tr f I)) (tr f I e)
  | [], _ => rfl
  | a :: as, e => by
      rw [instPrefix_cons, List.map_cons, instPrefix_cons, tr_instPrefix hclI as,
        tr_instantiate hclI, tr_lift hclI, List.length_map]

end Telescope

/-! ## §2 the family row -/

namespace RevEnv

variable (R : RevEnv)

/-- the inductive members of `E` are the twin's: the base's families and `F` (never the constructor or
    the recursor). -/
theorem twin₁_of_inductive {r : Nat} {m : CheckedMember} (hm : R.E.members r = some m)
    (hind : m.mclass = .inductiveM) : R.twin₁.members r = some m ∧ r ≠ R.f + 2 := by
  rcases R.members_class hm with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by rw [R.twin₁_agree r hlt]; exact hm, by omega⟩
  · exact ⟨R.twin₁_f, by omega⟩
  · exact absurd hind (by simp [revCtorM])
  · exact absurd hind (by simp [revRecM])

/-- every domain of a member's stored telescope is fixed by `tr`. -/
theorem tr_piDom {r : Nat} {m : CheckedMember} (hm : R.E.members r = some m) {i : Nat} {d : Expr Nat}
    (hd : (piDomsOf m.mtype)[i]? = some d) : tr R.f R.I d = d := by
  have h1 : (piDomsOf m.mtype).map (tr R.f R.I) = piDomsOf m.mtype := by
    rw [← piDomsOf_tr, R.tr_mtype hm]
  have h2 : ((piDomsOf m.mtype).map (tr R.f R.I))[i]? = some (tr R.f R.I d) := by
    rw [List.getElem?_map, hd]; rfl
  rw [h1, hd] at h2
  exact (Option.some.inj h2).symm

variable {n : Nat}

/-- sort uniqueness at `R.E` (DT-012 at a sort, read by row 1). -/
theorem sortUniq {Γ : LCtx} {T : Expr Nat} {u v : Level} (hΓ : CtxWfT R.E n Γ)
    (hu : HasTyT R.E n Γ T (.sort u)) (hv : HasTyT R.E n Γ T (.sort v)) : eqN u v := by
  obtain ⟨tc⟩ := DT012T_type_uniqueness_of_sortRow_piRow R.hW R.revSortRow (R.revPiRow n) hΓ hu hv
  exact R.revSortRow hΓ tc

/-- **ROW 3 (the family row) of the environment of any revealed singleton**, `TypedRowsWf.famAppRow`'s
    exact field: read in the twin, brought back slot by slot, assembled by the landed §7.4 reduction. -/
theorem revFamAppRow {Γ : LCtx} (hΓ : CtxWfT R.E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : R.E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT R.E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT R.E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT R.E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  have hpi : PiRowField R.E n := R.revPiRow n
  obtain ⟨hmT, hne⟩ := R.twin₁_of_inductive hm hind
  let W := R.twinTarget
  have hagree := R.twin₁_agree
  -- into the twin: the row of `tr`'s images
  obtain ⟨hΓ'⟩ := trCtxWfW R W hagree hΓ
  obtain ⟨hty'⟩ := trTyW R W hagree hty hΓ'
  obtain ⟨h'⟩ := trTyConvW R W hagree h hΓ'
  simp only [tr_foldApps, tr, trC_ne R.f R.I hne] at hty' h'
  obtain ⟨eqN, hlenT, hargsT⟩ := (R.twin₁Rows n).famAppRow hΓ' hmT hind hty' h'
  simp only [List.length_map] at hlenT
  -- the stored telescope, instantiated at each level list: an inductive member's type is an arity over a
  -- sort (landed `piResult_mtype_of_inductiveM`), so `policyPi (piDomsOf m.mtype) (.sort u₀)` is `m.mtype`
  obtain ⟨u₀, hpol⟩ : ∃ u₀, m.mtype = policyPi (piDomsOf m.mtype) (.sort u₀) :=
    ⟨NativeValleys.FamModelAudit.inductiveSortLevel R.hW hm hind, by
      have h := policyPi_piDomsOf_piTailOf m.mtype
      rw [NativeValleys.FamModelAudit.piTailOf_eq_piResult,
        NativeValleys.FamModelAudit.piResult_mtype_of_inductiveM R.hW hm hind] at h
      exact h.symm⟩
  have telFull : ∀ ms : List Level, instantiateLevels ms m.mtype =
      policyPi ((piDomsOf m.mtype).map (instantiateLevels ms)) (.sort (instLevel ms u₀)) := by
    intro ms
    have h1 := congrArg (instantiateLevels ms) hpol
    rw [instantiateLevels_policyPi] at h1
    exact h1
  have hargsT' : ConvArgsT R.twin₁ n (trCtx R.f R.I Γ)
      (policyPi ((piDomsOf m.mtype).map (instantiateLevels ls)) (.sort (instLevel ls u₀)))
      (xs.map (tr R.f R.I)) (xs'.map (tr R.f R.I)) := by
    rw [telFull ls] at hargsT; exact hargsT
  have hle : xs.length ≤ (piDomsOf m.mtype).length := by
    have := NativeValleys.FamModelAudit.convArgsT_length_le_piDoms_of_isArity
      (NativeFamilyProjection.familyArity_of_envWfT R.hW r m hm hind) hargsT
    simpa only [List.length_map] using this
  -- the saturation package: the first `xs.length` domains, the residual telescope as the body
  have telL : instantiateLevels ls m.mtype =
      policyPi (((piDomsOf m.mtype).map (instantiateLevels ls)).take xs.length)
        (policyPi (((piDomsOf m.mtype).map (instantiateLevels ls)).drop xs.length)
          (.sort (instLevel ls u₀))) := by
    rw [telFull ls, ← policyPi_append, List.take_append_drop]
  have telR : instantiateLevels ls' m.mtype =
      policyPi (((piDomsOf m.mtype).map (instantiateLevels ls')).take xs.length)
        (policyPi (((piDomsOf m.mtype).map (instantiateLevels ls')).drop xs.length)
          (.sort (instLevel ls' u₀))) := by
    rw [telFull ls', ← policyPi_append, List.take_append_drop]
  have lenXD : (((piDomsOf m.mtype).map (instantiateLevels ls)).take xs.length).length = xs.length := by
    rw [List.length_take, List.length_map]; exact Nat.min_eq_left hle
  have lenXD' : (((piDomsOf m.mtype).map (instantiateLevels ls')).take xs.length).length = xs'.length := by
    rw [List.length_take, List.length_map, Nat.min_eq_left hle]; exact hlenT
  have lenDD : (((piDomsOf m.mtype).map (instantiateLevels ls)).take xs.length).length =
      (((piDomsOf m.mtype).map (instantiateLevels ls')).take xs.length).length := by
    simp only [List.length_take, List.length_map]
  let sat : FamAppSaturation R.E r m ls ls' xs xs' :=
    { doms := ((piDomsOf m.mtype).map (instantiateLevels ls)).take xs.length
      doms' := ((piDomsOf m.mtype).map (instantiateLevels ls')).take xs.length
      U := policyPi (((piDomsOf m.mtype).map (instantiateLevels ls)).drop xs.length)
        (.sort (instLevel ls u₀))
      U' := policyPi (((piDomsOf m.mtype).map (instantiateLevels ls')).drop xs.length)
        (.sort (instLevel ls' u₀))
      telL := telL
      telR := telR
      eqN := eqN
      lenDD := lenDD
      lenXD := lenXD
      lenXD' := lenXD' }
  -- the per-slot typings in `E`: the Π-row spine inversion of both spines
  obtain ⟨⟨_, _, hargsL, _⟩⟩ := hasTyT_spineInv_rows R.hW hpi hΓ hm telL xs lenXD hty
  obtain ⟨_, htyR⟩ := tyConvT_rhsSort R.hW hΓ h ⟨w, hty⟩
  obtain ⟨⟨_, _, hargsR, _⟩⟩ := hasTyT_spineInv_rows R.hW hpi hΓ hm telR xs' lenXD' htyR
  -- the port: at every slot, the twin's conversion of the images, brought back and retyped, between the
  -- round trips of the two arguments
  have hport : RelevantSlotConv R.E n Γ []
      (((piDomsOf m.mtype).map (instantiateLevels ls)).take xs.length) xs xs' := by
    intro i x x' d u hx hx' hd hdT _hu
    simp only [List.nil_append] at hdT ⊢
    have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hx).1
    have hdL : ((piDomsOf m.mtype).map (instantiateLevels ls))[i]? = some d := by
      rw [List.getElem?_take, if_pos hi] at hd; exact hd
    obtain ⟨d₀, hd₀, rfl⟩ : ∃ d₀, (piDomsOf m.mtype)[i]? = some d₀ ∧ d = instantiateLevels ls d₀ := by
      rw [List.getElem?_map] at hdL
      obtain ⟨d₀, h1, h2⟩ := Option.map_eq_some'.mp hdL
      exact ⟨d₀, h1, h2.symm⟩
    have htrd : tr R.f R.I (instantiateLevels ls d₀) = instantiateLevels ls d₀ := by
      rw [tr_instantiateLevels R.hlvlI, R.tr_piDom hm hd₀]
    -- the twin's slot conversion, at the image of the left domain
    have hxm : (xs.map (tr R.f R.I))[i]? = some (tr R.f R.I x) := by
      rw [List.getElem?_map, hx]; rfl
    have hxm' : (xs'.map (tr R.f R.I))[i]? = some (tr R.f R.I x') := by
      rw [List.getElem?_map, hx']; rfl
    obtain ⟨cT⟩ := convArgsT_instPrefix hargsT' _ _ rfl i _ _ _ hxm hxm' hdL
    have hdom : instPrefix ((xs.map (tr R.f R.I)).take i) (instantiateLevels ls d₀) =
        tr R.f R.I (instPrefix (xs.take i) (instantiateLevels ls d₀)) := by
      rw [tr_instPrefix R.hclI, htrd, List.map_take]
    rw [hdom] at cT
    -- back to `E`, at `Γ`
    obtain ⟨hΓt⟩ := R.bkCtxWf hΓ'
    obtain ⟨cE⟩ := R.bkConv cT hΓt
    obtain ⟨cE'⟩ := R.convT_tr_ctx hΓ cE
    -- retyped at the original domain: the round trip of the domain, at its sort
    obtain ⟨cd⟩ := R.trConv_self hdT
    have cE'' : ConvT R.E n Γ (tr R.f R.I x) (tr R.f R.I x')
        (instPrefix (xs.take i) (instantiateLevels ls d₀)) :=
      .tyConv _ _ _ _ _ u cE' (.symm _ _ _ _ cd)
    -- the round trip of the left argument, at the left domain
    have hxE : HasTyT R.E n Γ x (instPrefix (xs.take i) (instantiateLevels ls d₀)) := by
      have := hargsL i x _ hx hd
      simpa only [List.nil_append] using this
    obtain ⟨cx⟩ := R.trConv_self hxE
    -- the round trip of the right argument, at the right domain, moved to the left domain by DT-012
    have hdR : (((piDomsOf m.mtype).map (instantiateLevels ls')).take xs.length)[i]? =
        some (instantiateLevels ls' d₀) := by
      rw [List.getElem?_take, if_pos hi, List.getElem?_map, hd₀]; rfl
    have hx'E : HasTyT R.E n Γ x' (instPrefix (xs'.take i) (instantiateLevels ls' d₀)) := by
      have := hargsR i x' _ hx' hdR
      simpa only [List.nil_append] using this
    obtain ⟨cx'⟩ := R.trConv_self hx'E
    have ends := NativeValleys.convEnds R.hW hΓ cE''
    have ends' := NativeValleys.convEnds R.hW hΓ cx'
    obtain ⟨tc⟩ := DT012T_type_uniqueness_of_sortRow_piRow R.hW R.revSortRow hpi hΓ ends'.2.1 ends.2.1
    obtain ⟨u', hdT'⟩ := ends'.2.2
    obtain ⟨cdd⟩ := F8EtaK.convT_of_tyConvT_sort_of_sortUniq R.hW
      (fun {_Γ' _T _u _v} hΓ' hu hv => R.sortUniq hΓ' hu hv) hΓ hdT' tc
    have cx'' : ConvT R.E n Γ x' (tr R.f R.I x') (instPrefix (xs.take i) (instantiateLevels ls d₀)) :=
      .tyConv _ _ _ _ _ u' cx' cdd
    exact ⟨.trans _ _ _ _ _ cx (.trans _ _ _ _ _ cE'' (.symm _ _ _ _ cx''))⟩
  exact famAppRow_of_piRow_saturation_slotConv hpi R.hW hΓ sat hport hm hind hty h

/-- **THE THREE ROWS of the environment of any revealed singleton.** -/
theorem revTypedRowsWf (n : Nat) : TypedRowsWf R.E n where
  sortRow := fun {_Γ} hΓ {_u _v} h => R.revSortRow hΓ h
  piRow := R.revPiRow n
  famAppRow := fun {_Γ} hΓ {_r _m _ls _ls' _xs _xs' _w} hm hind hty h =>
    R.revFamAppRow hΓ hm hind hty h

end RevEnv

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.piDomsOf_tr
#print axioms Rcic.Syn.FamApp.Rev.tr_instPrefix
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.revFamAppRow
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.revTypedRowsWf
