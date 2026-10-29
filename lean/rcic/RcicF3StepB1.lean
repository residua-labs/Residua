import rcic.RcicF3StepWMin

/-!
# F3 stepB1: the class-B1 field row, discharged (no named premise)

`PartitionSteps.stepB1` (`RcicF3Assembly`) is the B1 antecedent of the
soundness tier: at a `PendB` node (`Prop` family, `anySort` elimination, a
constructor field revealed in the result indices) with no function-recursive
field (`¬ PendA`) and no noncanonical `recursive 0` field (`¬ PendD`), the
`NodeFieldRow` — the fields-direct row and, under `BoundG`, the recursor
package. This module **proves** it; `stepB1` leaves the list of the tier's
named antecedents. `closure_claim = 0`; no theory is narrowed (no class is
restricted — the B1 nodes are proved, not excluded).

## Why no premise is left

On this base the proved class's package `recPkg_classG` (`RcicF3MainG`) takes
`hpf`, the no-reveal clause — exactly `¬ PendB`. The clause is dead weight at
the nodes the tier reaches: `BoundG`'s group clause (B3, `hB.2.2.2 node`)
types every field of a `Prop`/`anySort` constructor at a `UniformProp` level,
so every field is a proof, and at a `Prop` telescope every revealed index is
`∅` whether or not a field is revealed. (cc's `d570b060a7` on #7956 makes the
same observation by editing the landed `iota_group`/`rec_member_sound`/
`recPkg_classG`; this module edits no landed declaration and reaches the same
row by **new** declarations only.)

The ι half does not need a new `iota_group`: the landed one already accepts,
in place of the no-reveal data, the redex-reading agreement `IotaAgree`.
`iotaAgree_of_propTel` produces `IotaAgree` from the `Prop` telescope **at a
redex whose left-hand side is not `∅`** — there the recursor's arguments fit
its domains (`fits_of_fapps_ne`), so the major lies in the family at the
indices `is`, a constructor fits (`famEnd_prop_mem`), each revealed index is
the denotation of a proof field (`idx_pempty_of_ctorFits`), hence the
reconstruction is all `∅` (`recon_pempty`), and the right-hand side's
arguments are proofs too (`spine_proofs`). `iota_at_propB` splits on the
left-hand side: `≈ ∅` closes by `rhs_eq_ed_pempty`, otherwise the landed
`iota_at_gen_pt` runs with the `IotaAgree` disjunct.

The membership half is `rec_member_sound_propB` (the landed
`rec_member_sound` with the no-reveal conjunct dropped, its `hsafe` by
`recon_of_ctorFits_propTel`). `recPkg_classB` is the package without `hpf`:
away from `UniformProp ∧ anySort` it is `recPkg_classG` (its `hpf` vacuous);
at `UniformProp ∧ anySort` it is `rec_member_sound_propB` /
`rec_member_sound_empty` and `iota_at_propB`.

## The helpers

`posOf_some`, `LEq_of_getD`, `recon_getD`, `idx_pempty_of_ctorFits`,
`recon_pempty`, `recon_of_ctorFits_propTel` are glm-f3eq's route-independent
fibre lemmas (`6a915518b5`), byte-for-byte the statements `d570b060a7` adds to
`RcicF3PropIota`. They are kept under the **same names** in the same
namespace, so `dupdecl` flags the pair the moment both trees meet: whichever
of this branch and #7956 lands second deletes its copy (statements
identical).

## The tier

`nodeFieldRow_of_notAD` (the row from `¬ PendA ∧ ¬ PendD` alone — `PendB` is
not even consumed) and its instance `stepB1_proved`.
`PartitionStepsAD` is `PartitionSteps` with both `stepB1` and `stepW`
removed; `partitionStepsABD_of_AD` *builds* the `stepB1` field, and
`tierF3Uncond_of_AD_hyp` / `kernelSoundnessTierUncond_of_AD_hyp` compose
with glm's `StepWMin` wrappers: the tier is conditional on the A and D rows
and `StepWHyp` only.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-! ## §0 fibre lemmas at a `Prop` telescope (glm `6a915518b5` / cc `d570b060a7`) -/

/-- A position found by `posOf` is in range and holds the element. -/
theorem posOf_some {e : Expr Nat} : (l : List (Expr Nat)) → (p : Nat) →
    posOf e l = some p → p < l.length ∧ l[p]? = some e
  | [], _, h => Option.noConfusion h
  | e' :: l, 0, h => by
      simp only [posOf] at h
      split at h
      · rename_i he
        subst he
        exact ⟨Nat.zero_lt_succ _, List.getElem?_cons_zero⟩
      · rw [Option.map_eq_some'] at h
        obtain ⟨q, _, hq⟩ := h
        exact (Nat.succ_ne_zero q hq).elim
  | e' :: l, p + 1, h => by
      simp only [posOf] at h
      split at h
      · exact (Nat.succ_ne_zero p (Option.some.inj h).symm).elim
      · rw [Option.map_eq_some'] at h
        obtain ⟨q, hq, hq1⟩ := h
        have hqp : q = p := Nat.succ.inj hq1
        subst hqp
        obtain ⟨h1, h2⟩ := posOf_some l q hq
        exact ⟨Nat.succ_lt_succ h1, by rw [List.getElem?_cons_succ]; exact h2⟩

/-- Pointwise `≈` of equal-length lists. -/
theorem LEq_of_getD {xs ys : List PSet.{T}} (hl : xs.length = ys.length)
    (h : ∀ k, k < xs.length → Equiv (xs.getD k pempty) (ys.getD k pempty)) : LEq xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => trivial
      | cons y ys => exact (Nat.succ_ne_zero _ hl.symm).elim
  | cons x xs ih =>
      cases ys with
      | nil => exact (Nat.succ_ne_zero _ hl).elim
      | cons y ys =>
          exact ⟨h 0 (Nat.zero_lt_succ _), ih (Nat.succ.inj hl)
            (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))⟩

/-- An element at a position, as a `getD` at an equal position. -/
private theorem getElem_eq_getD {α : Type _} {l : List α} {i j : Nat} (hi : i < l.length) (e : i = j) (d : α) :
    l[i]'hi = l.getD j d := by
  subst e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- The reconstruction of field `k` is the index value at the position the field is revealed at. -/
theorem recon_getD {c : List (Expr Nat) × List (Expr Nat)} {is : List PSet.{T}} {k p : Nat} (hk : k < c.1.length)
    (hp : posOf (.bvar (c.1.length - 1 - k)) c.2 = some p) : (recon c is).getD k pempty = is.getD p pempty := by
  unfold recon
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some', Option.getD_some]
  unfold reconField
  rw [hp]

/-- **The revealed index is a proof.** `CtorFits`'s index agreement at `p` reads
`is[p] ≈ xs[k]` (the field revealed at `p` is `bvar (len-1-k)`, denoted by `xs[k]` under
`push xs ρp`); `propTel_fits` gives `xs[k] ≈ ∅` — so `is[p] ≈ ∅`. -/
theorem idx_pempty_of_ctorFits {M : Interp.{T}} {σ : Nat → Nat}
    {c : List (Expr Nat) × List (Expr Nat)} {ρp : Nat → PSet.{T}} {is xs : List PSet.{T}}
    (hcf : CtorFits M σ [c] ρp is 0 xs) (hPT : PropTel M σ c.1 ρp)
    {k p : Nat} (hk : k < c.1.length)
    (hp : posOf (.bvar (c.1.length - 1 - k)) c.2 = some p) :
    Equiv (is.getD p pempty) pempty := by
  obtain ⟨c', hc', htel, hri⟩ := hcf
  rw [List.getElem?_cons_zero, Option.some.injEq] at hc'
  subst hc'
  have hnf : xs.length = c.1.length := htel.length
  have hx0 := propTel_fits M σ _ _ _ hPT htel
  have hxk : Equiv (xs.getD k pempty) pempty := by
    have e := LEq_getD hx0 k
    have hkd : (xs.map fun _ => pempty).getD k pempty = pempty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (hnf ▸ hk : k < xs.length)]
      rfl
    rw [hkd] at e
    exact e
  obtain ⟨_, hld⟩ := posOf_some c.2 p hp
  have hd : den M σ (push xs ρp) (.bvar (c.1.length - 1 - k)) = xs.getD k pempty := by
    show push xs ρp (c.1.length - 1 - k) = xs.getD k pempty
    have hlt : c.1.length - 1 - k < xs.length := by
      rw [hnf]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.zero_lt_of_lt hk) (by decide))
    have hjk : xs.length - 1 - (c.1.length - 1 - k) = k := by
      rw [hnf]; exact Nat.sub_sub_self (Nat.le_pred_of_lt hk)
    rw [push_lt xs ρp _ hlt]
    exact getElem_eq_getD _ hjk _
  have hmap : (c.2.map (den M σ (push xs ρp))).getD p pempty =
      den M σ (push xs ρp) (.bvar (c.1.length - 1 - k)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hld]
    rfl
  have e1 := LEq_getD hri p
  rw [hmap, hd] at e1
  exact e1.symm.trans hxk

/-- **The reconstruction is all proofs.** If every revealed field's index is `≈ ∅`,
each reconstructed field is `≈ ∅` — `recon c is ≈ c.1.map (fun _ => ∅)`, component-wise via
`recon_getD`. -/
theorem recon_pempty (c : List (Expr Nat) × List (Expr Nat)) (is : List PSet.{T})
    (h : ∀ k p, k < c.1.length → posOf (.bvar (c.1.length - 1 - k)) c.2 = some p →
      Equiv (is.getD p pempty) pempty) :
    LEq (recon c is) (c.1.map fun _ => pempty) := by
  have hlen : (recon c is).length = (c.1.map fun _ => pempty).length := by
    rw [recon, List.length_map, List.length_map, List.length_range]
  refine LEq_of_getD hlen ?_
  intro k hk
  have hkn : k < c.1.length := by
    have h' := hk
    rwa [recon, List.length_map, List.length_range] at h'
  have hrhs : (c.1.map fun _ => pempty).getD k pempty = pempty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkn]
    rfl
  rw [hrhs]
  cases hp : posOf (.bvar (c.1.length - 1 - k)) c.2 with
  | none =>
      rw [show (recon c is).getD k pempty = pempty from by
        unfold recon
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkn,
          Option.map_some', Option.getD_some]
        unfold reconField
        rw [hp]]
      exact Equiv.rfl
  | some p => rw [recon_getD hkn hp]; exact h k p hkn hp

/-- **The mixed `hsafe`.** At a `Prop` telescope every fitting field is `≈ ∅`
(`propTel_fits`), and every reconstructed field is `≈ ∅` (`recon_pempty` of
`idx_pempty_of_ctorFits`) — so the fitting fields and the reconstruction agree,
`LEq xs (recon c is)`. -/
theorem recon_of_ctorFits_propTel {M : Interp.{T}} {σ : Nat → Nat}
    {c : List (Expr Nat) × List (Expr Nat)} {ρp : Nat → PSet.{T}} {is xs : List PSet.{T}}
    (hcf : CtorFits M σ [c] ρp is 0 xs) (hPT : PropTel M σ c.1 ρp) :
    LEq xs (recon c is) := by
  obtain ⟨c', hc', htel, hri⟩ := hcf
  rw [List.getElem?_cons_zero, Option.some.injEq] at hc'
  subst hc'
  have hlen : xs.length = c.1.length := htel.length
  have hxE : LEq xs (c.1.map fun _ => pempty) := by
    have hx := propTel_fits M σ _ _ _ hPT htel
    have hmap : xs.map (fun _ => pempty) = c.1.map fun _ => pempty := by
      apply List.ext_getElem
      · rw [List.length_map, List.length_map]; exact hlen
      · intro i _ _; rw [List.getElem_map, List.getElem_map]
    rwa [hmap] at hx
  have hre : LEq (recon c is) (c.1.map fun _ => pempty) :=
    recon_pempty c is fun k p hk hp =>
      idx_pempty_of_ctorFits ⟨c, rfl, htel, hri⟩ hPT hk hp
  exact LEq.trans hxE hre.symm

/-! ## §1 ι: `IotaAgree` from the `Prop` telescope at a nonempty redex -/

/-- **`IotaAgree` at a `Prop` telescope, revealed fields allowed.** At a witness of
the recursor admitted by `a` (constructor `j`), under `Prop` large elimination,
with family-free fields, the minor's type over the lifted fields, and the fields
a telescope of propositions — and at a redex whose left-hand side is **not `∅`** —
the landed `IotaAgree` holds. No index-agreement premise: the major lies in the
family (the recursor's arguments fit its domains), so a constructor fits and
every revealed index is the value of a proof field, i.e. `∅`; the right-hand
side's arguments are proofs by `spine_proofs`. -/
theorem iotaAgree_of_propTel {M : Interp.{T}} (W : Nat → PSet.{T}) {E E0 : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E0 r m) (w : IotaWitness E) (hrec : w.recRef = r)
    (hm : w.recMember = m) (σ : Nat → Nat) (ρ : Nat → PSet.{T})
    (hrecμ : Equiv (M.μ r (w.ls.map (evalTotal σ)))
      (piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd M (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
        (fun _ => pempty) m.mtype))
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf (w.ls.map (evalTotal σ))))))
      (piLam M (σOf (w.ls.map (evalTotal σ))) (famEnd M W (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
        (fun _ => pempty) (famType (famDataOf a))))
    (j : Fin a.constructors.length) (hj : w.ctorIdx = j.val) (hcm : w.ctorMember = a.constructors[j.val])
    (h0 : evalTotal (σOf (w.ls.map (evalTotal σ))) a.family.resultLevel = 0)
    (hfree : ∀ T, T ∈ (a.constructorViews j).fields → occursConst a.family.ref T = false)
    (hmt : ∃ b, a.minorTypes[j.val]? = some (policyPi (liftFields (1 + j.val) (a.constructorViews j).fields 0) b))
    (hprop : ∀ ps, TelFits M (σOf (w.ls.map (evalTotal σ))) a.family.parameters (fun _ => pempty) ps →
      PropTel M (σOf (w.ls.map (evalTotal σ))) (a.constructorViews j).fields (push ps (fun _ => pempty)))
    (hspine : SpineFacts M (den M σ ρ w.minor) ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      w.fields w.kinds w.ctorAfterParams).map (den M σ ρ)))
    (hne : ¬ Equiv (den M σ ρ (iotaLhsOf w)) pempty) :
    IotaAgree M σ ρ a w j := by
  intro ps mo ms is hsplit hpsl hmsl hisl hpre c hfd
  obtain ⟨hnp, hnM, hnq, hfr⟩ := iota_align a w hrec hm
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hjk : j.val < a.constructors.length := j.isLt
  -- the left-hand side as an application of the recursor's value; its arguments fit
  have hlhs : den M σ ρ (iotaLhsOf w) =
      fapps (M.μ r (w.ls.map (evalTotal σ))) (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) := by
    unfold iotaLhsOf recCall
    rw [fapps_den_append_singleton, hrec]
    rfl
  have hpvl : (w.preMajor.map (den M σ ρ)).length =
      a.family.parameters.length + 1 + a.constructors.length + a.family.indices.length := by
    rw [List.length_map, w.hpre, hnp, hnM, hnq]
  rw [recType_eq a] at hrecμ
  have hne' : ¬ Equiv (fapps (piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd M (σOf (w.ls.map (evalTotal σ)))
      (famDataOf a)) (fun _ => pempty) (policyPi (recPreDomsOf a ++ [recMajorOf a]) (recResultOf a)))
      (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)])) pempty := fun h =>
    hne (by rw [hlhs]; exact (fapps_congr hrecμ _).trans h)
  have hlenD : (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]).length =
      (recPreDomsOf a ++ [recMajorOf a]).length := by
    rw [List.length_append, List.length_append, hpvl, recPreDomsOf_length]; rfl
  have hfit := fits_of_fapps_ne M (σOf (w.ls.map (evalTotal σ)))
    (recEnd_resp M (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
    (recResultOf a) (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty) _ hlenD hne'
  obtain ⟨xs0, ys0, hxy, hf1, hf2⟩ := TelFits_split _ _ _ _ hfit
  have hx0 : xs0 = w.preMajor.map (den M σ ρ) := by
    have h1 := hf1.length
    have := List.append_inj hxy.symm (by rw [h1, hpvl, recPreDomsOf_length])
    exact this.1
  subst hx0
  have hy0 : ys0 = [den M σ ρ (ctorMajor w)] := (List.append_cancel_left hxy).symm
  subst hy0
  -- the major premise lies in the family at the indices `is`
  have hmaj : den M σ ρ (ctorMajor w) ∈ Ed M (den M (σOf (w.ls.map (evalTotal σ)))
      (push (w.preMajor.map (den M σ ρ)) (fun _ => pempty)) (recMajorOf a)) := hf2.1
  rw [hsplit, den_recMajor M _ a ps mo ms is _ hpsl (by rw [hmsl, hk]) hisl] at hmaj
  have hfdl : (famDataOf a).ctors.length = a.constructors.length := famDataOf_ctors_length a
  have hk1 : a.constructors.length = 1 := by rw [← hfdl, hfd]; rfl
  have hj0 : j.val = 0 := by omega
  have hc : c = ((a.constructorViews j).fields, (a.constructorViews j).resultIndices) := by
    have h2 := famDataOf_ctor a j
    rw [hfd] at h2
    simp only [hj0, List.getElem?_cons_zero, Option.some.injEq] at h2
    exact h2
  obtain ⟨j', xs', hcfj⟩ := (famEnd_prop_mem W _ (famDataOf a) ps is (by simpa [famDataOf] using hisl) h0
    (fam_app_fits W _ (famDataOf a) hfamμ ps is (by simp [famDataOf, hpsl, hisl]) hmaj).2).1
  rw [hfd] at hcfj
  obtain ⟨c', hc', htel', hri'⟩ := hcfj
  have hj'0 : j' = 0 := by
    cases j' with
    | zero => rfl
    | succ j'' =>
        rw [show [c][j'' + 1]? = none from List.getElem?_eq_none (Nat.succ_le_succ (Nat.zero_le _))] at hc'
        exact Option.noConfusion hc'
  subst hj'0
  -- the selected minor
  have hmin : ms.getD j.val pempty = den M σ ρ w.minor := by
    have hm1 := w.hminor
    rw [hnp, hj] at hm1
    have hm2 : (w.preMajor.map (den M σ ρ))[a.family.parameters.length + 1 + j.val]? =
        some (den M σ ρ w.minor) := by
      rw [List.getElem?_map, hm1]; rfl
    rw [hsplit, List.getElem?_append_right (by omega),
      show a.family.parameters.length + 1 + j.val - ps.length = j.val + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_append_left (by omega)] at hm2
    rw [List.getD_eq_getElem?_getD, hm2]
    rfl
  -- the constructor's stored type and the plain kinds
  have hst := (a.constructorViews j).storedType
  have hcpl := (a.constructorViews j).parameterCount
  have hctm : w.ctorMember.mtype = policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
          (a.constructorViews j).resultIndices)) := by rw [hcm]; exact hst
  have hfl : w.fields.length = (a.constructorViews j).fields.length := witness_fields_length a w hrec hm j hcm
  have hpeel := w.hpeel
  rw [hctm, show w.nparams + w.fields.length = ((a.constructorViews j).parameters ++
    (a.constructorViews j).fields).length by rw [List.length_append]; omega, peelPis_policyPi] at hpeel
  have hdoms : w.ctorDoms = (a.constructorViews j).parameters ++ (a.constructorViews j).fields :=
    (congrArg Prod.fst (Option.some.inj hpeel)).symm
  have hkinds := w.hkinds
  rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
  have hplain : w.kinds = (a.constructorViews j).fields.map fun _ => RecKind.plain := by
    have := analyzeFields_plain a.family.ref _ hfree
    rw [hkinds] at this
    exact Option.some.inj this
  have hrw : rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors w.fields w.kinds
      w.ctorAfterParams = w.fields :=
    rhsArgs_plain _ _ _ _ _ _ (fun k hk => by
      rw [hplain] at hk; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hk; rfl) _
  rw [hrw] at hspine
  -- the minor lies in its type, a telescope of propositions
  have hf1' := hpre
  rw [hsplit] at hf1'
  unfold recPreDomsOf at hf1'
  obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hf1'
  have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl])).1
  subst hxa
  have hxb : xb = mo :: (ms ++ is) := (List.append_cancel_left hxab).symm
  subst hxb
  obtain ⟨ya, yb, hyab, hya, _⟩ := TelFits_split _ _ _ _ hfb.2
  have hya' : ya = ms := (List.append_inj hyab.symm (by rw [hya.length, hmsl, hk])).1
  subst hya'
  obtain ⟨b, hmtb⟩ := hmt
  have hmt0 : a.minorTypes[0]'(by rw [hk, hk1]; exact Nat.zero_lt_one) =
      policyPi (liftFields 1 (a.constructorViews j).fields 0) b := by
    have e1 : a.minorTypes[j.val]? = a.minorTypes[0]? := by rw [hj0]
    have h1 := e1.symm.trans hmtb
    have e2 : 1 + j.val = 1 := by omega
    rw [e2] at h1
    exact (List.getElem?_eq_some_iff.mp h1).2
  have hg := TelFits_get a.minorTypes _ ya hya 0 (by rw [hk, hk1]; exact Nat.zero_lt_one)
  rw [hmt0] at hg
  have hPTj := hprop xa hfa
  have hPT := propTel_liftFields M (σOf (w.ls.map (evalTotal σ))) [mo] (push xa (fun _ => pempty))
    (a.constructorViews j).fields [] hPTj
  rw [hj0] at hmin
  rw [hmin] at hg
  have hlen : (w.fields.map (den M σ ρ)).length = (liftFields 1 (a.constructorViews j).fields 0).length := by
    rw [List.length_map, liftFields_length', hfl]
  have hsp := spine_proofs M (σOf (w.ls.map (evalTotal σ))) b _ _ _ _ hlen hg hPT hspine
  -- the reconstruction from the indices is all proofs
  subst hc
  have hrecon : LEq (recon ((a.constructorViews j).fields, (a.constructorViews j).resultIndices) is)
      ((a.constructorViews j).fields.map fun _ => pempty) :=
    recon_pempty _ is fun k p hk hp => idx_pempty_of_ctorFits ⟨_, hc', htel', hri'⟩ hPTj hk hp
  have e : (a.constructorViews j).fields.map (fun _ => pempty) =
      (w.fields.map (den M σ ρ)).map fun _ => pempty := by
    simp only [List.map_const', List.map_map, Function.comp_def, List.length_map, hfl]
  rw [e] at hrecon
  exact (fapps_congr_args _ hrecon).trans hsp.symm

/-- **ι at a group's recursor without the no-reveal clause** (the landed `iota_at`'s
condition minus its `posOf … = none` conjunct). At a redex whose left-hand side
is `≈ ∅` the two sides agree by `rhs_eq_ed_pempty`; otherwise the landed
`iota_at_gen_pt` runs with the `IotaAgree` disjunct, produced by
`iotaAgree_of_propTel`. -/
theorem iota_at_propB (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' Efin : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) (hrm : E'.members rr = some rm)
    (hrf : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
        ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
  cases (mkM P μ).dec (Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) with
  | isTrue h0 => exact rhs_eq_ed_pempty ml mr h0
  | isFalse hne =>
  exact iota_at_gen_pt P hG hsubF hrm hrf hlvC hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
    (fun hU hpol i hj hm hcm _ => (hpf hU hpol i).imp (fun ⟨h1, h2, h3⟩ => ⟨h1, Or.inr
      (iotaAgree_of_propTel W4 node.a w hwr hm σ ρ (hG.recur _) (groupFaith_famAt P hG _) i hj hcm (hU _)
        h1 h2 (h3 _ fun v hv => by
          obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
          exact hls l hl')
        (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) hne)⟩) id)

/-! ## §2 the recursor's membership and package without the no-reveal clause -/

/-- A recursor member is sound (the landed `rec_member_sound` with the no-reveal
conjunct dropped: its `hsafe` is `recon_of_ctorFits_propTel`). -/
theorem rec_member_sound_propB (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E E' : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm}
    (hG : GroupFaith P μ fm node)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 rm.mtype = rm.mtype)
    (hlvl : exprLevelsBounded rm.arity rm.mtype = true) (hbody : rm.body = none)
    (hnr : ∀ i fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref node.a.family.member.arity
        node.a.family.parameters.length node.a.family.indices.length node.a.family.parameters.length
        (node.a.constructorViews i).fields = some shapes → ∀ s, s ∈ shapes → s = .nonrecursive)
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0))
    (hfree : ∀ (i : Fin node.a.constructors.length) T, T ∈ (node.a.constructorViews i).fields →
      occursConst node.a.family.ref T = false) :
    MemberSound P μ K rr rm := by
  intro σ ls ρ hlen hls
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hG.recur _).symm ?_
  refine recVal_mem rfl node.a (ls.map (evalTotal σ)) ?_ (groupFaith_famAt P hG _) (groupFaith_ctorAt P hG _) ?_ hfree
  · intro i
    obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
    exact ⟨fuel, shapes, hnr i fuel shapes hfs,
      fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs, hdm⟩
  · intro h0 hpol c hc ps is xs hps hcf
    obtain ⟨hup, hk⟩ := selection_prop node.a _ h0 hpol
    obtain ⟨c', hc', hxs, hri⟩ := hcf
    rw [hc] at hc'
    simp at hc'
    subst hc'
    have hk1 : node.a.constructors.length = 1 := by
      have := famDataOf_ctors_length node.a
      rw [hc] at this
      simpa using this.symm
    have hc0 := famDataOf_ctor node.a ⟨0, by omega⟩
    rw [hc] at hc0
    simp at hc0
    have hprop := hpf hup hpol ⟨0, by omega⟩ _ (fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      exact hls l hl) ps hps
    rw [hc0] at hxs hri ⊢
    exact recon_of_ctorFits_propTel ⟨_, rfl, hxs, hri⟩ hprop

/-- **The recursor's package without the no-reveal clause.** As the landed
`recPkg_classG`, from `BoundG`'s B3 clause and the step context alone: away from
`UniformProp ∧ anySort` it *is* `recPkg_classG` (whose `hpf` is then vacuous); at
`UniformProp ∧ anySort` the membership is `rec_member_sound_propB` (family-free
fields) or `rec_member_sound_empty` (a family-mentioning field: the family is
empty), and ι is `iota_at_propB`. A field revealed in the result indices is
allowed throughout. -/
theorem recPkg_classB (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    (node : RecNode E E' f rr rm) {μ : Nat → List Nat → PSet.{4}}
    (hB3 : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) (vs : List Nat), (∀ v, v ∈ vs → v ≤ K rr) →
      ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level, UniformProp l ∧
        ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
          (policyPrefixContext (node.a.family.parameters ++ (node.a.constructorViews i).fields)
            (node.a.family.parameters.length + k.val))
          ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d)
    (X : RecStepCtx P K fm node μ) : RecPkg P μ K E' rr rm := by
  cases P.dec (UniformProp node.a.family.resultLevel ∧ node.a.policy = .anySort) with
  | isFalse hn => exact recPkg_classG P K node (fun hU hpol => absurd ⟨hU, hpol⟩ hn) hB3 X
  | isTrue hUP =>
  obtain ⟨hU, hpol⟩ := hUP
  obtain ⟨hG, hLimμ, hES_S, hTF, hpfF, hclsF, hr', hrb, hrfR, hlvC, hsh⟩ := X
  have hnrec : ∀ (i : Fin node.a.constructors.length),
      (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) →
      ∀ fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref
        node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
        node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
        ∀ s, s ∈ shapes → s = .nonrecursive := by
    intro i hnf fuel shapes hfs
    rw [node.fam] at hfs
    exact nonrec_of_shapesMatch (hsh i fuel shapes hfs) hnf
  have hPT : ∀ (i : Fin node.a.constructors.length) vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps,
      TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
      PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0) := by
    intro i vs hvs ps hps
    refine propTel_of_typings P μ K vs _ _ (hES_S (σOf vs) node.a.family.member.arity) (fun k => ?_) ps hps
    obtain ⟨l, hl, hd⟩ := hB3 hU hpol i vs hvs k
    exact ⟨l, hl _, hd⟩
  have hone : node.a.constructors.length ≤ 1 := (selection_prop node.a (fun _ => 0) (hU _) hpol).2
  have hnfOf : ∀ i : Fin node.a.constructors.length,
      ¬ (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) →
      ∀ c, c ∈ (famDataOf node.a).ctors → ¬ ∀ A, A ∈ c.1 → occursConst (famDataOf node.a).fref A = false := by
    intro i hni c hc hall
    have hc' : c ∈ ofFin node.a.constructors.length
        (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
    obtain ⟨i', rfl⟩ := mem_ofFin _ _ hc'
    have e : i' = i := Fin.ext (by have := i.isLt; have := i'.isLt; omega)
    subst e
    have hfr : (famDataOf node.a).fref = f := node.fam
    rw [hfr] at hall
    exact hni hall
  have hEmpty : (∀ c, c ∈ (famDataOf node.a).ctors → ¬ ∀ A, A ∈ c.1 → occursConst (famDataOf node.a).fref A = false) →
      ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a) := fun hnf vs =>
    propEmpty_of_lim P μ (famDataOf node.a) node.a.family.member.arity (famBounded_node node hTF) hpfF hclsF
      (σOf vs) (hU _) hnf (fun r ls => (tabLim_equiv P μ node.a hLimμ r ls).symm)
  have hIrr : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr :=
    fun Efin hsubF => iota_at_propB P hG hsubF hr' hrfR hlvC (fun _ _ i => by
      refine @Decidable.byCases (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) _ inferInstance
        (fun hfree => ?_) (fun hni => Or.inr (hEmpty (hnfOf i hni)))
      obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
      have hmt := derivedMinor_nonrec node.a i fuel shapes (hnrec i hfree fuel shapes hfs)
        (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
      rw [hdm] at hmt
      exact Or.inl ⟨fun T hT => by rw [node.fam]; exact hfree T hT, ⟨_, hmt⟩, hPT i⟩)
  have hcl := (hTF _ _ hr').1
  have hlvl := (hTF _ _ hr').2.1
  have hrmS : MemberSound P μ K rr rm := by
    refine @Decidable.byCases (∀ (i : Fin node.a.constructors.length) T, T ∈ (node.a.constructorViews i).fields →
      occursConst f T = false) _ inferInstance (fun hfree => ?_) (fun hni => ?_)
    · exact rec_member_sound_propB P hG hcl hlvl hrb (fun i => hnrec i (hfree i))
        (fun _ _ i => hPT i) (fun i T hT => by rw [node.fam]; exact hfree i T hT)
    · refine rec_member_sound_empty P hG hcl hlvl hrb hU (hEmpty fun c hc hall => ?_)
      have hc' : c ∈ ofFin node.a.constructors.length
          (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
      obtain ⟨i', rfl⟩ := mem_ofFin _ _ hc'
      have hfr : (famDataOf node.a).fref = f := node.fam
      rw [hfr] at hall
      refine hni fun i => ?_
      have e : i = i' := Fin.ext (by have := i.isLt; have := i'.isLt; omega)
      subst e
      exact hall
  exact ⟨hrmS, hIrr⟩

end PSet

/-! ## §3 the stepB1 field, proved; the tier without it -/

namespace StepB1

open Rcic.F3.PSet
open Rcic.F3.StepWMin

/-- **The field row from `¬ PendA ∧ ¬ PendD` alone.** The fields-direct row is the
exported `recFieldsDirect_of_notAD`; the package, under `BoundG`, is
`recPkg_classB` at `BoundG`'s B3 clause for the node. Whether a field is revealed
(`PendB`) is never consulted. -/
theorem nodeFieldRow_of_notAD (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hA : ¬ PendA node) (hD : ¬ PendD node) :
    NodeFieldRow P K hE hfam hctors hrec hmem node :=
  ⟨recFieldsDirect_of_notAD P node hA hD, fun hB _ X => recPkg_classB P K node (hB.2.2.2 node) X⟩

/-- **`PartitionSteps.stepB1`, proved** — exactly the field's type. -/
theorem stepB1_proved (P : Premises4) (K : Nat → Nat) :
    ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendB node → ¬ PendA node → ¬ PendD node →
      NodeFieldRow P K hE hfam hctors hrec hmem node :=
  fun hE hfam hctors hrec hmem node _ hA hD => nodeFieldRow_of_notAD P K hE hfam hctors hrec hmem node hA hD

/-- **The tier's remaining field-class antecedents**: `PartitionSteps` with the
`stepB1` field (proved here) and the `stepW` field (`StepWHyp`, glm's
`StepWMin`) removed. -/
structure PartitionStepsAD (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: function-recursive fields (`recursive (m+1)`); the KT lane. -/
  stepA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **D**: noncanonical `recursive 0` fields (reached through δ/β). -/
  stepD : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendD node → ¬ PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node

/-- The A/D projection of the A/B1/D record (the bridge for a caller holding it). -/
theorem partitionStepsAD_of_ABD {P : Premises4} {K : Nat → Nat} (abd : PartitionStepsABD P K) :
    PartitionStepsAD P K where
  stepA := abd.stepA
  stepD := abd.stepD

/-- **The `stepB1` field is constructed, not taken**: the A/B1/D record from the
A and D rows, with `stepB1` built by `stepB1_proved`. -/
theorem partitionStepsABD_of_AD {P : Premises4} {K : Nat → Nat} (ad : PartitionStepsAD P K) :
    PartitionStepsABD P K where
  stepA := ad.stepA
  stepB1 := stepB1_proved P K
  stepD := ad.stepD

/-- The full steps record from the A and D rows and `StepWHyp`: both `stepB1`
and `stepW` are built. -/
theorem partitionSteps_of_AD_hyp (P : Premises4) (K : Nat → Nat) (h : StepWHyp)
    (ad : PartitionStepsAD P K) : PartitionSteps P K :=
  partitionSteps_of_hyp P K h (partitionStepsABD_of_AD ad)

/-- **The conditional tier with no B1 debt**: the height-4 consistency tier holds
under the A and D rows and `StepWHyp` alone. -/
theorem tierF3Uncond_of_AD_hyp (h : StepWHyp) (ad : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsAD P K) :
    Rcic.Apex.TierF3Uncond :=
  tierF3Uncond_of_hyp h fun P K => partitionStepsABD_of_AD (ad P K)

/-- The full unconditional kernel tier (F1 closed, F3 modulo the A/D rows and
`StepWHyp`). -/
theorem kernelSoundnessTierUncond_of_AD_hyp (h : StepWHyp)
    (ad : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsAD P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  kernelSoundnessTierUncond_of_hyp h fun P K => partitionStepsABD_of_AD (ad P K)

end StepB1

end Rcic.F3
