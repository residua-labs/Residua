import rcic.RcicF3StepAG
import rcic.RcicF3KTWRecPA
import rcic.RcicF3FamKTPropTwin

/-!
# StepAG, the Prop-uniform A-route (`propOnly` groups)

The mirror of `RcicF3StepAG` §3/§4/§4b for uniform-`Prop` groups whose
elimination policy is `propOnly`:

* **§3'** `memberSoundA_prop_of_kt` — the recursor's `MemberSound` from the
  KT line's `recVal_mem_recP_KTA` (the `propOnly` twin of
  `recVal_mem_rec_KTA`), run at the faithful table exactly as the Type
  wiring does; the uniform-`Type` face `hT` is replaced by the
  uniform-`Prop` face `hP` plus the policy equation `hpol`;
* **§4'** `KTPropPrem` / `hpkgA_prop_of_kt` / `stepAG_of_ktProp` — the
  premise structure, the `hpkgA` cell, and the composition, twins of
  `KTTypePrem` / `hpkgA_type_of_kt` / `stepAG_of_ktType`;
* **§4b'** `ktPropPrem_of_famKT` — the table premise PRODUCED from the
  proved Prop twin `famLim_famKT_prop` (`RcicF3FamKTPropTwin`). The Prop
  bridge is strictly lighter than the Type one: no `hf`, no `hN` at the
  bridge level (those stay at the membership row only), and its class
  premise is the class-A form itself, straight from `RecGroupA`
  (`hclsA_of_recGroupA`) — no raw-class bridge needed;
* the apices `stepAG_of_famKT_prop` / `stepAG_of_famKT_prop_lim` (the
  `_lim` twin produces the famfix side too, via the landed `famLim_fix`
  route — Prop-agnostic).

Why a separate module: `RcicF3FamKTPropTwin` imports `RcicF3StepAG` (it
reuses `fieldsClass_of_classA_noFn` and `recApp_of_directRec`), so the
Prop wiring cannot live inside `RcicF3StepAG` without an import cycle.

The uniform-`Prop`∧`anySort` groups (policy `≠ propOnly`) remain outside
both routes (`AGPropAny`, the §5 corner of `RcicF3StepAG`).

`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAG

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup Rcic.F3.StepAObstr

/-! ## §3' membership (the `propOnly` row) -/

/-- **The recursor's `MemberSound` from the KT line — the `Prop`-instance
(`propOnly`) case**: the twin of §3's `memberSoundA_type_of_kt` at
`recVal_mem_recP_KTA`. Everything except the two Prop faces (`hP`
replacing `hT`, plus the policy equation `hpol`) is verbatim the Type
wiring: the faithfulness threading, the constructor premise
(`groupFaith_ctorAt`), the denotation canonicalization. -/
theorem memberSoundA_prop_of_kt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (X : RecStepCtxA P K fm node μ) (G : RecGroupA node.a)
    (hN : ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ f vs) (famKT P μ (famDataOf node.a) vs))
    (hP : ∀ vs, evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : node.a.policy = .propOnly) :
    MemberSound P μ K rr rm := by
  have hcl := (X.facts _ _ X.rmem).1
  have hlvl := (X.facts _ _ X.rmem).2.1
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [X.rbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (X.faith.recur _).symm ?_
  refine recVal_mem_recP_KTA P μ node.a G (ls.map (evalTotal σ)) hN hf ?_
    (groupFaith_ctorAt P X.faith _) (hP _) hpol
  intro vs
  rw [node.fam]
  exact hKT vs

/-! ## §4' the composition: the Prop-uniform A-route to `StepAG` -/

/-- **The per-group premises of the Prop-uniform KT route, gathered** — the
twin of `KTTypePrem`: the uniform-`Type` face `hT` is replaced by the
uniform-`Prop` face `hP` plus the per-node policy equation `hpol`. The
uniform-`Prop`∧`anySort` groups (policy `≠ propOnly`) remain outside both
routes (`AGPropAny`, the §5 corner of `RcicF3StepAG`). -/
structure KTPropPrem (P : Premises4) (K : Nat → Nat) : Prop where
  /-- the group's fields are class-A (the KT line's structure premise) -/
  hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ node : RecNode E E' f rr rm, RecGroupA node.a
  /-- the KT non-IR premise, per group and table -/
  hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
    ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1
  /-- the family ref avoids the two reserved refs -/
  hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ node : RecNode E E' f rr rm,
    (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2
  /-- the uniform-`Prop` face -/
  hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
    evalTotal (σOf vs) node.a.family.resultLevel = 0
  /-- the propOnly policy, per group -/
  hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly
  /-- the table premise: at any faithful-entry table the entry reads `famKT` -/
  hKT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
    (∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) →
    ∀ vs, Equiv (μ f vs) (famKT P μ (famDataOf node.a) vs)
  /-- the ι cell, per group -/
  hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
    IotaAtCell P K E E' f rr rm fm node

/-- **The `hpkgA` cell, proved for uniform-`Prop` `propOnly` A-groups** —
the twin of `hpkgA_type_of_kt`. -/
theorem hpkgA_prop_of_kt (P : Premises4) (K : Nat → Nat) (R : KTPropPrem P K) :
    ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (fm : CheckedMember)
      (Efin : ResolvedEnv) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      RecStepCtxA P K fm node μ → RecPkgAt P μ K Efin E' rr rm := by
  intro E E' f rr rm fm Efin node μ X hsub
  have hLimF : ∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
    have h := X.lim vs
    rw [node.fam] at h
    exact h
  exact ⟨memberSoundA_prop_of_kt P K X (R.hgrp node) (R.hN node μ) (R.hf node)
    (R.hKT node μ hLimF) (R.hP node) (R.hpol node), R.hι node fm μ X Efin hsub⟩

/-- **The Prop-uniform A-route**: the twin of `stepAG_of_ktType` — with
#8239's context-free family-fix cell `hfixA` plus `KTPropPrem`, the whole
`StepAG` field follows for uniform-`Prop` `propOnly` groups. -/
theorem stepAG_of_ktProp (P : Premises4) (K : Nat → Nat) (R : KTPropPrem P K)
    (hfixA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs)
        (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    StepAG P K :=
  stepAG_of_cells P K hfixA (hpkgA_prop_of_kt P K R)

/-! ## §4b' the bridge wiring: `KTPropPrem.hKT` produced from `famLim_famKT_prop` -/

/-- **The bridge wired, Prop side**: `KTPropPrem` with its `hKT` field
PRODUCED from the proved Prop twin `famLim_famKT_prop`
(`RcicF3FamKTPropTwin`). Strictly lighter than the Type wiring
(`ktTypePrem_of_famKT`): the Prop bridge carries no `hf` and no `hN`
(those stay at the membership row only), and its class premise is the
class-A form itself, straight from `RecGroupA` (`hclsA_of_recGroupA`) —
no `fieldsClass_of_classA_noFn` raw-class bridge needed. The Prop-read
premise `hk` is `hP` itself (`famDataOf`'s `resLevel` is
`family.resultLevel` by definition). -/
theorem ktPropPrem_of_famKT (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node) :
    KTPropPrem P K := by
  refine ⟨hgrp, hN, hf, hP, hpol, ?_, hι⟩
  intro E E' f rr rm node μ hLimF vs
  exact (hLimF vs).trans (famLim_famKT_prop (P := P) (μ := μ) (fd := famDataOf node.a)
    node.a.family.member.arity (hgrp node).bounded (hgrp node).famFree
    (hclsA_of_recGroupA (hgrp node))
    (hri_of_recGroupA (hgrp node)) (hres_of_admitted node.a)
    (hnoFn node) vs (hP node vs))

/-! ## the apices -/

/-- **The apex, bridge wired (Prop)**: uniform-`Prop` `propOnly` A-groups'
whole `StepAG` debt with the KT table premise produced from the proved
Prop twin. The named premises are exactly: `hfixA`, `hgrp`, `hN`, `hf`,
`hP`, `hpol`, `hnoFn`, `hι`. -/
theorem stepAG_of_famKT_prop (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node)
    (hfixA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs)
        (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    StepAG P K :=
  stepAG_of_ktProp P K (ktPropPrem_of_famKT P K hgrp hN hf hP hpol hnoFn hι) hfixA

/-- **The apex, famfix from table faithfulness (Prop)**: the `_lim` twin —
`StepAG` with BOTH cells produced for uniform-`Prop` `propOnly` A-groups,
the famfix side from the landed `famLim_fix` route at any faithful table
(`hLimTab`; Prop-agnostic — the same `hfix_of_lim_classA_noFn` as the
Type side). Named premises: `hgrp`, `hN`, `hf`, `hP`, `hpol`, `hnoFn`,
`hι`, `hLimTab`. -/
theorem stepAG_of_famKT_prop_lim (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node)
    (hLimTab : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) :
    StepAG P K :=
  stepAG_of_cells P K
    (fun {E E' f rr rm} node μ vs =>
      hfix_of_lim_classA_noFn P (hgrp node) (hnoFn node) (hLimTab node μ) vs)
    (hpkgA_prop_of_kt P K (ktPropPrem_of_famKT P K hgrp hN hf hP hpol hnoFn hι))

/-! ## the `_nonIR` apices (the §4c discharge on the Prop route) -/

/-- **The `_nonIR` apex (Prop)**: the twin of `stepAG_of_famKT_type_nonIR`
— the per-group `hN` premise derived from the structure's own `NonIR`
predicate (`hN_of_nonIR`, Prop-agnostic), so the named premises drop to
`hfixA`, `hgrp`, `hNI`, `hf`, `hP`, `hpol`, `hnoFn`, `hι`. -/
theorem stepAG_of_famKT_prop_nonIR (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hNI : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.NonIR)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node)
    (hfixA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs)
        (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    StepAG P K :=
  stepAG_of_famKT_prop P K hgrp
    (fun {E E' f rr rm} node μ => hN_of_nonIR P μ node.a (hgrp node) (hnoFn node) (hNI node))
    hf hP hpol hnoFn hι hfixA

/-- **The `_lim_nonIR` apex (Prop)**: the twin of
`stepAG_of_famKT_type_lim_nonIR` — both cells produced (`hKT` from the
bridge, famfix from `hLimTab`) and `hN` from the structure's `NonIR`.
Named premises: `hgrp`, `hNI`, `hf`, `hP`, `hpol`, `hnoFn`, `hι`,
`hLimTab`. -/
theorem stepAG_of_famKT_prop_lim_nonIR (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hNI : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.NonIR)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hP : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel = 0)
    (hpol : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.policy = .propOnly)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node)
    (hLimTab : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) :
    StepAG P K :=
  stepAG_of_famKT_prop_lim P K hgrp
    (fun {E E' f rr rm} node μ => hN_of_nonIR P μ node.a (hgrp node) (hnoFn node) (hNI node))
    hf hP hpol hnoFn hι hLimTab

end Rcic.F3.StepAG
