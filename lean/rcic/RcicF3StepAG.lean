import rcic.RcicF3TierGroup
import rcic.RcicF3KTWRecA
import rcic.RcicF3KTWNonIR
import rcic.RcicF3StepAObstr
import rcic.RcicF3FamKTBridge
import rcic.RcicAnnIotaCorr

/-!
# F3 `StepAG`: the producer line — bridge, membership, package, corners

`closure_claim = 0`.

cc's StepAG item (10-27 08:10Z): produce `StepAG P K` — the A-class
group-granular field of `PartitionStepsG` (#8237), the RCC frontier's
`premise_no_producer` node.

**This module consumes `Rcic.F3.StepAObstr` (#8239, signed off)** for the
class-agnostic group-step assembly: `RecStepCtxA`, `gInv_group_ofAt_A`,
`stepAAt_of_A` and the cell packaging `stepAG_of_cells` live THERE and are
not duplicated here. What this module adds is everything on the producer
side of those two cells:

* the **generic KT bridge** (`FamKTBridgeA`, §1) — `famLim ≈ famKT` at any
  `FamData`, the union-of-iterates limit vs the KT lane's fibre-set least
  fixed point — plus its reduction of the family-fix obligation to the
  landed `famKT_fix` (`agfix_of_famKTBridgeA`, proved; `agfixA_of_...` the
  per-group form via the landed admission bridges);
* the **ι cell** (`IotaAtCell`, §2) at the #8239 interface — with #8239's
  `iota_at_of_witDirect` already discharging it per witness under the
  decidable `CtorWitOK`, and `iotaAt_wEnv_vacuous` discharging it outright
  at the `wEnv` fixture; §2's `iotaAtCell_of_witDirect` is the
  μ/Efin-general PRODUCER (ctx supplies `faith`/`rmem`/`lvC`, the group
  supplies `opq`; new inputs: `FamFreeBodies`, `WitDirect`/`CtorWitOK`,
  the per-witness side condition `hpf`);
* the **recursor package cell PROVED for uniform-`Type` A-groups**
  (§3): `memberSoundA_type_of_kt` (from the KT lane's `recVal_mem_rec_KTA`
  at the faithful table), `recPkgA_of_ms_iota`, and `hpkgA_type_of_kt` —
  #8239's `hpkgA` cell in full, from the table premise + `hN` + `hT` + the
  ι cell;
* the **composition** (§4): `stepAG_of_ktType` — for uniform-`Type`
  A-groups the whole `StepAG` debt reduces to #8239's context-free `hfixA`
  cell (the named famfix residue) plus per-group `hN`/`hT`/structure
  premises and the ι cell; everything else is proved here or in #8239;
* the **bridge wiring** (§4b): `ktTypePrem_of_famKT` — `KTTypePrem`'s
  `hKT` table premise is no longer open on the `Type` route: it is produced
  from the proved bridge `famLim_famKT_type` (`RcicF3FamKTBridge` §6),
  whose raw-`FieldsClass` premise comes from `RecGroupA` under the bridge's
  own `hnoFn` (`fieldsClass_of_classA_noFn`: the `FnRec` arm is exactly the
  `.fn`-kinded arm, `kindOf_fnRec`), and whose Type-read premise `hk` is
  `hT` itself (`famDataOf`'s `resLevel` is `family.resultLevel` by
  definition). `stepAG_of_famKT_type` is the resulting apex — the named
  premises are exactly `hfixA`, `hgrp`, `hN`, `hf`, `hT`, `hnoFn`, `hι`;
  and `hfix_of_lim_classA_noFn` + `stepAG_of_famKT_type_lim` go one step
  further, producing the famfix side too at any faithful table (the
  landed `famLim_fix` route — no KT bridge needed there at all).
* the **`hN` discharge** (§4c): the per-group `hN` premise — #8055's named
  residue — is PRODUCED two ways: from the structure's own `NonIR`
  predicate (`hN_of_nonIR` + `stepAG_of_famKT_type_nonIR`/
  `…_lim_nonIR`), and from the environment at a scoped node (`hN_of_env` +
  the `_scoped` apices) via #8067's `admitted_group_nonIR_scoped` — NO
  full `RecGroup` needed (§4b's `RecGroupA` → raw-class bridge suffices;
  `ShapesMatch` never enters the hN route);
* the **named corners** (§5): `AGPropAny` (uniform-`Prop`/`anySort`) and
  `AGMixedAD` (the A∧D mixed fields #8234 called "the A lane's debt").

## Interface note (why `hfixA` stays a premise)

#8239's `hfixA` cell is context-free (`∀ node μ vs`, any table), while the
bridge→fix reduction is **faithfulness-conditioned**: `agfix_of_famKTBridgeA`
routes through `famKT_fix` at the `tabKT` table and transfers back via
`famVal_tables`, which needs the table's family entry to read `famKT` —
exactly the shape `RecStepCtxA.lim` supplies inside the assembly. So the
composition (§4) keeps `hfixA` itself as the one named premise it is.
§4b then produces the faithful-table instance WITHOUT the KT bridge at
all (`hfix_of_lim_classA_noFn`: the landed `famLim_fix` + `tabLim_equiv`
route — no `hN`/`hf`/`hres`, no full-`vs` bridge, no Prop twin), and
`stepAG_of_famKT_type_lim` reduces the context-free `hfixA` premise to
`hLimTab` — `RecStepCtxA.lim`'s own shape lifted to the tier level (the
landed direct row derives it from `FaithfulR` at every group). §4c and
§4d then discharge two more of those named premises: `hN` from the
structure's own `NonIR` (or #8067's scoped env route at a member-carrying
env), and `hLimTab` from `FaithfulR` itself — the tier's own table
premise. What remains named on the Type route: `hgrp`, `hNI`, `hf`,
`hT`, `hnoFn`, the ι inputs (`FamFreeBodies`/`WitDirect`/`hpf`), and
the Prop twin + the §5 corners.
Axioms of every sealed declaration ⊆ {`propext`, `Quot.sound`}; all case
splits on `Premises4.dec`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAG

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup Rcic.F3.StepAObstr
open Rcic.Model.PS (denRefs denRefsLit hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

/-! ## §1 the generic KT bridge (named residue) and the family-fix reduction -/

/-- **The generic KT bridge** (named residue `[rcic-f3-steag-famkt-bridge]`):
the union-of-iterates family limit `famLim` agrees with the KT lane's least
fixed point `famKT` for `FieldsClassA` families. Two constructions of the
same operator's least fixed point — one iterating in function space, one
iterating the fibre sets (`DStar`). The family-fix obligation of every
A-class group reduces to exactly this (`agfix_of_famKTBridgeA`), and it is
the bridge that turns the KT lane's `famKT_fix` (a theorem at the `tabKT`
table) into a statement at a faithful table.

Name: the `A` suffix marks the GENERIC form (any `μ`, any `FamData`);
`StepAObstr.FamKTBridge` is the `wEnv`-fixture instance of this statement
(`famDataOf wGroupAdmitted`), and stays the W-local residue name.

**Type arm proved**: `famLim_famKT_type` (`RcicF3FamKTBridge` §6) proves
this cell at every Type-read (under `hnoFn`); §4b wires it into
`KTTypePrem.hKT` (`ktTypePrem_of_famKT`). The full-`vs` cell above stays
named for the Prop-read half — residue
`[rcic-f3-famkt-bridge-prop-twin]`. -/

def FamKTBridgeA (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) : Prop :=
  ∀ vs, Equiv (famLim P μ fd vs) (famKT P μ fd vs)

/-- The `tabKT` table agrees with the table it updates — the `tabKT` twin of
the landed `tabLim_equiv`: given that the family's entry is the `famKT` value
(which faithfulness plus the bridge supply), the two tables are pointwise
`≈`. -/
theorem tabKT_equiv {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {fd : FamData}
    (hKT : ∀ vs, Equiv (μ fd.fref vs) (famKT P μ fd vs)) :
    ∀ r ls, Equiv (tabKT P μ fd r ls) (μ r ls) := by
  intro r ls
  by_cases hr : r = fd.fref
  · subst hr
    show Equiv (upd μ fd.fref (famKT P μ fd) fd.fref ls) _
    rw [upd_eq]
    exact (hKT ls).symm
  · show Equiv (upd μ fd.fref (famKT P μ fd) r ls) _
    rw [upd_ne μ _ _ hr]
    exact Equiv.rfl

/-- **The family-fix obligation from the bridge**: with `FamKTBridgeA` and
the faithfulness-shaped input (the table's family entry reads `famLim`), the
class-A family fix follows from the landed `famKT_fix` (at the `tabKT`
table) and the table transfer `famVal_tables`. All KT premises except the
bridge are the landed `famKT_fix`'s own. -/
theorem agfix_of_famKTBridgeA (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2)
    (hBridge : FamKTBridgeA P μ fd)
    (hLim : ∀ vs, Equiv (μ fd.fref vs) (famLim P μ fd vs)) (vs : List Nat) :
    Equiv (famLim P μ fd vs) (famVal (mkM P μ) W4 (σOf vs) fd) :=
  (hBridge vs).trans
    ((famKT_fix P μ fd ar hN hB hpf hclsA hri hres hf vs).symm.trans
      (famVal_tables P (tabKT_equiv (P := P) (μ := μ) (fd := fd)
        fun ls => (hLim ls).trans (hBridge ls)) (σOf vs) fd))

/-- **The family fix at an A-group, from the bridge**: `famKT_fix`'s class
premises are supplied by the landed admission bridges (`G.bounded`,
`G.famFree`, `hclsA_of_recGroupA`, `hri_of_recGroupA`,
`hres_of_admitted`); `hf` and `hN` stay per-group (the corner and the
named `hN` residue). The faithfulness premise is exactly
`RecStepCtxA.lim`. -/
theorem agfixA_of_famKTBridgeA (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (G : RecGroupA node.a)
    (hN : ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hBridge : FamKTBridgeA P μ (famDataOf node.a))
    (hLim : ∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) (vs : List Nat) :
    Equiv (famLim P μ (famDataOf node.a) vs)
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  have hLim' : ∀ ls, Equiv (μ (famDataOf node.a).fref ls) (famLim P μ (famDataOf node.a) ls) := by
    intro ls
    show Equiv (μ node.a.family.ref ls) (famLim P μ (famDataOf node.a) ls)
    rw [node.fam]
    exact hLim ls
  exact agfix_of_famKTBridgeA P μ (famDataOf node.a) node.a.family.member.arity hN G.bounded G.famFree
    (hclsA_of_recGroupA G) (hri_of_recGroupA G) (hres_of_admitted node.a) hf hBridge hLim' vs

/-! ## §2 the ι cell (named residue, at the #8239 interface) -/

/-- **The ι cell** (named residue `[rcic-f3-steag-iota-cell]`): `IotaAt` at
the A-group's recursor, from the step-context data, at every extension. The
landed ι generators (`iota_at`, `iota_at_gen_pt`) are `RecFieldsDirect`-gated;
on this base the class-A ι routes through #8239's per-witness discharger
`iota_at_of_witDirect` (the row is derived AT the witness's own constructor
under the decidable `CtorWitOK` shape check — so the cell is owed only
per witness, never per node), or through vacuity where no `IotaWitness`
exists (as at `wEnv`: `noWitness_wEnv` / `iotaAt_wEnv_vacuous`). Together
with the §3 membership this cell completes the recursor package. -/
def IotaAtCell (P : Premises4) (K : Nat → Nat) (E E' : ResolvedEnv) (f rr : Nat)
    (rm fm : CheckedMember) (node : RecNode E E' f rr rm) : Prop :=
  ∀ (μ : Nat → List Nat → PSet.{4}), RecStepCtxA P K fm node μ →
    ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr

/-- **The ι cell PRODUCED from the witness-shape cell** (#8239's
`iota_at_of_witDirect` repackaged at the cell's own μ/Efin-general
shape): three of the per-witness lemma's premises come from the ctx
itself (`X.faith`, `X.rmem`, `X.lvC`); `hop` is the group's `opq`;
the genuinely new inputs are the env-level `hFF : FamFreeBodies`, the
finite checked `hWit : WitDirect node` (= `CtorWitOK`, decidable at the
group, refused by constructor index and shape), and the per-witness side
condition `hpf` — stated here, like the cell itself, for EVERY table `μ`
and every `Efin` above `E'`. This is the honest producer: a node meeting
these inputs discharges its ι premise without any further ι work. -/
theorem iotaAtCell_of_witDirect (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    {node : RecNode E E' f rr rm}
    (G : RecGroupA node.a)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (hWit : WitDirect node)
    (hpf : ∀ (μ : Nat → List Nat → PSet.{4}) (Efin : ResolvedEnv),
      (∀ r m, E'.members r = some m → Efin.members r = some m) →
      ∀ (E'' : ResolvedEnv), (∀ r m, E''.members r = some m → Efin.members r = some m) →
        ∀ (w : IotaWitness E''), w.recRef = rr → ∀ (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
          (ρ : Nat → PSet.{4}) (hl : HasTyT E'' n Γ (iotaLhsOf w) T), HSoundT (mkM P μ) σ hl →
          (∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop), Good (mkM P μ) N Lv ∧ LOKt σ N K hl) →
          Fits (mkM P μ) σ Γ ρ → UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
        ∀ i : Fin node.a.constructors.length, w.ctorIdx = i.val → w.recMember = rm →
          w.ctorMember = node.a.constructors[i.val] →
          w.fields.length = (node.a.constructorViews i).fields.length →
          ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
          (((∀ k, k < (node.a.constructorViews i).fields.length →
            posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
              (node.a.constructorViews i).resultIndices = none) ∧
          (∃ b, node.a.minorTypes[i.val]? = some (policyPi
            (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
          ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) →
            ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
              PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
          IotaAgree (mkM P μ) σ ρ node.a w i)) ∨
          ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    IotaAtCell P K E E' f rr rm fm node := by
  intro μ X Efin hsubF
  exact iota_at_of_witDirect P X.faith hsubF X.rmem hFF G.opq hWit X.lvC (hpf μ Efin hsubF)

/-! ## §3 membership and the recursor package (the `hpkgA` cell producer) -/

/-- **The recursor's `MemberSound` from the KT line** — the `Type`-instance
case: `recVal_mem_rec_KTA` runs at the faithful table itself once the bridge
supplies its `hKT : μ f ≈ famKT` premise (the table never needs to be
modified — the KT theorem is parametric in any `μ` satisfying `hKT`), and
`groupFaith_ctorAt` supplies its constructor premise verbatim. `hN` and `hf`
stay per-group; `hT` is the uniform-`Type` condition (the `Prop` corner is
§5). -/
theorem memberSoundA_type_of_kt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (X : RecStepCtxA P K fm node μ) (G : RecGroupA node.a)
    (hN : ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ f vs) (famKT P μ (famDataOf node.a) vs))
    (hT : ∀ vs, evalTotal (σOf vs) node.a.family.resultLevel ≠ 0) :
    MemberSound P μ K rr rm := by
  have hcl := (X.facts _ _ X.rmem).1
  have hlvl := (X.facts _ _ X.rmem).2.1
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [X.rbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (X.faith.recur _).symm ?_
  refine recVal_mem_rec_KTA P μ node.a G (ls.map (evalTotal σ)) hN hf ?_
    (groupFaith_ctorAt P X.faith _) (hT _)
  intro vs
  rw [node.fam]
  exact hKT vs

/-- **The recursor package from membership plus the ι cell**: the §3/§2
components assemble into the `RecPkg` (the `RecPkg`-level twin of the cell
producer below — kept for fixture instantiations that fix `E'` once). -/
theorem recPkgA_of_ms_iota (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (hms : MemberSound P μ K rr rm) (hiota : IotaAtCell P K E E' f rr rm fm node)
    (X : RecStepCtxA P K fm node μ) : RecPkg P μ K E' rr rm :=
  ⟨hms, fun Efin hsub => hiota μ X Efin hsub⟩

/-- **The per-group premises of the Type-uniform KT route, gathered.** The
binders the producer applies are explicit (node/`μ` first), so the cell
producer below applies them positionally; no binder is phantom in its own
conclusion. `hN` is #8055's named residue (the W fixture proves it by hand
as `w_nonIR`); `hT` the uniform-`Type` face; `hKT` the table premise
(exactly `RecStepCtxA.lim ⬝ FamKTBridgeA`); `hι` the ι cell of §2. -/
structure KTTypePrem (P : Premises4) (K : Nat → Nat) : Prop where
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
  /-- the uniform-`Type` face (the `Prop` corner is §5) -/
  hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
    evalTotal (σOf vs) node.a.family.resultLevel ≠ 0
  /-- the table premise: at any faithful-entry table the entry reads `famKT` -/
  hKT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
    (∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) →
    ∀ vs, Equiv (μ f vs) (famKT P μ (famDataOf node.a) vs)
  /-- the ι cell, per group -/
  hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
    ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
    IotaAtCell P K E E' f rr rm fm node

/-- **The `hpkgA` cell, proved for uniform-`Type` A-groups**: #8239's second
cell in full, from `KTTypePrem` — everything else (the faithfulness
threading, the constructor premise, the denotation canonicalization) is
proved above or landed. -/
theorem hpkgA_type_of_kt (P : Premises4) (K : Nat → Nat) (R : KTTypePrem P K) :
    ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (fm : CheckedMember)
      (Efin : ResolvedEnv) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      RecStepCtxA P K fm node μ → RecPkgAt P μ K Efin E' rr rm := by
  intro E E' f rr rm fm Efin node μ X hsub
  have hLimF : ∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
    have h := X.lim vs
    rw [node.fam] at h
    exact h
  exact ⟨memberSoundA_type_of_kt P K X (R.hgrp node) (R.hN node μ) (R.hf node)
    (R.hKT node μ hLimF) (R.hT node), R.hι node fm μ X Efin hsub⟩

/-! ## §4 the composition: the Type-uniform A-route to `StepAG` -/

/-- **The Type-uniform A-route**: with #8239's context-free family-fix cell
`hfixA` (the one named premise — the famfix residue) plus `KTTypePrem`, the
whole `StepAG` field follows: every other input of
`StepAObstr.stepAG_of_cells` is produced by `hpkgA_type_of_kt`. The
uniform-`Prop`/`anySort` and A∧D-mixed groups are outside this route (§5)
and keep their own named corners. -/
theorem stepAG_of_ktType (P : Premises4) (K : Nat → Nat) (R : KTTypePrem P K)
    (hfixA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat),
      Equiv (famLim P μ (famDataOf node.a) vs)
        (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    StepAG P K :=
  stepAG_of_cells P K hfixA (hpkgA_type_of_kt P K R)

/-! ## §4b the bridge wiring: `KTTypePrem.hKT` produced from `famLim_famKT_type` -/

/-- **The class lift under `hnoFn`**: a class-A field list with no `.fn`
kind among its fields is a raw `FieldsClass` list. `FieldsClassA`'s third
arm (`FnRec`) is exactly the `.fn`-kinded arm (`kindOf_fnRec`), so `hnoFn`
kills it and the two remaining arms are `FieldsClass`'s own. The mirror of
the bridge module's `fieldsClassA_lift` (which goes the other way, raw →
class-A). -/
theorem fieldsClass_of_classA_noFn (f ar np nq : Nat) :
    ∀ (Fs : List (Expr Nat)) (d : Nat),
    (∀ A, A ∈ Fs → kindOf f A ≠ PKind.fn) →
    FieldsClassA f ar np nq Fs d → FieldsClass f ar np nq Fs d
  | [], _, _, _ => trivial
  | A :: Fs, d, hnf, hcl => by
      obtain ⟨hA, hFs⟩ := hcl
      refine ⟨?_, fieldsClass_of_classA_noFn f ar np nq Fs (d + 1)
        (fun A' hA' => hnf A' (List.mem_cons_of_mem _ hA')) hFs⟩
      rcases hA with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (kindOf_fnRec h) (hnf A (by simp))

/-- **The raw class premise of the bridge, from `RecGroupA` + `hnoFn`**:
the proved bridge (`famLim_famKT_type`) wants `FieldsClass` (no `FnRec`
arm); the group supplies `FieldsClassA` (landed `hclsA_of_recGroupA`);
`hnoFn` — the same premise the bridge itself carries — closes the gap arm
by arm. -/
theorem hcls_of_groupA_noFn {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} (G : RecGroupA a)
    (hnoFn : ∀ c, c ∈ (famDataOf a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf a).fref c.1 → p ≠ PKind.fn) :
    ∀ c, c ∈ (famDataOf a).ctors →
      FieldsClass (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length c.1 0 := by
  intro c hc
  refine fieldsClass_of_classA_noFn _ _ _ _ c.1 0 ?_ (hclsA_of_recGroupA G c hc)
  intro A hA hkind
  have hmem : PKind.fn ∈ kindsOf (famDataOf a).fref c.1 :=
    List.mem_map.mpr ⟨A, hA, hkind⟩
  exact (hnoFn c hc _ hmem) rfl

/-- **The direct-recursive field as a `RecApp`**: `famLim_fix`'s field
premise is the `RecApp` disjunction (the family at its canonical instance,
family-free args, as many as parameters + indices); a `DirectRec` field at
any depth is one — the depth only parametrizes the parameter locals, and
`recArgs_free` keeps the spliced args family-free. -/
theorem recApp_of_directRec {fd : FamData} {ar np nq d : Nat} {A : Expr Nat}
    (hnp : fd.params.length = np) (hnq : fd.indices.length = nq)
    (h : DirectRec fd.fref ar np nq d A) : RecApp fd ar A := by
  obtain ⟨idx, rfl, hlen, hfree⟩ := h
  refine ⟨policyParameterLocals np d ++ idx, rfl, ?_, recArgs_free fd.fref np d hfree⟩
  rw [List.length_append, List.length_append, length_paramLocals, hlen, hnp, hnq]

/-- **`famLim_fix`'s field premise, from `RecGroupA` + `hnoFn`**: the raw
`FieldsClass` of `hcls_of_groupA_noFn` read through `FieldsClass.mem` and
`recApp_of_directRec` — the same shape the landed direct row builds by
hand from `RecFieldsDirect.mem` (RcicF3MainG). -/
theorem hclsRec_of_classA_noFn {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} (G : RecGroupA a)
    (hnoFn : ∀ c, c ∈ (famDataOf a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf a).fref c.1 → p ≠ PKind.fn) :
    ∀ c, c ∈ (famDataOf a).ctors → ∀ A, A ∈ c.1 →
      occursConst (famDataOf a).fref A = false ∨
        RecApp (famDataOf a) a.family.member.arity A := by
  intro c hc A hA
  rcases FieldsClass.mem (hcls_of_groupA_noFn G hnoFn c hc) A hA with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr (recApp_of_directRec rfl rfl hd)

/-- **The famfix at a faithful table, WITHOUT the KT bridge**: the landed
`famLim_fix` route — `famLim` is a fixed point of `famVal` at the `tabLim`
table, and the transfer back to `μ`'s own table needs only the entry
faithfulness `hLim` (`tabLim_equiv`) — exactly the landed direct row's
`hfix` construction (RcicF3MainG), with the field premise supplied by
`hclsRec_of_classA_noFn` instead of `RecFieldsDirect`. Strictly lighter
than `agfix_of_famKTBridgeA`'s KT route: no `hN`, no `hf`, no `hres`, and
no full-`vs` bridge (the KT route's `tabKT_equiv` needs `μ f ≈ famKT` at
every `ls` — the Prop twin included); here the transfer is at `famLim`
itself. This produces #8239's `hfixA` cell instance at any table whose
family entry reads `famLim` — the shape of `RecStepCtxA.lim`. -/
theorem hfix_of_lim_classA_noFn (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (G : RecGroupA node.a)
    (hnoFn : ∀ c, c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hLim : ∀ vs, Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs)) :
    ∀ vs, Equiv (famLim P μ (famDataOf node.a) vs)
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  have hLim' : ∀ ls, Equiv (μ (famDataOf node.a).fref ls)
      (famLim P μ (famDataOf node.a) ls) := by
    intro ls
    show Equiv (μ node.a.family.ref ls) (famLim P μ (famDataOf node.a) ls)
    rw [node.fam]
    exact hLim ls
  intro vs
  exact (famLim_fix P μ (famDataOf node.a) node.a.family.member.arity G.bounded G.famFree
    (hclsRec_of_classA_noFn G hnoFn) (hri_of_recGroupA G) vs).symm.trans
    (famVal_tables P (tabLim_equiv P μ node.a hLim') _ _)

/-- **The bridge wired**: `KTTypePrem` with its `hKT` field PRODUCED — the
KT table premise is no longer open on the `Type` route. It is
`RecStepCtxA.lim` composed with the proved `famLim_famKT_type`
(`RcicF3FamKTBridge` §6); the bridge's per-group premises come from
`RecGroupA` (`bounded`/`famFree`/`riFree` via the landed admission
bridges), `hres_of_admitted`, the two per-group named residues `hN` +
`hf`, and the bridge's own `hnoFn` (no function-recursive field — the
class-A restriction). The bridge's Type-read premise `hk` is `hT`
itself: `famDataOf`'s `resLevel` is `family.resultLevel` by definition. -/
theorem ktTypePrem_of_famKT (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
    (hnoFn : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (c : List (Expr Nat) × List (Expr Nat)),
      c ∈ (famDataOf node.a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ PKind.fn)
    (hι : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (fm : CheckedMember),
      IotaAtCell P K E E' f rr rm fm node) :
    KTTypePrem P K := by
  refine ⟨hgrp, hN, hf, hT, ?_, hι⟩
  intro E E' f rr rm node μ hLimF vs
  exact (hLimF vs).trans (famLim_famKT_type P μ (famDataOf node.a)
    node.a.family.member.arity (hf node) (hgrp node).bounded (hgrp node).famFree
    (hcls_of_groupA_noFn (hgrp node) (hnoFn node))
    (hri_of_recGroupA (hgrp node)) (hres_of_admitted node.a) (hN node μ)
    (hnoFn node) vs (hT node vs))

/-- **The apex, bridge wired**: uniform-`Type` A-groups' whole `StepAG`
debt with the KT table premise produced from the proved bridge. The named
premises are exactly: `hfixA` (#8239's context-free famfix cell — the one
named premise of §4), `hgrp`/`hN`/`hf`/`hT` (§4's own per-group
premises), `hnoFn` (the bridge's class-A restriction), and `hι` (the ι
cell of §2). Everything between them and `StepAG` is proved here, in
#8239, or in `RcicF3FamKTBridge`. -/
theorem stepAG_of_famKT_type (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
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
  stepAG_of_ktType P K (ktTypePrem_of_famKT P K hgrp hN hf hT hnoFn hι) hfixA

/-- **The apex, famfix from table faithfulness**: `StepAG` with BOTH cells
produced — the KT table premise from the proved bridge (§4b) and the famfix
cell from the landed `famLim_fix` at any table whose family entry reads
`famLim` (`hLimTab` — exactly #8239's `RecStepCtxA.lim` field lifted to the
tier level; the landed direct row derives it from `FaithfulR` at every
group, RcicF3MainG:938). The context-free `hfixA` premise of §4 is hereby
reduced to the faithful-table form. Named premises: `hgrp`, `hN`, `hf`,
`hT`, `hnoFn`, `hι`, `hLimTab`. -/
theorem stepAG_of_famKT_type_lim (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hN : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}),
      ∀ σ ρp (j : Fin (famDataOf node.a).ctors.length),
        NonIRSem P μ σ ρp (famDataOf node.a).fref ((famDataOf node.a).ctors.get j).1)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
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
    (hpkgA_type_of_kt P K (ktTypePrem_of_famKT P K hgrp hN hf hT hnoFn hι))

/-! ## §4c the `hN` discharge (from the structure, and at a member-carrying env) -/

/-- **`hN` from the structure's own `NonIR` predicate**: the KT route's
per-group `hN` premise (session-21's named residue, #8055's) is produced
from `a.NonIR` — `∀ i, NonIRFieldList E a.family.ref
(a.constructorViews i).fields`, the landed non-IR predicate
(`RcicIndGroupNonIR:161`) — via `RcicF3KTWNonIR`'s route
(`hN_of_kinds` + `nonIRKinds_of_fieldList`), whose `FieldsClass` premise
is supplied by §4b's own `hcls_of_groupA_noFn` (the `RecGroupA` → raw-class
bridge under `hnoFn`; NO full `RecGroup` is needed — the `ShapesMatch`
component of `RecGroup.shapes` never enters the hN route). -/
theorem hN_of_nonIR (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (G : RecGroupA a)
    (hnoFn : ∀ c, c ∈ (famDataOf a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf a).fref c.1 → p ≠ PKind.fn)
    (hNI : a.NonIR) :
    ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1 := by
  refine hN_of_kinds P μ (famDataOf a) ?_
  intro c hc
  have hcls := hcls_of_groupA_noFn G hnoFn c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  exact nonIRKinds_of_fieldList hcls (hNI i)

/-- **`hN` from the environment, at a member-carrying env**: #8067's
`admitted_group_nonIR_scoped` (`EnvWfT` + the group's scope test + the
recursor member's presence) produces `a.NonIR`, composed with
`hN_of_nonIR`. This form applies wherever the admission's own env carries
the recursor member (fixture-level uses; the member premise is the group
identity). For TIER nodes — where `RecNode` admits at `E0` with the
recursor FRESH (`node.fresh`) — the scoped route additionally needs a
transport of the admission along `extendEnv node.E0 rr rm` (and of the
`NonIR` predicate across the env change); both are nameable cells, neither
is opened here. -/
theorem hN_of_envScoped (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (G : RecGroupA a)
    (hnoFn : ∀ c, c ∈ (famDataOf a).ctors →
      ∀ p, p ∈ kindsOf (famDataOf a).fref c.1 → p ≠ PKind.fn)
    (hW : EnvWfT E) (hC : hW.ScopeCheck) (hp : E.members r = some m) :
    ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1 :=
  hN_of_nonIR P μ a G hnoFn (admitted_group_nonIR_scoped hW hC hp a)

/-- **The apex, `hN` discharged from the structure**: `stepAG_of_famKT_type`
with the per-group `hN` premise replaced by `hNI` — every node's admitted
structure satisfies its own non-IR predicate (the W fixture's `w_nonIR` is
exactly this premise, by hand). The named premises are now exactly
`hfixA`, `hgrp`, `hNI`, `hf`, `hT`, `hnoFn`, `hι`. -/
theorem stepAG_of_famKT_type_nonIR (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hNI : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.NonIR)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
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
  stepAG_of_famKT_type P K hgrp
    (fun {E E' f rr rm} node μ => hN_of_nonIR P μ node.a (hgrp node) (hnoFn node) (hNI node))
    hf hT hnoFn hι hfixA

/-- **The faithful-table apex, `hN` discharged from the structure**:
`stepAG_of_famKT_type_lim` with `hN` replaced by `hNI` (per-node
`a.NonIR`), everything else unchanged. -/
theorem stepAG_of_famKT_type_lim_nonIR (P : Premises4) (K : Nat → Nat)
    (hgrp : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, RecGroupA node.a)
    (hNI : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm, node.a.NonIR)
    (hf : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ node : RecNode E E' f rr rm,
      (famDataOf node.a).fref ≠ 1 ∧ (famDataOf node.a).fref ≠ 2)
    (hT : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember},
      ∀ (node : RecNode E E' f rr rm) (vs : List Nat),
      evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
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
  stepAG_of_famKT_type_lim P K hgrp
    (fun {E E' f rr rm} node μ => hN_of_nonIR P μ node.a (hgrp node) (hnoFn node) (hNI node))
    hf hT hnoFn hι hLimTab

/-! ## §4d `hLimTab` from table faithfulness -/

/-- **The faithful-table premise produced from `FaithfulR`**: the apices'
`hLimTab` (#8239's `RecStepCtxA.lim` lifted to the tier) is exactly the
`.fam`-role equation of a faithful table: `RecNode`'s `E'` always carries
the family member (`node_fam_member`, RcicF3MainG:248), and `memberValR`
at the `.fam` role IS `famLim` (RcicF3EnvG:34). This is the tier-level
source the direct row uses inline (RcicF3MainG:938); here it is a
standalone producer — a consumer holding `FaithfulR P μ ctx E'` plus the
role equation at `f` discharges `hLimTab` outright. `FaithfulR` is
exactly the table premise the tier's own statements quantify over
(RcicF3MainG:645/:652), so it DOES survive to the tier level. -/
theorem hLimTab_of_faithfulR (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (hctxF : ctx f = Role.fam (famDataOf node.a))
    (hF : FaithfulR P μ ctx E') (vs : List Nat) :
    Equiv (μ f vs) (famLim P μ (famDataOf node.a) vs) := by
  have h := hF f node.a.family.member (node_fam_member node) vs
  rw [hctxF] at h
  exact h

/-! ## §5 the named corners -/

/-- **The uniform-`Prop`/`anySort` corner** (named residue
`[rcic-f3-steag-prop-anysort-corner]`): a `Prop` family with large
elimination and a function-recursive field. The KT `Type` route needs
`hT : evalTotal … ≠ 0`; the KT `Prop` route needs `policy = propOnly`; the B1
package needs `¬ PendA` (`recFieldsDirect_of_notAD`). No landed membership
route covers this corner. -/
def AGPropAny {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  UniformProp node.a.family.resultLevel ∧ node.a.policy = .anySort ∧ PendA node

/-- **The A∧D mixed corner** (named residue `[rcic-f3-steag-mixed-ad-corner]`):
`PendA` does not exclude a noncanonical `recursive 0` field (`PendD`), and a
mixed field is outside `FieldsClassA` (neither family-free, nor canonical
`DirectRec`, nor `FnRec`), so `RecGroupA` — the KT line's structure premise —
fails there, while the `PendA`-first dispatch (`groupStepAt_of_AD`) still
routes the group to `StepAG`. #8234 already names these groups "the A lane's
debt". -/
def AGMixedAD {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  PendA node ∧ PendD node

/-! ## §7 the route boundary: `RecGroupA ∧ hnoFn` meets `PendA` only at δ-exposed recursion

The §4 apices carry `hnoFn` (no `.fn`-kinded field) as a named premise — the
bridge's class restriction. This section measures what that premise does to
`StepAG`'s subject: a `PendA` node is one with an admission shape
`.recursive (m+1)` (`RcicF3Cover:101`) — a function-recursive field. Under
`RecGroupA` (`FieldsClassA`: every field family-free, canonical `DirectRec`,
or syntactic `FnRec`) the three arms of a `.recursive (m+1)` field are:

* `FnRec` — killed by `hnoFn` (`kindOf_fnRec`: a syntactic `FnRec` field is
  Π-headed with the family occurring, `kindOf` = `.fn`);
* `DirectRec` — killed by shape: a canonical family application is
  const-headed and δ-opaque (`RecGroupA.opq`), so its whnf telescope is
  empty and any permitted shape is `.recursive 0`, never `.recursive (m+1)`;
* family-free (`occursConst f A = false`) — the ONLY survivor: the field's
  function recursion is entirely δ-exposed (the stored field does not
  mention the family at all; `fieldAnalyze` sees the Π telescope only
  through `whnf` of a transparent body).

So the KT `Type` route can meet `StepAG`'s obligation ONLY at groups whose
function recursion is δ-exposed — the syntactic-`FnRec` `PendA` groups
(the `W` fixture, `wFieldF`) are OUTRIGHT outside its premise class, and a
"pure direct-rec fixture" (the session-22 plan) is a category error:
such a family is never `PendA` (its shapes are `.nonrecursive`/
`.recursive 0`), it is `ClassG`/B1 territory. Whether the δ-exposed
corner actually satisfies `RecGroupA.shapes` — the kind-based `shapesOf`
read vs the whnf-based `shapesAt` read deriving the same stored
`minorTypes` — is `derivedMinor`'s shape-injectivity question, NOT opened
here (named below). The honest remaining content of the producer line is
the bridge WITHOUT `hnoFn`: `famLim ≈ famKT ≈ famVal` at `FnRec` families
(`[rcic-f3-steag-famkt-bridge]`, the `W`-fixture instance `[rcic-f3-stepa-famfix]`). -/

/-- The `k`-th field's disjunction from a `FieldsClassA` (local twin of
`RcicF3KTWMinorA`'s private `fieldsClassA_at`). -/
theorem fieldsClassA_get {f ar np nq : Nat} :
    (Fs : List (Expr Nat)) → (d k : Nat) → FieldsClassA f ar np nq Fs d →
    ∀ A, Fs[k]? = some A →
      occursConst f A = false ∨ DirectRec f ar np nq (d + k) A ∨ FnRec f ar np nq (d + k) A
  | [], _, _, _, _, h => by cases h
  | A :: Fs, d, 0, h, _, hA => by
      obtain ⟨hd, -⟩ := h
      rw [List.getElem?_cons_zero] at hA
      obtain rfl := Option.some.inj hA
      exact hd
  | A :: Fs, d, k + 1, h, A', hA => by
      obtain ⟨-, ht⟩ := h
      rw [List.getElem?_cons_succ] at hA
      simpa only [Nat.add_right_comm] using fieldsClassA_get Fs (d + 1) k ht A' hA

/-- Position-wise read of the admission shapes: the `k`-th analyzed shape
is the `k`-th field's `fieldAnalyze` verdict at depth `depth + k`, and only
`.permitted` verdicts survive into the list. -/
theorem fieldShapesFuel_get {E : ResolvedEnv} {f nu np nq depth : Nat} :
    (Fs : List (Expr Nat)) → (fuel : Nat) → (ss : List FieldShape) →
    fieldShapesFuel E fuel f nu np nq depth Fs = some ss →
    ∀ (k : Nat) (s : FieldShape), ss[k]? = some s →
      ∃ (A : Expr Nat) (idxs : List (Expr Nat)),
        Fs[k]? = some A ∧ fieldAnalyze E fuel f nu np nq (depth + k) A = .permitted s idxs
  | [], _, ss, hss, _, _, hk => by
      simp only [fieldShapesFuel] at hss
      obtain rfl : ss = ([] : List FieldShape) := (Option.some.inj hss).symm
      rw [List.getElem?_nil] at hk
      cases hk
  | A :: Fs, fuel, ss, hss, k, s, hk => by
      simp only [fieldShapesFuel] at hss
      cases hfa : fieldAnalyze E fuel f nu np nq depth A with
      | permitted shape idxs =>
          rw [hfa] at hss
          cases hrest : fieldShapesFuel E fuel f nu np nq (depth + 1) Fs with
          | none => rw [hrest] at hss; exact absurd hss (by simp)
          | some rest =>
              rw [hrest] at hss
              have h1 : shape :: rest = ss := by injection hss
              obtain rfl : ss = shape :: rest := h1.symm
              rcases k with _ | k
              · rw [List.getElem?_cons_zero] at hk
                obtain rfl : s = shape := Option.some.inj hk.symm
                exact ⟨A, idxs, List.getElem?_cons_zero, by
                  simpa only [Nat.add_zero] using hfa⟩
              · rw [List.getElem?_cons_succ] at hk
                obtain ⟨A', idxs', hA, hfa'⟩ :=
                  fieldShapesFuel_get Fs fuel rest hrest k s hk
                refine ⟨A', idxs', ?_, by
                  simpa only [Nat.add_right_comm] using hfa'⟩
                rw [List.getElem?_cons_succ]
                exact hA
      | refused _ => rw [hfa] at hss; exact absurd hss (by simp)
      | unresolved => rw [hfa] at hss; exact absurd hss (by simp)

/-- **The route boundary** (named residue `[rcic-f3-steag-ktroute-boundary]`):
under `RecGroupA` and the bridge's `hnoFn`, every `PendA` field is
SYNTACTICALLY family-free — the group's function recursion is entirely
δ-exposed. The syntactic-`FnRec` `PendA` groups (the `W` fixture) are
outright outside the KT `Type` route's premise class, and a pure
direct-rec family is never `PendA` at all (`ClassG`/B1 territory). What
remains of the producer line is the bridge WITHOUT `hnoFn` (the `FnRec`
families); whether the δ-exposed corner even satisfies `RecGroupA.shapes`
(the kind-read vs whnf-read derivation of the stored `minorTypes`) is
`derivedMinor`'s shape-injectivity question, named here, not opened. -/
theorem pendA_deltaExposed_of_groupA_noFn {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (G : RecGroupA node.a)
    (hnoFn : ∀ i : Fin node.a.constructors.length,
      ∀ p, p ∈ kindsOf node.a.family.ref (node.a.constructorViews i).fields → p ≠ PKind.fn)
    (hP : PendA node) :
    ∃ (i : Fin node.a.constructors.length) (k m : Nat) (A : Expr Nat),
      (node.a.constructorViews i).fields[k]? = some A ∧
        (node.h14.shapesAt i)[k]? = some (FieldShape.recursive (m + 1)) ∧
        occursConst node.a.family.ref A = false := by
  obtain ⟨i, k, m, hs⟩ := hP
  obtain ⟨A, idxs, hAk, hfa⟩ :=
    fieldShapesFuel_get (node.a.constructorViews i).fields (node.h14.fuelAt i)
      (node.h14.shapesAt i) (node.h14.analyzed i) k _ hs
  rcases fieldsClassA_get (node.a.constructorViews i).fields 0 k (G.fields i) A hAk
    with hfree | hdr | hfr
  · exact ⟨i, k, m, A, hAk, hs, hfree⟩
  · -- canonical DirectRec: const-headed, δ-opaque, empty telescope
    obtain ⟨idx, hA, _, _⟩ := hdr
    rw [hA] at hfa
    have h0 := Rcic.Declarative.Ann.fieldAnalyze_famApp_permitted
      (fam := node.a.family.ref) (ls := canonL node.a.family.member.arity)
      (G.opq (canonL node.a.family.member.arity)) hfa
    injection h0 with h'
    exact absurd h' (by omega)
  · -- syntactic FnRec: kindOf = .fn, killed by hnoFn
    exfalso
    have hkind : kindOf node.a.family.ref A = PKind.fn := kindOf_fnRec hfr
    obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.mp hAk
    have hmem : kindOf node.a.family.ref A
        ∈ kindsOf node.a.family.ref (node.a.constructorViews i).fields :=
      List.mem_map_of_mem (f := kindOf node.a.family.ref) (hk2 ▸ List.getElem_mem hk1)
    rw [hkind] at hmem
    exact absurd rfl (hnoFn i _ hmem)

end Rcic.F3.StepAG
