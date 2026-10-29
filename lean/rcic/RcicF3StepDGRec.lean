import rcic.RcicF3StepDGOrder

/-!
# F3 D, group-granular, stage 2: the bounded recursor chain and the checked order

`closure_claim = 0`.

Stage 1 (`RcicF3StepDGOrder`) controlled the raw family chain at the
canonical instance and produced `GroupFaithB` in the raw roles
(`groupFaithB_raw`). Stage 2 finishes the group step.

* §1 lifts `NoFunRec` out of `¬ PendA`: the `StepDG` premise is the absence
  of function-recursive shapes; the group machinery consumes the same
  statement fieldwise.
* §2 is the transfer the bounded chain reads: at instances within the
  recursor's bound `K rr` the family's entry is the normalized limit
  (`famLim_raw_norm`), so the model table at `tabLim` agrees with the raw
  table on every constructor row and every canonical family application the
  chain constructs (`famLE_lim_self`, `ed_lim_of_self`, `ed_self_of_lim`).
  These are the only reads of the family entry the chain makes —
  `den_recApp`, `famLE_upd`, `famEnd_upd_equiv` are all canonical-instance
  statements.
* §3 is the landed `RcicF3DRec` chain verbatim — `rec_stepDB`,
  `rec_stageDB`, `rec_fields_okDB`, `minor_ok_groupDB`,
  `recVal_mem_recDB`, `recVal_mem_recPDB` — with the family's entry read at
  instances within `K rr` instead of the global fixed point `hLim`.
* §4 is `ctor_member_soundB`: `ctor_member_sound` with the family's value
  needed only at instances within the constructor's own bound `K c`.
* §5 is `CtorsBelowRec`: the converse of the landed `RecBelowCtors` —
  every constructor's instance bound at or below the recursor's. A finite
  check (`ctorsBelowRecB`). It is the side condition this order route
  needs: the constructor's soundness at `ls` reads the family's entry at
  `ls.map (evalTotal σ)`, which must sit within `K rr` for `famB_raw` —
  `K c ≤ K rr` discharges it.
* §6 is `gInv_groupRawD`: `gInv_groupD` in the raw roles — `dStage_of` +
  `groupFaithB_raw` + `iota_at_D` + the bounded chain + `walk_sound` —
  consuming the `GroupStepAt` premises plus `hpar`, the `Prop`-corner
  clause, and `CtorsBelowRec`.
* §7 is `stepDG_under`: `StepDG` under the checked side conditions —
  rescoped to `StepDG`'s own domain after swe-audit-m3's stage-2 refusal
  (`StepDGSide` demanded per group under `(∀ node, ¬ PendA) ∧ (∃ node,
  PendD)`, `stepDG_at` the per-group producer), the weakest side
  condition this route needs, recorded rather than hidden. The checks
  themselves (`hpar`, the `Prop` corner, the order) are decided in
  `RcicF3StepDGCheck`.

Axioms of every declaration ⊆ {`propext`, `Quot.sound`}.
-/

set_option autoImplicit false

namespace Rcic.F3.StepDGOrder

open Rcic.Declarative Rcic.Model.PS Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup

/-! ## §1 `¬ PendA` is `NoFunRec` -/

/-- A `PendA` witness is a `recursive (m+1)` shape at a constructor field;
without one every admitted shape is `.nonrecursive` or `.recursive 0`. -/
theorem noFunRec_of_not_pendA {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    {node : RecNode E E' f rr rm} (h : ¬ PendA node) : NoFunRec node := by
  intro i s hs
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hs
  cases hs' : (node.h14.shapesAt i)[k] with
  | nonrecursive => exact Or.inl rfl
  | recursive m =>
      cases m with
      | zero => exact Or.inr rfl
      | succ m =>
          exact absurd ⟨i, k, m, (List.getElem?_eq_getElem hk).trans (congrArg Option.some hs')⟩ h

/-! ## §2 the canonical-instance transfer

At instances within the recursor's bound the raw family entry is the
normalized limit (stage 1). Everything the recursor chain reads of the
family's entry is at the canonical instance `(canonL ar).map (evalTotal σ)`
— the constructor-row fibre, the recursive-argument application, the limit
itself — so the `tabLim` table agrees with `μ` on every one of them. -/

section BRec

variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat}
  {rm : CheckedMember} {node : RecNode E E' f rr rm}
  {μ : Nat → List Nat → PSet.{4}}
  (D : DStage P K node μ)
  (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs))

include D hlim

/-- The canonical instance of a `≤ K rr`-bounded instance stays bounded:
its levels are `evalTotal σ (Level.param i)` with `i < ar`, hence `σOf vs i`. -/
theorem canonL_bounded (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) :
    ∀ v, v ∈ (canonL node.a.family.member.arity).map (evalTotal (σOf vs)) → v ≤ K rr := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  exact σOf_le hvs i

/-- The canonical instance has the family's arity. -/
theorem canonL_length {σ : Nat → Nat} :
    ((canonL node.a.family.member.arity).map (evalTotal σ)).length =
      node.a.family.member.arity := by simp [canonL]

/-- Updating the family's entry by its own current value is the identity. -/
theorem upd_self : upd μ (nodeFam node).fref (μ (nodeFam node).fref) = μ := by
  funext r ls
  by_cases h : r = (nodeFam node).fref
  · subst h; exact upd_eq μ _ _ ls
  · exact upd_ne μ _ _ h ls

/-- The entry is the normalized limit at instances within the bound —
`famB_raw` at `vs` composed with `famLim_raw_norm`. -/
theorem limB (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hlen : vs.length = node.a.family.member.arity) :
    Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs) :=
  (hlim vs).trans (famLim_raw_norm D vs hvs hlen)

/-- The recursive family's application under its own table is the fibre of
its own value — `den_recApp` with the entry updated by itself. -/
theorem den_self_recApp (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {args : List (Expr Nat)}
    (hargs : ∀ e, e ∈ args → occursConst (nodeFam node).fref e = false) :
    den (mkM P μ) σ ρ (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args) =
      fapps (μ (nodeFam node).fref ((canonL node.a.family.member.arity).map (evalTotal σ)))
        (args.map (den (mkM P μ) σ ρ)) := by
  have h := den_recApp P μ (μ (nodeFam node).fref) σ ρ
    (ar := node.a.family.member.arity) hargs
  rwa [upd_self D hlim] at h

/-- The `tabLim` fibre's elements at a bounded instance are the raw fibre's:
`den_recApp` on both sides plus `ed_mkM`, with `limB` at the canonical
instance. -/
theorem ed_self_of_lim (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) (ρ : Nat → PSet.{4})
    {args : List (Expr Nat)} (hargs : ∀ e, e ∈ args → occursConst (nodeFam node).fref e = false)
    {x : PSet.{4}}
    (h : x ∈ Ed (mkM P (tabLim P μ (nodeFam node)))
      (den (mkM P (tabLim P μ (nodeFam node))) (σOf vs) ρ
        (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args))) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ
      (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args)) := by
  unfold tabLim at h
  rw [den_recApp P μ (famLim P μ (nodeFam node)) (σOf vs) ρ
    (ar := node.a.family.member.arity) hargs, ed_mkM P _ μ] at h
  rw [den_self_recApp D hlim (σOf vs) ρ hargs]
  exact mem_congr_right (ed_congr _ (fapps_congr (limB D hlim _
    (canonL_bounded D hlim vs hvs) (canonL_length D hlim)).symm _)) h

/-- And the converse direction. -/
theorem ed_lim_of_self (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) (ρ : Nat → PSet.{4})
    {args : List (Expr Nat)} (hargs : ∀ e, e ∈ args → occursConst (nodeFam node).fref e = false)
    {x : PSet.{4}}
    (h : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ
      (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args))) :
    x ∈ Ed (mkM P (tabLim P μ (nodeFam node)))
      (den (mkM P (tabLim P μ (nodeFam node))) (σOf vs) ρ
        (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args)) := by
  unfold tabLim
  rw [den_recApp P μ (famLim P μ (nodeFam node)) (σOf vs) ρ
    (ar := node.a.family.member.arity) hargs, ed_mkM P _ μ]
  rw [den_self_recApp D hlim (σOf vs) ρ hargs] at h
  exact mem_congr_right (ed_congr _ (fapps_congr (limB D hlim _
    (canonL_bounded D hlim vs hvs) (canonL_length D hlim)) _)) h

/-- The `tabLim` table bounds the raw table on the constructor rows, at a
bounded instance: `famLE_upd` with `X₂ = μ (nodeFam node).fref` — the source
`hsm`/`hrec` obligations are `small_rec_lim` and the canonical-instance
transfer. -/
theorem famLE_lim_self (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) :
    FamLE (mkM P (tabLim P μ (nodeFam node))) (mkM P μ)
      (W4 (evalTotal (σOf vs) (nodeFam node).resLevel)) (σOf vs) (nodeFam node).ctors := by
  have hX : Equiv (famLim P μ (nodeFam node)
      ((canonL node.a.family.member.arity).map (evalTotal (σOf vs))))
      (μ (nodeFam node).fref ((canonL node.a.family.member.arity).map (evalTotal (σOf vs)))) :=
    (limB D hlim _ (canonL_bounded D hlim vs hvs) (canonL_length D hlim)).symm
  have hrec : ∀ (ρ : Nat → PSet.{4}) (args : List (Expr Nat)),
      (∀ e, e ∈ args → occursConst (nodeFam node).fref e = false) →
      args.length = ((nodeFam node).params ++ (nodeFam node).indices).length → ∀ z,
      z ∈ Ed (mkM P (upd μ (nodeFam node).fref (famLim P μ (nodeFam node))))
        (den (mkM P (upd μ (nodeFam node).fref (famLim P μ (nodeFam node)))) (σOf vs) ρ
          (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args)) →
      z ∈ Ed (mkM P (upd μ (nodeFam node).fref (μ (nodeFam node).fref)))
        (den (mkM P (upd μ (nodeFam node).fref (μ (nodeFam node).fref))) (σOf vs) ρ
          (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args)) := by
    intro ρ args hargs _ z hz
    rw [den_recApp P μ _ (σOf vs) ρ (ar := node.a.family.member.arity) hargs, ed_mkM P _ μ] at hz
    rw [den_recApp P μ _ (σOf vs) ρ (ar := node.a.family.member.arity) hargs, ed_mkM P _ μ]
    exact mem_congr_right (ed_congr _ (fapps_congr hX _)) hz
  have hsm : ∀ (ρ : Nat → PSet.{4}) (args : List (Expr Nat)),
      (∀ e, e ∈ args → occursConst (nodeFam node).fref e = false) →
      args.length = ((nodeFam node).params ++ (nodeFam node).indices).length →
      Ed (mkM P (upd μ (nodeFam node).fref (μ (nodeFam node).fref)))
        (den (mkM P (upd μ (nodeFam node).fref (μ (nodeFam node).fref))) (σOf vs) ρ
          (foldApps (.const (nodeFam node).fref (canonL node.a.family.member.arity)) args)) ∈
        W4 (evalTotal (σOf vs) (nodeFam node).resLevel) := by
    intro ρ args hargs hl
    exact small_recApp_of_equiv P μ (nodeFam node) _ _ _ (σOf vs) _ hX.symm ρ args hargs
      (small_rec_lim P μ (nodeFam node) _ D.RG.bounded D.RG.famFree (σOf vs) ρ args hargs hl)
  have h := famLE_upd P μ (nodeFam node) node.a.family.member.arity D.RG.cls
    (RecGroupD.ri node.a D.RG) (famLim P μ (nodeFam node)) (μ (nodeFam node).fref) (σOf vs) hrec hsm
  rw [upd_self D hlim] at h
  exact h

/-- The family's value at its own instance, bounded: `famB_raw` at
`policyFamilyLevels` (within `K rr` by `famLevels_le`), then
`famVal_levels` to `σOf vs`. -/
theorem famμ_of_limDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) :
    Equiv (μ node.a.family.ref ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) :=
  (famB_raw D hlim _ (famLevels_le node.a.family hvs) (famLevels_length node.a.family vs)).trans
    (famVal_levels (mkM P μ) (k := node.a.family.member.arity) (σOf_policyFamilyLevels_agree node.a.family vs)
      W4 _ hBfd)

/-! ## §3 the bounded recursor chain

The `RcicF3DRec` chain verbatim, with the family's entry read at instances
within the bound: `hLim` replaced by `hvs` (the instance is within the
recursor's bound) plus `limB`/`famLE_lim_self`/`ed_lim_of_self`/
`ed_self_of_lim`/`famμ_of_limDB`. -/

/-- **One step, bounded**: the stage claim at `n`, given the recursive
fields' values at `n`. -/
theorem rec_stepDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps)
    (hpsl : ps.length = node.a.family.parameters.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType node.a.family node.a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) node.a.minorTypes (vcons mo (push ps ρ0)) ms)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = node.a.family.indices.length → TelFits (mkM P μ) (σOf vs) node.a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) →
      CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors (push ps ρ0) is j xs →
      Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs) z →
      fapps (ms.getD j pempty) (ihArgs node.a.family.ref g (ctorFieldsOf (famDataOf node.a) j) xs) ∈
        Ed (mkM P μ) (fapps mo (is ++ [z])) →
      g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z]))) (n : Nat)
    (hRn : ∀ (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4}), idx.length = node.a.family.indices.length →
      (∀ e, e ∈ idx → occursConst node.a.family.ref e = false) →
      x ∈ Ed (mkM P (tabIter P μ (nodeFam node) n)) (den (mkM P (tabIter P μ (nodeFam node) n)) (σOf vs)
        (push ys (push ps ρ0)) (foldApps (.const node.a.family.ref (canonL node.a.family.member.arity))
          (policyParameterLocals node.a.family.parameters.length ys.length ++ idx))) →
      g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x]))) :
    StageOKD P μ node.a (fuelAt := node.h14.fuelAt) g vs ps mo n := by
  intro is z hl hisfit hz
  obtain ⟨j, xs, hcf, hzc⟩ := mem_el_famEnd (fd := nodeFam node) hl hz
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (nodeFam node).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < node.a.constructors.length := by rwa [nodeFam_ctors_length] at hjk'
  have hC := famChain_iter P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree
    D.RG.cls (RecGroupD.ri node.a D.RG) (σOf vs)
  have hcfM : CtorFits (mkM P μ) (σOf vs) (nodeFam node).ctors (push ps ρ0) is j xs :=
    CtorFits_mono (famLE_lim_self D hlim vs hvs) (CtorFits_mono (hC.toLim n) hcf)
  have hcfM0 : CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors (push ps ρ0) is j xs :=
    (ctorFits_iff_of_agree _ _ (hag ps hps) is j xs).mpr hcfM
  have hfo : ctorFieldsOf (nodeFam node) j =
      (node.a.constructorViews ⟨j, hjk⟩).fields.map (normField node.E0 (node.h14.fuelAt ⟨j, hjk⟩) node.a.family.ref) :=
    ctorFieldsOf_of_get (nodeFam_ctor node ⟨j, hjk⟩)
  have hcc : c = ((node.a.constructorViews ⟨j, hjk⟩).fields.map (normField node.E0 (node.h14.fuelAt ⟨j, hjk⟩) node.a.family.ref),
      (node.a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := nodeFam_ctor node ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  have hih : IHOkF (mkM P μ) (σOf vs) node.a.family.parameters.length mo g
      node.a.family.ref (ctorFieldsOf (nodeFam node) j) (push ps ρ0) xs := by
    rw [hfo]
    exact ihOkF_walk (mkM P μ) (mkM P (tabIter P μ (nodeFam node) n)) (σOf vs) node.a.family.ref
      node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length mo _ ps hRn _ [] xs
      (D.RG.fields ⟨j, hjk⟩) hxs
  have hmin := minor_ok_recD node.a vs D.RG.hcl node.h14.fuelAt node.h14.shapesAt D.RG.shapes
    (famμ_of_limDB D hlim hBfd vs hvs) hctorμ ps mo ms is hpsl hl hmo hms hisfit j xs hcfM0 _ hih
  have hcv : Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs) z := hzc.symm
  exact hclose n is z j xs hl hisfit hz hcfM0 hcv
    (mem_congr_right (ed_congr _ (fapps_congr_args mo (LEq_append (LEq.refl is)
      (show LEq [ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs] [z] from ⟨hcv, trivial⟩)))) hmin)

/-- **The stage claim at every stage, bounded.** -/
theorem rec_stageDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps)
    (hpsl : ps.length = node.a.family.parameters.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType node.a.family node.a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) node.a.minorTypes (vcons mo (push ps ρ0)) ms)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = node.a.family.indices.length → TelFits (mkM P μ) (σOf vs) node.a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) →
      CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors (push ps ρ0) is j xs →
      Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs) z →
      fapps (ms.getD j pempty) (ihArgs node.a.family.ref g (ctorFieldsOf (famDataOf node.a) j) xs) ∈
        Ed (mkM P μ) (fapps mo (is ++ [z])) →
      g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z]))) :
    ∀ n, StageOKD P μ node.a (fuelAt := node.h14.fuelAt) g vs ps mo n := by
  intro n
  induction n with
  | zero =>
      refine rec_stepDB D hlim hBfd vs hvs hag hctorμ ps mo ms hps hpsl hmo hms g hclose 0
        fun ys idx x hl hidx hx => ?_
      exact absurd (mem_congr_right (ed_rec_zero P μ (nodeFam node) node.a.family.member.arity D.RG.bounded
        D.RG.famFree (σOf vs) _ _ (recArgs_free _ _ _ hidx)
        (by simp only [List.length_append, length_paramLocals, hl]; rfl)) hx) PSet.not_mem_pempty
  | succ k ih =>
      refine rec_stepDB D hlim hBfd vs hvs hag hctorμ ps mo ms hps hpsl hmo hms g hclose (k + 1)
        fun ys idx x hl hidx hx => ?_
      have hargs := recArgs_free node.a.family.ref node.a.family.parameters.length ys.length hidx
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ (nodeFam node) (σOf vs) (push ys (push ps ρ0))
        (policyParameterLocals node.a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
      · have hx' := mem_congr_right (ed_rec_succ_fit P μ (nodeFam node) node.a.family.member.arity D.RG.bounded
          D.RG.famFree k (σOf vs) _ _ hargs hfit) hx
        have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
        rw [hpsl] at e
        unfold RecFits at hfit
        rw [e] at hfit hx'
        exact stage_of_fibD P μ node.a g vs ps mo hpsl k ih _ x hfit hx'
      · exact absurd (mem_congr_right (ed_rec_succ_nofit P μ (nodeFam node) node.a.family.member.arity
          D.RG.bounded D.RG.famFree k (σOf vs) _ _ hargs
          (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hx) PSet.not_mem_pempty

/-- The recursive fields' values lie in the motive, at the final table,
bounded: `rec_fields_okD` with the limit transfer at the canonical
instance. -/
theorem rec_fields_okDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps)
    (hpsl : ps.length = node.a.family.parameters.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType node.a.family node.a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) node.a.minorTypes (vcons mo (push ps ρ0)) ms)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = node.a.family.indices.length → TelFits (mkM P μ) (σOf vs) node.a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) →
      CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors (push ps ρ0) is j xs →
      Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs) z →
      fapps (ms.getD j pempty) (ihArgs node.a.family.ref g (ctorFieldsOf (famDataOf node.a) j) xs) ∈
        Ed (mkM P μ) (fapps mo (is ++ [z])) →
      g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z])))
    (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4})
    (hl : idx.length = node.a.family.indices.length) (hidx : ∀ e, e ∈ idx → occursConst node.a.family.ref e = false)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const node.a.family.ref (canonL node.a.family.member.arity))
        (policyParameterLocals node.a.family.parameters.length ys.length ++ idx)))) :
    g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x])) := by
  have hargs := recArgs_free node.a.family.ref node.a.family.parameters.length ys.length hidx
  have hxL : x ∈ Ed (mkM P (tabLim P μ (nodeFam node))) (den (mkM P (tabLim P μ (nodeFam node))) (σOf vs)
      (push ys (push ps ρ0)) (foldApps (.const node.a.family.ref (canonL node.a.family.member.arity))
        (policyParameterLocals node.a.family.parameters.length ys.length ++ idx))) :=
    ed_lim_of_self D hlim vs hvs _ hargs hx
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ (nodeFam node) (σOf vs) (push ys (push ps ρ0))
    (policyParameterLocals node.a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (ed_rec_lim_fit P μ (nodeFam node)
      node.a.family.member.arity D.RG.bounded D.RG.famFree (σOf vs) _ _ hargs hfit) hxL)
    have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
    rw [hpsl] at e
    unfold RecFits at hfit
    rw [e] at hfit hn
    exact stage_of_fibD P μ node.a g vs ps mo hpsl n
      (rec_stageDB D hlim hBfd vs hvs hag hctorμ ps mo ms hps hpsl hmo hms g hclose n) _ x hfit hn
  · exact absurd (mem_congr_right (ed_rec_lim_nofit P μ (nodeFam node) node.a.family.member.arity
      D.RG.bounded D.RG.famFree (σOf vs) _ _ hargs
      (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hxL) PSet.not_mem_pempty

/-- The minor obligation of `recVal_mem_gen` for a group with δ-hidden
fields, bounded: `minor_ok_groupD` verbatim with the bounded reads. -/
theorem minor_ok_groupDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps)
    (hpsl : ps.length = node.a.family.parameters.length) (hisl : is.length = node.a.family.indices.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType node.a.family node.a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) node.a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hisfit : TelFits (mkM P μ) (σOf vs) node.a.family.indices (push ps ρ0) is)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = node.a.family.indices.length → TelFits (mkM P μ) (σOf vs) node.a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) →
      CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors (push ps ρ0) is j xs →
      Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs) z →
      fapps (ms.getD j pempty) (ihArgs node.a.family.ref g (ctorFieldsOf (famDataOf node.a) j) xs) ∈
        Ed (mkM P μ) (fapps mo (is ++ [z])) →
      g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z])))
    (j : Nat) (xs : List PSet.{4}) (hcf : CtorFits (mkM P μ) (σOf vs) (famDataOf node.a).ctors
      (push ps ρ0) is j xs) :
    fapps (ms.getD j pempty) (ihArgs (famDataOf node.a).fref g (ctorFieldsOf (famDataOf node.a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [ctorV (mkM P μ) (σOf vs) (famDataOf node.a) j xs])) := by
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (famDataOf node.a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < node.a.constructors.length := by rwa [famDataOf_ctors_length] at hjk'
  have hcc : c = ((node.a.constructorViews ⟨j, hjk⟩).fields, (node.a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor node.a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  -- the fitting fields fit the normalized telescope, at the final table
  obtain ⟨c', hc', hagj, _⟩ := (hag ps hps).get hc
  have hcc' : c' = ((node.a.constructorViews ⟨j, hjk⟩).fields.map
      (normField node.E0 (node.h14.fuelAt ⟨j, hjk⟩) node.a.family.ref),
      (node.a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := normFamData_ctor node.a node.h14.fuelAt ⟨j, hjk⟩
    rw [hc'] at this; exact Option.some.inj this
  rw [hcc, hcc'] at hagj
  have hxs' := (telFits_iff_of_agree _ _ hagj xs).mp hxs
  have hfo' : ctorFieldsOf (normFamData node.a node.h14.fuelAt) j =
      (node.a.constructorViews ⟨j, hjk⟩).fields.map (normField node.E0 (node.h14.fuelAt ⟨j, hjk⟩)
        node.a.family.ref) :=
    ctorFieldsOf_of_get (normFamData_ctor node.a node.h14.fuelAt ⟨j, hjk⟩)
  refine minor_ok_recD node.a vs D.RG.hcl node.h14.fuelAt node.h14.shapesAt D.RG.shapes
    (famμ_of_limDB D hlim hBfd vs hvs) hctorμ ps mo ms is hpsl hisl hmo hms hisfit j xs hcf _ ?_
  rw [hfo']
  exact ihOkF_walk (mkM P μ) (mkM P μ) (σOf vs) node.a.family.ref node.a.family.member.arity
    node.a.family.parameters.length node.a.family.indices.length mo _ ps (fun ys idx x hl hidx hx =>
      rec_fields_okDB D hlim hBfd vs hvs hag hctorμ ps mo ms hps hpsl hmo hms g hclose ys idx x hl hidx hx)
    _ [] xs (D.RG.fields ⟨j, hjk⟩) hxs'

/-- **The recursor of a recursive `Type` group with δ-hidden fields is an
element of its type**, bounded: `recVal_mem_recD` verbatim with the bounded
reads. -/
theorem recVal_mem_recDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (hType : evalTotal (σOf vs) node.a.family.resultLevel ≠ 0) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf node.a)) ρ0 rm.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 rm.mtype) := by
  refine recVal_mem_gen rfl node.a vs (famμ_of_limDB D hlim hBfd vs hvs) (fun h0 => absurd h0 hType)
    (fun h0 => absurd h0 hType)
    (fun _ _ j xs hcf => ihChildL_famDataOf_shapes node.a D.RG hcf (dataVal j xs))
    (recCore (mkM P μ) (famDataOf node.a)) (fun _ _ _ => rfl) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_groupDB D hlim hBfd vs hvs hag hctorμ ps mo ms is hps hpsl hisl hmo hms hisfit _ ?_ j xs hcf
  intro n is' z j' xs' _ _ _ hcf' hcv hm
  rcases id hcf' with ⟨c, hc, hxs, _⟩
  have hjk' : j' < (famDataOf node.a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hzd : Equiv z (dataVal j' xs') := by
    refine hcv.symm.trans ?_
    unfold ctorV PSet.cond
    dsimp only [mkM]
    cases P.dec (evalTotal (σOf vs) (famDataOf node.a).resLevel = 0) with
    | isTrue h => exact absurd h hType
    | isFalse _ => exact Equiv.rfl
  have hlen : xs'.length = nfOf (famDataOf node.a) j' := by unfold nfOf; rw [hc]; exact hxs.length
  have hch := ihChildL_famDataOf_shapes node.a D.RG hcf' (dataVal j' xs')
  exact mem_congr_left (recCore_data _ _ ms hzd hjk' hlen
    (ihChildL_congr' hzd.symm _ _ hch)).symm hm

/-- **The recursor of a recursive `Prop` group with δ-hidden fields
eliminating into `Prop` is an element of its type**, bounded:
`recVal_mem_recPD` verbatim with the bounded reads. -/
theorem recVal_mem_recPDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hag : AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs)
    (hctorμ : ∀ i : Fin node.a.constructors.length,
      Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (node.a.constructorViews i).fields.length) ρ0
          (node.a.constructors[i.val]).mtype))
    (hProp : evalTotal (σOf vs) node.a.family.resultLevel = 0) (hpol : node.a.policy = .propOnly) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf node.a)) ρ0 rm.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 rm.mtype) := by
  refine recVal_mem_gen rfl node.a vs (famμ_of_limDB D hlim hBfd vs hvs)
    (fun _ hp => by rw [hpol] at hp; cases hp) (fun _ hp => by rw [hpol] at hp; cases hp)
    (fun _ _ j xs hcf => ihChildL_famDataOf_shapes node.a D.RG hcf (dataVal j xs))
    (fun _ _ => pempty) (fun h0 => absurd hProp h0) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_groupDB D hlim hBfd vs hvs hag hctorμ ps mo ms is hps hpsl hisl hmo hms hisfit _ ?_ j xs hcf
  intro n is' z j' xs' hl' hisfit' hz _ _ hm
  have hargs : ∀ e, e ∈ policyLocals (ps.length + is'.length) → occursConst node.a.family.ref e = false := by
    intro e he
    unfold policyLocals at he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    rfl
  have hden : (policyLocals (ps.length + is'.length)).map (den (mkM P μ) (σOf vs) (push is' (push ps ρ0))) =
      ps ++ is' := by
    rw [show push is' (push ps ρ0) = push (ps ++ is') ρ0 from (push_append ps is' ρ0).symm,
      show ps.length + is'.length = (ps ++ is').length by simp only [List.length_append], den_policyLocals]
  have hfit : RecFits P μ (nodeFam node) (σOf vs) (push is' (push ps ρ0))
      (policyLocals (ps.length + is'.length)) := by
    unfold RecFits
    rw [hden]
    exact TelFits.append hps hisfit'
  have hzL : z ∈ Ed (mkM P (tabLim P μ (nodeFam node))) (den (mkM P (tabLim P μ (nodeFam node))) (σOf vs)
      (push is' (push ps ρ0)) (foldApps (.const node.a.family.ref (canonL node.a.family.member.arity))
        (policyLocals (ps.length + is'.length)))) := by
    refine mem_congr_right (ed_rec_lim_fit P μ (nodeFam node) node.a.family.member.arity D.RG.bounded
      D.RG.famFree (σOf vs) _ _ hargs hfit).symm (mem_iUnionN.mpr ⟨n, ?_⟩)
    rw [hden]
    exact hz
  have hzm : z ∈ Ed (mkM P μ) (fapps (μ node.a.family.ref ((policyFamilyLevels node.a.family).map
      (evalTotal (σOf vs)))) (ps ++ is')) := by
    have h1 := ed_self_of_lim D hlim vs hvs _ hargs hzL
    have h2 := Fapp_den (mkM P μ) (σOf vs) (nodeFam node).fref (canonL node.a.family.member.arity) ps is' ρ0
    rw [h2] at h1
    exact h1
  have hy := motive_prop_elem rfl node.a vs ps mo is' z hpsl hl' hpol hmo hisfit' hzm _ hm
  exact mem_congr_left hy hm

end BRec

/-! ## §4 constructor soundness at its own bound -/

/-- `ctor_member_sound` with the family's value needed only at instances
within the constructor's own bound `K c` — the only instance the constructor
value reads is its own (`ctorVal_mem`, at `ls.map (evalTotal σ)`, within
`K c` by `hl`). -/
theorem ctor_member_soundB (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {c : Nat}
    {cm : CheckedMember} (fd : FamData) (j : Nat) (cps fs ri : List (Expr Nat))
    (hj : fd.ctors[j]? = some (fs, ri)) (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hst : cm.mtype = policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range cm.arity).map Level.param))
      (policyParameterLocals cps.length fs.length ++ ri)))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 cm.mtype = cm.mtype)
    (hlvl : exprLevelsBounded cm.arity cm.mtype = true) (hbody : cm.body = none)
    (hF : ∀ vs, Equiv (μ c vs)
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 cm.mtype))
    (hfam : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) → Equiv (μ fd.fref vs)
      (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) fd) (fun _ => pempty) (famType fd)))
    (htyp : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      ∀ zs, TelFits (mkM P μ) (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits (mkM P μ) (σOf vs) cps ρ0 ps →
      TelFits (mkM P μ) (σOf vs) fs (push ps ρ0) xs →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    MemberSound P μ K c cm := by
  intro σ ls ρ hlen hl
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvl : (ls.map (evalTotal σ)).length = cm.arity := by rw [List.length_map, hlen]
  have hbd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K c := by
    intro v hv
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
    exact hl l hl'
  rw [den_inst_canon (mkM P μ) σ ls ρ cm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hF _).symm ?_
  have hnf : nfOf fd j = fs.length := by unfold nfOf; rw [hj]
  rw [hnf, hst]
  have hst' : (List.range cm.arity).map Level.param =
      (List.range (ls.map (evalTotal σ)).length).map Level.param := by rw [hvl]
  rw [hst']
  exact ctorVal_mem rfl (ls.map (evalTotal σ)) fd j cps fs ri hj hnp hq (hfam _ hvl hbd)
    (htyp _ hvl hbd) (hsmall _ hvl hbd)

/-! ## §5 the order on the bounds: `CtorsBelowRec`

The bounded chain reads the family's entry only at instances within `K rr`
(`GroupFaithB.famB`, `famB_raw`). The constructor's `MemberSound` at `ls`
reads the family at `ls.map (evalTotal σ)`, bounded by `K c`. The join is
`K c ≤ K rr`: every constructor's bound at or below the recursor's — the
converse of the landed `RecBelowCtors`. A finite check; together with it
the constructors and the recursor share the recursor's bound. -/

/-- **Every constructor's instance bound at or below the recursor's.** -/
def CtorsBelowRec (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ i : Fin node.a.constructors.length, K (f + 1 + i.val) ≤ K rr

/-- The finite check: every index `i < n` has `K (f + 1 + i) ≤ K rr`. -/
def ctorsBelowRecB (K : Nat → Nat) (f rr n : Nat) : Bool :=
  (List.range n).all (fun i => decide (K (f + 1 + i) ≤ K rr))

theorem ctorsBelowRecB_true {K : Nat → Nat} {f rr n : Nat} (h : ctorsBelowRecB K f rr n = true) :
    ∀ i, i < n → K (f + 1 + i) ≤ K rr := by
  intro i hi
  have h1 := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  exact of_decide_eq_true h1

theorem ctorsBelowRecB_eq_true {K : Nat → Nat} {f rr n : Nat}
    (h : ∀ i, i < n → K (f + 1 + i) ≤ K rr) : ctorsBelowRecB K f rr n = true :=
  List.all_eq_true.mpr fun i hi => decide_eq_true (h i (List.mem_range.mp hi))

/-- `CtorsBelowRec` is decidable through `ctorsBelowRecB`: the constructor
refs are `f + 1 + i` for `i < node.a.constructors.length`, and the walk
gives `ctors.length = node.a.constructors.length`. -/
def ctorsBelowRec_dec (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Decidable (CtorsBelowRec K node) :=
  if h : ctorsBelowRecB K f rr node.a.constructors.length then
    .isTrue fun i => ctorsBelowRecB_true h i.val i.isLt
  else
    .isFalse fun hc => h (ctorsBelowRecB_eq_true fun i hi => hc ⟨i, hi⟩)

/-! ## §6 the group step in the raw roles

`gInv_groupD` verbatim with `GroupFaithB` from stage 1 (`groupFaithB_raw`),
the bounded chain for the recursor, `ctor_member_soundB` for the
constructors, and `walk_sound` (the raw walk) — under `hpar` (the
constructor view's parameter prefix is the family's), the `Prop`-corner
clause, and `CtorsBelowRec`. -/

/-- **The step of a group in the raw roles, bounded.** -/
theorem gInv_groupRawD (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hsh : ∀ node : RecNode E E' f rr rm, NoFunRec node)
    (hpar : ∀ node : RecNode E E' f rr rm, ∀ i : Fin node.a.constructors.length,
      (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hprop : ∀ node : RecNode E E' f rr rm, UniformProp node.a.family.resultLevel →
      node.a.policy = .anySort → ∀ i : Fin node.a.constructors.length,
      (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
      (∀ k, k < (node.a.constructorViews i).fields.length →
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
          (node.a.constructorViews i).resultIndices = none))
    (hCB : ∀ node : RecNode E E' f rr rm, CtorsBelowRec K node)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (IH : GInv P K hE) :
    ∀ ctx : Nat → Role,
      (∀ r, Dom E' r → ctx r = envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
      ∀ μ, FaithfulR P μ ctx E' →
      AllSound P μ K E' ∧ ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) →
        ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
  obtain ⟨hBG, hB1, hWB, hB3⟩ := hB
  obtain ⟨_, hDG⟩ := hD
  have hWR : WalkRec hmem := walkRec_of_group hmem
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  intro ctx hctx μ hF
  obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtx hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr (envCtx hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtx_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : FaithfulR P μ ctx E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH ctx hctxE μ hFE
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := PSet.groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  -- the family's entry is the raw chain's limit, at every instance
  have hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
    have h := hF f fm hf' vs
    rw [hctxG f (dom_of_members hf'), groupRoles_at_f] at h
    rw [node.fam]
    exact h
  have hpfF : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have := groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at this
    unfold Dom at this
    rw [hf0] at this
    exact absurd this (by decide)
  have hopq : ∀ ls, transparentBody node.E0 f ls = none := by
    intro ls
    have hp := node.a.family.present
    rw [node.fam] at hp
    unfold transparentBody
    rw [hp]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have hopq' : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by rw [node.fam]; exact hopq
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]; exact famFreeBodies_node hE hf0 hmem node
  -- the stage data, by the order
  have D : DStage P K node μ :=
    dStage_of hE hfam hctors hrec hmem node (hsh node) (hpar node) hBG (fun i => hDG node i) IH ctx hctxE μ hFE hlim
  have hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity := famBounded_node node hTF
  -- the family's soundness in the raw roles, at every instance
  have hfmS : MemberSound P μ K f fm :=
    fam_member_sound_raw hE hfam hctors hrec hmem node μ hlim
  -- the constructor scope at the table
  have hES_S : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
    intro σ n
    refine envSound_of P hSsub ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.2 E' hsubE r m h hk
  have hbodies_S : ∀ σ, BodiesOK (extendEnv E f fm) σ K := fun σ =>
    bodiesOK_of_envWfT K hE hBG (fun r m h => members_extend_preserved hf0 r m h) (fun r m hm h0 => by
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at hm; cases hm; exact hbf
      · rw [members_extend_ne E f fm r hr] at hm; rw [hm] at h0; cases h0) σ
  have hwhnf_S : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel (extendEnv E f fm) fuel e :=
    whnfFuel_eq_along hmem node.base (node_sub' node) (fun r m h => members_extend_preserved hf0 r m h) hSsub
  -- the transfer at instances within the recursor's bound
  have hagR0 : ∀ vs, vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
      AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs := fun vs hlen hvs => D.agree vs hvs hlen
  -- a recursor instance carries one more level under `anySort`: transport from the family's instance
  have hagR : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs :=
    fun vs hvs =>
    agreeAt_levels P μ node.a _ vs (σOf_policyFamilyLevels_agree node.a.family vs) hBfd
      (nodeFam_bounded node hTF (node_bodies_levelsBounded0 hE hmem node K hBG))
      (hagR0 _ (famLevels_length node.a.family vs) (famLevels_le node.a.family hvs))
  have hG : GroupFaithB P μ K fm node := groupFaithB_raw hmem hL hrr node hF hctxG hTF D
  -- under large elimination of a `Prop` family: nonrecursive shapes, proof fields
  have hsh' : ∀ (i : Fin node.a.constructors.length) fuel shapes, UniformProp node.a.family.resultLevel →
      node.a.policy = .anySort →
      fieldShapesFuel node.E0 fuel f node.a.family.member.arity node.a.family.parameters.length
        node.a.family.indices.length node.a.family.parameters.length (node.a.constructorViews i).fields =
        some shapes →
      ShapesMatch f shapes (node.a.constructorViews i).fields := fun i fuel shapes hU hpol hfs =>
    shapesMatch_of_direct (famFreeBodies_node hE hf0 hmem node) hopq _ 0 _
      (recFieldsDirect_of_free (lsF := []) (np := 0) (nq := 0) _ 0
        (fun T hT => by rw [← node.fam]; exact (hprop node hU hpol i).1 T hT)) shapes hfs
  have hnrec : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref
        node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
        node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
        ∀ s, s ∈ shapes → s = .nonrecursive := by
    intro hU hpol i fuel shapes hfs s hs
    have hnf := (hprop node hU hpol i).1
    rw [node.fam] at hnf hfs
    obtain ⟨_, hm⟩ := hsh' i fuel shapes hU hpol hfs
    obtain ⟨k, hk1, hk2⟩ := List.mem_iff_getElem.mp hs
    have hkF : k < (node.a.constructorViews i).fields.length := by
      rw [← (hsh' i fuel shapes hU hpol hfs).1]; exact hk1
    rcases hm k s _ (by rw [List.getElem?_eq_getElem hk1, hk2]) (List.getElem?_eq_getElem hkF) with
      ⟨h, _⟩ | ⟨_, _, ho⟩
    · exact h
    · rw [hnf _ (List.getElem_mem hkF)] at ho; cases ho
  have hPT : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps,
        TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
        PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0) := by
    intro hU hpol i vs hvs ps hps
    refine propTel_of_typings P μ K vs _ _ (hES_S (σOf vs) node.a.family.member.arity) (fun k => ?_) ps hps
    obtain ⟨l, hl, hd⟩ := hB3 node hU hpol i vs hvs k
    exact ⟨l, hl _, hd⟩
  have hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true := fun i => by
    have h := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at h
    exact h
  -- ι at the group's recursor
  have hIrr : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr :=
    fun Efin hsubF => iota_at_D P hG hsubF hr' hFF hopq' (hsh node) hlvC (fun hU hpol i => by
      obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
      have hmt := derivedMinor_nonrec node.a i fuel shapes (hnrec hU hpol i fuel shapes hfs)
        (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
      rw [hdm] at hmt
      exact ⟨fun T hT => (hprop node hU hpol i).1 T hT, (hprop node hU hpol i).2,
        ⟨_, hmt⟩, hPT hU hpol i⟩)
  -- every recursor of the extended environment
  have hIall : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) →
      ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
    intro Efin hsubF r m h hk
    rcases group_member_cases hmem hL hrr node h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact IHμ.2 Efin (fun r m h => hsubF r m (hsubE r m h)) r m h1 hk
    · rw [hfam] at hk; cases hk
    · exact hIrr Efin hsubF
    · rw [(node.a.constructorViews i).hasClass] at hk; cases hk
  -- the recursor
  have hrmS : MemberSound P μ K rr rm := by
    have hcl := (hTF _ _ hr').1
    have hlvl := (hTF _ _ hr').2.1
    have hrb : rm.body = none :=
      hbody _ _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
    rcases selection_uniform node.a with hU | hT
    · cases hpol : node.a.policy with
      | propOnly =>
          intro σ ls ρ hlen hls
          refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
          rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
          refine mem_congr_left (hG.recur _).symm ?_
          have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
            intro v hv
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
            exact hls l hl
          exact recVal_mem_recPDB D hlim hBfd _ hbnd (hagR _ hbnd) (groupFaithB_ctorAt P hG _) (hU _) hpol
      | anySort =>
          exact rec_member_soundB P hG hcl hlvl hrb (hnrec hU hpol)
            (fun hU' hpol' i => ⟨(hprop node hU' hpol' i).2, hPT hU' hpol' i⟩)
            (fun i T hT => (hprop node hU hpol i).1 T hT)
    · intro σ ls ρ hlen hls
      refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
      rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
      refine mem_congr_left (hG.recur _).symm ?_
      have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact hls l hl
      exact recVal_mem_recDB D hlim hBfd _ hbnd (hagR _ hbnd) (groupFaithB_ctorAt P hG _)
        (Nat.pos_iff_ne_zero.mp (hT _))
  -- the constructors, along the walk
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → Ew.members r = none →
      FieldUniverseAdmitted cv →
      AgreeAt node.a.family.parameters.length Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh h07 hagc hB2w hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' := fun r' m' h =>
      hsubw r' m' (members_extend_preserved hfresh r' m' h)
    -- the member is one of the group's constructors
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
      rcases group_member_cases hmem hL hrr node (groupMembersT_installed hmem hin) with
        h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h1
      · rcases List.mem_cons.mp hin with h2 | h2
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; rw [hfam] at hkC; cases hkC
        · rcases List.mem_append.mp h2 with h3 | h3
          · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
            rw [hL] at hr
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
            have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
            exact ⟨⟨i, hi'⟩, rfl, Option.some.inj ((groupMembersT_installed hmem hin).symm.trans
              (node_ctor_member node ⟨i, hi'⟩))⟩
          · rw [List.mem_singleton] at h3
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3; rw [hrec] at hkC; cases hkC
      · rw [hfam] at hkC; cases hkC
      · rw [hrec] at hkC; cases hkC
      · exact h1
    obtain ⟨i, rfl, rfl⟩ := hctor
    -- the constructor's own view agrees with the recursor's
    have hstO := cv.storedType
    have hstR := (node.a.constructorViews i).storedType
    have hspl := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
      (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (hstO.symm.trans hstR)
    have hcat := hspl.1
    have href : famO.ref = node.a.family.ref := foldApps_const_head hspl.2
    have hfamO : famO.member = fm := by
      have h1 := famO.present
      rw [href, node.fam] at h1
      exact Option.some.inj ((hEw f _ h1).symm.trans hf')
    have hlvO : famO.resultLevel = node.a.family.resultLevel := by
      have e1 := famO.storedType
      have e2 := node.a.family.storedType
      rw [hfamO] at e1
      rw [hfmm] at e2
      have := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) (e1.symm.trans e2)).2
      injection this
    have harO : famO.member.arity = node.a.family.member.arity := by rw [hfamO, hfmm]
    have hES_w : ∀ vs, EnvSound (mkM P μ) (σOf vs) K Ew famO.member.arity := fun vs =>
      envSound_of P hEw hAw (fun r m h hk => hIall E' (fun _ _ h => h) r m (hEw r m h) hk) _ _
    refine ctor_member_soundB P (famDataOf node.a) i.val (node.a.constructorViews i).parameters
      (node.a.constructorViews i).fields (node.a.constructorViews i).resultIndices (famDataOf_ctor node.a i)
      (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
      (hTF _ _ (node_ctor_member node i)).1 (hTF _ _ (node_ctor_member node i)).2.1
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) (fun vs => hG.ctor i vs) ?_ ?_ ?_
    · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
      rfl
    · intro vs hvl hbd
      exact famB_raw D hlim vs (fun v hv => Nat.le_trans (hbd v hv) (hCB node i))
        (hvl.trans (node.a.constructorViews i).arity)
    · intro vs hvl hbd zs hz
      obtain ⟨u, d, hd⟩ := hB1 node i vs (hvl.trans (node.a.constructorViews i).arity) hbd
      have hsd := hsound_ty (P.good _ rfl) (hES_S (σOf vs) _) d hd
      have := tel_end_type' _ _ d (node.a.constructorViews i).storedType hsd ρ0 zs trivial hz
      have e : (List.range vs.length).map Level.param = policyFamilyLevels node.a.family := by
        rw [hvl, (node.a.constructorViews i).arity]; rfl
      rw [e]
      exact this
    · intro vs hvl hbd h0 ps xs hps hxs
      have hvlO : vs.length = famO.member.arity := by rw [harO, ← (node.a.constructorViews i).arity]; exact hvl
      have hB2v := hB2w vs hvlO hbd
      have hD : RefsIn (Dom Ew) (cv.parameters ++ cv.fields) := fun e he r hr => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
        obtain ⟨d, _⟩ := hB2v ⟨k, hk⟩
        exact hasTyT_denRefs d r hr
      have h0O : evalTotal (σOf vs) famO.resultLevel ≠ 0 := by rw [hlvO]; exact h0
      -- the level bound on the recursor view's fields: own fields by the own admission, positions the own
      -- view reads as parameters by the level agreement and the recursor's admission
      have hlevF : ∀ (j : Fin (node.a.constructorViews i).fields.length)
          (hk : (node.a.constructorViews i).parameters.length + j.val < (cv.parameters ++ cv.fields).length),
          evalTotal (σOf vs) (cv.domainsTyped.levels ⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩) ≤
            evalTotal (σOf vs) node.a.family.resultLevel := by
        intro j hk
        have hlenN : (node.a.constructorViews i).parameters.length = node.a.family.parameters.length :=
          (node.a.constructorViews i).parameterCount
        rcases Nat.lt_or_ge ((node.a.constructorViews i).parameters.length + j.val) cv.parameters.length with
          hpar | hfld
        · rcases hagc _ hk (by omega) hpar with hp | hle
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
        · have hj : (kk : Nat) → kk = (node.a.constructorViews i).parameters.length + j.val →
              kk - cv.parameters.length < cv.fields.length := fun kk hkk => by
            simp only [List.length_append] at hk; omega
          let j' : Fin cv.fields.length :=
            ⟨(node.a.constructorViews i).parameters.length + j.val - cv.parameters.length, hj _ rfl⟩
          have hfi : (⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩ :
              Fin (cv.parameters ++ cv.fields).length) = cv.fieldIndex j' :=
            Fin.ext (by
              show (node.a.constructorViews i).parameters.length + j.val =
                cv.parameters.length + ((node.a.constructorViews i).parameters.length + j.val - cv.parameters.length)
              omega)
          rw [hfi]
          rcases h07 j' with hp | ⟨_, hle⟩
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
      exact field_small_gen P μ μ K (Epre := Ew) famO.member.arity (cv.parameters ++ cv.fields)
        (node.a.constructorViews i).parameters (node.a.constructorViews i).fields hcat.symm
        cv.domainsTyped.levels node.a.family.resultLevel vs (hES_w vs) hB2v (fun _ _ _ => rfl) hD h0 hlevF
        ps xs hps hxs
  have hAll : AllSound P μ K E' := by
    refine walk_sound P μ K ((f, fm) :: ctors ++ [(rr, rm)]) (AgreeAt node.a.family.parameters.length) ?_ ?_
      hfmS hrmS hcS hmem (fun _ h => h) (fun _ _ h => h) hWR (hAg node) hWB IHμ.1
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; subst h; rw [hrec] at hk; cases hk
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · subst h; rw [hfam] at hk; cases hk
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; exact h
  exact ⟨hAll, fun Efin hsubF r m h hk => hIall Efin hsubF r m h hk⟩

/-! ## §7 `StepDG` under the checked side condition

swe-audit-m3's stage-2 verdict (`baabba797b..fbb140c03b` → REFUSE) found
that the previous shape of this premise — the triple below demanded at
**every** `RecNode` of **every** group — is uninhabitable at every `K`: at
the admitted `accP` group (`RcicAccPiEnv`) `resultLevel = .zero` and
`policy = .anySort` hold while the field `paFieldDom` mentions the family,
so the `Prop` corner's occurs-free conjunct is false there. But `accP`'s
field analyzes `.recursive 2` — `PendA` — a node `StepDG`'s own domain
already excludes; the route never runs there. The demand was the vacuity,
not the check. The triple is therefore scoped to `StepDG`'s domain:
demanded at a group only under `(∀ node, ¬ PendA) ∧ (∃ node, PendD)` —
the group's own antecedent — which is exactly where `gInv_groupRawD`
consumes it. -/

/-- **The side condition at one node**: the three premises
`gInv_groupRawD` consumes — the constructor views' parameter prefix is
the family's (`hpar`), the `Prop`/`anySort` corner (family-free,
unrevealed fields; vacuous unless `UniformProp` and `.anySort` both
hold), and `CtorsBelowRec`. Packaged as one `Prop` so the checked face
(`RcicF3StepDGCheck`) can decide it piecewise. -/
def StepDGSide (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  (∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters =
      node.a.family.parameters) ∧
  (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
    ∀ i : Fin node.a.constructors.length,
      (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
      (∀ k, k < (node.a.constructorViews i).fields.length →
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
          (node.a.constructorViews i).resultIndices = none)) ∧
  CtorsBelowRec K node

/-- **The side condition at a group, domain-guarded**: demanded only where
`StepDG`'s own antecedent holds — no `PendA` node and a `PendD` node.
The guard is what kills m3's vacuity: at a `PendA` group (e.g. `accP`)
nothing is asked, and at a `PendD`-free group the D route never runs. -/
def StepDGSideG (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    {S E1 : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (_hmem : GroupMembersT S E1 ms E') : Prop :=
  (∀ node : RecNode E E' f rr rm, ¬ PendA node) →
    (∃ node : RecNode E E' f rr rm, PendD node) →
    ∀ node : RecNode E E' f rr rm, StepDGSide K node

/-- **The step at one group under the side condition** — the repair
shape: `StepDGSide` is a premise of *this* group only, so the premise
class is inhabited wherever the checks pass at the group's nodes
(`RcicF3StepDGCheck` runs them at the δ fixture). The `PendD` witness
is taken but not used — the route needs no use of it, only the domain
it marks. -/
theorem stepDG_at (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hside : ∀ node : RecNode E E' f rr rm, StepDGSide K node)
    (hAn : ∀ node : RecNode E E' f rr rm, ¬ PendA node)
    (_hDp : ∃ node : RecNode E E' f rr rm, PendD node) :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun hAg hB hD IH => gInv_groupRawD P K hE hfam hctors hrec hmem
    (fun node => noFunRec_of_not_pendA (hAn node))
    (fun node => (hside node).1)
    (fun node => (hside node).2.1)
    (fun node => (hside node).2.2)
    hAg hB hD IH

/-- **`StepDG` under the domain-guarded side condition.** Soundness is
unconditional: wherever every in-domain group pays `StepDGSide`, `StepDG`
holds. The side condition is per-node decidable and refuses by name
(`RcicF3StepDGCheck`); its inhabitation on an environment is a premise
here, not a claim. -/
theorem stepDG_under (P : Premises4) (K : Nat → Nat)
    (hside : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
      StepDGSideG K (E := E) (E' := E') (f := f) (rr := rr) (rm := rm) hmem) : StepDG P K :=
  fun {E} {E'} {f} {rr} {fm} {rm} {ctors} hE hfam hctors hrec hmem hAn hDp hAg hB hD IH =>
    stepDG_at P K hE hfam hctors hrec hmem
      (fun node => hside hE hfam hctors hrec hmem hAn hDp node) hAn hDp hAg hB hD IH

end Rcic.F3.StepDGOrder
