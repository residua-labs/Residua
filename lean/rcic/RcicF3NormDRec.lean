import rcic.RcicF3NormDStage

/-!
# The bounded data/PropOnly recursor chain at normalized family values

The existing bounded D chain is reused with the actual normalized finite
limit equation. The family equation is used only at the full canonical
instances read by the original normalized direct-recursive fields. Its
connection to the raw constructor value follows from the produced DStage
agreement at bounded instances, not an all-instance raw-limit comparison.

This kernel keeps the original stored recursor type, complete parameter
and index data, and the separate motive universe. Its explicit normalized
family equation is produced by the finite-family adapter. The typed
Prop/anySort branch is a separate indexed-evaluation producer.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDRec
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder

section
variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat}
  {rm : CheckedMember}

/-- The current family is the raw constructor value at bounded instances,
from its normalized limit and the actual stage comparison. -/
theorem famB_normal {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}} (D : DStage P K node μ)
    (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs))
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) (hlen : vs.length = node.a.family.member.arity) :
    Equiv (μ node.a.family.ref vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  have e1 : Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs) :=
    hlim vs
  have e2 := (famLim_fix P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree D.RG.cls
    (RecGroupD.ri node.a D.RG) vs).symm
  have hX : Equiv (famLim P μ (nodeFam node) ((canonL node.a.family.member.arity).map (evalTotal (σOf vs))))
      (μ (nodeFam node).fref ((canonL node.a.family.member.arity).map (evalTotal (σOf vs)))) := by
    rw [canon_eq_of_length hlen]
    exact e1.symm
  have hsm₁ := fun ρ args hargs hl =>
    small_rec_lim P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree (σOf vs) ρ args hargs hl
  have hsm₂ := fun ρ args hargs hl =>
    small_recApp_of_equiv P μ (nodeFam node) node.a.family.member.arity _ _ (σOf vs) _ hX.symm ρ args hargs
      (hsm₁ ρ args hargs hl)
  have hT : ∀ r, r ≠ (nodeFam node).fref → ∀ ls,
      Equiv (tabLim P μ (nodeFam node) r ls) (upd μ (nodeFam node).fref (μ (nodeFam node).fref) r ls) := by
    intro r hr ls
    have e1 : tabLim P μ (nodeFam node) r ls = μ r ls := upd_ne μ _ _ hr ls
    have e2 : upd μ (nodeFam node).fref (μ (nodeFam node).fref) r ls = μ r ls := upd_ne μ _ _ hr ls
    rw [e1, e2]
    exact Equiv.rfl
  have e3 := piLam_tablesOn P hT (σOf vs) (famEnd_resp _ W4 _ _)
    (famEnd_upd_equiv P μ (nodeFam node) node.a.family.member.arity D.RG.cls (RecGroupD.ri node.a D.RG)
      _ _ (σOf vs) hX hsm₁ hsm₂) _ (famType_refs_ne (nodeFam node) D.RG.famFree) ρ0
  have hμ : upd μ (nodeFam node).fref (μ (nodeFam node).fref) = μ := by
    funext r ls
    by_cases h : r = (nodeFam node).fref
    · subst h; exact upd_eq μ _ _ ls
    · exact upd_ne μ _ _ h ls
  rw [hμ] at e3
  have e4 := (famVal_agree (mkM P μ) W4 (σOf vs) (famDataOf node.a) (nodeFam node).ctors (D.agree vs hvs hlen)).symm
  exact e1.trans (e2.trans (e3.trans e4))

end

section BRec

variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat}
  {rm : CheckedMember} {node : RecNode E E' f rr rm}
  {μ : Nat → List Nat → PSet.{4}}
  (D : DStage P K node μ)
  (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs))

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

/-- The supplied normalized family equation is retained at each bounded
instance; no all-instance raw-limit equation is required. -/
theorem limB (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hlen : vs.length = node.a.family.member.arity) :
    Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs) :=
  hlim vs

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

/-- The family's value at its own instance, bounded: `famB_normal` at
`policyFamilyLevels` (within `K rr` by `famLevels_le`), then
`famVal_levels` to `σOf vs`. -/
theorem famμ_of_limDB (hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) :
    Equiv (μ node.a.family.ref ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) :=
  (famB_normal D hlim _ (famLevels_le node.a.family hvs) (famLevels_length node.a.family vs)).trans
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

/-- The minor obligation uses the normalized family limit together with
the bounded comparison to original constructor fields. -/
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

/-- The original stored data recursor is typed using the normalized limit
at canonical instances. The bounded raw-family equation is produced by
`famB_normal`, retaining the complete motive valuation. -/
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

/-- The stored PropOnly recursor uses the normalized limit and the bounded
raw-family equation. Its literal endpoint remains `recEnd`; the original
parameter, index and minor inputs are retained. -/
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

end Rcic.F3.PSet.NormDRec
