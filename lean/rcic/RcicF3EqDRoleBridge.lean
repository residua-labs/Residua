import rcic.RcicF3TierGroup

/-!
# F3 D role bridge at the δ fixture — `DrRoleBridge`, proved

`closure_claim = 0`.

The item (cc INBOX 20261027T084517Z): produce `StepDG P K` (∀ P K), and close
`DrRoleBridge P K := GInvD P K drEnvWfT → GInv P K drEnvWfT` — the
fixture-scoped remainder named by `RcicF3TierGroup.stepDAt_drEnv_iff`. This
module **proves the bridge** (§6), which discharges the D group step at the
δ fixture unconditionally (`stepDAt_drEnv_uncond`): the fixture arm of
`StepDG` is no longer owed.

## Why the bridge is true: every iterate is empty

`GInv` and `GInvD` differ only in the family role at the group: `envCtx`
installs the family at the limit of the **raw** data's iterates (`famDataOf`,
field `Id F`), `envCtxD` at the **normalized** ones (`nodeFam`, field `F`).
At `drEnv` the raw field's denotation is not the `Id` entry itself but its
**application**: `den (Id F) = fapp (μ 0 []) (stage)` — the table entry of
`Id`, applied to the stage value. Faithfulness at `Id` (`μ 0 [] ≈
lamVal … (fun x => x)`, §2) makes that application the identity *on codes of
the universe* (β through `beta_val`; every stage value is a family value,
hence a code by `famVal_mem`), while the normalized field reads the stage
value directly. Either way an element of the stage-`n+1` fibre needs a field
element of the stage-`n` fibre (the family value *is* the previous stage's
`famEnd`; `ed_famEnd` transports the family value's `Ed` to the previous
stage's `El`), and the stage-`0` fibre's field set is `Ed (tyv pempty)` —
empty. So every iterate is empty at every level assignment (§3), both limits
are `≈`-equal (§4), and the constructor/recursor readings are equal outright
(§5, `RecDataAgree`'s content minus its policy field, which only the
unreachable Prop branch reads). Faithfulness therefore transfers from
`envCtx` to `envCtxD` member by member — and `GInvD`'s conclusion
(`AllSound` + `IotaAt`) is role-free, so `GInvD → GInv` at `drEnvWfT`.

The stage descent is well-founded by construction: an impossible element
chain would have to live inside one finite stage index, and each stage's
fields point strictly into the previous one; no `TransGen` descent on the
foundation relation is needed.

## The honest boundary (what this does NOT give)

`StepDG` beyond the fixture. Two routes to the general group step are
measured:

* the **node-granular** route (the `G` fold's `NodeFieldRow` input) is
  refuted at this very fixture — `dr_not_nodeFieldRow` (m3's refutation, on
  record);
* the **group-granular** route through the D model needs the raw/normalized
  family limits to agree. The landed fixed-point machinery
  (`famLim_fix`/`famChain_iter`) controls only constructor lists whose fields
  are family-free or literal family applications — the δ-hidden field is
  neither (the fixture is outside `ClassG`, `drEnvWfT_not_classG`), so the
  raw chain is outside every landed fixed-point theorem. The general
  producer therefore owes a genuinely new model theorem (the raw chain's
  control); the weakest checked side condition under which the general step
  follows is stated in §7 (`RoleBridgeEnv`), and §6 is exactly its fixture
  instance.

Axioms of every sealed declaration ⊆ {`propext`, `Quot.sound`}; all case splits
on `Premises4.dec`.
-/

set_option autoImplicit false

namespace Rcic.F3.TierGroup

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet

/-! ## §1 the fixture's two family data -/

/-- The raw family data of the fixture's group, as `envCtx` installs it
(read off the admission `drGroupAdmitted` directly — no node needed). -/
def drRawFam : FamData := famDataOf drGroupAdmitted

/-- The raw data's shape: family `F` at `1`, no parameters or indices, level
`1`, one constructor `mk` with the single δ-hidden field. -/
theorem drRawFam_shape :
    drRawFam.fref = 1 ∧ drRawFam.params = [] ∧ drRawFam.indices = [] ∧
      drRawFam.resLevel = .succ .zero ∧ drRawFam.ctors = [([drField], [])] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have h0 : drRawFam.ctors[0]? = some ([drField], []) := rfl
  have hlen' : drRawFam.ctors.length = 1 := rfl
  exact List.ext_get (by simp [hlen']) (by
    rintro i _ hi2
    have : i = 0 := Nat.lt_one_iff.mp (by simpa [hlen'] using hi2)
    subst this
    exact (List.getElem?_eq_some_iff.mp h0).2)

/-- The two fields the bridge treats uniformly: the raw δ-hidden field and
its normal form. -/
theorem drField_norm_cases {E : ResolvedEnv} (fuel : Nat) (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember) :
    normField E fuel 1 drField = .const 1 [] ∨ normField E fuel 1 drField = drField := by
  have htb0 : transparentBody E 0 [] = some (.lam (.sort (.succ .zero)) (.bvar 0)) := by
    rw [transparentBody, h0]
    rfl
  have htb1 : transparentBody E 1 [] = none := by
    rw [transparentBody, h1]
    rfl
  have h8 : whnfFuel E 8 drField = some (.const 1 []) := by
    simp only [whnfFuel, appsSpine, drField, htb0, htb1, foldApps, instantiate0, instantiate,
      List.nil_append, List.cons_append]
    rfl
  have hocc : occursConst 1 drField = true := by decide
  unfold normField
  rw [if_pos hocc]
  cases hf : whnfFuel E fuel drField with
  | some w =>
      left
      have hw : w = .const 1 [] := by
        rcases Nat.lt_trichotomy fuel 8 with hlt | heq | hgt
        · have h := whnfFuel_mono E (by omega : fuel ≤ 8) hf
          rw [h8] at h
          exact Option.some.inj h.symm
        · rw [heq] at hf; rw [h8] at hf; exact Option.some.inj hf.symm
        · have h := whnfFuel_mono E (by omega : 8 ≤ fuel) h8
          rw [hf] at h
          exact Option.some.inj h
      rw [hw]
      rfl
  | none =>
      right
      rfl

/-- The normalized family data of the fixture's group, as `envCtxD` installs
it (read off the group's recursor node). -/
def drNormFam (node : DrNode) : FamData := nodeFam node

/-- The normalized data's shape: the raw shape with the single field replaced
by its normal form — which is either `F` itself or the field unchanged. The
node's `a.policy` is deliberately **not** pinned: it is free data of the
existential and is provably irrelevant (§5 reads only policy-free
components). -/
theorem drNormFam_shape (node : DrNode) :
    ∃ A : Expr Nat, (A = drField ∨ A = .const 1 []) ∧
      (drNormFam node).fref = drRawFam.fref ∧ (drNormFam node).params = drRawFam.params ∧
      (drNormFam node).indices = drRawFam.indices ∧
      (drNormFam node).resLevel = drRawFam.resLevel ∧ (drNormFam node).ctors = [([A], [])] := by
  obtain ⟨h0, h1⟩ := dr_node_members node
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  have i0 : Fin node.a.constructors.length := ⟨0, by rw [hlen]; exact Nat.zero_lt_one⟩
  have hview : (node.a.constructorViews i0).fields = [drField] := (dr_view node i0).2.2
  have hi0 : (i0 : Nat) = 0 := Nat.lt_one_iff.mp
    (Nat.lt_of_lt_of_le i0.isLt (by rw [hlen]; exact Nat.le_refl 1))
  refine ⟨normField node.E0 (node.h14.fuelAt i0) 1 drField, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases drField_norm_cases _ h0 h1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · show (famDataOf node.a).fref = _
    show node.a.family.ref = _
    rw [node.fam]
    rfl
  · show (famDataOf node.a).params = _
    show node.a.family.parameters = _
    rw [(dr_family node).1]
    rfl
  · show (famDataOf node.a).indices = _
    show node.a.family.indices = _
    rw [(dr_family node).2.1]
    rfl
  · show (famDataOf node.a).resLevel = _
    show node.a.family.resultLevel = _
    rw [(dr_family node).2.2]
    rfl
  · have hlen' : (drNormFam node).ctors.length = 1 := by
      have h1' := normFamData_ctors_length node.a node.h14.fuelAt
      rw [hlen] at h1'
      exact h1'
    obtain ⟨a, hdeq⟩ := List.length_eq_one.mp hlen'
    have h0v : (drNormFam node).ctors[0]? = some a := by
      rw [hdeq]
      rfl
    have hnfv : (drNormFam node).ctors[0]? =
        some ([normField node.E0 (node.h14.fuelAt i0) 1 drField], []) := by
      rw [show (0 : Nat) = ↑i0 from hi0.symm]
      unfold drNormFam nodeFam
      rw [normFamData_ctor node.a node.h14.fuelAt i0, hview, node.fam, (dr_view node i0).2.1]
      rfl
    have ha : a = ([normField node.E0 (node.h14.fuelAt i0) 1 drField], []) :=
      Option.some.inj (h0v.symm.trans hnfv)
    rw [hdeq, ha]

/-! ## §2 the `Id` entry's β lemma -/

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})

/-- The faithful value of the `Id` entry: the polymorphic identity. -/
theorem drIdVal :
    den (mkM P μ) (fun _ => 0) ρ0 (.lam (.sort (.succ .zero)) (.bvar 0)) =
      lamVal (mkM P μ) (tyv (U W4 1)) (fun x => x) := rfl

/-- Faithfulness at `Id` makes its application the identity on codes of the
universe `U W4 1`. -/
theorem drId_fapp (hId : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0)))) (a : PSet.{4}) (ha : a ∈ U W4 1) :
    Equiv (fapp (μ 0 []) a) a := by
  rw [drIdVal] at hId
  have hmem : a ∈ Ed (mkM P μ) (tyv (U W4 1)) :=
    mem_congr_right (ed_tyv (mkM P μ) (U4_dich 1)).symm ha
  exact (fapp_congr hId Equiv.rfl).trans (beta_val (mkM P μ) (fun _ _ h => h) hmem)

/-! ## §3 every iterate of the fixture's families is empty -/

/-- The shape hypothesis the emptiness chain runs on: family `F` at `1`, no
parameters or indices, level `1`, one constructor with a single field that is
either the δ-hidden `Id F` or its normal form `F`. -/
structure DrFamShape (fd : FamData) : Prop where
  fref : fd.fref = 1
  params : fd.params = []
  indices : fd.indices = []
  resLevel : fd.resLevel = .succ .zero
  field : fd.ctors = [([drField], [])] ∨ fd.ctors = [([.const 1 []], [])]

theorem drRawFam_DrFamShape : DrFamShape drRawFam :=
  let ⟨_, _, _, _, hc⟩ := drRawFam_shape
  ⟨rfl, rfl, rfl, rfl, Or.inl hc⟩

theorem drNormFam_DrFamShape (node : DrNode) : DrFamShape (drNormFam node) := by
  obtain ⟨A, hA, hf, hp, hi, hr, hc⟩ := drNormFam_shape node
  obtain ⟨rf, rp, ri, rr, rc⟩ := drRawFam_shape
  refine ⟨by rw [hf, rf], by rw [hp, rp], by rw [hi, ri], by rw [hr, rr], ?_⟩
  rw [hc]
  exact hA.elim (fun h => h ▸ Or.inl rfl) (fun h => h ▸ Or.inr rfl)

variable {fd : FamData} (S : DrFamShape fd)

/-- The family's type is the bare sort (no telescope). -/
theorem drFamType (S : DrFamShape fd) : famType fd = .sort (.succ .zero) := by
  rw [famType, S.params, S.indices, S.resLevel, List.nil_append]
  rfl

/-- An element of the family's `Type` fibre at any table forces a field
element: either in `fapp (μ 0 []) (stage)` (the raw field) or in the stage
value itself (the normalized field). -/
theorem drFibre_field (S : DrFamShape fd) (M : Interp.{4}) (σ : Nat → Nat) (z : PSet.{4})
    (hz : z ∈ El (famEnd M W4 σ fd ρ0)) :
    ∃ x : PSet.{4}, ∃ A : Expr Nat, (A = drField ∨ A = .const 1 []) ∧
      x ∈ Ed M (den M σ ρ0 A) := by
  unfold famEnd at hz
  rw [S.resLevel] at hz
  have hev : evalTotal σ (.succ (.zero : Level)) = 0 + 1 := rfl
  rw [hev] at hz
  rw [cond_neg (Nat.succ_ne_zero 0)] at hz
  rw [S.indices] at hz
  have hshift : shiftρ ([] : List (Expr Nat)).length ρ0 = ρ0 := rfl
  have hlast : lastVals ([] : List (Expr Nat)).length ρ0 = [] := rfl
  rw [hshift, hlast] at hz
  have hz' : z ∈ TypeFib M W4 (0 + 1) σ fd.ctors ρ0 [] :=
    mem_congr_right el_tyv hz
  obtain ⟨j, xs, c, hcx, hcf, _, _⟩ := mem_TypeFib.mp hz'
  obtain ⟨c', hc'x, htel, _⟩ := hcf
  have hj : j = 0 := by
    match j, hcx with
    | 0, _ => rfl
    | j + 1, h => rcases S.field with h' | h' <;> rw [h'] at h <;> simp at h
  subst hj
  have hc1 : c'.1 = [drField] ∨ c'.1 = [.const 1 []] := by
    rcases S.field with h | h <;> rw [h] at hc'x <;>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'x <;> obtain rfl := hc'x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc1 with h | h <;> rw [h] at htel
  · obtain ⟨x, hx⟩ := List.length_eq_one.mp htel.length
    subst hx
    exact ⟨x, drField, Or.inl rfl, htel.1⟩
  · obtain ⟨x, hx⟩ := List.length_eq_one.mp htel.length
    subst hx
    exact ⟨x, .const 1 [], Or.inr rfl, htel.1⟩

section
variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})

/-- The stage tables read `μ` at the base reference `0`. -/
theorem drTabIter_zero_base (S : DrFamShape fd) (k : Nat) : (tabIter P μ fd k) 0 [] = μ 0 [] := by
  show (upd μ fd.fref (famIter P μ fd k)) 0 [] = _
  rw [S.fref]
  rfl

/-- The stage-`0` family entry is the empty type. -/
theorem drTabIter_zero_entry (S : DrFamShape fd) :
    (tabIter P μ fd 0) 1 [] = tyv pempty := by
  show (upd μ fd.fref (famIter P μ fd 0)) 1 [] = _
  rw [S.fref]
  show famZero P μ fd (σOf []) = _
  show piLam (mkM P μ) (σOf []) (fun _ => tyv pempty) ρ0 (famType fd) = _
  rw [drFamType S]
  rfl

/-- The stage-`n+1` family entry is the previous stage's fibre. -/
theorem drTabIter_succ_entry (S : DrFamShape fd) (n : Nat) :
    (tabIter P μ fd (n + 1)) 1 [] =
      famEnd (mkM P (tabIter P μ fd n)) W4 (σOf []) fd ρ0 := by
  show (upd μ fd.fref (famIter P μ fd (n + 1))) 1 [] =
      famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 (σOf []) fd ρ0
  rw [S.fref]
  have hfi : famIter P μ fd (n + 1) [] =
      famVal (mkM P (upd μ 1 (famIter P μ fd n))) W4 (σOf []) fd := by
    show famVal (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 (σOf []) fd = _
    rw [S.fref]
  rw [show (upd μ 1 (famIter P μ fd (n + 1))) 1 [] = famIter P μ fd (n + 1) [] from rfl, hfi]
  show piLam (mkM P (upd μ 1 (famIter P μ fd n))) (σOf [])
      (famEnd (mkM P (upd μ 1 (famIter P μ fd n))) W4 (σOf []) fd) ρ0 (famType fd) = _
  rw [drFamType S]
  rfl

/-- Every stage entry is a code of the universe — the β domain. -/
theorem drTabIter_entry_code (S : DrFamShape fd) (n : Nat) :
    (tabIter P μ fd n) 1 [] ∈ U W4 1 := by
  match n with
  | 0 =>
      rw [drTabIter_zero_entry P μ S]
      exact tyv_pempty_mem_U4 P 1
  | n + 1 =>
      have hmem := famVal_mem P (mkM P (upd μ fd.fref (famIter P μ fd n))) rfl (σOf []) fd ρ0
      rw [drFamType S] at hmem
      have hden : den (mkM P (upd μ fd.fref (famIter P μ fd n))) (σOf []) ρ0
            (.sort (.succ (.zero : Level))) = tyv (U W4 1) := rfl
      rw [hden] at hmem
      rw [ed_mkM P (upd μ fd.fref (famIter P μ fd n)) μ (tyv (U W4 1))] at hmem
      rw [drTabIter_succ_entry P μ S n]
      exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich 1)) hmem


/-- The raw field's set at a stage table transports, through the `Id`
entry's β, to the previous stage's fibre. -/
theorem drFieldRaw_step (S : DrFamShape fd)
    (hId : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0)))) (n : Nat) (σ : Nat → Nat) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (tabIter P μ fd (n + 1)))
      (fapp ((tabIter P μ fd (n + 1)) 0 []) ((tabIter P μ fd (n + 1)) 1 []))) :
    x ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf []) fd ρ0) := by
  have hcode := drTabIter_entry_code P μ S (n + 1)
  rw [drTabIter_zero_base P μ S (n + 1)] at hx
  rw [drTabIter_succ_entry P μ S n] at hx hcode
  have hx'' : x ∈ Ed (mkM P (tabIter P μ fd (n + 1)))
      (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf []) fd ρ0) :=
    mem_congr_right (ed_congr _ (drId_fapp P μ hId _ hcode)) hx
  exact mem_congr_right (ed_famEnd _ _ rfl (σOf []) fd ρ0) hx''

/-- The normalized field's set at a stage table is the previous stage's
fibre's `Ed`. -/
theorem drFieldNorm_step (S : DrFamShape fd) (n : Nat) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (tabIter P μ fd (n + 1))) ((tabIter P μ fd (n + 1)) 1 [])) :
    x ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf []) fd ρ0) := by
  rw [drTabIter_succ_entry P μ S n] at hx
  exact mem_congr_right (ed_famEnd _ _ rfl (σOf []) fd ρ0) hx

end

/-- **Every iterate of a fixture-shaped family is empty**, at every level
assignment. The stage descent: a field element of the stage-`n+1` fibre lies
in the previous stage's fibre; the raw field reaches it through the `Id`
entry's β, the normalized field reads the stage value directly. -/
theorem drIter_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (S : DrFamShape fd)
    (hId : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0)))) :
    ∀ n σ z, ¬ z ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd ρ0) := by
  intro n
  induction n with
  | zero =>
      intro σ z hz
      obtain ⟨x, A, hA, hx⟩ := drFibre_field S _ σ z hz
      rcases hA with rfl | rfl
      · have hx' : x ∈ Ed (mkM P (tabIter P μ fd 0))
          (fapp ((tabIter P μ fd 0) 0 []) ((tabIter P μ fd 0) 1 [])) := hx
        have hcode := drTabIter_entry_code P μ S 0
        rw [drTabIter_zero_base P μ S 0] at hx'
        rw [drTabIter_zero_entry P μ S] at hx' hcode
        have hx'' : x ∈ Ed (mkM P (tabIter P μ fd 0)) (tyv pempty) :=
          mem_congr_right (ed_congr _ (drId_fapp P μ hId _ hcode)) hx'
        exact not_mem_pempty (mem_congr_right (ed_tyv_empty _) hx'')
      · have hx' : x ∈ Ed (mkM P (tabIter P μ fd 0)) ((tabIter P μ fd 0) 1 []) := hx
        rw [drTabIter_zero_entry P μ S] at hx'
        exact not_mem_pempty (mem_congr_right (ed_tyv_empty _) hx')
  | succ n ih =>
      intro σ z hz
      obtain ⟨x, A, hA, hx⟩ := drFibre_field S _ σ z hz
      rcases hA with rfl | rfl
      · have hx' : x ∈ Ed (mkM P (tabIter P μ fd (n + 1)))
          (fapp ((tabIter P μ fd (n + 1)) 0 []) ((tabIter P μ fd (n + 1)) 1 [])) := hx
        exact ih (σOf []) x (drFieldRaw_step P μ S hId n σ x hx')
      · have hx' : x ∈ Ed (mkM P (tabIter P μ fd (n + 1))) ((tabIter P μ fd (n + 1)) 1 []) := hx
        exact ih (σOf []) x (drFieldNorm_step P μ S n x hx')

/-! ## §4 the two limits agree -/

/-- Every fixture-shaped family's limit is the empty type. -/
theorem drFamLim_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (S : DrFamShape fd)
    (hId : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0)))) (vs : List Nat) :
    Equiv (famLim P μ fd vs) (tyv pempty) := by
  have hf : famLim P μ fd vs =
      tyv (iUnionN fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd ρ0)) := by
    show piLam (mkM P μ) (σOf vs) (limEnd P μ fd (σOf vs)) ρ0 (famType fd) = _
    rw [drFamType S]
    rfl
  rw [hf]
  refine tyv_congr (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
    exact (drIter_empty P μ S hId n (σOf vs) z hn).elim
  · exact absurd hz (not_mem_pempty)

/-- The raw and normalized limits agree at every instance. -/
theorem drFamLim_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {fd fd' : FamData} (S : DrFamShape fd) (S' : DrFamShape fd')
    (hId : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0)))) (vs : List Nat) :
    Equiv (famLim P μ fd vs) (famLim P μ fd' vs) :=
  (drFamLim_empty P μ S hId vs).trans (drFamLim_empty P μ S' hId vs).symm

/-! ## §5 policy-free recursor-data agreement -/

/-- `RecDataAgree` minus its policy field: the components the constructor and
recursor values actually read. The policy is read only by `propRecEnd`, i.e.
only in the Prop branch of `recEnd`'s condition — unreachable at level-1
families. -/
structure DrDataAgree (fd fd' : FamData) : Prop where
  fref : fd'.fref = fd.fref
  indices : fd'.indices = fd.indices
  resLevel : fd'.resLevel = fd.resLevel
  len : fd'.ctors.length = fd.ctors.length
  ctor : ∀ (j : Nat) (c c' : List (Expr Nat) × List (Expr Nat)), fd.ctors[j]? = some c →
    fd'.ctors[j]? = some c' → c'.1.length = c.1.length ∧ c'.2 = c.2 ∧
    ∀ k (hk : k < c.1.length) (hk' : k < c'.1.length),
      occursConst fd.fref (c'.1[k]'hk') = occursConst fd.fref (c.1[k]'hk) ∧
      ihDepth (c'.1[k]'hk') = ihDepth (c.1[k]'hk)

theorem DrDataAgree.get {fd fd' : FamData} (h : DrDataAgree fd fd') {j : Nat}
    {c : List (Expr Nat) × List (Expr Nat)} (hc : fd.ctors[j]? = some c) :
    ∃ c', fd'.ctors[j]? = some c' ∧ c'.1.length = c.1.length ∧ c'.2 = c.2 ∧
      ∀ k (hk : k < c.1.length) (hk' : k < c'.1.length),
        occursConst fd.fref (c'.1[k]'hk') = occursConst fd.fref (c.1[k]'hk) ∧
        ihDepth (c'.1[k]'hk') = ihDepth (c.1[k]'hk) := by
  have hj : j < fd'.ctors.length := by rw [h.len]; exact (List.getElem?_eq_some_iff.mp hc).1
  exact ⟨_, List.getElem?_eq_getElem hj, h.ctor j c _ hc (List.getElem?_eq_getElem hj)⟩

theorem DrDataAgree.get_none {fd fd' : FamData} (h : DrDataAgree fd fd') {j : Nat}
    (hc : fd.ctors[j]? = none) : fd'.ctors[j]? = none := by
  cases hc' : fd'.ctors[j]? with
  | none => rfl
  | some c' =>
      have hj : j < fd'.ctors.length := (List.getElem?_eq_some_iff.mp hc').1
      rw [h.len] at hj
      rw [List.getElem?_eq_getElem hj] at hc
      exact Option.noConfusion hc

theorem DrDataAgree.ihArgs_eq {fd fd' : FamData} (h : DrDataAgree fd fd')
    (g : PSet.{4} → PSet.{4}) (j : Nat) (xs : List PSet.{4}) :
    ihArgs fd'.fref g (ctorFieldsOf fd' j) xs = ihArgs fd.fref g (ctorFieldsOf fd j) xs := by
  cases hc : fd.ctors[j]? with
  | none =>
      rw [ctorFieldsOf_of_none hc, ctorFieldsOf_of_none (h.get_none hc), h.fref]
  | some c =>
      obtain ⟨c', hc', hl, _, hocc⟩ := h.get hc
      rw [ctorFieldsOf_of_get hc, ctorFieldsOf_of_get hc', h.fref]
      exact (ihArgs_congr_occ fd.fref g c.1 c'.1 xs hl hocc).symm

theorem DrDataAgree.nfOf_agree {fd fd' : FamData} (h : DrDataAgree fd fd') (j : Nat) :
    nfOf fd' j = nfOf fd j := by
  cases hc : fd.ctors[j]? with
  | none => rw [nfOf_eq, nfOf_eq, ctorFieldsOf_of_none hc, ctorFieldsOf_of_none (h.get_none hc)]
  | some c =>
      obtain ⟨c', hc', hl, _, _⟩ := h.get hc
      rw [nfOf_eq, nfOf_eq, ctorFieldsOf_of_get hc, ctorFieldsOf_of_get hc', hl]

theorem DrDataAgree.recBody_eq {fd fd' : FamData} (h : DrDataAgree fd fd') (M : Interp.{4})
    (ms : List PSet.{4}) (z : PSet.{4}) (g : PSet.{4} → PSet.{4}) :
    recBody M fd' ms z g = recBody M fd ms z g := by
  unfold recBody
  rw [h.len]
  cases findIdx M (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | none => rfl
  | some j =>
      show fapps (ms.getD j pempty) (ihArgs fd'.fref g (ctorFieldsOf fd' j) (untup (nfOf fd' j) (payload z))) =
        fapps (ms.getD j pempty) (ihArgs fd.fref g (ctorFieldsOf fd j) (untup (nfOf fd j) (payload z)))
      rw [h.nfOf_agree, h.ihArgs_eq]

theorem DrDataAgree.recCore_eq {fd fd' : FamData} (h : DrDataAgree fd fd') (M : Interp.{4})
    (ms : List PSet.{4}) :
    recCore M fd' ms = recCore M fd ms := by
  show WellFounded.fix memT_wf (fun z IH => recBody M fd' ms z fun x =>
      @dite _ (MemT x z) (M.dec _) (fun h => IH x h) (fun _ => pempty)) =
    WellFounded.fix memT_wf (fun z IH => recBody M fd ms z fun x =>
      @dite _ (MemT x z) (M.dec _) (fun h => IH x h) (fun _ => pempty))
  exact congrArg (WellFounded.fix memT_wf) (funext fun z => funext fun IH => h.recBody_eq M ms z _)

theorem DrDataAgree.ctorEnd_eq {fd fd' : FamData} (h : DrDataAgree fd fd') (M : Interp.{4})
    (σ : Nat → Nat) (j nf : Nat) : ctorEnd M σ fd' j nf = ctorEnd M σ fd j nf := by
  unfold ctorEnd
  rw [h.resLevel]

/-- The recursor readings agree whenever the Prop branch is unreachable
(the family's result level is never `0`). -/
theorem DrDataAgree.recEnd_eq {fd fd' : FamData} (h : DrDataAgree fd fd')
    (hne : ∀ σ : Nat → Nat, ¬ evalTotal σ fd.resLevel = 0) (M : Interp.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) :
    recEnd M σ fd' ρ = recEnd M σ fd ρ := by
  unfold recEnd
  rw [h.resLevel]
  simp only [cond_neg (hne σ)]
  rw [h.indices, h.len, h.recCore_eq]

/-- The fixture's two family data agree on every component the constructor
and recursor values read. The field's occurs/ihDepth pairs match: both
normalize to `occursConst 1 _ = true` (`drField_norm_cases`) and
`ihDepth _ = 0` (neither field is a Π). -/
theorem drDataAgree (node : DrNode) : DrDataAgree drRawFam (drNormFam node) := by
  obtain ⟨A, hA, hf, hp, hi, hres, hc⟩ := drNormFam_shape node
  obtain ⟨rf, rp, ri, rr, rc⟩ := drRawFam_shape
  refine ⟨by rw [hf], by rw [hi], by rw [hres], by rw [hc, rc]; rfl, ?_⟩
  intro j c c' hcx hc'x
  match j, hcx with
  | 0, h =>
      have hs : ([drField], []) = c := by
        rw [rc] at h
        simpa using h
      obtain rfl := hs.symm
      rw [hc] at hc'x
      simp only [List.getElem?_cons_zero] at hc'x
      obtain rfl := Option.some.inj hc'x
      have hocc : occursConst drRawFam.fref A = occursConst drRawFam.fref drField := by
        rcases hA with h | h
        · rw [h, rf]
        · rw [h, rf]
          decide
      refine ⟨rfl, rfl, fun k hk hk' => ?_⟩
      have hk0 : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
      subst hk0
      refine ⟨hocc, ?_⟩
      rcases hA with h | h <;> rw [h] <;> rfl
  | j + 1, h => rw [rc] at h; simp at h

/-! ## §6 the bridge -/

/-- The fixture's members: `drEnv`'s table. -/
theorem drEnv_members (c : Nat) :
    drEnv.members c = if c = 3 then some drRecMember else if c = 2 then some drMkMember
      else if c = 1 then some drFamMember else if c = 0 then some drIdMember else none := rfl

/-- Faithfulness transfers from the raw family roles to the normalized ones
at the fixture: member by member, via the limits' agreement (§4) and the
policy-free data agreement (§5). -/
theorem drFaithfulD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    FaithfulR P μ (envCtx drEnvWfT) drEnv → FaithfulR P μ (envCtxD drEnvWfT) drEnv := by
  intro hF
  obtain ⟨node, hnode⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
    (rr := 3) (rm := drRecMember) drBaseWfT rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl
    (drMembersT : GroupMembersT (extendEnv drBase 1 drFamMember) drBase
      ((1, drFamMember) :: [(2, drMkMember)] ++ [(3, drRecMember)]) drEnv)
  have hctx : envCtx drEnvWfT = groupRoles drRawFam 1 3 (envCtx drBaseWfT) :=
    envCtx_group_some (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
      (rr := 3) (rm := drRecMember) drBaseWfT rfl
      (fun c hc => by simp at hc; subst hc; rfl) rfl
      (drMembersT : GroupMembersT (extendEnv drBase 1 drFamMember) drBase
        ((1, drFamMember) :: [(2, drMkMember)] ++ [(3, drRecMember)]) drEnv)
      drRawFam rfl
  have hctxD : envCtxD drEnvWfT = groupRoles (drNormFam node) 1 3 (envCtxD drBaseWfT) :=
    envCtxD_group_some (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
      (rr := 3) (rm := drRecMember) drBaseWfT rfl
      (fun c hc => by simp at hc; subst hc; rfl) rfl
      (drMembersT : GroupMembersT (extendEnv drBase 1 drFamMember) drBase
        ((1, drFamMember) :: [(2, drMkMember)] ++ [(3, drRecMember)]) drEnv)
      (drNormFam node) hnode
  have hId : Equiv (μ 0 []) (memberValR P μ (.plain) drIdMember []) := hF 0 drIdMember rfl []
  have hId' : Equiv (μ 0 []) (den (mkM P μ) (fun _ => 0) ρ0
      (.lam (.sort (.succ .zero)) (.bvar 0))) := hId
  have hraw : DrFamShape drRawFam := drRawFam_DrFamShape
  have hnorm : DrFamShape (drNormFam node) := drNormFam_DrFamShape node
  have hagree := drDataAgree node
  have hne : ∀ σ : Nat → Nat, ¬ evalTotal σ drRawFam.resLevel = 0 := fun σ h0 => by
    rw [(drRawFam_shape).2.2.2.1] at h0
    exact absurd h0 (Nat.succ_ne_zero _)
  intro r m hm vs
  match r, hm with
  | 0, hm =>
      -- both contexts are plain at `0` (the base environment is `Id` only)
      show Equiv (μ 0 vs) (memberValR P μ ((envCtxD drEnvWfT) 0) m vs)
      show Equiv (μ 0 vs) (memberVal P μ m vs)
      exact hF 0 m hm vs
  | 1, hm =>
      show Equiv (μ 1 vs) (memberValR P μ ((envCtxD drEnvWfT) 1) m vs)
      rw [drEnv_members, if_neg (by omega : ¬(1 : Nat) = 3),
        if_neg (by omega : ¬(1 : Nat) = 2), if_pos (rfl : (1 : Nat) = 1)] at hm
      obtain rfl := Option.some.inj hm
      rw [hctxD]
      show Equiv (μ 1 vs) (famLim P μ (drNormFam node) vs)
      rw [hctx] at hF
      exact (hF 1 drFamMember rfl vs).trans (drFamLim_eq P μ hraw hnorm hId' vs)
  | 2, hm =>
      show Equiv (μ 2 vs) (memberValR P μ ((envCtxD drEnvWfT) 2) m vs)
      rw [drEnv_members, if_neg (by omega : ¬(2 : Nat) = 3),
        if_pos (rfl : (2 : Nat) = 2)] at hm
      obtain rfl := Option.some.inj hm
      rw [hctxD]
      show Equiv (μ 2 vs) (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (drNormFam node) 0 (nfOf (drNormFam node) 0)) ρ0
        drMkMember.mtype)
      have hval : piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (drNormFam node) 0 (nfOf (drNormFam node) 0)) ρ0
          drMkMember.mtype =
          piLam (mkM P μ) (σOf vs)
            (ctorEnd (mkM P μ) (σOf vs) drRawFam 0 (nfOf drRawFam 0)) ρ0
            drMkMember.mtype := by
        rw [hagree.nfOf_agree 0, hagree.ctorEnd_eq]
      rw [hval]
      rw [hctx] at hF
      exact hF 2 drMkMember rfl vs
  | 3, hm =>
      show Equiv (μ 3 vs) (memberValR P μ ((envCtxD drEnvWfT) 3) m vs)
      rw [drEnv_members, if_pos (rfl : (3 : Nat) = 3)] at hm
      obtain rfl := Option.some.inj hm
      rw [hctxD]
      show Equiv (μ 3 vs) (piLam (mkM P μ) (σOf vs)
        (recEnd (mkM P μ) (σOf vs) (drNormFam node)) ρ0 drRecMember.mtype)
      rw [show (recEnd (mkM P μ) (σOf vs) (drNormFam node)) =
          recEnd (mkM P μ) (σOf vs) drRawFam from
        funext (fun ρ => hagree.recEnd_eq hne (mkM P μ) (σOf vs) ρ)]
      rw [hctx] at hF
      exact hF 3 drRecMember rfl vs
  | (r + 4), hm =>
      rw [drEnv_members] at hm
      simp at hm

/-- **The bridge at the δ fixture, proved**: the normalized-role invariant
gives the raw-role one. -/
theorem drRoleBridge (P : Premises4) (K : Nat → Nat) : DrRoleBridge P K := by
  intro hD ctx hctx μ hF
  have hF' : FaithfulR P μ (envCtx drEnvWfT) drEnv := by
    intro r m hm
    have hdom : Dom drEnv r := by
      rw [Dom, hm]
      exact Option.isSome_some
    rw [← hctx r hdom]
    exact hF r m hm
  exact hD (envCtxD drEnvWfT) (fun r _ => rfl) μ (drFaithfulD P μ hF')

/-- The D group step at the δ fixture, unconditionally. -/
theorem stepDAt_drEnv_uncond (P : Premises4) (K : Nat → Nat) :
    GroupStepAt P K (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
      (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT :=
  stepDAt_drEnv_of_bridge P K (drRoleBridge P K)

/-! ## §7 the general schema and the measured boundary -/

/-- The weakest checked side condition under which the general D step's role
bridge follows: faithfulness at the raw roles transfers to the normalized
roles, at environment granularity. -/
def RoleBridgeEnv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ μ : Nat → List Nat → PSet.{4}, FaithfulR P μ (envCtx hW) E → FaithfulR P μ (envCtxD hW) E

/-- Under the side condition, the role bridge holds at every environment:
`GInvD`'s conclusion is role-free. -/
theorem gInv_of_roleBridgeEnv {P : Premises4} {K : Nat → Nat} {E : ResolvedEnv} {hW : EnvWfT E}
    (hR : RoleBridgeEnv P K hW) (hD : GInvD P K hW) : GInv P K hW := by
  intro ctx hctx μ hF
  have hF' : FaithfulR P μ (envCtx hW) E := by
    intro r m hm
    have hdom : Dom E r := by
      rw [Dom, hm]
      exact Option.isSome_some
    rw [← hctx r hdom]
    exact hF r m hm
  exact hD (envCtxD hW) (fun r _ => rfl) μ (hR μ hF')

/-- The side condition is discharged at the fixture (§6 is exactly this). -/
theorem roleBridgeEnv_drEnv (P : Premises4) (K : Nat → Nat) : RoleBridgeEnv P K drEnvWfT :=
  fun μ hF => drFaithfulD P μ hF

end Rcic.F3.TierGroup
