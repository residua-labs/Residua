import rcic.RcicIotaWitnessTyped
import rcic.RcicIARecTyped
import rcic.RcicConstsClosedEnvWfT

/-!
# DT-019 / IA-021 S1 — the recursor cell WITH the admission typing

`RecursorCellT` (`RcicIATypedIota`) keeps, of a `GroupMembersT.cons` node at a
recursor, the admission record, the ι descriptor clause and the typed ι
equations. The direct ι-SR route and IA-021 at `EnvWfT` need three more things
the same node carries and the cell dropped:

* `hT` — the stored recursor type sort-typed in the derivation prefix `E0`;
* `IndGroupTypedT`'s family and constructor typed content (`FamilyTypedT`,
  `∀ i, CtorTypedT`);
* the closure of every stored type in `E0` (`MembersClosed`, from
  `RcicConstsClosedEnvWfT`), the gate-free form of package B's env-transfer
  gates.

`RecursorCellHT` is that bundle; `envWfT_cellHT` is the same walk as
`envWfT_recursorCellMinors` carrying it. IA-021 at `EnvWfT`
(`IA021T_minorDomains_of_cellHT`): every stored minor domain is sort-typed in
its minor context from `hT` alone (`recursor_minorType_typed`), and a finite
constructive choice packages the per-minor `∃ w, Nonempty …` into
`Nonempty (MinorDomainsTyped c.adm)`. The sealed tooth
`IA021T_minorDomains_not_of_admission` is untouched: it is about a bare admission
record, this is about an admitted environment.

`closure_claim` 0.
-/

namespace Rcic.Declarative

structure RecursorCellHT (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type where
  cell : RecursorCellT E r m
  u : Level
  hT : HasTyT cell.E0 m.arity [] m.mtype (.sort u)
  famTyped : FamilyTypedT cell.adm.family
  ctorsTyped : ∀ i, CtorTypedT (cell.adm.constructorViews i)
  closed : MembersClosed cell.E0
  bodies : BodiesClosed cell.E0

def RecursorCellHT.lift {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hsub : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (c : RecursorCellHT E r m) : RecursorCellHT E' r m :=
  ⟨c.cell.lift hsub, c.u, c.hT, c.famTyped, c.ctorsTyped, c.closed, c.bodies⟩

def recursorCellHT_of_admitted {E E'' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hcls : m.mclass = .recursorM)
    (hsub : ∀ r' m', (extendEnv E r m).members r' = some m' → E''.members r' = some m')
    (u : Level) (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (hM : MembersClosed E) (hB : BodiesClosed E) :
    (hadm : IndGroupAdmitted E r m) → IndGroupTypedT hadm → RecursorCellHT E'' r m
  | .family _ view _ hm _, _ =>
      absurd (show m.mclass = .inductiveM from hm ▸ view.hasClass)
        (fun h => by rw [hcls] at h; cases h)
  | .constructor _ view _ _ _ _ _, _ =>
      absurd view.hasClass (fun h => by rw [hcls] at h; cases h)
  | .recursor a hfresh _ _ _ _ h14, ht =>
      ⟨⟨E, a, h14, ht.2.2, hsub, hfresh⟩, u, hT, ht.1, ht.2.1, hM, hB⟩

def groupMembersT_cellHT {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → BodiesClosed E → MembersClosed E → {r : Nat} → {m : CheckedMember} →
    E'.members r = some m → E.members r = none → m.mclass = .recursorM →
    RecursorCellHT E' r m
  | _, _, _, .nil _, _, _, _, _, hm, hnone, _ => absurd (hnone ▸ hm) (by simp)
  | _, _, _, .cons E r₀ m₀ _ E' hfresh hnobody _ _ _ _ _ hadm _ u hT _ htyped hrest, hB, hM,
      r, m, hm, hnone, hcls => by
      by_cases hr : r = r₀
      · subst hr
        have hm0 : E'.members r = some m₀ :=
          groupMembersT_mono hrest r m₀ (by simp [extendEnv])
        have heq : m₀ = m := Option.some.inj (hm0.symm.trans hm)
        subst heq
        exact recursorCellHT_of_admitted hcls (groupMembersT_mono hrest) u hT hM hB hadm htyped
      · exact groupMembersT_cellHT hrest (bodiesClosed_extend_nobody hfresh hnobody hB)
          (membersClosed_extend hfresh hB hM (hasTyT_constsIn hT)) hm
          (by simp only [extendEnv, if_neg hr]; exact hnone) hcls

def envWfT_cellHT : {E : ResolvedEnv} → EnvWfT E → {r : Nat} → {m : CheckedMember} →
    E.members r = some m → m.mclass = .recursorM → RecursorCellHT E r m
  | _, .empty, _, _, hm, _ => absurd hm (by simp [emptyEnv])
  | _, .axiom E r₀ _ _ hE hfresh _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHT hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .definition E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHT hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .thm E r₀ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHT hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .opaque E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHT hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .group E _ _ _ _ _ _ hE _ _ _ hmem, r, m, hm, hcls => by
      cases hb : E.members r with
      | some m' =>
          have h' := groupMembersT_mono hmem r m' hb
          have heq : m' = m := Option.some.inj (h'.symm.trans hm)
          subst heq
          exact (envWfT_cellHT hE hb hcls).lift (groupMembersT_mono hmem)
      | none =>
          exact groupMembersT_cellHT hmem (bodiesClosed_of_envWfT hE)
            (membersClosed_of_envWfT hE) hm hb hcls

/-! ## IA-021 at `EnvWfT`: the minors are typed from `hT` -/

/-- finite constructive choice over `Fin k`: per-index existence of a level with an
    inhabited (`Type`-valued) family packages into one inhabited level function. -/
theorem finChoiceLevel : (k : Nat) → (P : Fin k → Level → Type) →
    (∀ i, ∃ w, Nonempty (P i w)) → Nonempty (Σ' ws : Fin k → Level, ∀ i, P i (ws i))
  | 0, _, _ => ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | k + 1, P, h => by
      obtain ⟨w0, ⟨h0⟩⟩ := h 0
      obtain ⟨⟨ws', h'⟩⟩ := finChoiceLevel k (fun i w => P i.succ w) (fun i => h i.succ)
      refine ⟨⟨Fin.cases w0 ws', fun i => ?_⟩⟩
      refine Fin.cases (motive := fun i => P i (Fin.cases w0 ws' i)) ?_ ?_ i
      · simpa using h0
      · intro j; simpa using h' j

/-- IA-021 at an admitted recursor cell: `MinorDomainsTyped` is inhabited — every stored
    minor domain is sort-typed in its minor context from the cell's `hT`
    (`recursor_minorType_typed`), the levels chosen by `finChoiceLevel`. -/
theorem IA021T_minorDomains_of_cellHT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellHT E r m) : Nonempty (MinorDomainsTyped c.cell.adm) := by
  have h : ∀ i : Fin c.cell.adm.minorTypes.length, ∃ w,
      Nonempty (HasTyT c.cell.E0 m.arity (minorCtxT c.cell.adm i.val)
        (c.cell.adm.minorTypes[i.val]) (.sort w)) :=
    fun i => recursor_minorType_typed c.cell.adm c.hT i.val i.isLt
  obtain ⟨⟨ws, hws⟩⟩ := finChoiceLevel _ _ h
  exact ⟨⟨ws, hws⟩⟩

/-- IA-021 at `EnvWfT`: every recursor member's admission has typed minors. -/
theorem IA021T_minorDomains_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    Nonempty (MinorDomainsTyped (envWfT_cellHT hW hm hcls).cell.adm) :=
  IA021T_minorDomains_of_cellHT _

end Rcic.Declarative

#print axioms Rcic.Declarative.envWfT_cellHT
#print axioms Rcic.Declarative.IA021T_minorDomains_of_cellHT
#print axioms Rcic.Declarative.IA021T_minorDomains_of_envWfT
