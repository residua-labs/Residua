/-
Class-A boundary discharge (F3 route-c, lane devin-fcd 2026-10-24):
`admitted_group_nonIR`, scoped form.

THEOREM (`admitted_group_nonIR_scoped`): for `hW : EnvWfT E` passing
the group's scope test (`hW.ScopeCheck`) and a recursor member
`E.members r = some m`, every `a : RecursorEliminationAdmitted E r m`
satisfies `a.NonIR` — each constructor view's field list is a
`NonIRFieldList`: no field domain free-references an earlier field
whose domain mentions the family.

METHOD (all unconditional; no kernel row used — the RK-01 question
posed upstream is answered NO for this theorem):
  - the group's `GroupInScopeT` gives each constructor's
    `CtorViewT`: `member.mtype = ctorTypeT f canon mirrors fs res`,
    `fs`'s `.plain` domains typed in the BASE env (`FieldsTyT`), and
    `hsnd` excluding `.drecD`;
  - `policyPi`/peel injectivity plus the recursor member's stored-type
    equations pin the view's parameter count to the skeleton's
    (`np_a = np_g`), so `c.fields = ctorDomsT … fs` EXACTLY;
  - the sieve: a `FamilyVisible` field `j` must be `.drec` (a plain
    field's domain is `constsIn`-fam-free; `drecD` is gated out), which
    sets `recs[k-1-j] = true`; `ctorDomsT`-produced domains only reach
    mask positions through `unplainIdx`, and `unplainIdx` never lands
    on a `true` flag — so `freeBvarRef (k-1-j) _ fields[k] = false`.

`RecursorEliminationAdmitted`'s honest uses satisfy `E.members r =
some m` (the recursor member is present by construction), so the
premise is not an extra assumption — it is what makes `a` the record
of THIS recursor's group.

`closure_claim = 0` is untouched: this discharges the scoped
`admitted_group_nonIR`; the raw unconditional form
`∀ a : RecursorEliminationAdmitted E r m, a.NonIR` without the member
premise stays a named residue (a phantom `m`/`r` pairing can misalign
the parameter count; the member premise is the group identity).
-/

import rcic.RcicIndGroupNonIR
import rcic.RcicRouteCGroupScope
import rcic.RcicAnnEnvBridgeGroup
import rcic.RcicTypedScopeCheck
import rcic.RcicSubstT
import rcic.RcicConstsClosedEnvWfT
import rcic.RcicModelEnv
import rcic.RcicIARecUnique
import rcic.RcicIotaLegacyFamFree

namespace Rcic.Declarative

/-! ## (1) constants-in-env helpers -/

/-- a member added by the chain is present at the end. -/
theorem groupMembersT_mem_of_mem {S E : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (h : GroupMembersT S E ms E') {r : Nat} {m : CheckedMember}
    (hin : (r, m) ∈ ms) : E'.members r = some m := by
  induction h with
  | nil E₁ => exact absurd hin (List.not_mem_nil _)
  | cons E₁ r₀ m₀ rest E₁' hfresh hnobody hclT harity hlvlB hcanon
      harities hadm hidxAdmT u hT hTc htyped hrest ih =>
      cases hin with
      | head =>
          exact groupMembersT_mono hrest r m (members_extend_eq E₁ r m)
      | tail _ h' => exact ih h'

/-- a member of `E'` is either one of `ms` or was already in `E`. -/
theorem groupMembersT_cases {S E : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (h : GroupMembersT S E ms E') {r : Nat} {m : CheckedMember}
    (hm : E'.members r = some m) :
    (∃ m', (r, m') ∈ ms ∧ m = m') ∨ E.members r = some m := by
  induction h with
  | nil E₁ => exact Or.inr hm
  | cons E₁ r₀ m₀ rest E₁' hfresh hnobody hclT harity hlvlB hcanon
      harities hadm hidxAdmT u hT hTc htyped hrest ih =>
      cases ih hm with
      | inl h' =>
          obtain ⟨m', hmem', heq⟩ := h'
          exact Or.inl ⟨m', List.mem_cons_of_mem _ hmem', heq⟩
      | inr h' =>
          by_cases hrr : r = r₀
          · subst hrr
            rw [members_extend_eq] at h'
            exact Or.inl ⟨m₀, List.mem_cons_self _ _, (Option.some.inj h').symm⟩
          · rw [members_extend_ne E₁ r₀ m₀ r hrr] at h'
            exact Or.inr h'

/-- every member admitted along the chain is body-less. -/
theorem groupMembersT_nobody {S E : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (h : GroupMembersT S E ms E') {r : Nat} {m : CheckedMember}
    (hin : (r, m) ∈ ms) : m.body = none := by
  induction h with
  | nil E₁ => exact absurd hin (List.not_mem_nil _)
  | cons E₁ r₀ m₀ rest E₁' hfresh hnobody hclT harity hlvlB hcanon
      harities hadm hidxAdmT u hT hTc htyped hrest ih =>
      cases hin with
      | head => exact hnobody
      | tail _ h' => exact ih h'

/-! ## (2) containsFamilyFuel helpers -/

/-- the family's δ-unfold closure cannot reach the family through
    `E₀`-constants when the family is not yet a member. -/
theorem containsFamilyFuel_no_fam {E₀ E : ResolvedEnv} {fam : Nat}
    (hsub : ∀ r m, E₀.members r = some m → E.members r = some m)
    (hbody : ∀ r m b, E₀.members r = some m → m.body = some b → ConstsIn E₀ b)
    (hf : E₀.members fam = none) :
    (fuel : Nat) → (e : Expr Nat) → ConstsIn E₀ e →
      containsFamilyFuel E fam fuel e ≠ some true
  | 0, _, _ => by simp [containsFamilyFuel]
  | fuel + 1, e, hc => by
      cases e with
      | bvar i => simp [containsFamilyFuel]
      | sort l => simp [containsFamilyFuel]
      | const r ls =>
          obtain ⟨m, hm⟩ := hc
          have hmE : E.members r = some m := hsub r m hm
          simp only [containsFamilyFuel]
          rw [if_neg (by rintro rfl; rw [hm] at hf; exact Option.noConfusion hf)]
          cases htb : transparentBody E r ls with
          | none => simp
          | some body =>
              simp only [transparentBody, hmE] at htb
              split at htb
              · next _ =>
                  split at htb
                  · next b hbd =>
                      obtain rfl := Option.some.inj htb
                      exact containsFamilyFuel_no_fam hsub hbody hf fuel
                        (instantiateLevels ls b)
                        (constsIn_instantiateLevels ls (hbody r m b hm hbd))
                  · next _ => exact Option.noConfusion htb
              · next _ => exact Option.noConfusion htb
      | lit t =>
          cases t with
          | zero =>
              simp only [containsFamilyFuel]
              exact containsFamilyFuel_no_fam hsub hbody hf fuel litZero
                (by show ConstsIn E₀ (.const 1 []); exact hc)
          | succ t =>
              simp only [containsFamilyFuel]
              obtain ⟨h1, h2⟩ := hc
              cases h2r : containsFamilyFuel E fam fuel (.const 2 []) with
              | none => simp
              | some vb =>
                  have hnot := containsFamilyFuel_no_fam hsub hbody hf fuel
                    (.const 2 []) h2
                  rw [h2r] at hnot
                  cases vb with
                  | true => exact absurd rfl hnot
                  | false =>
                      exact containsFamilyFuel_no_fam hsub hbody hf fuel litZero
                        (by show ConstsIn E₀ (.const 1 []); exact h1)
      | app f x =>
          obtain ⟨hf1, hf2⟩ := hc
          simp only [containsFamilyFuel]
          cases hg : containsFamilyFuel E fam fuel f with
          | none => simp
          | some vb =>
              have hnot := containsFamilyFuel_no_fam hsub hbody hf fuel f hf1
              rw [hg] at hnot
              cases vb with
              | true => exact absurd rfl hnot
              | false =>
                  exact containsFamilyFuel_no_fam hsub hbody hf fuel x hf2
      | lam a b =>
          obtain ⟨ha, hb⟩ := hc
          simp only [containsFamilyFuel]
          cases hg : containsFamilyFuel E fam fuel a with
          | none => simp
          | some vb =>
              have hnot := containsFamilyFuel_no_fam hsub hbody hf fuel a ha
              rw [hg] at hnot
              cases vb with
              | true => exact absurd rfl hnot
              | false =>
                  exact containsFamilyFuel_no_fam hsub hbody hf fuel b hb
      | pi a b =>
          obtain ⟨ha, hb⟩ := hc
          simp only [containsFamilyFuel]
          cases hg : containsFamilyFuel E fam fuel a with
          | none => simp
          | some vb =>
              have hnot := containsFamilyFuel_no_fam hsub hbody hf fuel a ha
              rw [hg] at hnot
              cases vb with
              | true => exact absurd rfl hnot
              | false =>
                  exact containsFamilyFuel_no_fam hsub hbody hf fuel b hb
      | letE a v b =>
          obtain ⟨ha, hv, hb⟩ := hc
          simp only [containsFamilyFuel]
          cases hg : containsFamilyFuel E fam fuel a with
          | none => simp
          | some vb =>
              have hnot := containsFamilyFuel_no_fam hsub hbody hf fuel a ha
              rw [hg] at hnot
              cases vb with
              | true => exact absurd rfl hnot
              | false =>
                  cases hv2 : containsFamilyFuel E fam fuel v with
                  | none => simp
                  | some vb2 =>
                      have hnot2 := containsFamilyFuel_no_fam hsub hbody hf fuel v hv
                      rw [hv2] at hnot2
                      cases vb2 with
                      | true => exact absurd rfl hnot2
                      | false =>
                          exact containsFamilyFuel_no_fam hsub hbody hf fuel b hb

/-- `.up` preserves bvar-valuedness. -/
theorem substT_bvar_up {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) :
    ∀ i, ∃ j, σ.up i = .bvar j
  | 0 => ⟨0, rfl⟩
  | i + 1 => by
      obtain ⟨j, hj⟩ := hσ i
      exact ⟨j + 1, by rw [SubstT.up_succ, hj, lift_zero_one_bvar]⟩

/-- a `bvar`-valued parallel substitution preserves the family scan:
    the image's constants are the source's. -/
theorem containsFamilyFuel_substT {E : ResolvedEnv} {fam : Nat} :
    (fuel : Nat) → (σ : SubstT) → (∀ i, ∃ j, σ i = .bvar j) → (e : Expr Nat) →
    containsFamilyFuel E fam fuel (substT σ e) = containsFamilyFuel E fam fuel e
  | 0, _, _, _ => rfl
  | fuel + 1, σ, hσ, e => by
      cases e with
      | bvar i =>
          obtain ⟨j, hj⟩ := hσ i
          show containsFamilyFuel E fam (fuel + 1) (σ i) = _
          rw [hj]; rfl
      | sort l => rfl
      | lit t => rfl
      | const r ls => rfl
      | app f x =>
          show containsFamilyFuel E fam (fuel + 1)
              (.app (substT σ f) (substT σ x)) = _
          simp only [containsFamilyFuel, containsFamilyFuel_substT fuel σ hσ f,
            containsFamilyFuel_substT fuel σ hσ x]
      | lam a b =>
          show containsFamilyFuel E fam (fuel + 1)
              (.lam (substT σ a) (substT σ.up b)) = _
          simp only [containsFamilyFuel, containsFamilyFuel_substT fuel σ hσ a,
            containsFamilyFuel_substT fuel σ.up (substT_bvar_up hσ) b]
      | pi a b =>
          show containsFamilyFuel E fam (fuel + 1)
              (.pi (substT σ a) (substT σ.up b)) = _
          simp only [containsFamilyFuel, containsFamilyFuel_substT fuel σ hσ a,
            containsFamilyFuel_substT fuel σ.up (substT_bvar_up hσ) b]
      | letE a v b =>
          show containsFamilyFuel E fam (fuel + 1)
              (.letE (substT σ a) (substT σ v) (substT σ.up b)) = _
          simp only [containsFamilyFuel, containsFamilyFuel_substT fuel σ hσ a,
            containsFamilyFuel_substT fuel σ hσ v,
            containsFamilyFuel_substT fuel σ.up (substT_bvar_up hσ) b]

/-- the `const fam` head is visible through any argument spine. -/
theorem familyVisible_foldApps {E : ResolvedEnv} {fam : Nat} {f : Expr Nat}
    (h : FamilyVisible E fam f) : (args : List (Expr Nat)) →
    FamilyVisible E fam (foldApps f args)
  | [] => h
  | x :: xs => by
      show FamilyVisible E fam (foldApps (.app f x) xs)
      apply familyVisible_foldApps (f := .app f x)
      obtain ⟨fuel, hf⟩ := h
      refine ⟨fuel + 1, ?_⟩
      show containsFamilyFuel E fam (fuel + 1) (.app f x) = some true
      simp only [containsFamilyFuel]
      rw [hf]

/-- a `.drec` domain is family-visible: the literal `const fam` head. -/
theorem familyVisible_ctorDoms_drec {E : ResolvedEnv} {f : Nat} {ls : List Level}
    {args : List (Expr Nat)} :
    FamilyVisible E f (foldApps (.const f ls) args) :=
  familyVisible_foldApps familyVisible_const args

/-- `FamilyVisible` lifts through a `bvar`-valued `substT`. -/
theorem familyVisible_substT {E : ResolvedEnv} {fam : Nat}
    {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) {e : Expr Nat}
    (h : FamilyVisible E fam (substT σ e)) : FamilyVisible E fam e := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, by rw [← containsFamilyFuel_substT fuel σ hσ e]; exact hf⟩

/-! ## (3) `freeBvarRef` preimage under `substT` -/

/-- `upNT m σ (i + m)` reads `σ i`, lifted. -/
theorem SubstT.upNT_ge (m : Nat) (σ : SubstT) (i : Nat) :
    SubstT.upNT m σ (i + m) = lift 0 m (σ i) := by
  induction m generalizing σ i with
  | zero => exact (lift_zero_idx 0 (σ i)).symm
  | succ m ihm =>
      show SubstT.upNT m σ.up (i + (m + 1)) = lift 0 (m + 1) (σ i)
      rw [show i + (m + 1) = (i + 1) + m from by omega, ihm σ.up (i + 1),
        SubstT.up_succ, lift_lift_merge m 1 0 0 (Nat.le_refl 0) (Nat.zero_le _),
        Nat.add_comm]

/-- `upNT` of a bvar-valued substitution is bvar-valued. -/
theorem SubstT.upNT_bvar {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) :
    ∀ m i, ∃ j, SubstT.upNT m σ i = .bvar j := by
  intro m i
  by_cases hi : i < m
  · exact ⟨i, SubstT.upNT_lt m σ i hi⟩
  · obtain ⟨j, hj⟩ := hσ (i - m)
    refine ⟨j + m, ?_⟩
    rw [show i = i - m + m from by omega, SubstT.upNT_ge, hj]
    simp only [lift]
    rw [if_pos (Nat.zero_le _)]

/-- a hit of `freeBvarRef` under `substT (upNT d σ)` comes from a source
    `bvar` whose σ-image is that slot. -/
theorem freeBvarRef_upNT {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) :
    (e : Expr Nat) → (d p : Nat) →
    freeBvarRef p d (substT (SubstT.upNT d σ) e) = true →
    ∃ q, freeBvarRef q d e = true ∧ SubstT.upNT d σ (q + d) = .bvar (p + d)
  | .bvar i, d, p, h => by
      obtain ⟨j, hj⟩ := SubstT.upNT_bvar hσ d i
      have h2 : freeBvarRef p d (SubstT.upNT d σ i) = true := h
      rw [hj] at h2
      simp only [freeBvarRef] at h2
      have hjp : j = p + d := of_decide_eq_true h2
      by_cases hi : i < d
      · rw [SubstT.upNT_lt d σ i hi] at hj
        have hij : i = j := Expr.bvar.inj hj
        exact absurd (hij.trans hjp) (by omega)
      · refine ⟨i - d, ?_, ?_⟩
        · show freeBvarRef (i - d) d (.bvar i) = true
          simp only [freeBvarRef]
          have hi2 : i - d + d = i := by omega
          rw [hi2]
          exact decide_eq_true rfl
        · have hi2 : i - d + d = i := by omega
          rw [hi2, hj]
          exact congrArg Expr.bvar hjp
  | .sort _, _, _, h => by cases h
  | .const _ _, _, _, h => by cases h
  | .lit _, _, _, h => by cases h
  | .app f x, d, p, h => by
      simp only [substT, freeBvarRef, Bool.or_eq_true] at h
      cases h with
      | inl h' =>
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ f d p h'
          exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; rfl, hq2⟩
      | inr h' =>
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ x d p h'
          exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; simp, hq2⟩
  | .lam a b, d, p, h => by
      simp only [substT, freeBvarRef, Bool.or_eq_true] at h
      cases h with
      | inl h' =>
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ a d p h'
          exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; rfl, hq2⟩
      | inr h' =>
          rw [← SubstT.upNT_succ] at h'
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ b (d + 1) p h'
          refine ⟨q, ?_, ?_⟩
          · show freeBvarRef q d (.lam a b) = true
            simp only [freeBvarRef]
            rw [hq1]; simp
          · have huq : SubstT.upNT (d + 1) σ (q + (d + 1)) =
                lift 0 1 (SubstT.upNT d σ (q + d)) := by
              rw [SubstT.upNT_succ]
              show (SubstT.upNT d σ).up ((q + d) + 1) = _
              rw [SubstT.up_succ]
            rw [huq] at hq2
            obtain ⟨j, hj⟩ := SubstT.upNT_bvar hσ d (q + d)
            rw [hj] at hq2
            rw [lift_zero_one_bvar] at hq2
            have hjb : j + 1 = p + (d + 1) := Expr.bvar.inj hq2
            have hjp : j = p + d := by omega
            rw [hj]; exact congrArg Expr.bvar hjp
  | .pi a b, d, p, h => by
      simp only [substT, freeBvarRef, Bool.or_eq_true] at h
      cases h with
      | inl h' =>
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ a d p h'
          exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; rfl, hq2⟩
      | inr h' =>
          rw [← SubstT.upNT_succ] at h'
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ b (d + 1) p h'
          refine ⟨q, ?_, ?_⟩
          · show freeBvarRef q d (.pi a b) = true
            simp only [freeBvarRef]
            rw [hq1]; simp
          · have huq : SubstT.upNT (d + 1) σ (q + (d + 1)) =
                lift 0 1 (SubstT.upNT d σ (q + d)) := by
              rw [SubstT.upNT_succ]
              show (SubstT.upNT d σ).up ((q + d) + 1) = _
              rw [SubstT.up_succ]
            rw [huq] at hq2
            obtain ⟨j, hj⟩ := SubstT.upNT_bvar hσ d (q + d)
            rw [hj] at hq2
            rw [lift_zero_one_bvar] at hq2
            have hjb : j + 1 = p + (d + 1) := Expr.bvar.inj hq2
            have hjp : j = p + d := by omega
            rw [hj]; exact congrArg Expr.bvar hjp
  | .letE a v b, d, p, h => by
      simp only [substT, freeBvarRef, Bool.or_eq_true] at h
      cases h with
      | inl h' =>
          cases h' with
          | inl h'' =>
              obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ a d p h''
              exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; rfl, hq2⟩
          | inr h'' =>
              obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ v d p h''
              exact ⟨q, by simp only [freeBvarRef]; rw [hq1]; simp, hq2⟩
      | inr h' =>
          rw [← SubstT.upNT_succ] at h'
          obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT hσ b (d + 1) p h'
          refine ⟨q, ?_, ?_⟩
          · show freeBvarRef q d (.letE a v b) = true
            simp only [freeBvarRef]
            rw [hq1]; simp
          · have huq : SubstT.upNT (d + 1) σ (q + (d + 1)) =
                lift 0 1 (SubstT.upNT d σ (q + d)) := by
              rw [SubstT.upNT_succ]
              show (SubstT.upNT d σ).up ((q + d) + 1) = _
              rw [SubstT.up_succ]
            rw [huq] at hq2
            obtain ⟨j, hj⟩ := SubstT.upNT_bvar hσ d (q + d)
            rw [hj] at hq2
            rw [lift_zero_one_bvar] at hq2
            have hjb : j + 1 = p + (d + 1) := Expr.bvar.inj hq2
            have hjp : j = p + d := by omega
            rw [hj]; exact congrArg Expr.bvar hjp

/-- the mask substitution is `bvar`-valued. -/
theorem maskSubst_bvar (recs : List Bool) : ∀ i, ∃ j, maskSubst recs i = .bvar j :=
  fun i => ⟨unplainIdx recs i, rfl⟩

/-- a `freeBvarRef` hit in a `maskSubst` image resolves to a mask index. -/
theorem freeBvarRef_mask {p d : Nat} {recs : List Bool} {e : Expr Nat}
    (h : freeBvarRef p d (substT (SubstT.upNT d (maskSubst recs)) e) = true) :
    ∃ q, freeBvarRef q d e = true ∧ unplainIdx recs q = p := by
  obtain ⟨q, hq1, hq2⟩ := freeBvarRef_upNT (maskSubst_bvar recs) e d p h
  refine ⟨q, hq1, ?_⟩
  have hge : SubstT.upNT d (maskSubst recs) (q + d) =
      lift 0 d (maskSubst recs q) := SubstT.upNT_ge d _ q
  rw [hge] at hq2
  have hqq : lift 0 d (Expr.bvar (unplainIdx recs q)) = .bvar (p + d) := hq2
  rw [show lift 0 d (Expr.bvar (unplainIdx recs q)) =
      Expr.bvar (unplainIdx recs q + d) from by
    simp only [lift]; rw [if_pos (Nat.zero_le _)]] at hqq
  exact Nat.add_right_cancel (Expr.bvar.inj hqq)

/-! ## (4) `unplainIdx` and `ctorDomsT` -/

/-- `unplainIdx` never lands on a `true` flag within range. -/
theorem unplainIdx_eq_flag_false : (recs : List Bool) → (q p : Nat) →
    unplainIdx recs q = p → (hp : p < recs.length) → recs[p] = false
  | [], _, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | true :: rs, q, p, h, hp => by
      have h' : unplainIdx rs q + 1 = p := h
      cases p with
      | zero => omega
      | succ p' =>
          have hp' : p' < rs.length := by
            simp only [List.length_cons] at hp; omega
          have hpq : unplainIdx rs q = p' := by omega
          have hflag := unplainIdx_eq_flag_false rs q p' hpq hp'
          show ((true :: rs)[p' + 1]'(by
              simp only [List.length_cons]; omega)) = false
          rw [List.getElem_cons_succ]; exact hflag
  | false :: rs, q, p, h, hp => by
      cases q with
      | zero =>
          have h' : (0 : Nat) = p := h
          subst h'
          rfl
      | succ q' =>
          have h' : unplainIdx rs q' + 1 = p := h
          cases p with
          | zero => omega
          | succ p' =>
              have hp' : p' < rs.length := by
                simp only [List.length_cons] at hp; omega
              have hpq : unplainIdx rs q' = p' := by omega
              have hflag := unplainIdx_eq_flag_false rs q' p' hpq hp'
              show ((false :: rs)[p' + 1]'(by
                  simp only [List.length_cons]; omega)) = false
              rw [List.getElem_cons_succ]; exact hflag

/-- `ctorDomsT` splits at a list boundary. -/
theorem ctorDomsT_append (f : Nat) (ls : List Level) :
    (fs₁ fs₂ : List FieldT) → (pl : List (Expr Nat)) → (σ : SubstT) →
    ctorDomsT f ls pl σ (fs₁ ++ fs₂) =
      ctorDomsT f ls pl σ fs₁ ++
        ctorDomsT f ls (pl.map (lift 0 fs₁.length)) (ctorEndSubstT σ fs₁) fs₂
  | [], fs₂, pl, σ => by
      simp only [ctorDomsT, List.nil_append, ctorEndSubstT, List.length_nil]
      rw [show pl.map (lift 0 0) = pl from
        List.map_id'' (fun x => lift_zero_idx 0 x) pl]
  | .plain D u :: fs₁, fs₂, pl, σ => by
      show substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.up (fs₁ ++ fs₂) =
        (substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.up fs₁) ++
          ctorDomsT f ls (pl.map (lift 0 (fs₁.length + 1)))
            (ctorEndSubstT σ.up fs₁) fs₂
      rw [ctorDomsT_append f ls fs₁ fs₂ _ σ.up, ← List.cons_append]
      congr 1
      congr 1
      · show (pl.map (lift 0 1)).map (lift 0 fs₁.length) =
          pl.map (lift 0 (fs₁.length + 1))
        rw [map_lift_succ_merge]
  | .drec idx :: fs₁, fs₂, pl, σ => by
      show foldApps (.const f ls) (pl ++ idx.map (substT σ)) ::
          ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 (fs₁ ++ fs₂) =
        (foldApps (.const f ls) (pl ++ idx.map (substT σ)) ::
          ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 fs₁) ++
            ctorDomsT f ls (pl.map (lift 0 (fs₁.length + 1)))
              (ctorEndSubstT σ.shift1 fs₁) fs₂
      rw [ctorDomsT_append f ls fs₁ fs₂ _ σ.shift1, ← List.cons_append]
      congr 1
      congr 1
      · show (pl.map (lift 0 1)).map (lift 0 fs₁.length) =
          pl.map (lift 0 (fs₁.length + 1))
        rw [map_lift_succ_merge]
  | .drecD D _ :: fs₁, fs₂, pl, σ => by
      show substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 (fs₁ ++ fs₂) =
        (substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 fs₁) ++
          ctorDomsT f ls (pl.map (lift 0 (fs₁.length + 1)))
            (ctorEndSubstT σ.shift1 fs₁) fs₂
      rw [ctorDomsT_append f ls fs₁ fs₂ _ σ.shift1, ← List.cons_append]
      congr 1
      congr 1
      · show (pl.map (lift 0 1)).map (lift 0 fs₁.length) =
          pl.map (lift 0 (fs₁.length + 1))
        rw [map_lift_succ_merge]

/-- the `k`-th produced domain is the `k`-th field's entry form. -/
theorem ctorDomsT_getElem' (f : Nat) (ls : List Level) (pl : List (Expr Nat))
    (σ : SubstT) : (fs : List FieldT) → (k : Nat) →
    (ctorDomsT f ls pl σ fs)[k]? =
      fs[k]?.map (fun fk => match fk with
        | .plain D _ => substT (ctorEndSubstT σ (fs.take k)) D
        | .drec idx => foldApps (.const f ls)
            (pl.map (lift 0 k) ++ idx.map (substT (ctorEndSubstT σ (fs.take k))))
        | .drecD D _ => substT (ctorEndSubstT σ (fs.take k)) D)
  | [], k => by
      simp only [ctorDomsT]
      cases k with
      | zero => rfl
      | succ k => rfl
  | f0 :: fs, k => by
      cases k with
      | zero =>
          cases f0 with
          | plain D u =>
              simp only [ctorDomsT, List.getElem?_cons_zero, Option.map,
                List.take_zero, ctorEndSubstT]
          | drec idx =>
              simp only [ctorDomsT, List.getElem?_cons_zero, Option.map,
                List.take_zero, ctorEndSubstT]
              rw [List.map_id'' (fun x => lift_zero_idx 0 x) pl]
          | drecD D idx =>
              simp only [ctorDomsT, List.getElem?_cons_zero, Option.map,
                List.take_zero, ctorEndSubstT]
      | succ k =>
          cases f0 with
          | plain D u =>
              simp only [ctorDomsT, List.getElem?_cons_succ]
              rw [ctorDomsT_getElem' f ls (pl.map (lift 0 1)) σ.up fs k]
              congr 1
              funext fk
              cases fk with
              | plain D' u' => rfl
              | drec idx =>
                  show foldApps (.const f ls)
                      ((pl.map (lift 0 1)).map (lift 0 k) ++
                        idx.map (substT (ctorEndSubstT σ.up (fs.take k)))) =
                    foldApps (.const f ls)
                      (pl.map (lift 0 (k + 1)) ++
                        idx.map (substT (ctorEndSubstT σ
                          ((FieldT.plain D u :: fs).take (k + 1)))))
                  congr 1
                  congr 1
                  · rw [map_lift_succ_merge]
              | drecD D' idx => rfl
          | drec idx =>
              simp only [ctorDomsT, List.getElem?_cons_succ]
              rw [ctorDomsT_getElem' f ls (pl.map (lift 0 1)) σ.shift1 fs k]
              congr 1
              funext fk
              cases fk with
              | plain D' u' => rfl
              | drec idx2 =>
                  show foldApps (.const f ls)
                      ((pl.map (lift 0 1)).map (lift 0 k) ++
                        idx2.map (substT (ctorEndSubstT σ.shift1 (fs.take k)))) =
                    foldApps (.const f ls)
                      (pl.map (lift 0 (k + 1)) ++
                        idx2.map (substT (ctorEndSubstT σ
                          ((FieldT.drec idx :: fs).take (k + 1)))))
                  congr 1
                  congr 1
                  · rw [map_lift_succ_merge]
              | drecD D' idx2 => rfl
          | drecD D idx =>
              simp only [ctorDomsT, List.getElem?_cons_succ]
              rw [ctorDomsT_getElem' f ls (pl.map (lift 0 1)) σ.shift1 fs k]
              congr 1
              funext fk
              cases fk with
              | plain D' u' => rfl
              | drec idx2 =>
                  show foldApps (.const f ls)
                      ((pl.map (lift 0 1)).map (lift 0 k) ++
                        idx2.map (substT (ctorEndSubstT σ.shift1 (fs.take k)))) =
                    foldApps (.const f ls)
                      (pl.map (lift 0 (k + 1)) ++
                        idx2.map (substT (ctorEndSubstT σ
                          ((FieldT.drecD D idx :: fs).take (k + 1)))))
                  congr 1
                  congr 1
                  · rw [map_lift_succ_merge]
              | drecD D' idx2 => rfl

/-- `freeBvarRef` distributes over an application spine. -/
theorem freeBvarRef_foldApps (base d : Nat) :
    (args : List (Expr Nat)) → (h : Expr Nat) →
    freeBvarRef base d (foldApps h args) =
      (freeBvarRef base d h || args.any (fun x => freeBvarRef base d x))
  | [], h => by simp [foldApps]
  | x :: xs, h => by
      show freeBvarRef base d (foldApps (.app h x) xs) = _
      rw [freeBvarRef_foldApps base d xs (.app h x)]
      simp only [freeBvarRef, List.any_cons]
      rw [Bool.or_assoc]

/-- a plain field's stored domain is constant-closed in the base env:
    its typing is carried by `FieldsTyT`. -/
theorem fieldsTyT_constsIn {E : ResolvedEnv} {n : Nat} {idxTel : Nat → Expr Nat} :
    {Γ : LCtx} → {k : Nat} → {fs : List FieldT} → {res : List (Expr Nat)} →
    FieldsTyT E n idxTel Γ k fs res →
    ∀ {i : Nat} {D u}, fs[i]? = some (FieldT.plain D u) → ConstsIn E D
  | _, _, _, _, .nil _ _ _ _, i, D, u, h => by cases h
  | _, _, _, _, .plain _ _ D₀ u₀ _ _ hD tl, i, D, u, h => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at h
          obtain ⟨rfl, rfl⟩ := FieldT.plain.inj (Option.some.inj h)
          exact hasTyT_constsIn hD
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          exact fieldsTyT_constsIn tl h
  | _, _, _, _, .drec _ _ _ _ _ _ tl, i, D, u, h => by
      cases i with
      | zero => simp at h
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          exact fieldsTyT_constsIn tl h
  | _, _, _, _, .drecD _ _ _ _ _ _ _ tl, i, D, u, h => by
      cases i with
      | zero => simp at h
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          exact fieldsTyT_constsIn tl h

/-- mirror conversion preserves the list length. -/
theorem mirrorsConvT_length {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {ms ps : List (Expr Nat × Level)} →
    MirrorsConvT E n Γ ms ps → ms.length = ps.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ tl =>
      by simp only [List.length_cons]
         exact congrArg Nat.succ (mirrorsConvT_length tl)

/-! ## (5) `policyPi` injectivity and spine facts -/

/-- `policyPi`'s peel is the telescope prefix plus the body's own peel. -/
theorem peelPisAll_policyPi :
    (xs : List (Expr Nat)) → (b : Expr Nat) →
    peelPisAll (policyPi xs b) = (xs ++ (peelPisAll b).1, (peelPisAll b).2)
  | [], b => by
      show peelPisAll b = ((peelPisAll b).1, (peelPisAll b).2)
      exact (Prod.eta _).symm
  | x :: xs, b => by
      show peelPisAll (.pi x (policyPi xs b)) = _
      simp only [peelPisAll]
      rw [peelPisAll_policyPi xs b]
      rfl

/-- a non-`pi` head peels to itself. -/
theorem peelPisAll_not_pi {e : Expr Nat} (h : ∀ A B, e ≠ .pi A B) :
    peelPisAll e = ([], e) := by
  cases e with
  | pi A B => exact absurd rfl (h A B)
  | _ => rfl

/-- telescoped `pi`s are injective once the bodies cannot be `pi`s. -/
theorem policyPi_inj_of_not_pi {xs ys : List (Expr Nat)} {b c : Expr Nat}
    (hb : ∀ A B, b ≠ .pi A B) (hc : ∀ A B, c ≠ .pi A B)
    (h : policyPi xs b = policyPi ys c) : xs = ys ∧ b = c := by
  have hpeel := congrArg peelPisAll h
  rw [peelPisAll_policyPi, peelPisAll_policyPi, peelPisAll_not_pi hb,
    peelPisAll_not_pi hc] at hpeel
  rw [List.append_nil, List.append_nil] at hpeel
  exact Prod.mk.inj hpeel

/-! ## (6) `ConstsIn`/`occursConst` under `substT` and `lift` -/

/-- a `bvar`-valued `substT` preserves constant membership. -/
theorem constsIn_substT_bvar {E : ResolvedEnv} {σ : SubstT}
    (hσ : ∀ i, ∃ j, σ i = .bvar j) : {e : Expr Nat} →
    ConstsIn E e → ConstsIn E (substT σ e)
  | .bvar i, _ => by
      obtain ⟨j, hj⟩ := hσ i
      show ConstsIn E (σ i); rw [hj]; trivial
  | .sort _, h => h
  | .const _ _, h => h
  | .app f x, h => ⟨constsIn_substT_bvar hσ h.1, constsIn_substT_bvar hσ h.2⟩
  | .lam a b, h => ⟨constsIn_substT_bvar hσ h.1,
      constsIn_substT_bvar (substT_bvar_up hσ) h.2⟩
  | .pi a b, h => ⟨constsIn_substT_bvar hσ h.1,
      constsIn_substT_bvar (substT_bvar_up hσ) h.2⟩
  | .letE a v b, h => ⟨constsIn_substT_bvar hσ h.1,
      constsIn_substT_bvar hσ h.2.1,
      constsIn_substT_bvar (substT_bvar_up hσ) h.2.2⟩
  | .lit _, h => h

/-- a constant outside the environment does not occur in a
    constant-closed expression. -/
theorem constsIn_not_occurs {E : ResolvedEnv} {f : Nat} (hf : E.members f = none) :
    {e : Expr Nat} → ConstsIn E e → occursConst f e = false
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r _, h => by
      obtain ⟨m, hm⟩ := h
      show decide (r = f) = false
      rw [decide_eq_false_iff_not]
      rintro rfl; rw [hf] at hm; exact Option.noConfusion hm
  | .app g x, h => by
      show (occursConst f g || occursConst f x) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨constsIn_not_occurs hf h.1, constsIn_not_occurs hf h.2⟩
  | .lam a b, h => by
      show (occursConst f a || occursConst f b) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨constsIn_not_occurs hf h.1, constsIn_not_occurs hf h.2⟩
  | .pi a b, h => by
      show (occursConst f a || occursConst f b) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨constsIn_not_occurs hf h.1, constsIn_not_occurs hf h.2⟩
  | .letE a v b, h => by
      show (occursConst f a || occursConst f v || occursConst f b) = false
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
      exact ⟨⟨constsIn_not_occurs hf h.1, constsIn_not_occurs hf h.2.1⟩,
        constsIn_not_occurs hf h.2.2⟩
  | .lit t, h => by
      cases t with
      | zero =>
          show litOccurs f 0 = false
          show decide (f = 1) = false
          rw [decide_eq_false_iff_not]
          rintro rfl
          obtain ⟨m, hm⟩ := h; rw [hf] at hm; exact Option.noConfusion hm
      | succ t =>
          show litOccurs f (t + 1) = false
          show (decide (f = 1) || decide (f = 2)) = false
          rw [Bool.or_eq_false_iff]
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [decide_eq_false_iff_not]
            rintro rfl
            obtain ⟨m, hm⟩ := h1; rw [hf] at hm; exact Option.noConfusion hm
          · rw [decide_eq_false_iff_not]
            rintro rfl
            obtain ⟨m, hm⟩ := h2; rw [hf] at hm; exact Option.noConfusion hm

/-- `occursConst` distributes over `policyPi`. -/
theorem occursConst_policyPi (f : Nat) :
    (xs : List (Expr Nat)) → (b : Expr Nat) →
    occursConst f (policyPi xs b) = (xs.any (occursConst f) || occursConst f b)
  | [], b => by simp [policyPi]
  | x :: xs, b => by
      show occursConst f (.pi x (policyPi xs b)) = _
      simp only [occursConst, List.any_cons]
      rw [occursConst_policyPi f xs b, Bool.or_assoc]

/-- the motive domain mentions the family: its inner binder's domain
    is the literal family application. -/
theorem occursConst_policyMotiveType {E : ResolvedEnv} (family : PolicyFamilyView E)
    (pol : EliminationPolicy) :
    occursConst family.ref (policyMotiveType family pol) = true := by
  simp only [policyMotiveType]
  rw [occursConst_policyPi]
  simp only [occursConst]
  rw [occursConst_foldApps]
  simp only [occursConst]
  simp

/-- `lift` distributes over a folded spine. -/
theorem lift_foldApps (c k : Nat) :
    (args : List (Expr Nat)) → (h : Expr Nat) →
    lift c k (foldApps h args) = foldApps (lift c k h) (args.map (lift c k))
  | [], h => rfl
  | x :: xs, h => by
      show lift c k (foldApps (.app h x) xs) = _
      rw [lift_foldApps c k xs (.app h x)]
      rfl

/-- `lift` preserves the head constructor's non-`sort`-ness through a
    spine: a `foldApps` over a non-`sort` head is never a sort. -/
theorem foldApps_ne_sort_of_head {h : Expr Nat} {s : Level}
    (hh : ∀ u, h ≠ .sort u) :
    (args : List (Expr Nat)) → foldApps h args ≠ .sort s
  | [] => by
      show h ≠ .sort s
      exact hh s
  | x :: xs => by
      show foldApps (.app h x) xs ≠ .sort s
      exact foldApps_ne_sort_of_head (fun u h' => Expr.noConfusion h') xs

/-! ## (7) the scoped theorem: locator, pins, and the mask sieve -/

/-- `shift1` preserves bvar-valuedness. -/
theorem substT_bvar_shift1 {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) :
    ∀ i, ∃ j, σ.shift1 i = .bvar j := fun i => by
  obtain ⟨j, hj⟩ := hσ i
  exact ⟨j + 1, by show lift 0 1 (σ i) = _; rw [hj, lift_zero_one_bvar]⟩

/-- `SubstT.id` is bvar-valued. -/
theorem substT_id_bvar : ∀ i, ∃ j, SubstT.id i = .bvar j := fun i => ⟨i, rfl⟩

/-- `ctorEndSubstT` of a bvar-valued substitution is bvar-valued. -/
theorem ctorEndSubstT_bvar {σ : SubstT} (hσ : ∀ i, ∃ j, σ i = .bvar j) :
    (fs : List FieldT) → ∀ i, ∃ j, ctorEndSubstT σ fs i = .bvar j
  | [], i => hσ i
  | .plain _ _ :: fs, i => ctorEndSubstT_bvar (substT_bvar_up hσ) fs i
  | .drec _ :: fs, i => ctorEndSubstT_bvar (substT_bvar_shift1 hσ) fs i
  | .drecD _ _ :: fs, i => ctorEndSubstT_bvar (substT_bvar_shift1 hσ) fs i

/-- a `freeBvarRef` hit at a `true` mask position is impossible. -/
theorem freeBvarRef_substT_mask_false {p : Nat} {recs : List Bool} {e : Expr Nat}
    (hp : p < recs.length) (hrec : recs[p] = true) :
    freeBvarRef p 0 (substT (maskSubst recs) e) = false := by
  cases hb : freeBvarRef p 0 (substT (maskSubst recs) e) with
  | false => rfl
  | true =>
      obtain ⟨q, _, hq2⟩ := freeBvarRef_mask (d := 0) hb
      have hf := unplainIdx_eq_flag_false recs q p hq2 hp
      rw [hrec] at hf
      exact hf

/-- every `bvar` in the parameter locals sits at or above the field offset. -/
theorem freeBvarRef_paramLocals {t np k : Nat} (ht : t < k) :
    (policyParameterLocals np k).any (fun x => freeBvarRef t 0 x) = false := by
  rw [List.any_eq_false]
  intro e he
  simp only [policyParameterLocals, List.mem_map, List.mem_reverse,
    List.mem_range] at he
  obtain ⟨i, _, rfl⟩ := he
  simp only [freeBvarRef, Nat.add_zero, decide_eq_true_eq]
  show i + k ≠ t
  omega

/-- the mask list's `k-1-j`-th flag is the `j`-th field's `isRec`. -/
theorem mask_flag_getElem {fs : List FieldT} {k j : Nat}
    (hj : j < k) (hk : k ≤ fs.length) :
    ((fs.take k).reverse.map FieldT.isRec)[k - 1 - j]? = some fs[j].isRec := by
  have hlen : (fs.take k).length = k := by
      rw [List.length_take]; exact Nat.min_eq_left hk
  have hrev := List.getElem?_reverse (i := k - 1 - j) (l := fs.take k)
      (by rw [hlen]; omega)
  rw [List.getElem?_map, hrev]
  have hpos : (fs.take k).length - 1 - (k - 1 - j) = j := by rw [hlen]; omega
  rw [hpos, List.getElem?_take, if_pos hj,
    List.getElem?_eq_getElem (by omega : j < fs.length), Option.map_some']

/-! ## (8) the scoped discharge

    The spine helpers, the `occursConst` first-position pin, the
    `EnvWfT` group locator, the view↔skeleton correspondence, and the
    main theorem. -/

/-- `peelPisAll` is injective (its body component is never a `pi`). -/
theorem peelPisAll_inj : (e e' : Expr Nat) → peelPisAll e = peelPisAll e' → e = e' := by
  intro e
  induction e with
  | bvar i => intro e' h; cases e' <;> simp_all [peelPisAll]
  | sort l => intro e' h; cases e' <;> simp_all [peelPisAll]
  | const r ls => intro e' h; cases e' <;> simp_all [peelPisAll]
  | app f x ihf ihx => intro e' h; cases e' <;> simp_all [peelPisAll]
  | lam A B ihA ihB => intro e' h; cases e' <;> simp_all [peelPisAll]
  | pi A B ihA ihB =>
      intro e' h
      cases e' with
      | pi A' B' =>
          simp only [peelPisAll, Prod.mk.injEq, List.cons.injEq] at h
          obtain ⟨⟨rfl, hB⟩, h2⟩ := h
          exact congrArg _ (ihB _ (Prod.ext hB h2))
      | _ => simp_all [peelPisAll]
  | letE A v B ihA ihv ihB => intro e' h; cases e' <;> simp_all [peelPisAll]
  | lit t => intro e' h; cases e' <;> simp_all [peelPisAll]

/-- the motive domain mentions the family head literally. -/
theorem occursConst_motTyT (f : Nat) (ls : List Level)
    (params indices : List (Expr Nat × Level)) (wM : Level) :
    occursConst f (motTyT f ls params indices wM) = true := by
  simp only [motTyT, famLocalsT]
  rw [occursConst_policyPi]
  simp only [occursConst]
  rw [occursConst_foldApps]
  simp only [occursConst]
  simp

/-- `TelTyT` domains are constant-closed in the env. -/
theorem telTyT_constsIn {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {ds : List (Expr Nat × Level)} →
    TelTyT E n Γ ds → ∀ {D u}, (D, u) ∈ ds → ConstsIn E D
  | _, _, .nil _, _, _, h => by cases h
  | _, _, .cons _ D₀ u₀ ds hD tl, D, u, h => by
      cases h with
      | head => exact hasTyT_constsIn hD
      | tail _ h' => exact telTyT_constsIn tl h'

/-- a `map Prod.fst` element is a telescope domain. -/
theorem fst_mem_of_mem_map {α β : Type} {e : α} {ds : List (α × β)}
    (h : e ∈ ds.map Prod.fst) : ∃ u, (e, u) ∈ ds := by
  simp only [List.mem_map] at h
  obtain ⟨⟨e', u'⟩, hm', he⟩ := h
  exact ⟨u', he ▸ hm'⟩

/-- the first `occursConst`-true position is unique across equal lists. -/
theorem occursConst_first_eq {f : Nat}
    {pre_a post_a pre_g post_g : List (Expr Nat)} {ma mg : Expr Nat}
    (h : pre_a ++ ma :: post_a = pre_g ++ mg :: post_g)
    (ha : ∀ e ∈ pre_a, occursConst f e = false)
    (hma : occursConst f ma = true)
    (hg : ∀ e ∈ pre_g, occursConst f e = false)
    (hmg : occursConst f mg = true) :
    pre_a.length = pre_g.length := by
  rw [List.append_eq_append_iff] at h
  rcases h with ⟨a', hpg, hrest⟩ | ⟨c', hxs, hrest⟩
  · rcases Nat.lt_trichotomy pre_a.length pre_g.length with hlt | heq | hgt
    · exfalso
      have hpos : 0 < a'.length := by
        have hlen := congrArg List.length hpg
        simp only [List.length_append] at hlen
        omega
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_length_pos hpos
      rw [List.cons_append] at hrest
      obtain ⟨rfl, -⟩ := List.cons.inj hrest
      have hmem : ma ∈ pre_g := by
        rw [hpg]; exact List.mem_append_right _ (List.mem_cons_self _ _)
      have hf := hg _ hmem
      rw [hma] at hf
      exact Bool.noConfusion hf
    · exact heq
    · exfalso
      have hlen := congrArg List.length hpg
      simp only [List.length_append] at hlen
      omega
  · rcases Nat.lt_trichotomy pre_g.length pre_a.length with hlt | heq | hgt
    · exfalso
      have hpos : 0 < c'.length := by
        have hlen := congrArg List.length hxs
        simp only [List.length_append] at hlen
        omega
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_length_pos hpos
      rw [List.cons_append] at hrest
      obtain ⟨rfl, -⟩ := List.cons.inj hrest
      have hmem : mg ∈ pre_a := by
        rw [hxs]; exact List.mem_append_right _ (List.mem_cons_self _ _)
      have hf := ha _ hmem
      rw [hmg] at hf
      exact Bool.noConfusion hf
    · exact heq.symm
    · exfalso
      have hlen := congrArg List.length hxs
      simp only [List.length_append] at hlen
      omega

/-- THE LOCATOR: an `.inductiveM` member of a scoped environment sits at the
    head of some group node. -/
theorem envWfT_locate_inductive {f : Nat} {fm : CheckedMember} :
    {E : ResolvedEnv} → (hW : EnvWfT E) → hW.InScope →
    E.members f = some fm → fm.mclass = .inductiveM →
    ∃ (E₀ : ResolvedEnv) (ctors : List (Nat × CheckedMember)) (rr : Nat)
      (rm : CheckedMember),
      Nonempty (GroupInScopeT E₀ f fm ctors rr rm) ∧
      Ann.EnvSub E₀ E ∧ E₀.members f = none ∧
      (∀ r m b, E₀.members r = some m → m.body = some b → ConstsIn E₀ b) ∧
      (∀ r m, (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → E.members r = some m) := by
  intro E hW
  induction hW with
  | empty =>
      intro _ hp _
      simp [emptyEnv] at hp
  | @«axiom» arity E₀ r₀ A u hE hfresh hA hcl hlvl ih =>
      intro hI hp hc
      by_cases hfr : f = r₀
      · subst hfr
        rw [members_extend_eq] at hp
        obtain rfl := Option.some.inj hp
        exact MemberClass.noConfusion hc
      · rw [members_extend_ne E₀ r₀ ⟨.axiomM, arity, A, none⟩ f hfr] at hp
        obtain ⟨E₁, ctors, rr, rm, hg, hsub, hfn, hbody, hmems⟩ := ih hI hp hc
        exact ⟨E₁, ctors, rr, rm, hg,
          fun r m h => members_extend_preserved hfresh r m (hsub r m h), hfn, hbody,
          fun r m hin => members_extend_preserved hfresh r m (hmems r m hin)⟩
  | definition E₀ r₀ A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      intro hI hp hc
      by_cases hfr : f = r₀
      · subst hfr
        rw [members_extend_eq] at hp
        obtain rfl := Option.some.inj hp
        exact MemberClass.noConfusion hc
      · rw [members_extend_ne E₀ r₀ ⟨.definitionM, 0, A, some v⟩ f hfr] at hp
        obtain ⟨E₁, ctors, rr, rm, hg, hsub, hfn, hbody, hmems⟩ := ih hI hp hc
        exact ⟨E₁, ctors, rr, rm, hg,
          fun r m h => members_extend_preserved hfresh r m (hsub r m h), hfn, hbody,
          fun r m hin => members_extend_preserved hfresh r m (hmems r m hin)⟩
  | thm E₀ r₀ A p₀ hE hfresh hA hp0 hclA hclp hlvlA hlvlp ih =>
      intro hI hp hc
      by_cases hfr : f = r₀
      · subst hfr
        rw [members_extend_eq] at hp
        obtain rfl := Option.some.inj hp
        exact MemberClass.noConfusion hc
      · rw [members_extend_ne E₀ r₀ ⟨.theoremM, 0, A, some p₀⟩ f hfr] at hp
        obtain ⟨E₁, ctors, rr, rm, hg, hsub, hfn, hbody, hmems⟩ := ih hI hp hc
        exact ⟨E₁, ctors, rr, rm, hg,
          fun r m h => members_extend_preserved hfresh r m (hsub r m h), hfn, hbody,
          fun r m hin => members_extend_preserved hfresh r m (hmems r m hin)⟩
  | «opaque» E₀ r₀ A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      intro hI hp hc
      by_cases hfr : f = r₀
      · subst hfr
        rw [members_extend_eq] at hp
        obtain rfl := Option.some.inj hp
        exact MemberClass.noConfusion hc
      · rw [members_extend_ne E₀ r₀ ⟨.opaqueM, 0, A, some v⟩ f hfr] at hp
        obtain ⟨E₁, ctors, rr, rm, hg, hsub, hfn, hbody, hmems⟩ := ih hI hp hc
        exact ⟨E₁, ctors, rr, rm, hg,
          fun r m h => members_extend_preserved hfresh r m (hsub r m h), hfn, hbody,
          fun r m hin => members_extend_preserved hfresh r m (hmems r m hin)⟩
  | group E₀ f₀ fm₀ ctors₀ rr₀ rm₀ E' hE hfam hctors hrec hmem ih =>
      intro hI hp hc
      obtain ⟨hI₀, ⟨g⟩⟩ := hI
      rcases groupMembersT_cases hmem hp with hin | hE₀
      · obtain ⟨m', hmem', hmeq⟩ := hin
        rcases List.mem_cons.mp hmem' with hhead | hrest
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
          subst hmeq
          exact ⟨E₀, ctors₀, rr₀, rm₀, ⟨g⟩,
            fun r m h => Rcic.Model.PS.groupMembersT_preserve hmem r m h,
            groupMembersT_head_fresh hmem,
            fun r m b hm hb => envWfT_body_constsIn hE hm hb,
            fun r m hin => Rcic.Model.PS.groupMembersT_installed hmem hin⟩
        · rcases List.mem_append.mp hrest with hc' | hrr'
          · have hcm := hctors (f, m') hc'
            subst hmeq
            rw [hcm] at hc
            exact MemberClass.noConfusion hc
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hrr')
            subst hmeq
            rw [hrec] at hc
            exact MemberClass.noConfusion hc
      · obtain ⟨E₁, ctors, rr, rm, hg, hsub, hfn, hbody, hmems⟩ := ih hI₀ hE₀ hc
        exact ⟨E₁, ctors, rr, rm, hg,
          fun r m h => Rcic.Model.PS.groupMembersT_preserve hmem r m (hsub r m h), hfn, hbody,
          fun r m hin => Rcic.Model.PS.groupMembersT_preserve hmem r m (hmems r m hin)⟩


/-- the `ctorFieldsT` telescope peels to `ctorDomsT` and the family-headed result. -/
theorem peelPisAll_ctorFieldsT (f : Nat) (ls : List Level) :
    (pl : List (Expr Nat)) → (σ : SubstT) → (fs : List FieldT) → (res : List (Expr Nat)) →
    peelPisAll (ctorFieldsT f ls pl σ fs res) =
      (ctorDomsT f ls pl σ fs,
        foldApps (.const f ls)
          (pl.map (lift 0 fs.length) ++ res.map (substT (ctorEndSubstT σ fs))))
  | pl, σ, [], res => by
      simp only [ctorFieldsT, ctorDomsT, ctorEndSubstT, List.map_nil, List.length_nil]
      rw [List.map_id'' (fun x => lift_zero_idx 0 x),
        peelPisAll_not_pi
          (fun A B => foldApps_notPi _ (fun _ _ h => Expr.noConfusion h) A B)]
  | pl, σ, .plain D u :: fs, res => by
      have ih := peelPisAll_ctorFieldsT f ls (pl.map (lift 0 1)) σ.up fs res
      simp only [ctorFieldsT, peelPisAll, ih, ctorDomsT, List.length_cons, ctorEndSubstT,
        map_lift_succ_merge]
  | pl, σ, .drec idx :: fs, res => by
      have ih := peelPisAll_ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res
      simp only [ctorFieldsT, peelPisAll, ih, ctorDomsT, List.length_cons, ctorEndSubstT,
        map_lift_succ_merge]
  | pl, σ, .drecD D idx :: fs, res => by
      have ih := peelPisAll_ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res
      simp only [ctorFieldsT, peelPisAll, ih, ctorDomsT, List.length_cons, ctorEndSubstT,
        map_lift_succ_merge]

/-- `policyRecursorType`'s peel, flattened. -/
theorem peelPisAll_policyRecursorType {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (mins : List (Expr Nat)) (pol : EliminationPolicy) :
    peelPisAll (policyRecursorType fam mins pol) =
      (fam.parameters ++ policyMotiveType fam pol :: mins ++
          fam.indices.mapIdx (fun j T => lift j (mins.length + 1) T) ++
          [foldApps (.const fam.ref (policyFamilyLevels fam))
            (policyParameterLocals fam.parameters.length
              (mins.length + 1 + fam.indices.length) ++ policyLocals fam.indices.length)],
        foldApps (.bvar (mins.length + fam.indices.length + 1))
          ((List.range fam.indices.length).reverse.map (fun i => .bvar (i + 1)) ++ [.bvar 0])) := by
  simp only [policyRecursorType]
  rw [peelPisAll_policyPi]
  simp only [peelPisAll]
  rw [peelPisAll_policyPi, peelPisAll_policyPi]
  simp only [peelPisAll]
  rw [peelPisAll_not_pi
    (fun A B => foldApps_notPi _ (fun _ _ h => Expr.noConfusion h) A B)]
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append]

/-- `lift 0 k` of a `bvar` cannot hit a target below `k`. -/
theorem freeBvarRef_lift_bvar {t k i : Nat} (h : t < k) :
    freeBvarRef t 0 (lift 0 k (Expr.bvar i : Expr Nat)) = false := by
  have h1 : lift 0 k (Expr.bvar i : Expr Nat) = .bvar (i + k) := by
    simp only [lift]; rw [if_pos (Nat.zero_le i)]
  rw [h1]
  simp only [freeBvarRef, Nat.add_zero, decide_eq_false_iff_not]
  omega

/-- `lift`-mapped `policyLocals` never hit a target below `k`. -/
theorem freeBvarRef_policyLocals_lift {t n k : Nat} (h : t < k) :
    ((policyLocals n).map (lift 0 k)).any (fun x => freeBvarRef t 0 x) = false := by
  rw [List.any_eq_false]
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  simp only [policyLocals, List.mem_reverse, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rw [freeBvarRef_lift_bvar h]
  exact fun hb => Bool.noConfusion hb

/-- THE SIEVE: a `ctorDomsT` domain list over `policyLocals`, from `.drecD`-free
    `FieldsTyT`-typed fields, is non-IR. -/
theorem nonIR_ctorDomsT {E₀ E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {ls : List Level} {n : Nat}
    {fs : List FieldT} {res : List (Expr Nat)}
    (hsub : ∀ r m, E₀.members r = some m → E.members r = some m)
    (hbody : ∀ r m b, E₀.members r = some m → m.body = some b → ConstsIn E₀ b)
    (hf : E₀.members f = none)
    (htyped : FieldsTyT E₀ fm.arity (fun k => lift 0 k fv.idxTel) (telCtxT fv.params) 0 fs res)
    (hsnd : ∀ d ∈ fs, d.isDrecD = false) :
    NonIRFieldList E f (ctorDomsT f ls (policyLocals n) SubstT.id fs) := by
  intro j k hjk hvis
  have hlen : (ctorDomsT f ls (policyLocals n) SubstT.id fs).length = fs.length :=
    ctorDomsT_length f ls fs (policyLocals n) SubstT.id
  have hj : j.val < fs.length := hlen ▸ j.isLt
  have hk : k.val < fs.length := hlen ▸ k.isLt
  have hml : ((fs.take k.val).reverse.map FieldT.isRec).length = k.val := by
    simp only [List.length_map, List.length_reverse, List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hk)
  -- flag at the mask position k-1-j, in `?`-form
  have hflag0 := mask_flag_getElem hjk (Nat.le_of_lt hk)
  -- doms[j] is family-visible: force fs[j] to be `.drec` (hence mask flag = true)
  cases hfj : fs[j.val]'hj with
  | plain D u =>
      have hfj' : fs[j.val]? = some (.plain D u) :=
        (List.getElem?_eq_getElem hj).trans (congrArg some hfj)
      have h := ctorDomsT_getElem' f ls (policyLocals n) SubstT.id fs j.val
      rw [hfj', Option.map_some', List.getElem?_eq_getElem j.isLt] at h
      have hd2 : (ctorDomsT f ls (policyLocals n) SubstT.id fs)[j.val]'j.isLt =
          substT (ctorEndSubstT SubstT.id (fs.take j.val)) D := Option.some.inj h
      rw [ctorEndSubstT_id] at hd2
      have hvisD : FamilyVisible E f D :=
        familyVisible_substT (maskSubst_bvar _) (hd2 ▸ hvis)
      obtain ⟨fuel, hfuel⟩ := hvisD
      have hcon : ConstsIn E₀ D := fieldsTyT_constsIn htyped hfj'
      exact absurd hfuel (containsFamilyFuel_no_fam hsub hbody hf fuel D hcon)
  | drec idx =>
      -- mask flag is true
      have hflag2 : ((fs.take k.val).reverse.map FieldT.isRec)[k.val - 1 - j.val]'(by rw [hml]; omega) =
          true := by
        have h2 := hflag0
        rw [List.getElem?_eq_getElem (by rw [hml]; omega)] at h2
        have h3 := Option.some.inj h2
        rw [hfj] at h3
        exact h3
      cases hfk : fs[k.val]'hk with
      | plain D2 u2 =>
          have hfk' : fs[k.val]? = some (.plain D2 u2) :=
            (List.getElem?_eq_getElem hk).trans (congrArg some hfk)
          have h := ctorDomsT_getElem' f ls (policyLocals n) SubstT.id fs k.val
          rw [hfk', Option.map_some', List.getElem?_eq_getElem k.isLt] at h
          have hd2 : (ctorDomsT f ls (policyLocals n) SubstT.id fs)[k.val]'k.isLt =
              substT (ctorEndSubstT SubstT.id (fs.take k.val)) D2 := Option.some.inj h
          rw [hd2, ctorEndSubstT_id]
          exact freeBvarRef_substT_mask_false (by rw [hml]; omega) hflag2
      | drec idx2 =>
          have hfk' : fs[k.val]? = some (.drec idx2) :=
            (List.getElem?_eq_getElem hk).trans (congrArg some hfk)
          have h := ctorDomsT_getElem' f ls (policyLocals n) SubstT.id fs k.val
          rw [hfk', Option.map_some', List.getElem?_eq_getElem k.isLt] at h
          have hd2 : (ctorDomsT f ls (policyLocals n) SubstT.id fs)[k.val]'k.isLt =
              foldApps (.const f ls) ((policyLocals n).map (lift 0 k.val) ++
                idx2.map (substT (ctorEndSubstT SubstT.id (fs.take k.val)))) :=
            Option.some.inj h
          rw [hd2, freeBvarRef_foldApps]
          simp only [freeBvarRef, List.any_append, Bool.or_eq_false_iff, Bool.false_or]
          exact ⟨freeBvarRef_policyLocals_lift (by omega), by
            rw [List.any_eq_false]
            intro e he
            simp only [List.mem_map] at he
            obtain ⟨e', _, rfl⟩ := he
            rw [ctorEndSubstT_id, freeBvarRef_substT_mask_false (by rw [hml]; omega) hflag2]
            exact fun hb => Bool.noConfusion hb⟩
      | drecD D2 u2 =>
          have hdd := hsnd (fs[k.val]'hk) (List.getElem_mem hk)
          rw [hfk] at hdd
          exact Bool.noConfusion hdd
  | drecD D idx =>
      have hdd := hsnd (fs[j.val]'hj) (List.getElem_mem hj)
      rw [hfj] at hdd
      exact Bool.noConfusion hdd


/-! ## (9) the scoped discharge -/

/-- `admitted_group_nonIR_scoped`: an admitted recursor elimination whose
    group passes the scope test is non-IR. -/
theorem admitted_group_nonIR_scoped {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hC : hW.ScopeCheck) (hp : E.members r = some m)
    (a : RecursorEliminationAdmitted E r m) : a.NonIR := by
  obtain ⟨E₀, ctors, rr, rm, ⟨g⟩, hsub, hf, hbody, hmems⟩ :=
    envWfT_locate_inductive hW (hW.inScope_of_scopeCheck hC)
      a.family.present a.family.hasClass
  have hrrm : E.members rr = some rm :=
    hmems rr rm (List.mem_append_right _ (List.mem_singleton_self _))
  have hctors2 : ctors = g.cs.reverse.map GroupCtorT.entry :=
    g.hctors.symm.trans (List.map_reverse _ _).symm
  -- the env member at `f+1+i` is the `i`-th constructor, in candidate order
  have hctor_at : ∀ i : Nat, i < g.cs.length →
      ∃ vi : GroupCtorT E₀ a.family.ref a.family.member g.fv,
        vi ∈ g.cs ∧ E.members (a.family.ref + 1 + i) = some vi.member := by
    intro i hi
    have hi' : i < g.cs.reverse.length := by rw [List.length_reverse]; exact hi
    refine ⟨g.cs.reverse[i]'hi', List.mem_reverse.mp (List.getElem_mem hi'), ?_⟩
    apply hmems _ _
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    have hmem : (a.family.ref + 1 + i, (g.cs.reverse[i]'hi').member) ∈
        g.cs.reverse.map GroupCtorT.entry := by
      refine List.mem_map.mpr ⟨g.cs.reverse[i]'hi', List.getElem_mem hi', ?_⟩
      have href : (g.cs.reverse[i]'hi').ref = a.family.ref + 1 + i := by
        have h : (g.cs.reverse.map GroupCtorT.ref)[i]? =
            (List.range' (a.family.ref + 1) g.cs.length)[i]? :=
          congrArg (fun l : List Nat => l[i]?) g.hlayout
        rw [List.getElem?_map] at h
        rw [List.getElem?_eq_getElem hi', List.getElem?_range' (a.family.ref + 1) 1 hi] at h
        simp only [Option.map_some', Option.some.injEq, Nat.one_mul] at h
        exact h
      exact Prod.ext href rfl
    simp only [← hctors2] at hmem
    exact hmem
  rcases Nat.lt_trichotomy a.constructors.length g.cs.length with hlt | heq | hgt
  · -- `r` lands on a constructor member: the stored types' heads disagree.
    exfalso
    obtain ⟨vi, _, hmem'⟩ := hctor_at a.constructors.length hlt
    have hp2 : E.members (a.family.ref + 1 + a.constructors.length) = some m :=
      a.recursorRef ▸ hp
    have hm : m = vi.member := Option.some.inj (hp2.symm.trans hmem')
    have h1 : m.mtype = ctorTypeT a.family.ref (canonLevels a.family.member.arity)
        vi.view.mirrors vi.view.fields vi.view.res :=
      (congrArg (·.mtype) hm.symm).symm.trans vi.view.stored
    have hty : ctorTypeT a.family.ref (canonLevels a.family.member.arity)
        vi.view.mirrors vi.view.fields vi.view.res =
        policyRecursorType a.family a.minorTypes a.policy :=
      h1.symm.trans a.recursorType
    have hcontra : foldApps (.const a.family.ref (canonLevels a.family.member.arity))
          ((policyLocals vi.view.mirrors.length).map (lift 0 vi.view.fields.length) ++
            vi.view.res.map (substT (ctorEndSubstT SubstT.id vi.view.fields))) =
        foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1))
          ((List.range a.family.indices.length).reverse.map (fun i => .bvar (i + 1)) ++
            [.bvar 0]) := by
      have h2 : (peelPisAll (ctorTypeT a.family.ref (canonLevels a.family.member.arity)
            vi.view.mirrors vi.view.fields vi.view.res)).2 =
          (peelPisAll (policyRecursorType a.family a.minorTypes a.policy)).2 :=
        congrArg (fun e => (peelPisAll e).2) hty
      simp only [ctorTypeT, peelPisAll_policyPi, peelPisAll_ctorFieldsT,
        peelPisAll_policyRecursorType] at h2
      exact h2
    have hhead := congrArg Prod.fst (congrArg appsSpine hcontra)
    rw [appsSpine_foldApps, appsSpine_foldApps, appsSpine_const, appsSpine_bvar] at hhead
    exact Expr.noConfusion hhead
  · -- `r = rr`: `m = rm`; peel-pin `np_a = np_g`; per-ctor correspondence + sieve.
    have hreq : r = rr := a.recursorRef.trans (by rw [heq]; exact g.hrr.symm)
    have hm : m = rm := by
      have hp2 : E.members rr = some m := hreq ▸ hp
      exact Option.some.inj (hp2.symm.trans hrrm)
    have h1 : m.mtype = groupRecTypeT g.cs g.grec.elim :=
      (congrArg (·.mtype) hm).trans
        ((congrArg (·.mtype) g.hrm).symm.trans g.grec.stored)
    have hty : policyRecursorType a.family a.minorTypes a.policy =
        groupRecTypeT g.cs g.grec.elim := a.recursorType.symm.trans h1
    -- recursor-type peel: `.1`-projection, both sides flattened
    have hpeel : (peelPisAll (policyRecursorType a.family a.minorTypes a.policy)).1 =
        (peelPisAll (groupRecTypeT g.cs g.grec.elim)).1 :=
      congrArg (fun e => (peelPisAll e).1) hty
    rw [peelPisAll_policyRecursorType] at hpeel
    have hpeelG : (peelPisAll (groupRecTypeT g.cs g.grec.elim)).1 =
        recDomsT a.family.ref (canonLevels a.family.member.arity) g.fv.params g.fv.indices
          (policyMotiveLevel a.family.member.arity g.grec.elim)
          (g.cs.reverse.map GroupCtorT.minorData) := by
      show (peelPisAll (recTypeT a.family.ref (canonLevels a.family.member.arity)
          g.fv.params g.fv.indices (policyMotiveLevel a.family.member.arity g.grec.elim)
          (g.cs.reverse.map GroupCtorT.minorData))).1 = _
      rw [recTypeT, peelPisAll_policyPi]
      simp only [recBodyT]
      rw [peelPisAll_not_pi
        (fun A B => foldApps_notPi _ (fun _ _ h => Expr.noConfusion h) A B),
        List.append_nil]
    rw [hpeelG] at hpeel
    simp only [recDomsT, List.append_assoc, List.singleton_append] at hpeel
    -- family-telescope identity: `a`'s tele is the view's tele
    have hpeelF := policyPi_inj_of_not_pi
      (fun A B (h : Expr.sort a.family.resultLevel = .pi A B) => Expr.noConfusion h)
      (fun A B (h : Expr.sort g.fv.sort = .pi A B) => Expr.noConfusion h)
      (a.family.storedType.symm.trans g.fv.stored)
    -- `a`'s parameters are family-free (the scope's telescope is `ConstsIn E₀`)
    have ha : ∀ e ∈ a.family.parameters, occursConst a.family.ref e = false := by
      intro e he
      have hmem : e ∈ (g.fv.params ++ g.fv.indices).map Prod.fst := by
        rw [← hpeelF.1]; exact List.mem_append_left _ he
      obtain ⟨u, hu⟩ := fst_mem_of_mem_map hmem
      exact constsIn_not_occurs hf (telTyT_constsIn g.htel hu)
    have hg : ∀ e ∈ g.fv.params.map Prod.fst, occursConst a.family.ref e = false := by
      intro e he
      obtain ⟨u, hu⟩ := fst_mem_of_mem_map he
      exact constsIn_not_occurs hf (telTyT_constsIn g.htel (List.mem_append_left _ hu))
    have hnp : a.family.parameters.length = g.fv.params.length := by
      have h := occursConst_first_eq hpeel ha
        (occursConst_policyMotiveType a.family a.policy) hg
        (occursConst_motTyT a.family.ref (canonLevels a.family.member.arity)
          g.fv.params g.fv.indices (policyMotiveLevel a.family.member.arity g.grec.elim))
      rwa [List.length_map] at h
    intro i
    have hi : i.val < g.cs.length := heq ▸ i.isLt
    obtain ⟨vi, hci, hmem_i⟩ := hctor_at i.val hi
    -- `a.constructors[i] = vi.member`
    have hcp := a.constructorsPresent i
    rw [hmem_i] at hcp
    obtain hmi := Option.some.inj hcp
    -- the stored types pin `ctorTypeT = policyPi (params ++ fields) result`
    have h1 : (a.constructors[i.val]).mtype = ctorTypeT a.family.ref
        (canonLevels a.family.member.arity)
        vi.view.mirrors vi.view.fields vi.view.res :=
      (congrArg (·.mtype) hmi).symm.trans vi.view.stored
    have hst := h1.symm.trans (a.constructorViews i).storedType
    have hpeelc : (peelPisAll (ctorTypeT a.family.ref (canonLevels a.family.member.arity)
        vi.view.mirrors vi.view.fields vi.view.res)).1 =
        (peelPisAll (policyPi ((a.constructorViews i).parameters ++
            (a.constructorViews i).fields)
          (foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals (a.constructorViews i).parameters.length
              (a.constructorViews i).fields.length ++
              (a.constructorViews i).resultIndices)))).1 :=
      congrArg (fun e => (peelPisAll e).1) hst
    simp only [ctorTypeT, peelPisAll_policyPi, peelPisAll_ctorFieldsT] at hpeelc
    rw [peelPisAll_not_pi
        (fun A B => foldApps_notPi _ (fun _ _ h => Expr.noConfusion h) A B),
      List.append_nil] at hpeelc
    -- `cv.fields = ctorDomsT` by `append_inj` on the pinned parameter count
    have hl1 : vi.view.mirrors.length = g.fv.params.length :=
      mirrorsConvT_length vi.view.mirrorsConv
    have hlen : (vi.view.mirrors.map Prod.fst).length =
        (a.constructorViews i).parameters.length := by
      rw [List.length_map, hl1, ← hnp]
      exact (a.constructorViews i).parameterCount.symm
    obtain ⟨_, hflds⟩ := List.append_inj hpeelc hlen
    rw [← hflds]
    exact nonIR_ctorDomsT hsub hbody hf vi.view.typed
      (fun d hd => g.hsnd vi hci d hd)
  · -- `a.constructors[cs.length]` sits at `rr`: constructor vs recursor class.
    exfalso
    have hcp := a.constructorsPresent ⟨g.cs.length, hgt⟩
    have hmem2 : E.members (a.family.ref + 1 + g.cs.length) = some rm := g.hrr ▸ hrrm
    rw [hmem2] at hcp
    obtain hmi := Option.some.inj hcp
    have hcls1 := (a.constructorViews ⟨g.cs.length, hgt⟩).hasClass
    have hcls2 : rm.mclass = .recursorM :=
      (congrArg (·.mclass) g.hrm).symm.trans g.grec.hcls
    exact MemberClass.noConfusion
      (((congrArg (·.mclass) hmi).trans hcls1).symm.trans hcls2)

/-! ## (10) the unconditional boundary — `NonIR` modulo the phantom prefix

`admitted_group_nonIR_scoped` uses `hp : E.members r = some m` for exactly ONE
thing: `m = rm`, hence `polRec a-family = groupRecTypeT`, hence the peel-pin
`np_a = np_g`.  Dropping `hp`, the parameter/index split of `a.family` floats
freely inside `parameters ++ indices = tele_g` — and NOTHING in `a`'s evidence
recovers it:

  - the recursor-type spine is `fl`-compensating:
    `policyParameterLocals n fl`'s `i`-th entry is `bvar (n-1-i+fl)`, which at
    `fl = np_g+k-n` equals the group's `bvar (np_g-1-i+k)` for EVERY `n ≤ np_g`
    (`policyParameterLocals_eq_take_lifted` below).  The result-spine compare
    sees an identical prefix at any split.
  - `a.family`'s stored type is `fm.mtype` literally — `peelPisAll` pins
    `parameters ++ indices` but not the cut.
  - the constructor-side is `MirrorsConvT` — `TyConvT` CONVERSION, not
    equality — so `mirrors.fst` entries are conversion subjects: a `letE`-,
    β-, or δ-erased `const f` is `TyConvT`-invisible but `containsFamilyFuel`-
    VISIBLE (the fuel walk unfolds `letE` bodies and transparent defs).

Consequence: for `np_a < np_g`, `cv.fields` LEADS with `np_g − np_a`
`mirrors.fst` entries, and `a.NonIR` can fail ON THE MIRROR TAIL — a dirty
mirror `M` (say `letE _ (const f _) (.sort u)`) makes `FamilyVisible fields[j]`
fire while `ctorDoms`'s honest `bvar`-positions rebind onto mirror positions
under the shifted indexing.  The raw `∀ a, a.NonIR` is therefore FALSE in
general; the exact unconditional content is `admitted_group_nonIR_drop` —
after dropping at most `a.family.indices.length` leading entries (the phantom
prefix `np_g − np_a` is bounded by `ni_a`), the field list IS the group's
`ctorDomsT` output, which the sieve discharges. -/

/-- `NonIRFieldList` is suffix-closed. -/
theorem nonIRFieldList_drop {E : ResolvedEnv} {f : Nat} {fs : List (Expr Nat)}
    (d : Nat) (h : NonIRFieldList E f fs) :
    NonIRFieldList E f (fs.drop d) := by
  intro j k hjk hvis
  have hj : d + j.val < fs.length := by
    have h2 := j.isLt
    simp only [List.length_drop] at h2
    omega
  have hk : d + k.val < fs.length := by
    have h2 := k.isLt
    simp only [List.length_drop] at h2
    omega
  have hfb : freeBvarRef (d + k.val - 1 - (d + j.val)) 0 fs[d + k.val] = false :=
    h ⟨d + j.val, hj⟩ ⟨d + k.val, hk⟩ (Nat.add_lt_add_left hjk d)
      (by simpa using hvis)
  rw [show d + k.val - 1 - (d + j.val) = k.val - 1 - j.val by omega] at hfb
  simpa using hfb

/-- the slack witness: the parameter-locals spine at the compensating shift
    `fl = np_g + k − n` equals the prefix of the group's lifted locals — the
    spine's first `n` entries carry no information about `n`. -/
theorem policyParameterLocals_eq_take_lifted (n np_g k : Nat) (h : n ≤ np_g) :
    policyParameterLocals n (np_g + k - n) =
      ((policyLocals np_g).map (lift 0 k)).take n := by
  apply List.ext_getElem
  · simp only [policyParameterLocals, List.length_map, List.length_reverse,
      List.length_range, policyLocals, List.length_take]
    omega
  · intro i hi hi'
    simp only [policyParameterLocals, List.length_map, List.length_reverse,
      List.length_range] at hi
    simp only [policyParameterLocals, policyLocals, List.length_range,
      List.getElem_take, List.getElem_map, List.getElem_reverse, List.getElem_range]
    simp only [lift]
    rw [if_pos (Nat.zero_le _)]
    congr 1
    omega

/-- the unconditional discharge: the field list is `ctorDomsT` past a phantom
    prefix of `TyConvT`-admitted mirror domains — `a.NonIR` holds modulo at
    most `a.family.indices.length` dropped entries.  The member premise `hp`
    kills the phantom (`np_a = np_g`, prefix empty); without it this is the
    sharp theorem. -/
theorem admitted_group_nonIR_drop {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hC : hW.ScopeCheck)
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) :
    ∃ Δ ≤ a.family.indices.length,
      NonIRFieldList E a.family.ref ((a.constructorViews i).fields.drop Δ) := by
  obtain ⟨E₀, ctors, rr, rm, ⟨g⟩, hsub, hf, hbody, hmems⟩ :=
    envWfT_locate_inductive hW (hW.inScope_of_scopeCheck hC)
      a.family.present a.family.hasClass
  have hrrm : E.members rr = some rm :=
    hmems rr rm (List.mem_append_right _ (List.mem_singleton_self _))
  have hctors2 : ctors = g.cs.reverse.map GroupCtorT.entry :=
    g.hctors.symm.trans (List.map_reverse _ _).symm
  have hctor_at : ∀ i : Nat, i < g.cs.length →
      ∃ vi : GroupCtorT E₀ a.family.ref a.family.member g.fv,
        vi ∈ g.cs ∧ E.members (a.family.ref + 1 + i) = some vi.member := by
    intro i hi
    have hi' : i < g.cs.reverse.length := by rw [List.length_reverse]; exact hi
    refine ⟨g.cs.reverse[i]'hi', List.mem_reverse.mp (List.getElem_mem hi'), ?_⟩
    apply hmems _ _
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    have hmem : (a.family.ref + 1 + i, (g.cs.reverse[i]'hi').member) ∈
        g.cs.reverse.map GroupCtorT.entry := by
      refine List.mem_map.mpr ⟨g.cs.reverse[i]'hi', List.getElem_mem hi', ?_⟩
      have href : (g.cs.reverse[i]'hi').ref = a.family.ref + 1 + i := by
        have h : (g.cs.reverse.map GroupCtorT.ref)[i]? =
            (List.range' (a.family.ref + 1) g.cs.length)[i]? :=
          congrArg (fun l : List Nat => l[i]?) g.hlayout
        rw [List.getElem?_map] at h
        rw [List.getElem?_eq_getElem hi', List.getElem?_range' (a.family.ref + 1) 1 hi] at h
        simp only [Option.map_some', Option.some.injEq, Nat.one_mul] at h
        exact h
      exact Prod.ext href rfl
    simp only [← hctors2] at hmem
    exact hmem
  -- `a` cannot list more constructors than the group: slot `cs.length` is the
  -- recursor (`rm`, class `recursorM`), which `constructorViews` would
  -- contradict — no `hp` needed.
  have hle : a.constructors.length ≤ g.cs.length := by
    rcases Nat.lt_or_ge g.cs.length a.constructors.length with hgt | hle
    · have hcp := a.constructorsPresent ⟨g.cs.length, hgt⟩
      have hmem2 : E.members (a.family.ref + 1 + g.cs.length) = some rm := g.hrr ▸ hrrm
      rw [hmem2] at hcp
      obtain hmi := Option.some.inj hcp
      have hcls1 := (a.constructorViews ⟨g.cs.length, hgt⟩).hasClass
      have hcls2 : rm.mclass = .recursorM :=
        (congrArg (·.mclass) g.hrm).symm.trans g.grec.hcls
      exact MemberClass.noConfusion
        (((congrArg (·.mclass) hmi).trans hcls1).symm.trans hcls2)
    · exact hle
  -- the telescope identity needs no member premise: both stored types ARE
  -- `fm.mtype`.
  have hpeelF := policyPi_inj_of_not_pi
      (fun A B (h : Expr.sort a.family.resultLevel = .pi A B) => Expr.noConfusion h)
      (fun A B (h : Expr.sort g.fv.sort = .pi A B) => Expr.noConfusion h)
      (a.family.storedType.symm.trans g.fv.stored)
  have hi : i.val < g.cs.length := Nat.lt_of_lt_of_le i.isLt hle
  obtain ⟨vi, hci, hmem_i⟩ := hctor_at i.val hi
  have hcp := a.constructorsPresent i
  rw [hmem_i] at hcp
  obtain hmi := Option.some.inj hcp
  have h1 : (a.constructors[i.val]).mtype = ctorTypeT a.family.ref
      (canonLevels a.family.member.arity)
      vi.view.mirrors vi.view.fields vi.view.res :=
    (congrArg (·.mtype) hmi).symm.trans vi.view.stored
  have hst := h1.symm.trans (a.constructorViews i).storedType
  have hpeelc := congrArg (fun e => (peelPisAll e).1) hst
  simp only [ctorTypeT, peelPisAll_policyPi, peelPisAll_ctorFieldsT] at hpeelc
  rw [peelPisAll_not_pi
      (fun A B => foldApps_notPi _ (fun _ _ h => Expr.noConfusion h) A B),
    List.append_nil] at hpeelc
  -- `mirrors.fst ++ ctorDoms = cv.params ++ cv.fields`: split at the shared cut.
  have hnIR := nonIR_ctorDomsT (E₀ := E₀) (E := E) (f := a.family.ref)
    (fm := a.family.member) (fv := g.fv)
    (ls := canonLevels a.family.member.arity)
    (n := vi.view.mirrors.length) (fs := vi.view.fields) (res := vi.view.res)
    hsub hbody hf vi.view.typed (fun d hd => g.hsnd vi hci d hd)
  rcases List.append_eq_append_iff.mp hpeelc with ⟨a', hp', hd'⟩ | ⟨c', hp', hd'⟩
  · -- `cv.params` overruns the mirrors: `cv.fields` is a `ctorDoms` suffix.
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [List.drop_zero]
    have hd2 : (a.constructorViews i).fields =
        (ctorDomsT a.family.ref (canonLevels a.family.member.arity)
          (policyLocals vi.view.mirrors.length) SubstT.id vi.view.fields).drop a'.length :=
      (List.drop_left a' _).symm.trans (congrArg (·.drop a'.length) hd'.symm)
    rw [hd2]
    exact nonIRFieldList_drop _ hnIR
  · -- `mirrors.fst` overruns `cv.params`: `cv.fields = mirror-tail ++ ctorDoms`.
    refine ⟨c'.length, ?_, ?_⟩
    · have hl1 : vi.view.mirrors.length = g.fv.params.length :=
        mirrorsConvT_length vi.view.mirrorsConv
      have htl : a.family.parameters.length + a.family.indices.length =
          g.fv.params.length + g.fv.indices.length := by
        have h2 := congrArg List.length hpeelF.1
        simp only [List.length_append, List.length_map] at h2
        exact h2
      have hlen : c'.length + (a.constructorViews i).parameters.length =
          g.fv.params.length := by
        have h2 := congrArg List.length hp'
        simp only [List.length_append, List.length_map, hl1] at h2
        omega
      have hpc := (a.constructorViews i).parameterCount
      omega
    · have hd2 : (a.constructorViews i).fields.drop c'.length =
          ctorDomsT a.family.ref (canonLevels a.family.member.arity)
            (policyLocals vi.view.mirrors.length) SubstT.id vi.view.fields :=
        (congrArg (·.drop c'.length) hd').trans (List.drop_left _ _)
      rw [hd2]
      exact hnIR

end Rcic.Declarative
