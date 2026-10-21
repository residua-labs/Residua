import rcic.RcicSynTableBuildI

/-!
# PART 3 of the `tableOfI` team — `TableWF.congr` + `TableWF.closed` for `tableOfI`

`briefs/swe-tablei-common.md` PART 3 owns the `congr` and `closed` fields of
`TableWF (tableOfI hEnv)` — *the erased rhs is closed, and the table is
level-congruent*. This module proves both **from `hEnv : EnvWfT E` alone**,
inductively over the `tableOfI` construction of PART 1
(`rcic.RcicSynTableBuildI`, PR #7719):

* δ nodes (`axiom`/`thm`/`opaque`/`empty`) contribute nothing new;
* `.definition` prepends one `deltaRule`, discharged by `deltaRule_data` from
  `closedWf_enrichHasTyT` on the node's own `hv`;
* `.group` prepends `iotaRulesOf f fm ctors rr rm`; every rule it emits comes
  from `iotaRuleOfCtor`, whose erased rhs is `lamN K` over the ctor's minor
  applied to `iotaFieldArgs` — congruence (`iotaFieldArgs_congr`) and
  closedness (`iotaFieldArgs_closedAt`) are proved **unconditionally** for
  PART 1's `eraseTelK` index erasure (`eraseTelK_congr`,
  `eraseTelK_closedAt`), so no emitter-supplied structure is needed.

The final fields are `tableCongr_tableOfI` and `tableClosed_tableOfI`, each
with `hEnv` as its only premise. `tableCongr_append` is deliberately **not**
defined here — PART 2 (`rcic.RcicSynTableIotaWF`, PR #7718) lands it; the
single-`∀`-data induction `ruleData_tableOfI` needs no append lemma. `lamN`
is PART 1's (`RcicSynTableBuildI.lamN`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 λ-tower and leaf lemmas -/

theorem lvlEqList_refl : (xs : List ETm) → LvlEqList xs xs
  | [] => .nil
  | x :: xs => .cons (LvlEq.rfl' x) (lvlEqList_refl xs)

theorem lvlEq_lamN : (n : Nat) → {a b : ETm} → LvlEq a b → LvlEq (lamN n a) (lamN n b)
  | 0, _, _, h => h
  | n + 1, _, _, h => .lam (lvlEq_lamN n h)

/-- Pointwise `LvlEq` under `List.map`. -/
theorem lvlEqList_map {α : Type} {xs : List α} {f g : α → ETm}
    (h : ∀ x ∈ xs, LvlEq (f x) (g x)) : LvlEqList (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      exact .cons (h x (List.mem_cons_self x xs))
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- `appN` of a closed head over a pointwise-closed spine is closed. -/
theorem closedAt_appN {k : Nat} {f : ETm} (hf : ETm.ClosedAt k f)
    {xs : List ETm} (hxs : ∀ x ∈ xs, ETm.ClosedAt k x) :
    ETm.ClosedAt k (f.appN xs) := by
  induction xs generalizing f with
  | nil => exact hf
  | cons x xs ih =>
      apply ih
      · exact ⟨hf, hxs x (List.mem_cons_self x xs)⟩
      · exact fun y hy => hxs y (List.mem_cons_of_mem x hy)

/-- `n` λs pull the `ClosedAt` bound down by `n`. -/
theorem closedAt_lamN : (n K : Nat) → {t : ETm} →
    ETm.ClosedAt (n + K) t → ETm.ClosedAt K (lamN n t)
  | 0, K, _, h => Nat.zero_add K ▸ h
  | n + 1, K, _, h =>
      closedAt_lamN n (K + 1) ((by omega : n + (K + 1) = n + 1 + K) ▸ h)

/-! ## §2 Congruence and closedness of PART 1's index erasure -/

/-- `eraseLit n` is closed at every depth — only `const`s. -/
theorem eraseLit_closedAt (k n : Nat) : ETm.ClosedAt k (eraseLit n) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact ⟨True.intro, ih⟩

/-- `LvlEq` of `eraseTelK` under `eqNList` — unconditional: only `sort`/`const`
    carry levels; every `bvar`/`lit`/`letE` arm is `ls`-independent. -/
theorem eraseTelK_congr {K nargs t : Nat} {ls₁ ls₂ : List Level}
    (hls : eqNList ls₁ ls₂) (d : Nat) (e : Expr Nat) :
    LvlEq (eraseTelK K nargs t ls₁ d e) (eraseTelK K nargs t ls₂ d e) := by
  induction e generalizing d with
  | bvar k => exact LvlEq.rfl' _
  | sort l => exact .sort (instLevel_eqNList hls l)
  | const r ms => exact .const r (eqNList_map_of_pointwise (instLevel_eqNList hls) ms)
  | app f a ihf iha => exact .app (ihf d) (iha d)
  | lam a b iha ihb => exact .lam (ihb (d + 1))
  | pi a b iha ihb => exact .pi (iha d) (ihb (d + 1))
  | letE a v b iha ihv ihb => exact .star
  | lit n => exact LvlEq.rfl' _

/-- `eraseTelK` at local depth `d` is closed at `K + d` whenever `0 < K`: local
    `bvar`s stay under `d`, telescope `bvar`s re-base to `K - 1 - … < K`. -/
theorem eraseTelK_closedAt {K : Nat} (hK : 0 < K) (nargs t : Nat)
    (ls : List Level) (d : Nat) (e : Expr Nat) :
    ETm.ClosedAt (K + d) (eraseTelK K nargs t ls d e) := by
  induction e generalizing d with
  | bvar k =>
      simp only [eraseTelK]
      by_cases hkd : k < d
      · rw [if_pos hkd]; show k < K + d; omega
      · rw [if_neg hkd]; show K - 1 - (nargs + t - 1 - (k - d)) < K + d; omega
  | sort l => trivial
  | const r ms => trivial
  | app f a ihf iha => exact ⟨ihf d, iha d⟩
  | lam a b iha ihb => exact ihb (d + 1)
  | pi a b iha ihb => exact ⟨iha d, ihb (d + 1)⟩
  | letE a v b iha ihv ihb => trivial
  | lit n => exact eraseLit_closedAt _ n

/-! ## §3 Congruence and closedness of `iotaFieldArgs` -/

/-- `LvlEqList` of PART 1's erased field spine under `eqNList`: field `bvar`s
    are reflexive, `.directRec` rec-calls congruent by `hls` on the `const`
    and by `eraseTelK_congr` on the index terms. -/
theorem iotaFieldArgs_congr {rr K nargs nparams nMinors : Nat}
    {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂)
    (ds : List (Expr Nat)) (ks : List RecKind) (j : Nat) :
    LvlEqList (iotaFieldArgs rr ls₁ K nargs nparams nMinors ds ks j)
      (iotaFieldArgs rr ls₂ K nargs nparams nMinors ds ks j) := by
  induction ds generalizing ks j with
  | nil =>
      cases ks with
      | nil => exact .nil
      | cons k ks => exact .nil
  | cons A ds ih =>
      cases ks with
      | nil => exact .nil
      | cons k ks =>
          cases k with
          | plain =>
              exact .cons (.bvar _) (ih ks (j + 1))
          | directRec =>
              refine .cons (.bvar _) (.cons ?_ (ih ks (j + 1)))
              exact lvlEq_appN (.const _ hls)
                (LvlEqList.append
                  (LvlEqList.append (lvlEqList_refl _)
                    (lvlEqList_map (fun x _ => eraseTelK_congr hls 0 x)))
                  (.cons (.bvar _) .nil))

/-- Every term of `iotaFieldArgs` is closed at `K` whenever `0 < K`: field and
    prefix `bvar`s are `K - 1 - … < K`, index terms are `ClosedAt (K + 0)` by
    `eraseTelK_closedAt`. -/
theorem iotaFieldArgs_closedAt {rr K nargs nparams nMinors : Nat} (hK : 0 < K)
    (ls : List Level) (ds : List (Expr Nat)) (ks : List RecKind) (j : Nat) :
    ∀ t ∈ iotaFieldArgs rr ls K nargs nparams nMinors ds ks j,
      ETm.ClosedAt K t := by
  induction ds generalizing ks j with
  | nil =>
      intro t ht
      cases ks with
      | nil => exact absurd ht (List.not_mem_nil _)
      | cons k ks => exact absurd ht (List.not_mem_nil _)
  | cons A ds ih =>
      intro t ht
      cases ks with
      | nil => exact absurd ht (List.not_mem_nil _)
      | cons k ks =>
          cases k with
          | plain =>
              rcases List.mem_cons.mp ht with rfl | ht
              · show K - 1 - (nargs + nparams + j) < K; omega
              · exact ih ks (j + 1) t ht
          | directRec =>
              rcases List.mem_cons.mp ht with rfl | ht
              · show K - 1 - (nargs + nparams + j) < K; omega
              · rcases List.mem_cons.mp ht with rfl | ht
                · apply closedAt_appN
                  · exact True.intro
                  · intro x hx
                    simp only [List.mem_append, List.mem_map, List.mem_range,
                      List.mem_singleton] at hx
                    rcases hx with (⟨p, _, rfl⟩ | ⟨x', _, rfl⟩) | rfl
                    · show K - 1 - p < K; omega
                    · exact eraseTelK_closedAt hK nargs _ ls 0 x'
                    · show K - 1 - (nargs + nparams + j) < K; omega
                · exact ih ks (j + 1) t ht

/-! ## §4 The per-rule contract -/

/-- The per-rule contract for `TableWF.congr` + `TableWF.closed`: the two
    fields specialized to one rule. Discharged for every rule of
    `tableOfI hEnv` from `hEnv` alone (`ruleData_tableOfI`). -/
structure RuleCongrData (ρ : CRule) : Prop where
  /-- `LvlEq` of `ρ.rhs` under `eqNList`. -/
  rhsCongr : ∀ {ls ls₂ ms ms₂ : List Level}, eqNList ls ls₂ → eqNList ms ms₂ →
    LvlEq (ρ.rhs ls ms) (ρ.rhs ls₂ ms₂)
  /-- `ρ.nargs` invariant under `eqNList`. -/
  nargsCongr : ∀ {ls ls₂ : List Level}, eqNList ls ls₂ → ρ.nargs ls = ρ.nargs ls₂
  /-- `ρ.major`'s arity invariant under `eqNList`. -/
  marityCongr : ∀ {d : Nat} {m : List Level → Nat}, ρ.major = some (d, m) →
    ∀ {ls ls₂ : List Level}, eqNList ls ls₂ → m ls = m ls₂
  /-- `ρ.rhs` is closed under `0` — the erased computation only ever produces
      bound variables, constants, and levels. -/
  rhsClosed : ∀ (ls ms : List Level), ETm.ClosedAt 0 (ρ.rhs ls ms)

/-- `TableCongr` for a table whose every rule carries `RuleCongrData`. -/
theorem tableCongr_of_ruleData {tbl : List CRule}
    (h : ∀ ρ ∈ tbl, RuleCongrData ρ) : TableCongr tbl where
  rhs := fun ρ hρ {_ _ _ _} hls hms => (h ρ hρ).rhsCongr hls hms
  nargs := fun ρ hρ {_ _} hls => (h ρ hρ).nargsCongr hls
  marity := fun ρ hρ {_ _} hm {_ _} hls => (h ρ hρ).marityCongr hm hls

/-- `TableClosed` for a table whose every rule carries `RuleCongrData`. -/
theorem tableClosed_of_ruleData {tbl : List CRule}
    (h : ∀ ρ ∈ tbl, RuleCongrData ρ) :
    ∀ ρ ∈ tbl, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms) :=
  fun ρ hρ ls ms => (h ρ hρ).rhsClosed ls ms

/-- `cons` variant: a rule with `RuleCongrData` in front of a congruent table. -/
theorem tableCongr_cons_ruleData {ρ : CRule} {tbl : List CRule}
    (h : RuleCongrData ρ) (hT : TableCongr tbl) : TableCongr (ρ :: tbl) where
  rhs := fun σ hσ {_ _ _ _} hls hms => by
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · exact h.rhsCongr hls hms
    · exact hT.rhs σ hσ' hls hms
  nargs := fun σ hσ {_ _} hls => by
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · exact h.nargsCongr hls
    · exact hT.nargs σ hσ' hls
  marity := fun σ hσ {_ _} hm {_ _} hls => by
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · exact h.marityCongr hm hls
    · exact hT.marity σ hσ' hm hls

/-- `cons` variant of `tableClosed_of_ruleData`'s contravariant form. -/
theorem tableClosed_cons_ruleData {ρ : CRule} {tbl : List CRule}
    (h : RuleCongrData ρ)
    (hcl : ∀ σ ∈ tbl, ∀ ls ms, ETm.ClosedAt 0 (σ.rhs ls ms)) :
    ∀ σ ∈ ρ :: tbl, ∀ ls ms, ETm.ClosedAt 0 (σ.rhs ls ms) := by
  intro σ hσ ls ms
  rcases List.mem_cons.mp hσ with rfl | hσ'
  · exact h.rhsClosed ls ms
  · exact hcl σ hσ' ls ms

/-- Per-rule `RuleCongrData` extracted from `TableWF`. -/
theorem tableWF_data {tbl : List CRule} (hW : TableWF tbl) :
    ∀ ρ ∈ tbl, RuleCongrData ρ := fun ρ hρ =>
  { rhsCongr := fun {_ _ _ _} hls hms => hW.congr.rhs ρ hρ hls hms
    nargsCongr := fun {_ _} hls => hW.congr.nargs ρ hρ hls
    marityCongr := fun {_ _} hm {_ _} hls => hW.congr.marity ρ hρ hm hls
    rhsClosed := fun ls ms => hW.closed ρ hρ ls ms }

/-- `RuleCongrData` for `deltaRule r D_b` — from `D_b.ClosedWf`. -/
theorem deltaRule_data (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {D_b : TyP E a [] b T} (hDb : D_b.ClosedWf) :
    RuleCongrData (deltaRule r D_b) where
  rhsCongr := fun {_ _ _ _} hls hms => deltaRule_congr_rhs r D_b hls hms
  nargsCongr := fun {_ _} _ => rfl
  marityCongr := fun {_ _} hm {_ _} _ => by cases hm
  rhsClosed := fun ls ms => deltaRule_closed r hDb ls ms

/-! ## §5 `RuleCongrData` for PART 1's ι rules -/

/-- `RuleCongrData` for the literal rule `iotaRuleOfCtor` emits on its `some`
    branch: `nargs = nparams + 1 + nMinors + nindices ≥ 1`, so `K > 0` and the
    minor `bvar` `K - 1 - (nparams + 1 + ctorIdx) < K`; the field spine is
    closed/congruent by §3. No `iotaCtorSafe` premise is needed — congr and
    closed hold of the emitted syntax itself. -/
theorem iotaCtorRule_data {rr nparams nindices nMinors ctorIdx ctorRef ctorSpine : Nat}
    {fields : List (Expr Nat)} {kinds : List RecKind} :
    let nargs := nparams + 1 + nMinors + nindices
    let K := nargs + ctorSpine
    RuleCongrData { head := rr,
                    nargs := fun _ => nargs,
                    major := some (ctorRef, fun _ => ctorSpine),
                    rhs := fun ls _ =>
                      lamN K (.appN (.bvar (K - 1 - (nparams + 1 + ctorIdx)))
                        (iotaFieldArgs rr ls K nargs nparams nMinors fields kinds 0)) } := by
  intro nargs K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ls₁ ls₂ ms₁ ms₂ hls _hms
    exact lvlEq_lamN K (lvlEq_appN (.bvar _)
      (iotaFieldArgs_congr hls fields kinds 0))
  · intro _ _ _; rfl
  · intro _ _ hm _ _ _; cases hm; rfl
  · intro ls ms
    have hK : 0 < K := by omega
    exact closedAt_lamN K 0 (closedAt_appN
      (by show K - 1 - (nparams + 1 + ctorIdx) < K; omega)
      (iotaFieldArgs_closedAt hK ls fields kinds 0))

/-- Every rule `iotaRuleOfCtor` emits carries `RuleCongrData` — destructure the
    `some` branch to the `iotaCtorRule_data` literal. -/
theorem iotaRuleOfCtor_data {rr fam nparams nindices nMinors : Nat}
    {ctorIdx ctorRef : Nat} {cm : CheckedMember} {ρ : CRule}
    (h : iotaRuleOfCtor rr fam nparams nindices nMinors ctorIdx ctorRef cm =
      some ρ) :
    RuleCongrData ρ := by
  unfold iotaRuleOfCtor at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          exact iotaCtorRule_data
        · cases h

/-- Every rule of a group's `iotaRulesOf` carries `RuleCongrData` — each is an
    `iotaRuleOfCtor` `some` at some ctor index. The `mapIdx` membership is
    inverted by a custom strengthened-accumulator induction on `List.mapIdx.go`:
    every core `mapIdx` characterization lemma routes through
    `Classical.choice`, which the seal's `allowedAxioms` rejects. -/
theorem iotaRulesOf_data {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (hρ : ρ ∈ iotaRulesOf f fm ctors rr rm) : RuleCongrData ρ := by
  unfold iotaRulesOf at hρ
  dsimp only at hρ
  split at hρ
  · cases hρ
  · split at hρ
    · cases hρ
    · split at hρ
      · cases hρ
      · have H : ∀ (g : Nat → (Nat × CheckedMember) → Option CRule),
            (∀ i c r, g i c = some r → RuleCongrData r) →
            ∀ (l : List (Nat × CheckedMember)) (acc : Array (Option CRule)),
            (∀ o ∈ acc.toList, ∀ r, o = some r → RuleCongrData r) →
            ∀ r, r ∈ (List.mapIdx.go g l acc).filterMap id → RuleCongrData r := by
          intro g hg l
          induction l with
          | nil =>
              intro acc hacc r h
              rw [List.mem_filterMap] at h
              obtain ⟨o, ho, hoo⟩ := h
              exact hacc o ho r hoo
          | cons a as ih =>
              intro acc hacc r h
              refine ih (acc.push (g acc.size a)) ?_ r ?_
              · intro o ho r' hoo
                rw [Array.push_toList, List.mem_append] at ho
                rcases ho with ho | ho
                · exact hacc o ho r' hoo
                · rcases List.mem_cons.mp ho with rfl | ho
                  · exact hg _ _ _ hoo
                  · exact absurd ho (List.not_mem_nil _)
              · exact h
        exact H _ (fun i c r h => iotaRuleOfCtor_data h) ctors #[]
          (fun o ho r hoo => absurd ho (List.not_mem_nil _)) ρ hρ

/-! ## §6 `tableOfI` — the two `TableWF` fields from `EnvWfT` alone -/

/-- Per-rule `RuleCongrData` for every rule of `tableOfI hEnv`, by induction on
    the environment derivation: δ rules by `deltaRule_data` +
    `closedWf_enrichHasTyT`, group ι rules by `iotaRulesOf_data`. -/
theorem ruleData_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, RuleCongrData ρ := by
  induction hEnv with
  | empty =>
      intro ρ hρ
      rw [tableOfI_empty] at hρ
      exact absurd hρ (List.not_mem_nil _)
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfI_axiom] at hρ
      exact ih ρ hρ
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfI_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · exact deltaRule_data _ (closedWf_enrichHasTyT _ _ _ _ _ _)
      · exact ih ρ hρ'
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfI_thm] at hρ
      exact ih ρ hρ
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfI_opaque] at hρ
      exact ih ρ hρ
  | group _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfI_group] at hρ
      rcases List.mem_append.mp hρ with hL | hR
      · exact iotaRulesOf_data hL
      · exact ih ρ hR

/-- The `congr` field of `TableWF (tableOfI hEnv)` — premise is `hEnv` alone. -/
theorem tableCongr_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) :
    TableCongr (tableOfI hEnv) :=
  tableCongr_of_ruleData (ruleData_tableOfI hEnv)

/-- The `closed` field of `TableWF (tableOfI hEnv)` — premise is `hEnv` alone. -/
theorem tableClosed_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms) :=
  tableClosed_of_ruleData (ruleData_tableOfI hEnv)

/-! ## §7 Positive control — Nat's `tableOfI` -/

/-- `tableOfI natEnvUWfT` computes to the two landed constructor rules. -/
theorem tableOfI_nat : tableOfI natEnvUWfT = [natZeroRule, natSuccRule] := by
  have hg : tableOfI natEnvUWfT =
      iotaRulesOf 0 natFamMember [(1, natZeroMember), (2, natSuccMember)]
        3 natRecMemberU ++ tableOfI .empty := tableOfI_group
  rw [hg, tableOfI_empty, iotaRulesOf_nat, List.append_nil]

/-- `TableCongr` at the Nat control — via `tableCongr_tableOfI` alone. -/
theorem tableCongr_tableOfI_nat : TableCongr [natZeroRule, natSuccRule] := by
  rw [← tableOfI_nat]
  exact tableCongr_tableOfI natEnvUWfT

/-- `TableClosed` at the Nat control — via `tableClosed_tableOfI` alone. -/
theorem tableClosed_tableOfI_nat :
    ∀ ρ ∈ [natZeroRule, natSuccRule], ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms) := by
  rw [← tableOfI_nat]
  exact tableClosed_tableOfI natEnvUWfT

end Rcic.Syn
