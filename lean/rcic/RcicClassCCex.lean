import rcic.RcicSynTableK
import rcic.RcicSynFamRigid
import rcic.RcicSynTableOfIFull

/-!
# cc-classc — adversarial search for class-(c) counterexamples to the rows: the positive half

Lane cc-classc (Klaus 2026-10-23). The report is `research/rcic/classc/CLASSC_CEX.md`.
No counterexample to `TypedRowsWf` in class (c) was found. This module holds the kernel-checked
pieces the report cites. `closure_claim = 0`.

* §1 (O1, no K-like ι). Every `DerivedIota` left-hand side is a recursor applied to a
  CONSTRUCTOR-headed major (`derivedIota_lhs_ctorMajor`). So `ConvT.iota` never fires at a
  variable major (`derivedIota_no_bvar_major`). The only way a class-(c) recursor reduces at a
  proof variable `h : I ps idx` is `irr` against a constructor proof of the SAME type, then ι. The
  Lean kernel's K-like rule is not a `ConvT` rule.
* §2 (G1, generic override). Take any `TableWF` table `t` and a list `ks` of bare, nullary,
  closed, level-congruent rules with pairwise distinct heads, none of which is a constructor head
  that a major rule of `t` matches. Replacing every rule of `t` at a head of `ks` by `ks` gives a
  `TableWF` table (`tableWF_override`).
* §3 (G1 at `tableOfK`, every admitted environment). For every `EnvWfT` environment and every such
  `ks` headed at recursors, `ks ++ dropHeads (heads ks) (tableOfK hW)` is `TableWF`
  (`tableWF_override_tableOfK`). So the erased system stays confluent (`confluent_override_tableOfK`).
  Erased sort separation, erased Π-injectivity and erased family rigidity hold
  (`eqN_of_convE_sort_override`, `convE_pi_inv_override`, `convE_appN_const_inv_override`),
  WHATEVER bare ★-unfold right-hand sides class (c) is given: revealed data fields read off the
  indices, indexed recursive fields, Acc's frec unfold. The class-(c) gap of the syntactic route
  is therefore never a confluence gap. What stays open is ES, the simulation of each typed step
  under the chosen table.
* §4 (G1 into the landed rows assembly). The override table is `TableOfICompat`
  (`tableOfICompat_override`). So the landed assembly
  `typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI` instantiates at it
  (`typedRowsWf_of_override`). For a class-(c) environment the rows reduce to the `AllBelowScoped`
  pack over an override table, plus the two inputs the assembly already names. The `tableOfI`
  pack is refuted at `Eq` (`eq_not_es_tableOfI`) and the `tableOfK` pack at `RI`
  (`not_allBelowScoped_tableOfK_ri`, `RcicClassCRevealed`).
-/

namespace Rcic.Syn.ClassC

open Rcic.Declarative
open Rcic.Syn

/-! ## §1 O1 — `ConvT`'s ι needs a constructor-headed major -/

/-- every `DerivedIota` redex is a recursor call whose major is a constructor spine. -/
theorem derivedIota_lhs_ctorMajor {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (d : DerivedIota E lhs rhs) :
    ∃ (rr cr : Nat) (ls lsC : List Level) (pre sp : List (Expr Nat)) (cm : CheckedMember),
      lhs = recCall (.const rr ls) pre (foldApps (.const cr lsC) sp) ∧
        E.members cr = some cm ∧ cm.mclass = .constructorM := by
  cases d with
  | of w =>
      exact ⟨w.recRef, w.ctorRef, w.ls, w.lsC, w.preMajor, ctorSpine w, w.ctorMember, rfl,
        w.hctor, w.hctorK⟩

theorem foldApps_const_ne_bvar' {r i : Nat} {ls : List Level} :
    (xs : List (Expr Nat)) → foldApps (.const r ls) xs ≠ .bvar i := by
  intro xs h
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  exact Expr.noConfusion (congrArg Prod.fst hs)

/-- **No K-like ι.** No `DerivedIota` redex has a variable as its major. -/
theorem derivedIota_no_bvar_major {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (d : DerivedIota E lhs rhs) {r i : Nat} {ls : List Level} {pre : List (Expr Nat)}
    (h : lhs = recCall (.const r ls) pre (.bvar i)) : False := by
  obtain ⟨rr, cr, ls₀, lsC, pre₀, sp, _, rfl, _, _⟩ := derivedIota_lhs_ctorMajor d
  have hs := congrArg appsSpine h
  simp only [recCall, appsSpine_foldApps_const] at hs
  have h2 := (List.append_inj' (congrArg Prod.snd hs) rfl).2
  exact foldApps_const_ne_bvar' sp (List.singleton_inj.mp h2)

/-! ## §2 G1 — the generic override -/

/-- every rule of `t` whose head is not in `hs`. -/
def dropHeads (hs : List Nat) (t : List CRule) : List CRule :=
  t.filter (fun σ => decide (σ.head ∉ hs))

theorem mem_dropHeads {hs : List Nat} {t : List CRule} {σ : CRule} :
    σ ∈ dropHeads hs t ↔ σ ∈ t ∧ σ.head ∉ hs := by
  simp [dropHeads, List.mem_filter]

/-- a list of bare unfold rules: bare, nullary, closed, level-congruent, distinct heads. -/
structure BareOverride (ks : List CRule) : Prop where
  bare : ∀ ρ ∈ ks, ρ.major = none
  nullary : ∀ ρ ∈ ks, ∀ ls, ρ.nargs ls = 0
  closed : ∀ ρ ∈ ks, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)
  congr : TableCongr ks
  nodup : (ks.map CRule.head).Nodup

theorem eq_of_nodup_map_head : {ks : List CRule} → (ks.map CRule.head).Nodup →
    ∀ {ρ σ : CRule}, ρ ∈ ks → σ ∈ ks → ρ.head = σ.head → ρ = σ
  | [], _, _, _, hρ, _, _ => absurd hρ (List.not_mem_nil _)
  | κ :: ks, hnd, ρ, σ, hρ, hσ, hh => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hρ with rfl | hρ' <;> rcases List.mem_cons.mp hσ with rfl | hσ'
      · rfl
      · exact absurd (hh ▸ List.mem_map_of_mem CRule.head hσ') hnd.1
      · exact absurd (hh.symm ▸ List.mem_map_of_mem CRule.head hρ') hnd.1
      · exact eq_of_nodup_map_head hnd.2 hρ' hσ' hh

theorem tableCongr_of_sub {t t' : List CRule} (h : TableCongr t) (hs : ∀ ρ ∈ t', ρ ∈ t) :
    TableCongr t' where
  rhs := fun ρ hρ => h.rhs ρ (hs ρ hρ)
  nargs := fun ρ hρ => h.nargs ρ (hs ρ hρ)
  marity := fun ρ hρ => h.marity ρ (hs ρ hρ)

/-- **G1.** Replacing a `TableWF` table's rules at the heads of a bare override by the override
    keeps `TableWF`, provided no override head is a constructor that a major rule matches. -/
theorem tableWF_override {t ks : List CRule} (ht : TableWF t) (hk : BareOverride ks)
    (hrig : ∀ κ ∈ ks, ∀ σ ∈ t, ∀ {d : Nat} {m : List Level → Nat},
      σ.major = some (d, m) → κ.head ≠ d) :
    TableWF (ks ++ dropHeads (ks.map CRule.head) t) where
  congr := tableCongr_append hk.congr
    (tableCongr_of_sub ht.congr fun _ hρ => (mem_dropHeads.mp hρ).1)
  closed := by
    intro ρ hρ ls ms
    rcases List.mem_append.mp hρ with hρ | hρ
    · exact hk.closed ρ hρ ls ms
    · exact ht.closed ρ (mem_dropHeads.mp hρ).1 ls ms
  rigid := by
    intro ρ hρ d m hm σ hσ
    rcases List.mem_append.mp hρ with hρ | hρ
    · exact Option.noConfusion ((hk.bare ρ hρ).symm.trans hm)
    · have hρt := (mem_dropHeads.mp hρ).1
      rcases List.mem_append.mp hσ with hσ | hσ
      · exact hrig σ hσ ρ hρt hm
      · exact ht.rigid ρ hρt hm σ (mem_dropHeads.mp hσ).1
  bare_unique := by
    intro ρ hρ hm σ hσ hh
    rcases List.mem_append.mp hρ with hρ | hρ <;> rcases List.mem_append.mp hσ with hσ | hσ
    · exact eq_of_nodup_map_head hk.nodup hσ hρ hh
    · exact absurd (hh ▸ List.mem_map_of_mem CRule.head hρ) (mem_dropHeads.mp hσ).2
    · exact absurd (hh.symm ▸ List.mem_map_of_mem CRule.head hσ) (mem_dropHeads.mp hρ).2
    · exact ht.bare_unique ρ (mem_dropHeads.mp hρ).1 hm σ (mem_dropHeads.mp hσ).1 hh
  ctor_disjoint := by
    intro ρ hρ σ hσ hh d e m n hm hn
    rcases List.mem_append.mp hρ with hρ | hρ
    · exact Option.noConfusion ((hk.bare ρ hρ).symm.trans hm)
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact Option.noConfusion ((hk.bare σ hσ).symm.trans hn)
    exact ht.ctor_disjoint ρ (mem_dropHeads.mp hρ).1 σ (mem_dropHeads.mp hσ).1 hh hm hn
  bare_nullary := by
    intro ρ hρ hm ls
    rcases List.mem_append.mp hρ with hρ | hρ
    · exact hk.nullary ρ hρ ls
    · exact ht.bare_nullary ρ (mem_dropHeads.mp hρ).1 hm ls

/-! ## §3 G1 at `tableOfK`, for every admitted environment -/

/-- the override table at an admitted environment. -/
noncomputable def overrideTableK {E : ResolvedEnv} (hW : EnvWfT E) (ks : List CRule) :
    List CRule :=
  ks ++ dropHeads (ks.map CRule.head) (tableOfK hW)

/-- override heads are recursors of the environment. -/
def HeadsAtRecursors (E : ResolvedEnv) (ks : List CRule) : Prop :=
  ∀ κ ∈ ks, ∃ m, E.members κ.head = some m ∧ m.mclass = .recursorM

/-- a major rule of `tableOfK` matches a constructor, which is never a recursor head. -/
theorem override_rigid_tableOfK {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hrec : HeadsAtRecursors E ks) :
    ∀ κ ∈ ks, ∀ σ ∈ tableOfK hW, ∀ {d : Nat} {m : List Level → Nat},
      σ.major = some (d, m) → κ.head ≠ d := by
  intro κ hκ σ hσ d m hm hhead
  obtain ⟨mk, hmk, hmkc⟩ := hrec κ hκ
  rcases tableOfK_head_major hW σ hσ with ⟨_, _, _, htb⟩ | ⟨_, _, _, hmaj⟩
  · exact Option.noConfusion (hm.symm.trans (major_none_tableOf hW σ htb))
  · rcases hmaj with hn | ⟨d', k, md, hmaj', hd, hmc'⟩
    · exact Option.noConfusion (hm.symm.trans hn)
    · have hd' : d = d' := congrArg Prod.fst (Option.some.inj (hm.symm.trans hmaj'))
      subst hd'
      exact members_ne_of_mclass_ne hmk hd
        (fun h => MemberClass.noConfusion (hmkc.symm.trans (h.trans hmc'))) hhead

/-- **G1 at every admitted environment.** -/
theorem tableWF_override_tableOfK {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) :
    TableWF (overrideTableK hW ks) :=
  tableWF_override (tableWF_tableOfK hW) hk (override_rigid_tableOfK hW hrec)

/-- the overridden erased system is confluent (no termination is used). -/
theorem confluent_override_tableOfK {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) :
    Confluent (EStep (overrideTableK hW ks)) :=
  confluent_eStep_wf (tableWF_override_tableOfK hW hk hrec)

/-- erased sort separation under any class-(c) override. -/
theorem eqN_of_convE_sort_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) {l l' : Level}
    (h : ConvMod (EStep (overrideTableK hW ks)) LvlEq (.sort l) (.sort l')) : eqN l l' :=
  eqN_of_convE_sort_wf (tableWF_override_tableOfK hW hk hrec) h

/-- erased Π-injectivity under any class-(c) override. -/
theorem convE_pi_inv_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) {A B A' B' : ETm}
    (h : ConvMod (EStep (overrideTableK hW ks)) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep (overrideTableK hW ks)) LvlEq A A' ∧
      ConvMod (EStep (overrideTableK hW ks)) LvlEq B B' :=
  convE_pi_inv_wf (tableWF_override_tableOfK hW hk hrec) h

/-- no rule of the overridden table is headed at a family. -/
theorem noHeadRule_override_family {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hrec : HeadsAtRecursors E ks) {f : Nat} {fm : CheckedMember}
    (hf : E.members f = some fm) (hclass : fm.mclass = .inductiveM) :
    NoHeadRule (overrideTableK hW ks) f := by
  intro ρ hρ hhead
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨m, hm, hmc⟩ := hrec ρ hρ
    rw [hhead, hf] at hm
    cases hm
    exact MemberClass.noConfusion (hclass.symm.trans hmc)
  · rcases tableOfK_head_major hW ρ (mem_dropHeads.mp hρ).1 with
        ⟨m, hm, hmc, -⟩ | ⟨m, hm, hmc, -⟩ <;>
      · rw [hhead, hf] at hm
        cases hm
        exact MemberClass.noConfusion (hclass.symm.trans hmc)

/-- erased family rigidity under any class-(c) override. -/
theorem convE_appN_const_inv_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) {f : Nat} {fm : CheckedMember}
    (hf : E.members f = some fm) (hclass : fm.mclass = .inductiveM)
    {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep (overrideTableK hW ks)) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep (overrideTableK hW ks)) LvlEq) xs ys :=
  convE_appN_const_inv_wf (tableWF_override_tableOfK hW hk hrec)
    (noHeadRule_override_family hW hrec hf hclass) h

/-- the empty override is `tableOfK` itself, up to the filter. -/
theorem overrideTableK_nil {E : ResolvedEnv} (hW : EnvWfT E) :
    overrideTableK hW [] = tableOfK hW := by
  simp [overrideTableK, dropHeads]

/-! ## §4 G1 into the landed rows assembly -/

open Rcic.Declarative.KernelRowsAssembly in
/-- the override table meets the assembly's table interface. -/
theorem tableOfICompat_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) :
    TableOfICompat hW (overrideTableK hW ks) where
  sup := by
    intro ρ hρ
    refine List.mem_append_right _ (mem_dropHeads.mpr ⟨mem_tableOfK_of_mem_tableOf hW hρ, ?_⟩)
    intro hin
    obtain ⟨κ, hκ, hhead⟩ := List.mem_map.mp hin
    obtain ⟨m, hm, hmc⟩ := head_defM_build hW ρ hρ
    obtain ⟨mk, hmk, hmkc⟩ := hrec κ hκ
    rw [hhead, hm] at hmk
    cases hmk
    exact MemberClass.noConfusion (hmc.symm.trans hmkc)
  wf := tableWF_override_tableOfK hW hk hrec
  headM := by
    intro ρ hρ
    rcases List.mem_append.mp hρ with hρ | hρ
    · obtain ⟨m, hm, hmc⟩ := hrec ρ hρ
      exact ⟨m, hm, fun h => MemberClass.noConfusion (hmc.symm.trans h)⟩
    · rcases tableOfK_head_major hW ρ (mem_dropHeads.mp hρ).1 with
          ⟨m, hm, hmc, -⟩ | ⟨m, hm, hmc, -⟩
      · exact ⟨m, hm, fun h => MemberClass.noConfusion (hmc.symm.trans h)⟩
      · exact ⟨m, hm, fun h => MemberClass.noConfusion (hmc.symm.trans h)⟩

open Rcic.Declarative.KernelRowsAssembly in
/-- **the rows from an override pack.** At every admitted environment, `TypedRowsWf` follows from
    the `AllBelowScoped` pack over ANY G1 override table, with the landed assembly's two other
    inputs. -/
theorem typedRowsWf_of_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw (overrideTableK hW ks)) {n : Nat}
    (joinPi : Rcic.Declarative.NativeValleys.NativeKProjectionAudit.PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW
    (tableOfICompat_override hW hk hrec) hBel joinPi hSlot

open Rcic.Declarative.KernelRowsAssembly in
/-- sortRow alone from an override pack. -/
theorem sortRow_of_override {E : ResolvedEnv} (hW : EnvWfT E) {ks : List CRule}
    (hk : BareOverride ks) (hrec : HeadsAtRecursors E ks) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw (overrideTableK hW ks)) {n : Nat} :
    Rcic.Declarative.NativeFamilyProjection.SortRow E n :=
  sortRow_of_allBelowScoped_tableI hW (tableOfICompat_override hW hk hrec) hBel

end Rcic.Syn.ClassC

#print axioms Rcic.Syn.ClassC.derivedIota_lhs_ctorMajor
#print axioms Rcic.Syn.ClassC.derivedIota_no_bvar_major
#print axioms Rcic.Syn.ClassC.tableWF_override
#print axioms Rcic.Syn.ClassC.tableWF_override_tableOfK
#print axioms Rcic.Syn.ClassC.confluent_override_tableOfK
#print axioms Rcic.Syn.ClassC.eqN_of_convE_sort_override
#print axioms Rcic.Syn.ClassC.convE_pi_inv_override
#print axioms Rcic.Syn.ClassC.convE_appN_const_inv_override
#print axioms Rcic.Syn.ClassC.tableOfICompat_override
#print axioms Rcic.Syn.ClassC.typedRowsWf_of_override
#print axioms Rcic.Syn.ClassC.sortRow_of_override
