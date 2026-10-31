import rcic.RcicAnnEnvWf
import rcic.RcicIotaFunRecFrag

/-!
# R-NoFunRec S6 3b-pre: the admitted frec field — cc's `funRecFrag_of_admitted` question

cc's verdict on #6545 asks, before 3c: at the fired constructor of an admitted environment
(`EnvWfA` + `EnvNormEraseA`), does admission's semantic read together with erasure-normal
stored types already give `FunRecFrag`'s two new clauses, `canonTail` and `innerClean`?
This file is the measured answer:

* `canonTail` and `innerClean` ARE admission theorems at a group constructor: the stored
  type is `ctorTypeA`-built (`CtorViewA.stored`), whose `.frec` domain is `frecDomA` — a
  syntactic Π-telescope over inner binders typed in the base (`FieldsTyA.frec`), ending in
  the family at the lifted parameter locals and its indices (`frecDomA_tailParts`). Typing
  in the base plus freshness (`GroupFreshA.base`) makes every constant of the telescope
  family-free (`FieldsTyA.freeOf` through `occursConst_erase_freeOf`): `innerClean`. The
  built tail is the canonical application — `properShapeB` at the field's `top`
  (`properShapeB_erase_frecDom`): `canonTail`.
* `rigid` (`noTransparentB`) is NOT an admission theorem and is not needed: an inner binder
  is an arbitrary `HasTyA`-typed term of the base and may mention the base's definitions;
  δ can fire there. What rigidity guarded — the family surfacing by δ — cannot happen at
  an admitted group: every body reachable from the constructor's stored type belongs to
  the base, and no member body of an admitted environment mentions a reference fresh
  outside it (`envWfA_bodiesSelf`), so the δ-scan can never FIND the family
  (`containsFamilyFuel_ne_true_of_confined`).
* The verdicts therefore agree at any fuel that resolves: `admittedFrec_verdict` — the
  semantic read at an admitted group's `.frec` field is `.permitted (.recursive k)` at the
  fired indices, or `.unresolved`. What remains is fuel EXISTENCE (the δ-closure bound —
  the same typed-SN-lite residual the direct side carries,
  `RcicAnnIotaCorr.lean:1801-1804`), not a frec-specific narrowing.

Plan: `research/rcic/nofunrec/S6_PLAN.md` §3 A2 + cc's 2026-10-12 question.
`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) `Expr`-side constants, through erasure and level instantiation -/

/-- every constant of the erased term satisfies `D` — `ConstsInA`'s `Expr` twin. -/
def ConstsInE (D : Nat → Prop) : Expr Nat → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => D r
  | .app f x => ConstsInE D f ∧ ConstsInE D x
  | .lam a b => ConstsInE D a ∧ ConstsInE D b
  | .pi a b => ConstsInE D a ∧ ConstsInE D b
  | .letE a v b => ConstsInE D a ∧ ConstsInE D v ∧ ConstsInE D b
  | .lit t =>
      match t with
      | 0 => D 1
      | _ + 1 => D 1 ∧ D 2

/-- erasure forgets annotations only: the constants are the same. -/
theorem constsInE_erase (D : Nat → Prop) : (e : ExprA) → ConstsInA D e → ConstsInE D (erase e)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const _ _, h => h
  | .app _ _, ⟨hf, hx⟩ => ⟨constsInE_erase D _ hf, constsInE_erase D _ hx⟩
  | .lam _ _ _, ⟨ha, hb⟩ => ⟨constsInE_erase D _ ha, constsInE_erase D _ hb⟩
  | .pi _ _ _ _, ⟨ha, hb⟩ => ⟨constsInE_erase D _ ha, constsInE_erase D _ hb⟩
  | .letE _ _ _, ⟨ha, hv, hb⟩ =>
      ⟨constsInE_erase D _ ha, constsInE_erase D _ hv, constsInE_erase D _ hb⟩
  | .lit 0, h => h
  | .lit (_ + 1), h => h

/-- level instantiation does not touch references. -/
theorem constsInE_instantiateLevels (D : Nat → Prop) (ls : List Level) :
    (e : Expr Nat) → ConstsInE D e → ConstsInE D (instantiateLevels ls e)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const _ _, h => h
  | .app _ _, ⟨hf, hx⟩ =>
      ⟨constsInE_instantiateLevels D ls _ hf, constsInE_instantiateLevels D ls _ hx⟩
  | .lam _ _, ⟨ha, hb⟩ =>
      ⟨constsInE_instantiateLevels D ls _ ha, constsInE_instantiateLevels D ls _ hb⟩
  | .pi _ _, ⟨ha, hb⟩ =>
      ⟨constsInE_instantiateLevels D ls _ ha, constsInE_instantiateLevels D ls _ hb⟩
  | .letE _ _ _, ⟨ha, hv, hb⟩ =>
      ⟨constsInE_instantiateLevels D ls _ ha, constsInE_instantiateLevels D ls _ hv,
        constsInE_instantiateLevels D ls _ hb⟩
  | .lit 0, h => h
  | .lit (_ + 1), h => h

/-- a term whose constants all differ from `f` does not mention `f`. -/
theorem occursConst_eq_false_of_constsInE {f : Nat} :
    (e : Expr Nat) → ConstsInE (fun r => r ≠ f) e → occursConst f e = false
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r _, h => by
      simp only [occursConst, decide_eq_false h]
  | .app _ _, ⟨hf, hx⟩ => by
      simp only [occursConst, occursConst_eq_false_of_constsInE _ hf,
        occursConst_eq_false_of_constsInE _ hx, Bool.or_false]
  | .lam _ _, ⟨ha, hb⟩ => by
      simp only [occursConst, occursConst_eq_false_of_constsInE _ ha,
        occursConst_eq_false_of_constsInE _ hb, Bool.or_false]
  | .pi _ _, ⟨ha, hb⟩ => by
      simp only [occursConst, occursConst_eq_false_of_constsInE _ ha,
        occursConst_eq_false_of_constsInE _ hb, Bool.or_false]
  | .letE _ _ _, ⟨ha, hv, hb⟩ => by
      simp only [occursConst, occursConst_eq_false_of_constsInE _ ha,
        occursConst_eq_false_of_constsInE _ hv, occursConst_eq_false_of_constsInE _ hb,
        Bool.or_false]
  | .lit 0, h => by
      simp only [occursConst, litOccurs, decide_eq_false (Ne.symm h)]
  | .lit (_ + 1), h => by
      simp only [occursConst, litOccurs, decide_eq_false (Ne.symm h.1),
        decide_eq_false (Ne.symm h.2), Bool.or_false]

/-- the region-form: membership in the base and not the family. -/
def ConfinedE (E : ResolvedEnvA) (fam : Nat) (r : Nat) : Prop := domA E r ∧ r ≠ fam

/-- both predicates, pointwise. -/
private theorem constsInA_inter {P Q : Nat → Prop} :
    (e : ExprA) → ConstsInA P e → ConstsInA Q e → ConstsInA (fun r => P r ∧ Q r) e
  | .bvar _, _, _ => trivial
  | .sort _, _, _ => trivial
  | .const _ _, hP, hQ => ⟨hP, hQ⟩
  | .app _ _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨constsInA_inter _ h1 h3, constsInA_inter _ h2 h4⟩
  | .lam _ _ _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨constsInA_inter _ h1 h3, constsInA_inter _ h2 h4⟩
  | .pi _ _ _ _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨constsInA_inter _ h1 h3, constsInA_inter _ h2 h4⟩
  | .letE _ _ _, ⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩ =>
      ⟨constsInA_inter _ h1 h4, constsInA_inter _ h2 h5, constsInA_inter _ h3 h6⟩
  | .lit 0, hP, hQ => ⟨hP, hQ⟩
  | .lit (_ + 1), hP, hQ => ⟨⟨hP.1, hQ.1⟩, ⟨hP.2, hQ.2⟩⟩

/-! ## (2) admission keeps every body inside its own environment -/

/-- `domA` grows along a prefix. -/
theorem domA_of_prefix {E EA : ResolvedEnvA} (hpre : PrefixA E EA) : ∀ r, domA E r → domA EA r :=
  fun r ⟨m, hm⟩ => ⟨m, hpre r m hm⟩

/-- the single-extension step: the new member's body (if any) is typed in the base, and
    the base's bodies stay confined (`domA` grows along the extension). -/
private theorem bodiesSelf_extend {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hbodies : ∀ r' m' b', E.members r' = some m' → m'.bodyA = some b' → ConstsInA (domA E) b')
    (hnew : ∀ b', m.bodyA = some b' → ConstsInA (domA E) b') :
    ∀ r' m' b, (extendEnvA E r m).members r' = some m' → m'.bodyA = some b →
      ConstsInA (domA (extendEnvA E r m)) b := by
  have hmono : ∀ r₀, domA E r₀ → domA (extendEnvA E r m) r₀ := by
    intro r₀ ⟨m₀, hm₀⟩
    by_cases hr : r₀ = r
    · exact ⟨m, by rw [hr]; exact members_extendEnvA_self E r m⟩
    · exact ⟨m₀, by rw [members_extendEnvA_ne E r m hr]; exact hm₀⟩
  intro r' m' b hm hb
  by_cases hr : r' = r
  · subst hr; rw [members_extendEnvA_self] at hm; cases hm
    exact constsInA_mono hmono _ (hnew b hb)
  · rw [members_extendEnvA_ne E r m hr] at hm
    exact constsInA_mono hmono _ (hbodies r' m' b hm hb)

theorem envWfA_bodiesSelf {I : IotaIfaceA} :
    {EA : ResolvedEnvA} → EnvWfA I EA →
      ∀ r m b, EA.members r = some m → m.bodyA = some b → ConstsInA (domA EA) b
  | _, .empty => fun r _ _ hr => by
      rw [show emptyEnvA.members r = none from rfl] at hr; exact Option.noConfusion hr
  | _, .axiomM (arity := arity) E r A u hE hfresh hA hcl hlvl =>
      bodiesSelf_extend (envWfA_bodiesSelf hE) (fun b' hb => by
        rw [show (⟨.axiomM, arity, A, none, 0, none⟩ : CheckedMemberA).bodyA = none from rfl] at hb
        exact Option.noConfusion hb)
  | _, .definitionM E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      bodiesSelf_extend (envWfA_bodiesSelf hE) (fun b' hb => by
        rw [show (⟨.definitionM, 0, A, some v, 0, none⟩ : CheckedMemberA).bodyA = some v from rfl]
          at hb
        cases hb
        exact hasTyA_constsIn hv)
  | _, .theoremM E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      bodiesSelf_extend (envWfA_bodiesSelf hE) (fun b' hb => by
        rw [show (⟨.theoremM, 0, A, some p, 0, none⟩ : CheckedMemberA).bodyA = some p from rfl]
          at hb
        cases hb
        exact hasTyA_constsIn hp)
  | _, .opaqueM E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      bodiesSelf_extend (envWfA_bodiesSelf hE) (fun b' hb => by
        rw [show (⟨.opaqueM, 0, A, some v, 0, none⟩ : CheckedMemberA).bodyA = some v from rfl]
          at hb
        cases hb
        exact hasTyA_constsIn hv)
  | _, .group E f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh =>
      by
        have hbase := envWfA_bodiesSelf hE
        have hmono : ∀ r₀, domA E r₀ → domA (groupEnvA E f fm (cs.map GroupCtorA.entry)) r₀ :=
          fun r₀ hd => domA_of_prefix (prefixA_groupEnvA hfresh) r₀ hd
        intro r' m' b hm hb
        rcases members_groupEnvA _ r' m' hm with ⟨rfl, rfl⟩ | h | h
        · rw [hnobody] at hb; exact Option.noConfusion hb
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp h
          have hm' : m' = c.member := by
            injection hce with _ h2; exact h2.symm
          rw [hm', c.hnobody] at hb; exact Option.noConfusion hb
        · exact constsInA_mono hmono _ (hbase r' m' b h hb)
  | _, .groupRec E f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh hlayout rec hrfresh =>
      by
        have hgrp : ∀ r' m' b, (groupEnvA E f fm (cs.map GroupCtorA.entry)).members r' = some m' →
            m'.bodyA = some b → ConstsInA (domA (groupEnvA E f fm (cs.map GroupCtorA.entry))) b := by
          have hbase := envWfA_bodiesSelf hE
          have hmono : ∀ r₀, domA E r₀ →
              domA (groupEnvA E f fm (cs.map GroupCtorA.entry)) r₀ :=
            fun r₀ hd => domA_of_prefix (prefixA_groupEnvA hfresh) r₀ hd
          intro r' m' b hm hb
          rcases members_groupEnvA _ r' m' hm with ⟨rfl, rfl⟩ | h | h
          · rw [hnobody] at hb; exact Option.noConfusion hb
          · obtain ⟨c, _, hce⟩ := List.mem_map.mp h
            have hm' : m' = c.member := by
              injection hce with _ h2; exact h2.symm
            rw [hm', c.hnobody] at hb; exact Option.noConfusion hb
          · exact constsInA_mono hmono _ (hbase r' m' b h hb)
        have hmono : ∀ r₀, domA (groupEnvA E f fm (cs.map GroupCtorA.entry)) r₀ →
            domA (groupRecEnvA cs rec) r₀ := by
          intro r₀ ⟨m₀, hm₀⟩
          by_cases hr : r₀ = f + 1 + cs.length
          · subst hr; rw [hrfresh] at hm₀; exact Option.noConfusion hm₀
          · exact ⟨m₀, by rw [groupRecEnvA, members_extendEnvA_ne _ _ _ hr]; exact hm₀⟩
        intro r' m' b hm hb
        by_cases hr : r' = f + 1 + cs.length
        · subst hr; rw [groupRecEnvA, members_extendEnvA_self] at hm; cases hm
          rw [rec.hnobody] at hb; exact Option.noConfusion hb
        · rw [groupRecEnvA, members_extendEnvA_ne _ _ _ hr] at hm
          exact constsInA_mono hmono _ (hgrp r' m' b hm hb)

/-! ## (3) the δ-scan cannot find the family from a confined term -/

/-- the bodies of base members stay confined and family-free. -/
private theorem bodyConfined {E : ResolvedEnvA} {fam r : Nat} {m : CheckedMemberA} {b : ExprA}
    (hfam : E.members fam = none)
    (hbodies : ∀ r' m' b', E.members r' = some m' → m'.bodyA = some b' → ConstsInA (domA E) b')
    (hm : E.members r = some m) (hb : m.bodyA = some b) :
    ConstsInA (fun r' => domA E r' ∧ r' ≠ fam) b :=
  have h1 : ConstsInA (domA E) b := hbodies r m b hm hb
  constsInA_mono (fun r' hr => ⟨hr, by
    intro hrf; subst hrf
    obtain ⟨mm, hmm⟩ := hr
    rw [hmm] at hfam
    exact Option.noConfusion hfam⟩) b h1

/-- the erased environment unfolds a base member's transparent body to the level
    instantiation of its erasure. -/
private theorem transparentBody_eraseEnv_some {EA : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {ls : List Level} {b : ExprA} (hEA : EA.members r = some m) (hb : m.bodyA = some b)
    (htr : transparent m.mclass = true) :
    transparentBody (eraseEnv EA) r ls = some (instantiateLevels ls (erase b)) := by
  simp only [transparentBody, members_eraseEnv, hEA, Option.map_some', eraseMember, hb, htr,
    if_true, Option.map_some']

/-- nothing to unfold: a rigid member, or one with no body. -/
private theorem transparentBody_eraseEnv_none {EA : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {ls : List Level} (hEA : EA.members r = some m)
    (h : ¬(transparent m.mclass = true) ∨ m.bodyA = none) :
    transparentBody (eraseEnv EA) r ls = none := by
  simp only [transparentBody, members_eraseEnv, hEA, Option.map_some', eraseMember]
  rcases h with h | h
  · rw [if_neg h]
  · rw [h, Option.map_none']
    split <;> rfl

/-- at an admitted group, the δ-scan over a term whose constants are base members cannot
    report the family: every body it can unfold belongs to the base (members survive
    extension unchanged), and no base body mentions the fresh family. Whatever the ambient
    environment added elsewhere is unreachable — the scan only ever reads the constants the
    term itself names. -/
theorem containsFamilyFuel_ne_true_of_confined {EA E : ResolvedEnvA} {fam : Nat}
    (hpre : PrefixA E EA) (hfam : E.members fam = none)
    (hbodies : ∀ r m b, E.members r = some m → m.bodyA = some b → ConstsInA (domA E) b) :
    ∀ (fuel : Nat) (T : Expr Nat), ConstsInE (ConfinedE E fam) T →
      containsFamilyFuel (eraseEnv EA) fam fuel T ≠ some true := by
  intro fuel
  induction fuel with
  | zero => intro T _ h; exact Option.noConfusion h
  | succ fuel ih =>
      intro T hc
      cases T with
      | bvar => intro h; simp only [containsFamilyFuel] at h; exact absurd h (by simp)
      | sort => intro h; simp only [containsFamilyFuel] at h; exact absurd h (by simp)
      | lit t =>
          cases t with
          | zero =>
              exact ih _ (show ConstsInE (ConfinedE E fam) (.const 1 []) from hc)
          | succ n =>
              have hc1 := ih _ (show ConstsInE (ConfinedE E fam) (.const 1 []) from hc.1)
              have hc2 := ih _ (show ConstsInE (ConfinedE E fam) (.const 2 []) from hc.2)
              show (match containsFamilyFuel (eraseEnv EA) fam fuel (.const 2 []) with
                    | some false => containsFamilyFuel (eraseEnv EA) fam fuel litZero
                    | r => r) ≠ some true
              cases hb : containsFamilyFuel (eraseEnv EA) fam fuel (.const 2 []) with
              | none => exact fun h => Option.noConfusion h
              | some b =>
                  cases b with
                  | false => exact hc1
                  | true => exact absurd hb hc2
      | const r ls =>
          intro h
          obtain ⟨⟨m, hm⟩, hrf⟩ := hc
          have hEA : EA.members r = some m := hpre r m hm
          simp only [containsFamilyFuel, if_neg hrf] at h
          by_cases htr : transparent m.mclass = true
          · cases hb : m.bodyA with
            | none =>
                rw [transparentBody_eraseEnv_none hEA (Or.inr hb)] at h
                exact absurd h (by simp)
            | some b =>
                rw [transparentBody_eraseEnv_some hEA hb htr] at h
                exact ih _ (constsInE_instantiateLevels _ _ _
                  (constsInE_erase _ _ (bodyConfined hfam hbodies hm hb))) h
          · rw [transparentBody_eraseEnv_none hEA (Or.inl htr)] at h
            exact absurd h (by simp)
      | app f x =>
          intro h
          obtain ⟨hcf, hcx⟩ := hc
          simp only [containsFamilyFuel] at h
          split at h
          · rename_i h1; exact ih _ hcf h1
          · rename_i _; exact ih _ hcx h
          · exact absurd h (by simp)
      | lam a b =>
          intro h
          obtain ⟨hca, hcb⟩ := hc
          simp only [containsFamilyFuel] at h
          split at h
          · rename_i h1; exact ih _ hca h1
          · rename_i _; exact ih _ hcb h
          · exact absurd h (by simp)
      | pi a b =>
          intro h
          obtain ⟨hca, hcb⟩ := hc
          simp only [containsFamilyFuel] at h
          split at h
          · rename_i h1; exact ih _ hca h1
          · rename_i _; exact ih _ hcb h
          · exact absurd h (by simp)
      | letE a v b =>
          intro h
          obtain ⟨hca, ⟨hcv, hcb⟩⟩ := hc
          simp only [containsFamilyFuel] at h
          split at h
          · rename_i h1; exact ih _ hca h1
          · split at h
            · rename_i h1; exact ih _ hcv h1
            · exact ih _ hcb h
            · exact absurd h (by simp)
          · exact absurd h (by simp)

/-! ## (4) the frec field's canonical tail, from the view -/

/-- the lifted parameter locals compose along the telescope threading. -/
private theorem liftA_map_comp (pl : List ExprA) (i k : Nat) :
    (pl.map (liftA 0 i)).map (liftA 0 k) = pl.map (liftA 0 (i + k)) := by
  rw [List.map_map]
  exact List.map_congr_left fun e _ => liftA_liftA_merge k i 0 0 (Nat.zero_le 0) (by omega) e

/-- the substitution threaded through `k` inner binders. -/
def SubstA.upN : Nat → SubstA → SubstA
  | 0, σ => σ
  | k + 1, σ => SubstA.upN k σ.up

/-- a function-recursive field's domain, read through its tail: the Π-body is the family at
    the parameter locals lifted past the inner binders, followed by exactly the field's
    indices — the canonical application's spine. -/
private theorem map_liftA_zero (pl : List ExprA) : pl.map (liftA 0 0) = pl := by
  induction pl with
  | nil => rfl
  | cons a as ih => simp only [List.map, liftA_zero, ih]

theorem frecDomA_tailParts (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    (∀ d ∈ ds, FreeOfA f d.1) → (∀ a ∈ idx, FreeOfA f a) → (∀ i, FreeOfA f (σ i)) →
    ∃ xs, piBodyA (frecDomA f ls w pl σ ds idx).1 =
        foldAppsA (.const f ls) (pl.map (liftA 0 ds.length) ++ xs) ∧
      xs = idx.map (substA (SubstA.upN ds.length σ)) ∧
      xs.length = idx.length ∧ ∀ x ∈ xs, FreeOfA f x
  | [], pl, σ, _, hidx, hσ => by
      refine ⟨idx.map (substA σ), ?_, rfl, List.length_map idx (substA σ), fun x hx => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact constsInA_substA a σ (hidx a ha) hσ⟩
      simp only [frecDomA, List.length_nil, map_liftA_zero]
      rw [piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
  | (D, u) :: ds, pl, σ, hds, hidx, hσ => by
      simp only [frecDomA, piBodyA]
      obtain ⟨xs, ih, hdef, hlen, hfree⟩ :=
        frecDomA_tailParts f ls w idx ds (pl.map (liftA 0 1)) σ.up
          (fun d hd => hds d (List.mem_cons_of_mem _ hd)) hidx
          (constsInA_substA.up σ hσ)
      refine ⟨xs, ?_, hdef, hlen, hfree⟩
      rw [ih, liftA_map_comp, List.length_cons, Nat.add_comm 1 ds.length]

/-- one step of the fields telescope, per field kind — the inner call stays folded. -/
private theorem ctorFieldsA_cons_plain (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (D : ExprA) (u : Level) (fs : List FieldA) (pl : List ExprA) (σ : SubstA) :
    ctorFieldsA f ls w pl σ (.plain D u :: fs) res =
      (.pi (substA σ D) u (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.up fs res).1
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.up fs res).2,
        .imax u (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.up fs res).2) := rfl

private theorem ctorFieldsA_cons_drec (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (ix : List ExprA) (fs : List FieldA) (pl : List ExprA) (σ : SubstA) :
    ctorFieldsA f ls w pl σ (.drec ix :: fs) res =
      (.pi (foldAppsA (.const f ls) (pl ++ ix.map (substA σ))) w
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2,
        .imax w (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2) := rfl

private theorem ctorFieldsA_cons_frec (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA) (fs : List FieldA)
    (pl : List ExprA) (σ : SubstA) :
    ctorFieldsA f ls w pl σ (.frec B uB Bs idx :: fs) res =
      (.pi (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1
          (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).2
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2,
        .imax (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).2
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2) := rfl

private theorem ctorFieldsA_cons_drecD (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (D : ExprA) (ix : List ExprA) (fs : List FieldA) (pl : List ExprA) (σ : SubstA) :
    ctorFieldsA f ls w pl σ (.drecD D ix :: fs) res =
      (.pi (substA σ D) w
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1
          (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2,
        .imax w (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).2) := rfl

/-- the substitution threading never leaves the bvar fragment: every image is a binder. -/
private theorem bvarImages_up {σ : SubstA} (h : ∀ i, ∃ j, σ i = .bvar j) :
    ∀ i, ∃ j, σ.up i = .bvar j := by
  intro i
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i' =>
      obtain ⟨j, hj⟩ := h i'
      exact ⟨j + 1, by simp only [SubstA.up_succ, hj, liftA]; rw [if_pos (Nat.zero_le j)]⟩

private theorem bvarImages_shift1 {σ : SubstA} (h : ∀ i, ∃ j, σ i = .bvar j) :
    ∀ i, ∃ j, σ.shift1 i = .bvar j := by
  intro i
  obtain ⟨j, hj⟩ := h i
  refine ⟨j + 1, ?_⟩
  simp only [SubstA.shift1, hj, liftA]
  rw [if_pos (Nat.zero_le j)]

private theorem bvarImages_upN {σ : SubstA} (h : ∀ i, ∃ j, σ i = .bvar j) :
    (k : Nat) → ∀ i, ∃ j, SubstA.upN k σ i = .bvar j
  | 0, _ => h _
  | k + 1, _ => bvarImages_upN (bvarImages_up h) k _

/-- the `.frec` field's stored domain, at its position in the built telescope: the domain
    list's entry at the field's index is the frec dom at the parameter locals lifted past
    the earlier fields, at a substitution whose images are all binders (the stored type is
    closed under it; in particular every image is family-free). -/
theorem ctorFieldsA_dom_frec (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA) :
    (fsPre fsRest : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    (∀ i, ∃ j, σ i = .bvar j) →
    ∃ σ', (∀ i, ∃ j, σ' i = .bvar j) ∧
      ((piDomsA (ctorFieldsA f ls w pl σ (fsPre ++ FieldA.frec B uB Bs idx :: fsRest)
        res).1)[fsPre.length]? =
        some (frecDomA f ls w (pl.map (liftA 0 fsPre.length)) σ' ((B, uB) :: Bs) idx).1)
  | [], _, pl, σ, hb => by
      refine ⟨σ, hb, ?_⟩
      rw [List.nil_append, ctorFieldsA_cons_frec]
      simp only [piDomsA, List.length_nil, map_liftA_zero, List.getElem?_cons_zero]
  | .plain D u :: fsPre', fsRest, pl, σ, hb => by
      obtain ⟨σ'', hbv'', ih⟩ :=
        ctorFieldsA_dom_frec f ls w res B uB Bs idx fsPre' fsRest (pl.map (liftA 0 1)) σ.up
          (bvarImages_up hb)
      refine ⟨σ'', hbv'', ?_⟩
      rw [List.cons_append, ctorFieldsA_cons_plain]
      simp only [piDomsA, List.length_cons, List.getElem?_cons_succ]
      rw [ih, liftA_map_comp, Nat.add_comm 1 fsPre'.length]
  | .drec ix :: fsPre', fsRest, pl, σ, hb => by
      obtain ⟨σ'', hbv'', ih⟩ :=
        ctorFieldsA_dom_frec f ls w res B uB Bs idx fsPre' fsRest (pl.map (liftA 0 1))
          σ.shift1 (bvarImages_shift1 hb)
      refine ⟨σ'', hbv'', ?_⟩
      rw [List.cons_append, ctorFieldsA_cons_drec]
      simp only [piDomsA, List.length_cons, List.getElem?_cons_succ]
      rw [ih, liftA_map_comp, Nat.add_comm 1 fsPre'.length]
  | .frec B' uB' Bs' ix :: fsPre', fsRest, pl, σ, hb => by
      obtain ⟨σ'', hbv'', ih⟩ :=
        ctorFieldsA_dom_frec f ls w res B uB Bs idx fsPre' fsRest (pl.map (liftA 0 1))
          σ.shift1 (bvarImages_shift1 hb)
      refine ⟨σ'', hbv'', ?_⟩
      rw [List.cons_append, ctorFieldsA_cons_frec]
      simp only [piDomsA, List.length_cons, List.getElem?_cons_succ]
      rw [ih, liftA_map_comp, Nat.add_comm 1 fsPre'.length]
  | .drecD D ix :: fsPre', fsRest, pl, σ, hb => by
      obtain ⟨σ'', hbv'', ih⟩ :=
        ctorFieldsA_dom_frec f ls w res B uB Bs idx fsPre' fsRest (pl.map (liftA 0 1))
          σ.shift1 (bvarImages_shift1 hb)
      refine ⟨σ'', hbv'', ?_⟩
      rw [List.cons_append, ctorFieldsA_cons_drecD]
      simp only [piDomsA, List.length_cons, List.getElem?_cons_succ]
      rw [ih, liftA_map_comp, Nat.add_comm 1 fsPre'.length]

/-- the frec field's own typing facts, read off the fields typing at its position: the inner
    binders and the indices are family-free (typed in the base, where the family is fresh). -/
private theorem fieldsTyA_frec_freeOf {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} {f : Nat} (hfresh : E.members f = none) :
    (fsPre : List FieldA) → {B : ExprA} → {uB : Level} → {Bs : List (ExprA × Level)} →
    {idx : List ExprA} → {fsRest : List FieldA} → {res : List ExprA} → {Γ : LCtxA} → {k : Nat} →
    FieldsTyA E I n idxTel Γ k (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) res →
    (∀ d ∈ (B, uB) :: Bs, FreeOfA f d.1) ∧ ∀ a ∈ idx, FreeOfA f a
  | [], _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom _ => by
      obtain ⟨h1, h2⟩ := hdom.freeOf hfresh
      refine ⟨fun d hd => h1 (plainA d) (List.mem_map_of_mem _ hd), h2⟩
  | .plain _ _ :: fsPre, _, _, _, _, _, _, _, _, .plain _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_freeOf hfresh fsPre tl
  | .drec _ :: fsPre, _, _, _, _, _, _, _, _, .drec _ _ _ _ _ _ tl =>
      fieldsTyA_frec_freeOf hfresh fsPre tl
  | FieldA.frec _ _ _ _ :: fsPre, _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_freeOf hfresh fsPre tl
  | .drecD _ _ :: fsPre, _, _, _, _, _, _, _, _, .drecD _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_freeOf hfresh fsPre tl

/-! ## (4b) 3b plumbing: `hidxLen` from the view's own typing

`viewTy_args_piTel_length` (`RcicAnnViewTy`, downstream of this file) counts an
argument list against a sort-telescope; the frec field's indices are typed against
the LIFTED index telescope (`FieldsTyA.frec`'s inner walk ends in `ArgsTyA` at
`liftA 0 k fv.idxTelA`), so the count needs the substituted form. The two lemmas
below are that one lemma's upstream form; `idxLen_of_fieldsTyA_frec` is the
discharge of `admittedFrec_shape`'s `hidxLen` premise. -/

/-- a lift by `k` at cutoff `c` is the substitution shifting every index at or
    above `c` up by `k` (the binder case's `SubstA.up` shift agrees pointwise). -/
private theorem substA_shiftAt_up (c k i : Nat) :
    SubstA.up (fun j => if c ≤ j then ExprA.bvar (j + k) else ExprA.bvar j) i =
      if c + 1 ≤ i then ExprA.bvar (i + k) else ExprA.bvar i := by
  cases i with
  | zero => rfl
  | succ i' =>
      show liftA 0 1 (if c ≤ i' then ExprA.bvar (i' + k) else ExprA.bvar i')
        = if c + 1 ≤ i' + 1 then ExprA.bvar (i' + 1 + k) else ExprA.bvar (i' + 1)
      split
      · next h =>
          have hc : c + 1 ≤ i' + 1 := by omega
          rw [if_pos hc]
          simp only [liftA, Nat.zero_le, ite_true]
          congr 1
          omega
      · next h =>
          have hc : ¬ c + 1 ≤ i' + 1 := by omega
          rw [if_neg hc]
          simp only [liftA, Nat.zero_le, ite_true]

private theorem substA_shiftAt_eq_liftA (c k : Nat) : (e : ExprA) →
    substA (fun i => if c ≤ i then ExprA.bvar (i + k) else ExprA.bvar i) e = liftA c k e := by
  intro e
  induction e generalizing c with
  | bvar i =>
      by_cases h : c ≤ i
      · simp only [substA, h, if_pos, liftA]
      · simp only [substA, h, if_neg, liftA]
  | sort _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx => simp only [substA, liftA, ihf c, ihx c]
  | lam a u b iha ihb =>
      have hup : SubstA.up (fun j => if c ≤ j then ExprA.bvar (j + k) else ExprA.bvar j)
          = fun i => if c + 1 ≤ i then ExprA.bvar (i + k) else ExprA.bvar i :=
        funext (substA_shiftAt_up c k)
      simp only [substA, liftA, iha c]
      rw [hup]
      congr 1
      exact ihb (c + 1)
  | pi a u b v iha ihb =>
      have hup : SubstA.up (fun j => if c ≤ j then ExprA.bvar (j + k) else ExprA.bvar j)
          = fun i => if c + 1 ≤ i then ExprA.bvar (i + k) else ExprA.bvar i :=
        funext (substA_shiftAt_up c k)
      simp only [substA, liftA, iha c]
      rw [hup]
      congr 1
      exact ihb (c + 1)
  | letE a w b iha ihw ihb =>
      have hup : SubstA.up (fun j => if c ≤ j then ExprA.bvar (j + k) else ExprA.bvar j)
          = fun i => if c + 1 ≤ i then ExprA.bvar (i + k) else ExprA.bvar i :=
        funext (substA_shiftAt_up c k)
      simp only [substA, liftA, iha c, ihw c]
      rw [hup]
      congr 1
      exact ihb (c + 1)
  | lit _ => rfl

/-- an argument list typed against a SUBSTITUTED sort-telescope is as long as the
    telescope — `viewTy_args_piTel_length`'s form at an arbitrary substitution
    (the frec field's indices are typed at the lifted index telescope). -/
private theorem argsTyA_substPiTelA_length {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {T : ExprA}→ {asr : List ExprA}→
      ArgsTyA E I n Γ T asr →
      ∀ (ds : List (ExprA × Level)) (w s : Level) (τ : SubstA),
        T = substA τ (piTelA ds (.sort w) s).1 → asr.length = ds.length := by
  intro Γ T asr h
  induction h with
  | nil l =>
      intro ds w s τ hT
      cases ds with
      | nil => rfl
      | cons d ds' =>
          simp only [piTelA, substA] at hT
          exact ExprA.noConfusion hT
  | cons A u B v a asl ha tl ih =>
      intro ds w s τ hT
      cases ds with
      | nil =>
          simp only [piTelA, substA] at hT
          exact ExprA.noConfusion hT
      | cons d ds' =>
          obtain ⟨D, u'⟩ := d
          simp only [piTelA, substA] at hT
          injection hT with hA _ hB _
          subst hA
          subst hB
          have hstep := ih ds' w s
            (fun i => substA (SubstA.cons a SubstA.id) (SubstA.up τ i))
            ((instantiate0A_eq_substA_cons a (substA (SubstA.up τ)
              (piTelA ds' (.sort w) s).1)).trans
              (substA_substA (SubstA.cons a SubstA.id) (SubstA.up τ)
                (piTelA ds' (.sort w) s).1))
          show asl.length + 1 = ds'.length + 1
          exact congrArg (fun x => x + 1) hstep
/-- the inner plain walk ends in `ArgsTyA` at the lifted index telescope: the
    frec field's indices are as many as the family's. -/
private theorem fieldsTyA_plain_idxLen {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} :
    {Γ : LCtxA}→{k : Nat}→{fs : List FieldA}→{idx : List ExprA}→
      (∀ x ∈ fs, ∃ d u, x = FieldA.plain d u) →
      FieldsTyA E I n (fun j => liftA 0 j fv.idxTelA) Γ k fs idx →
      idx.length = fv.indices.length := by
  intro Γ k fs idx hall h
  induction h with
  | nil Γ' k' res hres =>
      have h2 : liftA 0 k' fv.idxTelA =
          substA (fun i => if 0 ≤ i then ExprA.bvar (i + k') else ExprA.bvar i) fv.idxTelA :=
        (substA_shiftAt_eq_liftA 0 k' _).symm
      have h3 : substA (fun i => if 0 ≤ i then ExprA.bvar (i + k') else ExprA.bvar i) fv.idxTelA
          = substA (fun i => ExprA.bvar (i + k')) fv.idxTelA :=
        substA_ext (fun i => by simp) _
      exact argsTyA_substPiTelA_length hres fv.indices fv.sort (.succ fv.sort) _
        (h2.trans h3)
  | plain Γ' k' D u fs' res hD tl ih =>
      exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
  | drec Γ' k' idxl fs' res hidx tl ih =>
      exact absurd (hall _ (List.mem_cons_self _ _)) (by
        rintro ⟨d, u, h'⟩
        exact FieldA.noConfusion h')
  | frec Γ' k' B uB Bs idxl fs' res hdom tl ih =>
      exact absurd (hall _ (List.mem_cons_self _ _)) (by
        rintro ⟨d, u, h'⟩
        exact FieldA.noConfusion h')
  | drecD Γ' k' D idxl fs' res hidx tl ih =>
      exact absurd (hall _ (List.mem_cons_self _ _)) (by
        rintro ⟨d, u, h'⟩
        exact FieldA.noConfusion h')

/-- THE 3b DISCHARGE: at a typed `.frec` field, `hidxLen` (the field's indices against the
    family's) is the view's own typing — `FieldsTyA.frec`'s inner walk counts them along the
    index telescope. This is the premise `admittedFrec_shape` carried until 3b. -/
theorem idxLen_of_fieldsTyA_frec {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} :
    (fsPre : List FieldA) → {B : ExprA}→{uB : Level}→{Bs : List (ExprA × Level)}→
    {idx : List ExprA}→{fsRest : List FieldA}→{res : List ExprA}→{Γ : LCtxA}→{k : Nat}→
      FieldsTyA E I n (fun j => liftA 0 j fv.idxTelA) Γ k
        (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) res →
      idx.length = fv.indices.length
  | [], _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom _ =>
      fieldsTyA_plain_idxLen (fun x hx => by
        obtain ⟨d, u, rfl⟩ := List.mem_map.mp hx
        exact ⟨_, _, rfl⟩) hdom
  | .plain _ _ :: fsPre, _, _, _, _, _, _, _, _, .plain _ _ _ _ _ _ _ tl =>
      idxLen_of_fieldsTyA_frec fsPre tl
  | .drec _ :: fsPre, _, _, _, _, _, _, _, _, .drec _ _ _ _ _ _ tl =>
      idxLen_of_fieldsTyA_frec fsPre tl
  | FieldA.frec _ _ _ _ :: fsPre, _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ _ tl =>
      idxLen_of_fieldsTyA_frec fsPre tl
  | .drecD _ _ :: fsPre, _, _, _, _, _, _, _, _, .drecD _ _ _ _ _ _ _ tl =>
      idxLen_of_fieldsTyA_frec fsPre tl

/-! ## (5) the answer: canonTail and innerClean at an admitted `.frec` field -/
/-- the lifted parameter locals are the exact locals at their depth. -/
theorem exactParamLocals_paramLocalsA (n m : Nat) :
    exactParamLocals (((paramLocalsA n).map (liftA 0 m)).map erase) (m + n - 1) = true := by
  induction n generalizing m with
  | zero => simp only [paramLocalsA, List.map, exactParamLocals]
  | succ n ih =>
      have hhead : (n + m : Nat) = m + (n + 1) - 1 := by omega
      have htop : m + (n + 1) - 1 - 1 = m + n - 1 := by omega
      simp only [paramLocalsA, List.map, liftA, if_pos (Nat.zero_le n), erase,
        exactParamLocals, hhead, htop]
      rw [ih m]
      rfl

/-- the erased frec tail is the canonical family application: the family head, saturated
    at parameters and indices, exact parameter locals at its depth, canonical levels, and
    family-free indices. -/
theorem properShapeB_erase_frecTail {f : Nat} {ls : List Level} {nuniv n nindices m : Nat}
    {plL xs : List ExprA} (hls : ls = canonLevelsA nuniv) (hpl : plL.length = n)
    (hplform : plL = (paramLocalsA n).map (liftA 0 m))
    (hxs : xs.length = nindices) (hfree : ∀ x ∈ xs, FreeOfA f x) :
    properShapeB f nuniv n nindices (m + n - 1)
        (erase (foldAppsA (.const f ls) (plL ++ xs))) = true := by
  have hlenE : (plL.map erase).length = n := by rw [List.length_map, hpl]
  have hargs : ((plL ++ xs).map erase).length = n + nindices := by
    rw [List.map_append, List.length_append, List.length_map, List.length_map, hpl, hxs]
  have htake : ((plL ++ xs).map erase).take n =
      ((paramLocalsA n).map (liftA 0 m)).map erase := by
    rw [List.map_append, List.take_left' hlenE, hplform]
  have hdrop : ((plL ++ xs).map erase).drop n = xs.map erase :=
    by rw [List.map_append, List.drop_left' hlenE]
  simp only [properShapeB, erase_foldAppsA, appsSpine_foldApps, appsSpine, List.nil_append,
    hargs, htake, hdrop, hls, canonLevelsA, decide_eq_true_eq, exactParamLocals_paramLocalsA,
    decide_True, Bool.true_and]
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  simp only [occursConst_erase_freeOf x (hfree x hx), Bool.not_false]

/-- the leading-Π count is the leading-domains count. -/
private theorem piCountA_piDomsA : (X : ExprA) → piCountA X = (piDomsA X).length
  | .pi _ _ B _ => by
      rw [piCountA, piDomsA, List.length_cons, piCountA_piDomsA B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- THE ANSWER to cc's 2026-10-12 question: at an admitted group constructor's
    function-recursive field, the erased stored domain carries the frec fragment's two new
    clauses — `innerClean` by typing in the base plus freshness, `canonTail` by
    construction. The domain's Π-count is the inner-binder count, and the whole-domain
    Π-spine/tail is the canonical family application at the field's depth. `hidxLen` (the
    field's indices against the family's) is DERIVED from the view's own `hdom` typing
    (`idxLen_of_fieldsTyA_frec` above — 3b plumbing). -/
theorem admittedFrec_shape {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (gc : GroupCtorA I E f fm fv) (hfresh : E.members f = none)
    {fsPre : List FieldA} {B : ExprA} {uB : Level} {Bs : List (ExprA × Level)}
    {idx : List ExprA} {fsRest : List FieldA}
    (hfields : gc.view.fields = fsPre ++ FieldA.frec B uB Bs idx :: fsRest) :
    ∃ T, ((piDomsA gc.member.mtypeA).map erase)[fm.nparamsA + fsPre.length]? = some T ∧
      piCount T = 1 + Bs.length ∧
      ((piDomsOf T).all fun D => !occursConst f D) = true ∧
      properShapeB f fm.arity fm.nparamsA fv.indices.length
        (piCount T + (fm.nparamsA + fsPre.length) - 1) (piTailOf T) = true := by
  -- the field's indices are as many as the family's (the view's own typing)
  have hidxLen : idx.length = fv.indices.length :=
    idxLen_of_fieldsTyA_frec fsPre (by rw [← hfields]; exact gc.view.typed)
  -- the view's typing facts at the frec field
  have ⟨hdsFree, hidxFree⟩ := fieldsTyA_frec_freeOf (I := I) (E := E) hfresh fsPre
    (B := B) (uB := uB) (Bs := Bs) (idx := idx) (fsRest := fsRest) (res := gc.view.res)
    (hfields ▸ gc.view.typed)
  -- mirrors = the family's parameters
  have hmir : gc.view.mirrors.length = fm.nparamsA := by
    rw [gc.view.mirrorsConv.length, fv.nparams]
  -- the field's position, through the built telescope
  obtain ⟨σ', hbvar, hdom⟩ :=
    ctorFieldsA_dom_frec f (canonLevelsA fm.arity) fv.sort gc.view.res B uB Bs idx fsPre
      fsRest (paramLocalsA fm.nparamsA) SubstA.id
      (fun i => ⟨i, rfl⟩)
  -- the stored type is the built one: mirrors, then the fields' domains
  have hpiDoms : piDomsA gc.member.mtypeA =
      gc.view.mirrors.map Prod.fst ++
        piDomsA (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
          (paramLocalsA gc.view.mirrors.length) SubstA.id gc.view.fields gc.view.res).1 := by
    rw [gc.view.stored, ctorTypeA, piDomsA_piTelA]
  have hget : ((piDomsA gc.member.mtypeA).map erase)[fm.nparamsA + fsPre.length]? =
      some (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        ((B, uB) :: Bs) idx).1) := by
    have hle : (List.map erase (List.map Prod.fst gc.view.mirrors)).length ≤
        fm.nparamsA + fsPre.length := by
      rw [List.length_map, List.length_map, hmir]
      exact Nat.le_add_right fm.nparamsA fsPre.length
    rw [hpiDoms, List.map_append, List.getElem?_append_right hle]
    rw [List.length_map, List.length_map, hmir, Nat.add_sub_cancel_left,
      List.getElem?_map, hfields, hdom]
    rfl
  refine ⟨erase (frecDomA f (canonLevelsA fm.arity) fv.sort
    ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' ((B, uB) :: Bs) idx).1,
    hget, ?_, ?_, ?_⟩
  · -- the Π-count
    have hparts := frecDomA_parts f (canonLevelsA fm.arity) fv.sort idx hidxFree
      ((B, uB) :: Bs) ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
      hdsFree (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact constsInA_liftA fsPre.length q 0 (paramLocalsA_freeOf f _ q hq))
      (fun i => by
        obtain ⟨j, hj⟩ := hbvar i
        rw [hj]; trivial)
    rw [piCountA_erase, piCountA_piDomsA, hparts.1]
    simp only [List.length_cons]
    omega
  · -- innerClean
    have hparts := frecDomA_parts f (canonLevelsA fm.arity) fv.sort idx hidxFree
      ((B, uB) :: Bs) ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
      hdsFree (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact constsInA_liftA fsPre.length q 0 (paramLocalsA_freeOf f _ q hq))
      (fun i => by
        obtain ⟨j, hj⟩ := hbvar i
        rw [hj]; trivial)
    have hspine : piDomsOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        ((B, uB) :: Bs) idx).1) =
        (piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
          ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
          ((B, uB) :: Bs) idx).1).map erase :=
      (congrArg Prod.fst (piTelE_piDomsOf
        (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
          ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
          ((B, uB) :: Bs) idx).1))).symm.trans
        (piTelE_erase_fst (frecDomA f (canonLevelsA fm.arity) fv.sort
          ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
          ((B, uB) :: Bs) idx).1)
    rw [hspine, List.all_eq_true]
    intro D hD
    obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hD
    simp only [occursConst_erase_freeOf D' (hparts.2.1 D' hD'), Bool.not_false]
  · -- canonTail
    obtain ⟨xs, htail, hxsdef, hxslen, hxsfree⟩ :=
      frecDomA_tailParts f (canonLevelsA fm.arity) fv.sort idx ((B, uB) :: Bs)
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        hdsFree hidxFree
        (fun i => by
          obtain ⟨j, hj⟩ := hbvar i
          rw [hj]; trivial)
    have hpiTail : piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        ((B, uB) :: Bs) idx).1) =
        erase (foldAppsA (ExprA.const f (canonLevelsA fm.arity))
          ((paramLocalsA fm.nparamsA).map
            (liftA 0 (fsPre.length + (1 + Bs.length))) ++ xs)) := by
      rw [show piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
          ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
          ((B, uB) :: Bs) idx).1) =
          erase (piBodyA (frecDomA f (canonLevelsA fm.arity) fv.sort
            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
            ((B, uB) :: Bs) idx).1) from
        (congrArg Prod.snd (piTelE_piDomsOf _)).symm.trans (piTelE_erase _).2,
        htail, List.length_cons, liftA_map_comp,
        show fsPre.length + (Bs.length + 1) = fsPre.length + (1 + Bs.length) from by omega]
    have hcanon := properShapeB_erase_frecTail (f := f) (ls := canonLevelsA fm.arity)
      (nuniv := fm.arity) (n := fm.nparamsA) (nindices := fv.indices.length)
      (m := fsPre.length + (1 + Bs.length)) (plL := (paramLocalsA fm.nparamsA).map
        (liftA 0 (fsPre.length + (1 + Bs.length)))) (xs := xs) rfl
      (by rw [List.length_map, paramLocalsA_length])
      rfl
      (hxslen.trans hidxLen) hxsfree
    rw [hpiTail]
    have htop : (1 + Bs.length) + (fm.nparamsA + fsPre.length) - 1 =
        fsPre.length + (1 + Bs.length) + fm.nparamsA - 1 := by omega
    have hpc : piCount (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        ((B, uB) :: Bs) idx).1) = 1 + Bs.length := by
      have hparts2 := frecDomA_parts f (canonLevelsA fm.arity) fv.sort idx hidxFree ((B, uB) :: Bs)
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        hdsFree (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA fsPre.length q 0 (paramLocalsA_freeOf f _ q hq))
        (fun i => by
          obtain ⟨j, hj⟩ := hbvar i
          rw [hj]; trivial)
      rw [piCountA_erase, piCountA_piDomsA, hparts2.1]
      simp only [List.length_cons]
      omega
    rw [hpc, htop]
    exact hcanon

/-! ## (6) the verdict: the semantic read at an admitted `.frec` field -/

/-- the plain-field telescope keeps its domains and its tail inside the environment. -/
private theorem plainTel_constsIn {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} :
    (ds : List (ExprA × Level)) → {idx : List ExprA} → {Γ : LCtxA} → {k : Nat} →
    FieldsTyA E I n idxTel Γ k (ds.map plainA) idx →
    (∀ d ∈ ds, ConstsInA (domA E) d.1) ∧ ∀ a ∈ idx, ConstsInA (domA E) a
  | [], _, _, _, .nil _ _ _ hres =>
      ⟨fun d hd => absurd hd (List.not_mem_nil _), fun a ha => ArgsTyA.constsIn hres a ha⟩
  | (D, _) :: ds, _, _, _, .plain _ _ _ _ _ _ hD tl => by
      obtain ⟨h1, h2⟩ := plainTel_constsIn ds tl
      refine ⟨fun d hd => ?_, h2⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hasTyA_constsIn hD
      · exact h1 d hd

/-- the frec field's typing keeps its inner binders and indices inside the base. -/
private theorem fieldsTyA_frec_confined {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} :
    (fsPre : List FieldA) → {B : ExprA} → {uB : Level} → {Bs : List (ExprA × Level)} →
    {idx : List ExprA} → {fsRest : List FieldA} → {res : List ExprA} → {Γ : LCtxA} → {k : Nat} →
    FieldsTyA E I n idxTel Γ k (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) res →
    (∀ d ∈ (B, uB) :: Bs, ConstsInA (domA E) d.1) ∧ ∀ a ∈ idx, ConstsInA (domA E) a
  | [], _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom _ => plainTel_constsIn _ hdom
  | .plain _ _ :: fsPre, _, _, _, _, _, _, _, _, .plain _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_confined fsPre tl
  | .drec _ :: fsPre, _, _, _, _, _, _, _, _, .drec _ _ _ _ _ _ tl =>
      fieldsTyA_frec_confined fsPre tl
  | FieldA.frec _ _ _ _ :: fsPre, _, _, _, _, _, _, _, _, .frec _ _ _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_confined fsPre tl
  | .drecD _ _ :: fsPre, _, _, _, _, _, _, _, _, .drecD _ _ _ _ _ _ _ tl =>
      fieldsTyA_frec_confined fsPre tl

/-- the list lift of the δ-scan confinement: a domain list scan never reports the family. -/
private theorem domainsContainFuel_ne_true {EA E : ResolvedEnvA} {fam : Nat}
    (hpre : PrefixA E EA) (hfam : E.members fam = none)
    (hbodies : ∀ r m b, E.members r = some m → m.bodyA = some b → ConstsInA (domA E) b) :
    ∀ (fuel : Nat) (doms : List (Expr Nat)),
      (∀ D ∈ doms, ConstsInE (ConfinedE E fam) D) →
        domainsContainFuel (eraseEnv EA) fam fuel doms ≠ some true
  | _, [], _ => by intro h; simp [domainsContainFuel] at h
  | 0, _ :: _, _ => by intro h; exact Option.noConfusion h
  | fuel + 1, D :: Ds, hconf => by
      intro h
      simp only [domainsContainFuel] at h
      split at h
      · rename_i h1
        exact containsFamilyFuel_ne_true_of_confined hpre hfam hbodies _ _
          (hconf D (List.mem_cons_self _ _)) h1
      · rename_i _
        exact domainsContainFuel_ne_true hpre hfam hbodies fuel Ds
          (fun D' hD' => hconf D' (List.mem_cons_of_mem _ hD')) h
      · exact absurd h (by simp)

/-- the index list's δ-scan never reports the family. -/
private theorem indicesCleanFuel_ne_true {EA E : ResolvedEnvA} {fam : Nat}
    (hpre : PrefixA E EA) (hfam : E.members fam = none)
    (hbodies : ∀ r m b, E.members r = some m → m.bodyA = some b → ConstsInA (domA E) b) :
    ∀ (fuel : Nat) (args : List (Expr Nat)),
      (∀ D ∈ args, ConstsInE (ConfinedE E fam) D) →
        indicesCleanFuel (eraseEnv EA) fam fuel args ≠ some true
  | _, [], _ => by intro h; simp [indicesCleanFuel] at h
  | 0, _ :: _, _ => by intro h; exact Option.noConfusion h
  | fuel + 1, D :: Ds, hconf => by
      intro h
      simp only [indicesCleanFuel] at h
      split at h
      · rename_i h1
        exact containsFamilyFuel_ne_true_of_confined hpre hfam hbodies _ _
          (hconf D (List.mem_cons_self _ _)) h1
      · rename_i _
        exact indicesCleanFuel_ne_true hpre hfam hbodies fuel Ds
          (fun D' hD' => hconf D' (List.mem_cons_of_mem _ hD')) h
      · exact absurd h (by simp)

/-- a family application headed at an inductive member is whnf-stable in the erased
    environment, at any fuel. -/
private theorem whnfFuel_famApp_of_inductive {EA : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {ls : List Level} {args : List (Expr Nat)} (hmem : EA.members f = some fm)
    (hcls : fm.mclass = .inductiveM) (fuel : Nat) :
    whnfFuel (eraseEnv EA) (fuel + 1) (foldApps (.const f ls) args) =
      some (foldApps (.const f ls) args) := by
  have htb : transparentBody (eraseEnv EA) f ls = none :=
    transparentBody_eraseEnv_none hmem (Or.inl (by
      rw [hcls]
      intro hcc
      exact Bool.noConfusion hcc))
  simp only [whnfFuel, appsSpine_foldApps, appsSpine, htb]

/-- an applied constant spine is never a Π. -/
private theorem foldApps_const_ne_pi (f : Nat) (ls : List Level) :
    (args : List (Expr Nat)) → ∀ A B, foldApps (.const f ls) args ≠ .pi A B := by
  intro args A B h
  have h1 : appsSpine (foldApps (.const f ls) args) =
      ((appsSpine (.const f ls)).1, (appsSpine (.const f ls)).2 ++ args) :=
    appsSpine_foldApps _ _
  rw [h, show appsSpine (Expr.pi A B) = (Expr.pi A B, []) from rfl] at h1
  simp only [appsSpine, List.append_nil] at h1
  exact Expr.noConfusion (congrArg Prod.fst h1)

/-- the telescope's one-step equation, so rewrites stop after one unfolding. -/
private theorem piTelescopeFuel_one {E : ResolvedEnv} (fuel : Nat) (e : Expr Nat) :
    piTelescopeFuel E (fuel + 1) e =
      (match whnfFuel E fuel e with
      | none => none
      | some (.pi A B) =>
          match piTelescopeFuel E fuel B with
          | none => none
          | some (ds, body) => some (A :: ds, body)
      | some w => some ([], w)) := rfl

/-- the semantic Π-telescope of an erased frec dom: it never deviates from the syntactic
    one — it resolves to it, or runs out of fuel. -/
private theorem piTelescopeFuel_erase_frecDom {EA : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {ls : List Level} {w : Level} (hmem : EA.members f = some fm)
    (hcls : fm.mclass = .inductiveM) :
    ∀ (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) (idx : List ExprA)
      (fuel : Nat),
      piTelescopeFuel (eraseEnv EA) fuel
          (erase (frecDomA f ls w pl σ ds idx).1) = none ∨
        piTelescopeFuel (eraseEnv EA) fuel
          (erase (frecDomA f ls w pl σ ds idx).1) =
          some ((piDomsA (frecDomA f ls w pl σ ds idx).1).map erase,
            erase (piBodyA (frecDomA f ls w pl σ ds idx).1))
  | [], _, _, _, 0 => Or.inl rfl
  | [], pl, σ, idx, fuel + 1 => by
      have hd : piDomsA (frecDomA f ls w pl σ [] idx).1 = [] :=
        piDomsA_of_not_pi (foldAppsA_const_ne_pi f ls _)
      have hb : piBodyA (frecDomA f ls w pl σ [] idx).1 =
          (frecDomA f ls w pl σ [] idx).1 :=
        piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)
      have hE : erase (frecDomA f ls w pl σ [] idx).1 =
          foldApps (.const f ls) ((pl ++ idx.map (substA σ)).map erase) := by
        simp only [frecDomA, erase_foldAppsA, erase]
      cases fuel with
      | zero => exact Or.inl rfl
      | succ fuel' =>
          have hw : whnfFuel (eraseEnv EA) (fuel' + 1)
              (foldApps (.const f ls) ((pl ++ idx.map (substA σ)).map erase)) =
              some (foldApps (.const f ls) ((pl ++ idx.map (substA σ)).map erase)) :=
            whnfFuel_famApp_of_inductive hmem hcls fuel'
          refine Or.inr ?_
          rw [hd, hb, List.map_nil]
          rw [show piTelescopeFuel (eraseEnv EA) (fuel' + 1 + 1)
              (erase (frecDomA f ls w pl σ [] idx).1) =
              some ([], erase (frecDomA f ls w pl σ [] idx).1) from by
            rw [hE]
            simp only [piTelescopeFuel, hw]
            cases hE2 : foldApps (.const f ls) ((pl ++ idx.map (substA σ)).map erase) with
            | pi A B => exact absurd hE2 (foldApps_const_ne_pi f ls _ A B)
            | bvar _ => rfl
            | sort _ => rfl
            | const _ _ => rfl
            | app _ _ => rfl
            | lam _ _ => rfl
            | letE _ _ _ => rfl
            | lit _ => rfl]
  | (D, u) :: ds, pl, σ, idx, 0 => Or.inl rfl
  | (D, u) :: ds, pl, σ, idx, fuel + 1 => by
      have hstep : erase (frecDomA f ls w pl σ ((D, u) :: ds) idx).1 =
          Expr.pi (erase (substA σ D))
            (erase (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1) := by
        simp only [frecDomA, erase]
      have hdcons : piDomsA (frecDomA f ls w pl σ ((D, u) :: ds) idx).1 =
          (substA σ D) ::
            (piDomsA (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1) := rfl
      have hbcons : piBodyA (frecDomA f ls w pl σ ((D, u) :: ds) idx).1 =
          piBodyA (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1 := rfl
      rw [hdcons, hbcons, List.map_cons]
      cases fuel with
      | zero => exact Or.inl rfl
      | succ fuel' =>
          have hwpi : whnfFuel (eraseEnv EA) (fuel' + 1)
              (Expr.pi (erase (substA σ D))
                (erase (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1)) =
              some (Expr.pi (erase (substA σ D))
                (erase (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1)) := rfl
          rcases piTelescopeFuel_erase_frecDom hmem hcls ds (pl.map (liftA 0 1)) σ.up idx
            (fuel' + 1) with htel | htel
          · refine Or.inl ?_
            rw [hstep, piTelescopeFuel_one, hwpi]
            dsimp only
            rw [htel]
          · refine Or.inr ?_
            rw [hstep, piTelescopeFuel_one, hwpi]
            dsimp only
            rw [htel]

/-- `properShapeB`'s four spine conditions carry the shape check of the semantic
    analyser: with the indices' δ-scan unable to find the family, `properFamilyFuel`
    is true or unresolved — never a rejection. -/
private theorem properFamilyFuel_of_properShapeB {E' : ResolvedEnv} {f nuniv n nindices top : Nat}
    {fuel : Nat} {body : Expr Nat}
    (hs : properShapeB f nuniv n nindices top body = true)
    (hne : ∀ ls args, appsSpine body = (Expr.const f ls, args) →
      indicesCleanFuel E' f fuel (args.drop n) ≠ some true) :
    properFamilyFuel E' fuel f nuniv n nindices top body ≠ some false := by
  intro hpf
  unfold properFamilyFuel at hpf
  unfold properShapeB at hs
  cases hsp : appsSpine body with
  | mk h args =>
      cases h with
      | const r ls =>
          rw [hsp] at hpf hs
          dsimp only at hpf
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
          have hcondB : (decide (r = f) && decide (args.length = n + nindices) &&
              exactParamLocals (args.take n) top &&
              decide (ls = (List.range nuniv).map Level.param)) = true := by
            rw [decide_eq_true hs.1.1.1.1, decide_eq_true hs.1.1.1.2, hs.1.1.2,
              decide_eq_true hs.1.2]
            rfl
          split at hpf
          · split at hpf
            · rename_i hicc
              exact hne ls args (by rw [← hs.1.1.1.1]; exact hsp) hicc
            · exact absurd hpf (by simp)
            · exact absurd hpf (by simp)
          · rename_i hneg
            exact absurd hcondB hneg
      | pi A B => rw [hsp] at hs; exact absurd hs (by simp)
      | bvar v => rw [hsp] at hs; exact absurd hs (by simp)
      | sort l => rw [hsp] at hs; exact absurd hs (by simp)
      | app a b => rw [hsp] at hs; exact absurd hs (by simp)
      | lam a b => rw [hsp] at hs; exact absurd hs (by simp)
      | letE a v b => rw [hsp] at hs; exact absurd hs (by simp)
      | lit t => rw [hsp] at hs; exact absurd hs (by simp)

/-- the frec dom's Π-spine domains are substituted raws: with bvar-image substitutions and
    confined raw domains, the spine domains stay confined. -/
private theorem frecDomA_spineDoms_confined {f : Nat} {ls : List Level} {w : Level}
    {idx : List ExprA} {P : Nat → Prop} :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    (∀ i, ∃ j, σ i = ExprA.bvar j) → (∀ d ∈ ds, ConstsInA P d.1) →
      ∀ D ∈ piDomsA (frecDomA f ls w pl σ ds idx).1, ConstsInA P D
  | [], pl, σ, _, _, D, hD => by
      rw [show piDomsA (frecDomA f ls w pl σ [] idx).1 = [] from
        piDomsA_of_not_pi (foldAppsA_const_ne_pi f ls _)] at hD
      exact absurd hD (List.not_mem_nil D)
  | (D0, u0) :: ds, pl, σ, hb, hraw, D, hD => by
      have hstep : piDomsA (frecDomA f ls w pl σ ((D0, u0) :: ds) idx).1 =
          (substA σ D0) :: (piDomsA (frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx).1) :=
        rfl
      rw [hstep] at hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact constsInA_substA D0 σ (hraw _ (List.mem_cons_self _ _)) (fun i => by
          obtain ⟨j, hj⟩ := hb i
          rw [hj]
          trivial)
      · exact frecDomA_spineDoms_confined ds (pl.map (liftA 0 1)) σ.up
          (bvarImages_up hb) (fun d hd => hraw _ (List.mem_cons_of_mem _ hd)) D hD

/-- a negative-occurrence refusal needs the family found in an inner domain, at a
    resolved telescope. -/
private theorem fieldAnalyze_refused_neg_inv {E' : ResolvedEnv} {f nuniv nparams nindices depth : Nat}
    {fuel : Nat} {T : Expr Nat}
    (hfa : fieldAnalyze E' fuel f nuniv nparams nindices depth T =
        .refused .negativeOccurrence) :
    ∃ fuel' doms body, fuel = fuel' + 1 ∧ piTelescopeFuel E' fuel' T = some (doms, body) ∧
      domainsContainFuel E' f fuel' doms = some true := by
  cases fuel with
  | zero => exact FieldAnalyze.noConfusion hfa
  | succ fuel' =>
      simp only [fieldAnalyze] at hfa
      rcases htel : piTelescopeFuel E' fuel' T with none | ⟨doms, body⟩
      · rw [htel] at hfa
        exact FieldAnalyze.noConfusion hfa
      · rw [htel] at hfa
        dsimp only at hfa
        rcases hdc : domainsContainFuel E' f fuel' doms with _ | b
        · rw [hdc] at hfa
          dsimp only at hfa
          exact FieldAnalyze.noConfusion hfa
        · cases b with
          | false =>
              rw [hdc] at hfa
              dsimp only at hfa
              exfalso
              repeat' split at hfa
              all_goals simp at hfa
          | true => exact ⟨fuel', doms, body, rfl, htel, hdc⟩

/-- THE VERDICT (cc 2026-10-12, question 1): at the fired constructor of an admitted
    environment, the semantic field analysis at a function-recursive field can never
    REFUSE — the negative-occurrence verdict needs the family in an inner domain, and the
    δ-scan cannot find it there (typing in the base + freshness + bodies staying in their
    own environment) — and when the fuel carries it, the read is exactly the fired shape,
    `.permitted (.recursive k)` at the tail's indices. What can remain is `unresolved`:
    fuel EXISTENCE (the δ-closure bound), the same typed-SN-lite residual the direct side
    carries — not a verdict divergence. -/
theorem admittedFrec_verdict {I : IotaIfaceA} {EA E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (gc : GroupCtorA I E f fm fv)
    (hpre : PrefixA E EA) (hfresh : E.members f = none) (hW : EnvWfA I E)
    (hmem : EA.members f = some fm) (hcls : fm.mclass = .inductiveM)
    {fsPre : List FieldA} {B : ExprA} {uB : Level} {Bs : List (ExprA × Level)}
    {idx : List ExprA} {fsRest : List FieldA}
    (hfields : gc.view.fields = fsPre ++ FieldA.frec B uB Bs idx :: fsRest) :
    ∃ T, ((piDomsA gc.member.mtypeA).map erase)[fm.nparamsA + fsPre.length]? = some T ∧
      ∀ fuel, fieldAnalyze (eraseEnv EA) fuel f fm.arity fm.nparamsA fv.indices.length
          (fm.nparamsA + fsPre.length) T ≠ .refused .negativeOccurrence ∧
        (fieldAnalyze (eraseEnv EA) fuel f fm.arity fm.nparamsA fv.indices.length
            (fm.nparamsA + fsPre.length) T =
            .permitted (.recursive (1 + Bs.length)) (familyIdx fm.nparamsA (piTailOf T)) ∨
          fieldAnalyze (eraseEnv EA) fuel f fm.arity fm.nparamsA fv.indices.length
            (fm.nparamsA + fsPre.length) T = .unresolved) := by
  have htyped' : FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0
      (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) gc.view.res := by
    rw [← hfields]
    exact gc.view.typed
  have hfree := fieldsTyA_frec_freeOf (I := I) (E := E) hfresh fsPre (B := B) (uB := uB)
    (Bs := Bs) (idx := idx) (fsRest := fsRest) (res := gc.view.res) htyped'
  have hconf := fieldsTyA_frec_confined (I := I) (E := E) fsPre (B := B) (uB := uB)
    (Bs := Bs) (idx := idx) (fsRest := fsRest) (res := gc.view.res) htyped'
  have hbodies := envWfA_bodiesSelf hW
  have hidxLen : idx.length = fv.indices.length :=
    idxLen_of_fieldsTyA_frec fsPre htyped'
  have hmir : gc.view.mirrors.length = fm.nparamsA := by
    rw [gc.view.mirrorsConv.length, fv.nparams]
  obtain ⟨Tshape, hgetS, hpcS, hcleanS, hcanonS⟩ :=
    admittedFrec_shape gc hfresh hfields
  obtain ⟨σ', hbvar, hdom⟩ :=
    ctorFieldsA_dom_frec f (canonLevelsA fm.arity) fv.sort gc.view.res B uB Bs idx fsPre
      fsRest (paramLocalsA gc.view.mirrors.length) SubstA.id
      (fun i => ⟨i, rfl⟩)
  rw [hmir] at hdom
  -- the shared freeness/confines of the frec dom's pieces
  have hplFree : ∀ p ∈ ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)), FreeOfA f p :=
    fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact constsInA_liftA fsPre.length q 0 (paramLocalsA_freeOf f _ q hq)
  have hσFree : ∀ i, FreeOfA f (σ' i) := by
    intro i
    obtain ⟨j, hj⟩ := hbvar i
    rw [hj]
    trivial
  have hparts := frecDomA_parts f (canonLevelsA fm.arity) fv.sort idx hfree.2 ((B, uB) :: Bs)
    ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' hfree.1 hplFree hσFree
  have hdomsConf : ∀ D ∈ (piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' ((B, uB) :: Bs) idx).1),
      ConstsInE (ConfinedE E f) (erase D) := by
    intro D hD
    have hc : ConstsInA (domA E) D :=
      frecDomA_spineDoms_confined ((B, uB) :: Bs) _ σ' hbvar hconf.1 D hD
    have hf : FreeOfA f D := hparts.2.1 D hD
    exact constsInE_erase _ D (constsInA_inter D hc hf)
  have hdomsConfE : ∀ D ∈ (piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' ((B, uB) :: Bs) idx).1).map
      erase, ConstsInE (ConfinedE E f) D := by
    intro D hD
    obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hD
    exact hdomsConf D' hD'
  have hdomsConfE : ∀ D ∈ (piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' ((B, uB) :: Bs) idx).1).map
      erase, ConstsInE (ConfinedE E f) D := by
    intro D hD
    obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hD
    exact hdomsConf D' hD'
  obtain ⟨xs, htail, hxsdef, hxslen, hxsfree⟩ :=
    frecDomA_tailParts f (canonLevelsA fm.arity) fv.sort idx ((B, uB) :: Bs)
      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' hfree.1 hfree.2 hσFree
  have hxsConf : ∀ y ∈ xs.map erase, ConstsInE (ConfinedE E f) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [hxsdef] at hx
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hx
    exact constsInE_erase _ _
      (constsInA_substA a' (SubstA.upN ((B, uB) :: Bs).length σ')
        (constsInA_inter a' (hconf.2 a' ha') (hfree.2 a' ha'))
        (fun i => by
          obtain ⟨j, hj⟩ := bvarImages_upN hbvar ((B, uB) :: Bs).length i
          rw [hj]
          trivial))
  have hgetv : ((piDomsA gc.member.mtypeA).map erase)[fm.nparamsA + fsPre.length]? =
      some (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
        ((B, uB) :: Bs) idx).1) := by
    have hpiDoms : piDomsA gc.member.mtypeA =
        gc.view.mirrors.map Prod.fst ++
          piDomsA (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
            (paramLocalsA gc.view.mirrors.length) SubstA.id gc.view.fields gc.view.res).1 := by
      rw [gc.view.stored, ctorTypeA, piDomsA_piTelA]
    have hle : (List.map erase (List.map Prod.fst gc.view.mirrors)).length ≤
        fm.nparamsA + fsPre.length := by
      rw [List.length_map, List.length_map, hmir]
      exact Nat.le_add_right fm.nparamsA fsPre.length
    rw [hpiDoms, List.map_append, List.getElem?_append_right hle]
    rw [List.length_map, List.length_map, hmir, Nat.add_sub_cancel_left, List.getElem?_map,
      hfields, hdom]
    rfl
  have hTeq : Tshape = erase (frecDomA f (canonLevelsA fm.arity) fv.sort
      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
      ((B, uB) :: Bs) idx).1 :=
    Option.some.inj (hgetS.symm.trans hgetv)
  rw [hTeq] at hpcS hcanonS
  refine ⟨_, hgetv, ?_⟩
  · intro fuel
    constructor
    · -- never a negative occurrence
      intro hfa
      obtain ⟨fuel0, doms, body, hfuel, htel0, hdt0⟩ := fieldAnalyze_refused_neg_inv hfa
      cases fuel with
      | zero => exact absurd hfuel (by omega)
      | succ fuel' =>
          have hf0 : fuel0 = fuel' := by omega
          rw [hf0] at htel0 hdt0
          rcases piTelescopeFuel_erase_frecDom (ls := canonLevelsA fm.arity) (w := fv.sort)
            hmem hcls ((B, uB) :: Bs)
            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' idx fuel' with htel | htel
          · rw [htel] at htel0
            exact Option.noConfusion htel0
          · rw [htel] at htel0
            have hpair := Option.some.inj htel0
            have hd : doms =
                (piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                  ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                  ((B, uB) :: Bs) idx).1).map erase :=
              (Prod.mk.injEq _ _ _ _ |>.mp hpair).1.symm
            rw [hd] at hdt0
            exact domainsContainFuel_ne_true hpre hfresh hbodies _ _ hdomsConfE hdt0
    · -- the fired shape, or unresolved
      cases fuel with
      | zero => exact Or.inr rfl
      | succ fuel' =>
          simp only [fieldAnalyze]
          rcases piTelescopeFuel_erase_frecDom (ls := canonLevelsA fm.arity) (w := fv.sort)
            hmem hcls ((B, uB) :: Bs)
            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ' idx fuel' with htel' | htel'
          · rw [htel']
            exact Or.inr rfl
          · rw [htel']
            dsimp only
            have hplen : (((paramLocalsA fm.nparamsA).map
                (liftA 0 (fsPre.length + ((B, uB) :: Bs).length))).map erase).length =
                fm.nparamsA := by
              rw [List.length_map, List.length_map, paramLocalsA_length]
            rcases hdc : domainsContainFuel (eraseEnv EA) f fuel'
                ((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                  ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                  ((B, uB) :: Bs) idx).1).map erase) with _ | b
            · exact Or.inr rfl
            · cases b with
              | true =>
                  exfalso
                  exact domainsContainFuel_ne_true hpre hfresh hbodies _ _ hdomsConfE hdc
              | false =>
                  have hbody' : piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                      ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                      ((B, uB) :: Bs) idx).1) =
                      erase (piBodyA (frecDomA f (canonLevelsA fm.arity) fv.sort
                        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                        ((B, uB) :: Bs) idx).1) :=
                    (congrArg Prod.snd (piTelE_piDomsOf _)).symm.trans (piTelE_erase _).2
                  rcases hpf : properFamilyFuel (eraseEnv EA) fuel' f fm.arity fm.nparamsA
                      fv.indices.length
                      (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                        ((B, uB) :: Bs) idx).1).map erase).length +
                        (fm.nparamsA + fsPre.length) - 1)
                      (erase (piBodyA (frecDomA f (canonLevelsA fm.arity) fv.sort
                        ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                        ((B, uB) :: Bs) idx).1)) with _ | c
                  · exact Or.inr rfl
                  · cases c with
                    | true =>
                        refine Or.inl ?_
                        rw [hbody']
                        have hlen : (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                            ((B, uB) :: Bs) idx).1).map erase).length) = 1 + Bs.length := by
                          rw [List.length_map, hparts.1]
                          simp only [List.length_cons]
                          omega
                        rw [hlen]
                    | false =>
                        exfalso
                        have hlen : (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                            ((B, uB) :: Bs) idx).1).map erase).length) = 1 + Bs.length := by
                          rw [List.length_map, hparts.1]
                          simp only [List.length_cons]
                          omega
                        have hpcT : piCount (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                            ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                            ((B, uB) :: Bs) idx).1) = 1 + Bs.length := hpcS
                        have hcanon' : properShapeB f fm.arity fm.nparamsA fv.indices.length
                            (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1).map erase).length +
                              (fm.nparamsA + fsPre.length) - 1)
                            (piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1)) = true := by
                          rw [show (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1).map erase).length +
                              (fm.nparamsA + fsPre.length) - 1) =
                              piCount (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                                ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                                ((B, uB) :: Bs) idx).1) +
                                (fm.nparamsA + fsPre.length) - 1 from by
                            rw [piCountA_erase, piCountA_piDomsA, List.length_map]]
                          exact hcanonS
                        have hne' : ∀ ls args,
                            appsSpine (piTailOf (erase (frecDomA f (canonLevelsA fm.arity)
                                fv.sort ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                                ((B, uB) :: Bs) idx).1)) = (Expr.const f ls, args) →
                              indicesCleanFuel (eraseEnv EA) f fuel' (args.drop fm.nparamsA)
                                ≠ some true := by
                          intro ls args hsp
                          have hspTail : appsSpine (piTailOf (erase (frecDomA f
                              (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1)) =
                              (Expr.const f (canonLevelsA fm.arity),
                                ((paramLocalsA fm.nparamsA).map
                                  (liftA 0 (fsPre.length + ((B, uB) :: Bs).length))).map erase ++
                                  xs.map erase) := by
                            rw [hbody', htail, erase_foldAppsA, appsSpine_foldApps,
                              liftA_map_comp]
                            simp only [appsSpine, List.nil_append, List.length_cons,
                              List.map_append]
                          have hargs : args = ((paramLocalsA fm.nparamsA).map
                              (liftA 0 (fsPre.length + ((B, uB) :: Bs).length))).map erase ++
                              xs.map erase :=
                            (Prod.mk.injEq _ _ _ _ |>.mp (hsp.symm.trans hspTail)).2
                          rw [hargs, List.drop_left' hplen]
                          exact indicesCleanFuel_ne_true hpre hfresh hbodies _ _ hxsConf
                        have htopEq : 1 + Bs.length + (fm.nparamsA + fsPre.length) - 1 =
                            (((piDomsA (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1).map erase).length +
                              (fm.nparamsA + fsPre.length) - 1) := by
                          rw [hlen]
                        have hcanon'' : properShapeB f fm.arity fm.nparamsA
                            fv.indices.length (1 + Bs.length +
                              (fm.nparamsA + fsPre.length) - 1)
                            (piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1)) = true := by
                          rw [htopEq]
                          exact hcanon'
                        have hpf' : properFamilyFuel (eraseEnv EA) fuel' f fm.arity
                            fm.nparamsA fv.indices.length (1 + Bs.length +
                              (fm.nparamsA + fsPre.length) - 1)
                            (piTailOf (erase (frecDomA f (canonLevelsA fm.arity) fv.sort
                              ((paramLocalsA fm.nparamsA).map (liftA 0 fsPre.length)) σ'
                              ((B, uB) :: Bs) idx).1)) = some false := by
                          rw [htopEq, hbody']
                          exact hpf
                        exact properFamilyFuel_of_properShapeB hcanon'' hne' hpf'

#print axioms admittedFrec_shape
#print axioms admittedFrec_verdict
#print axioms envWfA_bodiesSelf
#print axioms containsFamilyFuel_ne_true_of_confined
