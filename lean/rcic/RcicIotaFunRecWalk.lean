import rcic.RcicIotaFunRecFrag

/-!
# R-NoFunRec S6 segment 3b: the walk agreement — `iotaArgs` = `rhsArgsS` over the fragment

The typed root's ι witness (`IotaWitnessS`) carries its right-hand side as the SCHEMA
`iotaOpenRhs` computes (the fuel-bounded `iotaArgs` walk on the canonical equation
context), instantiated in parallel (`instPrefix (preMajor ++ fields)`); the copy's ι
(`iotaReductA`) computes its reduct by the SEQUENTIAL `rhsArgsA` walk on the redex's own
arguments (tree-side: `rhsArgsS`). The direct side CHECKS the agreement (the recognizers'
decided conjunct); this file PROVES it on the fun-recursive fragment, which is what the
frec arm of the union erase direction (segment 3c, `RcicAnnIotaCorrUA.lean`) needs to
ASSEMBLE a witness from a firing instead of checking one.

Two substitution traversals agree exactly when the arguments are CLOSED: sequential
`instantiate0` corrupts free `bvar 0`s inside earlier arguments, the parallel
`instPrefix` does not (S6_MEASURE's divergence class, now named). The redex's argument
closedness (`exprClosedAt 0`) is therefore an honest premise of the walk agreement, and
the canonical equation context always satisfies it.

Plan: `research/rcic/nofunrec/S6_PLAN.md` §3 A2b + cc's 2026-10-13 ruling.
`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## (1) components -/

/-- canonical levels instantiate to the redex's level list, at matching length. -/
theorem canonRecLevels_instLevel (ls : List Level) (n : Nat) (h : ls.length = n) :
    (canonRecLevels n).map (instLevel ls) = ls := by
  have aux : ∀ (m : Nat) (hm : m ≤ ls.length),
      ((List.range m).map Level.param).map (instLevel ls) = ls.take m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        rw [List.range_succ, List.map_append, List.map_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil]
        have hget : m < ls.length := by omega
        have htak : ls.take (m + 1) = ls.take m ++ [ls[m]'hget] := by
          rw [List.take_succ, List.getElem?_eq_getElem hget]
          rfl
        rw [htak]
        have hin : instLevel ls (Level.param m) = ls[m]'hget := by
          simp only [instLevel, levelParamSubst, lvlSubst, List.getElem?_eq_getElem hget,
            Option.getD_some]
        rw [hin]
  rw [← h]
  have hcore := aux ls.length (Nat.le_refl _)
  have htall : ls.take ls.length = ls := List.take_length ls
  rw [htall] at hcore
  exact hcore

/-- a canonical-level constant head instantiates to the redex's own levels. -/
theorem instantiateLevels_const_canonRecLevels (ls : List Level) (r n : Nat)
    (h : ls.length = n) :
    instantiateLevels ls (.const r (canonRecLevels n)) = .const r ls := by
  show Expr.const r ((canonRecLevels n).map (instLevel ls)) = _
  rw [canonRecLevels_instLevel ls n h]

/-- the prelude context's bvar at slot `u` (`fieldBvars_getElem?`'s prelude sibling). -/
theorem preMajorBvars_getElem? (nparams nMinors nindices nf u : Nat)
    (hu : u < nparams + 1 + nMinors + nindices) :
    (preMajorBvars nparams nMinors nindices nf)[u]? =
      some (.bvar (nparams + nMinors + nindices - u + nf)) := by
  unfold preMajorBvars
  rw [List.getElem?_map,
    List.getElem?_reverse (i := u) (l := List.range (nparams + 1 + nMinors + nindices))
      (by simp only [List.length_range]; omega),
    List.length_range,
    List.getElem?_range
      (m := nparams + 1 + nMinors + nindices - 1 - u)
      (n := nparams + 1 + nMinors + nindices) (by omega)]
  show some (Expr.bvar (nparams + 1 + nMinors + nindices - 1 - u + nf)) = _
  exact congrArg (fun k => some (Expr.bvar k)) (by omega)

/-- the prelude context's bvars map, under the final parallel instantiation, to the
    redex's own pre-major arguments, in order (`preMajorBvars` is the reversed range). -/
theorem preMajorBvars_map_instPrefix (pre fields : List (Expr Nat))
    (nparams nMinors nindices : Nat)
    (hpre : pre.length = nparams + 1 + nMinors + nindices) :
    (preMajorBvars nparams nMinors nindices fields.length).map
      (fun a => instPrefix (pre ++ fields) a) = pre := by
  apply List.ext_getElem
  · simp only [List.length_map, preMajorBvars, List.length_reverse, List.length_range]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1
    have hi : i < nparams + 1 + nMinors + nindices := by omega
    have hlen : i < (preMajorBvars nparams nMinors nindices fields.length).length := by
      simp only [preMajorBvars, List.length_map, List.length_reverse, List.length_range]
      omega
    have hg := preMajorBvars_getElem? nparams nMinors nindices fields.length i hi
    rw [List.getElem?_eq_getElem hlen] at hg
    have hget2 := Option.some.inj hg
    rw [List.getElem_map, hget2]
    have hip : i < pre.length := by rw [hpre]; omega
    apply instPrefix_bvar_lt
    · rw [List.length_append, hpre]
      omega
    · have hL : (pre ++ fields).length - 1 -
          (nparams + nMinors + nindices - i + fields.length) = i := by
        rw [List.length_append, hpre]
        omega
      rw [hL, List.getElem?_append_left hip, List.getElem?_eq_getElem hip]

/-! ## (2) level/bvar commutations

`instantiateLevels` commutes with `lift` and `instantiate` — ALREADY upstream
(`lift_instantiateLevels`, `instantiateLevels_instantiate`/`…_instantiate0`,
`RcicLevelCalc.lean:487/:516`); the walk's step machinery consumes them as-is.
Design note §7.3/§7.4 of `research/rcic/nofunrec/S6_PLAN.md`. -/

/-! ## (3) TEL-CONS: the sequential↔parallel telescope base bridge

The base bridge of the walk invariant (S6_PLAN §7 item 5): the copy's ι applies
the constructor's parameter prefix SEQUENTIALLY (`applyTel`, one `instantiate0`
per Π), while the invariant's parallel side instantiates the whole equation
context frame in one shot (`instPrefix (pre ++ done ++ identity)`), the remaining
field binders given INCREASING identity bvars. The components here are pure
substitution arithmetic on Π-telescopes — `peelPis`/`applyTel`/`instPrefix`/
`instantiateLevels` — and touch none of the walk's recursive-call construction
(`iotaOpenRhs`'s arms): the family-index lift under ruling R6a (grokF, Lean
batch 22) lives there, not here, so 3b-2b can consume these unchanged once the
corrected `iotaOpenRhs` lands. -/

/-- a peeled telescope is its domains' foldr: the domains are collected in
    place, so rebuilding the Π-nesting is the identity on the peel's input. -/
theorem peelPis_rebuild :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → T = ds.foldr Expr.pi r
  | 0, T, ds, r, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds htr
      subst hds
      subst htr
      rfl
  | n + 1, T, ds, r, h => by
      have ⟨A, B, ds', hT, hds, hpeel⟩ := peelPis_succ h
      subst hT
      subst hds
      simp only [List.foldr_cons]
      exact congrArg _ (peelPis_rebuild n B hpeel)

/-- the identity suffix never fires on a closed telescope: `instPrefix` at any
    arguments is the identity when every free reference is bound. This is the
    base case of the bridge (nothing consumed, all `m` remaining field binders
    given INCREASING identity bvars — S6_PLAN §7 item 3). -/
theorem instPrefix_exprClosedAt_0 {T : Expr Nat} (hcl : exprClosedAt 0 T = true)
    (args : List (Expr Nat)) : instPrefix args T = T := by
  induction args generalizing T with
  | nil => rfl
  | cons a as ih =>
      rw [instPrefix_cons]
      have hinst : instantiate as.length (lift 0 as.length a) T = T :=
        instantiate_eq_of_exprClosedAt_le hcl (Nat.zero_le _) _
      rw [hinst]
      exact ih hcl

/-- closedness is preserved by substituting a closed term at the cutoff slot:
    `e` closed at `c+1` (its free references are the cutoff slot and below),
    `v` closed at `c` — then `instantiate c v e` is closed at `c`. This is the
    sequential step's closedness carrier for the bridge induction. -/
theorem exprClosedAt_instantiate_cutoff {e v : Expr Nat} {c : Nat}
    (he : exprClosedAt (c + 1) e = true) (hv : exprClosedAt c v = true) :
    exprClosedAt c (instantiate c v e) = true := by
  induction e generalizing c v with
  | bvar i =>
      simp only [exprClosedAt, decide_eq_true_eq] at he
      by_cases h : i = c
      · simp only [instantiate, if_pos h]
        exact hv
      · have hlt : ¬ (c < i) := by omega
        simp only [instantiate, if_neg h, if_neg hlt]
        simp only [exprClosedAt, decide_eq_true_eq]
        omega
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f a ihf iha =>
      simp only [exprClosedAt, Bool.and_eq_true] at he ⊢
      exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at he ⊢
      have hv1 : exprClosedAt (c + 1) (lift 0 1 v) = true := by
        have h := exprClosedAt_lift (m := c) (d := 0) (a := 1) hv
        simpa using h
      exact ⟨ihA he.1 hv, ihB he.2 hv1⟩
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at he ⊢
      have hv1 : exprClosedAt (c + 1) (lift 0 1 v) = true := by
        have h := exprClosedAt_lift (m := c) (d := 0) (a := 1) hv
        simpa using h
      exact ⟨ihA he.1 hv, ihB he.2 hv1⟩
  | letE A v' B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at he ⊢
      have hv1 : exprClosedAt (c + 1) (lift 0 1 v) = true := by
        have h := exprClosedAt_lift (m := c) (d := 0) (a := 1) hv
        simpa using h
      exact ⟨⟨ihA he.1.1 hv, ihv he.1.2 hv⟩, ihB he.2 hv1⟩


/-- per-domain instantiation of a peeled telescope: domain `i` is instantiated
    at index `j + i` with the replacement lifted over the `i` binders above it
    — exactly `peelPis_instantiate_body`'s body clause, made transparent in the
    domains. -/
private def instDoms (j : Nat) (v : Expr Nat) : List (Expr Nat) → List (Expr Nat)
  | [] => []
  | E :: es => instantiate j v E :: instDoms (j + 1) (lift 0 1 v) es

/-- `peelPis_instantiate_body` with the domains exposed: instantiating a
    peeled telescope's input instantiates every domain at its own depth and the
    body at the full peel depth. -/
theorem peelPis_instantiate_doms :
    (n : Nat) → (j : Nat) → (v e : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n e = some (ds, r) →
    peelPis n (instantiate j v e) =
      some (instDoms j v ds, instantiate (j + n) (lift 0 n v) r)
  | 0, j, v, e, ds, r, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds htr
      subst hds
      subst htr
      simp only [peelPis, instDoms, Nat.add_zero, lift_zero]
  | n + 1, j, v, e, ds, r, h => by
      have ⟨A, B, ds', hE, hds, hpeel⟩ := peelPis_succ h
      subst hE
      subst hds
      simp only [instantiate, peelPis, instDoms]
      have hinner :=
        peelPis_instantiate_doms n (j + 1) (lift 0 1 v) B hpeel
      simp only [hinner]
      have hidx : j + 1 + n = j + (n + 1) := by omega
      have hlift : lift 0 n (lift 0 1 v) = lift 0 (n + 1) v := by
        have hmerge := lift_lift_merge n 1 0 0 (Nat.le_refl 0) (by omega) v
        simp only [Nat.add_comm 1 n] at hmerge
        exact hmerge
      rw [hidx, hlift]

/-- instantiating a rebuilt telescope decomposes per-domain: each domain at its
    own depth, the body at the full depth — the parallel counterpart of
    `peelPis_instantiate_doms`. -/
theorem instantiate_foldr_pi :
    (j : Nat) → (v : Expr Nat) →
    (es : List (Expr Nat)) → (r : Expr Nat) →
    instantiate j v (es.foldr Expr.pi r) =
      (instDoms j v es).foldr Expr.pi
        (instantiate (j + es.length) (lift 0 es.length v) r)
  | _, _, [], _ => by
      simp only [List.foldr_nil, instDoms, List.length_nil, Nat.add_zero, lift_zero]
  | j, v, E :: es, r => by
      simp only [List.foldr_cons, instantiate, instDoms, List.length_cons]
      rw [instantiate_foldr_pi (j + 1) (lift 0 1 v) es r]
      have hidx : j + 1 + es.length = j + (es.length + 1) := by omega
      have hlift : lift 0 es.length (lift 0 1 v) =
          lift 0 (es.length + 1) v := by
        have hmerge := lift_lift_merge es.length 1 0 0 (Nat.zero_le 0) (by omega) v
        simp only [Nat.add_comm 1 es.length] at hmerge
        exact hmerge
      rw [hidx, hlift]

/-- at a CLOSED replacement, the progressive lifts inside `instDoms` collapse:
    the lifted value is the value. -/
theorem instDoms_lift_closed {v : Expr Nat} (hcl : exprClosedAt 0 v = true) :
    (j k : Nat) → (es : List (Expr Nat)) →
    instDoms j (lift 0 k v) es = instDoms j v es
  | _, _, [] => rfl
  | j, k, E :: es => by
      have hv : lift 0 k v = v :=
        lift_amt_eq_of_exprClosedAt_le hcl (Nat.le_refl 0)
      have hmerge : lift 0 1 (lift 0 k v) = lift 0 (k + 1) v :=
        lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (by omega) v
      simp only [instDoms, hv, ← hmerge]

/-- at a CLOSED replacement, `instDoms` past a consumed prefix aligns with the
    prefix length: the sequential side's per-domain instantiation of the
    remaining suffix, at the offset the prefix consumed. -/
theorem instDoms_append_drop {v : Expr Nat} (hcl : exprClosedAt 0 v = true) :
    (j : Nat) → (l₁ l₂ : List (Expr Nat)) →
    (instDoms j v (l₁ ++ l₂)).drop l₁.length = instDoms (j + l₁.length) v l₂
  | _, [], _ => rfl
  | j, E :: l₁, l₂ => by
      have hv1 : lift 0 1 v = v :=
        lift_amt_eq_of_exprClosedAt_le hcl (Nat.le_refl 0)
      simp only [List.cons_append, instDoms, List.length_cons, hv1,
        List.drop_succ_cons]
      have hstep := instDoms_append_drop hcl (j + 1) l₁ l₂
      exact hstep.trans
        (congrArg (fun k => instDoms k v l₂) (by omega))

/-! ### the bridge

The base bridge itself: SEQUENTIAL parameter application (`applyTel`, the
copy's ι) equals the PARALLEL prefix instantiation of the remaining field
telescope lifted into the walk's frame, the remaining binders given INCREASING
identity bvars. Premises are exactly the honest ones — the telescope closed
(the stored constructor type is), the arguments closed (the redex's parameter
arguments, S6_MEASURE's divergence class (i)) — and NOTHING about family
indices: the recursive-call construction is not in sight, so ruling R6a's
`iotaOpenRhs` fix composes with this unchanged. -/

/-- TEL-CONS: applying the parameter prefix sequentially to a closed telescope
    yields the parallel instantiation of the rebuilt remaining telescope. -/
theorem tel_cons :
    (as : List (Expr Nat)) → (m : Nat) → (T : Expr Nat) →
    exprClosedAt 0 T = true → (∀ a ∈ as, exprClosedAt 0 a = true) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (as.length + m) T = some (ds, r) →
    applyTel as T = some (instPrefix (as ++ (List.range m).map Expr.bvar)
      (lift 0 m ((ds.drop as.length).foldr Expr.pi r)))
  | [], m, T, hcl, _, ds, r, h => by
      have hT : T = ds.foldr Expr.pi r := by
        have hr := peelPis_rebuild (0 + m) T h
        simpa using hr
      subst hT
      have hlTV : lift 0 m (ds.foldr Expr.pi r) = ds.foldr Expr.pi r :=
        lift_amt_eq_of_exprClosedAt_le hcl (Nat.le_refl 0)
      simp only [applyTel, List.nil_append, List.length_nil, List.drop_zero,
        hlTV, instPrefix_exprClosedAt_0 hcl _]
  | a :: as, m, T, hcl, hargs, ds, r, h => by
      have hn : (a :: as).length = as.length + 1 := rfl
      rw [hn, Nat.add_right_comm as.length 1 m] at h
      have ⟨A, B, ds', hT, hds, hpeel⟩ := peelPis_succ (n := as.length + m) h
      subst hT
      subst hds
      -- the sequential step, and its peel
      have hclB : exprClosedAt 1 B = true := by
        simp only [exprClosedAt, Bool.and_eq_true] at hcl
        exact hcl.2
      have hcla : exprClosedAt 0 a = true := hargs a (List.mem_cons_self ..)
      have hclInst : exprClosedAt 0 (instantiate 0 a B) = true :=
        exprClosedAt_instantiate_cutoff (by simpa using hclB) hcla
      have hargs' : ∀ x ∈ as, exprClosedAt 0 x = true := fun x hx =>
        hargs x (List.mem_cons_of_mem _ hx)
      have hpeelInst := peelPis_instantiate_doms (as.length + m) 0 a B hpeel
      have hrec := tel_cons as m (instantiate 0 a B) hclInst hargs' hpeelInst
      simp only [applyTel_cons_pi, List.length_cons, List.drop_succ_cons,
        List.cons_append] at hrec ⊢
      -- the parallel head step against the sequential one
      have hw : lift 0 (as.length + m) a = a :=
        lift_amt_eq_of_exprClosedAt_le hcla (Nat.le_refl 0)
      have hliftA : lift 0 m a = a :=
        lift_amt_eq_of_exprClosedAt_le hcla (Nat.le_refl 0)
      rw [hw] at hpeelInst hrec
      have hlenIds : (as ++ (List.range m).map Expr.bvar).length = as.length + m := by
        simp only [List.length_append, List.length_map, List.length_range]
      rw [instPrefix_cons, hlenIds, hw]
      have hP4rev : instantiate (as.length + m) a (lift 0 m
          ((ds'.drop as.length).foldr Expr.pi r)) =
          lift 0 m (instantiate as.length a
            ((ds'.drop as.length).foldr Expr.pi r)) := by
        have h4 := lift_instantiate_high m 0 as.length a
          (Nat.zero_le as.length) ((ds'.drop as.length).foldr Expr.pi r)
        rw [hliftA, Nat.add_comm m as.length] at h4
        exact h4.symm
      rw [hP4rev]
      have hdsl : ds'.length = as.length + m := peelPis_length _ B hpeel
      have hdropLen : (ds'.drop as.length).length = m := by
        rw [List.length_drop, hdsl]
        omega
      have hsplit : (instDoms 0 a ds').drop as.length =
          instDoms as.length a (ds'.drop as.length) := by
        have happ : ds'.take as.length ++ ds'.drop as.length = ds' :=
          List.take_append_drop as.length ds'
        have hstep := instDoms_append_drop hcla 0
          (ds'.take as.length) (ds'.drop as.length)
        have hle : as.length ≤ ds'.length := by omega
        rw [happ, List.length_take] at hstep
        simp only [Nat.min_eq_left hle] at hstep
        simpa only [Nat.zero_add] using hstep
      have hbodyInst := instantiate_foldr_pi as.length a
        (ds'.drop as.length) r
      rw [hdropLen, hliftA] at hbodyInst
      rw [hbodyInst, ← hsplit]
      simpa only [Nat.zero_add] using hrec

#print axioms Rcic.Declarative.tel_cons

end Rcic.Declarative
