import rcic.RcicIotaShapeStable
import rcic.RcicIndGroupJudgment
import rcic.RcicParRedSortWall

namespace Rcic.Declarative

open List

/-! # R-NoFunRec-1 B2 step 2b-2 — legacy/typed ι analysis adapter

`analyzeField` / `analyzeFields` (05 §8, legacy declarative carrier) and
`fieldAnalyze` / `fieldShapesFuel` (admission's shape-based analyser)
compute DIFFERENT scans: the legacy scan is purely syntactic —
`occursConst` on the stored domain, `isFamilyApp` on its application
spine — while the shape analyser weak-head-normalizes
(`piTelescopeFuel`), scans through transparent member bodies
(`containsFamilyFuel`), and accepts an extra class the legacy carrier
does not have (`recursive inner` for `inner > 0`, the FunRec telescope
shape).

This file connects them on an explicitly stated DIRECT fragment.  The
fragment (`DirectFieldFrag`) says per field `T` at telescope depth
`depth`:

* `rigid` — no transparent constant is reachable inside `T`, so
  `containsFamilyFuel` degenerates to `occursConst`;
* `stableTail` — the spine of `T`'s Π-tail is whnf-stable (not a
  β-redex, let, or transparent-headed application), so
  `piTelescopeFuel` returns the syntactic Π decomposition;
* `fuelBound` — `esize T + piCount T + 2 ≤ fuel`, covering the
  telescope descent, the domain scan, and the whole-field occurrence
  scan (each analyser burns one unit up front);
* `canon` — when `T` is a family application, its parameters are the
  exact enclosing parameter locals at `depth`, the spine has
  `nparams + nindices` arguments, and the head carries the canonical
  stored-universe vector (this is `properFamilyFuel`'s positive
  clause, checked syntactically as `properShapeB`);
* `noInner` — `T`'s Π-tail is not a canonical family application, so
  the shape analyser cannot return `.recursive inner` with
  `inner > 0`, a class `analyzeField` always refuses.

Two honest divergences fall outside the fragment and are reported, not
patched: (i) a Π-domain wrapping a family application is
`.recursive (inner>0)` for the shape analyser and `none` for the
legacy scan — that is the FunRec extension point, not a defect; and
`RcicTypedDeltaRecPins.drField` (`Id F`) is permitted by admission's
δ-aware scan while the legacy syntactic scan returns `none` — fenced
out by `rigid`; (ii) for a direct-recursive field whose INDEX
arguments mention the constructor's parameters, `iotaRhsOfS` and
`iotaRhsOf` can genuinely differ — `familyIdx` drops the param spine
positions but keeps index positions, and canonical-position
instantiation and parameter instantiation need not agree there.  The
recognizer DECIDES the final
`instPrefix (preMajor ++ fields) (instantiateLevels ls schema) =
iotaRhsOf` equality, so any witness where the two computations
diverge is refused rather than adapted — checked agreement, not
assumed agreement. -/

/-- Syntactic size of an expression, the fuel bound for the
constructor scan (`containsFamilyFuel` charges one unit per node). -/
def esize : Expr Nat → Nat
  | .bvar _ => 1
  | .sort _ => 1
  | .lit t => 2 * t + 2
  | .const _ _ => 1
  | .app f x => esize f + esize x + 1
  | .lam a b => esize a + esize b + 1
  | .pi a b => esize a + esize b + 1
  | .letE a v b => esize a + esize v + esize b + 1

/-- Every constant in `e` resolves to a member with no transparent
body — δ can never fire inside the analysers on this term. -/
def noTransparentB (E : ResolvedEnv) : Expr Nat → Bool
  | .bvar _ => true
  | .sort _ => true
  | .lit t =>
      match t with
      | 0 => (transparentBody E 1 []).isNone
      | _ + 1 =>
          (transparentBody E 1 []).isNone && (transparentBody E 2 []).isNone
  | .const r ls => (transparentBody E r ls).isNone
  | .app f x => noTransparentB E f && noTransparentB E x
  | .lam a b => noTransparentB E a && noTransparentB E b
  | .pi a b => noTransparentB E a && noTransparentB E b
  | .letE a v b =>
      noTransparentB E a && noTransparentB E v && noTransparentB E b

/-- The spine head is not a β-redex (`lam` applied) nor a `letE`
spine — `whnfFuel` is the identity on such a term. Transparent-headed
spines are excluded separately by `noTransparentB`. -/
def headStableB : Expr Nat → Bool
  | e => match appsSpine e with
    | (.lam _ _, _ :: _) => false
    | (.letE _ _ _, _) => false
    | _ => true

/-- The domains `piTelescopeFuel` peels off a term. -/
def piDomsOf : Expr Nat → List (Expr Nat)
  | .pi A B => A :: piDomsOf B
  | _ => []

/-- The non-Π tail `piTelescopeFuel` returns. -/
def piTailOf : Expr Nat → Expr Nat
  | .pi _ B => piTailOf B
  | e => e

/-- The shape-analyser's family-application shape check, with the
fuel-bounded index scan replaced by the equivalent syntactic
occurrence test (valid under `noTransparentB`). `top` is
`doms.length + depth - 1` as in `fieldAnalyze`. -/
def properShapeB (fam nuniv nparams nindices top : Nat) (body : Expr Nat) :
    Bool :=
  match appsSpine body with
  | (.const r ls, args) =>
      decide (r = fam) && decide (args.length = nparams + nindices) &&
        exactParamLocals (args.take nparams) top &&
        decide (ls = (List.range nuniv).map Level.param) &&
        (args.drop nparams).all (fun a => !(occursConst fam a))
  | _ => false

/-- The DIRECT fragment: the per-field hypotheses under which
`fieldAnalyze` agrees with `analyzeField`. `depth` is the field's
position in the constructor telescope (its parameter-prefix depth), as
threaded by `fieldShapesFuel` starting at `nparams`. -/
structure DirectFieldFrag (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) (T : Expr Nat) : Prop where
  /-- δ never fires inside `T`. -/
  rigid : noTransparentB E T = true
  /-- `T`'s Π-tail is whnf-stable, so `piTelescopeFuel` returns the
      syntactic decomposition `piDomsOf`/`piTailOf`. -/
  stableTail : headStableB (piTailOf T) = true
  /-- Fuel covers the telescope descent, the domain scan, and the
      whole-field occurrence scan (each burns one unit up front). -/
  fuelBound : esize T + piCount T + 2 ≤ fuel
  /-- A field that IS a family application has the canonical shape
      (exact parameter locals, `nparams + nindices` spine, stored
      canonical levels) — the shape analyser's positive clause. -/
  canon : isFamilyApp fam T = true →
      properShapeB fam nuniv nparams nindices (depth - 1) T = true
  /-- No inner-recursive escape: a Π-telescope whose tail is a
      canonical family application would be `.recursive inner` with
      `inner > 0` for the shape analyser but `none` for the legacy
      scan. -/
  noInner : piCount T = 0 ∨
      properShapeB fam nuniv nparams nindices (piCount T + depth - 1)
        (piTailOf T) = false

/-- Pointwise map from the legacy kind to the typed shape. -/
def shapeOfKind : RecKind → FieldShape
  | .plain => .nonrecursive
  | .directRec => .recursive 0

/-- The index list `fieldAnalyze` reports for a kind: empty for
`.plain`, the field's family-application indices for `.directRec`. -/
def kindIdx (nparams : Nat) (k : RecKind) (T : Expr Nat) :
    List (Expr Nat) :=
  match k with
  | .plain => []
  | .directRec => familyIdx nparams T

end Rcic.Declarative

namespace Rcic.Declarative

/-! ### Rigidity: `containsFamilyFuel` on transparent-body-free terms -/

theorem transparentBody_none_of_none {E : ResolvedEnv} {r : Nat}
    {ls ls' : List Level}
    (h : transparentBody E r ls = none) : transparentBody E r ls' = none := by
  unfold transparentBody at h ⊢
  cases hm : E.members r with
  | none => rfl
  | some m =>
      rw [hm] at h
      dsimp only at h ⊢
      by_cases htr : transparent m.mclass = true
      · rw [htr] at h ⊢
        rw [if_pos rfl] at h
        rw [if_pos rfl]
        cases hbody : m.body with
        | some b =>
            rw [hbody] at h
            simp at h
        | none => rfl
      · rw [if_neg htr] at h
        rw [if_neg htr]

theorem noTransparentB_const {E : ResolvedEnv} {r : Nat} {ls : List Level}
    (h : noTransparentB E (.const r ls) = true) : transparentBody E r ls = none := by
  simp only [noTransparentB] at h
  revert h
  cases transparentBody E r ls with
  | none => intro _; rfl
  | some _ => intro h'; simp at h'

theorem noTransparentB_foldApps {E : ResolvedEnv} :
    ∀ (f : Expr Nat) (args : List (Expr Nat)),
    noTransparentB E (foldApps f args) =
      (noTransparentB E f && args.all (noTransparentB E))
  | f, [] => by simp [foldApps]
  | f, x :: xs => by
      simp only [foldApps]
      rw [noTransparentB_foldApps (.app f x) xs, noTransparentB,
        List.all_cons, Bool.and_assoc]

theorem noTransparentB_head {E : ResolvedEnv} {T : Expr Nat}
    (hnt : noTransparentB E T = true) {r : Nat} {ls : List Level}
    {args : List (Expr Nat)}
    (hsp : appsSpine T = (.const r ls, args)) :
    transparentBody E r ls = none := by
  have hT : T = foldApps (.const r ls) args := by
    have := foldApps_appsSpine T
    rw [hsp] at this
    exact this.symm
  rw [hT, noTransparentB_foldApps, Bool.and_eq_true] at hnt
  exact noTransparentB_const hnt.1

/-- `noTransparentB` descends through the literal expansion: the constants
`lit t` hides (`1`, and `2` for `t ≥ 1`) are exactly what `natExpand t`
exposes. -/
theorem noTransparentB_natExpand {E : ResolvedEnv} :
    ∀ (t : Nat), noTransparentB E (.lit t) = true →
      noTransparentB E (natExpand t) = true
  | 0, h => h
  | m + 1, h => by
      obtain ⟨h1, h2⟩ : (transparentBody E 1 []).isNone = true ∧
          (transparentBody E 2 []).isNone = true := by
        simpa only [noTransparentB, Bool.and_eq_true] using h
      have him : noTransparentB E (.lit m) = true := by
        cases m with
        | zero => exact h1
        | succ _ =>
            show ((transparentBody E 1 []).isNone &&
              (transparentBody E 2 []).isNone) = true
            simp only [Bool.and_eq_true]
            exact ⟨h1, h2⟩
      have ih := noTransparentB_natExpand m him
      show ((transparentBody E 2 []).isNone && noTransparentB E (natExpand m)) = true
      simp only [Bool.and_eq_true]
      exact ⟨h2, ih⟩

/-- Fuel accounting on the literal expansion: `containsFamilyFuel` on
`natExpand m` costs `m + 1` nodes (`lit t` itself already burned one unit
entering the expansion). -/
theorem containsFamilyFuel_natExpand {E : ResolvedEnv} {fam : Nat} :
    ∀ (m g : Nat), noTransparentB E (natExpand m) = true → m + 1 ≤ g →
      containsFamilyFuel E fam g (natExpand m) = some (litOccurs fam m)
  | 0, g, hntg, hg => by
      cases g with
      | zero => omega
      | succ g' =>
          have htb : transparentBody E 1 [] = none := noTransparentB_const hntg
          simp only [natExpand, litZero, containsFamilyFuel, htb, litOccurs]
          by_cases h1 : 1 = fam
          · rw [if_pos h1]; subst h1; rfl
          · rw [if_neg h1, decide_eq_false (Ne.symm h1)]
  | m + 1, g, hntg, hg => by
      obtain ⟨h2, hrest⟩ : noTransparentB E (.const 2 []) = true ∧
          noTransparentB E (natExpand m) = true := by
        simpa only [natExpand, litSucc, noTransparentB, Bool.and_eq_true]
          using hntg
      have htb2 : transparentBody E 2 [] = none := noTransparentB_const h2
      cases g with
      | zero => omega
      | succ g' =>
          have hc : containsFamilyFuel E fam g' (.const 2 []) =
              some (decide (2 = fam)) := by
            cases g' with
            | zero => omega
            | succ _ =>
                simp only [containsFamilyFuel, htb2]
                by_cases h2f : 2 = fam
                · rw [if_pos h2f, decide_eq_true h2f]
                · rw [if_neg h2f, decide_eq_false h2f]
          show containsFamilyFuel E fam (g' + 1) (litSucc (natExpand m)) =
            some (litOccurs fam (m + 1))
          simp only [litSucc, containsFamilyFuel]
          rw [hc]
          by_cases h2f : 2 = fam
          · subst h2f
            rw [decide_eq_true rfl]
            rfl
          · rw [decide_eq_false h2f]
            have hlt : litOccurs fam (m + 1) = litOccurs fam m := by
              cases m with
              | zero =>
                  show (decide (fam = 1) || decide (fam = 2)) = decide (fam = 1)
                  rw [decide_eq_false (Ne.symm h2f), Bool.or_false]
              | succ _ => rfl
            rw [hlt]
            exact containsFamilyFuel_natExpand m g' hrest (by omega)

theorem whnfFuel_of_stable {E : ResolvedEnv} {fuel : Nat} {T : Expr Nat}
    (hnt : noTransparentB E T = true) (hst : headStableB T = true) :
    whnfFuel E (fuel + 1) T = some T := by
  simp only [whnfFuel]
  simp only [headStableB] at hst
  cases hsp : appsSpine T with
  | mk hd tl =>
      cases hd with
      | lam A B =>
          cases tl with
          | nil => rfl
          | cons a args => simp [hsp] at hst
      | letE A v B => simp [hsp] at hst
      | const r ls =>
          simp only [hsp]
          rw [transparentBody_none_of_none (noTransparentB_head hnt hsp) (ls' := ls)]
      | bvar _ => rfl
      | sort _ => rfl
      | pi _ _ => rfl
      | lit _ => rfl
      | app _ _ => rfl

theorem containsFamilyFuel_of_noTransparent {E : ResolvedEnv} {fam : Nat} :
    ∀ (T : Expr Nat) {fuel : Nat},
    noTransparentB E T = true → esize T + 1 ≤ fuel →
    containsFamilyFuel E fam fuel T = some (occursConst fam T)
  | .bvar _, fuel, _, hf => by
      cases fuel with
      | zero => omega
      | succ _ => rfl
  | .sort _, fuel, _, hf => by
      cases fuel with
      | zero => omega
      | succ _ => rfl
  | .lit t, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          have hf' : t + 1 ≤ f' := by simp only [esize] at hf; omega
          cases t with
          | zero =>
              show containsFamilyFuel E fam f' litZero =
                some (litOccurs fam 0)
              exact containsFamilyFuel_natExpand 0 f' hnt hf'
          | succ n =>
              simp only [noTransparentB, Bool.and_eq_true] at hnt
              obtain ⟨h1n, h2n⟩ := hnt
              have htb1 : transparentBody E 1 [] = none := by
                cases hb : transparentBody E 1 [] with
                | none => rfl
                | some _ => simp [hb] at h1n
              have htb2 : transparentBody E 2 [] = none := by
                cases hb : transparentBody E 2 [] with
                | none => rfl
                | some _ => simp [hb] at h2n
              cases f' with
              | zero => omega
              | succ f'' =>
                  show (match containsFamilyFuel E fam (f'' + 1) (.const 2 []) with
                        | some false =>
                            containsFamilyFuel E fam (f'' + 1) litZero
                        | r => r) = some (litOccurs fam (n + 1))
                  have hc2 : containsFamilyFuel E fam (f'' + 1) (.const 2 []) =
                      if 2 = fam then some true else some false := by
                    simp only [containsFamilyFuel, htb2]
                  rw [hc2]
                  by_cases h2f : 2 = fam
                  · rw [if_pos h2f]
                    subst h2f
                    rfl
                  · rw [if_neg h2f]
                    have hlt : litOccurs fam (n + 1) = decide (fam = 1) := by
                      simp only [litOccurs, decide_eq_false (Ne.symm h2f),
                        Bool.or_false]
                    rw [hlt]
                    show containsFamilyFuel E fam (f'' + 1) litZero =
                      some (decide (fam = 1))
                    simp only [litZero, containsFamilyFuel, htb1]
                    by_cases h1f : 1 = fam
                    · rw [if_pos h1f]
                      subst h1f
                      rfl
                    · rw [if_neg h1f, decide_eq_false (Ne.symm h1f)]
  | .const r ls, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          simp only [containsFamilyFuel]
          have hb := noTransparentB_const hnt
          by_cases hr : r = fam
          · rw [if_pos hr]
            subst hr
            simp only [occursConst]
            rfl
          · rw [if_neg hr, hb]
            simp only [occursConst]
            rw [decide_eq_false hr]
  | .app f x, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          simp only [noTransparentB, Bool.and_eq_true] at hnt
          simp only [esize] at hf
          simp only [containsFamilyFuel]
          have h1 := containsFamilyFuel_of_noTransparent f (fam := fam) hnt.1
            (by omega : esize f + 1 ≤ f')
          have h2 := containsFamilyFuel_of_noTransparent x (fam := fam) hnt.2
            (by omega : esize x + 1 ≤ f')
          rw [h1]
          simp only [occursConst]
          cases occursConst fam f with
          | true => rfl
          | false =>
              rw [h2]
              rfl
  | .lam A B, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          simp only [noTransparentB, Bool.and_eq_true] at hnt
          simp only [esize] at hf
          simp only [containsFamilyFuel]
          have h1 := containsFamilyFuel_of_noTransparent A (fam := fam) hnt.1
            (by omega : esize A + 1 ≤ f')
          have h2 := containsFamilyFuel_of_noTransparent B (fam := fam) hnt.2
            (by omega : esize B + 1 ≤ f')
          rw [h1]
          simp only [occursConst]
          cases occursConst fam A with
          | true => rfl
          | false =>
              rw [h2]
              rfl
  | .pi A B, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          simp only [noTransparentB, Bool.and_eq_true] at hnt
          simp only [esize] at hf
          simp only [containsFamilyFuel]
          have h1 := containsFamilyFuel_of_noTransparent A (fam := fam) hnt.1
            (by omega : esize A + 1 ≤ f')
          have h2 := containsFamilyFuel_of_noTransparent B (fam := fam) hnt.2
            (by omega : esize B + 1 ≤ f')
          rw [h1]
          simp only [occursConst]
          cases occursConst fam A with
          | true => rfl
          | false =>
              rw [h2]
              rfl
  | .letE A v B, fuel, hnt, hf => by
      cases fuel with
      | zero => omega
      | succ f' =>
          simp only [noTransparentB, Bool.and_eq_true] at hnt
          obtain ⟨⟨ha, hv⟩, hb'⟩ := hnt
          simp only [esize] at hf
          simp only [containsFamilyFuel]
          have h1 := containsFamilyFuel_of_noTransparent A (fam := fam) ha
            (by omega : esize A + 1 ≤ f')
          have h2 := containsFamilyFuel_of_noTransparent v (fam := fam) hv
            (by omega : esize v + 1 ≤ f')
          have h3 := containsFamilyFuel_of_noTransparent B (fam := fam) hb'
            (by omega : esize B + 1 ≤ f')
          rw [h1]
          simp only [occursConst]
          cases occursConst fam A with
          | true => rfl
          | false =>
              rw [h2]
              cases occursConst fam v with
              | true => rfl
              | false =>
                  rw [h3]
                  rfl

theorem piDomsOf_length : ∀ T : Expr Nat, (piDomsOf T).length = piCount T
  | .pi A B => by
      simp only [piDomsOf, piCount, List.length_cons, piDomsOf_length B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem noTransparentB_piTail {E : ResolvedEnv} :
    ∀ (T : Expr Nat), noTransparentB E T = true →
      noTransparentB E (piTailOf T) = true
  | .pi A B => by
      simp only [noTransparentB, Bool.and_eq_true, piTailOf]
      intro h
      exact noTransparentB_piTail B h.2
  | .bvar _ | .sort _ | .lit _ | .const _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ => by intro h; exact h

theorem piTailOf_piTail : ∀ T : Expr Nat, piTailOf (piTailOf T) = piTailOf T
  | .pi _ B => piTailOf_piTail B
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- `piTelescopeFuel` on a term whose telescope tail is rigid and
whnf-stable returns the structural Π-decomposition. -/
theorem piTelescopeFuel_of_tailStable {E : ResolvedEnv} :
    ∀ (T : Expr Nat) {fuel : Nat},
    noTransparentB E (piTailOf T) = true → headStableB (piTailOf T) = true →
    piCount T + 2 ≤ fuel →
    piTelescopeFuel E fuel T = some (piDomsOf T, piTailOf T)
  | .pi A B, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ f' =>
              rw [piTelescopeFuel.eq_2]
              have hpi : whnfFuel E (f' + 1) (.pi A B) = some (.pi A B) := rfl
              rw [hpi]
              have hnt' : noTransparentB E (piTailOf B) = true := hnt
              have hst' : headStableB (piTailOf B) = true := hst
              have hf' : piCount B + 2 ≤ f' + 1 := by
                simp only [piCount] at hf; omega
              have hrec := piTelescopeFuel_of_tailStable B hnt' hst' hf'
              simp only [hrec]
              rfl
  | .bvar a, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ f' =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .bvar a) hnt hst]
              rfl
  | .sort l, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ f' =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .sort l) hnt hst]
              rfl
  | .const r ls, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ f' =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .const r ls) hnt hst]
              rfl
  | .app f' x, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ fr =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .app f' x) hnt hst]
              rfl
  | .lam a b, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ fr =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .lam a b) hnt hst]
              rfl
  | .letE a v b, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ fr =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .letE a v b) hnt hst]
              rfl
  | .lit l, fuel, hnt, hst, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
          cases f with
          | zero => simp only [piCount] at hf; omega
          | succ fr =>
              rw [piTelescopeFuel.eq_2]
              rw [whnfFuel_of_stable (T := .lit l) hnt hst]
              rfl

end Rcic.Declarative

namespace Rcic.Declarative

/-! ### Occurrence structure of the syntactic Π decomposition -/

theorem occursConst_piTail {fam : Nat} :
    ∀ (T : Expr Nat), occursConst fam T = false →
      occursConst fam (piTailOf T) = false
  | .pi A B => by
      simp only [occursConst, Bool.or_eq_false_iff, piTailOf]
      intro h
      exact occursConst_piTail B h.2
  | .bvar _ | .sort _ | .lit _ | .const _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ => by intro h; exact h

theorem occursConst_piDom {fam : Nat} :
    ∀ (T : Expr Nat) (D : Expr Nat), occursConst fam T = false →
      D ∈ piDomsOf T → occursConst fam D = false
  | .pi A B, D, hT, hD => by
      simp only [occursConst, Bool.or_eq_false_iff] at hT
      simp only [piDomsOf, List.mem_cons] at hD
      cases hD with
      | inl hDA => exact hDA ▸ hT.1
      | inr hDB => exact occursConst_piDom B D hT.2 hDB
  | .bvar _, _, _, hD | .sort _, _, _, hD | .lit _, _, _, hD
    | .const _ _, _, _, hD | .app _ _, _, _, hD | .lam _ _, _, _, hD
    | .letE _ _ _, _, _, hD => by
        simp only [piDomsOf, List.mem_nil_iff] at hD

theorem noTransparentB_piDom {E : ResolvedEnv} :
    ∀ (T : Expr Nat) (D : Expr Nat), noTransparentB E T = true →
      D ∈ piDomsOf T → noTransparentB E D = true
  | .pi A B, D, hT, hD => by
      simp only [noTransparentB, Bool.and_eq_true] at hT
      simp only [piDomsOf, List.mem_cons] at hD
      cases hD with
      | inl hDA => exact hDA ▸ hT.1
      | inr hDB => exact noTransparentB_piDom B D hT.2 hDB
  | .bvar _, _, _, hD | .sort _, _, _, hD | .lit _, _, _, hD
    | .const _ _, _, _, hD | .app _ _, _, _, hD | .lam _ _, _, _, hD
    | .letE _ _ _, _, _, hD => by
        simp only [piDomsOf, List.mem_nil_iff] at hD

theorem esize_piDom_le :
    ∀ (T : Expr Nat) (D : Expr Nat), D ∈ piDomsOf T → esize D < esize T
  | .pi A B, D, hD => by
      simp only [piDomsOf, List.mem_cons, esize] at hD ⊢
      cases hD with
      | inl hDA => subst hDA; omega
      | inr hDB =>
          have := esize_piDom_le B D hDB
          omega
  | .bvar _, _, hD | .sort _, _, hD | .lit _, _, hD | .const _ _, _, hD
    | .app _ _, _, hD | .lam _ _, _, hD | .letE _ _ _, _, hD => by
        simp only [piDomsOf, List.mem_nil_iff] at hD

/-! ### `domainsContainFuel` / `indicesCleanFuel` on rigid lists -/

theorem domainsContainFuel_of_noTransparent {E : ResolvedEnv} {fam : Nat} :
    ∀ (Ts : List (Expr Nat)) {fuel : Nat},
    (∀ T ∈ Ts, noTransparentB E T = true) →
    (∀ T ∈ Ts, esize T + Ts.length + 1 ≤ fuel) →
    domainsContainFuel E fam fuel Ts =
      some (Ts.any fun T => occursConst fam T)
  | [], fuel, _, _ => by
      simp only [domainsContainFuel, List.any_nil]
  | T :: Ts, fuel, hnt, hf => by
      cases fuel with
      | zero =>
          have := hf T (by simp)
          omega
      | succ f' =>
          simp only [domainsContainFuel]
          have hTf : esize T + 1 ≤ f' := by
            have := hf T (by simp)
            simp only [List.length_cons] at this
            omega
          have hT := containsFamilyFuel_of_noTransparent (fam := fam) T
            (hnt T (by simp)) hTf
          rw [hT]
          have hrest := domainsContainFuel_of_noTransparent (E := E)
            (fam := fam) (fuel := f') Ts
            (fun x hx => hnt x (by simp [hx]))
            (fun x hx => by
              have := hf x (by simp [hx])
              simp only [List.length_cons] at this
              omega)
          rw [hrest]
          show _ = some (occursConst fam T || Ts.any _)
          cases occursConst fam T <;> rfl

theorem indicesCleanFuel_of_noTransparent {E : ResolvedEnv} {fam : Nat} :
    ∀ (Ts : List (Expr Nat)) {fuel : Nat},
    (∀ T ∈ Ts, noTransparentB E T = true) →
    (∀ T ∈ Ts, esize T + Ts.length + 1 ≤ fuel) →
    indicesCleanFuel E fam fuel Ts =
      some (Ts.any fun T => occursConst fam T)
  | [], fuel, _, _ => by
      simp only [indicesCleanFuel, List.any_nil]
  | T :: Ts, fuel, hnt, hf => by
      cases fuel with
      | zero =>
          have := hf T (by simp)
          omega
      | succ f' =>
          simp only [indicesCleanFuel]
          have hTf : esize T + 1 ≤ f' := by
            have := hf T (by simp)
            simp only [List.length_cons] at this
            omega
          have hT := containsFamilyFuel_of_noTransparent (fam := fam) T
            (hnt T (by simp)) hTf
          rw [hT]
          have hrest := indicesCleanFuel_of_noTransparent (E := E)
            (fam := fam) (fuel := f') Ts
            (fun x hx => hnt x (by simp [hx]))
            (fun x hx => by
              have := hf x (by simp [hx])
              simp only [List.length_cons] at this
              omega)
          rw [hrest]
          show _ = some (occursConst fam T || Ts.any _)
          cases occursConst fam T <;> rfl

theorem all_not_eq_not_any {α : Type} :
    ∀ (xs : List α) (p : α → Bool),
    xs.all (fun a => !(p a)) = !(xs.any p)
  | [], _ => rfl
  | x :: xs, p => by
      rw [List.all_cons, List.any_cons, all_not_eq_not_any xs p]
      cases p x <;> cases xs.any p <;> rfl

/-! ### `properFamilyFuel` reduces to `properShapeB` on rigid terms -/

/-- `properShapeB` unfolds to the conjunction `properFamilyFuel`
checks: family-const head, `nparams + nindices` arguments, exact
parameter locals, canonical levels, family-free indices. -/
theorem properShapeB_eq {fam nuniv nparams nindices top : Nat}
    {body : Expr Nat} :
    properShapeB fam nuniv nparams nindices top body =
      (match appsSpine body with
      | (.const r ls, args) =>
          decide (r = fam) && decide (args.length = nparams + nindices) &&
            exactParamLocals (args.take nparams) top &&
            decide (ls = (List.range nuniv).map Level.param) &&
            (args.drop nparams).all fun a => !(occursConst fam a)
      | _ => false) := rfl

theorem properFamilyFuel_of_noTransparent {E : ResolvedEnv}
    {fam nuniv nparams nindices top : Nat} {body : Expr Nat} {fuel : Nat}
    (hnt : noTransparentB E body = true)
    (hf : ∀ x ∈ (appsSpine body).2.drop nparams,
        esize x + ((appsSpine body).2.drop nparams).length + 1 ≤ fuel) :
    properFamilyFuel E fuel fam nuniv nparams nindices top body =
      some (properShapeB fam nuniv nparams nindices top body) := by
  simp only [properFamilyFuel, properShapeB]
  cases hsp : appsSpine body with
  | mk hd args =>
      cases hd with
      | const r ls =>
          simp only [hsp]
          by_cases hshape :
              (r = fam && args.length = nparams + nindices &&
                exactParamLocals (args.take nparams) top &&
                ls = (List.range nuniv).map Level.param) = true
          · rw [if_pos hshape]
            have hnt' := hnt
            have hT : body = foldApps (.const r ls) args := by
              have := foldApps_appsSpine body
              rw [hsp] at this
              exact this.symm
            rw [hT, noTransparentB_foldApps, Bool.and_eq_true] at hnt'
            have hall := hnt'.2
            simp only [List.all_eq_true] at hall
            have hcl := indicesCleanFuel_of_noTransparent (fam := fam)
              (args.drop nparams)
              (fun x hx => hall x (List.mem_of_mem_drop hx))
              (fun x hx => by
                have hxf := hf x (by rw [hsp]; exact hx)
                rwa [hsp] at hxf)
            rw [hcl]
            rw [hshape]
            rw [all_not_eq_not_any]
            cases (args.drop nparams).any (fun a => occursConst fam a) <;>
              rfl
          · rw [if_neg hshape]
            have hcf : (decide (r = fam) &&
                decide (args.length = nparams + nindices) &&
                exactParamLocals (args.take nparams) top &&
                decide (ls = (List.range nuniv).map Level.param)) = false :=
              Bool.eq_false_iff.mpr hshape
            rw [hcf]
            rfl
      | _ => rfl

end Rcic.Declarative

namespace Rcic.Declarative

/-! ### The pointwise correspondence -/

/-- `esize` is always positive. -/
theorem esize_pos : ∀ e : Expr Nat, 0 < esize e
  | .bvar _ => Nat.zero_lt_one
  | .sort _ => Nat.zero_lt_one
  | .lit _ => by simp only [esize]; omega
  | .const _ _ => Nat.zero_lt_one
  | .app _ _ => by simp only [esize]; omega
  | .lam _ _ => by simp only [esize]; omega
  | .pi _ _ => by simp only [esize]; omega
  | .letE _ _ _ => by simp only [esize]; omega

/-- The exact `esize` of a folded application spine. -/
theorem esize_foldApps : ∀ (f : Expr Nat) (args : List (Expr Nat)),
    esize (foldApps f args) =
      esize f + (args.map esize).sum + args.length
  | f, [] => by simp [foldApps, esize]
  | f, x :: xs => by
      simp only [foldApps, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [esize_foldApps (.app f x) xs]
      simp only [esize]
      omega

theorem esize_le_map_sum {a : Expr Nat} {xs : List (Expr Nat)}
    (h : a ∈ xs) : esize a ≤ (xs.map esize).sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.mem_cons] at h
      simp only [List.map_cons, List.sum_cons]
      cases h with
      | inl hx => subst hx; omega
      | inr hxs =>
          have := ih hxs
          omega

/-- Every dropped index argument of an application spine is small
enough for the fuelled scan, given the whole-spine bound. -/
theorem esize_mem_drop_spine_le {f : Expr Nat} {args : List (Expr Nat)}
    {n : Nat} {a : Expr Nat} (h : a ∈ args.drop n) :
    esize a + (args.drop n).length + 1 ≤ esize (foldApps f args) := by
  rw [esize_foldApps]
  have ha : a ∈ args := List.mem_of_mem_drop h
  have h1 := esize_le_map_sum ha
  have h2 : (args.drop n).length ≤ args.length := by
    rw [List.length_drop]
    omega
  have h3 := esize_pos f
  omega

/-- The `esize` of the Π-tail is bounded by the whole term. -/
theorem esize_piTail_le : ∀ T : Expr Nat, esize (piTailOf T) ≤ esize T
  | .pi A B => by
      simp only [piTailOf, esize]
      have := esize_piTail_le B
      omega
  | .bvar _ | .sort _ | .lit _ | .const _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ => Nat.le_refl _

/-- A term whose application spine is constant-headed is not a Π, so
the syntactic telescope is trivial on it. -/
theorem piTailOf_eq_self_of_const_spine {T : Expr Nat} {r : Nat}
    {ls : List Level} {args : List (Expr Nat)}
    (h : appsSpine T = (.const r ls, args)) :
    piTailOf T = T ∧ piDomsOf T = [] := by
  cases T with
  | pi A B => simp [appsSpine] at h
  | _ => exact ⟨rfl, rfl⟩

theorem piTailOf_eq_self_of_piCount_zero {T : Expr Nat}
    (h : piCount T = 0) : piTailOf T = T := by
  cases T with
  | pi A B => simp [piCount] at h
  | _ => rfl

theorem piDomsOf_eq_nil_of_piCount_zero {T : Expr Nat}
    (h : piCount T = 0) : piDomsOf T = [] := by
  cases T with
  | pi A B => simp [piCount] at h
  | _ => rfl

/-- `occursConst` distributes over a folded application spine. -/
theorem occursConst_foldApps {fam : Nat} :
    ∀ (f : Expr Nat) (args : List (Expr Nat)),
    occursConst fam (foldApps f args) =
      (occursConst fam f || args.any fun a => occursConst fam a)
  | f, [] => by simp [foldApps]
  | f, x :: xs => by
      simp only [foldApps, List.any_cons]
      rw [occursConst_foldApps (.app f x) xs, occursConst,
        Bool.or_assoc]

/-- `isFamilyApp` extracts a family-const-headed spine with
family-free arguments. -/
theorem isFamilyApp_spine {fam : Nat} {T : Expr Nat}
    (h : isFamilyApp fam T = true) :
    ∃ ls args, appsSpine T = (.const fam ls, args) ∧
      args.all (fun a => !(occursConst fam a)) = true := by
  simp only [isFamilyApp] at h
  cases hsp : appsSpine T with
  | mk hd args =>
      rw [hsp] at h
      cases hd with
      | const r ls =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hr, hargs⟩ := h
          subst hr
          exact ⟨ls, args, rfl, hargs⟩
      | _ => simp at h

/-- A family application always contains the family (its head does). -/
theorem occursConst_of_isFamilyApp {fam : Nat} {T : Expr Nat}
    (h : isFamilyApp fam T = true) : occursConst fam T = true := by
  obtain ⟨ls, args, hsp, _⟩ := isFamilyApp_spine h
  have hT : T = foldApps (.const fam ls) args := by
    have := foldApps_appsSpine T
    rw [hsp] at this
    exact this.symm
  rw [hT, occursConst_foldApps]
  simp [occursConst]

/-- `isFamilyApp`-headed terms are not Πs: the syntactic telescope is
trivial on them. -/
theorem piCount_eq_zero_of_isFamilyApp {fam : Nat} {T : Expr Nat}
    (h : isFamilyApp fam T = true) : piCount T = 0 := by
  obtain ⟨ls, args, hsp, _⟩ := isFamilyApp_spine h
  cases T with
  | pi A B => simp [appsSpine] at hsp
  | _ => rfl

/-- `exactParamLocals` forces every element to be a bound variable,
hence family-free. -/
theorem exactParamLocals_famfree {fam : Nat} :
    ∀ (xs : List (Expr Nat)) (top : Nat),
    exactParamLocals xs top = true →
      ∀ x ∈ xs, occursConst fam x = false
  | [], _, _ => by simp
  | e :: es, top, h => by
      simp only [exactParamLocals, Bool.and_eq_true,
        decide_eq_true_eq] at h
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl hxe =>
          subst hxe
          rw [h.1]
          rfl
      | inr hxes => exact exactParamLocals_famfree es (top - 1) h.2 x hxes

/-- `properShapeB` at `true` forces `isFamilyApp`: the exact-parameter
prefix and the family-free index check cover the whole spine. -/
theorem isFamilyApp_of_properShapeB {fam nuniv nparams nindices top : Nat}
    {body : Expr Nat}
    (h : properShapeB fam nuniv nparams nindices top body = true) :
    isFamilyApp fam body = true := by
  simp only [properShapeB] at h
  cases hsp : appsSpine body with
  | mk hd args =>
      rw [hsp] at h
      cases hd with
      | const r ls =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨hr, hlen⟩, hpl⟩, hls⟩, hdrop⟩ := h
          simp only [isFamilyApp]
          rw [hsp]
          rw [hr]
          show (decide (fam = fam) &&
              args.all fun a => !(occursConst fam a)) = true
          rw [decide_eq_true rfl, Bool.true_and]
          have hsplit : args = args.take nparams ++ args.drop nparams :=
            (List.take_append_drop nparams args).symm
          rw [hsplit, List.all_append, Bool.and_eq_true]
          refine ⟨?_, hdrop⟩
          rw [List.all_eq_true]
          intro x hx
          have hfm := exactParamLocals_famfree (fam := fam)
            (args.take nparams) top hpl x hx
          rw [hfm]
          rfl
      | _ => simp at h


/-- A domain of the syntactic Π telescope containing the family makes
the whole field contain it. -/
theorem occursConst_of_mem_piDoms {fam : Nat} :
    ∀ {T : Expr Nat} {D : Expr Nat},
    D ∈ piDomsOf T → occursConst fam D = true →
      occursConst fam T = true
  | .pi A B, D, hD, hDoc => by
      simp only [piDomsOf, List.mem_cons] at hD
      simp only [occursConst]
      cases hD with
      | inl hDA => subst hDA; rw [hDoc]; simp
      | inr hDB =>
          have := occursConst_of_mem_piDoms hDB hDoc
          rw [this]; simp
  | .bvar _, _, hD, _ | .sort _, _, hD, _ | .lit _, _, hD, _
    | .const _ _, _, hD, _ | .app _ _, _, hD, _ | .lam _ _, _, hD, _
    | .letE _ _ _, _, hD, _ => by simp [piDomsOf] at hD

/-- `fieldAnalyze` on the DIRECT fragment refines the legacy
`analyzeField`: `some` kinds map to `.permitted` shapes
(`plain ↦ nonrecursive`, `directRec ↦ recursive 0` with the family
indices), and a legacy `none` never maps to `.permitted`. This is the
pointwise half of the step-2b-2 correspondence; `DirectFieldFrag`
states exactly which inputs are covered — transparent δ inside the
domain, inner-recursive Π-telescopes (the FunRec extension point),
and non-canonical family applications are all excluded. -/
theorem fieldAnalyze_of_directFrag {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (h : DirectFieldFrag E fuel fam nuniv nparams nindices depth T) :
    (∀ k, analyzeField fam T = some k →
      fieldAnalyze E fuel fam nuniv nparams nindices depth T =
        .permitted (shapeOfKind k) (kindIdx nparams k T)) ∧
    (analyzeField fam T = none →
      ¬ ∃ s i, fieldAnalyze E fuel fam nuniv nparams nindices depth T =
        .permitted s i) := by
  obtain ⟨hrigid, hstable, hfuelB, hcanon, hnoInner⟩ := h
  cases fuel with
  | zero => exact absurd hfuelB (by omega)
  | succ f' =>
      have hpi := piTelescopeFuel_of_tailStable
        (E := E) (T := T) (fuel := f')
        (noTransparentB_piTail T hrigid) hstable (by
          have := esize_pos T
          omega)
      have hdoms := domainsContainFuel_of_noTransparent (E := E)
        (fam := fam) (fuel := f') (piDomsOf T)
        (fun D hD => noTransparentB_piDom T D hrigid hD)
        (fun D hD => by
          have hsz := esize_piDom_le T D hD
          have := piDomsOf_length T
          omega)
      have hcf := containsFamilyFuel_of_noTransparent (fam := fam)
        (E := E) T hrigid (by omega : esize T + 1 ≤ f')
      have hpf := properFamilyFuel_of_noTransparent (E := E) (fam := fam)
        (nuniv := nuniv) (nindices := nindices)
        (top := (piDomsOf T).length + depth - 1)
        (fuel := f') (body := piTailOf T)
        (noTransparentB_piTail T hrigid)
        (fun x hx => by
          have hfold : piTailOf T = foldApps (appsSpine (piTailOf T)).1
              (appsSpine (piTailOf T)).2 :=
            (foldApps_appsSpine _).symm
          have hsz := esize_mem_drop_spine_le
            (f := (appsSpine (piTailOf T)).1) (n := nparams) hx
          rw [← hfold] at hsz
          have hle := esize_piTail_le T
          omega)
      simp only [fieldAnalyze]
      rw [hpi]
      dsimp only
      rw [hdoms]
      by_cases hfa : isFamilyApp fam T = true
      · -- directRec: spine head is const → piCount = 0
        have hpc0 := piCount_eq_zero_of_isFamilyApp hfa
        have hdms := piDomsOf_eq_nil_of_piCount_zero hpc0
        have htl := piTailOf_eq_self_of_piCount_zero hpc0
        have hoccT : occursConst fam T = true :=
          occursConst_of_isFamilyApp hfa
        rw [hdms]
        simp only [List.any_nil, List.length_nil, Nat.zero_add]
        rw [htl]
        rw [hdms, List.length_nil, Nat.zero_add, htl] at hpf
        rw [hpf, hcanon hfa]
        -- goal: .permitted (.recursive 0) (familyIdx np T) = ...
        constructor
        · intro k hk
          have haf : analyzeField fam T = some .directRec := by
            simp only [analyzeField]
            rw [if_neg (by rw [hoccT]; simp), if_pos hfa]
          rw [haf] at hk
          injection hk with hk'
          subst hk'
          rfl
        · intro hnone
          have haf : analyzeField fam T = some .directRec := by
            simp only [analyzeField]
            rw [if_neg (by rw [hoccT]; simp), if_pos hfa]
          rw [haf] at hnone
          contradiction
      · have hfa' : isFamilyApp fam T = false :=
          Bool.eq_false_iff.mpr (fun hc => hfa hc)
        cases hdomAny : (piDomsOf T).any
            (fun D => occursConst fam D) with
        | true =>
            constructor
            · intro k hk
              have hocc : occursConst fam T = true := by
                rw [List.any_eq_true] at hdomAny
                obtain ⟨D, hD, hDoc⟩ := hdomAny
                exact occursConst_of_mem_piDoms hD hDoc
              have haf : analyzeField fam T = none := by
                simp only [analyzeField]
                rw [if_neg (by rw [hocc]; simp), if_neg (by simp [hfa'])]
              rw [haf] at hk; contradiction
            · intro _ hcon
              obtain ⟨s, i, hsi⟩ := hcon
              simp only [fieldAnalyze, hpi, hdoms, hdomAny] at hsi
              contradiction
        | false =>
            rw [hpf]
            cases hps : properShapeB fam nuniv nparams nindices
                ((piDomsOf T).length + depth - 1) (piTailOf T) with
            | true =>
                -- inner-recursive: excluded by noInner unless
                -- piCount = 0, which contradicts isFamilyApp=false
                have hinner0 : piCount T = 0 := hnoInner.elim
                  (fun hp => hp)
                  (fun hbad => by
                    rw [piDomsOf_length] at hps
                    rw [hps] at hbad
                    contradiction)
                have htl := piTailOf_eq_self_of_piCount_zero hinner0
                rw [piDomsOf_length] at hps
                rw [htl] at hps
                have hfam' := isFamilyApp_of_properShapeB hps
                rw [hfa'] at hfam'
                contradiction
            | false =>
                rw [hcf]
                cases hocc : occursConst fam T with
                | false =>
                    constructor
                    · intro k hk
                      simp only [analyzeField] at hk
                      rw [if_pos (by rw [hocc]; rfl)] at hk
                      injection hk with hk'
                      subst hk'
                      rfl
                    · intro hn
                      simp only [analyzeField] at hn
                      rw [if_pos (by rw [hocc]; rfl)] at hn
                      contradiction
                | true =>
                    constructor
                    · intro k hk
                      have haf : analyzeField fam T = none := by
                        simp only [analyzeField]
                        rw [if_neg (by rw [hocc]; simp), if_neg (by simp [hfa'])]
                      rw [haf] at hk; contradiction
                    · intro _ hcon
                      obtain ⟨s, i, hsi⟩ := hcon
                      simp only [fieldAnalyze, hpi, hdoms, hdomAny, hpf,
                        hps, hcf, hocc] at hsi
                      cases hsp : appsSpine (piTailOf T) with
                      | mk hd args =>
                          cases hd with
                          | const r ls =>
                              simp only [hsp] at hsi
                              by_cases hr : r = fam
                              · rw [if_pos hr] at hsi
                                contradiction
                              · rw [if_neg hr] at hsi
                                have hdomsA :=
                                  domainsContainFuel_of_noTransparent
                                  (E := E) (fam := fam) (fuel := f') args
                                  (fun D hD => by
                                    have hta := noTransparentB_piTail T
                                      hrigid
                                    have hT : piTailOf T =
                                        foldApps (.const r ls) args := by
                                      have := foldApps_appsSpine
                                        (piTailOf T)
                                      rw [hsp] at this
                                      exact this.symm
                                    rw [hT, noTransparentB_foldApps,
                                      Bool.and_eq_true] at hta
                                    rw [List.all_eq_true] at hta
                                    exact hta.2 D hD)
                                  (fun D hD => by
                                    have hsz :=
                                      esize_mem_drop_spine_le
                                      (f := .const r ls)
                                      (args := args) (n := 0) hD
                                    simp only [List.drop_zero] at hsz
                                    have hT : piTailOf T =
                                        foldApps (.const r ls) args := by
                                      have := foldApps_appsSpine
                                        (piTailOf T)
                                      rw [hsp] at this
                                      exact this.symm
                                    rw [← hT] at hsz
                                    have hle := esize_piTail_le T
                                    omega)
                                cases hdomsA' : (args.any
                                    fun D => occursConst fam D) with
                                | true =>
                                    rw [hdomsA, hdomsA'] at hsi
                                    contradiction
                                | false =>
                                    rw [hdomsA, hdomsA'] at hsi
                                    contradiction
                          | _ =>
                              simp only [hsp] at hsi
                              contradiction


/-- List-level correspondence: `fieldShapesFuel` refines
`analyzeFields` pointwise through `shapeOfKind` on the DIRECT
fragment, taken at the running telescope depth `depth + j`. -/
theorem fieldShapesFuel_eq_analyzeFields_of_directFrag {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} :
    ∀ (Ts : List (Expr Nat)),
    (∀ j (hj : j < Ts.length),
        DirectFieldFrag E fuel fam nuniv nparams nindices (depth + j)
          Ts[j]) →
    fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts =
      (analyzeFields fam Ts).map fun ks => ks.map shapeOfKind
  | [], _ => rfl
  | T :: Ts, hfr => by
      have h0 := hfr 0 (by simp)
      have hT := fieldAnalyze_of_directFrag (E := E) (fuel := fuel)
        (fam := fam) (nuniv := nuniv) (nparams := nparams)
        (nindices := nindices) (depth := depth) (T := T) h0
      have hrest : ∀ j (hj : j < Ts.length),
          DirectFieldFrag E fuel fam nuniv nparams nindices
            (depth + 1 + j) Ts[j] := by
        intro j hj
        have h' := hfr (j + 1) (by simp [List.length_cons]; omega)
        rwa [List.getElem_cons_succ,
          show depth + (j + 1) = depth + 1 + j by omega] at h'
      have ih := fieldShapesFuel_eq_analyzeFields_of_directFrag Ts hrest
      simp only [fieldShapesFuel, analyzeFields]
      cases haf : analyzeField fam T with
      | some k =>
          rw [hT.1 k haf, ih]
          cases analyzeFields fam Ts with
          | some ks => rfl
          | none => rfl
      | none =>
          have hnp := hT.2 haf
          cases hfa : fieldAnalyze E fuel fam nuniv nparams nindices
              depth T with
          | permitted s i =>
              exact absurd ⟨s, i, hfa⟩ hnp
          | refused _ => rfl
          | unresolved => rfl


/-! ### Substitution algebra: `instOff`, `exprClosedAt`, prefix composition -/

theorem exprClosedAt_mono {c c' : Nat} {e : Expr Nat}
    (h : exprClosedAt c e = true) (hc : c ≤ c') :
    exprClosedAt c' e = true := by
  induction e generalizing c c' with
  | bvar i =>
      simp only [exprClosedAt, decide_eq_true_eq] at h ⊢
      omega
  | sort _ => rfl
  | lit _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx =>
      simp only [exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihf h.1 hc, ihx h.2 hc⟩
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihA h.1 hc, ihB h.2 (by omega)⟩
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihA h.1 hc, ihB h.2 (by omega)⟩
  | letE A v B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ihA h.1.1 hc, ihv h.1.2 hc⟩, ihB h.2 (by omega)⟩

theorem lift_amt_eq_of_exprClosedAt_le {c d a : Nat} {e : Expr Nat}
    (h : exprClosedAt c e = true) (hc : c ≤ d) : lift d a e = e := by
  induction e generalizing c d a with
  | bvar i =>
      simp only [exprClosedAt, decide_eq_true_eq] at h
      simp only [lift]
      rw [if_neg (by omega)]
  | sort _ => rfl
  | lit _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihf h.1 hc, ihx h.2 hc]
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hc,
        ihB h.2 (show c + 1 ≤ d + 1 by omega)]
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hc,
        ihB h.2 (show c + 1 ≤ d + 1 by omega)]
  | letE A v B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1.1 hc, ihv h.1.2 hc,
        ihB h.2 (show c + 1 ≤ d + 1 by omega)]

theorem exprClosedAt_lift {m d a : Nat} {e : Expr Nat}
    (h : exprClosedAt m e = true) :
    exprClosedAt (m + a) (lift d a e) = true := by
  induction e generalizing m d a with
  | bvar i =>
      simp only [exprClosedAt, decide_eq_true_eq] at h
      simp only [lift]
      by_cases hi : d ≤ i
      · rw [if_pos hi]
        simp only [exprClosedAt, decide_eq_true_eq]
        omega
      · rw [if_neg hi]
        simp only [exprClosedAt, decide_eq_true_eq]
        omega
  | sort _ => rfl
  | lit _ => rfl
  | const _ _ => rfl
  | app f x ihf ihx =>
      simp only [lift, exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihf h.1, ihx h.2⟩
  | lam A B ihA ihB =>
      simp only [lift, exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihA h.1,
        Nat.add_right_comm m 1 a ▸ ihB (m := m + 1) (d := d + 1) (a := a) h.2⟩
  | pi A B ihA ihB =>
      simp only [lift, exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ihA h.1,
        Nat.add_right_comm m 1 a ▸ ihB (m := m + 1) (d := d + 1) (a := a) h.2⟩
  | letE A v B ihA ihv ihB =>
      simp only [lift, exprClosedAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ihA h.1.1, ihv h.1.2⟩,
        Nat.add_right_comm m 1 a ▸ ihB (m := m + 1) (d := d + 1) (a := a) h.2⟩

/-- `instOff k xs e`: instantiate `xs` left-to-right at offset `k`.
`instOff 0 = instPrefix`; `instOff 1 = instTel`-flavoured stepping. -/
def instOff (k : Nat) : List (Expr Nat) → Expr Nat → Expr Nat
  | [], e => e
  | a :: as, e => instOff k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e)

theorem instOff_cons (k : Nat) (a : Expr Nat) (as : List (Expr Nat)) (e : Expr Nat) :
    instOff k (a :: as) e =
      instOff k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e) := rfl

theorem instOff_zero (xs : List (Expr Nat)) (e : Expr Nat) :
    instOff 0 xs e = instPrefix xs e := by
  induction xs generalizing e with
  | nil => rfl
  | cons a as ih =>
      simp only [instOff_cons, List.length_cons, instPrefix_cons, Nat.zero_add]
      exact ih _

theorem instPrefix_append (xs rest : List (Expr Nat)) (e : Expr Nat) :
    instPrefix (xs ++ rest) e = instPrefix rest (instOff rest.length xs e) := by
  induction xs generalizing e with
  | nil => simp only [List.nil_append, instOff]
  | cons a as ih =>
      simp only [List.cons_append, instPrefix_cons, List.length_append]
      rw [ih]
      congr 1
      show instOff rest.length as
            (instantiate (as.length + rest.length)
              (lift 0 (as.length + rest.length) a) e) =
          instOff rest.length (a :: as) e
      rw [instOff_cons]
      have heq : rest.length + as.length = as.length + rest.length := Nat.add_comm _ _
      rw [heq]

theorem instOff_instantiate (k : Nat) (xs : List (Expr Nat)) (v e : Expr Nat) :
    instOff k xs (instantiate k v e) =
      instantiate k (instOff k xs v) (instOff (k + 1) xs e) := by
  induction xs generalizing v e with
  | nil => simp only [instOff]
  | cons a as ih =>
      have hcom :
          instantiate (k + as.length) (lift 0 (k + as.length) a)
              (instantiate k v e) =
            instantiate k (instantiate (k + as.length) (lift 0 (k + as.length) a) v)
              (instantiate (k + as.length + 1)
                (lift k 1 (lift 0 (k + as.length) a)) e) := by
        rw [instantiate_instantiate k (k + as.length) v
            (lift 0 (k + as.length) a) (by omega) e]
      have hmerge : lift k 1 (lift 0 (k + as.length) a) =
          lift 0 (k + as.length + 1) a := by
        have h := lift_lift_merge 1 (k + as.length) 0 k (by omega) (by omega) a
        simp only [Nat.zero_add] at h
        rw [h]
      have hk : k + 1 + as.length = k + as.length + 1 := by omega
      simp only [instOff_cons, List.length_cons]
      rw [hcom, hmerge, ih]
      show instantiate k
          (instOff k as (instantiate (k + as.length) (lift 0 (k + as.length) a) v))
          (instOff (k + 1) as
            (instantiate (k + as.length + 1) (lift 0 (k + as.length + 1) a) e)) =
        instantiate k (instOff k (a :: as) v) (instOff (k + 1) (a :: as) e)
      rw [show instOff k (a :: as) v =
          instOff k as (instantiate (k + as.length) (lift 0 (k + as.length) a) v) from rfl]
      rw [show instOff (k + 1) (a :: as) e =
          instOff (k + 1) as
            (instantiate (k + 1 + as.length) (lift 0 (k + 1 + as.length) a) e) from rfl]
      rw [hk]

theorem instOff_lift (k : Nat) (xs : List (Expr Nat)) (v : Expr Nat) :
    instOff k xs (lift 0 k v) = lift 0 k (instPrefix xs v) := by
  induction xs generalizing k v with
  | nil => simp only [instOff, instPrefix]
  | cons a as ih =>
      simp only [instOff_cons, List.length_cons, instPrefix_cons]
      have hinner : instantiate (k + as.length) (lift 0 (k + as.length) a)
          (lift 0 k v) =
        lift 0 k (instantiate as.length (lift 0 as.length a) v) := by
        have h := lift_instantiate_high k 0 as.length (lift 0 as.length a)
          (by omega) v
        rw [h]
        congr 1
        have hm := lift_lift_merge k as.length 0 0 (by omega) (by omega) a
        simp only [Nat.zero_add] at hm
        rw [hm]
        congr 1
        omega
      rw [hinner, ih]

/-- Prefix instantiation composes: `instPrefix xs` after `instPrefix ys`
instantiates the merged prefix, with `ys`'s entries transported. -/
theorem instPrefix_instPrefix (xs ys : List (Expr Nat)) (e : Expr Nat) :
    instPrefix xs (instPrefix ys e) =
      instPrefix (xs ++ ys.map (instPrefix xs)) e := by
  induction ys generalizing e with
  | nil => simp only [instPrefix_nil, List.map_nil, List.append_nil]
  | cons y ys' ih =>
      simp only [instPrefix_cons, List.map_cons, List.cons_append]
      rw [ih]
      rw [instPrefix_append xs (ys'.map (instPrefix xs))]
      rw [instPrefix_append xs (instPrefix xs y :: ys'.map (instPrefix xs))]
      have hlen1 : (ys'.map (instPrefix xs)).length = ys'.length :=
        List.length_map ys' (instPrefix xs)
      have hlen2 : (instPrefix xs y :: ys'.map (instPrefix xs)).length =
          ys'.length + 1 := by
        simp [List.length_cons, List.length_map]
      rw [hlen1, hlen2]
      rw [instPrefix_cons]
      congr 1
      rw [hlen1, instOff_instantiate, instOff_lift]

/-- A term closed at `post.length` ignores the `pre` part of the
instantiated prefix — this is the field-prefix/parameter-prefix split
used at index positions. -/
theorem instPrefix_append_front_closed (pre post : List (Expr Nat)) (e : Expr Nat)
    (he : exprClosedAt post.length e = true) :
    instPrefix (pre ++ post) e = instPrefix post e := by
  induction pre generalizing e with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, instPrefix_cons, List.length_append]
      rw [show instantiate (as.length + post.length)
          (lift 0 (as.length + post.length) a) e = e from
        instantiate_eq_of_exprClosedAt_le he (by omega)
          (lift 0 (as.length + post.length) a)]
      exact ih _ he

theorem instOff_closed (k : Nat) (xs : List (Expr Nat)) (e : Expr Nat)
    (he : exprClosedAt k e = true) : instOff k xs e = e := by
  induction xs generalizing e with
  | nil => rfl
  | cons a as ih =>
      simp only [instOff_cons]
      rw [show instantiate (k + as.length)
          (lift 0 (k + as.length) a) e = e from
        instantiate_eq_of_exprClosedAt_le he (by omega) _]
      exact ih e he

theorem fieldBvars_length (nf : Nat) : (fieldBvars nf).length = nf := by
  unfold fieldBvars
  simp

theorem fieldBvars_getElem? (nf u : Nat) (hu : u < nf) :
    (fieldBvars nf)[u]? = some (.bvar (nf - 1 - u)) := by
  unfold fieldBvars
  rw [List.getElem?_map,
    List.getElem?_reverse (i := u) (l := List.range nf)
      (by rw [List.length_range]; exact hu)]
  rw [List.length_range,
    List.getElem?_range (m := nf - 1 - u) (n := nf) (by omega)]
  rfl

theorem fieldBvars_getElem (nf u : Nat) (hu : u < nf)
    (h : u < (fieldBvars nf).length := by rw [fieldBvars_length]; exact hu) :
    (fieldBvars nf)[u] = .bvar (nf - 1 - u) := by
  have h' := fieldBvars_getElem? nf u hu
  rw [List.getElem?_eq_getElem] at h'
  exact Option.some.inj h' 

/-- `instPrefix (pm ++ fs)` maps the canonical field bvar
`bvar (nf - 1 - i)` to `fs[i]`, taking `i` fields at a time. -/
theorem fieldBvars_take_map_instPrefix
    {args pm fs : List (Expr Nat)} {np nf i : Nat}
    (hargs : args = pm ++ fs) (hpm : pm.length = np + (args.length - np - nf))
    (hfs : fs.length = nf) (hi : i ≤ nf) :
    ((fieldBvars nf).take i).map (instPrefix args) = fs.take i := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, fieldBvars_length, hfs]
  · intro u hu1 hu2
    simp only [List.getElem_map, List.getElem_take]
    have hu : u < nf := by
      have h1 := hu1
      simp only [List.length_map, List.length_take, fieldBvars_length] at h1
      omega
    rw [fieldBvars_getElem nf u hu]
    have hL : args.length - 1 - (nf - 1 - u) = pm.length + u := by
      rw [hargs, List.length_append, hpm, hfs]
      omega
    have hb : instPrefix args (.bvar (nf - 1 - u)) = fs[u] := by
      apply instPrefix_bvar_lt
      · rw [hargs, List.length_append]; omega
      · rw [hL, hargs,
          List.getElem?_append_right (by omega : pm.length ≤ pm.length + u),
          show pm.length + u - pm.length = u from by omega,
          List.getElem?_eq_getElem]
    exact hb


/-! ### The whole-witness DIRECT recognizer and the `IotaWitness →
`IotaWitnessS` adapter

The theorems above relate the two field ANALYSES.  The witness
adapter needs one more piece of agreement: the open ι schema
`iotaOpenRhs` computes on the canonical context must instantiate, at
the redex's `preMajor ++ fields`, to the legacy `iotaRhsOf`.  That is
an equational claim about two different substitution traversals; the
recognizer CHECKS it (`decide`), so any witness where the two
computations genuinely diverge is refused, not patched.  The
structural correspondence (`fieldAnalyze_of_directFrag` /
`fieldShapesFuel_eq_analyzeFields_of_directFrag`) is proved on the
fragment; the RHS equality is discharged by computation under it. -/

/-- The schema `IotaWitnessS` stores, computed on admission's
analyser at the canonical equation context: the recursor head at
canonical levels, the minor as `bvar`, `preMajor`/`fields` as the
context bvars, and the lifted raw constructor field telescope.
`none` when `iotaArgs` fails at `fuel`. -/
def iotaSchemaS (w : IotaWitness E) (fuel : Nat) : Option (Expr Nat) :=
  iotaOpenRhs E fuel
    (.const w.recRef (canonRecLevels w.recMember.arity))
    (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
    (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
    w.nparams w.nMinors (w.kinds.map shapeOfKind)
    (fieldBvars w.fields.length)
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))

/-- Per-field DIRECT-fragment Boolean check at telescope `depth`
(the field's parameter-prefix depth, `nparams + j` at field `j`).
Mirrors `DirectFieldFrag` pointwise. -/
def directFragOne (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) (T : Expr Nat) :
    Bool :=
  noTransparentB E T && headStableB (piTailOf T) &&
  decide (esize T + piCount T + 2 ≤ fuel) &&
  (!(isFamilyApp fam T) ||
    properShapeB fam nuniv nparams nindices (depth - 1) T) &&
  (decide (piCount T = 0) ||
    !(properShapeB fam nuniv nparams nindices
      (piCount T + depth - 1) (piTailOf T)))

/-- The fragment check over the stored constructor domains after the
parameter prefix, threading the telescope depth `nparams + j`. -/
def directFragCheck (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) :
    List (Expr Nat) → Bool
  | [] => true
  | T :: Ts =>
      directFragOne E fuel fam nuniv nparams nindices depth T &&
      directFragCheck E fuel fam nuniv nparams nindices (depth + 1) Ts

/-- Read a successful `directFragOne` back as `DirectFieldFrag`. -/
theorem directFragOfCheck {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (h : directFragOne E fuel fam nuniv nparams nindices depth T =
      true) :
    DirectFieldFrag E fuel fam nuniv nparams nindices depth T := by
  unfold directFragOne at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpre4, hnoin⟩ := h
  rw [Bool.and_eq_true] at hpre4
  obtain ⟨hpre3, hcan⟩ := hpre4
  rw [Bool.and_eq_true] at hpre3
  obtain ⟨hpre2, hfuel⟩ := hpre3
  rw [Bool.and_eq_true] at hpre2
  obtain ⟨hrig, hstab⟩ := hpre2
  exact {
    rigid := hrig
    stableTail := hstab
    fuelBound := of_decide_eq_true hfuel
    canon := by
      intro hf
      rw [Bool.or_eq_true] at hcan
      cases hcan with
      | inl hnl =>
          rw [hf] at hnl
          exact absurd hnl (by decide)
      | inr hp => exact hp
    noInner := by
      rw [Bool.or_eq_true] at hnoin
      cases hnoin with
      | inl hp0 => exact Or.inl (of_decide_eq_true hp0)
      | inr hnp =>
          right
          cases hp : properShapeB fam nuniv nparams nindices
              (piCount T + depth - 1) (piTailOf T)
          · rfl
          · rw [hp] at hnp
            exact absurd hnp (by decide) }

/-- Read `directFragCheck` back pointwise at each index. -/
theorem directFragCheck_getElem {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} :
    ∀ (Ts : List (Expr Nat)) {j : Nat} (hj : j < Ts.length),
      directFragCheck E fuel fam nuniv nparams nindices depth Ts =
        true →
      DirectFieldFrag E fuel fam nuniv nparams nindices (depth + j)
        Ts[j]
  | [], _, hj, _ => absurd hj (by simp)
  | T :: Ts, j, hj, h => by
      simp only [directFragCheck, Bool.and_eq_true] at h
      cases j with
      | zero => exact directFragOfCheck h.1
      | succ j =>
          have ih := directFragCheck_getElem Ts
            (by simp only [List.length_cons] at hj; omega :
              j < Ts.length) h.2
          rwa [List.getElem_cons_succ,
            show depth + (j + 1) = depth + 1 + j by omega]

/-- The DIRECT adapter recognizer — a computable sufficient condition
for `iotaWitnessSOf`.  The three conjuncts are (i) the per-field
DIRECT fragment, (ii) the `iotaWitnessStableB` closure check used by
`iotaWitnessS_hstable_of_constsMemberFuel`, and (iii) the schema
conjunct: admission's `iotaOpenRhs` succeeds at `fuel`, its result is
closed at the equation context's cutoff, and its instance at
`preMajor ++ fields` EQUALS `iotaRhsOf w`.  The last is decided, not
assumed: a witness whose typed schema and legacy RHS disagree (for
instance an index argument mentioning constructor parameters, where
`familyIdx` and canonical-position instantiation can differ) makes
the recognizer `false` and is reported, never adapted. -/
def iotaWitnessSB (w : IotaWitness E) (fuel : Nat) : Bool :=
  directFragCheck E fuel w.familyRef w.famMember.arity w.nparams
    w.nindices w.nparams (w.ctorDoms.drop w.nparams) &&
  iotaWitnessStableB E fuel (w.ctorDoms.drop w.nparams)
    (fieldBvars w.fields.length)
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) &&
  match iotaSchemaS w fuel with
  | none => false
  | some schema =>
      exprClosedAt
        (w.nparams + 1 + w.nMinors + w.nindices + w.fields.length)
        schema &&
      decide (instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls schema) = iotaRhsOf w)

/-- The recognizer decomposes into its three conjuncts, with the
fragment check read back as pointwise `DirectFieldFrag`s. -/
theorem iotaWitnessSB_iff_parts {w : IotaWitness E} {fuel : Nat}
    (h : iotaWitnessSB w fuel = true) :
    (∀ j (hj : j < (w.ctorDoms.drop w.nparams).length),
        DirectFieldFrag E fuel w.familyRef w.famMember.arity w.nparams
          w.nindices (w.nparams + j)
          ((w.ctorDoms.drop w.nparams)[j])) ∧
    iotaWitnessStableB E fuel (w.ctorDoms.drop w.nparams)
      (fieldBvars w.fields.length)
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true ∧
    ∃ schema, iotaSchemaS w fuel = some schema ∧
      exprClosedAt
        (w.nparams + 1 + w.nMinors + w.nindices + w.fields.length)
        schema = true ∧
      instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls schema) = iotaRhsOf w := by
  unfold iotaWitnessSB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpre, hmatch⟩ := h
  rw [Bool.and_eq_true] at hpre
  obtain ⟨hfrag, hstable⟩ := hpre
  refine ⟨?_, hstable, ?_⟩
  · intro j hj
    exact directFragCheck_getElem _ hj hfrag
  · cases hO : iotaSchemaS w fuel with
    | none =>
        rw [hO] at hmatch
        simp only at hmatch
        exact absurd hmatch (by decide)
    | some s =>
        rw [hO] at hmatch
        simp only at hmatch
        rw [Bool.and_eq_true] at hmatch
        exact ⟨s, rfl, hmatch.1, of_decide_eq_true hmatch.2⟩

/-- Adapt a legacy `IotaWitness` to the typed `IotaWitnessS`, given
the recognizer's success.  Every field of the redex identity is
carried verbatim; `shapes` is `kinds.map shapeOfKind`; `hshapes` is
the proved list-level correspondence under the checked fragment;
`hschema`/`hstable`/`hschemaScope` are read off the checked conjuncts.
-/
def iotaWitnessSOf (w : IotaWitness E) (fuel : Nat)
    (h : iotaWitnessSB w fuel = true) : IotaWitnessS E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := w.preMajor
  fields := w.fields
  ctorParams := w.ctorParams
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := w.hctorParams
  hnpar := w.hnpar
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := w.hpre
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := w.hpeel
  hfamApp := w.hfamApp
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  fuel := fuel
  shapes := w.kinds.map shapeOfKind
  hshapes := by
    obtain ⟨hfr, _, _⟩ := iotaWitnessSB_iff_parts h
    have hc := fieldShapesFuel_eq_analyzeFields_of_directFrag
      (E := E) (fuel := fuel) (fam := w.familyRef)
      (nuniv := w.famMember.arity) (nparams := w.nparams)
      (nindices := w.nindices) (depth := w.nparams)
      (w.ctorDoms.drop w.nparams) hfr
    rw [w.hkinds] at hc
    exact hc
  schema := (iotaSchemaS w fuel).getD (.bvar 0)
  hschema := by
    obtain ⟨_, _, s, hO, _, _⟩ := iotaWitnessSB_iff_parts h
    have hget : (iotaSchemaS w fuel).getD (.bvar 0) = s := by
      rw [hO, Option.getD_some]
    rw [hget]
    unfold iotaSchemaS at hO
    exact hO
  hstable := by
    obtain ⟨hfr, hstab, s, hO, _, _⟩ := iotaWitnessSB_iff_parts h
    have hget : (iotaSchemaS w fuel).getD (.bvar 0) = s := by
      rw [hO, Option.getD_some]
    rw [hget]
    have hsh : fieldShapesFuel E fuel w.familyRef w.famMember.arity
        w.nparams w.nindices w.nparams (w.ctorDoms.drop w.nparams) =
        some (w.kinds.map shapeOfKind) := by
      have hc := fieldShapesFuel_eq_analyzeFields_of_directFrag
        (E := E) (fuel := fuel) (fam := w.familyRef)
        (nuniv := w.famMember.arity) (nparams := w.nparams)
        (nindices := w.nindices) (depth := w.nparams)
        (w.ctorDoms.drop w.nparams) hfr
      rw [w.hkinds] at hc
      exact hc
    have hsc : iotaOpenRhs E fuel
        (.const w.recRef (canonRecLevels w.recMember.arity))
        (.bvar (w.fields.length + w.nindices +
          (w.nMinors - 1 - w.ctorIdx)))
        (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
        w.nparams w.nMinors (w.kinds.map shapeOfKind)
        (fieldBvars w.fields.length)
        (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
        some s := by unfold iotaSchemaS at hO; exact hO
    exact iotaWitnessS_hstable_of_constsMemberFuel hsh hsc hstab
  hschemaScope := by
    obtain ⟨_, _, s, hO, hcl, _⟩ := iotaWitnessSB_iff_parts h
    have hget : (iotaSchemaS w fuel).getD (.bvar 0) = s := by
      rw [hO, Option.getD_some]
    rw [hget]
    exact hcl

/-- The adapted witness has the same ι left-hand side: both are
`recCall` of the recursor head at `ls` on the stored `preMajor` and
the constructor application `ctorRef lsC ctorParams ++ fields`. -/
theorem iotaLhsOfS_iotaWitnessSOf (w : IotaWitness E) (fuel : Nat)
    (h : iotaWitnessSB w fuel = true) :
    iotaLhsOfS (iotaWitnessSOf w fuel h) = iotaLhsOf w := rfl

/-- The adapted witness's right-hand side is the legacy `iotaRhsOf`:
the schema instance `instPrefix (preMajor ++ fields)
(instantiateLevels ls schema)` is exactly what `iotaWitnessSB`
decided equal.  Where the equality fails the recognizer refuses —
this is checked agreement, not assumed agreement. -/
theorem iotaRhsOfS_iotaWitnessSOf (w : IotaWitness E) (fuel : Nat)
    (h : iotaWitnessSB w fuel = true) :
    iotaRhsOfS (iotaWitnessSOf w fuel h) = iotaRhsOf w := by
  obtain ⟨_, _, s, hO, _, hrhs⟩ := iotaWitnessSB_iff_parts h
  have hsch : (iotaWitnessSOf w fuel h).schema = s := by
    show (iotaSchemaS w fuel).getD (.bvar 0) = s
    rw [hO, Option.getD_some]
  unfold iotaRhsOfS
  rw [hsch]
  exact hrhs

/-- The argument-level form of the checked RHS equality: `iotaArgs`'s
schema arguments, instantiated at `preMajor ++ fields`, are exactly
`rhsArgs` — the list `foldApps` applies to the minor.  This is the
`iotaArgs`/`rhsArgs` correspondence, derived from the decided
foldApps equality by `appsSpine`-injectivity. -/
theorem iotaArgs_rhsArgs_of_iotaWitnessSB (w : IotaWitness E) (fuel : Nat)
    (h : iotaWitnessSB w fuel = true) :
    ∃ sargs,
      iotaArgs E fuel
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (w.kinds.map shapeOfKind)
          (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
        some sargs ∧
      sargs.map (fun a => instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls a)) =
        rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams := by
  obtain ⟨_, _, s, hO, _, hrhs⟩ := iotaWitnessSB_iff_parts h
  unfold iotaSchemaS iotaOpenRhs at hO
  obtain ⟨sargs, hargs, hfold⟩ := Option.map_eq_some.mp hO
  refine ⟨sargs, hargs, ?_⟩
  rw [← hfold, foldApps_instantiateLevels] at hrhs
  simp only [instantiateLevels] at hrhs
  rw [instPrefix_foldApps] at hrhs
  have hminor : instPrefix (w.preMajor ++ w.fields)
      (.bvar (w.fields.length + w.nindices +
        (w.nMinors - 1 - w.ctorIdx))) = w.minor := by
    apply instPrefix_bvar_lt
    · rw [List.length_append, w.hpre]
      have := w.hidx
      omega
    · have hidx : (w.preMajor ++ w.fields).length - 1 -
          (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)) =
          w.nparams + 1 + w.ctorIdx := by
        rw [List.length_append, w.hpre]
        have := w.hidx
        omega
      rw [hidx]
      rw [List.getElem?_append_left
        (by rw [w.hpre]; have := w.hidx; omega :
          w.nparams + 1 + w.ctorIdx < w.preMajor.length)]
      exact w.hminor
  rw [hminor] at hrhs
  simp only [List.map_map, Function.comp] at hrhs
  unfold iotaRhsOf at hrhs
  have hsp := congrArg appsSpine hrhs
  simp only [appsSpine_foldApps] at hsp
  exact List.append_cancel_left (Prod.ext_iff.mp hsp).2

/-- Soundness of the recognizer for the typed ι equation: under
`iotaWitnessSB`, the adapted witness's typed lhs and rhs are the
legacy redex's lhs and rhs.  Combined with `IotaPreserve`-style
transport this is the B2 correspondence between `Conv.iota` and the
typed rule to come. -/
theorem iotaWitnessSB_sound (w : IotaWitness E) (fuel : Nat)
    (h : iotaWitnessSB w fuel = true) :
    iotaLhsOfS (iotaWitnessSOf w fuel h) = iotaLhsOf w ∧
    iotaRhsOfS (iotaWitnessSOf w fuel h) = iotaRhsOf w :=
  ⟨iotaLhsOfS_iotaWitnessSOf w fuel h, iotaRhsOfS_iotaWitnessSOf w fuel h⟩


/-! ### The redex-level recognizer `iotaRedexB`

`iotaWitnessSB` certifies a REBUILT legacy `IotaWitness`.  The
operational entry point — the computation path step 2c uses — works
on the redex EXPRESSION instead.  `iotaReductShapeCert` reuses
`iotaReductCert` (the stored-type spine analyser of
`RcicParRedSortWall`) to recover the legacy witness from `lhs`, runs
the DIRECT adapter check at `fuel`, and on success returns the full
`IotaWitnessS` together with the proof that its typed lhs is `lhs`.
`iotaRedexB E fuel lhs rhs` is the `Bool` recognizer on top: it
additionally decides that the typed rhs — the schema instantiated at
the redex's `preMajor ++ fields` arguments — is `rhs`.  This is
checked agreement, as in the adapter: `iotaWitnessSB` refuses any
reconstructed witness whose two rhs computations differ, so the
recognizer's verdict never asserts an equality the analysers did not
compute. -/

/-- The typed redex certificate: parse `lhs` as a legacy ι redex
(`iotaReductCert` recovers the `IotaWitness` and proves `iotaLhsOf w =
lhs`), certify it in the DIRECT fragment (`iotaWitnessSB`), and
return the adapted `IotaWitnessS` with its lhs identity.  The
computation path step 2c consumes; `none` when `lhs` is not a
recognized redex or the reconstruction leaves the fragment. -/
def iotaReductShapeCert (E : ResolvedEnv) (fuel : Nat)
    (lhs : Expr Nat) :
    Option (Σ' (w : IotaWitnessS E), iotaLhsOfS w = lhs) :=
  match iotaReductCert E lhs with
  | none => none
  | some ⟨w, hw⟩ =>
      if h : iotaWitnessSB w fuel = true then
        some ⟨iotaWitnessSOf w fuel h,
          (iotaLhsOfS_iotaWitnessSOf w fuel h).trans hw⟩
      else none

/-- The operational recognizer: `iotaRedexB E fuel lhs rhs` matches
`lhs` as a recursor-on-constructor redex, peels the stored types
(`iotaReductCert`), runs `fieldShapesFuel`/`iotaOpenRhs` at `fuel`
inside `iotaWitnessSB`, instantiates the schema at the redex args
(`iotaRhsOfS` of the adapted witness), and compares it to `rhs` with
expression equality — `true` only when a full typed witness with
those sides exists. -/
def iotaRedexB (E : ResolvedEnv) (fuel : Nat)
    (lhs rhs : Expr Nat) : Bool :=
  match iotaReductShapeCert E fuel lhs with
  | none => false
  | some ⟨w, _⟩ => decide (iotaRhsOfS w = rhs)

/-- Soundness of the recognizer: a `true` verdict exhibits a full
`IotaWitnessS` whose typed lhs and rhs are exactly the given
expressions. -/
theorem iotaRedexB_sound {E : ResolvedEnv} {fuel : Nat}
    {lhs rhs : Expr Nat} (h : iotaRedexB E fuel lhs rhs = true) :
    ∃ w : IotaWitnessS E, iotaLhsOfS w = lhs ∧ iotaRhsOfS w = rhs := by
  unfold iotaRedexB at h
  cases hc : iotaReductShapeCert E fuel lhs with
  | none => rw [hc] at h; exact Bool.noConfusion h
  | some p =>
      obtain ⟨w, hw⟩ := p
      rw [hc] at h
      exact ⟨w, hw, of_decide_eq_true h⟩

/-- The certificate's rhs agrees with the legacy reduct of the
reconstructed witness — the `iotaRhsOfS`/`iotaRhsOf` correspondence
at the `Option` level. -/
theorem iotaReductShapeCert_rhs {E : ResolvedEnv} {fuel : Nat}
    {lhs : Expr Nat} {p : Σ' (w : IotaWitnessS E), iotaLhsOfS w = lhs}
    (h : iotaReductShapeCert E fuel lhs = some p) :
    ∃ (w0 : IotaWitness E) (_ : iotaLhsOf w0 = lhs)
      (hB : iotaWitnessSB w0 fuel = true),
      p.1 = iotaWitnessSOf w0 fuel hB ∧ iotaRhsOfS p.1 = iotaRhsOf w0 := by
  unfold iotaReductShapeCert at h
  cases hc : iotaReductCert E lhs with
  | none => rw [hc] at h; exact Option.noConfusion h
  | some pr =>
      rw [hc] at h
      obtain ⟨w0, hw0⟩ := pr
      dsimp only at h
      by_cases hB : iotaWitnessSB w0 fuel = true
      · rw [dif_pos hB] at h
        injection h with hp
        subst hp
        exact ⟨w0, hw0, hB, rfl, iotaRhsOfS_iotaWitnessSOf w0 fuel hB⟩
      · rw [dif_neg hB] at h
        exact Option.noConfusion h

end Rcic.Declarative
