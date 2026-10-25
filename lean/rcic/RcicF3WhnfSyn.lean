import rcic.RcicF3Whnf
import rcic.RcicF3RecValRec
import rcic.RcicIndGroupJudgment
import rcic.RcicIARecIH

/-!
# F3 D-2: δ-hidden recursive fields, syntactically

Admission classifies a constructor field by its weak-head normal form
(`fieldAnalyze`: `piTelescopeFuel`, then `properFamilyFuel`). A field is
δ-hidden when its normal form is the family applied to the parameter
locals and family-free indices while the field itself is not (`Id (F ps idx)`).

- `piTelescopeFuel_lift_nil` (with `whnfFuel_lift` of `RcicIARecIH`): normalization commutes with
  `lift` in an environment of closed members (`EnvClosed`);
- `occursConst_false_of_contains`, `indicesCleanFuel_false`: the fuelled
  occurrence scanners answer `some false` only on family-free terms;
- `fieldAnalyze_rec0`, `fieldAnalyze_nonrec_free`, `properFamilyFuel_shape`:
  what a permitted shape says about the field's normal form;
- `normField`: the field normalized at a bound; `normFields_direct`: under
  admission's shapes, the normalized fields are family-free or literal family
  applications (`RecFieldsDirect`), the class the recursive-group model is
  built for;
- `funIHType_whnf`: the recursor's induction-hypothesis type reads the
  normal form's indices (generalizing `funIHType_recHead`).

Three lemmas restate `RcicIARecIH.transparentBody_lift` / `whnfFuel_lift` /
`properFamilyFuel_true` (that module is outside the F3 chain); they are
cited, not reused. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-! ### `whnfFuel` and `lift` -/

/-- A telescope-free normal form lifts with the term. -/
theorem piTelescopeFuel_lift_nil (E : ResolvedEnv) (hcl : EnvClosed E) (c a : Nat) :
    (fuel : Nat) → {e w : Expr Nat} → piTelescopeFuel E fuel e = some ([], w) →
      piTelescopeFuel E fuel (Rcic.Declarative.lift c a e) = some ([], Rcic.Declarative.lift c a w)
  | 0, _, _, h => by simp only [piTelescopeFuel] at h; cases h
  | fuel + 1, e, w, h => by
      simp only [piTelescopeFuel] at h ⊢
      rw [Rcic.Declarative.whnfFuel_lift E hcl c a fuel e]
      cases hw : whnfFuel E fuel e with
      | none => rw [hw] at h; cases h
      | some v =>
          rw [hw] at h
          simp only [Option.map_some']
          cases v with
          | pi A B =>
              cases hp : piTelescopeFuel E fuel B with
              | none => simp only [hp] at h; cases h
              | some p =>
                  obtain ⟨ds, b⟩ := p
                  simp only [hp] at h
                  exact absurd (Prod.mk.inj (Option.some.inj h)).1 (List.cons_ne_nil _ _)
          | bvar i =>
              have hv : w = .bvar i := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv
              by_cases hci : c ≤ i
              · simp only [Rcic.Declarative.lift, if_pos hci]
              · simp only [Rcic.Declarative.lift, if_neg hci]
          | sort l =>
              have hv : w = .sort l := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl
          | const r ls =>
              have hv : w = .const r ls := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl
          | app f x =>
              have hv : w = .app f x := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl
          | lam A b =>
              have hv : w = .lam A b := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl
          | letE A v b =>
              have hv : w = .letE A v b := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl
          | lit t =>
              have hv : w = .lit t := (Prod.mk.inj (Option.some.inj h)).2.symm
              subst hv; rfl

/-! ### the fuelled occurrence scanners -/

/-- `containsFamilyFuel` answers `some false` only on family-free terms. -/
theorem occursConst_false_of_contains {E : ResolvedEnv} {fam : Nat} :
    (fuel : Nat) → (e : Expr Nat) → containsFamilyFuel E fam fuel e = some false → occursConst fam e = false
  | 0, _, h => by simp only [containsFamilyFuel] at h; cases h
  | _ + 1, .bvar _, _ => rfl
  | _ + 1, .sort _, _ => rfl
  | fuel + 1, .lit 0, h => by
      have h1 := occursConst_false_of_contains fuel litZero h
      have h1' : ¬ (1 = fam) := fun e => by
        have : occursConst fam litZero = true := by
          show decide (1 = fam) = true
          exact decide_eq_true e
        rw [h1] at this; cases this
      show litOccurs fam 0 = false
      simp only [litOccurs]
      exact decide_eq_false (fun e => h1' e.symm)
  | fuel + 1, .lit (t + 1), h => by
      simp only [containsFamilyFuel] at h
      cases hc : containsFamilyFuel E fam fuel (.const 2 []) with
      | none => rw [hc] at h; cases h
      | some b =>
          cases b with
          | true => rw [hc] at h; cases h
          | false =>
              rw [hc] at h
              have h2 := occursConst_false_of_contains fuel (.const 2 []) hc
              have h1 := occursConst_false_of_contains fuel litZero h
              have h2' : ¬ (fam = 2) := fun e => by
                have : occursConst fam (.const 2 []) = true := by
                  show decide (2 = fam) = true
                  exact decide_eq_true e.symm
                rw [h2] at this; cases this
              have h1' : ¬ (fam = 1) := fun e => by
                have : occursConst fam litZero = true := by
                  show decide (1 = fam) = true
                  exact decide_eq_true e.symm
                rw [h1] at this; cases this
              show litOccurs fam (t + 1) = false
              simp only [litOccurs, decide_eq_false h1', decide_eq_false h2', Bool.or_self]
  | fuel + 1, .const r ls, h => by
      simp only [containsFamilyFuel] at h
      by_cases hr : r = fam
      · rw [if_pos hr] at h; cases h
      · show decide (r = fam) = false
        exact decide_eq_false hr
  | fuel + 1, .app f x, h => by
      simp only [containsFamilyFuel] at h
      cases hf : containsFamilyFuel E fam fuel f with
      | none => rw [hf] at h; cases h
      | some b =>
          cases b with
          | true => rw [hf] at h; cases h
          | false =>
              rw [hf] at h
              show (occursConst fam f || occursConst fam x) = false
              rw [occursConst_false_of_contains fuel f hf, occursConst_false_of_contains fuel x h]
              rfl
  | fuel + 1, .lam A b, h => by
      simp only [containsFamilyFuel] at h
      cases hA : containsFamilyFuel E fam fuel A with
      | none => rw [hA] at h; cases h
      | some c =>
          cases c with
          | true => rw [hA] at h; cases h
          | false =>
              rw [hA] at h
              show (occursConst fam A || occursConst fam b) = false
              rw [occursConst_false_of_contains fuel A hA, occursConst_false_of_contains fuel b h]
              rfl
  | fuel + 1, .pi A B, h => by
      simp only [containsFamilyFuel] at h
      cases hA : containsFamilyFuel E fam fuel A with
      | none => rw [hA] at h; cases h
      | some c =>
          cases c with
          | true => rw [hA] at h; cases h
          | false =>
              rw [hA] at h
              show (occursConst fam A || occursConst fam B) = false
              rw [occursConst_false_of_contains fuel A hA, occursConst_false_of_contains fuel B h]
              rfl
  | fuel + 1, .letE A v b, h => by
      simp only [containsFamilyFuel] at h
      cases hA : containsFamilyFuel E fam fuel A with
      | none => rw [hA] at h; cases h
      | some c =>
          cases c with
          | true => rw [hA] at h; cases h
          | false =>
              rw [hA] at h
              cases hv : containsFamilyFuel E fam fuel v with
              | none => rw [hv] at h; cases h
              | some c' =>
                  cases c' with
                  | true => rw [hv] at h; cases h
                  | false =>
                      rw [hv] at h
                      show (occursConst fam A || occursConst fam v || occursConst fam b) = false
                      rw [occursConst_false_of_contains fuel A hA, occursConst_false_of_contains fuel v hv,
                        occursConst_false_of_contains fuel b h]
                      rfl

/-- Clean indices are family-free. -/
theorem indicesCleanFuel_false {E : ResolvedEnv} {fam : Nat} : (fuel : Nat) → (es : List (Expr Nat)) →
    indicesCleanFuel E fam fuel es = some false → ∀ e, e ∈ es → occursConst fam e = false
  | _, [], _, _, h => absurd h (List.not_mem_nil _)
  | 0, _ :: _, h, _, _ => by simp only [indicesCleanFuel] at h; cases h
  | fuel + 1, A :: As, h, e, he => by
      simp only [indicesCleanFuel] at h
      cases hc : containsFamilyFuel E fam fuel A with
      | none => rw [hc] at h; cases h
      | some b =>
          cases b with
          | true => rw [hc] at h; cases h
          | false =>
              rw [hc] at h
              rcases List.mem_cons.mp he with rfl | he
              · exact occursConst_false_of_contains fuel e hc
              · exact indicesCleanFuel_false fuel As h e he

/-! ### exact parameter locals -/



/-- The parameter locals at the depth `fieldAnalyze` passes are those at the field's position. -/
theorem paramLocals_top (np d : Nat) :
    policyParameterLocals np (np + d - 1 + 1 - np) = policyParameterLocals np d := by
  by_cases hnp : np = 0
  · subst hnp
    simp [policyParameterLocals]
  · congr 1
    omega

/-- A proper family application: the family at the canonical levels, applied to
the parameter locals and family-free indices (as `RcicIARecIH.properFamilyFuel_true`,
with the indices' family-freeness). -/
theorem properFamilyFuel_shape {E : ResolvedEnv} {fuel fam nuniv nparams nindices top : Nat} {body : Expr Nat}
    (hnpt : nparams ≤ top + 1) (h : properFamilyFuel E fuel fam nuniv nparams nindices top body = some true) :
    ∃ idx : List (Expr Nat), body = foldApps (.const fam ((List.range nuniv).map Level.param))
      (policyParameterLocals nparams (top + 1 - nparams) ++ idx) ∧
      idx.length = nindices ∧ ∀ e, e ∈ idx → occursConst fam e = false := by
  have he := foldApps_appsSpine body
  simp only [properFamilyFuel] at h
  generalize hsp : appsSpine body = sp at h he
  obtain ⟨hd, args⟩ := sp
  cases hd with
  | const r ls =>
      simp only at h he
      split at h
      · rename_i hcond
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨hrf, harglen⟩, hexact⟩, hls⟩ := hcond
        revert h
        cases hc : indicesCleanFuel E fam fuel (args.drop nparams) with
        | none => intro h; exact Option.noConfusion h
        | some b =>
            cases b <;> intro h
            · have hlen : args.length = nparams + nindices := of_decide_eq_true harglen
              have htake : (args.take nparams).length = nparams := by
                rw [List.length_take, hlen]
                exact Nat.min_eq_left (Nat.le_add_right _ _)
              have hp := Rcic.Declarative.exactParamLocals_eq_PL (args.take nparams) top (by rw [htake]; exact hnpt) hexact
              rw [htake] at hp
              refine ⟨args.drop nparams, ?_, ?_, indicesCleanFuel_false fuel _ hc⟩
              · rw [← he, hrf, of_decide_eq_true hls, ← hp, List.take_append_drop]
              · rw [List.length_drop, hlen]
                omega
            · exact absurd h (by decide)
      · exact absurd h (by decide)
  | bvar _ => simp only at h; exact absurd h (by decide)
  | sort _ => simp only at h; exact absurd h (by decide)
  | app _ _ => simp only at h; exact absurd h (by decide)
  | lam _ _ => simp only at h; exact absurd h (by decide)
  | pi _ _ => simp only at h; exact absurd h (by decide)
  | letE _ _ _ => simp only at h; exact absurd h (by decide)
  | lit _ => simp only at h; exact absurd h (by decide)

/-! ### what a permitted shape says -/

/-- A directly recursive shape: the field normalizes to a proper family
application at its depth, and the shape's indices are its indices. -/
theorem fieldAnalyze_rec0 {E : ResolvedEnv} {fuel fam nuniv np ni depth : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)} (h : fieldAnalyze E fuel fam nuniv np ni depth T = .permitted (.recursive 0) idx) :
    ∃ body, whnfFuel E fuel T = some body ∧ piTelescopeFuel E fuel T = some ([], body) ∧ idx = familyIdx np body ∧
      ∃ fu, properFamilyFuel E fu fam nuniv np ni (depth - 1) body = some true := by
  cases fuel with
  | zero => simp only [fieldAnalyze] at h; cases h
  | succ fuel =>
      simp only [fieldAnalyze] at h
      cases hp : piTelescopeFuel E fuel T with
      | none => simp only [hp] at h; cases h
      | some p =>
          obtain ⟨doms, body⟩ := p
          simp only [hp] at h
          cases hd : domainsContainFuel E fam fuel doms with
          | none => simp only [hd] at h; cases h
          | some b =>
              cases b with
              | true => simp only [hd] at h; cases h
              | false =>
                  simp only [hd] at h
                  cases hpf : properFamilyFuel E fuel fam nuniv np ni (doms.length + depth - 1) body with
                  | none => simp only [hpf] at h; cases h
                  | some b =>
                      cases b with
                      | true =>
                          simp only [hpf] at h
                          have h' := FieldAnalyze.permitted.inj h
                          have hl : doms.length = 0 := FieldShape.recursive.inj h'.1
                          have hdoms : doms = [] := List.eq_nil_of_length_eq_zero hl
                          subst hdoms
                          simp only [List.length_nil, Nat.zero_add] at hpf
                          refine ⟨body, ?_, piTelescopeFuel_mono E (Nat.le_succ _) hp, h'.2.symm, fuel, hpf⟩
                          cases fuel with
                          | zero => simp only [piTelescopeFuel] at hp; cases hp
                          | succ fuel =>
                              simp only [piTelescopeFuel] at hp
                              cases hw : whnfFuel E fuel T with
                              | none => rw [hw] at hp; cases hp
                              | some w =>
                                  rw [hw] at hp
                                  have hwb : w = body := by
                                    cases w with
                                    | pi A B =>
                                        cases hq : piTelescopeFuel E fuel B with
                                        | none => simp only [hq] at hp; cases hp
                                        | some q =>
                                            obtain ⟨ds, b⟩ := q
                                            simp only [hq] at hp
                                            exact absurd (Prod.mk.inj (Option.some.inj hp)).1 (List.cons_ne_nil _ _)
                                    | bvar _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | sort _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | const _ _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | app _ _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | lam _ _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | letE _ _ _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                    | lit _ => exact (Prod.mk.inj (Option.some.inj hp)).2
                                  subst hwb
                                  exact whnfFuel_mono E (by omega) hw
                      | false =>
                          simp only [hpf] at h
                          cases hc : containsFamilyFuel E fam fuel T with
                          | none => simp only [hc] at h; cases h
                          | some b =>
                              cases b with
                              | false =>
                                  simp only [hc] at h
                                  have h' := FieldAnalyze.permitted.inj h
                                  cases h'.1
                              | true =>
                                  simp only [hc] at h
                                  exact (fieldAnalyze_tail_not_permitted h).elim

/-- A non-recursive shape: the field is family-free. -/
theorem fieldAnalyze_nonrec_free {E : ResolvedEnv} {fuel fam nuniv np ni depth : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)} (h : fieldAnalyze E fuel fam nuniv np ni depth T = .permitted .nonrecursive idx) :
    occursConst fam T = false := by
  cases fuel with
  | zero => simp only [fieldAnalyze] at h; cases h
  | succ fuel =>
      simp only [fieldAnalyze] at h
      cases hp : piTelescopeFuel E fuel T with
      | none => simp only [hp] at h; cases h
      | some p =>
          obtain ⟨doms, body⟩ := p
          simp only [hp] at h
          cases hd : domainsContainFuel E fam fuel doms with
          | none => simp only [hd] at h; cases h
          | some b =>
              cases b with
              | true => simp only [hd] at h; cases h
              | false =>
                  simp only [hd] at h
                  cases hpf : properFamilyFuel E fuel fam nuniv np ni (doms.length + depth - 1) body with
                  | none => simp only [hpf] at h; cases h
                  | some b =>
                      cases b with
                      | true =>
                          simp only [hpf] at h
                          have h' := FieldAnalyze.permitted.inj h
                          cases h'.1
                      | false =>
                          simp only [hpf] at h
                          cases hc : containsFamilyFuel E fam fuel T with
                          | none => simp only [hc] at h; cases h
                          | some b =>
                              cases b with
                              | false => exact occursConst_false_of_contains fuel T hc
                              | true =>
                                  simp only [hc] at h
                                  exact (fieldAnalyze_tail_not_permitted h).elim

/-! ### normalized fields -/

/-- A field normalized at the bound `fuel`, for the family `f`: a field that
mentions the family is replaced by its weak-head normal form (when it has one
at the bound); a family-free field is left as it is. -/
def normField (E : ResolvedEnv) (fuel f : Nat) (A : Expr Nat) : Expr Nat :=
  if occursConst f A = true then (whnfFuel E fuel A).getD A else A

theorem normField_of_whnf {E : ResolvedEnv} {fuel f : Nat} {A w : Expr Nat} (hocc : occursConst f A = true)
    (h : whnfFuel E fuel A = some w) : normField E fuel f A = w := by
  unfold normField
  rw [if_pos hocc, h]
  rfl

theorem normField_free {E : ResolvedEnv} {fuel f : Nat} {A : Expr Nat} (h : occursConst f A = false) :
    normField E fuel f A = A := by
  unfold normField
  rw [h]
  rfl

/-- A field whose normal form has the family at its head mentions the family. -/
theorem occursConst_of_whnf_head {E : ResolvedEnv} {f : Nat} (hFF : FamFreeBodies E f) {fuel : Nat} {A : Expr Nat}
    {ls : List Level} {args : List (Expr Nat)} (hw : whnfFuel E fuel A = some (foldApps (.const f ls) args)) :
    occursConst f A = true := by
  cases hA : occursConst f A with
  | true => rfl
  | false =>
      have := whnfFuel_famFree hFF fuel A hA hw
      rw [occursConst_foldApps] at this
      simp only [occursConst, decide_True, Bool.true_or] at this
      cases this

/-- A field is its own normal form or has one: the shape `telAgree_of_typings` reads. -/
theorem normField_cases (E : ResolvedEnv) (fuel f : Nat) (A : Expr Nat) :
    normField E fuel f A = A ∨ ∃ fu, whnfFuel E fu A = some (normField E fuel f A) := by
  unfold normField
  cases occursConst f A with
  | false => exact Or.inl rfl
  | true =>
      cases hw : whnfFuel E fuel A with
      | none => exact Or.inl rfl
      | some w => exact Or.inr ⟨fuel, by rw [hw]; rfl⟩

/-- **Under admission's shapes, the normalized fields are family-free or literal
family applications** at the parameter locals and family-free indices. -/
theorem normFields_direct {E : ResolvedEnv} {f nu np nq fuel : Nat} (hFF : FamFreeBodies E f) :
    (Fs : List (Expr Nat)) → (d : Nat) → (shapes : List FieldShape) →
    fieldShapesFuel E fuel f nu np nq (np + d) Fs = some shapes →
    (∀ s, s ∈ shapes → s = .nonrecursive ∨ s = .recursive 0) →
    RecFieldsDirect f ((List.range nu).map Level.param) np nq (Fs.map (normField E fuel f)) d
  | [], _, _, _, _ => trivial
  | A :: Fs, d, shapes, hs, hsh => by
      unfold fieldShapesFuel at hs
      cases ha : fieldAnalyze E fuel f nu np nq (np + d) A with
      | permitted s idx =>
          rw [ha] at hs
          cases hr : fieldShapesFuel E fuel f nu np nq (np + d + 1) Fs with
          | none => rw [hr] at hs; cases hs
          | some rest =>
              rw [hr] at hs
              have e : shapes = s :: rest := (Option.some.inj hs).symm
              subst e
              have ih := normFields_direct hFF Fs (d + 1) rest
                (by rw [show np + (d + 1) = np + d + 1 by omega]; exact hr)
                (fun s' hs' => hsh s' (List.mem_cons_of_mem _ hs'))
              refine ⟨?_, ih⟩
              rcases hsh s (List.mem_cons_self _ _) with rfl | rfl
              · have h0 := fieldAnalyze_nonrec_free ha
                left
                show occursConst f (normField E fuel f A) = false
                rw [normField_free h0]
                exact h0
              · obtain ⟨body, hw, _, _, fu, hpf⟩ := fieldAnalyze_rec0 ha
                obtain ⟨idx', hb, hl, hidx⟩ := properFamilyFuel_shape (by omega) hpf
                refine Or.inr ⟨idx', ?_, hl, hidx⟩
                have hocc : occursConst f A = true := by
                  rw [hb] at hw
                  exact occursConst_of_whnf_head hFF hw
                show normField E fuel f A = _
                rw [normField_of_whnf hocc hw, hb, paramLocals_top]
      | unresolved => rw [ha] at hs; cases hs
      | refused _ => rw [ha] at hs; cases hs

/-- The normalized fields have the family exactly where the fields do, under
admission's shapes. -/
theorem occursConst_normField_of_shapes {E : ResolvedEnv} {f nu np nq fuel : Nat} (hFF : FamFreeBodies E f) :
    (Fs : List (Expr Nat)) → (depth : Nat) → (shapes : List FieldShape) →
    fieldShapesFuel E fuel f nu np nq depth Fs = some shapes →
    (∀ s, s ∈ shapes → s = .nonrecursive ∨ s = .recursive 0) →
    ∀ A, A ∈ Fs → occursConst f (normField E fuel f A) = occursConst f A
  | [], _, _, _, _, _, hA => absurd hA (List.not_mem_nil _)
  | A :: Fs, depth, shapes, hs, hsh, B, hB => by
      unfold fieldShapesFuel at hs
      cases ha : fieldAnalyze E fuel f nu np nq depth A with
      | permitted s idx =>
          rw [ha] at hs
          cases hr : fieldShapesFuel E fuel f nu np nq (depth + 1) Fs with
          | none => rw [hr] at hs; cases hs
          | some rest =>
              rw [hr] at hs
              have e : shapes = s :: rest := (Option.some.inj hs).symm
              subst e
              rcases List.mem_cons.mp hB with rfl | hB
              · rcases hsh s (List.mem_cons_self _ _) with rfl | rfl
                · rw [normField_free (fieldAnalyze_nonrec_free ha)]
                · obtain ⟨body, hw, _, _, fu, hpf⟩ := fieldAnalyze_rec0 ha
                  obtain ⟨ls, args, hsp⟩ := properFamilyFuel_true_head hpf
                  have hb : body = foldApps (.const f ls) args := by rw [← foldApps_appsSpine body, hsp]
                  have hocc : occursConst f B = true := by
                    rw [hb] at hw
                    exact occursConst_of_whnf_head hFF hw
                  rw [normField_of_whnf hocc hw, occursConst_true_of_head hsp, hocc]
              · exact occursConst_normField_of_shapes hFF Fs (depth + 1) rest hr
                  (fun s' hs' => hsh s' (List.mem_cons_of_mem _ hs')) B hB
      | unresolved => rw [ha] at hs; cases hs
      | refused _ => rw [ha] at hs; cases hs

/-! ### the induction-hypothesis type of a hidden field -/

/-- The recursor's induction-hypothesis type reads the field's normal form:
the motive at the normal form's indices and the field (generalizing
`funIHType_recHead`, where the normal form is the field itself). -/
theorem funIHType_whnf {E : ResolvedEnv} (hcl : EnvClosed E) {fuel np : Nat} {A A' M : Expr Nat}
    (hA : piTelescopeFuel E fuel A = some ([], A')) :
    funIHType E fuel np A M 0 = some (foldApps (Rcic.Declarative.lift 0 1 M)
      ((familyIdx np A').map (Rcic.Declarative.lift 0 1) ++ [.bvar 0])) := by
  unfold funIHType
  rw [piTelescopeFuel_lift_nil E hcl 0 1 fuel hA]
  simp only [List.length_nil, lift_zero_idx, policyPi, familyIdx_lift, List.range_zero, List.reverse_nil,
    List.map_nil, foldApps]
  rfl

/-- A normal form with the family at its head has no telescope. -/
theorem piTelescopeFuel_of_whnf_famHead {E : ResolvedEnv} {fam : Nat} {fuel : Nat} {A : Expr Nat}
    {ls : List Level} {args : List (Expr Nat)}
    (hw : whnfFuel E fuel A = some (foldApps (.const fam ls) args)) :
    piTelescopeFuel E (fuel + 1) A = some ([], foldApps (.const fam ls) args) := by
  simp only [piTelescopeFuel]
  rw [hw]
  generalize hfa : foldApps (.const fam ls) args = fa
  have hnp : ∀ A' B', fa ≠ .pi A' B' := by
    rw [← hfa]; exact foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _
  cases fa with
  | pi A' B' => exact absurd rfl (hnp A' B')
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ => rfl
  | lam _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

end PSet

end Rcic.F3
