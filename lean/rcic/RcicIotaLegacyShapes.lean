import rcic.RcicIotaShapeAdapter

/-!
# DT-019 S2 (c) — admission's field shapes are the legacy kinds

On a constructor whose field domains admission classified
(`fieldShapesFuel … = some shapes`) and the legacy analysis also classified
(`analyzeFields fam … = some kinds`), the two agree: `shapes = kinds.map shapeOfKind`,
provided no transparent body of the environment mentions the family
(`FamFreeBodies`, supplied at an admitted recursor by `RcicIotaLegacyFamFree`).

* legacy `.plain` (no syntactic occurrence of the family): the typed analysis
  unfolds only fam-free bodies, so its telescope body is fam-free and cannot be
  the proper family application `.recursive` needs; admission's `.permitted`
  verdict is then `.nonrecursive`.
* legacy `.directRec` (a literal family application): `whnfFuel` is stuck at
  the family head (no body), the telescope is empty, and admission's
  `.permitted` verdict is `.recursive 0`; the `containsFamilyFuel` arm cannot
  answer `some false` at a family-headed term.

No DIRECT-fragment premise (`noTransparentB` and friends): fields like
`Id Nat` through a transparent `Id` are covered.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-- no transparent body of `E` mentions `fam`. -/
def FamFreeBodies (E : ResolvedEnv) (fam : Nat) : Prop :=
  ∀ r ls b, transparentBody E r ls = some b → occursConst fam b = false

/-! ## (1) occurrence under lift / instantiate -/

theorem occursConst_lift {r : Nat} (c a : Nat) :
    (e : Expr Nat) → occursConst r (lift c a e) = occursConst r e
  | .bvar i => by
      simp only [lift]
      split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [lift, occursConst, occursConst_lift c a f, occursConst_lift c a x]
  | .lam A b => by
      simp only [lift, occursConst, occursConst_lift c a A, occursConst_lift (c + 1) a b]
  | .pi A b => by
      simp only [lift, occursConst, occursConst_lift c a A, occursConst_lift (c + 1) a b]
  | .letE A v b => by
      simp only [lift, occursConst, occursConst_lift c a A, occursConst_lift c a v,
        occursConst_lift (c + 1) a b]
  | .lit _ => rfl

theorem occursConst_instantiate_false {r : Nat} :
    (j : Nat) → (v : Expr Nat) → occursConst r v = false →
    (e : Expr Nat) → occursConst r e = false → occursConst r (instantiate j v e) = false
  | j, v, hv, .bvar i, _ => by
      simp only [instantiate]
      split
      · exact hv
      · split <;> rfl
  | _, _, _, .sort _, _ => rfl
  | _, _, _, .const _ _, h => h
  | j, v, hv, .app f x, h => by
      simp only [occursConst, Bool.or_eq_false_iff] at h
      simp only [instantiate, occursConst, Bool.or_eq_false_iff]
      exact ⟨occursConst_instantiate_false j v hv f h.1, occursConst_instantiate_false j v hv x h.2⟩
  | j, v, hv, .lam A b, h => by
      simp only [occursConst, Bool.or_eq_false_iff] at h
      simp only [instantiate, occursConst, Bool.or_eq_false_iff]
      exact ⟨occursConst_instantiate_false j v hv A h.1,
        occursConst_instantiate_false (j + 1) (lift 0 1 v) (by rw [occursConst_lift]; exact hv) b h.2⟩
  | j, v, hv, .pi A b, h => by
      simp only [occursConst, Bool.or_eq_false_iff] at h
      simp only [instantiate, occursConst, Bool.or_eq_false_iff]
      exact ⟨occursConst_instantiate_false j v hv A h.1,
        occursConst_instantiate_false (j + 1) (lift 0 1 v) (by rw [occursConst_lift]; exact hv) b h.2⟩
  | j, v, hv, .letE A w b, h => by
      simp only [occursConst, Bool.or_eq_false_iff] at h
      simp only [instantiate, occursConst, Bool.or_eq_false_iff]
      exact ⟨⟨occursConst_instantiate_false j v hv A h.1.1,
        occursConst_instantiate_false j v hv w h.1.2⟩,
        occursConst_instantiate_false (j + 1) (lift 0 1 v) (by rw [occursConst_lift]; exact hv) b h.2⟩
  | _, _, _, .lit _, h => h

theorem occursConst_foldApps_false {r : Nat} {f : Expr Nat} {args : List (Expr Nat)}
    (hf : occursConst r f = false) (hargs : ∀ a ∈ args, occursConst r a = false) :
    occursConst r (foldApps f args) = false := by
  rw [occursConst_foldApps, hf, Bool.false_or]
  simp only [List.any_eq_false, Bool.not_eq_true]
  exact hargs

theorem occursConst_spine_false {r : Nat} {e : Expr Nat} (h : occursConst r e = false) :
    occursConst r (appsSpine e).1 = false ∧ ∀ a ∈ (appsSpine e).2, occursConst r a = false := by
  rw [← foldApps_appsSpine e, occursConst_foldApps, Bool.or_eq_false_iff] at h
  simp only [List.any_eq_false, Bool.not_eq_true] at h
  exact h

/-! ## (2) whnf keeps the family out -/

theorem whnfFuel_famFree {E : ResolvedEnv} {fam : Nat} (hE : FamFreeBodies E fam) :
    (fuel : Nat) → (e : Expr Nat) → occursConst fam e = false →
    {w : Expr Nat} → whnfFuel E fuel e = some w → occursConst fam w = false
  | 0, _, _, _, h => by cases h
  | fuel + 1, e, he, w, h => by
      obtain ⟨hhd, hargs⟩ := occursConst_spine_false he
      cases hs : appsSpine e with
      | mk hd args =>
          rw [hs] at hhd hargs
          simp only at hhd hargs
          cases hd with
          | lam A b =>
              cases args with
              | nil =>
                  simp only [whnfFuel, hs] at h
                  cases h
                  exact he
              | cons a args =>
                  simp only [whnfFuel, hs] at h
                  simp only [occursConst, Bool.or_eq_false_iff] at hhd
                  exact whnfFuel_famFree hE fuel _
                    (occursConst_foldApps_false
                      (occursConst_instantiate_false 0 a (hargs a (List.mem_cons_self _ _)) b hhd.2)
                      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))) h
          | letE A v b =>
              simp only [whnfFuel, hs] at h
              simp only [occursConst, Bool.or_eq_false_iff] at hhd
              exact whnfFuel_famFree hE fuel _
                (occursConst_foldApps_false
                  (occursConst_instantiate_false 0 v hhd.1.2 b hhd.2) hargs) h
          | const r ls =>
              cases ht : transparentBody E r ls with
              | none =>
                  simp only [whnfFuel, hs, ht] at h
                  cases h
                  exact he
              | some body =>
                  simp only [whnfFuel, hs, ht] at h
                  exact whnfFuel_famFree hE fuel _
                    (occursConst_foldApps_false (hE r ls body ht) hargs) h
          | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact he
          | sort _ => simp only [whnfFuel, hs] at h; cases h; exact he
          | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact he
          | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact he
          | lit _ => simp only [whnfFuel, hs] at h; cases h; exact he

theorem piTelescopeFuel_famFree {E : ResolvedEnv} {fam : Nat} (hE : FamFreeBodies E fam) :
    (fuel : Nat) → (T : Expr Nat) → occursConst fam T = false →
    {doms : List (Expr Nat)} → {body : Expr Nat} →
    piTelescopeFuel E fuel T = some (doms, body) → occursConst fam body = false
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, T, hT, doms, body, h => by
      simp only [piTelescopeFuel] at h
      cases hw : whnfFuel E fuel T with
      | none => rw [hw] at h; cases h
      | some w =>
          rw [hw] at h
          have hwf := whnfFuel_famFree hE fuel T hT hw
          cases w with
          | pi A B =>
              cases hp : piTelescopeFuel E fuel B with
              | none => simp only [hp] at h <;> cases h
              | some p =>
                  obtain ⟨ds, b⟩ := p
                  simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.2]
                  simp only [occursConst, Bool.or_eq_false_iff] at hwf
                  exact piTelescopeFuel_famFree hE fuel B hwf.2 hp
          | bvar _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | sort _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | const _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | app _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | lam _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | letE _ _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf
          | lit _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact hwf

/-! ## (3) the proper family application is family-headed -/

theorem properFamilyFuel_true_head {E : ResolvedEnv} {fuel fam nuniv np ni top : Nat}
    {body : Expr Nat}
    (h : properFamilyFuel E fuel fam nuniv np ni top body = some true) :
    ∃ ls args, appsSpine body = (.const fam ls, args) := by
  unfold properFamilyFuel at h
  revert h
  cases hs : appsSpine body with
  | mk hd args =>
      intro h
      cases hd with
      | const r ls =>
          simp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            exact ⟨ls, args, by rw [hc.1.1.1]⟩
          · cases h
      | bvar _ => cases h
      | sort _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
      | letE _ _ _ => cases h
      | lit _ => cases h

theorem occursConst_true_of_head {fam : Nat} {e : Expr Nat} {ls : List Level}
    {args : List (Expr Nat)} (h : appsSpine e = (.const fam ls, args)) :
    occursConst fam e = true := by
  rw [← foldApps_appsSpine e, h, occursConst_foldApps]
  simp only [occursConst, decide_True, Bool.true_or]

/-! ## (4) stuck at the family head -/

theorem whnfFuel_famHead {E : ResolvedEnv} {fam : Nat} {ls : List Level} {args : List (Expr Nat)}
    {T : Expr Nat} (hs : appsSpine T = (.const fam ls, args))
    (hfam : transparentBody E fam ls = none) (fuel : Nat) :
    whnfFuel E (fuel + 1) T = some T := by
  simp only [whnfFuel]
  rw [hs]
  simp only
  rw [hfam]

theorem piTelescopeFuel_famHead {E : ResolvedEnv} {fam : Nat} {ls : List Level}
    {args : List (Expr Nat)} {T : Expr Nat} (hs : appsSpine T = (.const fam ls, args))
    (hfam : transparentBody E fam ls = none) (fuel : Nat) :
    piTelescopeFuel E (fuel + 2) T = some ([], T) := by
  simp only [piTelescopeFuel]
  rw [whnfFuel_famHead hs hfam fuel]
  cases T with
  | pi A B => simp only [appsSpine] at hs; cases hs
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ => rfl
  | lam _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

theorem containsFamilyFuel_famHead {E : ResolvedEnv} {fam : Nat} :
    (fuel : Nat) → (T : Expr Nat) → {ls : List Level} → {args : List (Expr Nat)} →
    appsSpine T = (.const fam ls, args) → containsFamilyFuel E fam fuel T ≠ some false
  | 0, T, _, _, _ => by
      cases T <;> simp [containsFamilyFuel]
  | fuel + 1, .app f x, ls, args, hs => by
      simp only [appsSpine, Prod.mk.injEq] at hs
      simp only [containsFamilyFuel]
      cases hc : containsFamilyFuel E fam fuel f with
      | none => simp
      | some b =>
          cases b with
          | true => simp
          | false =>
              exact absurd hc (containsFamilyFuel_famHead fuel f (ls := ls)
                (args := (appsSpine f).2) (by rw [← hs.1]))
  | fuel + 1, .const r ls', ls, args, hs => by
      simp only [appsSpine, Prod.mk.injEq, Expr.const.injEq] at hs
      simp only [containsFamilyFuel]
      rw [if_pos hs.1.1]
      simp
  | _ + 1, .bvar _, _, _, hs => by simp only [appsSpine] at hs; cases hs
  | _ + 1, .sort _, _, _, hs => by simp only [appsSpine] at hs; cases hs
  | _ + 1, .lam _ _, _, _, hs => by simp only [appsSpine] at hs; cases hs
  | _ + 1, .pi _ _, _, _, hs => by simp only [appsSpine] at hs; cases hs
  | _ + 1, .letE _ _ _, _, _, hs => by simp only [appsSpine] at hs; cases hs
  | _ + 1, .lit _, _, _, hs => by simp only [appsSpine] at hs; cases hs

/-! ## (5) the per-field agreement -/

/-- the `containsFamilyFuel = some true` tail of `fieldAnalyze` never permits. -/
theorem fieldAnalyze_tail_not_permitted {E : ResolvedEnv} {fam fuel : Nat} {body : Expr Nat}
    {shape : FieldShape} {idx : List (Expr Nat)}
    (h : (match appsSpine body with
      | (.const r _, args) =>
          if r = fam then FieldAnalyze.refused .invalidPositiveOccurrence
          else
            match domainsContainFuel E fam fuel args with
            | none => FieldAnalyze.unresolved
            | some true => FieldAnalyze.refused .nestedInductiveOutOfProfile
            | some false => FieldAnalyze.refused .invalidPositiveOccurrence
      | _ => FieldAnalyze.refused .invalidPositiveOccurrence) = .permitted shape idx) : False := by
  revert h
  cases hs : appsSpine body with
  | mk hd args =>
      intro h
      cases hd with
      | const r _ =>
          simp only at h
          split at h
          · cases h
          · cases hd : domainsContainFuel E fam fuel args with
            | none => simp only [hd] at h <;> cases h
            | some b => cases b <;> simp only [hd] at h <;> cases h
      | bvar _ => cases h
      | sort _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
      | letE _ _ _ => cases h
      | lit _ => cases h

/-- a syntactically family-free field domain, if permitted, is `.nonrecursive`. -/
theorem fieldAnalyze_plain {E : ResolvedEnv} {fam : Nat} (hE : FamFreeBodies E fam)
    {fuel nuniv np ni depth : Nat} {T : Expr Nat} (hT : occursConst fam T = false)
    {shape : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv np ni depth T = .permitted shape idx) :
    shape = .nonrecursive := by
  cases fuel with
  | zero => simp only [fieldAnalyze] at h <;> cases h
  | succ fuel =>
      simp only [fieldAnalyze] at h
      cases hp : piTelescopeFuel E fuel T with
      | none => simp only [hp] at h <;> cases h
      | some p =>
          obtain ⟨doms, body⟩ := p
          simp only [hp] at h
          cases hd : domainsContainFuel E fam fuel doms with
          | none => simp only [hd] at h <;> cases h
          | some b =>
              cases b with
              | true => simp only [hd] at h <;> cases h
              | false =>
                  simp only [hd] at h
                  cases hpf : properFamilyFuel E fuel fam nuniv np ni (doms.length + depth - 1) body with
                  | none => simp only [hpf] at h <;> cases h
                  | some b =>
                      cases b with
                      | true =>
                          exfalso
                          obtain ⟨ls, args, hsp⟩ := properFamilyFuel_true_head hpf
                          have hb := piTelescopeFuel_famFree hE _ _ hT hp
                          rw [occursConst_true_of_head hsp] at hb
                          cases hb
                      | false =>
                          simp only [hpf] at h
                          cases hc : containsFamilyFuel E fam fuel T with
                          | none => simp only [hc] at h <;> cases h
                          | some b =>
                              cases b with
                              | false =>
                                  simp only [hc, FieldAnalyze.permitted.injEq] at h
                                  exact h.1.symm
                              | true =>
                                  simp only [hc] at h
                                  exact (fieldAnalyze_tail_not_permitted h).elim

/-- a literal family application, if permitted, is `.recursive 0`. -/
theorem fieldAnalyze_directRec {E : ResolvedEnv} {fam : Nat}
    (hfam : ∀ ls, transparentBody E fam ls = none)
    {fuel nuniv np ni depth : Nat} {T : Expr Nat} (hT : isFamilyApp fam T = true)
    {shape : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv np ni depth T = .permitted shape idx) :
    shape = .recursive 0 := by
  obtain ⟨ls, args, hsp, _⟩ := isFamilyApp_spine hT
  cases fuel with
  | zero => simp only [fieldAnalyze] at h <;> cases h
  | succ fuel =>
      simp only [fieldAnalyze] at h
      cases fuel with
      | zero => simp only [piTelescopeFuel] at h <;> cases h
      | succ fuel =>
          cases fuel with
          | zero => simp only [piTelescopeFuel, whnfFuel] at h <;> cases h
          | succ fuel =>
              simp only [piTelescopeFuel_famHead hsp (hfam ls) fuel, domainsContainFuel,
                List.length_nil, Nat.zero_add] at h
              cases hpf : properFamilyFuel E (fuel + 2) fam nuniv np ni (depth - 1) T with
              | none => simp only [hpf] at h <;> cases h
              | some b =>
                  cases b with
                  | true =>
                      simp only [hpf, FieldAnalyze.permitted.injEq] at h
                      exact h.1.symm
                  | false =>
                      simp only [hpf] at h
                      cases hc : containsFamilyFuel E fam (fuel + 2) T with
                      | none => simp only [hc] at h <;> cases h
                      | some b =>
                          cases b with
                          | false => exact absurd hc (containsFamilyFuel_famHead _ _ hsp)
                          | true =>
                              simp only [hc] at h
                              exact (fieldAnalyze_tail_not_permitted h).elim

/-- the list-level agreement: admission's shapes are the legacy kinds. -/
theorem fieldShapesFuel_eq_kinds {E : ResolvedEnv} {fam : Nat} (hE : FamFreeBodies E fam)
    (hfam : ∀ ls, transparentBody E fam ls = none) {fuel nuniv np ni : Nat} :
    (Ts : List (Expr Nat)) → (depth : Nat) → {kinds : List RecKind} →
    analyzeFields fam Ts = some kinds → {shapes : List FieldShape} →
    fieldShapesFuel E fuel fam nuniv np ni depth Ts = some shapes →
    shapes = kinds.map shapeOfKind
  | [], _, kinds, hk, shapes, hs => by
      simp only [analyzeFields, Option.some.injEq] at hk
      simp only [fieldShapesFuel, Option.some.injEq] at hs
      rw [← hk, ← hs]
      rfl
  | T :: Ts, depth, kinds, hk, shapes, hs => by
      simp only [analyzeFields] at hk
      cases ha : analyzeField fam T with
      | none => simp only [ha] at hk <;> cases hk
      | some k =>
          cases hr : analyzeFields fam Ts with
          | none => simp only [ha, hr] at hk <;> cases hk
          | some ks =>
              simp only [ha, hr, Option.some.injEq] at hk
              rw [← hk]
              simp only [fieldShapesFuel] at hs
              cases hf : fieldAnalyze E fuel fam nuniv np ni depth T with
              | permitted shape idx =>
                  simp only [hf] at hs
                  cases hrest : fieldShapesFuel E fuel fam nuniv np ni (depth + 1) Ts with
                  | none => simp only [hrest] at hs <;> cases hs
                  | some rest =>
                      simp only [hrest, Option.map_some', Option.some.injEq] at hs
                      rw [← hs, List.map_cons, fieldShapesFuel_eq_kinds hE hfam Ts (depth + 1) hr hrest]
                      congr 1
                      unfold analyzeField at ha
                      by_cases ho : occursConst fam T = false
                      · rw [ho] at ha
                        simp only [Bool.not_false, if_true, Option.some.injEq] at ha
                        rw [← ha]
                        exact fieldAnalyze_plain hE ho hf
                      · have ho' : occursConst fam T = true := by
                          cases h : occursConst fam T with
                          | false => exact absurd h ho
                          | true => rfl
                        rw [ho'] at ha
                        simp only [Bool.not_true, Bool.false_eq_true, if_false] at ha
                        by_cases hfa : isFamilyApp fam T = true
                        · simp only [hfa, if_true, Option.some.injEq] at ha
                          rw [← ha]
                          exact fieldAnalyze_directRec hfam hfa hf
                        · rw [if_neg hfa] at ha
                          cases ha
              | refused _ => simp only [hf] at hs <;> cases hs
              | unresolved => simp only [hf] at hs <;> cases hs

end Rcic.Declarative

#print axioms Rcic.Declarative.fieldShapesFuel_eq_kinds
#print axioms Rcic.Declarative.whnfFuel_famFree
#print axioms Rcic.Declarative.piTelescopeFuel_famHead
