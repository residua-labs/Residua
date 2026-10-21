import rcic.RcicNativeTypedModelRel

/-!
# RcicNativeTypedModelIota — the recursor clauses of `ApproxT` at work: K dissolves model-side

Item 2 (T2 of #7689).  Segment 3's `ApproxT` now has two recursor clauses: `recursor` (the
`ApproxDI` shape: the major is demanded as a constructor spine) for a family **not** declared
into `Sort 0`, and **`recursorProp`** for a family declared into `Sort 0` (`PropFamilyS`): the
major's demand is `[]` and the fields' interpretations are `⊥`.  A proposition family has only
the non-strict clause.

* **§1 Application spines** over `CptT`: `AppCptT`, `FoldAppCptT`, `approxT_app_iff_appCpt`,
  `approxT_foldApps_iff`, and the peeling of a curried step function across an argument spine
  (`foldAppCptT_curryStepT_iff`).
* **§2 The constant inversion** `approxT_const_inv`, and the recursor inversion for a reference
  all of whose witnesses are proposition-family (`approxT_propRec_inv`).
* **§3 Major independence (T2)**: `approxT_recCall_major_indep` — at a proposition-family
  recursor the denotation of `recCall r pre x` does not depend on `x` at all.  Hence, with the
  ι-soundness of the typed model as the one named premise (`IotaSoundT`, the port of
  `approxDI_iotaS`), **the K step is model-invariant**: `semEqT_kStar_of_iotaSoundT` relates
  `recCall (const w.recRef w.ls) w.preMajor x` to `iotaRhsOf w` for every major `x` — this is
  the `ReadbackModelInv` obligation of `readback-ck`'s `kStar` arm (and of `WhStepK.pmajor`),
  discharged on the model side.  No use of T1 is needed: the typed demands of `pi`/`lam`
  already make a minor unable to demand anything but `⊥` of a proof argument.
* **§4** W-K's model side at the pins: `approxT_recCall_kRec_indep` at `trueEnvU` for every
  proof major.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

/-! ### §1 — application spines -/

/-- One application step on compacts. -/
inductive AppCptT (E : ResolvedEnv) (ρ : EnvT) : CptT → Expr Nat → CptT → Prop
  | bot (d : CptT) (x : Expr Nat) : AppCptT E ρ d x .bot
  | app {g : List (List CptT × CptT)} {s : List CptT × CptT} {x : Expr Nat}
      (hs : s ∈ g) (hx : ∀ u ∈ s.1, ApproxT E ρ x u) :
      AppCptT E ρ (.lam g) x s.2
  | appSpine {r : Nat} {args : List CptT} {x : Expr Nat} {u : CptT}
      (hx : ApproxT E ρ x u) :
      AppCptT E ρ (.spine r args) x (.spine r (args ++ [u]))

theorem approxT_app_iff_appCpt (E : ResolvedEnv) (ρ : EnvT) (f x : Expr Nat) (c : CptT) :
    ApproxT E ρ (.app f x) c ↔ ∃ d, ApproxT E ρ f d ∧ AppCptT E ρ d x c := by
  constructor
  · intro h
    rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨r, args, u, rfl, hf, ha⟩
    · exact ⟨.bot, .bot ρ f, .bot _ _⟩
    · exact ⟨.lam g, hf, .app hs ha⟩
    · exact ⟨.spine r args, hf, .appSpine ha⟩
  · rintro ⟨d, hf, hstep⟩
    cases hstep with
    | bot => exact .bot _ _
    | app hs hx => exact .app hf hs hx
    | appSpine hx => exact .appSpine hf hx

/-- Application of a compact to an argument spine. -/
inductive FoldAppCptT (E : ResolvedEnv) (ρ : EnvT) : CptT → List (Expr Nat) → CptT → Prop
  | bot (d : CptT) (xs : List (Expr Nat)) : FoldAppCptT E ρ d xs .bot
  | nil (c : CptT) : FoldAppCptT E ρ c [] c
  | cons {d d' c : CptT} {x : Expr Nat} {xs : List (Expr Nat)}
      (hstep : AppCptT E ρ d x d') (hrest : FoldAppCptT E ρ d' xs c) :
      FoldAppCptT E ρ d (x :: xs) c

theorem approxT_foldApps_iff (E : ResolvedEnv) (ρ : EnvT) (f : Expr Nat) (xs : List (Expr Nat))
    (c : CptT) : ApproxT E ρ (foldApps f xs) c ↔ ∃ d, ApproxT E ρ f d ∧ FoldAppCptT E ρ d xs c := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps]
      constructor
      · intro h; exact ⟨c, h, .nil c⟩
      · rintro ⟨d, hd, hfold⟩
        cases hfold with
        | bot => exact .bot ρ f
        | nil => exact hd
  | cons x xs ih =>
      simp only [foldApps]
      rw [ih]
      constructor
      · rintro ⟨d', hfx, hrest⟩
        rw [approxT_app_iff_appCpt] at hfx
        obtain ⟨d, hf, hstep⟩ := hfx
        exact ⟨d, hf, .cons hstep hrest⟩
      · rintro ⟨d, hf, hfold⟩
        cases hfold with
        | bot => exact ⟨.bot, .bot ρ (.app f x), .bot .bot xs⟩
        | cons hstep hrest =>
            exact ⟨_, (approxT_app_iff_appCpt E ρ f x _).mpr ⟨d, hf, hstep⟩, hrest⟩

theorem foldAppCptT_bot_inv {E : ResolvedEnv} {ρ : EnvT} {xs : List (Expr Nat)} {c : CptT}
    (h : FoldAppCptT E ρ .bot xs c) : c = .bot := by
  induction xs with
  | nil => cases h <;> rfl
  | cons x xs ih =>
      cases h with
      | bot => rfl
      | cons hstep hrest =>
          cases hstep with
          | bot => exact ih hrest

/-- Pointwise demand approximation of an argument spine. -/
inductive ApproxArgsDemandT (E : ResolvedEnv) (ρ : EnvT) : List (Expr Nat) → List (List CptT) → Prop
  | nil : ApproxArgsDemandT E ρ [] []
  | cons {a : Expr Nat} {as : List (Expr Nat)} {us : List CptT} {uss : List (List CptT)}
      (ha : ∀ u ∈ us, ApproxT E ρ a u) (has : ApproxArgsDemandT E ρ as uss) :
      ApproxArgsDemandT E ρ (a :: as) (us :: uss)

/-- Peeling `curryStepT uss c₀` across an argument spine of the same length. -/
theorem foldAppCptT_curryStepT_iff {E : ResolvedEnv} {ρ : EnvT} {uss : List (List CptT)}
    {xs : List (Expr Nat)} (hlen : uss.length = xs.length) {c₀ c : CptT} :
    FoldAppCptT E ρ (curryStepT uss c₀) xs c ↔ c = .bot ∨ (ApproxArgsDemandT E ρ xs uss ∧ c = c₀) := by
  induction uss generalizing xs c₀ c with
  | nil =>
      cases xs with
      | nil =>
          simp only [curryStepT]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | nil => exact Or.inr ⟨.nil, rfl⟩
          · rintro (rfl | ⟨_, rfl⟩)
            · exact .bot _ []
            · exact .nil _
      | cons _ _ => cases hlen
  | cons us uss ih =>
      cases xs with
      | nil => cases hlen
      | cons x xs =>
          simp only [List.length_cons] at hlen
          simp only [curryStepT]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | cons hstep hrest =>
                cases hstep with
                | bot => exact Or.inl (foldAppCptT_bot_inv hrest)
                | app hs hx =>
                    have hs' : _ = (us, curryStepT uss c₀) := List.mem_singleton.mp hs
                    cases hs'
                    rcases (ih (Nat.succ.inj hlen)).mp hrest with rfl | ⟨hxs, rfl⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨.cons hx hxs, rfl⟩
          · rintro (rfl | ⟨hargs, rfl⟩)
            · exact .bot _ _
            · cases hargs with
              | cons hx hxs =>
                  exact .cons (.app (List.mem_singleton.mpr rfl) hx)
                    ((ih (Nat.succ.inj hlen)).mpr (Or.inr ⟨hxs, rfl⟩))

/-! ### §2 — constant and recursor inversions -/

/-- Every way a constant reference acquires a compact. -/
theorem approxT_const_inv {E : ResolvedEnv} {ρ : EnvT} {r : Nat} {ls : List Level} {c : CptT}
    (h : ApproxT E ρ (.const r ls) c) :
    c = .bot ∨
    (RigidConst E r ∧ ¬ PropCtorT E r ∧ c = .spine r []) ∨
    (∃ m b, DeltaConst E r m b ∧ ApproxT E EnvT.bot (instantiateLevels ls b) c) ∨
    (∃ (w : IotaWitnessS E) (us_pre us_fields : List (List CptT)) (c₀ : CptT),
      w.recRef = r ∧ ¬ PropFamilyS w ∧ us_pre.length = w.preMajor.length ∧
      us_fields.length = w.fields.length ∧
      ApproxT E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c₀ ∧
      c = curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c₀) ∨
    (∃ (w : IotaWitnessS E) (us_pre : List (List CptT)) (c₀ : CptT),
      w.recRef = r ∧ PropFamilyS w ∧ us_pre.length = w.preMajor.length ∧
      ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c₀ ∧
      c = curryStepT (us_pre ++ [[]]) c₀) := by
  cases h with
  | bot => exact Or.inl rfl
  | const _ _ _ hrigid hnp => exact Or.inr (Or.inl ⟨hrigid, hnp, rfl⟩)
  | delta hd h => exact Or.inr (Or.inr (Or.inl ⟨_, _, hd, h⟩))
  | recursor ls hnp hpre hflds h =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, hnp, hpre, hflds, h, rfl⟩)))
  | recursorProp ls hP hpre h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, hP, hpre, h, rfl⟩)))

/-- At a reference every structured witness of which is proposition-family and that is neither
    rigid nor a definition, the only non-`⊥` compacts are the non-strict curried steps. -/
theorem approxT_propRec_inv {E : ResolvedEnv} {ρ : EnvT} {r : Nat} {ls : List Level} {c : CptT}
    (hnr : ¬ RigidConst E r) (hnd : ∀ m b, ¬ DeltaConst E r m b)
    (hP : ∀ w : IotaWitnessS E, w.recRef = r → PropFamilyS w)
    (h : ApproxT E ρ (.const r ls) c) :
    c = .bot ∨ ∃ (w : IotaWitnessS E) (us_pre : List (List CptT)) (c₀ : CptT),
      w.recRef = r ∧ us_pre.length = w.preMajor.length ∧
      ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c₀ ∧
      c = curryStepT (us_pre ++ [[]]) c₀ := by
  rcases approxT_const_inv h with h0 | ⟨hr, _, _⟩ | ⟨m, b, hd, _⟩ | ⟨w, _, _, _, hw, hnp, _⟩
    | ⟨w, us_pre, c₀, hw, _, hpre, hs, hc⟩
  · exact Or.inl h0
  · exact (hnr hr).elim
  · exact (hnd m b hd).elim
  · exact (hnp (hP w hw)).elim
  · exact Or.inr ⟨w, us_pre, c₀, hw, hpre, hs, hc⟩

/-- A recursor reference is neither rigid nor a definition. -/
theorem recRef_not_rigid {E : ResolvedEnv} (w : IotaWitnessS E) : ¬ RigidConst E w.recRef :=
  fun hr => (hr _ w.hrec).2 w.hrecK

theorem recRef_not_delta {E : ResolvedEnv} (w : IotaWitnessS E) (m : CheckedMember) (b : Expr Nat) :
    ¬ DeltaConst E w.recRef m b := fun hd => by
  obtain ⟨hm, _, hnrec, _⟩ := hd
  have e : w.recMember = m := Option.some.inj (w.hrec.symm.trans hm)
  exact hnrec (e ▸ w.hrecK)

/-! ### §3 — major independence (T2) and the K step -/

theorem approxArgsDemandT_append_singleton_inv {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {pre : List (Expr Nat)} {x : Expr Nat} {uss : List (List CptT)},
    ApproxArgsDemandT E ρ (pre ++ [x]) uss →
    ∃ us_pre us_x, uss = us_pre ++ [us_x] ∧ ApproxArgsDemandT E ρ pre us_pre ∧ ∀ u ∈ us_x, ApproxT E ρ x u
  | [], x, uss, h => by
      cases h with
      | cons hx has =>
          cases has
          exact ⟨[], _, rfl, .nil, hx⟩
  | p :: pre, x, uss, h => by
      cases h with
      | cons hp has =>
          obtain ⟨us_pre, us_x, rfl, hpre, hx⟩ := approxArgsDemandT_append_singleton_inv has
          exact ⟨_ :: us_pre, us_x, rfl, .cons hp hpre, hx⟩

theorem approxArgsDemandT_append_singleton {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {pre : List (Expr Nat)} {x : Expr Nat} {us_pre : List (List CptT)} {us_x : List CptT},
    ApproxArgsDemandT E ρ pre us_pre → (∀ u ∈ us_x, ApproxT E ρ x u) →
    ApproxArgsDemandT E ρ (pre ++ [x]) (us_pre ++ [us_x])
  | [], x, us_pre, us_x, h, hx => by
      cases h
      exact .cons hx .nil
  | p :: pre, x, us_pre, us_x, h, hx => by
      cases h with
      | cons hp hpre => exact .cons hp (approxArgsDemandT_append_singleton hpre hx)

theorem ApproxArgsDemandT.length_eq {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {args : List (Expr Nat)} {uss : List (List CptT)}, ApproxArgsDemandT E ρ args uss →
      uss.length = args.length
  | _, _, .nil => rfl
  | _, _, .cons _ has => by simp [ApproxArgsDemandT.length_eq has]

/-- **T2 — major independence.**  At a reference all of whose structured witnesses are
    proposition-family with the given pre-major length, the denotation of `recCall r pre x` does
    not depend on the major `x`. -/
theorem approxT_recCall_major_indep {E : ResolvedEnv} {ρ : EnvT} {r : Nat} {ls : List Level}
    {pre : List (Expr Nat)}
    (hnr : ¬ RigidConst E r) (hnd : ∀ m b, ¬ DeltaConst E r m b)
    (hP : ∀ w : IotaWitnessS E, w.recRef = r → PropFamilyS w ∧ w.preMajor.length = pre.length)
    (x y : Expr Nat) (c : CptT) :
    ApproxT E ρ (recCall (.const r ls) pre x) c ↔ ApproxT E ρ (recCall (.const r ls) pre y) c := by
  have key : ∀ x : Expr Nat, ApproxT E ρ (recCall (.const r ls) pre x) c ↔
      (c = .bot ∨ ∃ (w : IotaWitnessS E) (us_pre : List (List CptT)),
        w.recRef = r ∧ us_pre.length = w.preMajor.length ∧ ApproxArgsDemandT E ρ pre us_pre ∧
        ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
          (instantiateLevels ls w.schema) c) := by
    intro x
    unfold recCall
    rw [approxT_foldApps_iff]
    constructor
    · rintro ⟨d, hd, hfold⟩
      rcases approxT_propRec_inv hnr hnd (fun w hw => (hP w hw).1) hd with rfl | ⟨w, us_pre, c₀, hw, hpre, hs, rfl⟩
      · exact Or.inl (foldAppCptT_bot_inv hfold)
      · have hlen : (us_pre ++ [[]]).length = (pre ++ [x]).length := by
          simp [hpre, (hP w hw).2]
        rcases (foldAppCptT_curryStepT_iff hlen).mp hfold with rfl | ⟨hargs, rfl⟩
        · exact Or.inl rfl
        · obtain ⟨us_pre', us_x, he, hpre', _⟩ := approxArgsDemandT_append_singleton_inv hargs
          have e := List.append_inj' he (by simp)
          obtain ⟨rfl, _⟩ := e
          exact Or.inr ⟨w, us_pre, hw, hpre, hpre', hs⟩
    · rintro (rfl | ⟨w, us_pre, hw, hpre, hargs, hs⟩)
      · exact ⟨.bot, .bot _ _, .bot _ _⟩
      · refine ⟨curryStepT (us_pre ++ [[]]) c, ?_, ?_⟩
        · subst hw
          exact .recursorProp ls (hP w rfl).1 hpre hs
        · have hlen : (us_pre ++ [[]]).length = (pre ++ [x]).length := by
            simp [hpre, (hP w hw).2]
          exact (foldAppCptT_curryStepT_iff hlen).mpr
            (Or.inr ⟨approxArgsDemandT_append_singleton hargs (fun _ hu => (List.not_mem_nil _ hu).elim), rfl⟩)
  rw [key x, key y]

/-- The one named premise: ι-soundness of the typed model (the port of `approxDI_iotaS`). -/
def IotaSoundT (E : ResolvedEnv) : Prop :=
  ∀ (w : IotaWitnessS E) (ρ : EnvT), SemEqT E ρ (iotaLhsOfS w) (iotaRhsOfS w)

/-- The structured witness behind a `DerivedIotaT`. -/
theorem derivedIotaT_inv {E : ResolvedEnv} {l r : Expr Nat} :
    DerivedIotaT E l r → ∃ w' : IotaWitnessS E, iotaLhsOfS w' = l ∧ iotaRhsOfS w' = r
  | .of w' => ⟨w', rfl, rfl⟩

/-- **The K step is model-invariant** given ι-soundness: for a proposition-family recursor the
    redex at ANY major has the denotation of the contractum at the canonical major.  This is the
    `ReadbackModelInv` obligation of `readback-ck`'s `kStar` arm (and `WhStepK.pmajor`) on the
    model side. -/
theorem semEqT_kStar_of_iotaSoundT {E : ResolvedEnv} (hW : EnvWfT E) (hI : IotaSoundT E)
    (w : IotaWitness E)
    (hP : ∀ w' : IotaWitnessS E, w'.recRef = w.recRef → PropFamilyS w' ∧ w'.preMajor.length = w.preMajor.length)
    (x : Expr Nat) (ρ : EnvT) :
    SemEqT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨ht⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  have hnr : ¬ RigidConst E w.recRef := fun hr => (hr _ w.hrec).2 w.hrecK
  have hnd : ∀ m b, ¬ DeltaConst E w.recRef m b := fun m b hd => by
    obtain ⟨hm, _, hnrec, _⟩ := hd
    have e : w.recMember = m := Option.some.inj (w.hrec.symm.trans hm)
    exact hnrec (e ▸ w.hrecK)
  intro c
  rw [approxT_recCall_major_indep hnr hnd hP x (ctorMajor w) c]
  obtain ⟨w', hl, hr⟩ := derivedIotaT_inv ht
  have := hI w' ρ c
  rw [hl, hr] at this
  exact this

/-! ### §4 — W-K's model side at the pins -/

/-- `True.rec` at `trueEnvU` (`kRec x = recCall (const 2 [2]) [kMot, Sort 0] x`): every structured
    witness at reference `2` is proposition-family with two pre-major arguments. -/
theorem trueEnvU_recRef_propFamily (w : IotaWitnessS trueEnvU) (hw : w.recRef = 2) :
    PropFamilyS w ∧ w.preMajor.length = 2 := by
  have hm : w.recMember = trueRecMemberU := Option.some.inj (w.hrec.symm.trans (by rw [hw]; rfl))
  have hfam : w.familyRef = 0 := by
    have h1 := w.hrecIdx
    have h2 := w.hnmin
    have h3 := w.hidx
    have h4 := w.hctorIdx
    rw [hm] at h2
    have hpc : piCount trueRecMemberU.mtype = 3 := rfl
    rw [hpc] at h2
    omega
  have hfm : w.famMember = trueFamMember := Option.some.inj (w.hfam.symm.trans (by rw [hfam]; rfl))
  refine ⟨?_, ?_⟩
  · show piBody w.famMember.mtype = .sort .zero
    rw [hfm]; rfl
  · have h2 := w.hnmin
    rw [hm] at h2
    have hpc : piCount trueRecMemberU.mtype = 3 := rfl
    rw [hpc] at h2
    have h3 := w.hpre
    omega

/-- **W-K, model side**: `True.rec M m x` has the same typed compacts for every major `x`. -/
theorem approxT_recCall_kRec_indep (ρ : EnvT) (x y : Expr Nat) (c : CptT) :
    ApproxT trueEnvU ρ (kRec x) c ↔ ApproxT trueEnvU ρ (kRec y) c := by
  show ApproxT trueEnvU ρ (recCall (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero] x) c ↔
    ApproxT trueEnvU ρ (recCall (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero] y) c
  exact approxT_recCall_major_indep (E := trueEnvU) (ρ := ρ) (r := 2)
    (ls := [.succ (.succ .zero)]) (pre := [kMot, .sort .zero])
    (fun hr => (hr _ rfl).2 rfl)
    (fun m b ⟨hm, _, hnrec, _⟩ =>
      hnrec (by
        have e : trueRecMemberU = m := Option.some.inj hm
        subst e
        rfl))
    (fun w hw => trueEnvU_recRef_propFamily w hw) x y c

#print axioms AppCptT
#print axioms approxT_app_iff_appCpt
#print axioms FoldAppCptT
#print axioms approxT_foldApps_iff
#print axioms foldAppCptT_bot_inv
#print axioms ApproxArgsDemandT
#print axioms foldAppCptT_curryStepT_iff
#print axioms approxT_const_inv
#print axioms approxT_propRec_inv
#print axioms recRef_not_rigid
#print axioms recRef_not_delta
#print axioms approxArgsDemandT_append_singleton_inv
#print axioms approxArgsDemandT_append_singleton
#print axioms ApproxArgsDemandT.length_eq
#print axioms approxT_recCall_major_indep
#print axioms IotaSoundT
#print axioms derivedIotaT_inv
#print axioms semEqT_kStar_of_iotaSoundT
#print axioms trueEnvU_recRef_propFamily
#print axioms approxT_recCall_kRec_indep

end Rcic.Declarative.NativeValleys.TypedModelAudit
