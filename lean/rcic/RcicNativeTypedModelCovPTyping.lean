import rcic.RcicNativeTypedModelCovPPositive
import rcic.RcicNativeTypedModelCov2
import rcic.RcicNativeTypedModelCovRelCore

/-!
# Positive collapse with optional neutral reflection

The universe arm retains `IsPropCT`, including partial proposition observations.
Only the proposition-collapse test is changed to `IsPropCTP`. `false` selects
(b); `true` additionally selects the guarded reflection clause (r).

Reflection is restricted to body-free ordinary declarations: axiom, definition,
theorem, or opaque. Inductive-family, constructor, and recursor classes are
excluded. The added target shape is Pi; the old non-Prop spine and sort arms
already admit spines. Bottom, lambda, and universe Prop retain their inversion
laws. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit TypedModelAudit TypedModelCovRelAudit

variable {E : ResolvedEnv} {reflect : Bool}

def NeutralHeadP (E : ResolvedEnv) (h : Nat) : Prop :=
  ∃ m, E.members h = some m ∧ m.body = none ∧
    (m.mclass = .axiomM ∨ m.mclass = .definitionM ∨
      m.mclass = .theoremM ∨ m.mclass = .opaqueM)

theorem neutralHeadP_rigid {h : Nat} (hh : NeutralHeadP E h) : RigidConst E h := by
  obtain ⟨m, hm, hb, hc⟩ := hh
  intro m' hm'
  have he : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  refine ⟨Or.inl hb, ?_⟩
  rcases hc with hc | hc | hc | hc <;> rw [hc] <;> decide

theorem neutralHeadP_not_constructor {h : Nat} {m : CheckedMember}
    (hh : NeutralHeadP E h) (hm : E.members h = some m) :
    m.mclass ≠ .constructorM := by
  obtain ⟨m', hm', _, hc⟩ := hh
  have he : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  rcases hc with hc | hc | hc | hc <;> rw [hc] <;> decide

/-- The original exact telescope condition, parameterized only in recursive
argument typing. Constructors continue to use this branch. -/
def RigidPiGateP (T : CptT → CptT → Prop) (E : ResolvedEnv)
    (h : Nat) (us : List CptT) (a : CptT)
    (g : List (List CptT × CptT)) : Prop :=
  ∃ m ls, E.members h = some m ∧ RigidConst E h ∧ ls.length = m.arity ∧
    (∀ i (hi : i < us.length) (D C : Expr Nat),
      peelPi (instantiateLevels ls m.mtype) i = some (.pi D C) →
      ∃ d, ApproxT E (spineArgEnv us i) D d ∧ T us[i] d) ∧
    ∃ Tres, peelPi (instantiateLevels ls m.mtype) us.length = some Tres ∧
      ApproxT E (spineArgEnv us us.length) Tres (.pi a g)

/-- One relation with a Boolean switch. The genuinely changed recursive
clauses are written once; unchanged atomic arms retain their old meaning. -/
def CTyCovP2 (reflect : Bool) (E : ResolvedEnv) : CptT → CptT → Prop
  | u, .bot => u = .bot
  | u, .prop => u = .bot ∨ IsPropCT E u
  | u, .sort => u = .bot ∨ TyCodeCT u
  | .bot, .pi _ _ => True
  | .lam f, .pi a g => ¬ IsPropCTP E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyCovP2 reflect E v a) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g,
        (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCovP2 reflect E s.2 t.2)
  | .spine h us, .pi a g => ¬ IsPropCTP E (.pi a g) ∧
      ((∃ m ls, E.members h = some m ∧ RigidConst E h ∧ ls.length = m.arity ∧
        (∀ i (hi : i < us.length) (D C : Expr Nat),
          peelPi (instantiateLevels ls m.mtype) i = some (.pi D C) →
          ∃ d, ApproxT E (spineArgEnv us i) D d ∧ CTyCovP2 reflect E us[i] d) ∧
        ∃ Tres, peelPi (instantiateLevels ls m.mtype) us.length = some Tres ∧
          ApproxT E (spineArgEnv us us.length) Tres (.pi a g)) ∨
        reflect = true ∧ NeutralHeadP E h)
  | _, .pi _ _ => False
  | u, .lam _ => u = .bot
  | u, .spine r args => u = .bot ∨
      ((∃ r' args', u = .spine r' args') ∧ ¬ IsPropCTP E (.spine r args))
termination_by u _ => sizeOf u
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show v ∈ s.1 from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₃ := sizeOfT_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₂ := sizeOfT_snd_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›)
    omega

namespace CTyCovP2

theorem bot (a : CptT) : CTyCovP2 reflect E .bot a := by
  cases a <;> simp only [CTyCovP2]
    <;> first | trivial | rfl | exact Or.inl True.intro | exact Or.inl rfl

theorem univProp {c : CptT} (h : IsPropCT E c) : CTyCovP2 reflect E c .prop := by
  cases c <;> rw [CTyCovP2] <;> exact Or.inr h

theorem univType {c : CptT} (h : TyCodeCT c) : CTyCovP2 reflect E c .sort := by
  cases c <;> rw [CTyCovP2] <;> exact Or.inr h

theorem lam {a : CptT} {g f : List (List CptT × CptT)}
    (hnp : ¬ IsPropCTP E (.pi a g))
    (hdom : ∀ s ∈ f, ∀ v ∈ s.1, CTyCovP2 reflect E v a)
    (hcov : ∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g,
      (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCovP2 reflect E s.2 t.2) :
    CTyCovP2 reflect E (.lam f) (.pi a g) := by
  rw [CTyCovP2]
  exact ⟨hnp, hdom, hcov⟩

theorem rigidPi {h : Nat} {us : List CptT} {a : CptT}
    {g : List (List CptT × CptT)} (hnp : ¬ IsPropCTP E (.pi a g))
    (hgate : RigidPiGateP (CTyCovP2 reflect E) E h us a g) :
    CTyCovP2 reflect E (.spine h us) (.pi a g) := by
  rw [CTyCovP2]
  exact ⟨hnp, Or.inl hgate⟩

theorem reflectedPi {h : Nat} {us : List CptT} {a : CptT}
    {g : List (List CptT × CptT)} (hr : reflect = true)
    (hh : NeutralHeadP E h) (hnp : ¬ IsPropCTP E (.pi a g)) :
    CTyCovP2 reflect E (.spine h us) (.pi a g) := by
  rw [CTyCovP2]
  exact ⟨hnp, Or.inr ⟨hr, hh⟩⟩

theorem spine {r r' : Nat} {args args' : List CptT}
    (hnp : ¬ IsPropCTP E (.spine r' args')) :
    CTyCovP2 reflect E (.spine r args) (.spine r' args') := by
  rw [CTyCovP2]
  exact Or.inr ⟨⟨r, args, rfl⟩, hnp⟩

end CTyCovP2

/-- Shape interface with positive collapse. Universe membership deliberately
continues to describe possibly partial proposition approximants. -/
structure CovTypingP (E : ResolvedEnv) where
  ty : CptT → CptT → Prop
  bot : ∀ a, ty .bot a
  bot_inv : ∀ {u}, ty u .bot → u = .bot
  prop_inv : ∀ {u}, ty u .prop → u = .bot ∨ IsPropCT E u
  sort_inv : ∀ {u}, ty u .sort → u = .bot ∨ TyCodeCT u
  lam_inv : ∀ {u g}, ty u (.lam g) → u = .bot
  spine_inv : ∀ {u r args}, ty u (.spine r args) →
    u = .bot ∨ ∃ r' args', u = .spine r' args'
  pi_inv : ∀ {u a g}, ty u (.pi a g) →
    u = .bot ∨ (∃ f, u = .lam f ∧ CovLamTyping ty a g f) ∨
      ∃ r args, u = .spine r args
  prop_bot : ∀ {a u}, IsPropCTP E a → ty u a → u = .bot

theorem ctyCovP2_bot_inv {u : CptT} (h : CTyCovP2 reflect E u .bot) :
    u = .bot := by cases u <;> rw [CTyCovP2] at h <;> exact h

theorem ctyCovP2_prop_inv {u : CptT} (h : CTyCovP2 reflect E u .prop) :
    u = .bot ∨ IsPropCT E u := by
  cases u <;> rw [CTyCovP2] at h <;> exact h

theorem ctyCovP2_sort_inv {u : CptT} (h : CTyCovP2 reflect E u .sort) :
    u = .bot ∨ TyCodeCT u := by
  cases u <;> rw [CTyCovP2] at h <;> exact h

theorem ctyCovP2_lam_inv {u : CptT} {g : List (List CptT × CptT)}
    (h : CTyCovP2 reflect E u (.lam g)) : u = .bot := by
  cases u <;> rw [CTyCovP2] at h <;> exact h

theorem ctyCovP2_spine_iff {u : CptT} {r : Nat} {args : List CptT} :
    CTyCovP2 reflect E u (.spine r args) ↔
      u = .bot ∨ (∃ r' args', u = .spine r' args') ∧
        ¬ IsPropCTP E (.spine r args) := by
  cases u <;> rw [CTyCovP2]

theorem ctyCovP2_pi_iff {u a : CptT} {g : List (List CptT × CptT)} :
    CTyCovP2 reflect E u (.pi a g) ↔ u = .bot ∨
      (¬ IsPropCTP E (.pi a g) ∧
        ((∃ f, u = .lam f ∧ CovLamTyping (CTyCovP2 reflect E) a g f) ∨
         ∃ h us, u = .spine h us ∧
           (RigidPiGateP (CTyCovP2 reflect E) E h us a g ∨
             reflect = true ∧ NeutralHeadP E h))) := by
  constructor
  · intro h
    cases u with
    | bot => exact Or.inl rfl
    | prop | sort | pi _ _ => simp only [CTyCovP2] at h
    | lam f =>
        rw [CTyCovP2] at h
        exact Or.inr ⟨h.1, Or.inl ⟨f, rfl, h.2⟩⟩
    | spine r us =>
        rw [CTyCovP2] at h
        exact Or.inr ⟨h.1, Or.inr ⟨r, us, rfl, h.2⟩⟩
  · rintro (rfl | ⟨hp, ⟨f, rfl, hd, hc⟩ | ⟨h, us, rfl, hg | ⟨hr, hh⟩⟩⟩)
    · exact .bot _
    · exact .lam hp hd hc
    · exact .rigidPi hp hg
    · exact .reflectedPi hr hh hp

theorem ctyCovP2_prop_bot {a u : CptT} (hp : IsPropCTP E a)
    (h : CTyCovP2 reflect E u a) : u = .bot := by
  cases a with
  | bot => exact ctyCovP2_bot_inv h
  | prop => exact (not_isPropCTP_prop E hp).elim
  | sort => exact (not_isPropCTP_sort E hp).elim
  | lam g => exact ctyCovP2_lam_inv h
  | pi a g =>
      rcases ctyCovP2_pi_iff.mp h with hb | ⟨hnp, _⟩
      · exact hb
      · exact (hnp hp).elim
  | spine r args =>
      rcases ctyCovP2_spine_iff.mp h with hb | ⟨_, hnp⟩
      · exact hb
      · exact (hnp hp).elim

def C2P (reflect : Bool) (E : ResolvedEnv) : CovTypingP E where
  ty := CTyCovP2 reflect E
  bot := CTyCovP2.bot
  bot_inv := ctyCovP2_bot_inv
  prop_inv := ctyCovP2_prop_inv
  sort_inv := ctyCovP2_sort_inv
  lam_inv := ctyCovP2_lam_inv
  spine_inv := by
    intro u r args ht
    rcases ctyCovP2_spine_iff.mp ht with hb | ⟨hs, _⟩
    · exact Or.inl hb
    · exact Or.inr hs
  pi_inv := by
    intro u a g ht
    rcases ctyCovP2_pi_iff.mp ht with hb | ⟨_, h⟩
    · exact Or.inl hb
    · rcases h with hl | ⟨r, args, he, _⟩
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr ⟨r, args, he⟩)
  prop_bot := ctyCovP2_prop_bot

/-- The unchanged universe arm is essential for this embedding. Changing
`prop_inv` to positive evidence would lose legitimate partial observations. -/
theorem ctyCovP2_of_ctyCov2 (reflect : Bool) :
    ∀ (u a : CptT), CTyCov2 E u a → CTyCovP2 reflect E u a := by
  suffices h : ∀ k (u : CptT), sizeOf u ≤ k →
      ∀ a, CTyCov2 E u a → CTyCovP2 reflect E u a from
    fun u a => h (sizeOf u) u (Nat.le_refl _) a
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro u hu a ht
      have rec : ∀ v, sizeOf v < sizeOf u →
          ∀ b, CTyCov2 E v b → CTyCovP2 reflect E v b := by
        intro v hv
        exact ih (sizeOf v) (Nat.lt_of_lt_of_le hv hu) v (Nat.le_refl _)
      cases a with
      | bot => rw [ctyCov2_bot_inv ht]; exact .bot _
      | prop =>
          rcases ctyCov2_prop_inv ht with rfl | hp
          · exact .bot _
          · exact .univProp hp
      | sort =>
          rcases ctyCov2_sort_inv ht with rfl | ht
          · exact .bot _
          · exact .univType ht
      | lam _ => rw [ctyCov2_lam_inv ht]; exact .bot _
      | spine r args =>
          rcases ctyCov2_spine_inv ht with rfl | ⟨⟨r', args', rfl⟩, hnp⟩
          · exact .bot _
          · exact .spine (fun hp => hnp (isPropCT_of_isPropCTP hp))
      | pi a g =>
          rcases ctyCov2_pi_inv ht with rfl | ⟨f, rfl, hnp, hd, hc⟩ |
            ⟨r, args, rfl, hnp, m, ls, hm, hr, hlen, hargs, Tres, hTres, hobs⟩
          · exact .bot _
          · apply CTyCovP2.lam (fun hp => hnp (isPropCT_of_isPropCTP hp))
            · intro s hs v hv
              apply rec v ?_ a (hd s hs v hv)
              have h₁ := List.sizeOf_lt_of_mem hv
              have h₂ := List.sizeOf_lt_of_mem hs
              have h₃ := sizeOfT_fst_lt s
              simp_wf
              omega
            · intro s hs
              rcases hc s hs with hb | ⟨t, ht, hsub, hout⟩
              · exact Or.inl hb
              · refine Or.inr ⟨t, ht, hsub, rec s.2 ?_ t.2 hout⟩
                have h₁ := List.sizeOf_lt_of_mem hs
                have h₂ := sizeOfT_snd_lt s
                simp_wf
                omega
          · apply CTyCovP2.rigidPi (fun hp => hnp (isPropCT_of_isPropCTP hp))
            refine ⟨m, ls, hm, hr, hlen, ?_, Tres, hTres, hobs⟩
            intro i hi D B hpi
            obtain ⟨d, hd, ht⟩ := hargs i hi D B hpi
            refine ⟨d, hd, rec args[i] ?_ d ht⟩
            have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem hi)
            simp_wf
            omega

theorem ctyCovP2_of_ctyS (reflect : Bool) {u a : CptT} (h : CTyS E u a) :
    CTyCovP2 reflect E u a :=
  ctyCovP2_of_ctyCov2 reflect u a (ctyCov2_of_ctyS h)

theorem ctyCovP2_prop_iff {u : CptT} :
    CTyCovP2 reflect E u .prop ↔ CTyCov2 E u .prop := by
  constructor
  · intro h
    rcases ctyCovP2_prop_inv h with rfl | hp
    · exact ctyCov2_bot _
    · cases u <;> simp only [CTyCov2] <;> exact Or.inr hp
  · exact ctyCovP2_of_ctyCov2 reflect u .prop

theorem ctyCovP2_sort_iff {u : CptT} :
    CTyCovP2 reflect E u .sort ↔ CTyCov2 E u .sort := by
  constructor
  · intro h
    rcases ctyCovP2_sort_inv h with rfl | ht
    · exact ctyCov2_bot _
    · cases u <;> simp only [CTyCov2] <;> exact Or.inr ht
  · exact ctyCovP2_of_ctyCov2 reflect u .sort

theorem ctyCovP2_spine_iff_ctyCov2 {u : CptT} {r : Nat} {args : List CptT} :
    CTyCovP2 reflect E u (.spine r args) ↔ CTyCov2 E u (.spine r args) := by
  constructor
  · intro h
    rcases ctyCovP2_spine_iff.mp h with rfl | ⟨⟨r', args', rfl⟩, hnp⟩
    · exact ctyCov2_bot _
    · rw [CTyCov2]
      exact Or.inr ⟨⟨r', args', rfl⟩, fun hp => hnp (isPropCTP_spine_iff.mpr hp)⟩
  · exact ctyCovP2_of_ctyCov2 reflect u (.spine r args)

/-- A universe observation which is valid but has no positive proposition
evidence. Thus the universe inversion field cannot simply be strengthened. -/
theorem positive_prop_inv_incompatible (E : ResolvedEnv) (reflect : Bool) :
    ¬ (∀ {u}, CTyCovP2 reflect E u .prop → u = .bot ∨ IsPropCTP E u) := by
  intro h
  have ht : CTyCovP2 reflect E (.pi .bot []) .prop :=
    .univProp (.pi .bot (by intro t ht; cases ht))
  rcases h ht with hb | hp
  · exact CptT.noConfusion hb
  · exact not_isPropCTP_pi_nil E .bot hp

/-- Merely excluding positive proposition codes is insufficient to preserve
bottom inversion: bottom itself has no positive proposition evidence. -/
theorem reflection_at_all_nonprop_incompatible (C : CovTypingP E)
    (r : Nat) (us : List CptT)
    (hr : ∀ a, ¬ IsPropCTP E a → C.ty (.spine r us) a) : False :=
  CptT.noConfusion (C.bot_inv (hr .bot (not_isPropCTP_bot E)))

/-- Excluding bottom alone is still insufficient: lambda codes must also
remain outside the reflection target shapes. -/
theorem reflection_at_all_nonbot_nonprop_incompatible (C : CovTypingP E)
    (r : Nat) (us : List CptT)
    (hr : ∀ a, a ≠ .bot → ¬ IsPropCTP E a → C.ty (.spine r us) a) : False :=
  CptT.noConfusion (C.lam_inv
    (hr (.lam []) CptT.noConfusion (not_isPropCTP_lam E [])))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_TYPING_ROOTS
#print axioms NeutralHeadP
#print axioms neutralHeadP_rigid
#print axioms neutralHeadP_not_constructor
#print axioms RigidPiGateP
#print axioms CTyCovP2
#print axioms CTyCovP2.bot
#print axioms CTyCovP2.univProp
#print axioms CTyCovP2.univType
#print axioms CTyCovP2.lam
#print axioms CTyCovP2.rigidPi
#print axioms CTyCovP2.reflectedPi
#print axioms CTyCovP2.spine
#print axioms CovTypingP
#print axioms ctyCovP2_bot_inv
#print axioms ctyCovP2_prop_inv
#print axioms ctyCovP2_sort_inv
#print axioms ctyCovP2_lam_inv
#print axioms ctyCovP2_spine_iff
#print axioms ctyCovP2_pi_iff
#print axioms ctyCovP2_prop_bot
#print axioms C2P
#print axioms ctyCovP2_of_ctyCov2
#print axioms ctyCovP2_of_ctyS
#print axioms ctyCovP2_prop_iff
#print axioms ctyCovP2_sort_iff
#print axioms ctyCovP2_spine_iff_ctyCov2
#print axioms positive_prop_inv_incompatible
#print axioms reflection_at_all_nonprop_incompatible
#print axioms reflection_at_all_nonbot_nonprop_incompatible
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_TYPING_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
