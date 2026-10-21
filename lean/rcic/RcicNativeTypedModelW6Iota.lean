import rcic.RcicNativeTypedModelK
import rcic.RcicNativeTypedModelKFragment
import rcic.RcicNativeTypedModelIota
import rcic.RcicNativeTypedModelSubst
import rcic.RcicNativeTypedModelFundDelta
import rcic.RcicNativeTypedModelCovNormConvCases
import rcic.RcicNativeTypedModelCovNormSaturatedControl

/-!
# WALL 6 — ordinary iota at the saturated model (SWE-C)

The general saturated-computation supplier for ordinary (non-K, no
indexed-proposition recursion) inductives, ported against
`origin/chatgpt/approxtk-covnorm-20261020` (#7773, `26e23be4bb`).

The proof shape is the forward half of `approxDI_iotaS`
(`RcicNativePiModelDeltaIota`), re-ported at `ApproxT`/`EnvT`/`CptT`.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelW6IotaAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit

variable {E : ResolvedEnv} {ρ : EnvT}

/-! ### §1 — `EnvT.pushArgs` algebra -/

/-- `pushArgs` at or past the list length reads the tail environment. -/
theorem envT_pushArgs_ge (L : List (CptT → Prop)) (ρ : EnvT) {i : Nat}
    (h : L.length ≤ i) : EnvT.pushArgs L ρ i = ρ (i - L.length) := by
  induction L generalizing ρ i with
  | nil => simp only [List.length_nil, Nat.sub_zero]; rfl
  | cons S Ss ih =>
      simp only [EnvT.pushArgs, List.length_cons] at h ⊢
      rw [ih (EnvT.cons S ρ) (Nat.le_trans (Nat.le_succ Ss.length) h)]
      have hj : i - Ss.length = (i - (Ss.length + 1)) + 1 := by omega
      rw [hj]
      rfl

/-- `pushArgs` at an index below the list length is environment-independent. -/
theorem envT_pushArgs_lt_indep (L : List (CptT → Prop)) (ρ σ : EnvT) {i : Nat}
    (h : i < L.length) : EnvT.pushArgs L ρ i = EnvT.pushArgs L σ i := by
  induction L generalizing ρ σ i with
  | nil => cases h
  | cons S Ss ih =>
      simp only [EnvT.pushArgs, List.length_cons] at h ⊢
      by_cases hi : i < Ss.length
      · exact ih _ _ hi
      · have he : i = Ss.length := Nat.le_antisymm
          (Nat.le_of_lt_succ h) (Nat.le_of_not_lt hi)
        subst he
        rw [envT_pushArgs_ge Ss (EnvT.cons S ρ) (Nat.le_refl _),
          envT_pushArgs_ge Ss (EnvT.cons S σ) (Nat.le_refl _), Nat.sub_self]
        rfl

/-- Dropping past a pushed prefix recovers the tail environment. -/
theorem envT_drop_pushArgs (L : List (CptT → Prop)) (ρ : EnvT) :
    EnvT.drop (EnvT.pushArgs L ρ) L.length = ρ := by
  funext i
  simp only [EnvT.drop]
  rw [envT_pushArgs_ge L ρ (show L.length ≤ i + L.length by omega), Nat.add_sub_cancel]

/-- Inserting at the end of a pushed prefix is pushing one more frame. -/
theorem envT_insert_pushArgs_len (L : List (CptT → Prop)) (ρ : EnvT) (S : CptT → Prop) :
    EnvT.insert (EnvT.pushArgs L ρ) L.length S = EnvT.pushArgs L (EnvT.cons S ρ) := by
  funext i
  simp only [EnvT.insert]
  by_cases hlt : i < L.length
  · rw [if_pos hlt]
    exact envT_pushArgs_lt_indep L ρ (EnvT.cons S ρ) hlt
  · rw [if_neg hlt]
    by_cases heq : i = L.length
    · subst heq
      rw [if_pos rfl, envT_pushArgs_ge L (EnvT.cons S ρ) (Nat.le_refl _),
        Nat.sub_self]
      rfl
    · rw [if_neg heq]
      have hge : L.length < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
      rw [envT_pushArgs_ge L ρ (show L.length ≤ i - 1 by omega),
        envT_pushArgs_ge L (EnvT.cons S ρ) (Nat.le_of_lt hge)]
      have hs : i - L.length = (i - 1) - L.length + 1 := by omega
      rw [hs]
      rfl

/-- Updating an inserted slot is inserting the new content. -/
theorem envT_update_insert_self (ρ : EnvT) (j : Nat) (S T : CptT → Prop) :
    EnvT.update (EnvT.insert ρ j S) j T = EnvT.insert ρ j T := by
  funext i
  simp only [EnvT.update, EnvT.insert]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_neg (Nat.lt_irrefl _), if_pos rfl]
  · rw [if_neg h, if_neg h]
    by_cases hlt : i < j
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt, if_neg h]

/-! ### §2 — `instPrefix` demand characterisation -/

/-- T-side port of `approxDI_instPrefix_demand_iff`: `instPrefix`-reduct
    observations are exactly a finite demand on each argument plus a
    schema-body derivation in the pushed demand environment. -/
theorem approxT_instPrefix_demand_iff (E : ResolvedEnv) (ρ : EnvT)
    (args : List (Expr Nat)) (e : Expr Nat) (c : CptT) :
    ApproxT E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemandT E ρ args uss ∧
        ApproxT E (EnvT.pushArgs (uss.map demandT) ρ) e c := by
  induction args generalizing e with
  | nil =>
      simp only [instPrefix]
      constructor
      · intro h; exact ⟨[], .nil, h⟩
      · rintro ⟨uss, hargs, h⟩
        cases hargs
        exact h
  | cons a as ih =>
      simp only [instPrefix]
      rw [ih]
      constructor
      · rintro ⟨uss, has, hsub⟩
        have hlen : (uss.map demandT).length = as.length := by
          rw [List.length_map, has.length_eq]
        rw [← hlen, approxT_subst_iff] at hsub
        rw [envT_drop_pushArgs] at hsub
        obtain ⟨us, hus, hbody⟩ := approxT_factor hsub (uss.map demandT).length
        have hus' : ∀ u ∈ us, ApproxT E ρ a u := by
          intro u hu
          have hu' := hus u hu
          simp only [EnvT.insert, Nat.lt_irrefl, ite_false, ite_true] at hu'
          exact hu'
        refine ⟨us :: uss, .cons hus' has, ?_⟩
        rw [envT_update_insert_self, envT_insert_pushArgs_len] at hbody
        rw [List.map_cons]
        exact hbody
      · rintro ⟨uss, hargs, h⟩
        cases hargs with
        | cons ha has =>
            rename_i us uss
            refine ⟨uss, has, ?_⟩
            have hlen : (uss.map demandT).length = as.length := by
              rw [List.length_map, has.length_eq]
            rw [← hlen, approxT_subst_iff, envT_drop_pushArgs]
            have h' := h
            simp only [List.map_cons, EnvT.pushArgs] at h'
            rw [← envT_insert_pushArgs_len] at h'
            refine approxT_mono_env (fun i d hd => ?_) h'
            simp only [EnvT.insert] at hd ⊢
            by_cases hlt : i < (uss.map demandT).length
            · rw [if_pos hlt] at hd ⊢
              exact hd
            · rw [if_neg hlt] at hd ⊢
              by_cases heq : i = (uss.map demandT).length
              · subst heq
                rw [if_pos rfl] at hd ⊢
                exact ha d hd
              · rw [if_neg heq] at hd ⊢
                exact hd

/-- Closed-schema variant: the tail environment collapses to `EnvT.bot`
    when `e` is closed at the argument length. -/
theorem approxT_instPrefix_closed_iff (E : ResolvedEnv) (ρ : EnvT)
    (args : List (Expr Nat)) (e : Expr Nat) (hcl : exprClosedAt args.length e = true)
    (c : CptT) :
    ApproxT E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemandT E ρ args uss ∧
        ApproxT E (EnvT.pushArgs (uss.map demandT) EnvT.bot) e c := by
  rw [approxT_instPrefix_demand_iff]
  constructor
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demandT).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs, approxT_closedAt_env h hcl'
      (fun i hi => envT_pushArgs_lt_indep (uss.map demandT) _ EnvT.bot hi)⟩
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demandT).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs, approxT_closedAt_env h hcl'
      (fun i hi => envT_pushArgs_lt_indep (uss.map demandT) EnvT.bot ρ hi)⟩

/-! ### §3 — spine-fold and rigid-const spines -/

/-- Pointwise `ApproxT` pairing of an argument spine with a compact list
    (heterogeneous replacement for `List.Forall₂`, which is homogeneous). -/
inductive ApproxArgsT (E : ResolvedEnv) (ρ : EnvT) :
    List (Expr Nat) → List CptT → Prop
  | nil : ApproxArgsT E ρ [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {u : CptT} {us : List CptT}
      (hx : ApproxT E ρ x u) (hxs : ApproxArgsT E ρ xs us) :
      ApproxArgsT E ρ (x :: xs) (u :: us)

theorem ApproxArgsT.length_eq {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs : List (Expr Nat)} {us : List CptT}, ApproxArgsT E ρ xs us →
      xs.length = us.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [ApproxArgsT.length_eq h]

theorem ApproxArgsT.append_inv {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs ys : List (Expr Nat)} {us vs : List CptT},
      xs.length = us.length → ApproxArgsT E ρ (xs ++ ys) (us ++ vs) →
      ApproxArgsT E ρ ys vs
  | [], _, [], _, _, h => h
  | _ :: xs, _, _ :: us, _, hlen, .cons _ h =>
      ApproxArgsT.append_inv (Nat.succ.inj hlen) h
  | _ :: _, _, [], _, hlen, _ => by cases hlen

/-- Element extraction from `ApproxArgsT` (explicit defaults; no
    `Inhabited` requirement). -/
theorem ApproxArgsT.getD {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs : List (Expr Nat)} {us : List CptT},
      ApproxArgsT E ρ xs us → ∀ (k : Nat), k < xs.length →
        ∀ d, ApproxT E ρ (xs.getD k d) (us.getD k .bot)
  | _, _, .cons hx _, 0, _, _ => hx
  | _, _, .cons _ hxs, k + 1, hk, d =>
      ApproxArgsT.getD hxs k (Nat.lt_of_succ_lt_succ hk) d
  | _, _, .nil, _, hk, _ => by cases hk

/-- Spine-fold inversion: applying a `.spine` compact across an argument
    spine grows the compact argument list pointwise. -/
theorem foldAppCptT_spine_iff {E : ResolvedEnv} {ρ : EnvT} {r : Nat}
    {args₀ : List CptT} {xs : List (Expr Nat)} {c : CptT} :
    FoldAppCptT E ρ (.spine r args₀) xs c ↔
      c = .bot ∨ ∃ us : List CptT,
        ApproxArgsT E ρ xs us ∧ c = .spine r (args₀ ++ us) := by
  induction xs generalizing args₀ c with
  | nil =>
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | nil => exact Or.inr ⟨[], .nil, congrArg _ (List.append_nil args₀).symm⟩
      · rintro (rfl | ⟨us, hf, rfl⟩)
        · exact .bot _ _
        · cases hf
          rw [List.append_nil]
          exact .nil _
  | cons x xs ih =>
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | cons hstep hrest =>
            cases hstep with
            | bot => exact Or.inl (foldAppCptT_bot_inv hrest)
            | appSpine hx =>
                rename_i u
                rcases ih.mp hrest with rfl | ⟨us, hf, rfl⟩
                · exact Or.inl rfl
                · have hEq : (args₀ ++ [u]) ++ us = args₀ ++ u :: us :=
                    List.append_assoc args₀ [u] us
                  exact Or.inr ⟨u :: us, .cons hx hf, congrArg _ hEq⟩
      · rintro (rfl | ⟨us, hf, rfl⟩)
        · exact .bot _ _
        · cases hf with
          | cons hx hxs =>
              rename_i u us'
              have hEq : (args₀ ++ [u]) ++ us' = args₀ ++ u :: us' :=
                List.append_assoc args₀ [u] us'
              rw [← hEq]
              exact .cons (.appSpine hx) (ih.mpr (Or.inr ⟨us', hxs, rfl⟩))

/-- T-side port of `approxDI_foldApps_rigid_iff`: a rigid, non-prop-ctor
    constant's application spine denotes only `⊥` or a grown `.spine`. -/
theorem approxT_foldApps_rigid_iff {E : ResolvedEnv} {ρ : EnvT} {r : Nat}
    {ls : List Level} (hr : RigidConst E r) (hnp : ¬ PropCtorT E r)
    (xs : List (Expr Nat)) (c : CptT) :
    ApproxT E ρ (foldApps (.const r ls) xs) c ↔
      c = .bot ∨ ∃ us : List CptT,
        ApproxArgsT E ρ xs us ∧ c = .spine r us := by
  rw [approxT_foldApps_iff]
  constructor
  · rintro ⟨d, hd, hfold⟩
    rcases approxT_const_inv hd with rfl | ⟨_, _, rfl⟩ | ⟨m, b, hdd, _⟩ |
      ⟨w, _, _, _, hw, _, _, _, _, _⟩ | ⟨w, _, _, hw, _, _, _, _⟩
    · exact Or.inl (foldAppCptT_bot_inv hfold)
    · rcases (foldAppCptT_spine_iff).mp hfold with rfl | ⟨us, hf, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨us, hf, rfl⟩
    · exact (not_rigidConst_of_deltaConst hdd hr).elim
    · exact ((hw ▸ recRef_not_rigid w) hr).elim
    · exact ((hw ▸ recRef_not_rigid w) hr).elim
  · rintro (rfl | ⟨us, hf, rfl⟩)
    · exact ⟨.bot, .bot _ _, .bot _ _⟩
    · exact ⟨.spine r [], .const ρ r ls hr hnp,
        (foldAppCptT_spine_iff).mpr (Or.inr ⟨us, hf, rfl⟩)⟩

/-! ### §4 — constructor-demand inversion -/

/-- `piBody` of a fully-peeled telescope is the peel result. -/
theorem piBody_eq_of_peelPis_piCount (T : Expr Nat) :
    ∀ {ds : List (Expr Nat)} {r : Expr Nat},
      peelPis (piCount T) T = some (ds, r) → piBody T = r := by
  induction T with
  | pi A B ihA ihB =>
      intro ds r h
      simp only [piCount, peelPis] at h
      cases hpeel : peelPis (piCount B) B with
      | none => rw [hpeel] at h; exact Option.noConfusion h
      | some pr =>
          rw [hpeel] at h
          obtain ⟨ds', r'⟩ := pr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihB hpeel
  | _ =>
      intro ds r h
      simp only [piCount, peelPis, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2

/-- `headConst` reads the spine head. -/
theorem headConst_eq_fst : ∀ (e : Expr Nat),
    headConst e = (match (appsSpine e).1 with | .const r _ => some r | _ => none)
  | .app f x => by
      have ih := headConst_eq_fst f
      simp only [appsSpine]
      exact ih
  | .const r ls => rfl
  | .bvar i => rfl
  | .sort l => rfl
  | .lam A B => rfl
  | .pi A B => rfl
  | .letE A B C => rfl
  | .lit n => rfl

/-- A proposition-family constructor is a prop-ctor: the `PropCtorT` premise
    of the strict-recursor clause reduces to `PropFamilyS`. -/
theorem propCtorT_imp_propFamilyS {E : ResolvedEnv} (w : IotaWitnessS E) :
    PropCtorT E w.ctorRef → PropFamilyS w := by
  rintro ⟨m, fam, fm, hm, hk, hh, hfm, hsort⟩
  have hm' : m = w.ctorMember := Option.some.inj (hm.symm.trans w.hctor)
  subst hm'
  have hpb : piBody w.ctorMember.mtype = w.ctorResult := by
    have h := w.hpeel
    rw [w.hnpar] at h
    exact piBody_eq_of_peelPis_piCount _ h
  rw [hpb, headConst_eq_fst] at hh
  have hfA := w.hfamApp
  unfold isFamilyApp at hfA
  split at hfA
  · rename_i r ls' args heq
    rw [heq] at hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfA
    have hfam : fam = w.familyRef :=
      (Option.some.inj hh).symm.trans hfA.1
    rw [hfam] at hfm
    have hfm' : fm = w.famMember := Option.some.inj (hfm.symm.trans w.hfam)
    subst hfm'
    exact hsort
  · cases hfA

/-- Pointwise `ApproxT` across appended spines. -/
theorem ApproxArgsT.append {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs ys : List (Expr Nat)} {us vs : List CptT},
      ApproxArgsT E ρ xs us → ApproxArgsT E ρ ys vs →
      ApproxArgsT E ρ (xs ++ ys) (us ++ vs)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hxs, h => .cons hx (ApproxArgsT.append hxs h)

/-- All-`⊥` compact vectors approximate any argument list. -/
theorem ApproxArgsT.replicate_bot {E : ResolvedEnv} (ρ : EnvT) :
    ∀ (xs : List (Expr Nat)),
      ApproxArgsT E ρ xs (List.replicate xs.length .bot)
  | [] => .nil
  | x :: xs => .cons (.bot ρ x) (ApproxArgsT.replicate_bot ρ xs)

/-- Demand-list analogue of `ApproxArgsT.append`. -/
theorem ApproxArgsDemandT.append {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs ys : List (Expr Nat)} {uss vss : List (List CptT)},
      ApproxArgsDemandT E ρ xs uss → ApproxArgsDemandT E ρ ys vss →
      ApproxArgsDemandT E ρ (xs ++ ys) (uss ++ vss)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hxs, h => .cons hx (ApproxArgsDemandT.append hxs h)

/-- Splitting a demand spine at a prefix boundary. -/
theorem ApproxArgsDemandT.append_inv {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {xs ys : List (Expr Nat)} {uss vss : List (List CptT)},
      xs.length = uss.length →
      ApproxArgsDemandT E ρ (xs ++ ys) (uss ++ vss) →
      ApproxArgsDemandT E ρ xs uss ∧ ApproxArgsDemandT E ρ ys vss
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | _ :: _, _, _ :: _, _, hlen, .cons hx hxs =>
      have ⟨h1, h2⟩ := ApproxArgsDemandT.append_inv (Nat.succ.inj hlen) hxs
      ⟨.cons hx h1, h2⟩
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _ => by cases hlen

/-- A field-demand vector realized pointwise from `ApproxArgsDemandT`. -/
theorem approxArgsT_of_fdvt_mem {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {fields : List (Expr Nat)} {us_fields : List (List CptT)} {vec : List CptT},
      ApproxArgsDemandT E ρ fields us_fields →
      vec ∈ fieldDemandVectorsT us_fields → ApproxArgsT E ρ fields vec
  | _, _, _, .nil, h => (List.not_mem_nil _ h).elim
  | f :: rest, us :: uss, vec, .cons ha has, hvec => by
      simp only [fieldDemandVectorsT, List.mem_append, List.mem_map] at hvec
      rcases hvec with ⟨u, hu, rfl⟩ | ⟨v', hv', rfl⟩
      · have hle : rest.length = uss.length := (has.length_eq).symm
        rw [← hle]
        exact .cons (ha u hu) (ApproxArgsT.replicate_bot ρ rest)
      · exact .cons (.bot ρ f) (approxArgsT_of_fdvt_mem has hv')
  | [], _ :: _, _, h, _ => by cases h.length_eq
  | _ :: _, [], _, h, _ => by cases h.length_eq

/-- `fieldDemandVectorsT` members realize each field's own demand list:
    the typed `ctorDemandT` inverse's pointwise core. -/
theorem approxArgsDemandT_of_fdvt {E : ResolvedEnv} {ρ : EnvT} :
    ∀ {fields : List (Expr Nat)} {us_fields : List (List CptT)},
      fields.length = us_fields.length →
      (∀ vec ∈ fieldDemandVectorsT us_fields, ApproxArgsT E ρ fields vec) →
      ApproxArgsDemandT E ρ fields us_fields
  | [], [], _, _ => .nil
  | f :: rest, us :: uss, hlen, hvec =>
      .cons
        (fun u hu => by
          have hmem : u :: List.replicate uss.length .bot ∈
              fieldDemandVectorsT (us :: uss) :=
            List.mem_append.mpr (Or.inl
              (List.mem_map.mpr ⟨u, hu, rfl⟩))
          have h := hvec _ hmem
          cases h with
          | cons hx _ => exact hx)
        (approxArgsDemandT_of_fdvt (Nat.succ.inj hlen) (fun v' hv' => by
          have hmem : .bot :: v' ∈ fieldDemandVectorsT (us :: uss) :=
            List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨v', hv', rfl⟩))
          have h := hvec _ hmem
          cases h with
          | cons _ hxs => exact hxs))
  | [], _ :: _, hlen, _ => by cases hlen
  | _ :: _, [], hlen, _ => by cases hlen

/-- Typed `ctorDemandT` inverse: a constructor major premise realizing every
    constructor-major demand yields `ApproxArgsDemandT` for the fields. -/
theorem ctorDemandT_inv {E : ResolvedEnv} {ρ : EnvT} {ctorRef : Nat}
    {ls : List Level} {params fields : List (Expr Nat)} {nparams : Nat}
    {us_fields : List (List CptT)}
    (hr : RigidConst E ctorRef) (hnp : ¬ PropCtorT E ctorRef)
    (hpar : params.length = nparams) (hflen : fields.length = us_fields.length)
    (hdem : ∀ c ∈ ctorDemandT ctorRef nparams us_fields,
        ApproxT E ρ (foldApps (.const ctorRef ls) (params ++ fields)) c) :
    ApproxArgsDemandT E ρ fields us_fields := by
  refine approxArgsDemandT_of_fdvt hflen (fun vec hvec => ?_)
  have hmem : .spine ctorRef (List.replicate nparams .bot ++ vec) ∈
      ctorDemandT ctorRef nparams us_fields :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vec, hvec, rfl⟩)
  rcases (approxT_foldApps_rigid_iff hr hnp _ _).mp (hdem _ hmem) with hbot |
    ⟨us₁, hA, hsp⟩
  · exact CptT.noConfusion hbot
  · have hlen : params.length = (List.replicate nparams (.bot : CptT)).length := by
      rw [hpar, List.length_replicate]
    cases hsp
    exact ApproxArgsT.append_inv hlen hA

/-- `fieldDemandVectorsT` members realized pointwise: the `ctorDemandT` intro. -/
theorem ctorDemandT_intro {E : ResolvedEnv} {ρ : EnvT} {ctorRef : Nat}
    {ls : List Level} {params fields : List (Expr Nat)} {nparams : Nat}
    {us_fields : List (List CptT)}
    (hr : RigidConst E ctorRef) (hnp : ¬ PropCtorT E ctorRef)
    (hpar : params.length = nparams)
    (hA : ApproxArgsDemandT E ρ fields us_fields) :
    ∀ c ∈ ctorDemandT ctorRef nparams us_fields,
        ApproxT E ρ (foldApps (.const ctorRef ls) (params ++ fields)) c := by
  intro c hc
  simp only [ctorDemandT, List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | ⟨vec, hvec, rfl⟩
  · exact (approxT_foldApps_rigid_iff hr hnp _ _).mpr (Or.inr
      ⟨_, ApproxArgsT.append
        (by rw [← hpar]; exact ApproxArgsT.replicate_bot ρ params)
        (by rw [hA.length_eq]; exact ApproxArgsT.replicate_bot ρ fields), rfl⟩)
  · exact (approxT_foldApps_rigid_iff hr hnp _ _).mpr (Or.inr
      ⟨_, ApproxArgsT.append
        (by rw [← hpar]; exact ApproxArgsT.replicate_bot ρ params)
        (approxArgsT_of_fdvt_mem hA hvec), rfl⟩)

/-! ### §5 — the ordinary-iota step -/

/-- `headConst` is invariant under `foldApps` spines. -/
theorem headConst_foldApps {f : Expr Nat} : ∀ (xs : List (Expr Nat)),
    headConst (foldApps f xs) = headConst f
  | [] => rfl
  | _ :: xs => headConst_foldApps xs

/-- `PropFamilyS` transports along `recRef`-equality: the family reference is
    pinned inside the (shared) recursor member's major-premise type, so two
    witnesses at the same recursor share `famMember`. -/
theorem familyRef_eq_of_recRef_eq {E : ResolvedEnv} {w' w : IotaWitnessS E}
    (hrec : w'.recRef = w.recRef) : w'.familyRef = w.familyRef := by
  obtain ⟨hmemr, _⟩ := iotaWitnessS_preMajor_length_eq w' w hrec
  have hpeel' := w'.hpeelRec
  have hpeel := w.hpeelRec
  rw [w'.hnmin] at hpeel'
  rw [w.hnmin, ← hmemr] at hpeel
  have hrecDoms : w'.recDoms = w.recDoms :=
    congrArg Prod.fst (Option.some.inj (hpeel'.symm.trans hpeel))
  have hidx : w'.nparams + 1 + w'.nMinors + w'.nindices =
      w.nparams + 1 + w.nMinors + w.nindices := by
    have a := w'.hnmin
    have b := w.hnmin
    rw [← hmemr] at b
    omega
  have hmaj := w'.hmajorTy
  rw [hidx, hrecDoms] at hmaj
  have h := Option.some.inj (hmaj.symm.trans w.hmajorTy)
  have hc := congrArg headConst h
  simp only [headConst_foldApps] at hc
  exact Option.some.inj hc

theorem famMember_eq_of_recRef_eq {E : ResolvedEnv} {w' w : IotaWitnessS E}
    (hrec : w'.recRef = w.recRef) : w'.famMember = w.famMember := by
  have hf := familyRef_eq_of_recRef_eq hrec
  have a := w'.hfam
  have b := w.hfam
  rw [hf] at a
  exact Option.some.inj (a.symm.trans b)

theorem nMinors_eq_of_recRef_eq {E : ResolvedEnv} {w' w : IotaWitnessS E}
    (hrec : w'.recRef = w.recRef) : w'.nMinors = w.nMinors := by
  have hf := familyRef_eq_of_recRef_eq hrec
  have a := w'.hrecIdx
  have b := w.hrecIdx
  rw [hf] at a
  omega

theorem propFamilyS_of_recRef_eq {E : ResolvedEnv} {w' w : IotaWitnessS E}
    (hrec : w'.recRef = w.recRef) (hP : PropFamilyS w') : PropFamilyS w := by
  have hmemf := famMember_eq_of_recRef_eq hrec
  unfold PropFamilyS
  rw [← hmemf]
  exact hP

theorem propFamilyS_iff_recRef_eq {E : ResolvedEnv} {w' w : IotaWitnessS E}
    (hrec : w'.recRef = w.recRef) : PropFamilyS w' ↔ PropFamilyS w := by
  have hmemf := famMember_eq_of_recRef_eq hrec
  unfold PropFamilyS
  rw [hmemf]

/-- The typed-model ordinary-iota step: under a strict (non-`Prop`) family,
    the iota redex and contractum carry the same compacts.  This is the
    `ApproxT` port of `approxDI_iotaS`; the `Prop`-family arm of the constant
    inversion is eliminated by `propFamilyS_of_recRef_eq`, matching the
    `recursorProp` clause's demand-erasure which makes the backward direction
    fail at proposition families (cf. `not_iotaSoundT_ex`). -/
theorem approxT_iotaS {E : ResolvedEnv} (w : IotaWitnessS E)
    (hnP : ¬ PropFamilyS w) (ρ : EnvT) (c : CptT) :
    ApproxT E ρ (iotaLhsOfS w) c ↔ ApproxT E ρ (iotaRhsOfS w) c := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  have hrigidCtor : RigidConst E w.ctorRef := rigidConst_of_ctor w.hctor w.hctorK
  have hnpCtor : ¬ PropCtorT E w.ctorRef :=
    fun h => hnP (propCtorT_imp_propFamilyS w h)
  have hnr : ¬ RigidConst E w.recRef := not_rigidConst_of_recursor w
  constructor
  · intro h
    unfold iotaLhsOfS recCall at h
    rw [approxT_foldApps_iff] at h
    obtain ⟨d, hd, hfold⟩ := h
    rcases approxT_const_inv hd with rfl | ⟨hr, -, -⟩ | ⟨m, b, hd', -⟩ |
        ⟨w', us_pre, us_fields, c₀, hrecEq, hnp', hpreLen, hfldsLen, hschema', rfl⟩ |
        ⟨w', us_pre, c₀, hrecEq, hP', hpreLen, hschema', rfl⟩
    · rw [foldAppCptT_bot_inv hfold]
      exact .bot ρ (iotaRhsOfS w)
    · exact absurd hr hnr
    · exact absurd hd' (not_deltaConst_of_recursor w)
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [ctorDemandT w'.ctorRef w'.nparams us_fields]).length =
          (w.preMajor ++
            [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptT_curryStepT_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨hpreArgs, hmajArgs⟩ := ApproxArgsDemandT.append_inv
          (by rw [hpreLen, hpreLenEq]) hargs
        cases hmajArgs with
        | cons hmaj _ =>
          have hhead : .spine w'.ctorRef (List.replicate w'.nparams .bot ++
              List.replicate us_fields.length .bot) ∈
              ctorDemandT w'.ctorRef w'.nparams us_fields := List.mem_cons_self _ _
          rcases (approxT_foldApps_rigid_iff hrigidCtor hnpCtor _ _).mp (hmaj _ hhead)
            with hbot | ⟨us₁, hA, hsp⟩
          · exact CptT.noConfusion hbot
          · injection hsp with hctorEq _
            obtain ⟨hnparEq, _, _, _, _, hfldsLenEq, _, hschemaEq⟩ :=
              iotaWitnessS_same_branch w' w hrecEq hctorEq
            have hmaj' := hmaj
            rw [← hctorEq] at hmaj'
            have hfldsArgs : ApproxArgsDemandT E ρ w.fields us_fields :=
              ctorDemandT_inv (rigidConst_of_ctor w'.hctor w'.hctorK)
                (fun h => hnp' (propCtorT_imp_propFamilyS w' h))
                (w.hctorParams.trans hnparEq.symm)
                (hfldsLenEq.symm.trans hfldsLen.symm) hmaj'
            rw [hschemaEq] at hschema'
            unfold iotaRhsOfS
            rw [approxT_instPrefix_closed_iff _ _ _ _ hclSchema]
            exact ⟨us_pre ++ us_fields,
              ApproxArgsDemandT.append hpreArgs hfldsArgs, hschema'⟩
    · exact absurd (propFamilyS_of_recRef_eq hrecEq hP') hnP
  · intro h
    unfold iotaRhsOfS at h
    rw [approxT_instPrefix_closed_iff _ _ _ _ hclSchema] at h
    obtain ⟨uss, hargs, hschema⟩ := h
    have hsplit : uss = List.take w.preMajor.length uss ++
        List.drop w.preMajor.length uss := (List.take_append_drop _ _).symm
    have hlt : (List.take w.preMajor.length uss).length = w.preMajor.length := by
      rw [List.length_take, hargs.length_eq, List.length_append]; omega
    rw [hsplit] at hargs
    obtain ⟨hpreArgs, hfldsArgs⟩ := ApproxArgsDemandT.append_inv hlt.symm hargs
    rw [hsplit] at hschema
    have hrecHead : ApproxT E ρ (.const w.recRef w.ls)
        (curryStepT (List.take w.preMajor.length uss ++
          [ctorDemandT w.ctorRef w.nparams (List.drop w.preMajor.length uss)]) c) :=
      .recursor w.ls hnP hpreArgs.length_eq hfldsArgs.length_eq hschema
    have hmaj : ∀ v ∈ ctorDemandT w.ctorRef w.nparams
        (List.drop w.preMajor.length uss),
        ApproxT E ρ (foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)) v :=
      ctorDemandT_intro hrigidCtor hnpCtor w.hctorParams hfldsArgs
    have htotArgs : ApproxArgsDemandT E ρ
        (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)])
        (List.take w.preMajor.length uss ++
          [ctorDemandT w.ctorRef w.nparams (List.drop w.preMajor.length uss)]) :=
      ApproxArgsDemandT.append hpreArgs (.cons hmaj .nil)
    unfold iotaLhsOfS recCall
    rw [approxT_foldApps_iff]
    exact ⟨_, hrecHead,
      (foldAppCptT_curryStepT_iff (by
        simp only [List.length_append, List.length_singleton, hlt])).mpr
        (Or.inr ⟨htotArgs, rfl⟩)⟩

#print axioms envT_pushArgs_ge
#print axioms envT_drop_pushArgs
#print axioms envT_insert_pushArgs_len
#print axioms envT_update_insert_self
#print axioms approxT_instPrefix_demand_iff
#print axioms approxT_instPrefix_closed_iff
#print axioms foldAppCptT_spine_iff
#print axioms approxT_foldApps_rigid_iff
#print axioms propCtorT_imp_propFamilyS
#print axioms ctorDemandT_inv
#print axioms ctorDemandT_intro
/-- Vacuous demands satisfy every field list: `fields` realized at
    `fields.map (fun _ => [])`, the `recursorProp` clause's erased demand. -/
theorem approxArgsDemandT_nil_fields {E : ResolvedEnv} {ρ : EnvT} :
    ∀ (fields : List (Expr Nat)),
      ApproxArgsDemandT E ρ fields (fields.map (fun _ => []))
  | [] => .nil
  | _ :: rest =>
      .cons (fun _ hu => absurd hu (List.not_mem_nil _))
        (approxArgsDemandT_nil_fields rest)

/-- Forward preservation at an unindexed single-ctor proposition family:
    the `recursorProp` clause's erased field demands are exactly the
    contractum's vacuous `map (fun _ => [])` demands, and `nMinors = 1`
    forces every prop-witness at the same recursor to share `w`'s
    constructor (hence schema). -/
theorem approxT_iotaS_fwd_prop {E : ResolvedEnv} (w : IotaWitnessS E)
    (hP : PropFamilyS w) (hn1 : w.nMinors = 1) (ρ : EnvT) {c : CptT}
    (h : ApproxT E ρ (iotaLhsOfS w) c) : ApproxT E ρ (iotaRhsOfS w) c := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  unfold iotaLhsOfS recCall at h
  rw [approxT_foldApps_iff] at h
  obtain ⟨d, hd, hfold⟩ := h
  rcases approxT_const_inv hd with rfl | ⟨hr, -, -⟩ | ⟨m, b, hd', -⟩ |
      ⟨w', us_pre, us_fields, c₀, hrecEq, hnp', hpreLen, hfldsLen, hschema', rfl⟩ |
      ⟨w', us_pre, c₀, hrecEq, hP', hpreLen, hschema', rfl⟩
  · rw [foldAppCptT_bot_inv hfold]
    exact .bot ρ (iotaRhsOfS w)
  · exact absurd hr (not_rigidConst_of_recursor w)
  · exact absurd hd' (not_deltaConst_of_recursor w)
  · exact absurd ((propFamilyS_iff_recRef_eq hrecEq).mpr hP) hnp'
  · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
    have htotLen : (us_pre ++ [[]]).length =
        (w.preMajor ++
          [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]).length := by
      simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
    rcases (foldAppCptT_curryStepT_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
    · exact .bot ρ (iotaRhsOfS w)
    · obtain ⟨hpreArgs, -⟩ := ApproxArgsDemandT.append_inv
        (by rw [hpreLen, hpreLenEq]) hargs
      have hctorEq : w'.ctorRef = w.ctorRef := by
        have hf := familyRef_eq_of_recRef_eq hrecEq
        have hn := nMinors_eq_of_recRef_eq hrecEq
        have a := w'.hctorIdx
        have b := w.hctorIdx
        have h₁ := w'.hidx
        have h₂ := w.hidx
        rw [hn, hn1] at h₁
        rw [hn1] at h₂
        omega
      obtain ⟨_, _, _, _, _, hfldsLenEq, _, hschemaEq⟩ :=
        iotaWitnessS_same_branch w' w hrecEq hctorEq
      have hmap : w'.fields.map (fun _ => ([] : List CptT)) =
          w.fields.map (fun _ => []) := by
        have e : ∀ (l : List (Expr Nat)),
            l.map (fun _ => ([] : List CptT)) = List.replicate l.length [] := by
          intro l; induction l with
          | nil => rfl
          | cons x xs ih =>
              show _ :: _ = _; rw [ih]; rfl
        rw [e, e, hfldsLenEq]
      rw [hschemaEq, hmap] at hschema'
      unfold iotaRhsOfS
      rw [approxT_instPrefix_closed_iff _ _ _ _ hclSchema]
      exact ⟨us_pre ++ w.fields.map (fun _ => []),
        ApproxArgsDemandT.append hpreArgs
          (approxArgsDemandT_nil_fields _), hschema'⟩

/-- Forward preservation for the ordinary (non-indexed-`Prop`) iota step:
    strict families by `approxT_iotaS`, single-ctor proposition families by
    `approxT_iotaS_fwd_prop`.  Multi-ctor unindexed proposition families
    (`Or`-like) are a genuine residual: a `w'` at a different `ctorIdx` can
    realize a `recursorProp` compact whose schema `w'` does not share. -/
theorem approxT_iotaS_fwd {E : ResolvedEnv} (w : IotaWitnessS E)
    (hw : ¬ PropFamilyS w ∨ w.nMinors = 1) (ρ : EnvT) (c : CptT)
    (h : ApproxT E ρ (iotaLhsOfS w) c) : ApproxT E ρ (iotaRhsOfS w) c := by
  cases hw with
  | inl hnP => exact (approxT_iotaS w hnP ρ c).mp h
  | inr hn1 =>
      have hPem : PropFamilyS w ∨ ¬ PropFamilyS w := by
        unfold PropFamilyS; exact Decidable.em _
      rcases hPem with hP | hnP
      · exact approxT_iotaS_fwd_prop w hP hn1 ρ h
      · exact (approxT_iotaS w hnP ρ c).mp h

/-- The `ApproxTK` lift: under no indexed proposition recursors the
    K-annotated model agrees with `ApproxT`, so ordinary-iota forward
    preservation transports. -/
theorem approxTK_iotaS_fwd {E : ResolvedEnv} (w : IotaWitnessS E)
    (hE : ∀ r, ¬ IndexedPropRecT E r)
    (hw : ¬ PropFamilyS w ∨ w.nMinors = 1)
    {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK E n Γ ρ (iotaLhsOfS w) c) :
    ApproxTK E n Γ ρ (iotaRhsOfS w) c := by
  have hfwd := approxT_iotaS_fwd w hw ρ c (approxTK_forget h)
  have hk := kFreeT_of_no_indexed hE (iotaRhsOfS w)
  exact .free hk hfwd

#print axioms propFamilyS_of_recRef_eq
#print axioms approxT_iotaS
#print axioms approxT_iotaS_fwd_prop
#print axioms approxT_iotaS_fwd
#print axioms approxTK_iotaS_fwd

end Rcic.Declarative.NativeValleys.TypedModelW6IotaAudit
