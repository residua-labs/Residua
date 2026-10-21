import rcic.RcicNativeTypedModel

/-!
# Positive evidence that a compact denotes a proposition

`.prop` remains the code of the universe Prop. It is not a proposition code.
An empty Pi table, and a Pi whose outputs are only bottom, carry no positive
evidence. This finite predicate does not claim to detect all native terms of
sort Prop; in particular it is uninhabited over the empty declaration table.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit

inductive IsPropCTP (E : ResolvedEnv) : CptT → Prop
  | pi {a : CptT} {g : List (List CptT × CptT)}
      (ha : TyCodeCT a) (hne : g ≠ [])
      (hout : ∀ t ∈ g, IsPropCTP E t.2) : IsPropCTP E (.pi a g)
  | spine {r : Nat} {args : List CptT} {m : CheckedMember}
      (hres : E.members r = some m)
      (hsort : piBody m.mtype = .sort .zero) : IsPropCTP E (.spine r args)

theorem isPropCT_of_isPropCTP {E : ResolvedEnv} {c : CptT}
    (h : IsPropCTP E c) : IsPropCT E c := by
  induction h with
  | pi ha _ _ ih => exact .pi ha ih
  | spine hm hs => exact .spine hm hs

theorem not_isPropCTP_bot (E : ResolvedEnv) : ¬ IsPropCTP E .bot :=
  fun h => nomatch h

theorem not_isPropCTP_prop (E : ResolvedEnv) : ¬ IsPropCTP E .prop :=
  fun h => nomatch h

theorem not_isPropCTP_sort (E : ResolvedEnv) : ¬ IsPropCTP E .sort :=
  fun h => nomatch h

theorem not_isPropCTP_lam (E : ResolvedEnv) (g : List (List CptT × CptT)) :
    ¬ IsPropCTP E (.lam g) := fun h => nomatch h

theorem not_isPropCTP_pi_nil (E : ResolvedEnv) (a : CptT) :
    ¬ IsPropCTP E (.pi a []) := by
  intro h
  cases h with
  | pi _ hne _ => exact hne rfl

theorem not_isPropCTP_pi_bot_outputs (E : ResolvedEnv) (a : CptT)
    (g : List (List CptT × CptT))
    (hb : ∀ t ∈ g, t.2 = .bot) : ¬ IsPropCTP E (.pi a g) := by
  intro h
  cases h with
  | pi _ hne hout =>
      cases g with
      | nil => exact hne rfl
      | cons t ts =>
          have ht := hout t (List.mem_cons_self t ts)
          rw [hb t (List.mem_cons_self t ts)] at ht
          exact not_isPropCTP_bot E ht

theorem not_isPropCTP_emptyEnv {a : CptT} : ¬ IsPropCTP emptyEnv a := by
  intro h
  induction h with
  | @pi a g _ hne _ ih =>
      cases g with
      | nil => exact hne rfl
      | cons t ts => exact ih t (List.mem_cons_self t ts)
  | spine hm _ => cases hm

theorem isPropCTP_spine_iff {E : ResolvedEnv} {r : Nat} {args : List CptT} :
    IsPropCTP E (.spine r args) ↔ IsPropCT E (.spine r args) := by
  constructor
  · exact isPropCT_of_isPropCTP
  · intro h
    cases h with
    | spine hm hs => exact .spine hm hs

/-- Universe membership and positive proposition collapse cannot both use a
predicate which classifies the universe code `.prop` itself as a proposition. -/
theorem prop_universe_seed_incompatible
    (T : CptT → CptT → Prop) (P : CptT → Prop)
    (hp : P .prop) (collapse : ∀ {a u}, P a → T u a → u = .bot)
    {r : Nat} {args : List CptT} (ht : T (.spine r args) .prop) : False :=
  CptT.noConfusion (collapse hp ht)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_POSITIVE_ROOTS
#print axioms IsPropCTP
#print axioms isPropCT_of_isPropCTP
#print axioms not_isPropCTP_bot
#print axioms not_isPropCTP_prop
#print axioms not_isPropCTP_sort
#print axioms not_isPropCTP_lam
#print axioms not_isPropCTP_pi_nil
#print axioms not_isPropCTP_pi_bot_outputs
#print axioms not_isPropCTP_emptyEnv
#print axioms isPropCTP_spine_iff
#print axioms prop_universe_seed_incompatible
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_POSITIVE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
