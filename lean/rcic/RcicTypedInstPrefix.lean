import rcic.RcicTypedSubst
import rcic.RcicParRedSRTyped
import rcic.RcicTypedEnvEntry

/-!
# DT-019 package A — the typed `instPrefix` theorem

`instPrefix` (`RcicDeclarative.lean:3041`) instantiates an expression under
exactly `args.length` outer binders, consuming the telescope
outermost-first:

```
instPrefix [] e = e
instPrefix (a :: as) e = instPrefix as (instantiate |as| (lift 0 |as| a) e)
```

Each step is one `hasTyT_substS` application at `j = |as|` over an
all-`assumption` telescope: removing `bvar |as|` deletes the outermost
domain and `substRemove` instantiates the stored types of the remaining
inner domains at the matching cutoff — exactly what `telSubstLast`
computes pointwise. The replacement typing `lift 0 |as| a : lift 0 |as| D`
in the substituted context is `hasTyTLiftPrefix` of the arg's typing in
`Γ`.

* `outerDom` / `telSubstLast` / `substRemove_tel_assumption`: index
  machinery — the `i`-th outermost domain, and the context after one
  outermost removal, in `map .assumption` form.
* `hasTyT_instPrefix` (structure core): domains `ΔT` stored as
  `.assumption`s over `Γ`, `e : T` in `ΔT.map .assumption ++ Γ`, and each
  `args[i]` typed in `Γ` at `instPrefix (args.take i) (outerDom ΔT i)`
  (the `i`-th outermost domain, its inner binders instantiated) give
  `instPrefix args e : instPrefix args T` in `Γ`.
* `hasTyT_instPrefix_of_envWfT`: the `EnvWfT`-fronted wrapper.

No row premises, no annotation; judgments Type-valued. `closure_claim` 0.
-/

namespace Rcic.Declarative

/-- the `i`-th outermost telescope domain: `ΔT[|ΔT|-1-i]`, defaulted
    out-of-range so the statement is total. -/
def outerDom (ΔT : List (Expr Nat)) (i : Nat) : Expr Nat :=
  ΔT.getD (ΔT.length - 1 - i) (.bvar 0)

theorem outerDom_eq_getElem (ΔT : List (Expr Nat)) (i : Nat)
    (hi : i < ΔT.length) :
    outerDom ΔT i = ΔT[ΔT.length - 1 - i]'(by omega) := by
  simp only [outerDom, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : ΔT.length - 1 - i < ΔT.length),
    Option.getD_some]

/-- the telescope left after `substRemove` removes the outermost domain:
    each remaining domain's stored type is instantiated at the removed
    binder's offset from it. Pointwise `instDecl`. -/
def telSubstLast (v : Expr Nat) : List (Expr Nat) → List (Expr Nat)
  | [] => []
  | D :: ΔT =>
      instantiate ΔT.length (lift 0 ΔT.length v) D :: telSubstLast v ΔT

theorem telSubstLast_length (v : Expr Nat) (ΔT : List (Expr Nat)) :
    (telSubstLast v ΔT).length = ΔT.length := by
  induction ΔT with
  | nil => rfl
  | cons D ΔT ih => simp only [telSubstLast, List.length_cons, ih]

/-- index-transport for `getElem`: two lookups at equal indices are equal
    (the bound proofs are proof-irrelevant). -/
theorem getElem_idx_congr {α : Type _} {l : List α} {i j : Nat}
    (h : i = j) (hi : i < l.length) (hj : j < l.length) :
    l[i]'hi = l[j]'hj := by
  subst h; rfl

theorem telSubstLast_getElem (v : Expr Nat) :
    (ΔT : List (Expr Nat)) → (i : Nat) → (hi : i < ΔT.length) →
      (telSubstLast v ΔT)[i]'(by rw [telSubstLast_length]; exact hi) =
        instantiate (ΔT.length - 1 - i) (lift 0 (ΔT.length - 1 - i) v)
          ΔT[i]
  | [], _, hi => absurd hi (by simp)
  | D :: ΔT, 0, _ => by
      simp only [telSubstLast, List.length_cons, List.getElem_cons_zero,
        Nat.sub_zero, Nat.add_sub_cancel]
  | D :: ΔT, i + 1, hi => by
      simp only [telSubstLast, List.length_cons, List.getElem_cons_succ]
      have := telSubstLast_getElem v ΔT i (Nat.lt_of_succ_lt_succ hi)
      rwa [show ΔT.length + 1 - 1 - (i + 1) = ΔT.length - 1 - i by omega]

/-- removing the outermost domain of an assumption telescope and
    substituting into the remaining stored types produces `telSubstLast`:
    `substRemove` at `|ΔT|` instantiates each inner domain at its own
    offset. -/
theorem substRemove_tel_assumption (v : Expr Nat) :
    (ΔT : List (Expr Nat)) → (D : Expr Nat) → (Γ : LCtx) →
      substRemove v ΔT.length
          (ΔT.map LocalDecl.assumption ++ .assumption D :: Γ) =
        (telSubstLast v ΔT).map LocalDecl.assumption ++ Γ
  | [], _, _ => by
      simp only [List.map_nil, List.nil_append, List.length_nil,
        substRemove_zero_cons, telSubstLast]
  | D₀ :: ΔT, D, Γ => by
      simp only [List.map_cons, List.cons_append, List.length_cons,
        substRemove_succ_cons, instDecl, telSubstLast]
      rw [substRemove_tel_assumption v ΔT D Γ]

/-- `getElem?`-form of `telSubstLast_getElem`. -/
theorem telSubstLast_getElem? (v : Expr Nat) (ΔT : List (Expr Nat)) (i : Nat)
    (hi : i < ΔT.length) :
    (telSubstLast v ΔT)[i]? =
      some (instantiate (ΔT.length - 1 - i)
        (lift 0 (ΔT.length - 1 - i) v) (ΔT[i]'hi)) := by
  rw [List.getElem?_eq_getElem (by rw [telSubstLast_length]; exact hi),
      telSubstLast_getElem v ΔT i hi]

/-- the index-`i` argument fills the `i`-th outermost telescope domain:
    `ΔT[|ΔT|-1-i]` under `Γ`, its `i` inner binders already instantiated
    by `args.take i`. The general-j substitution theorem peels one
    outermost binder per step. -/
def hasTyT_instPrefix {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (args : List (Expr Nat)) → {Γ : LCtx} → {ΔT : List (Expr Nat)} →
    {e T : Expr Nat} →
    (hlen : ΔT.length = args.length) →
    HasTyT E n (ΔT.map LocalDecl.assumption ++ Γ) e T →
    (∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) →
    HasTyT E n Γ (instPrefix args e) (instPrefix args T)
  | [], _, ΔT, e, T, hlen, he, _ => by
      cases ΔT with
      | nil => simpa only [List.map_nil, List.nil_append, instPrefix] using he
      | cons => simp only [List.length_cons, List.length_nil] at hlen
                omega
  | a :: as, Γ, ΔT, e, T, hlen, he, hargs => by
      have hnn : ΔT ≠ [] := by
        intro hnil
        rw [hnil, List.length_nil] at hlen
        exact Nat.noConfusion hlen
      generalize hΔT' : ΔT.dropLast = ΔT'
      generalize hD : ΔT.getLast hnn = D
      have hΔ : ΔT = ΔT' ++ [D] := by
        rw [← hΔT', ← hD]; exact (List.dropLast_concat_getLast hnn).symm
      clear hΔT' hD
      subst hΔ
      have hlen' : ΔT'.length = as.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hlen
        omega
      have hctx : (ΔT' ++ [D]).map LocalDecl.assumption ++ Γ =
          ΔT'.map LocalDecl.assumption ++ (.assumption D :: Γ) := by
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      rw [hctx] at he
      have hget :
          (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ)[ΔT'.length]? =
            some (.assumption D) := by
        rw [List.getElem?_append_right
          (by simp : (ΔT'.map LocalDecl.assumption).length ≤ ΔT'.length)]
        simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero]
      have hlast : outerDom (ΔT' ++ [D]) 0 = D := by
        have hidx : (ΔT' ++ [D]).length - 1 - 0 = ΔT'.length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [outerDom, List.getD_eq_getElem?_getD, hidx]
        rw [List.getElem?_append_right (Nat.le_refl ΔT'.length)]
        simp
      have ha0 : HasTyT E n Γ a D := by
        have h0 := hargs 0 (Nat.succ_pos _)
        rw [hlast] at h0
        simpa only [List.getElem_cons_zero, List.take_zero, instPrefix]
          using h0
      have hvty : HasTyT E n
          (substRemove a ΔT'.length
            (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ))
          (lift 0 ΔT'.length a) (lift 0 ΔT'.length D) := by
        rw [substRemove_tel_assumption]
        have hw := hasTyTLiftPrefix hcl
          ((telSubstLast a ΔT').map LocalDecl.assumption) ha0
        rwa [List.length_map, telSubstLast_length] at hw
      have hstep := hasTyT_substS hcl hinst a D (j := ΔT'.length)
        he hget hvty
      rw [substRemove_tel_assumption, hlen'] at hstep
      simp only [instPrefix]
      refine hasTyT_instPrefix hcl hinst as (ΔT := telSubstLast a ΔT')
        (e := instantiate as.length (lift 0 as.length a) e)
        (T := instantiate as.length (lift 0 as.length a) T) ?_ hstep ?_
      · exact (telSubstLast_length a ΔT').trans hlen'
      · intro i hi
        have hb : as.length - 1 - i < ΔT'.length := by rw [hlen']; omega
        have hdom : outerDom (ΔT' ++ [D]) (i + 1) =
            (ΔT'[as.length - 1 - i]'(hb)) := by
          have hidx : (ΔT' ++ [D]).length - 1 - (i + 1) =
              as.length - 1 - i := by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega
          simp only [outerDom, List.getD_eq_getElem?_getD, hidx,
            List.getElem?_append_left hb, List.getElem?_eq_getElem hb,
            Option.getD_some]
        have hsrc := hargs (i + 1) (Nat.succ_lt_succ hi)
        rw [hdom] at hsrc
        simp only [List.getElem_cons_succ, List.take_succ_cons, instPrefix,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hsrc
        have hdom' : outerDom (telSubstLast a ΔT') i =
            instantiate i (lift 0 i a) (ΔT'[as.length - 1 - i]'(hb)) := by
          have hb' : ΔT'.length - 1 - i < ΔT'.length := by
            rw [hlen']; omega
          have hlt2 : (telSubstLast a ΔT').length - 1 - i =
              ΔT'.length - 1 - i := by rw [telSubstLast_length]
          simp only [outerDom, List.getD_eq_getElem?_getD, hlt2]
          rw [telSubstLast_getElem? a ΔT' (ΔT'.length - 1 - i) hb']
          have hidx' : ΔT'.length - 1 - i = as.length - 1 - i := by
            rw [hlen']
          rw [getElem_idx_congr hidx' hb' hb]
          have hsub : ΔT'.length - 1 - (ΔT'.length - 1 - i) = i := by
            omega
          rw [hsub, Option.getD_some]
        rw [hdom']
        exact hsrc

/-- the `EnvWfT`-fronted wrapper. -/
def hasTyT_instPrefix_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} {ΔT : List (Expr Nat)} {args : List (Expr Nat)}
    {e T : Expr Nat} (hlen : ΔT.length = args.length)
    (he : HasTyT E n (ΔT.map LocalDecl.assumption ++ Γ) e T)
    (hargs : ∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) :
    HasTyT E n Γ (instPrefix args e) (instPrefix args T) :=
  hasTyT_instPrefix (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) args hlen he hargs

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyT_instPrefix
#print axioms Rcic.Declarative.hasTyT_instPrefix_of_envWfT
