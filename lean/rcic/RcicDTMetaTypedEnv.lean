import rcic.RcicTypedGroupPins
import rcic.RcicDTMetaTypedSR

/-!
# DT typed counterparts, segment 3 — DT-013 / DT-014 / DT-016

O2S-pattern typed counterparts (erratum E-O2SCounterparts) for three more
02 §14 rows, over the typed root (`HasTyT`/`ConvT`/`EnvWfT`), BESIDE the
legacy theorems — no legacy statement touched — each with a consumption
pin at a real fixture.

- DT-013 — environment weakening: `hasTyTExt` transports a typing along a
  membership-preserving extension — the SAME hypothesis shape the legacy
  `hasTyExt` reads; nothing about the premise changes on the typed side.
- DT-014 — transparent δ soundness: `ConvT.delta` is the typed δ rule —
  its `hb` field is exactly the member-body typing `envWfT_bodyTyped`
  supplies from the typed entry's admission. The legacy theorem's
  conclusion had no type index (the degenerate `Conv` is untyped); the
  typed rule concludes at the member's own instantiated type
  `instantiateLevels ls m.mtype`, and needs `EnvWfT` + the const rule's
  `hlen`/`hwf` premises — all satisfiable, as the `pinDefEnvU` pin shows.
- DT-016 — proof irrelevance soundness: `ConvT.irr` is the typed rule,
  verbatim shape, conclusion at the Prop `P` itself.

`dtTypedCensus` lives in `RcicDTMetaTypedLiftSubst` (seg 1); this file adds
the three counterparts it names.
-/

namespace Rcic.Declarative

/-- DT-013 typed: environment weakening — the member-extensionality
    transport, on the typed judgment. -/
theorem DT013T_environment_weakening {E E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTyT E n Γ e A)
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    Nonempty (HasTyT E' n Γ e A) := ⟨hasTyTExt hext h⟩

/-- DT-014 typed: transparent δ soundness — a transparent member's constant
    unfolds to its instantiated body, at the member's own instantiated
    type, by the typed `ConvT.delta` rule. `envWfT_bodyTyped` supplies the
    rule's body-typing field from the typed entry. -/
theorem DT014T_transparent_delta_soundness {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    Nonempty (ConvT E n Γ (.const r ls) (instantiateLevels ls b)
      (instantiateLevels ls m.mtype)) :=
  ⟨ConvT.delta _ r ls m b hres hbody htr hlen hwf
    (envWfT_bodyTyped hW hres hbody hlen)⟩

/-- DT-016 typed: proof irrelevance soundness — two proofs of one Prop are
    convertible at it, by the typed `ConvT.irr` rule. -/
theorem DT016T_proof_irrelevance_soundness {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    Nonempty (ConvT E n Γ p q P) := ⟨.irr _ _ _ _ hP hp hq⟩

/-! ## consumption pins at real fixtures -/

/-- PIN (DT-013T): `Sort 0`'s typing on `natEnvU`, transported across the
    `pinDefEnvU` definition extension. -/
theorem pin_DT013T_defU {n : Nat} :
    Nonempty (HasTyT pinDefEnvU n [] (.sort .zero) (.sort (.succ .zero))) :=
  DT013T_environment_weakening (pinSortT natEnvU n)
    (members_extend_preserved
      (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
      pinDefEnvU_fresh)

/-- PIN (DT-014T): the `pinDefEnvU` definition (`Sort 0 : Sort 1` at ref 4)
    unfolds — the typed δ conversion consumed at the fixture's own body
    and type. -/
theorem pin_DT014T_defU {n : Nat} :
    Nonempty (ConvT pinDefEnvU n [] (.const 4 [])
      (instantiateLevels [] (.sort .zero))
      (instantiateLevels [] (.sort (.succ .zero)))) :=
  DT014T_transparent_delta_soundness pinDefEnvUWfT
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    rfl rfl rfl rfl rfl

/-- `Π (X : Prop), X → X` — the polymorphic-identity Prop, sort-typed at
    `imax 1 (imax 0 0)` by the π rule. -/
def pinPropIdT (E : ResolvedEnv) (n : Nat) :
    HasTyT E n []
      (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1)))
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  HasTyT.pi [] (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.bvar 1)) (.imax .zero .zero)
    (HasTyT.sort [] .zero)
    (HasTyT.pi _ (.bvar 0) .zero (.bvar 1) .zero
      (HasTyT.bvar _ 0 (.sort .zero) rfl)
      (HasTyT.bvar _ 1 (.sort .zero) rfl))

/-- the same Prop, retyped at `Sort 0` along the `imax _ 0` collapse — the
    `hP` the irr rule consumes. -/
def pinPropIdT_sort0 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1)))
      (.sort .zero) :=
  HasTyT.conv [] _ _ _ _ (pinPropIdT E n)
    (ConvT.sorts _ _ _ (fun _ => rfl))

/-- first inhabitant: `λ (X : Prop), λ (x : X), x`. -/
def pinPropIdTm1 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n []
      (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0)))
      (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))) :=
  HasTyT.lam [] (.sort .zero) (.succ .zero)
    (.lam (.bvar 0) (.bvar 0)) (.pi (.bvar 0) (.bvar 1))
    (HasTyT.sort [] .zero)
    (HasTyT.lam _ (.bvar 0) .zero (.bvar 0) (.bvar 1)
      (HasTyT.bvar _ 0 (.sort .zero) rfl)
      (HasTyT.bvar _ 0 (.bvar 1) rfl))

/-- second inhabitant, a DIFFERENT term at the same type:
    `λ (X : Prop), λ (x : X), (λ (y : X), y) x`. -/
def pinPropIdTm2 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n []
      (.lam (.sort .zero) (.lam (.bvar 0)
        (.app (.lam (.bvar 1) (.bvar 1)) (.bvar 0))))
      (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))) :=
  HasTyT.lam [] (.sort .zero) (.succ .zero)
    (.lam (.bvar 0) (.app (.lam (.bvar 1) (.bvar 1)) (.bvar 0)))
    (.pi (.bvar 0) (.bvar 1))
    (HasTyT.sort [] .zero)
    (HasTyT.lam _ (.bvar 0) .zero
      (.app (.lam (.bvar 1) (.bvar 1)) (.bvar 0)) (.bvar 1)
      (HasTyT.bvar _ 0 (.sort .zero) rfl)
      (HasTyT.app _ (.lam (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 1) (.bvar 2)
        (HasTyT.lam _ (.bvar 1) .zero (.bvar 1) (.bvar 2)
          (HasTyT.bvar _ 1 (.sort .zero) rfl)
          (HasTyT.bvar _ 1 (.bvar 2) rfl))
        (HasTyT.bvar _ 0 (.bvar 1) rfl)))

/-- PIN (DT-016T): two different proofs of the same Prop are convertible
    at it — `ConvT.irr` consumed on `natEnvU` over the polymorphic identity
    type and its two built inhabitants. -/
theorem pin_DT016T_natU {n : Nat} :
    Nonempty (ConvT natEnvU n []
      (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0)))
      (.lam (.sort .zero) (.lam (.bvar 0)
        (.app (.lam (.bvar 1) (.bvar 1)) (.bvar 0))))
      (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1)))) :=
  DT016T_proof_irrelevance_soundness
    (pinPropIdT_sort0 natEnvU n) (pinPropIdTm1 natEnvU n)
    (pinPropIdTm2 natEnvU n)

/-! ## DT-013 / EG-023 — the `hext` premise, discharged and shown necessary

Census B rows: the open leg on `DT013T_environment_weakening` is its
member-extensionality hypothesis `hext`, a `∀`-premise the caller used to
present. It is not a free hypothesis: every admitted extension in the
model is an `extendEnv` step at a fresh ref, and the step's own freshness
pays `hext` through `members_extend_preserved` — the premise is derived
from the admission object, never presented. EG-023's data half
(`apps/rcic-env-weaken`) is the scm counterpart of the same law: a
canonical image extension keeps every old `{ref, bytes}` entry. The
countermodel below shows the premise is also NECESSARY: at a target that
is not an extension, the `∀` is false and the conclusion fails. -/

/-- `hext` discharged on the admitted extension object: weakening across
    `extendEnv E r m` needs only the step's freshness field. -/
theorem DT013T_environment_weakening_at_extend {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} {r : Nat} {m : CheckedMember}
    (h : HasTyT E n Γ e A) (hfresh : E.members r = none) :
    Nonempty (HasTyT (extendEnv E r m) n Γ e A) :=
  DT013T_environment_weakening h (members_extend_preserved hfresh)

/-- PIN (DT-013T / EG-023): weakening consumed across a real admitted
    step — the Nat family at ref 0, then the `zero` constructor at ref 1.
    No `hext` argument is passed: the freshness of `1` discharges it. -/
theorem pin_DT013T_weaken_fresh_extend {n : Nat} :
    Nonempty (HasTyT (extendEnv (extendEnv emptyEnv 0 natFamMember) 1
      natZeroMember) n [] (.const 0 [])
      (instantiateLevels [] (.sort (.succ .zero)))) :=
  DT013T_environment_weakening_at_extend
    (.const [] 0 [] natFamMember rfl rfl rfl) (by
      simp [extendEnv, emptyEnv])

/-- NECESSITY (DT-013T / EG-023): `hext` cannot be dropped for an
    arbitrary target. `emptyEnv` is not an extension of the Nat-family
    env — the `∀` is false at ref 0 — and the `.const 0` typing has no
    counterpart there (member inversion on `emptyEnv.members 0`). The
    premise is exactly what certifies the target as an extension. -/
theorem DT013T_hext_necessary {n : Nat} :
    Nonempty (HasTyT (extendEnv emptyEnv 0 natFamMember) n []
        (.const 0 []) (instantiateLevels [] (.sort (.succ .zero)))) ∧
    ¬ (∀ r m, (extendEnv emptyEnv 0 natFamMember).members r = some m →
        emptyEnv.members r = some m) ∧
    ∀ T, ¬ Nonempty (HasTyT emptyEnv n [] (.const 0 []) T) := by
  refine ⟨⟨.const [] 0 [] natFamMember rfl rfl rfl⟩, ?_, fun T ⟨h⟩ => ?_⟩
  · intro h
    have h0 := h 0 natFamMember rfl
    simp [emptyEnv] at h0
  · obtain ⟨m, hm⟩ := hasTyT_constsIn h
    simp [emptyEnv] at hm

end Rcic.Declarative

#print axioms Rcic.Declarative.DT013T_environment_weakening
#print axioms Rcic.Declarative.DT014T_transparent_delta_soundness
#print axioms Rcic.Declarative.DT016T_proof_irrelevance_soundness
#print axioms Rcic.Declarative.pin_DT013T_defU
#print axioms Rcic.Declarative.pin_DT014T_defU
#print axioms Rcic.Declarative.pinPropIdT
#print axioms Rcic.Declarative.pinPropIdT_sort0
#print axioms Rcic.Declarative.pinPropIdTm1
#print axioms Rcic.Declarative.pinPropIdTm2
#print axioms Rcic.Declarative.pin_DT016T_natU
#print axioms Rcic.Declarative.DT013T_environment_weakening_at_extend
#print axioms Rcic.Declarative.pin_DT013T_weaken_fresh_extend
#print axioms Rcic.Declarative.DT013T_hext_necessary
