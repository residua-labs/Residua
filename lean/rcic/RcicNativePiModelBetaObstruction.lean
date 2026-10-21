import rcic.RcicNativePiModel
import rcic.RcicNativePiHeadObs

set_option autoImplicit false

/-!
# An admitted beta equation refutes the fixed singleton approximation model

This file uses `PiModelAudit.Approx` and `Cpt.down` exactly as defined in
`RcicNativePiModel`. It does not redefine either relation. The obstruction
already occurs at a closed, sort-typed native beta conversion in `emptyEnv`.
There is no proof-irrelevance, recursor, axiom declaration, or inconsistent
local context in the native derivation.

Let `X = Pi (Sort 0), Sort 0`, with sorting level `k = imax 1 1`.
The body under `x : Sort k` is `Pi (y : x), x`, written `pi (bvar 0)
(bvar 1)`. Native beta equates its application to `X` with `Pi (y : X), X`.

The argument `X` has both compact approximations

* `smallCompact = pi bot []`, and
* `largeCompact = pi sort []`.

Consequently, the target has `probeCompact = pi smallCompact [(bot,
largeCompact)]`: its domain uses the first approximation of `X`, and its
codomain uses the second. On the source side, an application selects one
step-function input `u`. The lambda body is evaluated with the singleton
`Cpt.down u`, so its two occurrences of `x` would require both
`smallCompact = u` and `largeCompact = u`. The distinct compact constructors
make that impossible. All three distinguishing compacts are Pi-shaped,
so the universal `Approx.lamNil` rule does not supply them.

The result refutes the existing `TypedSoundnessAtBot emptyEnv 0` for this
fixed model. It does not refute semantic approaches to native injectivity.
It also does not refute `ApproxSubst`: that statement extends an environment
by the argument's full denotation, whereas this application rule tests the
lambda body under one singleton input. No claim about `ApproxSubst` is made.

All new proofs are finite constructor constructions or inversions. There
are no new recursive calls, no new axioms, and no injectivity, confluence,
typing-uniqueness, row, or fundamental-lemma premise. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiModelBetaObstructionAudit

open PiModelAudit

/-- The native sorting of the closed Pi argument. -/
def betaUniverse : Level := .imax (.succ .zero) (.succ .zero)

/-- The native sorting of both endpoints of the beta equation. -/
def betaResultLevel : Level := .imax betaUniverse betaUniverse

/-- `X = Pi (P : Prop), Prop`, reusing the previously constructed native
Pi fixture. -/
def betaArgument : Expr Nat := NativePiHeadObs.betaPiHead

/-- `Pi (y : x), x` under `x : Sort k`. -/
def betaBody : Expr Nat := .pi (.bvar 0) (.bvar 1)

def betaSource : Expr Nat :=
  .app (.lam (.sort betaUniverse) betaBody) betaArgument

def betaTarget : Expr Nat := .pi betaArgument betaArgument

def betaBodyContext : LCtx := [.assumption (.sort betaUniverse)]

/-- The environment is the admitted empty native environment. -/
def nativeEmptyEnvWf : EnvWfT emptyEnv := .empty

/-- The local context is empty as well. -/
def nativeEmptyCtxWf : CtxWfT emptyEnv 0 [] := .nil

def betaArgumentTyping (Γ : LCtx) :
    HasTyT emptyEnv 0 Γ betaArgument (.sort betaUniverse) :=
  NativePiHeadObs.betaPiHeadTy emptyEnv 0 Γ

/-- Both occurrences of `x` are typed at the same original native sort.
The codomain occurrence is `bvar 1` under the Pi's additional binder. -/
def betaBodyTyping :
    HasTyT emptyEnv 0 betaBodyContext betaBody (.sort betaResultLevel) :=
  .pi betaBodyContext (.bvar 0) betaUniverse (.bvar 1) betaUniverse
    (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)

def betaSourceTyping :
    HasTyT emptyEnv 0 [] betaSource (.sort betaResultLevel) :=
  .app [] (.lam (.sort betaUniverse) betaBody) betaArgument
    (.sort betaUniverse) (.sort betaResultLevel)
    (.lam [] (.sort betaUniverse) (.succ betaUniverse) betaBody
      (.sort betaResultLevel) (.sort [] betaUniverse) betaBodyTyping)
    (betaArgumentTyping [])

def betaTargetTyping :
    HasTyT emptyEnv 0 [] betaTarget (.sort betaResultLevel) :=
  .pi [] betaArgument betaUniverse betaArgument betaUniverse
    (betaArgumentTyping []) (betaArgumentTyping [.assumption betaArgument])

/-- This is the native substitution computation, by definitional equality. -/
theorem beta_substitution : instantiate0 betaArgument betaBody = betaTarget := rfl

/-- The actual native conversion is one beta constructor. -/
def betaConversion :
    ConvT emptyEnv 0 [] betaSource betaTarget (.sort betaResultLevel) :=
  .beta [] (.sort betaUniverse) betaBody betaArgument (.sort betaResultLevel)
    (.succ betaUniverse) (.sort [] betaUniverse) betaBodyTyping
    (betaArgumentTyping [])

def betaTypeChain : TyConvT emptyEnv 0 [] betaSource betaTarget :=
  .of [] betaSource betaTarget betaResultLevel betaConversion

/-! ## The separating compact and the fixed approximation relation -/

def smallCompact : Cpt := .pi .bot []

def largeCompact : Cpt := .pi .sort []

def probeCompact : Cpt := .pi smallCompact [(.bot, largeCompact)]

theorem small_ne_large : smallCompact ≠ largeCompact := by
  intro h
  exact Cpt.noConfusion (Cpt.pi.inj h).1

theorem argument_small (ρ : Env) : Approx ρ betaArgument smallCompact :=
  .pi (.bot ρ (.sort .zero)) (fun _ h => nomatch h)

theorem argument_large (ρ : Env) : Approx ρ betaArgument largeCompact :=
  .pi (.sort ρ .zero) (fun _ h => nomatch h)

/-- The target independently uses two approximations of the same closed
argument, once at its domain and once at its codomain. -/
theorem target_probe (ρ : Env) : Approx ρ betaTarget probeCompact := by
  refine .pi (argument_small ρ) ?_
  intro p hp
  have he := List.mem_singleton.mp hp
  cases he
  exact argument_large (Env.cons (Cpt.down .bot) ρ)

/-- Pi-shaped variable approximations must come from the environment;
neither the universal bottom rule nor `lamNil` can produce one. -/
theorem approx_bvar_pi {ρ : Env} {i : Nat} {a : Cpt}
    {f : List (Cpt × Cpt)} (h : Approx ρ (.bvar i) (.pi a f)) :
    ρ i (.pi a f) := by
  cases h with
  | bvar hρ => exact hρ

/-- The full argument denotation does support the same body observation.
This constructs the relevant side of the substitution interface at this
example; the obstruction arises when application asks for one singleton. -/
theorem full_argument_body_probe (ρ : Env) :
    Approx (Env.cons (fun c => Approx ρ betaArgument c) ρ) betaBody probeCompact := by
  refine .pi (.bvar (argument_small ρ)) ?_
  intro p hp
  have he := List.mem_singleton.mp hp
  cases he
  exact .bvar (argument_large ρ)

/-- Under a singleton input, the body cannot demand both distinct
Pi-shaped approximations of its one variable. -/
theorem singleton_body_no_probe (ρ : Env) (u : Cpt)
    (h : Approx (Env.cons (Cpt.down u) ρ) betaBody probeCompact) : False := by
  rcases approx_pi_inv h with h0 | h0 | ⟨a, f, heq, hA, hB⟩
  · exact Cpt.noConfusion h0
  · exact Cpt.noConfusion h0
  · obtain ⟨heA, heF⟩ := Cpt.pi.inj heq
    cases heA
    cases heF
    have hsmall : smallCompact = u := approx_bvar_pi hA
    have hlarge : largeCompact = u :=
      approx_bvar_pi (hB (.bot, largeCompact) (List.mem_singleton.mpr rfl))
    exact small_ne_large (hsmall.trans hlarge.symm)

/-- The source has no separating approximation at any environment.
Only a genuine application step can produce the Pi-shaped probe. Its
lambda premise evaluates the body at one singleton compact input. -/
theorem source_no_probe (ρ : Env) (h : Approx ρ betaSource probeCompact) : False := by
  rcases approx_app_inv h with h0 | h0 |
    ⟨g, p, heq, hf, hp, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
  · exact Cpt.noConfusion h0
  · exact Cpt.noConfusion h0
  · rcases approx_lam_inv hf with hbot | ⟨g', hg, hbody⟩
    · exact Cpt.noConfusion hbot
    · have heG := Cpt.lam.inj hg
      cases heG
      have hb := hbody p hp
      rw [← heq] at hb
      exact singleton_body_no_probe ρ p.1 hb
  · exact Cpt.noConfusion heq

/-- The fixed approximation semantics fails this native beta equation. -/
theorem beta_not_semEq (ρ : Env) : ¬ SemEq ρ betaSource betaTarget :=
  fun h => source_no_probe ρ ((h probeCompact).mpr (target_probe ρ))

/-- The exact named soundness interface of `RcicNativePiModel` is false
already in the admitted empty environment and the empty local context. -/
theorem typedSoundnessAtBot_refuted : ¬ TypedSoundnessAtBot emptyEnv 0 := by
  intro h
  exact beta_not_semEq Env.bot (h nativeEmptyCtxWf betaConversion)

/-- Terminal quotation of the fully constructed native counterexample. -/
theorem admitted_beta_counterexample :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv 0 []) ∧
    Nonempty (ConvT emptyEnv 0 [] betaSource betaTarget (.sort betaResultLevel)) ∧
    ¬ SemEq Env.bot betaSource betaTarget :=
  ⟨⟨nativeEmptyEnvWf⟩, ⟨nativeEmptyCtxWf⟩, ⟨betaConversion⟩, beta_not_semEq Env.bot⟩

#print axioms nativeEmptyEnvWf
#print axioms nativeEmptyCtxWf
#print axioms betaBodyTyping
#print axioms betaSourceTyping
#print axioms betaTargetTyping
#print axioms betaConversion
#print axioms betaTypeChain
#print axioms target_probe
#print axioms full_argument_body_probe
#print axioms singleton_body_no_probe
#print axioms source_no_probe
#print axioms beta_not_semEq
#print axioms typedSoundnessAtBot_refuted
#print axioms admitted_beta_counterexample

end Rcic.Declarative.NativeValleys.PiModelBetaObstructionAudit
