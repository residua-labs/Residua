import rcic.RcicF8JAppNondep
import rcic.RcicTypedEnvEntry

/-!
# RcicF8JAppNondepMutant — §7 teeth against the J-APP-NONDEP slice

Wrong implementations of the §4.8 pieces plus the shipped/noTooth check
pairs evaluating false/true on them. Fixtures are concrete: `ctxS` is the
one-binder context `assumption (.sort 0)`, `lamTy` the identity
introduction `.lam (sort 0) (bvar 0) : pi (sort 0) (sort 0)` — the
nondependent domain this slice covers.

- `collapsed` / `collapsedArg`: a one-step stand-in for a two-step child
  path (`appStepsOk`).
- `forgedDomain` / `forgedBody`: an `AppLamIntro`-shape claim whose
  fields do NOT come from the original subtree — wrong domain, wrong
  stored body (`appIntroOk`).
- `constTy`: a constant-typed function at the pi — no introduction
  subtree to extract from (`appFormOk`, `appLamIntro`).
- `rightIndex`: the index set to the RIGHT argument's instantiation —
  `instantiate0 a' (.bvar 0) = a'` ≠ `a` on a dependent codomain
  (`appIndexOk`); `bvarCodomain` drops the literal-sort gate
  (`appCodomainOk`).

`closure_claim = 0`.
-/

namespace Rcic.Declarative.JAppNondepMutant

open F8Measure

/-! ## fixtures -/

def ctxS : LCtx := [.assumption (.sort .zero)]

def ctxS_wf : CtxWfT emptyEnv 0 ctxS :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

/-- the identity lambda introduction at `pi (sort 0) (sort 0)` — the
    original introduction subtree the extractor reads. -/
def lamTy : HasTyT emptyEnv 0 ctxS
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  .lam _ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (.sort _ .zero) (.bvar _ 0 _ rfl)

/-- the intro's actual domain field, as extracted. -/
def realDomain : HasTyT emptyEnv 0 ctxS (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ .zero

/-- the intro's actual body field, as extracted. -/
def realBody : HasTyT emptyEnv 0 [.assumption (.sort .zero), .assumption (.sort .zero)]
    (.bvar 0) (.sort .zero) :=
  .bvar _ 0 _ rfl

def argTy : HasTyT emptyEnv 0 ctxS (.bvar 0) (.sort .zero) :=
  .bvar _ 0 _ rfl

/-- the app-node function-side typing of the app endpoint. -/
def appEndTy : HasTyT emptyEnv 0 ctxS
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
  .app _ _ _ _ _ lamTy argTy

/-- a concrete child step (reflexive on the lam). -/
def funStep : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.lam (.sort .zero) (.bvar 0)) (.lam (.sort .zero) (.bvar 0))
    (.pi (.sort .zero) (.sort .zero)) :=
  .refl _ _ _ lamTy

/-- the actual two-step function path. -/
def funChild : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.lam (.sort .zero) (.bvar 0)) (.lam (.sort .zero) (.bvar 0))
    (.pi (.sort .zero) (.sort .zero)) :=
  .tail funStep (.tail funStep (.refl _ _ _ lamTy))

/-- a concrete child step on the argument. -/
def argStep : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl _ _ _ argTy

/-- the actual two-step argument path. -/
def argChild : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .tail argStep (.tail argStep (.refl _ _ _ argTy))

/-- the shipped lifts on the fixtures — both honest two-step paths. -/
def liftedFun : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
  parRedTStar_app_fun_nondep peqLeafT_typed ctxS_wf argTy funChild

def liftedArg : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
  parRedTStar_app_arg_nondep peqLeafT_typed ctxS_wf lamTy argChild

/-- a constant-typed function at the same pi — a `CheckedMember` whose
    mtype IS the pi, so the typing is real but there is NO introduction
    subtree along it. -/
def fixEnv : ResolvedEnv :=
  extendEnv emptyEnv 7 ⟨.axiomM, 0, .pi (.sort .zero) (.sort .zero), none⟩

def constTy : HasTyT fixEnv 0 [] (.const 7 []) (.pi (.sort .zero) (.sort .zero)) :=
  .const [] 7 [] ⟨.axiomM, 0, .pi (.sort .zero) (.sort .zero), none⟩ rfl rfl rfl

/-! ## wrong implementations (mutants) -/

/-- the one-step stand-in: a "lift" that collapses the two-step function
    child to a single step. -/
def collapsed : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
  .tail (appFunStep argTy funStep lamTy) (.refl _ _ _ appEndTy)

/-- the one-step stand-in, argument side. -/
def collapsedArg : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 ctxS
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
  .tail (appArgStep lamTy argStep argTy) (.refl _ _ _ appEndTy)

/-- a forged domain field: a typing of `sort 1`, claimed as the intro's
    domain (`sort 0`) — not a field of the original subtree. -/
def forgedDomain : HasTyT emptyEnv 0 ctxS
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort _ (.succ .zero)

/-- a forged body field: the right context, but the subject `sort 0` is
    not the intro's stored body `bvar 0`. -/
def forgedBody : HasTyT emptyEnv 0 [.assumption (.sort .zero), .assumption (.sort .zero)]
    (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ .zero

/-! ## shipped/noTooth pairs -/

theorem intro_shipped_accepts :
    appIntroOk lamTy realDomain realBody = true := rfl

theorem introForgedDomain_shipped_rejects :
    appIntroOk lamTy forgedDomain realBody = false := rfl

theorem introForgedDomain_noTooth_accepts :
    appIntroOk_noTooth lamTy forgedDomain realBody = true := rfl

theorem introForgedBody_shipped_rejects :
    appIntroOk lamTy realDomain forgedBody = false := rfl

theorem introForgedBody_noTooth_accepts :
    appIntroOk_noTooth lamTy realDomain forgedBody = true := rfl

theorem index_shipped_accepts :
    appIndexOk (.lit 0) (.lit 1) (.sort .zero) (.sort .zero) = true := rfl

/-- the RIGHT-instantiation index on a dependent codomain —
    `instantiate0 (.lit 1) (.bvar 0) = .lit 1` while the left gives
    `.lit 0`. -/
theorem rightIndex_shipped_rejects :
    appIndexOk (.lit 0) (.lit 1) (.lit 1) (.bvar 0) = false := rfl

theorem rightIndex_noTooth_accepts :
    appIndexOk_noTooth (.lit 0) (.lit 1) (.lit 1) (.bvar 0) = true := rfl

theorem codomain_shipped_accepts :
    appCodomainOk (.sort .zero) = true := rfl

theorem bvarCodomain_shipped_rejects :
    appCodomainOk (.bvar 0) = false := rfl

theorem bvarCodomain_noTooth_accepts :
    appCodomainOk_noTooth (.bvar 0) = true := rfl

theorem form_shipped_accepts : appFormOk lamTy = true := rfl

theorem constForm_shipped_rejects : appFormOk constTy = false := by
  simp [appFormOk, constTy, wJAppFormDomain]

theorem constForm_noTooth_accepts : appFormOk_noTooth constTy = true := rfl

/-- the extractor itself: `some` on the real intro, `none` on the
    constant-typed function — the independent syntactic domain. -/
theorem extract_lam : (appLamIntro lamTy).isSome = true := rfl

theorem extract_const : (appLamIntro constTy).isSome = false := by
  simp [constTy, appLamIntro]

theorem steps_shipped_accepts :
    appStepsOk liftedFun funChild = true := by
  simp [appStepsOk, liftedFun, parRedTStar_app_fun_nondep_steps]

theorem steps_shipped_accepts_arg :
    appStepsOk liftedArg argChild = true := by
  simp [appStepsOk, liftedArg, parRedTStar_app_arg_nondep_steps]

theorem collapsed_shipped_rejects :
    appStepsOk collapsed funChild = false := rfl

theorem collapsed_noTooth_accepts :
    appStepsOk_noTooth collapsed funChild = true := rfl

theorem collapsedArg_shipped_rejects :
    appStepsOk collapsedArg argChild = false := rfl

theorem collapsedArg_noTooth_accepts :
    appStepsOk_noTooth collapsedArg argChild = true := rfl

#eval s!"intro shipped={appIntroOk lamTy forgedDomain realBody} noTooth={appIntroOk_noTooth lamTy forgedDomain realBody}"
#eval s!"index shipped={appIndexOk (.lit 0) (.lit 1) (.lit 1) (.bvar 0)} noTooth={appIndexOk_noTooth (.lit 0) (.lit 1) (.lit 1) (.bvar 0)}"
#eval s!"codomain shipped={appCodomainOk (.bvar 0)} noTooth={appCodomainOk_noTooth (.bvar 0)}"
#eval s!"form shipped={appFormOk constTy} noTooth={appFormOk_noTooth constTy}"
#eval s!"steps shipped={appStepsOk collapsed funChild} noTooth={appStepsOk_noTooth collapsed funChild}"

end Rcic.Declarative.JAppNondepMutant
