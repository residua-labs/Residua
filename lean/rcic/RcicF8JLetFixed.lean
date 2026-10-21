import rcic.RcicF8EvParStar
/-! # `RcicF8JLetFixed` — J-LET-FIXED, pre-#7150 half (JT-1 §4.9, design: ChatGPT
    supply map `JT1_OPEN_ROWS_SUPPLY_MAP.md` §3/§4.9/§5.2/§7).

Constraint (§4.9): `A' = A`, `value' = value`, `B` an explicit sort `.sort s`;
the centre is `letE A value N` for the child's actual centre `N`. Never a
fake let-binder move: `ParRedT.letE`'s left context is
`.letBinding A value :: Γ`, so the stored value in the child context is the
SAME `value` the centre names — there is no degree of freedom to fake here,
and the §7 mutant (`RcicF8JLetFixedPins`) shows what wrongly accepting that
mismatch would look like.

(a) Path lifting — `parRedTStar_letE_body_sort` is a COMPOSITION over the
landed general `parRedTStar_letE_body` (`RcicParRedTConv`): the general
lemma already fixes `A' = A`, `value' = value` on every `.tail` step; this
slice supplies `B := .sort s`, so `instantiate0 value (.sort s)` is
DEFINITIONALLY `.sort s` and the two side typings are the leaf-free
`HasTyT.sort`. It lifts EACH `.tail` step of an ACTUAL child chain
`b ⇒* b'` (a multi-step `ParRedTStar`, never a single-step stand-in —
`EvParStar.val` materializes the full chain for concrete child evidence).
Exact equations:

- source/target: `(lift hs)` runs `letE A value b ⇒ letE A value b'` — by
  construction of every `.tail` step and the terminal `.refl`;
- size: `(lift hs).steps = hs.steps` — one lifted step per child step,
  `parRedTStar_letE_body_steps` (proved for the landed general lemma);
- leaf: the terminal typing leaf is the `HasTyT.letE` introduction of the
  child's own terminal typing leaf at the SAME stored value,
  `parRedTStar_letE_body_finalTy`.

`valley_letE_fixed_legs` applies the sort-specialized lift to BOTH actual
multi-step legs of an actual child `Valley` (materialized via
`EvParStar.val`), centre `letE A value V.N`, shared index `.sort s`.

(b) Formation evidence — `hasTyT_letE_intro_fields`: extracts the letE
introduction's OWN domain/value/body evidence along the original path. Its
domain is fixed by the independent syntactic condition `HasTyT.isLetEIntro`
(the derivation's head IS `HasTyT.letE`); it never takes a `give me any
hB/hPi/hTy` interface. Refusal is structural: on every other constructor the
premise is `False`. `hasTyT_letE_intro_data` is the same extraction in
`Option` form for decidable callers.

`letEForm_ctxWf` rebuilds the REAL let context `.letBinding A value :: Γ`
from the extracted evidence — the same context the child star demands.

NOT claimed: the endpoint assembly (needs #7150's `EvTy` letE introduction
arm), the J-LET-FIXED row answered, or closure. closure_claim = 0. -/
set_option autoImplicit false
namespace Rcic.Declarative
open F8Measure

/-- Step count of a typed star (each `.tail` is one step; `.refl` is zero). -/
def ParRedTStar.steps {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    ParRedTStar PEq E n Γ a b T → Nat
  | .refl _ _ _ _ => 0
  | .tail _ hs => 1 + hs.steps

/-- **J-LET-FIXED (a): the letE body congruence at the §4.9 sort index** —
    the landed `parRedTStar_letE_body` with `B := .sort s`. `A' = A`,
    `value' = value` on every step; `instantiate0 value (.sort s)` is
    definitionally `.sort s`, so the let-context `B` typing and the
    ambient sort typing are the leaf-free `HasTyT.sort`. -/
def parRedTStar_letE_body_sort {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {A value b b' : Expr Nat} {u s : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (hs : ParRedTStar PEq E n (.letBinding A value :: Γ) b b' (.sort s)) :
    ParRedTStar PEq E n Γ (.letE A value b) (.letE A value b') (.sort s) :=
  parRedTStar_letE_body hPEq hΓ hA hv (.sort _ s) (.sort _ s) hs

/-- `PEqLeafT` instantiation — the endpoint evidence is the bundled
    projection, no extra premise. -/
def parRedTStar_letE_body_sort_peqLeafT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A value b b' : Expr Nat} {u s : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (hs : ParRedTStar (PEqLeafT E n) E n (.letBinding A value :: Γ) b b' (.sort s)) :
    ParRedTStar (PEqLeafT E n) E n Γ (.letE A value b) (.letE A value b') (.sort s) :=
  parRedTStar_letE_body_sort (fun h => ⟨h.2.1, h.2.2⟩) hΓ hA hv hs

/-- **Exact size equation** (of the landed general lift): the lifted chain
    has exactly the child's step count — the lift is step-for-step over the
    actual multi-step path, never a single-step stand-in. -/
theorem parRedTStar_letE_body_steps
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {A v b b' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w))
    (hs : ParRedTStar PEq E n (.letBinding A v :: Γ) b b' B) :
    (parRedTStar_letE_body hPEq hΓ hA hv hB hTy hs).steps = hs.steps := by
  induction hs with
  | refl _ _ _ => rfl
  | tail h hs ih =>
      have := ih hB hTy
      simp only [parRedTStar_letE_body, ParRedTStar.steps]
      omega

/-- **Exact leaf equation** (of the landed general lift): the lifted
    chain's terminal typing leaf is the `HasTyT.letE` introduction of the
    child's own terminal leaf — same domain, same stored `value`, same
    index `B`, no stand-in evidence. -/
theorem parRedTStar_letE_body_finalTy
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {A v b b' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 v B) (.sort w))
    (hs : ParRedTStar PEq E n (.letBinding A v :: Γ) b b' B) :
    parRedTStar_right_typed (parRedTStar_letE_body hPEq hΓ hA hv hB hTy hs) =
      HasTyT.letE Γ A u v B b' hA hv (parRedTStar_right_typed hs) := by
  induction hs with
  | refl _ _ _ => rfl
  | tail h hs ih => exact ih hB hTy

/-- **J-LET-FIXED (a), both legs**: the two actual multi-step `ParRedTStar`
    paths of an actual child `Valley` (materialized via `EvParStar.val`,
    `R = leaves`) lifted through the letE congruence — centre
    `letE A value V.N`, shared index `.sort s`, A' = A, value' = value. -/
def valley_letE_fixed_legs {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value b₁ b₂ : Expr Nat} {u s : Level}
    (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (V : Valley R (.letBinding A value :: Γ) b₁ b₂ (.sort s)) :
    ParRedTStar (PEqLeafT E n) E n Γ
        (.letE A value b₁) (.letE A value V.N) (.sort s) ×
    ParRedTStar (PEqLeafT E n) E n Γ
        (.letE A value b₂) (.letE A value V.N) (.sort s) :=
  ⟨parRedTStar_letE_body_sort_peqLeafT hΓ hA hv (V.left.val hcl hinst),
   parRedTStar_letE_body_sort_peqLeafT hΓ hA hv (V.right.val hcl hinst)⟩

/-- Both lifted legs keep their child legs' step counts. -/
theorem valley_letE_fixed_legs_steps {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value b₁ b₂ : Expr Nat} {u s : Level}
    (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (V : Valley R (.letBinding A value :: Γ) b₁ b₂ (.sort s)) :
    (valley_letE_fixed_legs hcl hinst hΓ hA hv V).1.steps =
        (V.left.val hcl hinst).steps ∧
      (valley_letE_fixed_legs hcl hinst hΓ hA hv V).2.steps =
        (V.right.val hcl hinst).steps :=
  ⟨parRedTStar_letE_body_steps _ hΓ hA hv _ _ _,
   parRedTStar_letE_body_steps _ hΓ hA hv _ _ _⟩

/-- **J-LET-FIXED (b): the independent syntactic domain condition.** The
    extractor below applies exactly when the ORIGINAL derivation's head is
    `HasTyT.letE` — it is never "give me any hB/hPi/hTy". -/
def HasTyT.isLetEIntro {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t T : Expr Nat} : HasTyT E n Γ t T → Prop
  | .letE _ _ _ _ _ _ _ _ _ => True
  | _ => False

/-- The letE introduction's own formation evidence: the domain annotation's
    sort typing, the stored value's typing at that annotation, and the
    body's typing in the REAL `.letBinding A value` context it was
    introduced under. -/
structure LetEFormData (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  A : Expr Nat
  value : Expr Nat
  B : Expr Nat
  body : Expr Nat
  u : Level
  hA : HasTyT E n Γ A (.sort u)
  hv : HasTyT E n Γ value A
  hb : HasTyT E n (.letBinding A value :: Γ) body B

/-- The same extraction in `Option` form: `some` exactly on the
    `HasTyT.letE` head, `none` (refusal) on every other constructor. -/
def hasTyT_letE_intro_data {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t T : Expr Nat} : HasTyT E n Γ t T → Option (LetEFormData E n Γ)
  | .letE _ A u v B b hA hv hb => some ⟨A, v, B, b, u, hA, hv, hb⟩
  | _ => none

/-- **The formation-evidence extractor along the original introduction
    path** (§5.2): from a derivation whose head IS `HasTyT.letE`
    (independent syntactic condition, not an evidence interface), return
    the actual domain/value/body evidence with the exact subject and index
    equations. On every other constructor the premise is `False` — the
    domain is refused, not supplied. -/
def hasTyT_letE_intro_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t T : Expr Nat} (h : HasTyT E n Γ t T) :
    h.isLetEIntro →
      Σ' d : LetEFormData E n Γ,
        t = .letE d.A d.value d.body ∧ T = instantiate0 d.value d.B := by
  intro hd
  cases h with
  | letE _ A u v B b hA hv hb =>
      exact ⟨⟨A, v, B, b, u, hA, hv, hb⟩, rfl, rfl⟩
  | _ => exact False.elim hd

/-- The extracted evidence re-forms the REAL let context — the same
    `.letBinding A value :: Γ` the child star requires. -/
def letEForm_ctxWf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) (d : LetEFormData E n Γ) :
    CtxWfT E n (.letBinding d.A d.value :: Γ) :=
  .letBinding Γ d.A d.u d.value hΓ d.hA d.hv

end Rcic.Declarative
