import rcic.RcicF8Child
import rcic.RcicF8EvParStar
import rcic.RcicParRedTConv
import rcic.RcicProofOccurrences

/-!
# RcicF8JAppNondep — J-APP-NONDEP, the pre-#7150 slice (supply map §4.8)

ChatGPT's approved row `research/rcic/j-tile/JT1_OPEN_ROWS_SUPPLY_MAP.md`
(#7213), §4.8. The application congruence `ParRedT.app` asks for three
things the dispatcher cannot fabricate:

- **W-J-APP-FORM** (named, §5.2 strict formation evidence): `hB`, `hPi`,
  `hTy` extracted along the ORIGINAL introduction path — never a generic
  "give me any `hB`/`hPi`/`hTy`" interface. This slice's extractor is
  `appLamIntro`: its domain is the independent syntactic condition
  `wJAppFormDomain` (the function-side typing's outer constructor IS
  `HasTyT.lam` at a `.pi A (.sort ℓ)` index), and the returned `hA`/`hbody`
  are literally the introduction's fields — `Jd.tyChildren` members of the
  original subtree.
- **W-J-APP-INDEX** (named): the step index is `instantiate0 a B`, the LEFT
  argument's instantiation, while the right endpoint is `app f' a'`. On the
  nondependent domain `B = .sort ℓ` both sides reduce to the same sort
  (`wJAppIndex_nondep`); the dependent coordination stays the named gap.
- **(a) path lifting**: each step of an ACTUAL child valley's two
  multi-step paths lifts through the congruence — `parRedTStar_app_fun_nondep`
  (the landed `parRedTStar_app_fun` specialized at `B := .sort ℓ`) and the
  new `parRedTStar_app_arg_nondep`, which needs NO semantic bundle: on
  `B = .sort ℓ` every step lands at the same index, so
  `convT_inst0_valueSort` never arises. Exact equations:
  `parRedTStar_steps` is preserved per leg (never a one-step stand-in),
  and `occurrences` of each lifted step are exactly the child step's,
  `.inl`- (fun) or `.inr`- (arg) embedded — `sumList`'s meaning.

`appValleyLegs` packages the four materialized legs of the future
`app f a ⇉ app Nf Na ⇇ app f' a'` valley from ACTUAL child `Valley`s.
The lazy `Jd`-leaf accounting between materialized `Occ` sites and
`EvParStar.leaves` is the D2b app producer's (EX boundary); endpoint
assembly into the J dispatcher waits for #7150's `EvTy` introduction arms.

`closure_claim = 0`.
-/

namespace Rcic.Declarative

open F8Measure F8Occurrences

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ## the `PEqLeafT` discharge -/

/-- the `PEqLeafT` bundle already carries both endpoint typings — the
    `hPEq` premise of the landed congruence kit is a projection. -/
def peqLeafT_typed {Γ : LCtx} {p q T : Expr Nat}
    (h : PEqLeafT E n Γ p q T) :
    HasTyT E n Γ p T × HasTyT E n Γ q T :=
  ⟨h.2.1, h.2.2⟩

/-! ## W-J-APP-INDEX — the nondependent case -/

/-- W-J-APP-INDEX's nondependent domain — an independent syntactic
    condition on the codomain expression alone. -/
def wJAppIndexDomain (B : Expr Nat) : Bool :=
  match B with
  | .sort _ => true
  | _ => false

/-- W-J-APP-INDEX, nondependent case — named. On `B = .sort ℓ` the left
    and right instantiation indices are literally the same term; the
    dependent `instantiate0 a B` vs `instantiate0 a' B` coordination does
    not arise. The general dependent W-J-APP-INDEX remains the named gap
    (this module does not discharge it). -/
theorem wJAppIndex_nondep {a a' : Expr Nat} {ℓ : Level} :
    instantiate0 a (.sort ℓ) = instantiate0 a' (.sort ℓ) := rfl

/-! ## W-J-APP-FORM — the strict extractor -/

/-- W-J-APP-FORM's nondependent domain — an independent syntactic
    condition on the derivation's outer shape: the ORIGINAL function-side
    typing is a direct `HasTyT.lam` introduction whose codomain is a
    literal sort. A conv-retyped, variable, constant, literal, or
    application typing — whatever introduction subtree sits inside it —
    is OUTSIDE this domain. -/
def wJAppFormDomain {Γ : LCtx} {f T : Expr Nat} :
    HasTyT E n Γ f T → Bool
  | .lam _ _ _ _ B _ _ => wJAppIndexDomain B
  | _ => false

/-- the fields extracted along the ORIGINAL introduction path. `hA` and
    `hbody` are literal `Jd.ty` children of the introducing `HasTyT.lam`
    (`Jd.tyChildren` = `[.ty hA, .ty hbody]`); `hbody` additionally feeds
    the future #7150 `lam` introduction arm. `A`/`B` are kept as fields —
    the extractor matches at a FREE index `T` (the dependent matcher
    cannot eliminate `.const` at a fixed pi index), and the caller's pi
    shape pins them via `appLamIntro_spec`. -/
structure AppLamIntro (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  A : Expr Nat
  B : Expr Nat
  body : Expr Nat
  u : Level
  hA : HasTyT E n Γ A (.sort u)
  hbody : HasTyT E n (.assumption A :: Γ) body B

/-- W-J-APP-FORM's extractor along the original introduction path —
    `some` exactly on `isLamIntro`. A `conv`-wrapped, `bvar`, `const`,
    `lit`, `app`, `pi`, `sort`, or `letE` typing returns `none`; the
    extractor never fabricates a domain typing from caller-supplied
    evidence. -/
def appLamIntro {Γ : LCtx} {f T : Expr Nat} :
    HasTyT E n Γ f T → Option (AppLamIntro E n Γ)
  | .lam _ A u body B hA hbody => some ⟨A, B, body, u, hA, hbody⟩
  | _ => none

/-- the extraction domain, purely syntactic: the typing's ROOT is a lam
    introduction (conv-wrapped typings are OUT — the introduction path is
    the root constructor itself). -/
def isLamIntro {Γ : LCtx} {f T : Expr Nat} : HasTyT E n Γ f T → Bool
  | .lam .. => true
  | _ => false

/-- extraction succeeds exactly on the lam-rooted typings. -/
theorem appLamIntro_isSome {Γ : LCtx} {f T : Expr Nat}
    (hty : HasTyT E n Γ f T) : (appLamIntro hty).isSome = isLamIntro hty := by
  cases hty <;> simp [appLamIntro, isLamIntro]

/-- the extracted domain typing IS a child of the original subtree —
    §5.2's provenance, not a caller-supplied `hA`. -/
theorem appLamIntro_hA_child {Γ : LCtx} {f T : Expr Nat}
    (hty : HasTyT E n Γ f T) {i : AppLamIntro E n Γ}
    (hi : appLamIntro hty = some i) : Jd.ty i.hA ∈ Jd.tyChildren hty := by
  cases hty <;> simp only [appLamIntro] at hi
  case lam A u body B hA hbody =>
      obtain rfl := Option.some.inj hi
      simp [Jd.tyChildren]
  all_goals cases hi

/-- the extracted body typing IS a child of the original subtree. -/
theorem appLamIntro_hbody_child {Γ : LCtx} {f T : Expr Nat}
    (hty : HasTyT E n Γ f T) {i : AppLamIntro E n Γ}
    (hi : appLamIntro hty = some i) : Jd.ty i.hbody ∈ Jd.tyChildren hty := by
  cases hty <;> simp only [appLamIntro] at hi
  case lam A u body B hA hbody =>
      obtain rfl := Option.some.inj hi
      simp [Jd.tyChildren]
  all_goals cases hi

/-- the extracted introduction's subject: `f` IS the original lambda. -/
theorem appLamIntro_subject {Γ : LCtx} {f T : Expr Nat}
    (hty : HasTyT E n Γ f T) {i : AppLamIntro E n Γ}
    (hi : appLamIntro hty = some i) : f = .lam i.A i.body := by
  cases hty <;> simp only [appLamIntro] at hi
  case lam A u body B hA hbody =>
      obtain rfl := Option.some.inj hi
      rfl
  all_goals cases hi

/-- on the strict domain the introduction's pi pins the extracted fields:
    `i.A`/`i.B` are the CLAIMED domain/codomain, not fresh ones. -/
theorem appLamIntro_spec {Γ : LCtx} {f T A : Expr Nat} {ℓ : Level}
    (hty : HasTyT E n Γ f T) (hT : T = .pi A (.sort ℓ)) {i : AppLamIntro E n Γ}
    (hi : appLamIntro hty = some i) : i.A = A ∧ i.B = .sort ℓ := by
  cases hty <;> simp only [appLamIntro] at hi
  case lam A' u body B' hA hbody =>
      obtain rfl := Option.some.inj hi
      obtain ⟨rfl, rfl⟩ := Expr.pi.inj hT
      exact ⟨rfl, rfl⟩
  all_goals cases hi

/-- the strict domain is exactly the extraction domain restricted to the
    literal-sort codomain. -/
theorem wJAppFormDomain_appLamIntro {Γ : LCtx} {f T : Expr Nat}
    (hty : HasTyT E n Γ f T) (h : wJAppFormDomain hty = true) :
    ∃ i : AppLamIntro E n Γ,
      appLamIntro hty = some i ∧ wJAppIndexDomain i.B = true := by
  cases hty
  case lam A u body B hA hbody =>
      exact ⟨⟨A, B, body, u, hA, hbody⟩, by simp [appLamIntro],
        by simpa only [wJAppFormDomain] using h⟩
  all_goals simp_all [wJAppFormDomain]

/-- W-J-APP-FORM's evidence bundle on the nondependent domain — named.
    `hA` is the extracted introduction field (provenance-bound); `hPi` is
    composed by `HasTyT.pi` — the plain-side analogue of the future
    #7150 `.pi` arm; `hB`/`hTy` are the direct leaf-free sort typings the
    `ParRedT.app` congruence consumes. -/
structure AppFormEvidence (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A : Expr Nat) (ℓ : Level) where
  u : Level
  hA : HasTyT E n Γ A (.sort u)
  hPi : HasTyT E n Γ (.pi A (.sort ℓ)) (.sort (.imax u (.succ ℓ)))
  hB : HasTyT E n (.assumption A :: Γ) (.sort ℓ) (.sort (.succ ℓ))
  hTy : HasTyT E n Γ (.sort ℓ) (.sort (.succ ℓ))

/-- `hTy` at the `instantiate0 a (.sort ℓ)` the congruence asks for —
    identical on the nondependent domain. -/
def AppFormEvidence.hTyAt {Γ : LCtx} {A : Expr Nat} {ℓ : Level}
    (e : AppFormEvidence E n Γ A ℓ) (a : Expr Nat) :
    HasTyT E n Γ (instantiate0 a (.sort ℓ)) (.sort (.succ ℓ)) :=
  e.hTy

/-- the bundle built ONLY from the extractor's output — never from
    caller-supplied `hB`/`hPi`/`hTy`. The `i.A = A`/`i.B = .sort ℓ`
    premises come from `appLamIntro_spec` at the claimed pi index —
    provenance, not a generic "give me any `hB`/`hPi`/`hTy`". -/
def appFormEvidence {Γ : LCtx} {A : Expr Nat} {ℓ : Level}
    (i : AppLamIntro E n Γ) (hAi : i.A = A) (hBi : i.B = .sort ℓ) :
    AppFormEvidence E n Γ A ℓ := by
  obtain ⟨Ai, Bi, _body, ui, hA', _hb'⟩ := i
  have hAi' : Ai = A := hAi
  have hBi' : Bi = .sort ℓ := hBi
  subst Ai
  subst Bi
  exact ⟨ui, hA', .pi Γ A ui (.sort ℓ) (.succ ℓ) hA' (.sort _ ℓ),
    .sort _ ℓ, .sort Γ ℓ⟩

/-! ## (a) path lifting — each step of an actual multi-step path -/

/-- the function-position lifted step: the actual child step `h` at the
    FIXED `.pi A (.sort ℓ)` index becomes one `ParRedT.app` step at index
    `.sort ℓ` — `hc` is `TyConvT.refl` (index already the pi), the argument
    rides `ParRedT.refl`, `hB`/`hTy` are the direct sort typings,
    `hr` the composed right endpoint typing. -/
def appFunStep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (h : ParRedT PEq E n Γ f f' (.pi A (.sort ℓ)))
    (hf' : HasTyT E n Γ f' (.pi A (.sort ℓ))) :
    ParRedT PEq E n Γ (.app f a) (.app f' a) (.sort ℓ) :=
  .app Γ f f' a a A (.sort ℓ) (.pi A (.sort ℓ)) (.succ ℓ) (.succ ℓ)
    h (.refl Γ _) (.sort _ ℓ) (.sort _ ℓ) (.refl Γ a A ha)
    (.app Γ f' a A (.sort ℓ) hf' ha)

/-- the argument-position lifted step: the actual child step `h` becomes
    one `ParRedT.app` step with the function reflexive. `hr` types the
    right endpoint at `instantiate0 a' (.sort ℓ)`, which on this domain is
    the same `.sort ℓ` the left instantiation gives — the W-J-APP-INDEX
    tooth lives exactly in this spot (`appIndexOk`). -/
def appArgStep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ)))
    (h : ParRedT PEq E n Γ a a' A)
    (ha' : HasTyT E n Γ a' A) :
    ParRedT PEq E n Γ (.app f a) (.app f a') (.sort ℓ) :=
  .app Γ f f a a' A (.sort ℓ) (.pi A (.sort ℓ)) (.succ ℓ) (.succ ℓ)
    (.refl Γ f _ hf) (.refl Γ _) (.sort _ ℓ) (.sort _ ℓ) h
    (.app Γ f a' A (.sort ℓ) hf ha')

/-- the function path lifted through application congruence — the landed
    `parRedTStar_app_fun` specialized at `B := .sort ℓ`, composed directly
    (`instantiate0 a (.sort ℓ)` and `.sort ℓ` are the same term here;
    `hB`/`hTy` are the direct leaf-free sort typings, so no semantic
    bundle is needed). Every step of the actual child star maps to one
    `appFunStep` — `parRedTStar_app_fun_nondep_tail` shows the landed
    implementation builds literally this step; nothing collapses. -/
def parRedTStar_app_fun_nondep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (s : ParRedTStar PEq E n Γ f f' (.pi A (.sort ℓ))) :
    ParRedTStar PEq E n Γ (.app f a) (.app f' a) (.sort ℓ) :=
  parRedTStar_app_fun hPEq hΓ (.sort _ ℓ) (.sort _ ℓ) ha s

/-- the specialization IS the landed operator — composition, not a
    second implementation. -/
theorem parRedTStar_app_fun_nondep_eq
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (s : ParRedTStar PEq E n Γ f f' (.pi A (.sort ℓ))) :
    parRedTStar_app_fun_nondep hPEq hΓ ha s =
      parRedTStar_app_fun hPEq hΓ (.sort _ ℓ) (.sort _ ℓ) ha s := rfl

/-- the argument path lifted through application congruence — NEW. The
    landed `parRedTStar_app_arg` carries `convT_inst0_valueSort` per step
    under the full semantic bundle because `instantiate0` moves; on
    `B = .sort ℓ` the index is constant so the lift needs only the fixed
    function typing and the context well-formedness for the per-step right
    endpoint (`parRedT_hasTy_right`). -/
def parRedTStar_app_arg_nondep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ))) :
    ParRedTStar PEq E n Γ a a' A →
    ParRedTStar PEq E n Γ (.app f a) (.app f a') (.sort ℓ)
  | .refl _ _ _ h => .refl Γ _ _ (.app Γ f a A (.sort ℓ) hf h)
  | .tail h hs =>
      .tail (appArgStep hf h (parRedT_hasTy_right hPEq hΓ h))
        (parRedTStar_app_arg_nondep hPEq hΓ hf hs)

/-- the full congruence: function leg then argument leg at the fixed
    `.sort ℓ` index. -/
def parRedTStar_app_congr_nondep {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a a' A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (hsf : ParRedTStar PEq E n Γ f f' (.pi A (.sort ℓ)))
    (hsa : ParRedTStar PEq E n Γ a a' A) :
    ParRedTStar PEq E n Γ (.app f a) (.app f' a') (.sort ℓ) :=
  parRedTStar_trans
    (parRedTStar_app_fun_nondep hPEq hΓ ha hsf)
    (parRedTStar_app_arg_nondep hPEq hΓ (parRedTStar_right_typed hsf) hsa)

/-- the lazy function path, materialized then lifted — same operator. -/
def evParStar_app_fun_nondep {Γ : LCtx} {f f' a A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (ha : HasTyT E n Γ a A)
    (s : EvParStar R Γ f f' (.pi A (.sort ℓ))) :
    ParRedTStar (PEqLeafT E n) E n Γ (.app f a) (.app f' a) (.sort ℓ) :=
  parRedTStar_app_fun_nondep peqLeafT_typed hΓ ha (s.val hcl hinst)

/-- the lazy argument path, materialized then lifted. -/
def evParStar_app_arg_nondep {Γ : LCtx} {f a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (hf : HasTyT E n Γ f (.pi A (.sort ℓ)))
    (s : EvParStar R Γ a a' A) :
    ParRedTStar (PEqLeafT E n) E n Γ (.app f a) (.app f a') (.sort ℓ) :=
  parRedTStar_app_arg_nondep peqLeafT_typed hΓ hf (s.val hcl hinst)

/-! ## exact size equations -/

/-- step count of a materialized star — the honest path size. A lift is
    exact iff it preserves this count; a one-step stand-in changes it. -/
def parRedTStar_steps {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {a b T : Expr Nat} :
    ParRedTStar PEq E n Γ a b T → Nat
  | .refl .. => 0
  | .tail _ hs => parRedTStar_steps hs + 1

theorem parRedTStar_steps_trans {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {a b c T : Expr Nat}
    (s₁ : ParRedTStar PEq E n Γ a b T) (s₂ : ParRedTStar PEq E n Γ b c T) :
    parRedTStar_steps (parRedTStar_trans s₁ s₂) =
      parRedTStar_steps s₁ + parRedTStar_steps s₂ := by
  induction s₁ with
  | refl _ => exact (Nat.zero_add _).symm
  | tail h hs ih =>
      show parRedTStar_steps (parRedTStar_trans hs s₂) + 1 =
        parRedTStar_steps hs + 1 + parRedTStar_steps s₂
      rw [ih]; omega

/-- per-case unfold: the specialized function lift on a `tail` is one
    `appFunStep` consed onto the recursive lift — propositionally, since
    the landed `parRedTStar_app_fun` builds literally this step
    (`instantiate0 a (.sort ℓ)` reduces to `.sort ℓ`). -/
theorem parRedTStar_app_fun_nondep_tail
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' b a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (h : ParRedT PEq E n Γ f b (.pi A (.sort ℓ)))
    (hs : ParRedTStar PEq E n Γ b f' (.pi A (.sort ℓ))) :
    parRedTStar_app_fun_nondep hPEq hΓ ha (.tail h hs) =
      .tail (appFunStep ha h (parRedT_hasTy_right hPEq hΓ h))
        (parRedTStar_app_fun_nondep hPEq hΓ ha hs) := by
  simp only [parRedTStar_app_fun_nondep, parRedTStar_app_fun, appFunStep,
    instantiate0_sort]

/-- size equation, function side: the lifted star has EXACTLY the child's
    step count — never a single-step stand-in. -/
theorem parRedTStar_app_fun_nondep_steps
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A) :
    (s : ParRedTStar PEq E n Γ f f' (.pi A (.sort ℓ))) →
    parRedTStar_steps (parRedTStar_app_fun_nondep hPEq hΓ ha s) =
      parRedTStar_steps s
  | .refl .. => by
      simp only [parRedTStar_app_fun_nondep, parRedTStar_app_fun,
        parRedTStar_steps]
  | .tail h hs => by
      rw [parRedTStar_app_fun_nondep_tail hPEq hΓ ha h hs]
      simp only [parRedTStar_steps,
        parRedTStar_app_fun_nondep_steps hPEq hΓ ha hs]

/-- size equation, argument side. -/
theorem parRedTStar_app_arg_nondep_steps
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ))) :
    (s : ParRedTStar PEq E n Γ a a' A) →
    parRedTStar_steps (parRedTStar_app_arg_nondep hPEq hΓ hf s) =
      parRedTStar_steps s
  | .refl .. => rfl
  | .tail h hs => by
      simp only [parRedTStar_app_arg_nondep, parRedTStar_steps,
        parRedTStar_app_arg_nondep_steps hPEq hΓ hf hs]

/-- size equation, full congruence: counts add over the trans. -/
theorem parRedTStar_app_congr_nondep_steps
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx}
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hΓ : CtxWfT E n Γ) {f f' a a' A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (hsf : ParRedTStar PEq E n Γ f f' (.pi A (.sort ℓ)))
    (hsa : ParRedTStar PEq E n Γ a a' A) :
    parRedTStar_steps (parRedTStar_app_congr_nondep hPEq hΓ ha hsf hsa) =
      parRedTStar_steps hsf + parRedTStar_steps hsa := by
  simp only [parRedTStar_app_congr_nondep, parRedTStar_steps_trans,
    parRedTStar_app_fun_nondep_steps, parRedTStar_app_arg_nondep_steps]

/-! ## exact leaf equations -/

/-- leaf equation, function-side step — the `sumList` form: the lifted
    step's J-request sites are the child's `.inl` plus the reflexive
    argument's `.inr`. -/
theorem occurrences_appFunStep_expand {Γ : LCtx} {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (h : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A (.sort ℓ)))
    (hf' : HasTyT E n Γ f' (.pi A (.sort ℓ))) :
    occurrences (appFunStep ha h hf') =
      (occurrences h).map Sum.inl ++
        (occurrences (.refl Γ a A ha : ParRedT (PEqLeafT E n) E n Γ a a A)).map Sum.inr := rfl

/-- leaf equation, function-side step: exactly the child's sites. -/
theorem occurrences_appFunStep {Γ : LCtx} {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A)
    (h : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A (.sort ℓ)))
    (hf' : HasTyT E n Γ f' (.pi A (.sort ℓ))) :
    occurrences (appFunStep ha h hf') = (occurrences h).map Sum.inl := by
  rw [occurrences_appFunStep_expand,
    show occurrences (ParRedT.refl Γ a A ha : ParRedT (PEqLeafT E n) E n Γ a a A) = [] from rfl,
    List.map_nil, List.append_nil]

/-- leaf equation, argument-side step — the `sumList` form. -/
theorem occurrences_appArgStep_expand {Γ : LCtx} {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ)))
    (h : ParRedT (PEqLeafT E n) E n Γ a a' A)
    (ha' : HasTyT E n Γ a' A) :
    occurrences (appArgStep hf h ha') =
      (occurrences (.refl Γ f _ hf : ParRedT (PEqLeafT E n) E n Γ f f (.pi A (.sort ℓ)))).map Sum.inl ++
        (occurrences h).map Sum.inr := rfl

/-- leaf equation, argument-side step: exactly the child's sites. -/
theorem occurrences_appArgStep {Γ : LCtx} {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ)))
    (h : ParRedT (PEqLeafT E n) E n Γ a a' A)
    (ha' : HasTyT E n Γ a' A) :
    occurrences (appArgStep hf h ha') = (occurrences h).map Sum.inr := by
  rw [occurrences_appArgStep_expand,
    show occurrences
        (ParRedT.refl Γ f _ hf : ParRedT (PEqLeafT E n) E n Γ f f (.pi A (.sort ℓ))) = [] from rfl,
    List.map_nil, List.nil_append]

/-- a materialized step occurrence bundled with its step — the
    J-request-site list of a whole star; steps at varying endpoints share
    the fixed index `T`. -/
abbrev StepOcc (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T : Expr Nat) : Type :=
  Σ' (a b : Expr Nat) (h : ParRedT (PEqLeafT E n) E n Γ a b T), Occ h

/-- per-step occurrences of a materialized star, in order. -/
def parRedTStar_occList {Γ : LCtx} {a b T : Expr Nat} :
    ParRedTStar (PEqLeafT E n) E n Γ a b T → List (StepOcc E n Γ T)
  | .refl .. => []
  | .tail h hs =>
      (occurrences h).map (fun o => ⟨_, _, h, o⟩) ++ parRedTStar_occList hs

/-- whole-star leaf equation, function side: the lifted star's
    J-request-site list IS the child's, step-for-step `.inl`-embedded. -/
theorem parRedTStar_app_fun_nondep_occList
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f f' a A : Expr Nat} {ℓ : Level}
    (ha : HasTyT E n Γ a A) :
    (s : ParRedTStar (PEqLeafT E n) E n Γ f f' (.pi A (.sort ℓ))) →
    parRedTStar_occList (parRedTStar_app_fun_nondep peqLeafT_typed hΓ ha s) =
      (parRedTStar_occList s).map fun ⟨_, _, h, o⟩ =>
        ⟨_, _, appFunStep ha h (parRedT_hasTy_right peqLeafT_typed hΓ h), Sum.inl o⟩
  | .refl .. => by
      simp [parRedTStar_app_fun_nondep, parRedTStar_app_fun,
        parRedTStar_occList]
  | .tail h hs => by
      rw [parRedTStar_app_fun_nondep_tail peqLeafT_typed hΓ ha]
      simp only [parRedTStar_occList, occurrences_appFunStep,
        List.map_append, List.map_map,
        parRedTStar_app_fun_nondep_occList hΓ ha hs]
      rfl

/-- whole-star leaf equation, argument side. -/
theorem parRedTStar_app_arg_nondep_occList
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a a' A : Expr Nat} {ℓ : Level}
    (hf : HasTyT E n Γ f (.pi A (.sort ℓ))) :
    (s : ParRedTStar (PEqLeafT E n) E n Γ a a' A) →
    parRedTStar_occList (parRedTStar_app_arg_nondep peqLeafT_typed hΓ hf s) =
      (parRedTStar_occList s).map fun ⟨_, _, h, o⟩ =>
        ⟨_, _, appArgStep hf h (parRedT_hasTy_right peqLeafT_typed hΓ h), Sum.inr o⟩
  | .refl .. => by
      simp [parRedTStar_app_arg_nondep, parRedTStar_occList]
  | .tail h hs => by
      simp only [parRedTStar_app_arg_nondep, parRedTStar_occList,
        occurrences_appArgStep, List.map_append, List.map_map,
        parRedTStar_app_arg_nondep_occList hΓ hf hs]
      rfl

/-! ## packaging — the actual child valleys' two paths lifted -/

/-- the four materialized legs of `app f a ⇉ app Nf Na ⇇ app f' a'` —
    the actual child valleys' two multi-step paths, lifted. -/
structure AppLegs (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f Nf f' a Na a' : Expr Nat) (ℓ : Level) where
  leftFun : ParRedTStar (PEqLeafT E n) E n Γ (.app f a) (.app Nf a) (.sort ℓ)
  leftArg : ParRedTStar (PEqLeafT E n) E n Γ (.app Nf a) (.app Nf Na) (.sort ℓ)
  rightFun : ParRedTStar (PEqLeafT E n) E n Γ (.app f' a') (.app Nf a') (.sort ℓ)
  rightArg : ParRedTStar (PEqLeafT E n) E n Γ (.app Nf a') (.app Nf Na) (.sort ℓ)

/-- lift the ACTUAL child valleys' legs through the congruence. The
    function valley's endpoint typings and the argument valley's endpoint
    typings are the ones carried by the valleys themselves — the
    centre-middle typings come off `parRedTStar_right_typed`, never
    fabricated. -/
def appValleyLegs {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ)
    (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    AppLegs E n Γ f vf.N f' a va.N a' ℓ where
  leftFun := parRedTStar_app_fun_nondep peqLeafT_typed hΓ
    (va.ty₁.val hcl hinst) (vf.left.val hcl hinst)
  leftArg := parRedTStar_app_arg_nondep peqLeafT_typed hΓ
    (parRedTStar_right_typed (vf.left.val hcl hinst)) (va.left.val hcl hinst)
  rightFun := parRedTStar_app_fun_nondep peqLeafT_typed hΓ
    (va.ty₂.val hcl hinst) (vf.right.val hcl hinst)
  rightArg := parRedTStar_app_arg_nondep peqLeafT_typed hΓ
    (parRedTStar_right_typed (vf.right.val hcl hinst)) (va.right.val hcl hinst)

/-- the left leg assembled: `app f a → app Nf Na`. -/
def AppLegs.leftLeg {Γ : LCtx} {f Nf f' a Na a' : Expr Nat} {ℓ : Level}
    (legs : AppLegs E n Γ f Nf f' a Na a' ℓ) :
    ParRedTStar (PEqLeafT E n) E n Γ (.app f a) (.app Nf Na) (.sort ℓ) :=
  parRedTStar_trans legs.leftFun legs.leftArg

/-- the right leg assembled: `app f' a' → app Nf Na`. -/
def AppLegs.rightLeg {Γ : LCtx} {f Nf f' a Na a' : Expr Nat} {ℓ : Level}
    (legs : AppLegs E n Γ f Nf f' a Na a' ℓ) :
    ParRedTStar (PEqLeafT E n) E n Γ (.app f' a') (.app Nf Na) (.sort ℓ) :=
  parRedTStar_trans legs.rightFun legs.rightArg

theorem appValleyLegs_leftFun_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).leftFun =
      parRedTStar_steps (vf.left.val hcl hinst) :=
  parRedTStar_app_fun_nondep_steps peqLeafT_typed hΓ _ _

theorem appValleyLegs_leftArg_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).leftArg =
      parRedTStar_steps (va.left.val hcl hinst) :=
  parRedTStar_app_arg_nondep_steps peqLeafT_typed hΓ _ _

theorem appValleyLegs_rightFun_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).rightFun =
      parRedTStar_steps (vf.right.val hcl hinst) :=
  parRedTStar_app_fun_nondep_steps peqLeafT_typed hΓ _ _

theorem appValleyLegs_rightArg_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).rightArg =
      parRedTStar_steps (va.right.val hcl hinst) :=
  parRedTStar_app_arg_nondep_steps peqLeafT_typed hΓ _ _

/-- the assembled left leg has exactly the two child legs' step count. -/
theorem appValleyLegs_leftLeg_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).leftLeg =
      parRedTStar_steps (vf.left.val hcl hinst) +
        parRedTStar_steps (va.left.val hcl hinst) := by
  simp only [AppLegs.leftLeg, parRedTStar_steps_trans,
    appValleyLegs_leftFun_steps, appValleyLegs_leftArg_steps]

/-- the assembled right leg has exactly the two child legs' step count. -/
theorem appValleyLegs_rightLeg_steps {Γ : LCtx} {f f' a a' A : Expr Nat} {ℓ : Level}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n Γ) (vf : Valley R Γ f f' (.pi A (.sort ℓ)))
    (va : Valley R Γ a a' A) :
    parRedTStar_steps (appValleyLegs hcl hinst hΓ vf va).rightLeg =
      parRedTStar_steps (vf.right.val hcl hinst) +
        parRedTStar_steps (va.right.val hcl hinst) := by
  simp only [AppLegs.rightLeg, parRedTStar_steps_trans,
    appValleyLegs_rightFun_steps, appValleyLegs_rightArg_steps]

/-! ## the check pairs (teeth, §7) -/

/-- shipped provenance tooth — the claimed extracted fields must line up
    with the ORIGINAL introduction's actual fields: the claimed domain
    typing's subject/context IS the intro's binder/context, and the
    claimed body typing's subject/context IS the intro's body under the
    binder. A forged field (wrong stored body, foreign domain) fails. -/
def appIntroOk {Γ : LCtx} {f T : Expr Nat} (hty : HasTyT E n Γ f T)
    {ΓA ΓB : LCtx} {A' B' TA TB : Expr Nat}
    (_claimA : HasTyT E n ΓA A' TA) (_claimB : HasTyT E n ΓB B' TB) : Bool :=
  match appLamIntro hty with
  | some i =>
      decide (A' = i.A) && decide (ΓA = Γ) &&
        decide (B' = i.body) && decide (ΓB = .assumption i.A :: Γ)
  | none => false

/-- the `_noTooth` twin drops the field match — any claim against a
    lam-shaped typing passes. -/
def appIntroOk_noTooth {Γ : LCtx} {f T : Expr Nat} (hty : HasTyT E n Γ f T)
    {ΓA ΓB : LCtx} {A' B' TA TB : Expr Nat}
    (_claimA : HasTyT E n ΓA A' TA) (_claimB : HasTyT E n ΓB B' TB) : Bool :=
  (appLamIntro hty).isSome

/-- shipped index tooth — the step index is the LEFT argument's
    instantiation `instantiate0 a B` (W-J-APP-INDEX's equation). -/
def appIndexOk (a _a' T B : Expr Nat) : Bool :=
  decide (T = instantiate0 a B)

/-- the `_noTooth` twin also accepts the RIGHT instantiation — the
    "swapping the right instantiation index" mutant; on dependent `B`
    (e.g. `.bvar 0`) the two differ. -/
def appIndexOk_noTooth (a a' T B : Expr Nat) : Bool :=
  decide (T = instantiate0 a B) || decide (T = instantiate0 a' B)

/-- shipped codomain tooth — `B` must be a literal sort (the nondependent
    gate). A `.bvar 0` codomain makes the two instantiation indices
    genuinely differ. -/
def appCodomainOk (B : Expr Nat) : Bool := wJAppIndexDomain B

/-- the `_noTooth` twin accepts any codomain. -/
def appCodomainOk_noTooth (_B : Expr Nat) : Bool := true

/-- shipped form tooth — W-J-APP-FORM's independent syntactic domain. -/
def appFormOk {Γ : LCtx} {f T : Expr Nat} (hty : HasTyT E n Γ f T) : Bool :=
  wJAppFormDomain hty

/-- the `_noTooth` twin accepts any typing as formation evidence — a
    constant-typed function (no introduction subtree to extract from)
    passes it. -/
def appFormOk_noTooth {Γ : LCtx} {f T : Expr Nat} (_hty : HasTyT E n Γ f T) : Bool :=
  true

/-- shipped path tooth — the lifted star's step count is EXACTLY the
    child star's; the one-step stand-in fails. -/
def appStepsOk {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {a b T a₂ b₂ T₂ : Expr Nat}
    (lifted : ParRedTStar PEq E n Γ a b T)
    (child : ParRedTStar PEq E n Γ a₂ b₂ T₂) : Bool :=
  decide (parRedTStar_steps lifted = parRedTStar_steps child)

/-- the `_noTooth` twin also accepts a collapsed one-step path. -/
def appStepsOk_noTooth {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {a b T a₂ b₂ T₂ : Expr Nat}
    (lifted : ParRedTStar PEq E n Γ a b T)
    (child : ParRedTStar PEq E n Γ a₂ b₂ T₂) : Bool :=
  decide (parRedTStar_steps lifted = parRedTStar_steps child) ||
    decide (parRedTStar_steps lifted = 1)

#print axioms appLamIntro
#print axioms appFormEvidence
#print axioms parRedTStar_app_fun_nondep
#print axioms parRedTStar_app_arg_nondep
#print axioms parRedTStar_app_congr_nondep
#print axioms appValleyLegs
#print axioms parRedTStar_app_fun_nondep_occList
#print axioms parRedTStar_app_arg_nondep_occList

end Rcic.Declarative
