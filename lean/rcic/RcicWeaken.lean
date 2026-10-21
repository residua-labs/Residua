/-
RCIC weakening construction — the ruling witness for knife 2's third
named wall, and the full context-insertion transport.

THE WALL DOES NOT EXIST. The reported failure ("implicit E/n cannot be
inferred in pattern positions; Type-valued judgments force a broken
∃/Nonempty bridge") does not reproduce: every hard case below — bvar
through the CtxMorph lookups, beta with SubstCalc rewriting INTO the
type indices, lam recursing at cutoff c+1, app through the instantiate0
commutation — elaborates in plain Type-valued mutual defs with implicit
E/n. Options A (Prop-valued judgments), B (custom eliminators), and
C (mirror judgments) are all REJECTED: no design change.

The real discipline, stated once:
  * constructions live in Type and chain as defs (this file);
  * `Nonempty` is a TERMINAL interface wrapper only — the axiom
    whitelist has no Classical.choice, so Prop→Type extraction is
    impossible by budget, and a chain through Nonempty is the actual
    failure that was misread as an inference wall;
  * recursive calls name their cutoff explicitly (`(c := c+1)`).

A REAL finding the construction forced out: under the transcription as
landed, weakening is UNPROVABLE at `const`/`delta` — nothing makes an
environment member's type or body closed, so `lift c 1 m.mtype = m.mtype`
is not available. 02 §6's members are CHECKED members; the transcription
does not yet carry that invariant. It enters here as the explicit
premise `EnvClosed`. IotaLift and LitLift are theorems (`iotaLift`,
`litLift` — `natExpand` is closed). LitPreserve was discharged
VACUOUSLY in segment 7a (00 §19.7 E-LitP: HasTy then had no lit rule)
and is discharged FOR REAL since DT-017 landed `HasTy.lit`
(`litPreserve`, 00 §20.11); `hasTyWeaken`'s own `.lit` arm transports
through `natExpand_lift`.

INFRASTRUCTURE (M-010): DT-004's interface statement (quoting 02 §14)
remains the batch's delivery; it will be a one-line wrapper over
`hasTyWeaken`.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicCtxMorph
import rcic.RcicIota
import rcic.RcicEnv

namespace Rcic.Declarative

/-- Lift-transport for the 08-owned literal interface. Discharged:
`natExpand` is closed. -/
def LitLift : Type :=
  ∀ t exp, LiteralExpansion t exp →
    ∀ c, LiteralExpansion t (lift c 1 exp)

def litLift : LitLift
  | t, _, .of _, c => by
      change LiteralExpansion t (lift c 1 (natExpand t))
      rw [natExpand_lift]
      exact .of t

mutual

def stepWeaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    {c : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Step E n Γ a b → Step E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
  | c, _, _, _, .beta Γ A body arg => by
      have h := lift_instantiate_low 1 c 0 arg (by omega) body
      simp only [lift, instantiate0]
      rw [h]
      exact .beta _ _ _ _
  | c, _, _, _, .zeta Γ A value body => by
      have h := lift_instantiate_low 1 c 0 value (by omega) body
      simp only [lift, instantiate0]
      rw [h]
      exact .zeta _ _ _ _
  | c, _, _, _, .zetaLocal Γ i v hv => by
      by_cases hic : i < c
      · have := lookupValue_insertAt_lt d hic hv
        simp only [lift, if_neg (by omega : ¬ c ≤ i)]
        exact .zetaLocal _ _ _ this
      · have := lookupValue_insertAt_ge d (by omega : c ≤ i) hv
        simp only [lift, if_pos (by omega : c ≤ i)]
        exact .zetaLocal _ _ _ this
  | c, _, _, _, .delta Γ r ls m b hres hbody htr => by
      -- 00 §20.6: the conclusion index is now `instantiateLevels ls b`,
      -- so the closedness fact has to be read through the instantiation
      -- (`envWf_closed_inst`, RcicEnv) rather than at the raw body.
      have hb := (envWf_closed_inst hE r m hres).2 b hbody ls c
      simp only [lift]
      rw [hb]
      exact .delta _ r ls m b hres hbody htr
  | c, _, _, _, .iota Γ lhs rhs h => by
      exact .iota _ _ _ (iotaLift E lhs rhs h c)
  | c, _, _, _, .lit Γ t exp h => by
      simp only [lift]
      exact .lit _ _ _ (litLift t exp h c)

def convWeaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    {c : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Conv E n Γ a b → Conv E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
  | c, _, _, _, .refl _ a => .refl _ _
  | c, _, _, _, .symm _ _ _ h => .symm _ _ _ (convWeaken d hE h)
  | c, _, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (convWeaken d hE h1) (convWeaken d hE h2)
  | c, _, _, _, .step _ _ _ hs => .step _ _ _ (stepWeaken d hE hs)
  | c, _, _, _, .app _ _ _ _ _ h1 h2 => by
      simp only [lift]
      exact .app _ _ _ _ _ (convWeaken d hE h1) (convWeaken d hE h2)
  | c, _, _, _, .lam _ A _ _ _ hA hb => by
      simp only [lift]
      have hb' := convWeaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ _ _ _ (convWeaken d hE hA) hb'
  | c, _, _, _, .pi _ A _ _ _ hA hb => by
      simp only [lift]
      have hb' := convWeaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .pi _ _ _ _ _ (convWeaken d hE hA) hb'
  | c, _, _, _, .letE _ A _ v _ _ _ hA hv hb => by
      simp only [lift]
      have hb' := convWeaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .letE _ _ _ _ _ _ _ (convWeaken d hE hA)
        (convWeaken d hE hv) hb'
  | c, _, _, _, .sorts _ l1 l2 h => by
      simp only [lift]; exact .sorts _ l1 l2 h
  | c, _, _, _, .consts _ r ls ls' h => by
      simp only [lift]; exact .consts _ r ls ls' h
  | c, _, _, _, .eta _ f A B hh => by
      have hf' := hasTyWeaken d hE (c := c) hh
      simp only [lift] at hf' ⊢
      have hp : lift (c+1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [lift_lift_permute 1 1 c 0 (by omega),
            show 1 + c = c + 1 from by omega]
      rw [show (if c + 1 ≤ 0 then Expr.bvar (0+1) else Expr.bvar 0) = Expr.bvar 0
            from by simp, hp]
      exact .eta _ _ _ _ hf'
  | c, _, _, _, .irr _ P p q hP hp hq => by
      have hP' := hasTyWeaken d hE (c := c) hP
      simp only [lift] at hP'
      exact .irr _ _ _ _ hP' (hasTyWeaken d hE hp) (hasTyWeaken d hE hq)

def hasTyWeaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    {c : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTy E n Γ e A → HasTy E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  | c, _, _, _, .sort Γ l => by
      simp only [lift]; exact .sort _ l
  | c, _, _, _, .bvar Γ i A h => by
      by_cases hic : i < c
      · have := lookupType_insertAt_lt d hic h
        simp only [lift, if_neg (by omega : ¬ c ≤ i)]
        exact .bvar _ _ _ this
      · have := lookupType_insertAt_ge d (by omega : c ≤ i) h
        simp only [lift, if_pos (by omega : c ≤ i)]
        exact .bvar _ _ _ this
  | c, _, _, _, .const Γ r ls m hres hlen hwf => by
      -- 00 §20.6: the ascribed type is now `instantiateLevels ls m.mtype`.
      have hm := (envWf_closed_inst hE r m hres).1 ls c
      simp only [lift]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | c, _, _, _, .pi Γ A u B v hA hB => by
      simp only [lift]
      have hB' := hasTyWeaken d hE (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl, lift] at hB'
      have hA' := hasTyWeaken d hE (c := c) hA
      simp only [lift] at hA'
      exact .pi _ _ u _ v hA' hB'
  | c, _, _, _, .lam Γ A u body B hA hbody => by
      simp only [lift]
      have hA' := hasTyWeaken d hE (c := c) hA
      simp only [lift] at hA'
      have hb' := hasTyWeaken d hE (c := c + 1) hbody
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ u _ _ hA' hb'
  | c, _, _, _, .app Γ f a A B hf ha => by
      have hf' := hasTyWeaken d hE (c := c) hf
      have ha' := hasTyWeaken d hE (c := c) ha
      simp only [lift] at hf'
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .app _ _ _ _ _ hf' ha'
  | c, _, _, _, .letE Γ A u value B hA hv hb => by
      have hA' := hasTyWeaken d hE (c := c) hA
      simp only [lift] at hA'
      have hv' := hasTyWeaken d hE (c := c) hv
      have hb' := hasTyWeaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .letE _ _ u _ _ hA' hv' hb'
  | c, _, _, _, .conv Γ e A B h hc => by
      exact .conv _ _ _ _ (hasTyWeaken d hE h) (convWeaken d hE hc)
  | c, _, _, _, .lit _Γ t _T hexp => by
      have hexp' := hasTyWeaken d hE (c := c) hexp
      rw [natExpand_lift c 1 t] at hexp'
      simp only [lift]
      exact .lit _ _ _ hexp'

end

/-- 04 EG-023: a closed typing in the empty context transports to any
Γ, same n. Fold: `hasTyWeaken` at cutoff 0 (the ctxWfLookupValue
template). Closedness rewrites `lift 0 1`. -/
def hasTyClosedWeaken {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    {e A : Expr Nat}
    (hcl : ∀ k, lift k 1 e = e)
    (hclA : ∀ k, lift k 1 A = A) :
    (Γ : LCtx) → HasTy E n [] e A → HasTy E n Γ e A
  | [], h => h
  | d :: Γ, h => by
      have hΓ := hasTyClosedWeaken hE hcl hclA Γ h
      have hw := hasTyWeaken d hE (c := 0) hΓ
      simp only [insertAt_zero] at hw
      rw [hcl 0, hclA 0] at hw
      exact hw

end Rcic.Declarative
