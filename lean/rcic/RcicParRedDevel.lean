/-
RCIC ParRed, piece 6 of 7: `develWf` (fuel-bounded complete
development) and the star-congruence scaffolding.  QUARANTINE.

Sealed, but on the abandoned Takahashi complete-development route
(attempt 51 ruling, recorded at the head of the pairwise-diamond
section in `RcicParRedIota`); nothing in `RcicParRedDiamond` imports
it.  Four of its star-congruence lemmas (`parRedStar_lam_congr`,
`parRedStar_pi_congr`, `parRedStar_app_congr`,
`parRedStar_letE_congr`) are load-bearing elsewhere and are
consumed from here.  Do not read "sealed" as "load-bearing for
the diamond".

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.
-/
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicParRedWeight
import rcic.RcicParRedSortWall
import rcic.RcicParRedSubst

namespace Rcic.Declarative

/-- Fuel-bounded complete development.
`fuel` budgets delta (EnvWf rank); `maj` budgets iota (ctor major
size); bvar unfolds via `getLet` tail (letsCount drops). Let bodies
develop under an assumption so letsCount does not grow. -/
def develWfGo {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (e : Expr Nat) : Expr Nat :=
  match e with
  | .sort l => .sort l
  | .lit t => natExpand t
  | .const r ls =>
      match hmem : E.members r with
      | none => .const r ls
      | some m =>
          if htr : transparent m.mclass = true then
            match m.body with
            | none => .const r ls
            -- 00 §20.6: the delta reduct is `instantiateLevels ls b`, so
            -- the development recurses on the INSTANTIATED body. The
            -- measure is unchanged (`exprSize_instantiateLevels`) and
            -- these arms decrease on `fuel` anyway.
            | some b =>
                if hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel then
                  develWfGo hE (envWf_rank (envWf_of_member hE hmem).2.1)
                    cwt maj Γ (instantiateLevels ls b)
                else
                  match fuel with
                  | 0 => instantiateLevels ls b
                  | fuel'+1 =>
                      develWfGo hE fuel' cwt maj Γ (instantiateLevels ls b)
          else .const r ls
  | .bvar i =>
      match hg : getLet Γ i with
      | none => .bvar i
      | some (stored, tail) =>
          lift 0 (i + 1) (develWfGo hE fuel cwt maj tail stored)
  | .app f a =>
      match iotaReductCert E (.app f a) with
      | some ⟨w, _hlhs⟩ =>
          if hlt : exprSize (ctorMajor w) < maj then
            develWfGo hE fuel cwt (exprSize (ctorMajor w)) Γ (iotaRhsOf w)
          else iotaRhsOf w
      | none =>
          let f' := develWfGo hE fuel cwt maj Γ f
          let a' := develWfGo hE fuel cwt maj Γ a
          match f' with
          | .lam _ b => instantiate0 a' b
          | _ => .app f' a'
  | .lam A b =>
      .lam (develWfGo hE fuel cwt maj Γ A)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
  | .pi A B =>
      .pi (develWfGo hE fuel cwt maj Γ A)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)
  | .letE A v b =>
      instantiate0 (develWfGo hE fuel cwt maj Γ v)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
termination_by (fuel, letsCount Γ, cwt, maj, exprSize e)
decreasing_by
  simp_wf
  · exact Prod.Lex.left _ _ hlt
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
  · refine Prod.Lex.right fuel
      (Prod.Lex.left _ _ (getLet_letsCount hg))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.left _ _ hlt)))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_app_left _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_app_right _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_lam_dom _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_lam_body _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_pi_dom _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_pi_body _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_let_val _ _ _))))
  · refine Prod.Lex.right fuel
      (Prod.Lex.right (letsCount Γ)
        (Prod.Lex.right cwt (Prod.Lex.right maj (exprSize_let_body _ _ _))))

/-- Wrapper: fuel = admission rank; `cwt`/`maj` saturate lets and iota. -/
def develWf {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (e : Expr Nat) : Expr Nat :=
  develWfGo hE (envWf_rank hE) (letsCount Γ + exprSize e + 1)
    (exprSize e + 1) Γ e

theorem develWfGo_sort {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (l : Level) :
    develWfGo hE fuel cwt maj Γ (.sort l) = .sort l := by
  rw [develWfGo]

theorem develWf_sort {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (l : Level) :
    develWf hE Γ (.sort l) = .sort l := by
  rw [develWf, develWfGo_sort]

theorem develWfGo_lit {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (t : Nat) :
    develWfGo hE fuel cwt maj Γ (.lit t) = natExpand t := by
  rw [develWfGo]

theorem develWf_lit {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (t : Nat) :
    develWf hE Γ (.lit t) = natExpand t := by
  rw [develWf, develWfGo_lit]

theorem develWfGo_bvar_none {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) {Γ : LCtx} {i : Nat}
    (h : getLet Γ i = none) :
    develWfGo hE fuel cwt maj Γ (.bvar i) = .bvar i := by
  unfold develWfGo
  rw [h]

theorem develWfGo_bvar_some {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) {Γ : LCtx} {i : Nat} {stored : Expr Nat}
    {tail : LCtx} (h : getLet Γ i = some (stored, tail)) :
    develWfGo hE fuel cwt maj Γ (.bvar i) =
      lift 0 (i + 1) (develWfGo hE fuel cwt maj tail stored) := by
  conv => lhs; unfold develWfGo; rw [h]

/-- c=0 bvar case of weakening devel: inserting a decl at the front
shifts a bvar and walks `getLet` one extra cons. Tails coincide, so
no recursive lift of `stored` is required. -/
theorem develWfGo_lift0_bvar {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (d : LocalDecl) (fuel cwt maj : Nat) (Γ : LCtx) (i : Nat) :
    develWfGo hE fuel cwt maj (d :: Γ) (.bvar (Nat.succ i)) =
      lift 0 1 (develWfGo hE fuel cwt maj Γ (.bvar i)) := by
  cases hg : getLet Γ i with
  | none =>
      have hnone : getLet (d :: Γ) (Nat.succ i) = none := by
        rw [getLet_cons_succ, hg]
      rw [develWfGo_bvar_none (h := hnone), develWfGo_bvar_none (h := hg)]
      simp only [lift]
      split
      · rfl
      · omega
  | some stored_tail =>
      match stored_tail with
      | (stored, tail) =>
          have hsome : getLet (d :: Γ) (Nat.succ i) = some (stored, tail) := by
            rw [getLet_cons_succ, hg]
          rw [develWfGo_bvar_some (h := hsome), develWfGo_bvar_some (h := hg)]
          exact (lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0)
            (Nat.zero_le _)
            (develWfGo hE fuel cwt maj tail stored)).symm

/-- iota arm of `develWf` returns the certified rhs. -/
theorem develWf_app_iota {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) {f a : Expr Nat} {w : IotaWitness E}
    {hlhs : iotaLhsOf w = .app f a}
    (h : iotaReductCert E (.app f a) = some ⟨w, hlhs⟩) :
    develWf hE Γ (.app f a) =
      if hlt : exprSize (ctorMajor w) < exprSize (.app f a) + 1 then
        develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.app f a) + 1)
          (exprSize (ctorMajor w)) Γ (iotaRhsOf w)
      else iotaRhsOf w := by
  rw [develWf, develWfGo]
  simp [h]

/-! ### Star congruence (Takahashi scaffolding). -/

def parRedStar_lam_dom {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A A' b : Expr Nat} →
    ParRedStar E n Γ A A' →
    ParRedStar E n Γ (.lam A b) (.lam A' b)
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.lam _ _ _ _ _ h (.refl _ _)) (parRedStar_lam_dom hs)

def parRedStar_lam_body {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A b b' : Expr Nat} →
    ParRedStar E n (.assumption A :: Γ) b b' →
    ParRedStar E n Γ (.lam A b) (.lam A b')
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.lam _ _ _ _ _ (.refl _ _) h) (parRedStar_lam_body hs)

def parRedStar_lam_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' : Expr Nat}
    (hA : ParRedStar E n Γ A A')
    (hb : ParRedStar E n (.assumption A :: Γ) b b') :
    ParRedStar E n Γ (.lam A b) (.lam A' b') :=
  parRedStar_trans (parRedStar_lam_dom hA)
    (parRedStar_lam_body (parRedStar_replace_assump hb))

def parRedStar_pi_dom {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A A' B : Expr Nat} →
    ParRedStar E n Γ A A' →
    ParRedStar E n Γ (.pi A B) (.pi A' B)
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.pi _ _ _ _ _ h (.refl _ _)) (parRedStar_pi_dom hs)

def parRedStar_pi_body {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A B B' : Expr Nat} →
    ParRedStar E n (.assumption A :: Γ) B B' →
    ParRedStar E n Γ (.pi A B) (.pi A B')
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.pi _ _ _ _ _ (.refl _ _) h) (parRedStar_pi_body hs)

def parRedStar_pi_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat}
    (hA : ParRedStar E n Γ A A')
    (hB : ParRedStar E n (.assumption A :: Γ) B B') :
    ParRedStar E n Γ (.pi A B) (.pi A' B') :=
  parRedStar_trans (parRedStar_pi_dom hA)
    (parRedStar_pi_body (parRedStar_replace_assump hB))

def parRedStar_app_fun {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {f f' a : Expr Nat} →
    ParRedStar E n Γ f f' →
    ParRedStar E n Γ (.app f a) (.app f' a)
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.app _ _ _ _ _ h (.refl _ _)) (parRedStar_app_fun hs)

def parRedStar_app_arg {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {f a a' : Expr Nat} →
    ParRedStar E n Γ a a' →
    ParRedStar E n Γ (.app f a) (.app f a')
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .tail h hs =>
      .tail (.app _ _ _ _ _ (.refl _ _) h) (parRedStar_app_arg hs)

def parRedStar_app_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' a a' : Expr Nat}
    (hf : ParRedStar E n Γ f f') (ha : ParRedStar E n Γ a a') :
    ParRedStar E n Γ (.app f a) (.app f' a') :=
  parRedStar_trans (parRedStar_app_fun hf) (parRedStar_app_arg ha)

theorem lookupValue_letType_irrel (A A' v : Expr Nat) (Γ : LCtx) (i : Nat) :
    lookupValue (.letBinding A v :: Γ) i =
      lookupValue (.letBinding A' v :: Γ) i := by
  cases i with
  | zero => rfl
  | succ i =>
      rw [lookupValue_cons_succ, lookupValue_cons_succ]

def parRedStar_letE_ty {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A A' v b : Expr Nat} →
    ParRedStar E n Γ A A' →
    ParRedStar E n Γ (.letE A v b) (.letE A' v b)
  | _, _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, _, .tail h hs =>
      .tail (.letE _ _ _ _ _ _ _ h (.refl _ _) (.refl _ _))
        (parRedStar_letE_ty hs)

def parRedStar_letE_val {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A v v' b : Expr Nat} →
    ParRedStar E n Γ v v' →
    ParRedStar E n Γ (.letE A v b) (.letE A v' b)
  | _, _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, _, .tail h hs =>
      .tail (.letE _ _ _ _ _ _ _ (.refl _ _) h (.refl _ _))
        (parRedStar_letE_val hs)

def parRedStar_letE_body {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A v b b' : Expr Nat} →
    ParRedStar E n (.letBinding A v :: Γ) b b' →
    ParRedStar E n Γ (.letE A v b) (.letE A v b')
  | _, _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, _, .tail h hs =>
      .tail (.letE _ _ _ _ _ _ _ (.refl _ _) (.refl _ _) h)
        (parRedStar_letE_body hs)

def parRedStar_letE_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' : Expr Nat}
    (hA : ParRedStar E n Γ A A')
    (hv : ParRedStar E n Γ v v')
    (hb : ParRedStar E n (.letBinding A v :: Γ) b b') :
    ParRedStar E n Γ (.letE A v b) (.letE A' v' b') :=
  parRedStar_trans (parRedStar_letE_body hb)
    (parRedStar_trans (parRedStar_letE_val hv) (parRedStar_letE_ty hA))

theorem develWfGo_lam {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (A b : Expr Nat) :
    develWfGo hE fuel cwt maj Γ (.lam A b) =
      .lam (develWfGo hE fuel cwt maj Γ A)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) b) := by
  rw [develWfGo]

theorem develWf_lam {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (A b : Expr Nat) :
    develWf hE Γ (.lam A b) =
      .lam (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.lam A b) + 1)
          (exprSize (.lam A b) + 1) Γ A)
        (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.lam A b) + 1)
          (exprSize (.lam A b) + 1) (.assumption A :: Γ) b) := by
  rw [develWf, develWfGo_lam]

theorem develWfGo_pi {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (A B : Expr Nat) :
    develWfGo hE fuel cwt maj Γ (.pi A B) =
      .pi (develWfGo hE fuel cwt maj Γ A)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B) := by
  rw [develWfGo]

theorem develWf_pi {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (A B : Expr Nat) :
    develWf hE Γ (.pi A B) =
      .pi (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.pi A B) + 1)
          (exprSize (.pi A B) + 1) Γ A)
        (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.pi A B) + 1)
          (exprSize (.pi A B) + 1) (.assumption A :: Γ) B) := by
  rw [develWf, develWfGo_pi]

theorem develWfGo_letE {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (A v b : Expr Nat) :
    develWfGo hE fuel cwt maj Γ (.letE A v b) =
      instantiate0 (develWfGo hE fuel cwt maj Γ v)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) b) := by
  rw [develWfGo]

theorem develWf_letE {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (A v b : Expr Nat) :
    develWf hE Γ (.letE A v b) =
      instantiate0 (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.letE A v b) + 1)
          (exprSize (.letE A v b) + 1) Γ v)
        (develWfGo hE (envWf_rank hE)
          (letsCount Γ + exprSize (.letE A v b) + 1)
          (exprSize (.letE A v b) + 1) (.assumption A :: Γ) b) := by
  rw [develWf, develWfGo_letE]

/-- Non-WF view of the const arm of `develWfGo`. Membership is an
argument so constructor equations reduce. -/
def develWfConstOf {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) :
    (o : Option CheckedMember) → (E.members r = o) → Expr Nat
  | none, _ => .const r ls
  | some m, hmem =>
      if htr : transparent m.mclass = true then
        match m.body with
        | none => .const r ls
        | some b =>
            if hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel then
              develWfGo hE (envWf_rank (envWf_of_member hE hmem).2.1)
                cwt maj Γ (instantiateLevels ls b)
            else
              match fuel with
              | 0 => instantiateLevels ls b
              | fuel'+1 =>
                  develWfGo hE fuel' cwt maj Γ (instantiateLevels ls b)
      else .const r ls

def develWfConstView {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) : Expr Nat :=
  develWfConstOf hE fuel cwt maj Γ r ls (E.members r) rfl

theorem develWfConstOf_congr {E : ResolvedEnv} {n : Nat}
    {hE : EnvWf E n} {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level}
    {o : Option CheckedMember} (ho : E.members r = o) :
    develWfConstOf hE fuel cwt maj Γ r ls (E.members r) rfl =
      develWfConstOf hE fuel cwt maj Γ r ls o ho := by
  subst ho
  rfl

theorem develWfGo_eq_constView {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) :
    develWfGo hE fuel cwt maj Γ (.const r ls) =
      develWfConstView hE fuel cwt maj Γ r ls := by
  unfold develWfGo develWfConstView
  split
  · rename_i hnone
    rw [develWfConstOf_congr hnone]
    simp [develWfConstOf]
  · rename_i _m hsome
    rw [develWfConstOf_congr hsome]
    simp [develWfConstOf]

theorem develWf_eq_constView {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (r : Nat) (ls : List Level) :
    develWf hE Γ (.const r ls) =
      develWfConstView hE (envWf_rank hE)
        (letsCount Γ + exprSize (.const r ls) + 1)
        (exprSize (.const r ls) + 1) Γ r ls := by
  rw [develWf, develWfGo_eq_constView]

theorem develWfGo_const_none {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    (h : E.members r = none) :
    develWfGo hE fuel cwt maj Γ (.const r ls) = .const r ls := by
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr h]
  rfl

theorem develWf_const_none {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {r : Nat} {ls : List Level}
    (h : E.members r = none) :
    develWf hE Γ (.const r ls) = .const r ls := by
  rw [develWf, develWfGo_const_none (hE := hE) h]

theorem develWfGo_const_opaque {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = false) :
    develWfGo hE fuel cwt maj Γ (.const r ls) = .const r ls := by
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr hmem]
  simp [develWfConstOf, htr]

theorem develWf_const_opaque {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = false) :
    develWf hE Γ (.const r ls) = .const r ls := by
  rw [develWf, develWfGo_const_opaque (hE := hE) hmem htr]

theorem develWfGo_const_nobody {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = none) :
    develWfGo hE fuel cwt maj Γ (.const r ls) = .const r ls := by
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr hmem]
  simp [develWfConstOf, htr, hb]

theorem develWf_const_nobody {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = none) :
    develWf hE Γ (.const r ls) = .const r ls := by
  rw [develWf, develWfGo_const_nobody (hE := hE) hmem htr hb]

theorem develWfGo_const_delta {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = some b)
    (hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel) :
    develWfGo hE fuel cwt maj Γ (.const r ls) =
      develWfGo hE (envWf_rank (envWf_of_member hE hmem).2.1) cwt maj Γ
        (instantiateLevels ls b) := by
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr hmem]
  simp [develWfConstOf, htr, hb, hlt]

theorem develWfGo_const_delta_succ {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {fuel cwt maj : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = some b)
    (hnlt : ¬ envWf_rank (envWf_of_member hE hmem).2.1 < fuel + 1) :
    develWfGo hE (fuel + 1) cwt maj Γ (.const r ls) =
      develWfGo hE fuel cwt maj Γ (instantiateLevels ls b) := by
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr hmem]
  simp [develWfConstOf, htr, hb, hnlt]

theorem develWfGo_const_delta_zero {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {cwt maj : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = some b) :
    develWfGo hE 0 cwt maj Γ (.const r ls) = instantiateLevels ls b := by
  have hnlt : ¬ envWf_rank (envWf_of_member hE hmem).2.1 < 0 :=
    Nat.not_lt_zero _
  rw [develWfGo_eq_constView, develWfConstView, develWfConstOf_congr hmem]
  simp [develWfConstOf, htr, hb, hnlt]

theorem develWf_const_delta {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat}
    (hmem : E.members r = some m)
    (htr : transparent m.mclass = true)
    (hb : m.body = some b) :
    develWf hE Γ (.const r ls) =
      develWfGo hE (envWf_rank (envWf_of_member hE hmem).2.1)
        (letsCount Γ + exprSize (.const r ls) + 1)
        (exprSize (.const r ls) + 1) Γ (instantiateLevels ls b) := by
  rw [develWf, develWfGo_const_delta (hE := hE) hmem htr hb
    (envWf_of_member hE hmem).2.2.2]
theorem develWfGo_app_none {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (f a : Expr Nat)
    (h : iotaReductCert E (.app f a) = none) :
    develWfGo hE fuel cwt maj Γ (.app f a) =
      match develWfGo hE fuel cwt maj Γ f with
      | .lam _ b => instantiate0 (develWfGo hE fuel cwt maj Γ a) b
      | _ => .app (develWfGo hE fuel cwt maj Γ f)
          (develWfGo hE fuel cwt maj Γ a) := by
  conv => lhs; unfold develWfGo; rw [h]

theorem develWfGo_app_some {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) {f a : Expr Nat}
    {w : IotaWitness E} {hlhs : iotaLhsOf w = .app f a}
    (h : iotaReductCert E (.app f a) = some ⟨w, hlhs⟩) :
    develWfGo hE fuel cwt maj Γ (.app f a) =
      if hlt : exprSize (ctorMajor w) < maj then
        develWfGo hE fuel cwt (exprSize (ctorMajor w)) Γ (iotaRhsOf w)
      else iotaRhsOf w := by
  conv => lhs; unfold develWfGo; rw [h]

/-- Weakening commutes with well-founded devel. Same fuel/cwt/maj:
`exprSize` is lift-invariant, so iota maj tests coincide.

App mixed cert (none/some or some/none) cannot form `none = some`
across different `Σ'` payloads. Closed by the isSome Bool:
`iotaReductCert_lift_isSome_of` / `iotaReductCert_isSome_of_lift`.
none/none is congruence; some/some is iotaReduct_lift + some_reduct
+ ctorMajor_eq_of_lhs. -/
theorem develWfGo_lift {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (d : LocalDecl) (fuel cwt maj : Nat)
    (Γ : LCtx) (c : Nat) (hlen : c ≤ Γ.length) :
    (e : Expr Nat) →
    develWfGo hE fuel cwt maj (insertAt d c Γ) (lift c 1 e) =
      lift c 1 (develWfGo hE fuel cwt maj Γ e)
  | .sort l => by
      simp only [lift, develWfGo_sort]
  | .lit t => by
      simp only [lift, develWfGo_lit]
      exact (natExpand_lift c 1 t).symm
  | .const r ls => by
      simp only [lift]
      match hmem : E.members r with
      | none =>
          rw [develWfGo_const_none (hE := hE) hmem,
            develWfGo_const_none (hE := hE) hmem]
          rfl
      | some m =>
          if htr : transparent m.mclass = true then
            match hb : m.body with
            | none =>
                rw [develWfGo_const_nobody (hE := hE) hmem htr hb,
                  develWfGo_const_nobody (hE := hE) hmem htr hb]
                rfl
            | some b =>
                have hcl : lift c 1 (instantiateLevels ls b) =
                    instantiateLevels ls b :=
                  (envWf_closed_inst hE r m hmem).2 b hb ls c
                if hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel then
                  rw [develWfGo_const_delta (hE := hE) hmem htr hb hlt,
                    develWfGo_const_delta (hE := hE) hmem htr hb hlt]
                  have ih := develWfGo_lift hE d
                    (envWf_rank (envWf_of_member hE hmem).2.1) cwt maj
                    Γ c hlen (instantiateLevels ls b)
                  rw [hcl] at ih
                  exact ih
                else
                  match fuel with
                  | 0 =>
                      rw [develWfGo_const_delta_zero (hE := hE) hmem htr hb,
                        develWfGo_const_delta_zero (hE := hE) hmem htr hb]
                      exact hcl.symm
                  | fuel'+1 =>
                      rw [develWfGo_const_delta_succ (hE := hE) hmem htr hb hlt,
                        develWfGo_const_delta_succ (hE := hE) hmem htr hb hlt]
                      have ih := develWfGo_lift hE d fuel' cwt maj Γ c hlen
                        (instantiateLevels ls b)
                      rw [hcl] at ih
                      exact ih
          else
            have hfalse : transparent m.mclass = false := by
              cases htr' : transparent m.mclass <;> simp_all
            rw [develWfGo_const_opaque (hE := hE) hmem hfalse,
              develWfGo_const_opaque (hE := hE) hmem hfalse]
            rfl
  | .bvar i => by
      simp only [lift]
      by_cases hi : c ≤ i
      · rw [if_pos hi]
        cases hg : getLet Γ i with
        | none =>
            have hnone : getLet (insertAt d c Γ) (i + 1) = none :=
              (getLet_insertAt_ge (Γ := Γ) d hi).trans hg
            rw [develWfGo_bvar_none (h := hnone),
              develWfGo_bvar_none (h := hg)]
            simp only [lift, if_pos hi]
        | some stored_tail =>
            match stored_tail with
            | (stored, tail) =>
                have hge : getLet (insertAt d c Γ) (i + 1) =
                    some (stored, tail) :=
                  (getLet_insertAt_ge (Γ := Γ) d hi).trans hg
                rw [develWfGo_bvar_some (h := hge),
                  develWfGo_bvar_some (h := hg)]
                have ih := develWfGo_lift hE d fuel cwt maj tail 0
                  (Nat.zero_le _) stored
                -- i ≥ c: tail is not rewritten; only commute two lifts.
                have hmerge :=
                  lift_lift_merge 1 (i + 1) 0 c (Nat.zero_le c)
                    (by omega : c ≤ i + 1)
                    (develWfGo hE fuel cwt maj tail stored)
                exact hmerge.symm
      · have hic : i < c := Nat.lt_of_not_ge hi
        rw [if_neg hi]
        cases hg : getLet Γ i with
        | none =>
            have hnone := getLet_insertAt_lt_none d hlen hic hg
            rw [develWfGo_bvar_none (h := hg),
              develWfGo_bvar_none (h := hnone)]
            simp only [lift, if_neg hi]
        | some stored_tail =>
            match stored_tail with
            | (stored, tail) =>
                have hsome := getLet_insertAt_lt_some d hlen hic hg
                rw [develWfGo_bvar_some (h := hsome),
                  develWfGo_bvar_some (h := hg)]
                have hcut := getLet_insertAt_lt_cut_le hlen hic hg
                have ih := develWfGo_lift hE d fuel cwt maj tail
                  (c - i - 1) hcut stored
                have hp :=
                  lift_lift_permute (i + 1) 1 (c - i - 1) 0
                    (Nat.zero_le _)
                    (develWfGo hE fuel cwt maj tail stored)
                have hsum : i + 1 + (c - i - 1) = c := by omega
                rw [hsum] at hp
                rw [ih, hp]
  | .lam A b => by
      simp only [lift]
      rw [develWfGo_lam, develWfGo_lam]
      have hA := develWfGo_lift hE d fuel cwt maj Γ c hlen A
      have hlen' : c + 1 ≤ (.assumption A :: Γ).length := by
        simp only [List.length_cons]; omega
      have hb := develWfGo_lift hE d fuel cwt maj (.assumption A :: Γ)
        (c + 1) hlen' b
      rw [insertAt_succ_cons] at hb
      simp only [liftDecl] at hb
      rw [hA, hb]
      simp only [lift]
  | .pi A B => by
      simp only [lift]
      rw [develWfGo_pi, develWfGo_pi]
      have hA := develWfGo_lift hE d fuel cwt maj Γ c hlen A
      have hlen' : c + 1 ≤ (.assumption A :: Γ).length := by
        simp only [List.length_cons]; omega
      have hB := develWfGo_lift hE d fuel cwt maj (.assumption A :: Γ)
        (c + 1) hlen' B
      rw [insertAt_succ_cons] at hB
      simp only [liftDecl] at hB
      rw [hA, hB]
      simp only [lift]
  | .letE A v b => by
      simp only [lift]
      rw [develWfGo_letE, develWfGo_letE]
      have hv := develWfGo_lift hE d fuel cwt maj Γ c hlen v
      have hlen' : c + 1 ≤ (.assumption A :: Γ).length := by
        simp only [List.length_cons]; omega
      have hb := develWfGo_lift hE d fuel cwt maj (.assumption A :: Γ)
        (c + 1) hlen' b
      rw [insertAt_succ_cons] at hb
      simp only [liftDecl] at hb
      rw [hv, hb]
      exact (lift_instantiate_low 1 c 0
        (develWfGo hE fuel cwt maj Γ v) (Nat.zero_le c)
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) b)).symm
  | .app f a => by
      simp only [lift]
      match hc : iotaReductCert E (.app f a),
          hc' : iotaReductCert E (.app (lift c 1 f) (lift c 1 a)) with
      | none, none =>
          rw [develWfGo_app_none (h := hc),
            develWfGo_app_none (h := hc')]
          have hf := develWfGo_lift hE d fuel cwt maj Γ c hlen f
          have ha := develWfGo_lift hE d fuel cwt maj Γ c hlen a
          rw [hf, ha]
          cases develWfGo hE fuel cwt maj Γ f with
          | lam A b =>
              simp only [lift]
              exact (lift_instantiate_low 1 c 0
                (develWfGo hE fuel cwt maj Γ a) (Nat.zero_le c) b).symm
          | sort _ => simp only [lift]
          | const _ _ => simp only [lift]
          | bvar i =>
              simp only [lift]
              by_cases h : c ≤ i <;> simp [h]
          | app _ _ => simp only [lift]
          | pi _ _ => simp only [lift]
          | letE _ _ _ => simp only [lift]
          | lit _ => simp only [lift]
      | some wσ, some wσ' =>
          match wσ, wσ' with
          | ⟨w, hlhs⟩, ⟨w', hlhs'⟩ =>
            rw [develWfGo_app_some (h := hc),
              develWfGo_app_some (h := hc')]
            have hlifted : iotaLhsOf (liftWitness c w) =
                .app (lift c 1 f) (lift c 1 a) := by
              rw [iotaLhsOf_lift, hlhs]; rfl
            have hlhsEq : iotaLhsOf w' = iotaLhsOf (liftWitness c w) :=
              hlhs'.trans hlifted.symm
            have hmaj : ctorMajor w' = lift c 1 (ctorMajor w) := by
              have := ctorMajor_eq_of_lhs hlhsEq
              rw [this, ctorMajor_lift]
            have hsz : exprSize (ctorMajor w') = exprSize (ctorMajor w) := by
              rw [hmaj, exprSize_lift]
            have hrhs : iotaRhsOf w' = lift c 1 (iotaRhsOf w) := by
              have r1 := iotaReductCert_some_reduct hc
              have r2 := iotaReductCert_some_reduct hc'
              have rlift := iotaReduct_lift E c (.app f a)
              rw [r1] at rlift
              simp only [Option.map, lift] at rlift
              rw [r2] at rlift
              exact Option.some.inj rlift
            rw [hsz]
            if hlt : exprSize (ctorMajor w) < maj then
              simp only [hlt]
              rw [hrhs]
              exact develWfGo_lift hE d fuel cwt
                (exprSize (ctorMajor w)) Γ c hlen (iotaRhsOf w)
            else
              simp only [hlt]
              exact hrhs
      | none, some _ =>
          have hlift :
              lift c 1 (.app f a) = .app (lift c 1 f) (lift c 1 a) := rfl
          have hsome' :
              (iotaReductCert E (lift c 1 (.app f a))).isSome = true := by
            rw [hlift, hc']
            rfl
          have hsome := iotaReductCert_isSome_of_lift (c := c) hsome'
          simp only [hc, Option.isSome] at hsome
          nomatch hsome
      | some ⟨w, hlhs⟩, none =>
          have hlift :
              lift c 1 (.app f a) = .app (lift c 1 f) (lift c 1 a) := rfl
          have hsome := iotaReductCert_lift_isSome_of (c := c) (h := hc)
          rw [hlift] at hsome
          simp only [hc', Option.isSome] at hsome
          nomatch hsome
termination_by e => (fuel, letsCount Γ, cwt, maj, exprSize e)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | exact Prod.Lex.left _ _ ‹_›
      | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (getLet_letsCount ‹_›))
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (Nat.zero_le _))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.left _ _ ‹_›)))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.right maj ?_)))
        first
          | exact exprSize_lam_dom _ _
          | exact exprSize_lam_body _ _
          | exact exprSize_pi_dom _ _
          | exact exprSize_pi_body _ _
          | exact exprSize_let_val _ _ _
          | exact exprSize_let_body _ _ _
          | exact exprSize_app_left _ _
          | exact exprSize_app_right _ _

/-- Multi-binder form of `develWfGo_lift` (bvarZeta tail unfold). -/
theorem develWfGo_lift_append {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) :
    (pre : LCtx) → (Γ : LCtx) → (e : Expr Nat) →
    develWfGo hE fuel cwt maj (pre ++ Γ) (lift 0 pre.length e) =
      lift 0 pre.length (develWfGo hE fuel cwt maj Γ e)
  | [], Γ, e => by
      simp only [List.nil_append, List.length_nil, lift_zero]
  | d :: pre, Γ, e => by
      have ih := develWfGo_lift_append hE fuel cwt maj pre Γ e
      have hlen : 0 ≤ (pre ++ Γ).length := Nat.zero_le _
      have h := develWfGo_lift hE d fuel cwt maj (pre ++ Γ) 0 hlen
        (lift 0 pre.length e)
      rw [insertAt_zero] at h
      have hmerge :
          lift 0 1 (lift 0 pre.length e) = lift 0 (pre.length + 1) e :=
        lift_lift_merge 1 pre.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) e
      rw [hmerge, ih] at h
      have hmerge' :
          lift 0 1 (lift 0 pre.length (develWfGo hE fuel cwt maj Γ e)) =
            lift 0 (pre.length + 1) (develWfGo hE fuel cwt maj Γ e) :=
        lift_lift_merge 1 pre.length 0 0 (Nat.le_refl 0) (Nat.zero_le _)
          (develWfGo hE fuel cwt maj Γ e)
      rw [hmerge'] at h
      simp only [List.cons_append, List.length_cons, Nat.succ_eq_add_one]
      exact h

theorem getLet_assumption_irrel (A A' : Expr Nat) (Γ : LCtx) :
    (i : Nat) →
    getLet (.assumption A :: Γ) i = getLet (.assumption A' :: Γ) i
  | 0 => rfl
  | _ + 1 => rfl

/-- `develWfGo` depends on `getLet`, not assumption types.
`Γ`/`Γ'`/`h` are def parameters so `termination_by` sees them. -/
theorem develWfGo_ctx_getLet {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ Γ' : LCtx)
    (h : ∀ i, getLet Γ i = getLet Γ' i) :
    (e : Expr Nat) →
    develWfGo hE fuel cwt maj Γ e = develWfGo hE fuel cwt maj Γ' e
  | .sort l => by
      rw [develWfGo_sort, develWfGo_sort]
  | .lit t => by
      rw [develWfGo_lit, develWfGo_lit]
  | .const r ls => by
      match hmem : E.members r with
      | none =>
          rw [develWfGo_const_none (hE := hE) hmem,
            develWfGo_const_none (hE := hE) hmem]
      | some m =>
          if htr : transparent m.mclass = true then
            match hb : m.body with
            | none =>
                rw [develWfGo_const_nobody (hE := hE) hmem htr hb,
                  develWfGo_const_nobody (hE := hE) hmem htr hb]
            | some b =>
                if hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel then
                  rw [develWfGo_const_delta (hE := hE) hmem htr hb hlt,
                    develWfGo_const_delta (hE := hE) hmem htr hb hlt]
                  exact develWfGo_ctx_getLet hE
                    (envWf_rank (envWf_of_member hE hmem).2.1) cwt maj Γ Γ' h
                    (instantiateLevels ls b)
                else
                  cases fuel with
                  | zero =>
                      rw [develWfGo_const_delta_zero (hE := hE) hmem htr hb,
                        develWfGo_const_delta_zero (hE := hE) hmem htr hb]
                  | succ fuel0 =>
                      rw [develWfGo_const_delta_succ (hE := hE) hmem htr hb hlt,
                        develWfGo_const_delta_succ (hE := hE) hmem htr hb hlt]
                      exact develWfGo_ctx_getLet hE fuel0 cwt maj Γ Γ' h
                        (instantiateLevels ls b)
          else
            have hfalse : transparent m.mclass = false := by
              cases htr' : transparent m.mclass <;> simp_all
            rw [develWfGo_const_opaque (hE := hE) hmem hfalse,
              develWfGo_const_opaque (hE := hE) hmem hfalse]
  | .bvar i => by
      have hg := h i
      cases hsome : getLet Γ i with
      | none =>
          have hnone : getLet Γ' i = none := hg.symm.trans hsome
          rw [develWfGo_bvar_none (h := hsome),
            develWfGo_bvar_none (h := hnone)]
      | some st =>
          have hsome' : getLet Γ' i = some st := hg.symm.trans hsome
          match st with
          | (stored, tail) =>
              rw [develWfGo_bvar_some (h := hsome),
                develWfGo_bvar_some (h := hsome')]
  | .lam A b => by
      rw [develWfGo_lam, develWfGo_lam]
      have hA := develWfGo_ctx_getLet hE fuel cwt maj Γ Γ' h A
      have hb := develWfGo_ctx_getLet hE fuel cwt maj
        (.assumption A :: Γ) (.assumption A :: Γ')
        (fun i => match i with
          | 0 => rfl
          | n + 1 => h n) b
      rw [hA, hb]
  | .pi A B => by
      rw [develWfGo_pi, develWfGo_pi]
      have hA := develWfGo_ctx_getLet hE fuel cwt maj Γ Γ' h A
      have hB := develWfGo_ctx_getLet hE fuel cwt maj
        (.assumption A :: Γ) (.assumption A :: Γ')
        (fun i => match i with
          | 0 => rfl
          | n + 1 => h n) B
      rw [hA, hB]
  | .letE A v b => by
      rw [develWfGo_letE, develWfGo_letE]
      have hv := develWfGo_ctx_getLet hE fuel cwt maj Γ Γ' h v
      have hb := develWfGo_ctx_getLet hE fuel cwt maj
        (.assumption A :: Γ) (.assumption A :: Γ')
        (fun i => match i with
          | 0 => rfl
          | n + 1 => h n) b
      rw [hv, hb]
  | .app f a => by
      match hc : iotaReductCert E (.app f a) with
      | some ⟨w, hlhs⟩ =>
          rw [develWfGo_app_some (h := hc),
            develWfGo_app_some (h := hc)]
          if hlt : exprSize (ctorMajor w) < maj then
            simp only [hlt]
            exact develWfGo_ctx_getLet hE fuel cwt
              (exprSize (ctorMajor w)) Γ Γ' h (iotaRhsOf w)
          else
            simp only [hlt]
            rfl
      | none =>
          rw [develWfGo_app_none (h := hc),
            develWfGo_app_none (h := hc)]
          have hf := develWfGo_ctx_getLet hE fuel cwt maj Γ Γ' h f
          have ha := develWfGo_ctx_getLet hE fuel cwt maj Γ Γ' h a
          rw [hf, ha]
termination_by e => (fuel, letsCount Γ, cwt, maj, exprSize e)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.left _ _ ‹_›
      | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (by omega))
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ ‹_›)
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (Nat.zero_le _))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.left _ _ ‹_›)))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.right maj ?_)))
        first
          | exact exprSize_lam_dom _ _
          | exact exprSize_lam_body _ _
          | exact exprSize_pi_dom _ _
          | exact exprSize_pi_body _ _
          | exact exprSize_let_val _ _ _
          | exact exprSize_let_body _ _ _
          | exact exprSize_app_left _ _
          | exact exprSize_app_right _ _

theorem develWfGo_assump_irrel {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) (A A' : Expr Nat) (e : Expr Nat) :
    develWfGo hE fuel cwt maj (.assumption A :: Γ) e =
      develWfGo hE fuel cwt maj (.assumption A' :: Γ) e :=
  develWfGo_ctx_getLet hE fuel cwt maj _ _ (getLet_assumption_irrel A A' Γ) e

mutual
/-- Member-extension of ParRed (prefix env to a later EnvWf). -/
def parRedExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b : Expr Nat} →
    ParRed E n Γ a b → ParRed E' n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .sortEq Γ l₁ l₂ h => .sortEq Γ l₁ l₂ h
  | _, _, _, .consts Γ r ls ls' h => .consts Γ r ls ls' h
  | _, _, _, .bvarZeta Γ i A v v' hlk hv =>
      .bvarZeta Γ i A v v' hlk (parRedExt hext hv)
  | _, _, _, .delta Γ r ls m b hres hbody htr =>
      .delta Γ r ls m b (hext r m hres) hbody htr
  | _, _, _, .app Γ f f' a a' hf ha =>
      .app Γ f f' a a' (parRedExt hext hf) (parRedExt hext ha)
  | _, _, _, .beta Γ A A' body body' arg arg' hA hb ha =>
      .beta Γ A A' body body' arg arg'
        (parRedExt hext hA) (parRedExt hext hb) (parRedExt hext ha)
  | _, _, _, .lam Γ A A' b b' hA hb =>
      .lam Γ A A' b b' (parRedExt hext hA) (parRedExt hext hb)
  | _, _, _, .pi Γ A A' B B' hA hB =>
      .pi Γ A A' B B' (parRedExt hext hA) (parRedExt hext hB)
  | _, _, _, .letE Γ A A' v v' b b' hA hv hb =>
      .letE Γ A A' v v' b b'
        (parRedExt hext hA) (parRedExt hext hv) (parRedExt hext hb)
  | _, _, _, .zeta Γ A A' v v' b b' hA hv hb =>
      .zeta Γ A A' v v' b b'
        (parRedExt hext hA) (parRedExt hext hv) (parRedExt hext hb)
  | _, _, _, .iotaSpine Γ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs =>
      .iotaSpine Γ (extWitness hext w2) lsR lsC hlsR hlsC
        pre pre' fields fields'
        (parRedArgsExt hext hf) (parRedArgsExt hext ha)
        hpreLen hfieldsLen
        (by
          change iotaLhsOf (extWitness hext w2) =
            recCall (.const w2.recRef w2.ls) pre'
              (foldApps (.const w2.ctorRef w2.lsC) fields')
          exact hlhs)
  | _, _, _, .lit Γ t => .lit Γ t

def parRedArgsExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {Γ : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys) :
    ParRedArgs E' n Γ xs ys :=
  match h with
  | ParRedArgs.nil Γ => ParRedArgs.nil Γ
  | ParRedArgs.cons hx t =>
      .cons (parRedExt hext hx) (parRedArgsExt hext (h := t))

def parRedStarExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b : Expr Nat} →
    ParRedStar E n Γ a b → ParRedStar E' n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .tail h hs =>
      .tail (parRedExt hext h) (parRedStarExt hext hs)
end

/-- `t ⇒* develWfGo fuel t`. Fuel-indexed so delta stays on `hE`. -/
noncomputable def star_to_develWfGo {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel cwt maj : Nat) (Γ : LCtx) :
    (e : Expr Nat) → ParRedStar E n Γ e (develWfGo hE fuel cwt maj Γ e)
  | .sort l => by
      rw [develWfGo_sort]
      exact .refl _ _
  | .lit t => by
      rw [develWfGo_lit]
      exact parRedStar_one (.lit Γ t)
  | .bvar i => by
      rw [develWfGo]
      match hg : getLet Γ i with
      | none => exact .refl _ _
      | some (stored, tail) =>
          have hlk := lookupValue_getLet hg
          let s := getLet_split hg
          let pre := s.fst
          let A := s.snd.fst
          let hsplit := s.snd.snd.fst
          let hlen := s.snd.snd.snd
          have hs := star_to_develWfGo hE fuel cwt maj tail stored
          have hs' :=
            parRedStar_lift_append hE
              (pre ++ [LocalDecl.letBinding A stored]) hs
          have hlen' :
              (pre ++ [LocalDecl.letBinding A stored]).length = i + 1 := by
            rw [List.length_append, hlen]
            rfl
          rw [hlen'] at hs'
          have hctx :
              (pre ++ [LocalDecl.letBinding A stored]) ++ tail = Γ := by
            rw [List.append_assoc]
            exact hsplit.symm
          rw [hctx] at hs'
          let ⟨A', st, hg', heq⟩ := get?_of_lookupValue hlk
          have hst : st = stored :=
            lift_zero_amount_inj (i + 1) heq.symm
          exact parRedStar_trans
            (parRedStar_one (hst ▸ .bvarZeta Γ i A' st st hg' (.refl _ _)))
            hs'
  | .const r ls =>
      match hmem : E.members r with
      | none => by
          rw [develWfGo_const_none (hE := hE) hmem]
          exact .refl _ _
      | some m =>
          if htr : transparent m.mclass = true then
            match hb : m.body with
            | none => by
                rw [develWfGo_const_nobody (hE := hE) hmem htr hb]
                exact .refl _ _
            | some b =>
                if hlt : envWf_rank (envWf_of_member hE hmem).2.1 < fuel then by
                  rw [develWfGo_const_delta (hE := hE) hmem htr hb hlt]
                  exact parRedStar_trans
                    (parRedStar_one
                      (.delta Γ r ls m b hmem hb htr))
                    (star_to_develWfGo hE
                      (envWf_rank (envWf_of_member hE hmem).2.1) cwt maj Γ
                      (instantiateLevels ls b))
                else
                  match fuel with
                  | 0 => by
                      rw [develWfGo_const_delta_zero (hE := hE) hmem htr hb]
                      exact parRedStar_one
                        (.delta Γ r ls m b hmem hb htr)
                  | fuel'+1 => by
                      rw [develWfGo_const_delta_succ (hE := hE) hmem htr hb hlt]
                      exact parRedStar_trans
                        (parRedStar_one
                          (.delta Γ r ls m b hmem hb htr))
                        (star_to_develWfGo hE fuel' cwt maj Γ
                          (instantiateLevels ls b))
          else by
            have hfalse : transparent m.mclass = false := by
              cases htr' : transparent m.mclass <;> simp_all
            rw [develWfGo_const_opaque (hE := hE) hmem hfalse]
            exact .refl _ _
  | .lam A b => by
      rw [develWfGo_lam]
      exact parRedStar_lam_congr
        (star_to_develWfGo hE fuel cwt maj Γ A)
        (star_to_develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
  | .pi A B => by
      rw [develWfGo_pi]
      exact parRedStar_pi_congr
        (star_to_develWfGo hE fuel cwt maj Γ A)
        (star_to_develWfGo hE fuel cwt maj (.assumption A :: Γ) B)
  | .letE A v b => by
      rw [develWfGo_letE]
      exact parRedStar_trans
        (parRedStar_letE_congr (.refl _ _)
          (star_to_develWfGo hE fuel cwt maj Γ v)
          (parRedStar_assump_to_let
            (star_to_develWfGo hE fuel cwt maj (.assumption A :: Γ) b)))
        (parRedStar_one
          (.zeta Γ A A (develWfGo hE fuel cwt maj Γ v)
            (develWfGo hE fuel cwt maj Γ v)
            (develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
            (develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
            (.refl _ _) (.refl _ _) (.refl _ _)))
  | .app f a =>
      match hc : iotaReductCert E (.app f a) with
      | some ⟨w, hlhs⟩ => by
          rw [develWfGo]
          simp [hc]
          have hstep : ParRed E n Γ (iotaLhsOf w) (iotaRhsOf w) :=
            parRed_iota Γ w
          rw [hlhs] at hstep
          if hlt : exprSize (ctorMajor w) < maj then
            simp [hlt]
            exact parRedStar_trans (parRedStar_one hstep)
              (star_to_develWfGo hE fuel cwt (exprSize (ctorMajor w)) Γ
                (iotaRhsOf w))
          else
            simp [hlt]
            exact parRedStar_one hstep
      | none => by
          have hcongr :
              ParRedStar E n Γ (.app f a)
                (.app (develWfGo hE fuel cwt maj Γ f) (develWfGo hE fuel cwt maj Γ a)) :=
            parRedStar_app_congr
              (star_to_develWfGo hE fuel cwt maj Γ f)
              (star_to_develWfGo hE fuel cwt maj Γ a)
          rw [develWfGo]
          simp only [hc]
          cases hdf : develWfGo hE fuel cwt maj Γ f with
          | lam A b =>
              have hcongr' :
                  ParRedStar E n Γ (.app f a)
                    (.app (.lam A b) (develWfGo hE fuel cwt maj Γ a)) :=
                @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                  (fun f' => ParRedStar E n Γ (.app f a)
                    (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
              exact parRedStar_trans hcongr'
                (parRedStar_one
                  (.beta Γ A A b b (develWfGo hE fuel cwt maj Γ a)
                    (develWfGo hE fuel cwt maj Γ a)
                    (.refl _ _) (.refl _ _) (.refl _ _)))
          | bvar i =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | sort l =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | const r ls =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | app f1 a1 =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | pi A B =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | letE A v b =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
          | lit t =>
              exact @Eq.ndrec _ (develWfGo hE fuel cwt maj Γ f)
                (fun f' => ParRedStar E n Γ (.app f a)
                  (.app f' (develWfGo hE fuel cwt maj Γ a))) hcongr _ hdf
termination_by e => (fuel, letsCount Γ, cwt, maj, exprSize e)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
      | exact Prod.Lex.left _ _ ‹_›
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (getLet_letsCount ‹_›))
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ (Nat.lt_succ_self _))
      | refine Prod.Lex.right fuel (Prod.Lex.left _ _ ‹_›)
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ) (Prod.Lex.left _ _ (Nat.lt_succ_self _)))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ) (Prod.Lex.left _ _ ‹_›))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.left _ _ ‹_›)))
      | refine Prod.Lex.right fuel
          (Prod.Lex.right (letsCount Γ)
            (Prod.Lex.right cwt (Prod.Lex.right maj ?_)))
        first
          | exact exprSize_lam_dom _ _
          | exact exprSize_lam_body _ _
          | exact exprSize_pi_dom _ _
          | exact exprSize_pi_body _ _
          | exact exprSize_let_val _ _ _
          | exact exprSize_let_body _ _ _
          | exact exprSize_app_left _ _
          | exact exprSize_app_right _ _

noncomputable def star_to_develWf {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) (e : Expr Nat) : ParRedStar E n Γ e (develWf hE Γ e) :=
  star_to_develWfGo hE (envWf_rank hE)
    (letsCount Γ + exprSize e + 1) (exprSize e + 1) Γ e

/-- Refl corner at a certified iota redex. -/
noncomputable def star_to_develWf_iota {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (Γ : LCtx) {f a : Expr Nat} {w : IotaWitness E}
    {hlhs : iotaLhsOf w = .app f a}
    (h : iotaReductCert E (.app f a) = some ⟨w, hlhs⟩) :
    ParRedStar E n Γ (.app f a) (develWf hE Γ (.app f a)) :=
  star_to_develWf hE Γ (.app f a)

theorem iotaReductCert_lam_app (E : ResolvedEnv) (A body arg : Expr Nat) :
    iotaReductCert E (.app (.lam A body) arg) = none := by
  rw [iotaReductCert_eq_spine E (.app (.lam A body) arg)
    (.lam A body, [arg]) (appsSpine_app_lam A body arg)]
  unfold iotaReductCertFromSpine
  dsimp only

theorem iotaReductCert_bvar_app (E : ResolvedEnv) (i : Nat) (arg : Expr Nat) :
    iotaReductCert E (.app (.bvar i) arg) = none := by
  rw [iotaReductCert_eq_spine E (.app (.bvar i) arg)
    (.bvar i, [arg]) (appsSpine_app_bvar i arg)]
  unfold iotaReductCertFromSpine
  dsimp only

def parRedStar_replace_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v : Expr Nat} {a b : Expr Nat} :
    ParRedStar E n (.letBinding A v :: Γ) a b →
    ParRedStar E n (.letBinding A' v :: Γ) a b :=
  parRedStar_ctx_lookup (lookupValue_letType_irrel A A' v Γ)

/-- Join of `let x := v in (x arg)` after zeta: fn is the unfolded
lookup, arg drops under the assumption. No extra beta — devel of
`app (bvar 0) arg` under assumption stays an app. -/
def parRedStar_app_bvar0_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx} {A : Expr Nat}
    {v v' val' arg arg' : Expr Nat}
    (ihfn : ParRedStar E n Γ (instantiate0 v' val')
      (develWfGo hE fuel cwt maj Γ v))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v))
    (iha : ParRedStar E n (.assumption A :: Γ) arg'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) arg)) :
    ParRedStar E n Γ
      (.app (instantiate0 v' val') (instantiate0 v' arg'))
      (.app (develWfGo hE fuel cwt maj Γ v)
        (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) arg))) :=
  parRedStar_app_congr ihfn
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') iha)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) arg)))

/-- Refl lookup of bvar 0: `instantiate0 v' (lift 0 1 v) = v`, then devel. -/
noncomputable def parRedStar_bvar0_refl_inst {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx}
    {v v' val' : Expr Nat} (hval' : val' = lift 0 1 v) :
    ParRedStar E n Γ (instantiate0 v' val')
      (develWfGo hE fuel cwt maj Γ v) := by
  have hid : instantiate0 v' (lift 0 1 v) = v :=
    instantiate_lift_id 0 v' v
  rw [hval', hid]
  exact star_to_develWfGo hE fuel cwt maj Γ v

/-- Reduced lookup of bvar 0 after drop_let + TRIANGLE under assumption. -/
def parRedStar_bvar0_reduced_inst {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A : Expr Nat}
    {v v' val' : Expr Nat}
    (ih : ParRedStar E n (.assumption A :: Γ) val'
      (lift 0 1 v)) :
    ParRedStar E n Γ (instantiate0 v' val') v :=
  by
    have hinst :=
      parRedStar_instantiate_term_assump (A := A) hE (s := v') ih
    have hid := instantiate_lift_id 0 v' v
    simp only [instantiate0] at hinst hid
    rw [hid] at hinst
    exact hinst

/-- Join of `let x := v in (fun y => x)` after zeta: domain drops,
body is bvar 1 with refl lookup (`instantiate_lift2_id`). -/
noncomputable def parRedStar_lam_bvar1_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx} {A : Expr Nat}
    {v v' B B' : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v)) :
    ParRedStar E n Γ
      (.lam (instantiate0 v' B') (lift 0 1 v))
      (.lam (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :=
  parRedStar_lam_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    (by
      have w := parRedStar_weaken
        (.assumption (instantiate0 v' B')) hE (c := 0)
        (star_to_develWfGo hE fuel cwt maj Γ v)
      rw [insertAt_zero] at w
      exact w)

noncomputable def parRedStar_pi_bvar1_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx} {A : Expr Nat}
    {v v' B B' : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v)) :
    ParRedStar E n Γ
      (.pi (instantiate0 v' B') (lift 0 1 v))
      (.pi (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :=
  parRedStar_pi_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    (by
      have w := parRedStar_weaken
        (.assumption (instantiate0 v' B')) hE (c := 0)
        (star_to_develWfGo hE fuel cwt maj Γ v)
      rw [insertAt_zero] at w
      exact w)

/-- Reduced bvarZeta at 1: triangle under two assumptions, instantiate
at index 1, `instantiate_lift2_id` hits `lift 0 1 w`. -/
def parRedStar_bvar1_reduced_body {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A B v' val' w : Expr Nat}
    (ih : ParRedStar E n (.assumption B :: .assumption A :: Γ) val'
      (lift 0 2 w)) :
    ParRedStar E n (.assumption (instantiate0 v' B) :: Γ)
      (instantiate 1 (lift 0 1 v') val')
      (lift 0 1 w) := by
  have ih1 :
      ParRedStar E n (.assumption B :: dummyAssump :: Γ) val'
        (lift 0 2 w) :=
    parRedStar_ctx_lookup
      (lookupValue_assump_assump_irrel B A (.sort .zero) Γ) ih
  have ih2 := parRedStar_instantiate_term1 (A := B) (s := v') hE ih1
  have hid := instantiate_lift2_id v' w
  rw [hid] at ih2
  exact ih2

def parRedStar_instantiate_term1_assump {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {A B s : Expr Nat} {e e' : Expr Nat}
    (h : ParRedStar E n (.assumption B :: .assumption A :: Γ) e e') :
    ParRedStar E n (.assumption (instantiate0 s B) :: Γ)
      (instantiate 1 (lift 0 1 s) e)
      (instantiate 1 (lift 0 1 s) e') :=
  parRedStar_instantiate_term1 (A := B) (s := s) hE
    (parRedStar_ctx_lookup
      (lookupValue_assump_assump_irrel B A (.sort .zero) Γ) h)

/-- WF-safe `let x := v in (fun y : x => b)` after zeta: domain is
bvarZeta 0 with refl lookup, body is refl so `star_to_devel` of `b`
(no `triangleGo` on a dropped binder proof). -/
noncomputable def parRedStar_lam_dom_bvar0_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx}
    {A v v' val' body : Expr Nat}
    (ihdom : ParRedStar E n Γ (instantiate0 v' val')
      (develWfGo hE fuel cwt maj Γ v))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v)) :
    ParRedStar E n Γ
      (.lam (instantiate0 v' val')
        (instantiate 1 (lift 0 1 v') body))
      (.lam (develWfGo hE fuel cwt maj Γ v)
        (instantiate 1 (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
          (develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body))) :=
  parRedStar_lam_congr ihdom
    (parRedStar_trans
      (parRedStar_replace_assump
        (A := instantiate0 v' (.bvar 0)) (A' := instantiate0 v' val')
        (parRedStar_instantiate_term1_assump (A := A) (B := .bvar 0)
          (s := v') hE
          (star_to_develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body)))
      (by
        have wv := parRedStar_weaken
          (.assumption (instantiate0 v' val')) hE (c := 0) ihv
        rw [insertAt_zero] at wv
        exact parRedStar_instantiate_arg hE (c := 1) wv
          (develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body)))

noncomputable def parRedStar_pi_dom_bvar0_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx}
    {A v v' val' body : Expr Nat}
    (ihdom : ParRedStar E n Γ (instantiate0 v' val')
      (develWfGo hE fuel cwt maj Γ v))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v)) :
    ParRedStar E n Γ
      (.pi (instantiate0 v' val')
        (instantiate 1 (lift 0 1 v') body))
      (.pi (develWfGo hE fuel cwt maj Γ v)
        (instantiate 1 (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
          (develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body))) :=
  parRedStar_pi_congr ihdom
    (parRedStar_trans
      (parRedStar_replace_assump
        (A := instantiate0 v' (.bvar 0)) (A' := instantiate0 v' val')
        (parRedStar_instantiate_term1_assump (A := A) (B := .bvar 0)
          (s := v') hE
          (star_to_develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body)))
      (by
        have wv := parRedStar_weaken
          (.assumption (instantiate0 v' val')) hE (c := 0) ihv
        rw [insertAt_zero] at wv
        exact parRedStar_instantiate_arg hE (c := 1) wv
          (develWfGo hE fuel cwt maj
            (.assumption (.bvar 0) :: .assumption A :: Γ) body)))

/-- Join of `let x := v in (fun y => x a)` after zeta: domain drops,
fn is bvar 1 (refl or reduced lookup), arg drops at 1. -/
def parRedStar_lam_app_bvar1_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx}
    {A B B' v v' val' arg arg' : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v))
    (ihfn : ParRedStar E n (.assumption (instantiate0 v' B') :: Γ)
      (instantiate 1 (lift 0 1 v') val')
      (lift 0 1 (develWfGo hE fuel cwt maj Γ v)))
    (iha : ParRedStar E n (.assumption B :: .assumption A :: Γ) arg'
      (develWfGo hE fuel cwt maj (.assumption B :: .assumption A :: Γ) arg)) :
    ParRedStar E n Γ
      (.lam (instantiate0 v' B')
        (.app (instantiate 1 (lift 0 1 v') val')
          (instantiate 1 (lift 0 1 v') arg')))
      (.lam (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (.app (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
          (instantiate 1 (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
            (develWfGo hE fuel cwt maj
              (.assumption B :: .assumption A :: Γ) arg)))) :=
  parRedStar_lam_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    (parRedStar_app_congr ihfn
      (parRedStar_trans
        (parRedStar_replace_assump
          (A := instantiate0 v' B) (A' := instantiate0 v' B')
          (parRedStar_instantiate_term1_assump (A := A) (B := B)
            (s := v') hE iha))
        (by
          have wv := parRedStar_weaken
            (.assumption (instantiate0 v' B')) hE (c := 0) ihv
          rw [insertAt_zero] at wv
          exact parRedStar_instantiate_arg hE (c := 1) wv
            (develWfGo hE fuel cwt maj
              (.assumption B :: .assumption A :: Γ) arg))))

def parRedStar_pi_app_bvar1_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx}
    {A B B' v v' val' arg arg' : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v))
    (ihfn : ParRedStar E n (.assumption (instantiate0 v' B') :: Γ)
      (instantiate 1 (lift 0 1 v') val')
      (lift 0 1 (develWfGo hE fuel cwt maj Γ v)))
    (iha : ParRedStar E n (.assumption B :: .assumption A :: Γ) arg'
      (develWfGo hE fuel cwt maj (.assumption B :: .assumption A :: Γ) arg)) :
    ParRedStar E n Γ
      (.pi (instantiate0 v' B')
        (.app (instantiate 1 (lift 0 1 v') val')
          (instantiate 1 (lift 0 1 v') arg')))
      (.pi (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (.app (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
          (instantiate 1 (lift 0 1 (develWfGo hE fuel cwt maj Γ v))
            (develWfGo hE fuel cwt maj
              (.assumption B :: .assumption A :: Γ) arg)))) :=
  parRedStar_pi_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    (parRedStar_app_congr ihfn
      (parRedStar_trans
        (parRedStar_replace_assump
          (A := instantiate0 v' B) (A' := instantiate0 v' B')
          (parRedStar_instantiate_term1_assump (A := A) (B := B)
            (s := v') hE iha))
        (by
          have wv := parRedStar_weaken
            (.assumption (instantiate0 v' B')) hE (c := 0) ihv
          rw [insertAt_zero] at wv
          exact parRedStar_instantiate_arg hE (c := 1) wv
            (develWfGo hE fuel cwt maj
              (.assumption B :: .assumption A :: Γ) arg))))

/-- Generalized lam join: body star already instantiated at 1. -/
def parRedStar_lam_inst_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx} {A : Expr Nat}
    {v v' B B' bInst : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v))
    (ihbody : ParRedStar E n
      (.assumption (instantiate0 v' B') :: Γ) bInst
      (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :
    ParRedStar E n Γ
      (.lam (instantiate0 v' B') bInst)
      (.lam (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :=
  parRedStar_lam_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    ihbody

def parRedStar_pi_inst_join {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (fuel cwt maj : Nat) {Γ : LCtx} {A : Expr Nat}
    {v v' B B' bInst : Expr Nat}
    (ihB : ParRedStar E n (.assumption A :: Γ) B'
      (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
    (ihv : ParRedStar E n Γ v'
      (develWfGo hE fuel cwt maj Γ v))
    (ihbody : ParRedStar E n
      (.assumption (instantiate0 v' B') :: Γ) bInst
      (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :
    ParRedStar E n Γ
      (.pi (instantiate0 v' B') bInst)
      (.pi (instantiate0 (develWfGo hE fuel cwt maj Γ v)
          (develWfGo hE fuel cwt maj (.assumption A :: Γ) B))
        (lift 0 1 (develWfGo hE fuel cwt maj Γ v))) :=
  parRedStar_pi_congr
    (parRedStar_trans
      (parRedStar_instantiate_term_assump (A := A) hE (s := v') ihB)
      (parRedStar_instantiate_arg hE (c := 0) ihv
        (develWfGo hE fuel cwt maj (.assumption A :: Γ) B)))
    ihbody

/-- More fuel develops at least as far. `fuel ≤ fuel'` →
`devel_fuel e ⇒* devel_fuel' e`. Delta hlt of the Takahashi map
joins prefix-fuel to full-fuel on the reduct. -/
noncomputable def develWfGo_fuel_mono {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (cwt maj : Nat) (Γ : LCtx)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel') :
    (e : Expr Nat) →
    ParRedStar E n Γ (develWfGo hE fuel cwt maj Γ e)
      (develWfGo hE fuel' cwt maj Γ e)
  | .sort l => by
      rw [develWfGo_sort, develWfGo_sort]
      exact .refl _ _
  | .lit t => by
      rw [develWfGo_lit, develWfGo_lit]
      exact .refl _ _
  | .const r ls =>
      match hmem : E.members r with
      | none => by
          rw [develWfGo_const_none (hE := hE) hmem,
            develWfGo_const_none (hE := hE) hmem]
          exact .refl _ _
      | some m =>
          if htr : transparent m.mclass = true then
            match hb : m.body with
            | none => by
                rw [develWfGo_const_nobody (hE := hE) hmem htr hb,
                  develWfGo_const_nobody (hE := hE) hmem htr hb]
                exact .refl _ _
            | some b => by
                let p := envWf_rank (envWf_of_member hE hmem).2.1
                if hlt' : p < fuel' then
                  if hlt : p < fuel then
                    rw [develWfGo_const_delta (hE := hE) hmem htr hb hlt,
                      develWfGo_const_delta (hE := hE) hmem htr hb hlt']
                    exact .refl _ _
                  else
                    cases fuel with
                    | zero =>
                        rw [develWfGo_const_delta_zero (hE := hE) hmem htr hb,
                          develWfGo_const_delta (hE := hE) hmem htr hb hlt']
                        exact star_to_develWfGo hE p cwt maj Γ
                          (instantiateLevels ls b)
                    | succ fuel0 =>
                        rw [develWfGo_const_delta_succ (hE := hE) hmem htr hb
                          hlt,
                          develWfGo_const_delta (hE := hE) hmem htr hb hlt']
                        have hle0 : fuel0 ≤ p := by omega
                        exact develWfGo_fuel_mono hE cwt maj Γ fuel0 p hle0
                          (instantiateLevels ls b)
                else
                  cases fuel with
                  | zero =>
                      cases fuel' with
                      | zero =>
                          exact .refl _ _
                      | succ fuel1 =>
                          have hnl : ¬ p < fuel1 + 1 := hlt'
                          rw [develWfGo_const_delta_zero (hE := hE) hmem htr hb,
                            develWfGo_const_delta_succ (hE := hE) hmem htr hb
                              hnl]
                          exact star_to_develWfGo hE fuel1 cwt maj Γ
                            (instantiateLevels ls b)
                  | succ fuel0 =>
                      cases fuel' with
                      | zero => omega
                      | succ fuel1 =>
                          have hnl : ¬ p < fuel0 + 1 := by omega
                          have hnl' : ¬ p < fuel1 + 1 := hlt'
                          rw [develWfGo_const_delta_succ (hE := hE) hmem htr hb
                            hnl,
                            develWfGo_const_delta_succ (hE := hE) hmem htr hb
                              hnl']
                          have hle0 : fuel0 ≤ fuel1 := by omega
                          exact develWfGo_fuel_mono hE cwt maj Γ fuel0 fuel1
                            hle0 (instantiateLevels ls b)
          else by
            have hfalse : transparent m.mclass = false := by
              cases htr' : transparent m.mclass <;> simp_all
            rw [develWfGo_const_opaque (hE := hE) hmem hfalse,
              develWfGo_const_opaque (hE := hE) hmem hfalse]
            exact .refl _ _
  | .bvar i => by
      match hg : getLet Γ i with
      | none =>
          rw [develWfGo_bvar_none (h := hg),
            develWfGo_bvar_none (h := hg)]
          exact .refl _ _
      | some (stored, tail) =>
          rw [develWfGo_bvar_some (h := hg),
            develWfGo_bvar_some (h := hg)]
          have ih := develWfGo_fuel_mono hE cwt maj tail fuel fuel' hle stored
          have hsplit := getLet_split hg
          let pre := hsplit.fst
          let A := hsplit.snd.fst
          let hΓ := hsplit.snd.snd.fst
          let hlen := hsplit.snd.snd.snd
          have hs :=
            parRedStar_lift_append hE
              (pre ++ [LocalDecl.letBinding A stored]) ih
          have hlen' :
              (pre ++ [LocalDecl.letBinding A stored]).length = i + 1 := by
            rw [List.length_append, hlen]
            rfl
          rw [hlen'] at hs
          have hctx :
              (pre ++ [LocalDecl.letBinding A stored]) ++ tail = Γ := by
            rw [List.append_assoc]
            exact hΓ.symm
          rw [hctx] at hs
          exact hs
  | .lam A b => by
      rw [develWfGo_lam, develWfGo_lam]
      exact parRedStar_lam_congr
        (develWfGo_fuel_mono hE cwt maj Γ fuel fuel' hle A)
        (parRedStar_replace_assump
          (develWfGo_fuel_mono hE cwt maj (.assumption A :: Γ)
            fuel fuel' hle b))
  | .pi A B => by
      rw [develWfGo_pi, develWfGo_pi]
      exact parRedStar_pi_congr
        (develWfGo_fuel_mono hE cwt maj Γ fuel fuel' hle A)
        (parRedStar_replace_assump
          (develWfGo_fuel_mono hE cwt maj (.assumption A :: Γ)
            fuel fuel' hle B))
  | .letE A v b => by
      rw [develWfGo_letE, develWfGo_letE]
      exact parRedStar_instantiate_zeta (A := A)
        (v := develWfGo hE fuel' cwt maj Γ v)
        (v' := develWfGo hE fuel cwt maj Γ v)
        (b := develWfGo hE fuel' cwt maj (.assumption A :: Γ) b)
        (b' := develWfGo hE fuel cwt maj (.assumption A :: Γ) b)
        hE
        (develWfGo_fuel_mono hE cwt maj Γ fuel fuel' hle v)
        (parRedStar_assump_to_let (A := A) (A' := A)
          (v := develWfGo hE fuel' cwt maj Γ v)
          (develWfGo_fuel_mono hE cwt maj (.assumption A :: Γ)
            fuel fuel' hle b))
  | .app f a =>
      match hc : iotaReductCert E (.app f a) with
      | some ⟨w, hlhs⟩ => by
          rw [develWfGo_app_some (h := hc),
            develWfGo_app_some (h := hc)]
          if hlt : exprSize (ctorMajor w) < maj then
            simp only [hlt]
            exact develWfGo_fuel_mono hE cwt (exprSize (ctorMajor w)) Γ
              fuel fuel' hle (iotaRhsOf w)
          else
            simp only [hlt]
            exact .refl _ _
      | none => by
          rw [develWfGo_app_none (h := hc),
            develWfGo_app_none (h := hc)]
          have hf := develWfGo_fuel_mono hE cwt maj Γ fuel fuel' hle f
          have ha := develWfGo_fuel_mono hE cwt maj Γ fuel fuel' hle a
          cases hdf : develWfGo hE fuel cwt maj Γ f with
          | lam A b =>
              have hf' :
                  ParRedStar E n Γ (.lam A b)
                    (develWfGo hE fuel' cwt maj Γ f) := by
                rw [← hdf]; exact hf
              have ⟨A', b', heq', _, hb'⟩ := parRedStar_lam hf' rfl
              rw [heq']
              exact parRedStar_instantiate_beta hE ha hb'
          | _ =>
              have hf' :
                  ParRedStar E n Γ (develWfGo hE fuel cwt maj Γ f)
                    (develWfGo hE fuel' cwt maj Γ f) := hf
              rw [hdf] at hf'
              cases hdf' : develWfGo hE fuel' cwt maj Γ f with
              | lam A' b' =>
                  rw [hdf'] at hf'
                  have hcongr := parRedStar_app_congr hf' ha
                  exact parRedStar_trans hcongr
                    (parRedStar_one
                      (.beta Γ A' A' b' b'
                        (develWfGo hE fuel' cwt maj Γ a)
                        (develWfGo hE fuel' cwt maj Γ a)
                        (.refl _ _) (.refl _ _) (.refl _ _)))
              | _ =>
                  rw [hdf'] at hf'
                  exact parRedStar_app_congr hf' ha
termination_by e => (fuel', fuel, letsCount Γ, cwt, maj, exprSize e)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.left _ _ ‹_›
      | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
      | refine Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | refine Prod.Lex.right _ (Prod.Lex.left _ _ ‹_›)
      | refine Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self _))
      | refine Prod.Lex.right _
          (Prod.Lex.right _ (Prod.Lex.left _ _ (getLet_letsCount ‹_›)))
      | refine Prod.Lex.right _
          (Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.zero_le _)))
      | refine Prod.Lex.right _
          (Prod.Lex.right _
            (Prod.Lex.right (letsCount Γ)
              (Prod.Lex.right cwt (Prod.Lex.left _ _ ‹_›))))
      | refine Prod.Lex.right _
          (Prod.Lex.right _
            (Prod.Lex.right (letsCount Γ)
              (Prod.Lex.right cwt (Prod.Lex.right maj ?_))))
        first
          | exact exprSize_lam_dom _ _
          | exact exprSize_lam_body _ _
          | exact exprSize_pi_dom _ _
          | exact exprSize_pi_body _ _
          | exact exprSize_let_val _ _ _
          | exact exprSize_let_body _ _ _
          | exact exprSize_app_left _ _
          | exact exprSize_app_right _ _

theorem iotaReductCert_eq_arg {E : ResolvedEnv} {e e' : Expr Nat}
    (heq : e = e') {w : IotaWitness E} {hlhs : iotaLhsOf w = e}
    (h : iotaReductCert E e = some ⟨w, hlhs⟩) :
    iotaReductCert E e' = some ⟨w, heq ▸ hlhs⟩ := by
  subst heq
  exact h

end Rcic.Declarative
