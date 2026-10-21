import rcic.RcicERScope2
import rcic.RcicSynLetBridge

/-!
# BelowC mixed interpreter, part 2 — §4.1 the `lsub` same-stage scope, discharged

`research/rcic/sortrow/BELOWC_MIXED_INTERPRETER.md` §4 "Transport preparation" (docs PR
#7477): for an `lsub` hit the worker needs `AvoidPrefix (countKeep (ρ.take j)) 0 (V.ε μ ρ)`,
"from the R2 support corollary on the original shifted `V` and the stage's prefix shape;
one stage-parametric structural theorem instantiated per node; this discharges #7452's
per-node hypothesis".

The structural theorem is S14 §6 `shifted_value_scope` (`RcicERScope2`, #7407): from the
value's `AssumpPref` and the stage's `DisplayFits` alone, no `AvoidPrefix` assumed. Here it is
instantiated at exactly the node's stage — the stage map `stageMap μ' (steps ss)` and the left
display `δ` — in the shape the LetBridge record carries (`lsub_scope_of_fits`), and the
`lsub` arm of `BodyAnswers` is given without its scope conjunct
(`bodyAnswers_lsub_of_fits`, `bodyAnswers_lsub_iff`): a builder of the per-node answers
supplies the per-stage `PBit`, the value's and the child's answers, and the two structural
facts the LetBridge induction threads to every node anyway (`letBridge` takes `AssumpPref`
and `DisplayFits` at the root and passes `hAP.2.2.1`, `hfit` to this very node). The same
instantiation discharges the `hScope` premise of the one-hit `lsub`/non-★ equation
(`lsub_hit_eps_eq_inline`, #7457).

The landed `BodyAnswers` keeps its conjunct (no landed statement is changed, and a second
copy of the family would be an inline copy); the conjunct is now redundant at every node
by these lemmas. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- §4.1 the per-node same-stage scope certificate at an original `lsub`, as the LetBridge
    record states it: `shifted_value_scope` at the node's map and display. -/
theorem lsub_scope_of_fits {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat}
    (σ : Level → Level) {δ : List Disp}
    (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hAP : hv.AssumpPref) (hfit : DisplayFits (substRemove v j Γ) δ) :
    hv.eps σ δ ≠ .star → AvoidPrefix (countKeep (δ.take j)) 0 (hv.eps σ δ) :=
  fun _ => shifted_value_scope σ hget hv hAP hfit

/-- §4.1 the `lsub` arm of `BodyAnswers` without its scope conjunct: the per-stage `PBit`, the
    value's answers and the child's answers at the stage `tyAtLet` visits it, plus the two
    structural facts of the node. -/
theorem bodyAnswers_lsub_of_fits {E : ResolvedEnv} {n : Nat} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (tbl : List CRule) (μ' : Level → Level) {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    {nIn : Nat} {Γ0 : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {e0 A0 t v : Expr Nat} {j : Nat} {u : Level}
    (Di : TyP Ei nIn Γ0 e0 A0) (hget : Γ0[j]? = some (.letBinding t v))
    (hv : TyP Ei nIn (substRemove v j Γ0) (lift 0 j v) (lift 0 j t))
    (hvT : TyP Ei nIn (substRemove v j Γ0) (lift 0 j t) (.sort u))
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ0))
    (δ : List Disp) (acts : List EAct) (s : Sites ss) (ρ' : List Disp)
    (hpb : PBit (stageMap μ' (steps ss)) δ hv hvT)
    (hAPv : hv.AssumpPref) (hfit : DisplayFits (substRemove v j Γ0) δ)
    (hansv : BodyAnswers hW ι ιenv tbl μ' hext hv p δ acts s ρ')
    (hansD : BodyAnswers hW ι ιenv tbl μ' hext Di
      (packLLsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
      (insertDisp (lsubDisp (countKeep (δ.take j)) (hv.eps (stageMap μ' (steps ss)) δ)) j δ) acts
      (.lsub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
        ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
        (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
        (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ') :
    BodyAnswers hW ι ιenv tbl μ' hext (TyP.lsub Ei nIn Γ0 e0 A0 t v j u Di hget hv hvT)
      p δ acts s ρ' := by
  show PBit (stageMap μ' (steps ss)) δ hv hvT ∧ _ ∧ _ ∧ _
  exact ⟨hpb, lsub_scope_of_fits (stageMap μ' (steps ss)) hget hv hAPv hfit, hansv, hansD⟩

/-- §4.1 at an `lsub` node the scope conjunct is redundant: `BodyAnswers` there is exactly the
    per-stage `PBit` with the value's and the child's answers. -/
theorem bodyAnswers_lsub_iff {E : ResolvedEnv} {n : Nat} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (tbl : List CRule) (μ' : Level → Level) {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    {nIn : Nat} {Γ0 : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {e0 A0 t v : Expr Nat} {j : Nat} {u : Level}
    (Di : TyP Ei nIn Γ0 e0 A0) (hget : Γ0[j]? = some (.letBinding t v))
    (hv : TyP Ei nIn (substRemove v j Γ0) (lift 0 j v) (lift 0 j t))
    (hvT : TyP Ei nIn (substRemove v j Γ0) (lift 0 j t) (.sort u))
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ0))
    (δ : List Disp) (acts : List EAct) (s : Sites ss) (ρ' : List Disp)
    (hAPv : hv.AssumpPref) (hfit : DisplayFits (substRemove v j Γ0) δ) :
    BodyAnswers hW ι ιenv tbl μ' hext (TyP.lsub Ei nIn Γ0 e0 A0 t v j u Di hget hv hvT)
        p δ acts s ρ' ↔
      (PBit (stageMap μ' (steps ss)) δ hv hvT ∧
        BodyAnswers hW ι ιenv tbl μ' hext hv p δ acts s ρ' ∧
        BodyAnswers hW ι ιenv tbl μ' hext Di
          (packLLsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
          (insertDisp (lsubDisp (countKeep (δ.take j)) (hv.eps (stageMap μ' (steps ss)) δ)) j δ)
          acts
          (.lsub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
            ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
            (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
            (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ') := by
  constructor
  · intro h
    obtain ⟨hpb, -, hansv, hansD⟩ := h
    exact ⟨hpb, hansv, hansD⟩
  · intro h
    obtain ⟨hpb, hansv, hansD⟩ := h
    exact bodyAnswers_lsub_of_fits hW ι ιenv tbl μ' hext Di hget hv hvT p δ acts s ρ' hpb hAPv hfit
      hansv hansD

end Rcic.Syn

#print axioms Rcic.Syn.lsub_scope_of_fits
#print axioms Rcic.Syn.bodyAnswers_lsub_of_fits
#print axioms Rcic.Syn.bodyAnswers_lsub_iff
