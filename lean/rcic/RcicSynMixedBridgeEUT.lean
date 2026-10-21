import rcic.RcicSynA6Span
import rcic.RcicSynLetRel

/-!
# BelowC mixed interpreter, part 2 — §5.4 the bridge MEUT across a changed declaration

`research/rcic/sortrow/BELOWC_MIXED_INTERPRETER.md` §5.4 (docs PR #7477), on the landed A6
span (`RcicSynA6Span`, `binderSpanZero`) and the landed ES transport arms (`RcicSynES`).

Two surviving `bvar`s reaching slot `0` under a changed declaration `cA : A ≡ A' : sort w`
have the terminal representatives `JL`, `JR` and the endpoint views `PL = wk₀ cA.dl`,
`PR = wk₀ cA.dr` of the span. Their MEUT is the chain

    e[JL] ≈ e[PL] ≈ e[PR] ≈ e[JR]

whose outer links are the two C legs (`CL` requests: same subject and context on each side)
and whose middle is **the actual `ES[cA]` through its prefix** — `es_wk_keep` /
`es_wk_not_keep` by the display's head at the inserted slot — and through the remaining
erased actions (`convMod_applyActs`). The erasure of a `wk` node never reads the inserted
declaration (`eps_wk_decl_irrel`), so the left and right declarations may differ, as they
do across a changed binder. The gate equality of the two sides (`BinderSpan.middle` is the
scalar on the bridge's recorded sort) is not enough: the domain erasures need the ES, which
is why the mixed MEUT worker reserves `ES[cA]` for every bridge the correspondence can
traverse (the unary `BodyAnswers` does not). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 conversion through an erased action word -/

/-- A conversion survives an erased action word: lifts by `convMod_lift`, instantiations at a
    common replacement by `convMod_inst_body`. No star-status premise (contrast
    `rel_applyActs`, which carries `Rel`). -/
theorem convMod_applyActs {tbl : List CRule} (hcl : TableClosed tbl) :
    (as : List EAct) → {s t : ETm} → ConvMod (EStep tbl) LvlEq s t →
      ConvMod (EStep tbl) LvlEq (applyActs as s) (applyActs as t)
  | [], _, _, h => h
  | .lift κ :: as, _, _, h => by
      rw [applyActs_cons, applyActs_cons]
      exact convMod_applyActs hcl as (convMod_lift hcl h κ 1)
  | .inst κ r :: as, _, _, h => by
      rw [applyActs_cons, applyActs_cons]
      exact convMod_applyActs hcl as (convMod_inst_body hcl h κ r)

/-! ## §2 the bridge through its prefix -/

/-- The erasure of a `wk` node does not read the inserted declaration. -/
theorem eps_wk_decl_irrel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (d d' : LocalDecl) (c : Nat) (D : TyP E n Γ e A) (σ : Level → Level) (ρ : List Disp) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = (TyP.wk E n Γ e A d' c D).eps σ ρ := rfl

/-- §5.4 the bridge through its prefix at slot `0`, with arbitrary left / right declarations:
    `ES[cA]` at the tail display makes the two lifted endpoint views `wk₀ cA.dl` / `wk₀ cA.dr`
    convertible (`es_wk_keep` / `es_wk_not_keep` by the display's head). -/
theorem convMod_bridge_zero {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    {σ : Level → Level} {ρ : List Disp} (hES : ES tbl σ (removeAt ρ 0) cA) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.wk E n Γ A (.sort w) declL 0 cA.dl).eps σ ρ)
      ((TyP.wk E n Γ A' (.sort w) declR 0 cA.dr).eps σ ρ) := by
  have key : ES tbl σ ρ (CvP.wk E n Γ A A' (.sort w) declR 0 cA) := by
    rcases hk : ρ[0]? with _ | d
    · exact es_wk_not_keep cA (.inl hk) hES
    · cases d with
      | keep => exact es_wk_keep hcl cA hk hES
      | drop => exact es_wk_not_keep cA (.inr (.inl hk)) hES
      | inline v => exact es_wk_not_keep cA (.inr (.inr ⟨v, hk⟩)) hES
  rw [eps_wk_decl_irrel declL declR]
  simpa only [ES, CvP.dl, CvP.dr] using key

/-- The same through the remaining erased actions. -/
theorem convMod_bridge_zero_acts {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    {σ : Level → Level} {ρ : List Disp} (hES : ES tbl σ (removeAt ρ 0) cA)
    (acts : List EAct) :
    ConvMod (EStep tbl) LvlEq
      (applyActs acts ((TyP.wk E n Γ A (.sort w) declL 0 cA.dl).eps σ ρ))
      (applyActs acts ((TyP.wk E n Γ A' (.sort w) declR 0 cA.dr).eps σ ρ)) :=
  convMod_applyActs hcl acts (convMod_bridge_zero hcl cA declL declR hES)

/-! ## §3 the chain on the span -/

/-- The slot-`0` span's left endpoint view reads back as `wk₀ cA.dl`. -/
theorem binderSpanZero_PL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    (hL : LocalDecl.ty declL = A) (hR : LocalDecl.ty declR = A')
    (sL : Survivor E n (declL :: Γ) 0) (sR : Survivor E n (declR :: Γ) 0) :
    (binderSpanZero cA declL declR hL hR sL sR).PL = TyP.wk E n Γ A (.sort w) declL 0 cA.dl :=
  rfl

/-- The slot-`0` span's right endpoint view reads back as `wk₀ cA.dr`. -/
theorem binderSpanZero_PR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    (hL : LocalDecl.ty declL = A) (hR : LocalDecl.ty declR = A')
    (sL : Survivor E n (declL :: Γ) 0) (sR : Survivor E n (declR :: Γ) 0) :
    (binderSpanZero cA declL declR hL hR sL sR).PR = TyP.wk E n Γ A' (.sort w) declR 0 cA.dr :=
  rfl

/-- §5.4 on any span: C leg, bridge middle, C leg — `e[JL] ≈ e[PL] ≈ e[PR] ≈ e[JR]`. -/
theorem mixedEUT_span_of_bridge {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {ΓL ΓR : LCtx}
    {j : Nat} (sp : BinderSpan E n ΓL ΓR j) {σ : Level → Level} {ρ : List Disp}
    (qL : CL tbl σ ρ sp.JL sp.PL)
    (hbr : ConvMod (EStep tbl) LvlEq (sp.PL.eps σ ρ) (sp.PR.eps σ ρ))
    (qR : CL tbl σ ρ sp.PR sp.JR) :
    ConvMod (EStep tbl) LvlEq (sp.JL.eps σ ρ) (sp.JR.eps σ ρ) :=
  ConvMod.trans qL (ConvMod.trans hbr qR)

/-- §5.4 at a changed declaration, slot `0`: the two C legs of the span and the actual
    `ES[cA]` through the prefix. -/
theorem mixedEUT_bridge_zero {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    (hL : LocalDecl.ty declL = A) (hR : LocalDecl.ty declR = A')
    (sL : Survivor E n (declL :: Γ) 0) (sR : Survivor E n (declR :: Γ) 0)
    {σ : Level → Level} {ρ : List Disp} (hES : ES tbl σ (removeAt ρ 0) cA)
    (qL : CL tbl σ ρ (binderSpanZero cA declL declR hL hR sL sR).JL
      (binderSpanZero cA declL declR hL hR sL sR).PL)
    (qR : CL tbl σ ρ (binderSpanZero cA declL declR hL hR sL sR).PR
      (binderSpanZero cA declL declR hL hR sL sR).JR) :
    ConvMod (EStep tbl) LvlEq
      ((binderSpanZero cA declL declR hL hR sL sR).JL.eps σ ρ)
      ((binderSpanZero cA declL declR hL hR sL sR).JR.eps σ ρ) :=
  mixedEUT_span_of_bridge (binderSpanZero cA declL declR hL hR sL sR) qL
    (by
      rw [binderSpanZero_PL, binderSpanZero_PR]
      exact convMod_bridge_zero hcl cA declL declR hES)
    qR

end Rcic.Syn

#print axioms Rcic.Syn.convMod_applyActs
#print axioms Rcic.Syn.eps_wk_decl_irrel
#print axioms Rcic.Syn.convMod_bridge_zero
#print axioms Rcic.Syn.convMod_bridge_zero_acts
#print axioms Rcic.Syn.binderSpanZero_PL
#print axioms Rcic.Syn.binderSpanZero_PR
#print axioms Rcic.Syn.mixedEUT_span_of_bridge
#print axioms Rcic.Syn.mixedEUT_bridge_zero
