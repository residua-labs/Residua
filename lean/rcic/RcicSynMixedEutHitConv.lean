import rcic.RcicSynRegStep
import rcic.RcicSynInst

/-!
# Syntactic sortRow, S18 §5 — conv outside the hit bvar: original-source chains

`research/rcic/sortrow/S18_MIXED_EUT_SUBST_HIT.md` §5 (and §2 for `reg`).

For `H = τ (TyP.conv d c)` — a `conv` sitting outside the hit `bvar` — `H`'s
regularity view is `τ(c.dr)`. The step issues three original-source chains:
`q₁ = MixedEUT [L, τ-view(d)]`, `q₂ = CL [τ-view(d.reg.2), τ-view(c.dl)]`,
`q₃ = ES` of the same τ-view of the original `c`, composed
`L.reg ↔ τ(d.reg) ↔ τ(c.dl) ↔ τ(c.dr) = H.reg`. No `CvP.esub c …` is ever built
as an original child: this module records the conv atom's real content, the three
`DMStep` edges on §5's exact occurrence tables (V/W counted once, in the kept
tail), and the composition — hypotheses only, no supplier.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `reg` reads the conv's `dr`; transports keep that equation -/

/-- `H.reg.2`'s source half: a `conv` node's regularity is the conversion's right
    endpoint `c.dr` (`TyP.reg`, `RcicConvPlus`). Definitional. -/
theorem reg_conv_snd {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat}
    {u : Level} {d : TyP E n Γ e A} {c : CvP E n Γ A B (.sort u)} :
    (TyP.conv E n Γ e A B u d c).reg.2 = c.dr := rfl

/-- `τ(c.dr) = H.reg.2` for the esub transport: `(esub (conv d c)).reg.2` is `esub`
    applied to the original `c.dr`. Definitional. -/
theorem reg_esub_conv_snd {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B t v : Expr Nat} {j : Nat} {u w : Level}
    {d : TyP E n Γ e A} {c : CvP E n Γ A B (.sort u)}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort w)} :
    (TyP.esub E n Γ e B t v j w (TyP.conv E n Γ e A B u d c) hget hv hvT).reg.2 =
      TyP.esub E n Γ B (.sort u) t v j w c.dr hget hv hvT := rfl

/-- the same equation for the let-binding transport `lsub`. Definitional. -/
theorem reg_lsub_conv_snd {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B t v : Expr Nat} {j : Nat} {u w : Level}
    {d : TyP E n Γ e A} {c : CvP E n Γ A B (.sort u)}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort w)} :
    (TyP.lsub E n Γ e B t v j w (TyP.conv E n Γ e A B u d c) hget hv hvT).reg.2 =
      TyP.lsub E n Γ B (.sort u) t v j w c.dr hget hv hvT := rfl

/-! ## §2 the conv atom's content — and what a materialized child would carry -/

/-- the `conv` atom in the caller's table is exactly `1 + d.wt + c.wt`
    (`TyP.atoms`, `TyP.wt`). Definitional. -/
theorem conv_atoms_eq (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) :
    (TyP.conv E n Γ e A B u d c).atoms Aw = [1 + d.wt Aw + c.wt Aw] := rfl

/-- the forbidden route, recorded: a materialized `CvP.esub c …` child would carry
    `at(c) ++ at(hv) ++ at(hvT)` — the replacement typings `hv`/`hvT` a second time —
    not `c`'s atoms alone. It is a transport node, never an original child of `c`. -/
theorem cvP_esub_atoms_eq (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T t v : Expr Nat} {j : Nat} {u : Level}
    (h : CvP E n Γ a b T) {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)} :
    (CvP.esub E n Γ a b T t v j u h hget hv hvT).atoms Aw =
      h.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := rfl

/-! ## §3 the three request edges on §5's exact occurrence tables -/

/-- §5 q₁ — `MixedEUT [L, τ-view d]`: `at(L) ++ at(d) ++ at(V) ++ at(W)` is strictly
    below `at(L) ++ [1 + d.wt + c.wt] ++ at(V) ++ at(W)`. The conv atom pays `d`'s
    real atoms; `L`, `V`, `W` keep their original counts (the kept tail `Z`). -/
theorem s18hitConv_q1_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (atL atV atW : List Nat) :
    DMStep (atL ++ d.atoms Aw ++ atV ++ atW)
      (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW) := by
  have inner : DMStep (d.atoms Aw ++ (atV ++ atW))
      ([1 + d.wt Aw + c.wt Aw] ++ (atV ++ atW)) :=
    ⟨[1 + d.wt Aw + c.wt Aw], d.atoms Aw, atV ++ atW,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, fun y hy =>
        ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, by
          have := TyP.atoms_le Aw d y hy; omega⟩⟩
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_ (dmStep_append_left inner atL))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §5 q₂ — `CL [τ-view(d.reg.2), τ-view(c.dl)]`: `at(d.reg.2) ++ at(c.dl) ++
    at(V) ++ at(W)` is strictly below the caller's row. `L` is unread and dropped
    (inside the removed `X`); the conv atom alone pays both fresh halves. -/
theorem s18hitConv_q2_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (atL atV atW : List Nat) :
    DMStep (d.reg.2.atoms Aw ++ c.dl.atoms Aw ++ atV ++ atW)
      (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW) := by
  refine ⟨atL ++ [1 + d.wt Aw + c.wt Aw], d.reg.2.atoms Aw ++ c.dl.atoms Aw,
    atV ++ atW, by
      intro h; exact List.cons_ne_nil _ _ (List.append_eq_nil.mp h).2, ?_, ?_, ?_⟩
  · rw [List.append_assoc]
  · rw [List.append_assoc]
  · intro y hy
    refine ⟨1 + d.wt Aw + c.wt Aw, List.mem_append_right _ (List.mem_cons_self _ _), ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · have h1 := TyP.atoms_le Aw d.reg.2 y hy
      have h2 := TyP.wt_reg_le Aw d
      omega
    · have h1 := TyP.atoms_le Aw c.dl y hy
      have h2 := CvP.wt_dl_lt Aw c
      omega

/-- §5 q₃ — `ES` of the same τ-view of the original `c`: `at(c) ++ at(V) ++ at(W)`
    is strictly below the caller's row; the conv atom pays `c`'s real atoms and
    the unread `L` is dropped with it. -/
theorem s18hitConv_q3_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (atL atV atW : List Nat) :
    DMStep (c.atoms Aw ++ atV ++ atW)
      (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW) := by
  refine ⟨atL ++ [1 + d.wt Aw + c.wt Aw], c.atoms Aw, atV ++ atW, by
      intro h; exact List.cons_ne_nil _ _ (List.append_eq_nil.mp h).2, ?_, ?_, ?_⟩
  · rw [List.append_assoc]
  · rw [List.append_assoc]
  · intro y hy
    exact ⟨1 + d.wt Aw + c.wt Aw, List.mem_append_right _ (List.mem_cons_self _ _),
      by have := CvP.atoms_le Aw c y hy; omega⟩

/-- the q₁ edge with §5's kept-live prefix `Klive` (the `K` fields still read by a
    route stay, appended on the left). -/
theorem s18hitConv_q1_dm_k (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (Klive atL atV atW : List Nat) :
    DMStep (Klive ++ (atL ++ d.atoms Aw ++ atV ++ atW))
      (Klive ++ (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW)) :=
  dmStep_append_left (s18hitConv_q1_dm Aw d c atL atV atW) Klive

/-- the q₂ edge under the kept-live prefix. -/
theorem s18hitConv_q2_dm_k (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (Klive atL atV atW : List Nat) :
    DMStep (Klive ++ (d.reg.2.atoms Aw ++ c.dl.atoms Aw ++ atV ++ atW))
      (Klive ++ (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW)) :=
  dmStep_append_left (s18hitConv_q2_dm Aw d c atL atV atW) Klive

/-- the q₃ edge under the kept-live prefix. -/
theorem s18hitConv_q3_dm_k (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (d : TyP E n Γ e A) (c : CvP E n Γ A B (.sort u)) (Klive atL atV atW : List Nat) :
    DMStep (Klive ++ (c.atoms Aw ++ atV ++ atW))
      (Klive ++ (atL ++ [1 + d.wt Aw + c.wt Aw] ++ atV ++ atW)) :=
  dmStep_append_left (s18hitConv_q3_dm Aw d c atL atV atW) Klive

/-! ## §4 the composition -/

/-- §5's composed chain `L.reg ↔ τ(d.reg) ↔ τ(c.dl) ↔ τ(c.dr) = H.reg`: the three
    answers `h1`/`h2`/`h3` compose into the regularity conclusion. Hypotheses only;
    `τ(c.dr) = H.reg.2` itself is `reg_esub_conv_snd`/`reg_lsub_conv_snd`. -/
theorem mixedEUT_hit_conv_compose {tbl : List CRule} {εLreg τdreg τcdl τcdr : ETm}
    (h1 : ConvMod (EStep tbl) LvlEq εLreg τdreg)
    (h2 : ConvMod (EStep tbl) LvlEq τdreg τcdl)
    (h3 : ConvMod (EStep tbl) LvlEq τcdl τcdr) :
    ConvMod (EStep tbl) LvlEq εLreg τcdr :=
  h1.trans (h2.trans h3)

end Rcic.Syn

#print axioms Rcic.Syn.reg_conv_snd
#print axioms Rcic.Syn.reg_esub_conv_snd
#print axioms Rcic.Syn.reg_lsub_conv_snd
#print axioms Rcic.Syn.conv_atoms_eq
#print axioms Rcic.Syn.cvP_esub_atoms_eq
#print axioms Rcic.Syn.s18hitConv_q1_dm
#print axioms Rcic.Syn.s18hitConv_q2_dm
#print axioms Rcic.Syn.s18hitConv_q3_dm
#print axioms Rcic.Syn.s18hitConv_q1_dm_k
#print axioms Rcic.Syn.s18hitConv_q2_dm_k
#print axioms Rcic.Syn.s18hitConv_q3_dm_k
#print axioms Rcic.Syn.mixedEUT_hit_conv_compose
