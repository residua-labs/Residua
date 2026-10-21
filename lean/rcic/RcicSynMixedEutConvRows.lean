import rcic.RcicSynMixedEutHitConv
import rcic.RcicSynES
import rcic.RcicSynBelow
import rcic.RcicSynPack

/-!
# Syntactic sortRow, S17 §4 — the HE request-table rows for `conv`

`research/rcic/sortrow/S17_MIXED_BIT_STEP.md` §4.

Right row `H = conv d c`: the current case's real requests are
`MixedEUT[I, d]`, `ES[c]`, `CL[d.reg.2, c.dl]`, plus the original endpoint
composition. Payment: the original `H` rule atom `1 + d.wt + c.wt`
(`conv_atoms_eq`, `RcicSynMixedEutHitConv`) is deleted; `I` is kept exactly
once in every request's live table; the `d`/`c`/`reg` fields are really
smaller — every child atom is strictly below the removed conv atom.

Left row `I = conv d c`: `MixedEUT[d, H]`, `ES[c]`, and the left side's real
reg/endpoint `CL[d.reg.2, c.dl]`. The original `I` rule atom is deleted; the
auxiliary requests keep the original suffix route (`H` once), never restoring
the full caller context plus `I`.

Every theorem is a local composition: the three answers arrive as hypotheses
and are only `ConvMod.trans`/symmetry-composed. The current `HE` is never an
input, and no same-rank `MixedBit`/`MixedEUT` answer is assumed recursively.
The endpoint equation `(conv d c).reg.2 = c.dr` is the definitional
`reg_conv_snd` of `RcicSynMixedEutHitConv`.

The rows are **mixed** in S17 §1's sense: `I` and `H` carry their own
`EI nI ΓI` / `EH nH ΓH` and their own erased-context routes `σI ρI` /
`σH ρH`; the `conv` lives on one side only. The two sides are linked only by
the displayed mixed-request hypotheses — never by a shared context.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 right row `H = conv d c` — the three request edges -/

/-- §4 right q₁ — `MixedEUT [I, d]`: the child live table
    `K ++ at(I) ++ at(d) ++ Z` is strictly below the caller's
    `K ++ at(I) ++ [1 + d.wt + c.wt] ++ Z`. The conv atom pays `d`'s real
    atoms; `I` is kept once. `I` and the `conv` may live in different
    environments/contexts — the edge only reads their atoms. -/
theorem s17convR_q1_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {eI TI e A B : Expr Nat} {u : Level}
    (I : TyP EI nI ΓI eI TI) (d : TyP EH nH ΓH e A) (c : CvP EH nH ΓH A B (.sort u))
    (K Z : List Nat) :
    DMStep (K ++ I.atoms Aw ++ d.atoms Aw ++ Z)
      (K ++ I.atoms Aw ++ [1 + d.wt Aw + c.wt Aw] ++ Z) := by
  have inner : DMStep (d.atoms Aw ++ Z)
      ([1 + d.wt Aw + c.wt Aw] ++ Z) :=
    ⟨[1 + d.wt Aw + c.wt Aw], d.atoms Aw, Z,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, fun y hy =>
        ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, by
          have := TyP.atoms_le Aw d y hy; omega⟩⟩
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_
    (dmStep_append_left inner (K ++ I.atoms Aw)))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 right q₂ — `ES [c]`: the child live table
    `K ++ at(I) ++ at(c) ++ Z` is strictly below the caller's row; the conv
    atom pays `c`'s real atoms, `I` kept once. -/
theorem s17convR_q2_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {eI TI e A B : Expr Nat} {u : Level}
    (I : TyP EI nI ΓI eI TI) (d : TyP EH nH ΓH e A) (c : CvP EH nH ΓH A B (.sort u))
    (K Z : List Nat) :
    DMStep (K ++ I.atoms Aw ++ c.atoms Aw ++ Z)
      (K ++ I.atoms Aw ++ [1 + d.wt Aw + c.wt Aw] ++ Z) := by
  have inner : DMStep (c.atoms Aw ++ Z)
      ([1 + d.wt Aw + c.wt Aw] ++ Z) :=
    ⟨[1 + d.wt Aw + c.wt Aw], c.atoms Aw, Z,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, fun y hy =>
        ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, by
          have := CvP.atoms_le Aw c y hy; omega⟩⟩
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_
    (dmStep_append_left inner (K ++ I.atoms Aw)))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 right q₃ — `CL [d.reg.2, c.dl]`: the child live table
    `K ++ at(I) ++ at(d.reg.2) ++ at(c.dl) ++ Z` is strictly below the
    caller's row; the conv atom alone pays both fresh halves (`d.reg.2`'s
    atoms via `wt_reg_le`, `c.dl`'s via `wt_dl_lt`), `I` kept once. -/
theorem s17convR_q3_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {eI TI e A B : Expr Nat} {u : Level}
    (I : TyP EI nI ΓI eI TI) (d : TyP EH nH ΓH e A) (c : CvP EH nH ΓH A B (.sort u))
    (K Z : List Nat) :
    DMStep (K ++ I.atoms Aw ++ d.reg.2.atoms Aw ++ c.dl.atoms Aw ++ Z)
      (K ++ I.atoms Aw ++ [1 + d.wt Aw + c.wt Aw] ++ Z) := by
  have inner : DMStep ((d.reg.2.atoms Aw ++ c.dl.atoms Aw) ++ Z)
      ([1 + d.wt Aw + c.wt Aw] ++ Z) := by
    refine ⟨[1 + d.wt Aw + c.wt Aw], d.reg.2.atoms Aw ++ c.dl.atoms Aw, Z,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, ?_⟩
    intro y hy
    refine ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · have h1 := TyP.atoms_le Aw d.reg.2 y hy
      have h2 := TyP.wt_reg_le Aw d
      omega
    · have h1 := TyP.atoms_le Aw c.dl y hy
      have h2 := CvP.wt_dl_lt Aw c
      omega
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_
    (dmStep_append_left inner (K ++ I.atoms Aw)))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 right composition — `I.reg ↔ d.reg ↔ c.dl ↔ c.dr = H.reg`: the three
    answers `hMEUT`/`hES`/`hCL` compose into the `MixedEUT [I, conv d c]`
    conclusion on the real regularity endpoints. Hypotheses only; the current
    `HE` is never an input. `(conv d c).reg.2 = c.dr` is `reg_conv_snd`. -/
theorem s17convR_compose {tbl : List CRule}
    {σI : Level → Level} {ρI : List Disp}
    {σH : Level → Level} {ρH : List Disp}
    {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {eI TI e A B : Expr Nat} {u : Level}
    {I : TyP EI nI ΓI eI TI} {d : TyP EH nH ΓH e A} {c : CvP EH nH ΓH A B (.sort u)}
    (hMEUT : ConvMod (EStep tbl) LvlEq ((I.reg.2).eps σI ρI) ((d.reg.2).eps σH ρH))
    (hES : ES tbl σH ρH c)
    (hCL : CL tbl σH ρH d.reg.2 c.dl) :
    ConvMod (EStep tbl) LvlEq ((I.reg.2).eps σI ρI)
      (((TyP.conv EH nH ΓH e A B u d c).reg.2).eps σH ρH) :=
  hMEUT.trans (hCL.trans hES)

/-! ## §2 left row `I = conv d c` — the three request edges -/

/-- §4 left q₁ — `MixedEUT [d, H]`: the child live table
    `K ++ at(d) ++ at(H) ++ Z` is strictly below the caller's
    `K ++ [1 + d.wt + c.wt] ++ at(H) ++ Z`. The original `I` rule atom is
    deleted; `H` is kept once on the original suffix route. -/
theorem s17convL_q1_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {e A B eH TH : Expr Nat} {u : Level}
    (d : TyP EI nI ΓI e A) (c : CvP EI nI ΓI A B (.sort u))
    (H : TyP EH nH ΓH eH TH) (K Z : List Nat) :
    DMStep (K ++ d.atoms Aw ++ H.atoms Aw ++ Z)
      (K ++ [1 + d.wt Aw + c.wt Aw] ++ H.atoms Aw ++ Z) := by
  have inner : DMStep (d.atoms Aw ++ (H.atoms Aw ++ Z))
      ([1 + d.wt Aw + c.wt Aw] ++ (H.atoms Aw ++ Z)) :=
    ⟨[1 + d.wt Aw + c.wt Aw], d.atoms Aw, H.atoms Aw ++ Z,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, fun y hy =>
        ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, by
          have := TyP.atoms_le Aw d y hy; omega⟩⟩
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_ (dmStep_append_left inner K))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 left q₂ — `ES [c]` on the original suffix route:
    `K ++ at(c) ++ at(H) ++ Z` is strictly below the caller's row; `H` kept
    once. -/
theorem s17convL_q2_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {e A B eH TH : Expr Nat} {u : Level}
    (d : TyP EI nI ΓI e A) (c : CvP EI nI ΓI A B (.sort u))
    (H : TyP EH nH ΓH eH TH) (K Z : List Nat) :
    DMStep (K ++ c.atoms Aw ++ H.atoms Aw ++ Z)
      (K ++ [1 + d.wt Aw + c.wt Aw] ++ H.atoms Aw ++ Z) := by
  have inner : DMStep (c.atoms Aw ++ (H.atoms Aw ++ Z))
      ([1 + d.wt Aw + c.wt Aw] ++ (H.atoms Aw ++ Z)) := by
    refine ⟨[1 + d.wt Aw + c.wt Aw], c.atoms Aw, H.atoms Aw ++ Z,
      List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _, ?_⟩
    intro y hy
    exact ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, by
      have := CvP.atoms_le Aw c y hy; omega⟩
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_ (dmStep_append_left inner K))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 left q₃ — the left side's real reg/endpoint `CL [d.reg.2, c.dl]`:
    `K ++ at(d.reg.2) ++ at(c.dl) ++ at(H) ++ Z` is strictly below the
    caller's row; `H` kept once on the original suffix route. -/
theorem s17convL_q3_dm (Aw : Nat → Nat) {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {e A B eH TH : Expr Nat} {u : Level}
    (d : TyP EI nI ΓI e A) (c : CvP EI nI ΓI A B (.sort u))
    (H : TyP EH nH ΓH eH TH) (K Z : List Nat) :
    DMStep (K ++ d.reg.2.atoms Aw ++ c.dl.atoms Aw ++ H.atoms Aw ++ Z)
      (K ++ [1 + d.wt Aw + c.wt Aw] ++ H.atoms Aw ++ Z) := by
  have inner : DMStep ((d.reg.2.atoms Aw ++ c.dl.atoms Aw) ++ (H.atoms Aw ++ Z))
      ([1 + d.wt Aw + c.wt Aw] ++ (H.atoms Aw ++ Z)) := by
    refine ⟨[1 + d.wt Aw + c.wt Aw], d.reg.2.atoms Aw ++ c.dl.atoms Aw,
      H.atoms Aw ++ Z, List.cons_ne_nil _ _, List.Perm.refl _,
      List.Perm.refl _, ?_⟩
    intro y hy
    refine ⟨1 + d.wt Aw + c.wt Aw, List.mem_cons_self _ _, ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · have h1 := TyP.atoms_le Aw d.reg.2 y hy
      have h2 := TyP.wt_reg_le Aw d
      omega
    · have h1 := TyP.atoms_le Aw c.dl y hy
      have h2 := CvP.wt_dl_lt Aw c
      omega
  refine dmStep_perm_right ?_ (dmStep_perm_left ?_ (dmStep_append_left inner K))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.refl _

/-- §4 left composition — `(conv d c).reg = c.dr ↔ c.dl ↔ d.reg ↔ H.reg`: the
    three answers `hMEUT`/`hES`/`hCL` compose, with `ES`/`CL` walked backwards,
    into the `EUT [conv d c, H]` conclusion. Hypotheses only; the current `HE`
    is never an input. -/
theorem s17convL_compose {tbl : List CRule}
    {σI : Level → Level} {ρI : List Disp}
    {σH : Level → Level} {ρH : List Disp}
    {EI : ResolvedEnv} {nI : Nat} {ΓI : LCtx}
    {EH : ResolvedEnv} {nH : Nat} {ΓH : LCtx}
    {e A B eH TH : Expr Nat} {u : Level}
    {d : TyP EI nI ΓI e A} {c : CvP EI nI ΓI A B (.sort u)}
    {H : TyP EH nH ΓH eH TH}
    (hMEUT : ConvMod (EStep tbl) LvlEq ((d.reg.2).eps σI ρI) ((H.reg.2).eps σH ρH))
    (hES : ES tbl σI ρI c)
    (hCL : CL tbl σI ρI d.reg.2 c.dl) :
    ConvMod (EStep tbl) LvlEq
      (((TyP.conv EI nI ΓI e A B u d c).reg.2).eps σI ρI) ((H.reg.2).eps σH ρH) :=
  (ConvMod.symm' LvlEq.symm' hES).trans
    ((ConvMod.symm' LvlEq.symm' hCL).trans hMEUT)

end Rcic.Syn

#print axioms Rcic.Syn.s17convR_q1_dm
#print axioms Rcic.Syn.s17convR_q2_dm
#print axioms Rcic.Syn.s17convR_q3_dm
#print axioms Rcic.Syn.s17convR_compose
#print axioms Rcic.Syn.s17convL_q1_dm
#print axioms Rcic.Syn.s17convL_q2_dm
#print axioms Rcic.Syn.s17convL_q3_dm
#print axioms Rcic.Syn.s17convL_compose
