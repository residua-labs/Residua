import rcic.RcicSynErase
import rcic.RcicSynRegStep

/-!
# Syntactic sortRow, S20 §6 — the two-level legal AP numeric control

`research/rcic/sortrow/S20_NESTED_EXPOSURE_HE.md` §6 (ChatGPT, #7415).

The fixture: `S₀ = sort 0`, `S₁ = sort 1`, `Γ₂ = []`, `Γ₁ = [y : S₁]`,
`Γ₀ = [x : S₁, y : S₁]`. `τ₁` is the `esub` removing `x` (index `0` of `Γ₀`)
replaced by `y`; `τ₂` the `esub` removing `y` (index `0` of `Γ₁`) replaced by
`S₀`. `W₂ : [] ⊢ S₁ : sort 2` is the six-node `.conv`/`.refl` sort typing —
the same shape as `pbitWallHeavySort`, one level up.

Measured on this fixture, S20 §6's claims hold exactly:

* the original atom table is `[1,2,2,1,1,6]` —
  `at(L) ++ [D₀.wt] ++ at(V₁) ++ at(W₁) ++ at(V₂) ++ at(W₂)`;
* `Qvalue = [1,2,1,6]`, `Qtype = [1,2,1,1,6]`, `Qreg = [1,1,1,6]` are each a
  strict `DMStep` below it (`D₀` and the unread `W₁` drop for Qvalue; `D₀`'s
  atom pays `G₀`'s real smaller atoms for Qtype; `V₁.reg.2` replaces `V₁`'s
  atom for Qreg);
* the materialized pair `[1,2,1,1,6,1,1,6]` — `Qtype` with both sides
  materialized — is NOT below: the second `6` can never be justified
  (`s20_qtype_materialized_not_dm`);
* the second hit's three requests `[1,1]` / `[1,1,6]` / `[1,6]` are all
  payable under `Qvalue`'s budget `[1,2,1,6]`;
* the two original transport weights are `6` (τ₁D₀) and `14` (τ₂τ₁D₀);
* the expected erasures compute: term erasure `.sort 0`, regularity erasure
  `.sort 1` (`s20_erasures`, definitional).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the contexts and original derivations -/

/-- `Γ₀ = [x : S₁, y : S₁]` — both entries `sort 1`; `x` at index `0`. -/
def s20Γ₀ : LCtx := [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]

/-- `Γ₁ = [y : S₁]` — what `substRemove v 0 Γ₀` leaves. -/
def s20Γ₁ : LCtx := [.assumption (.sort (.succ .zero))]

/-- `G₀ : Γ₀ ⊢ S₁ : sort 2`, weight `1`. -/
def s20G0 (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₀ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20Γ₀ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `D₀ : Γ₀ ⊢ x : S₁`, weight `2`. -/
def s20D0 (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₀ (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20Γ₀ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (s20G0 E n)

/-- `W₁ : Γ₁ ⊢ S₁ : sort 2`, weight `1` — τ₁'s replacement-type field `hvT`. -/
def s20W1 (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₁ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20Γ₁ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `V₁ : Γ₁ ⊢ y : S₁` (`y` is index `0` of `Γ₁`), weight `2` — τ₁'s `hv`. -/
def s20V1 (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20Γ₁ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (s20W1 E n)

/-- `V₂ : [] ⊢ S₀ : S₁`, weight `1` — τ₂'s `hv`. -/
def s20V2 (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)

/-- `W₂ : [] ⊢ S₁ : sort 2`, weight `6` — the six-node `.conv`/`.refl` sort
    typing, τ₂'s `hvT`. -/
def s20W2 (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  let s12 : TyP E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    TyP.sort E n [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)
  let s23 : TyP E n [] (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ (.succ .zero)))) :=
    TyP.sort E n [] (.succ (.succ .zero)) (.succ (.succ (.succ .zero))) (eqN_refl _)
  TyP.conv E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero))) s12
    (CvP.refl E n [] (.sort (.succ (.succ .zero))) (.sort (.succ (.succ (.succ .zero))))
      s23 s23 s23)

/-- `L : [] ⊢ S₀ : S₁`, weight `1` — the other side, displaying the same
    subject as `τ₂(τ₁ D₀)`. -/
def s20L (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)

/-- `τ₁(D₀)` — the `esub` at index `0` of `Γ₀`, `x` replaced by `y`
    (`v₁ = bvar 0`). Result: `Γ₁ ⊢ y : S₁`, weight `6`. -/
def s20t1D0 (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) :=
  TyP.esub E n s20Γ₀ (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.bvar 0) 0 (.succ (.succ .zero)) (s20D0 E n) rfl (s20V1 E n) (s20W1 E n)

/-- `H = τ₂(τ₁ D₀)` — the `esub` at index `0` of `Γ₁`, `y` replaced by `S₀`
    (`v₂ = sort 0`). Result: `[] ⊢ S₀ : S₁`, weight `14`. -/
def s20H (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.esub E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s20t1D0 E n) rfl (s20V2 E n) (s20W2 E n)

/-! ## §2 the measured atom table and transport weights -/

/-- §6's original atom table `[1,2,2,1,1,6]` —
    `at(L) ++ [D₀.wt] ++ at(V₁) ++ at(W₁) ++ at(V₂) ++ at(W₂)`, computed.
    `D₀`'s atom is its weight `2` (the bvar rule node). -/
theorem s20_input_atoms (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s20L E n).atoms Aw ++ [(s20D0 E n).wt Aw] ++ (s20V1 E n).atoms Aw ++
      (s20W1 E n).atoms Aw ++ (s20V2 E n).atoms Aw ++ (s20W2 E n).atoms Aw =
        [1, 2, 2, 1, 1, 6] := rfl

/-- The two original transport weights are `6` and `14`; `TyP.wt` itself is
    unchanged. -/
theorem s20_transport_weights (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s20t1D0 E n).wt Aw = 6 ∧ (s20H E n).wt Aw = 14 := ⟨rfl, rfl⟩

/-! ## §3 the three requests' strict DM edges -/

/-- `Qvalue = [1,2,1,6] < [1,2,2,1,1,6]` — `D₀`'s atom `2` and the unread
    `W₁`'s `1` are deleted (`X = [1,2]`, the removed block); `L`, `V₁`, `V₂`,
    `W₂` kept. -/
theorem s20_qvalue_dm : DMStep [1, 2, 1, 6] [1, 2, 2, 1, 1, 6] :=
  ⟨[1, 2], [], [2, 1, 1, 6], List.cons_ne_nil _ _, List.Perm.refl _,
    List.Perm.swap _ _ _,
    fun y hy => absurd hy (List.not_mem_nil y)⟩

/-- `Qtype = [1,2,1,1,6] < [1,2,2,1,1,6]` — `D₀`'s atom `2` pays `G₀`'s real
    atom `1` (`D₀.wt = 1 + G₀.wt`); `L`'s atom is dropped inside the removed
    block `X = [1,2]`. -/
theorem s20_qtype_dm : DMStep [1, 2, 1, 1, 6] [1, 2, 2, 1, 1, 6] :=
  ⟨[1, 2], [1], [2, 1, 1, 6], List.cons_ne_nil _ _, List.Perm.refl _,
    List.Perm.refl _,
    fun y hy => ⟨2, List.mem_cons.mpr (Or.inr (List.mem_cons_self 2 [])), by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      omega⟩⟩

/-- `Qreg = [1,1,1,6] < [1,2,2,1,1,6]` — the `V₁.reg.2` field's atom `1`
    replaces the removed block's head; `D₀` and `V₁`'s atoms drop; `W₁`,
    `V₂`, `W₂` are kept. -/
theorem s20_qreg_dm : DMStep [1, 1, 1, 6] [1, 2, 2, 1, 1, 6] :=
  ⟨[1, 2, 2], [1], [1, 1, 6], List.cons_ne_nil _ _, List.Perm.refl _,
    List.Perm.refl _,
    fun y hy => ⟨2, List.mem_cons.mpr (Or.inr (List.mem_cons_self 2 [2])), by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      omega⟩⟩

/-! ## §4 the rejected materialized pair -/

/-- `Qtype` with both sides materialized `[1,2,1,1,6,1,1,6]` is NOT below
    `[1,2,2,1,1,6]`: the callee multiset carries two `6`s while the caller
    has one — a `6` in `Y` could only be paid by a strictly larger caller
    atom, and none exists. No `W₂`-copy is ever legal. -/
theorem s20_qtype_materialized_not_dm :
    ¬ DMStep [1, 2, 1, 1, 6, 1, 1, 6] [1, 2, 2, 1, 1, 6] := by
  rintro ⟨X, Y, Z, _hX, hM, hM', hlt⟩
  have hxM : ∀ x ∈ X, x ≤ 6 := by
    intro x hx
    have hmem := hM.symm.subset (List.mem_append_left Z hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega
  have hY6 : 6 ∉ Y := by
    intro h6
    obtain ⟨x, hxX, hlt6⟩ := hlt 6 h6
    have := hxM x hxX
    omega
  have hc6 : List.count 6 (Y ++ Z) = 2 := by
    have h := hM'.count_eq 6
    have hc : List.count 6 [1, 2, 1, 1, 6, 1, 1, 6] = 2 := rfl
    omega
  rw [List.count_append] at hc6
  have hY0 : List.count 6 Y = 0 := List.count_eq_zero.mpr hY6
  have hM6 : List.count 6 [1, 2, 2, 1, 1, 6] = 1 := rfl
  have hcall := hM.count_eq 6
  rw [List.count_append] at hcall
  omega

/-! ## §5 the second hit's three requests, under `Qvalue`'s budget -/

/-- second hit, value request `MixedEUT[L, V₂]`: `[1,1] < [1,2,1,6]` — the
    `V₁` atom and the unread `W₂` drop. -/
theorem s20_hit2_value_dm : DMStep [1, 1] [1, 2, 1, 6] :=
  ⟨[2, 6], [], [1, 1], List.cons_ne_nil _ _,
    (List.Perm.swap 2 1 [1, 6]).trans (List.Perm.cons 2
      ((List.Perm.cons 1 (List.Perm.swap 6 1 [])).trans (List.Perm.swap 6 1 [1]))),
    List.Perm.refl _,
    fun y hy => absurd hy (List.not_mem_nil y)⟩

/-- second hit, type request `MixedCL[V₂.reg.2, W₂]`: `[1,1,6] < [1,2,1,6]` —
    the removed block `X = [1,2]` (the `V₁` atom and `V₂`'s own rule-node atom)
    pays `V₂.reg.2`'s `1`. -/
theorem s20_hit2_type_dm : DMStep [1, 1, 6] [1, 2, 1, 6] :=
  ⟨[1, 2], [1], [1, 6], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨2, List.mem_cons.mpr (Or.inr (List.mem_cons_self 2 [])), by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      omega⟩⟩

/-- second hit, reg request `MixedCL[τ₂-view(V₁.hType), W₂]`:
    `[1,6] < [1,2,1,6]` — `V₁`'s atom and `V₂`'s rule-node atom drop, `L`'s
    `1` and `W₂` kept. -/
theorem s20_hit2_reg_dm : DMStep [1, 6] [1, 2, 1, 6] :=
  ⟨[1, 2], [], [1, 6], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => absurd hy (List.not_mem_nil y)⟩

/-! ## §6 the expected erasures -/

/-- `τ₂(τ₁ D₀)` erases to the real term `sort 0` — the esub clauses substitute
    `V₂.eps = .sort 0` for the kept bvar, twice. Definitional. -/
theorem s20_erasure_term (E : ResolvedEnv) (n : Nat) :
    (s20H E n).eps id [] = .sort .zero := rfl

/-- The regularity erasure is the real `sort 1` — `reg`'s esub clause keeps the
    same transport and real fields, so `H.reg.2` is `τ₂(τ₁ G₀)` and erases to
    `.sort 1`. Definitional. -/
theorem s20_erasure_reg (E : ResolvedEnv) (n : Nat) :
    ((s20H E n).reg.2).eps id [] = .sort (.succ .zero) := rfl

/-- The display partner `L` erases to the same term `sort 0`. -/
theorem s20_erasure_L (E : ResolvedEnv) (n : Nat) :
    (s20L E n).eps id [] = .sort .zero := rfl

end Rcic.Syn

#print axioms Rcic.Syn.s20G0
#print axioms Rcic.Syn.s20D0
#print axioms Rcic.Syn.s20W1
#print axioms Rcic.Syn.s20V1
#print axioms Rcic.Syn.s20V2
#print axioms Rcic.Syn.s20W2
#print axioms Rcic.Syn.s20L
#print axioms Rcic.Syn.s20t1D0
#print axioms Rcic.Syn.s20H
#print axioms Rcic.Syn.s20_input_atoms
#print axioms Rcic.Syn.s20_transport_weights
#print axioms Rcic.Syn.s20_qvalue_dm
#print axioms Rcic.Syn.s20_qtype_dm
#print axioms Rcic.Syn.s20_qreg_dm
#print axioms Rcic.Syn.s20_qtype_materialized_not_dm
#print axioms Rcic.Syn.s20_hit2_value_dm
#print axioms Rcic.Syn.s20_hit2_type_dm
#print axioms Rcic.Syn.s20_hit2_reg_dm
#print axioms Rcic.Syn.s20_erasure_term
#print axioms Rcic.Syn.s20_erasure_reg
#print axioms Rcic.Syn.s20_erasure_L
