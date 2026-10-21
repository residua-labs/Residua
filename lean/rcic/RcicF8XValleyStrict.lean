import rcic.RcicF8XTile
import rcic.RcicF8XEdgeLex

/-!
# `RcicF8XValleyStrict` — the valley route with a strict call census (S3e; cc's ruling on E-X-MULT)

`S3E_STRICT_VALLEYS_DESIGN.md` (#7026) and cc's 2026-10-14 ruling on #7070: E-X-MULT (a D call
after U-alignment carrying a kept input atom twice) is not a measure change; restructure so that a
kept atom never enters a U/D/S call. Two local changes to S3b's valley route, no contract touched:

* **(R1)** index conversions are retained as a pending chain, outside the strict core. U aligns
  actual core indices; the readers consume only that core. `SRes.toValley` applies the entire
  chain once before exposing a valley at the caller's requested index (Devin desktop, #7115);
* **(R2)** a `refl D` node yields the TRIVIAL result (nothing to join): joining with it is the other
  side, with no U and no D call; `D.leaves` never meet a call.

So every leaf of every U/D/S argument is STRICT (`SubOf` an input atom): J's legs and endpoint
typings (`JContractWfP`), U's answers (`SubEq` strict typings), D's legs (`SubEq` strict legs), and
the steps S reads (legs' steps). Suppliers are partial (S3b): the route answers or refuses. The
worker `xValleyS?` returns, besides `XProcWf`'s components, the **census**: every U/D/S callee
bundle (strict) and every J literal (`SubEq` an input leaf), and `xValleyS_edges` proves
`EdgeContractLex` for every census from the caller `(c.leaves ++ Z, c.size)`: U/D/S by
`om3_edge_of_strictLeaves`, a J literal strictly below an input leaf likewise (E1), a J literal
equal to an input leaf by a drop when another atom exists (E2, `om3_edge_drop_to`) and by the lex
size step when it is the only atom (E-X-LONE, `om3_edgeLex_lone`, `EvTc.size_ge_two_of_cv_mem`).
K is a construction, not a call. Stratum A answers for every supplier bundle
(`xValleyS?_isSome_of_piSpined`), so nothing here is vacuous. S3b's `xValley?` stays as sealed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}

/-! ### kit: strict bounds -/

/-- `ℓ` is strictly below some element of `L`. -/
abbrev Strict (ℓ : Jd E n) (L : List (Jd E n)) : Prop := ∃ x ∈ L, SubOf ℓ x

theorem strict_left {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Strict ℓ L) : Strict ℓ (L ++ L') := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, List.mem_append.mpr (.inl hx), hs⟩

theorem strict_right {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Strict ℓ L') : Strict ℓ (L ++ L') := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, List.mem_append.mpr (.inr hx), hs⟩

theorem below_of_strict {ℓ : Jd E n} {L : List (Jd E n)} (h : Strict ℓ L) : Below ℓ L := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, hx, .inr hs⟩

theorem strict_of_below {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Below ℓ L)
    (hL : ∀ x ∈ L, Strict x L') : Strict ℓ L' := by
  obtain ⟨x, hx, hs⟩ := h
  obtain ⟨y, hy, hs'⟩ := hL x hx
  exact ⟨y, hy, subEq_trans_subOf hs hs'⟩

theorem strict_of_strict_below {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Strict ℓ L)
    (hL : ∀ x ∈ L, Below x L') : Strict ℓ L' := by
  obtain ⟨x, hx, hs⟩ := h
  obtain ⟨y, hy, hs'⟩ := hL x hx
  exact ⟨y, hy, subOf_trans_subEq hs hs'⟩

theorem ne_nil_append_left {α : Type} {a b : List α} (h : a ≠ []) : a ++ b ≠ [] :=
  fun e => h (List.append_eq_nil.mp e).1

theorem ne_nil_append_right {α : Type} {a b : List α} (h : b ≠ []) : a ++ b ≠ [] :=
  fun e => h (List.append_eq_nil.mp e).2

theorem below_ne_nil {ℓ : Jd E n} {L : List (Jd E n)} (h : Below ℓ L) : L ≠ [] := by
  obtain ⟨x, hx, _⟩ := h
  intro hL
  subst hL
  exact absurd hx (List.not_mem_nil _)

/-- the shape of a J literal's atom. -/
def JAtom (j : Jd E n) : Prop :=
  ∃ (Γ' : LCtx) (a b T : Expr Nat) (h : ConvT E n Γ' a b T), j = Jd.cv h

/-! ### the route's intermediate: trivial, or a strict valley at some index -/

/-- A strict core with its entire pending conversion to the requested index.
The pending chain is retained for final exposure and never enters a U/D/S call.
This follows Devin desktop's `SRes.toValley` design from #7115. -/
inductive SRes (R : List (Jd E n)) (Γ : LCtx) : Expr Nat → Expr Nat → Expr Nat → Type where
  | triv {a T₀ T : Expr Nat} (D : EvTy R Γ a T₀) (pending : EvTc R Γ T₀ T) : SRes R Γ a a T
  | val {a b T₀ T : Expr Nat} (V : Valley R Γ a b T₀) (pending : EvTc R Γ T₀ T) : SRes R Γ a b T

/-- Only the core enters the strict call bound. -/
def SRes.leaves : {a b T : Expr Nat} → SRes R Γ a b T → List (Jd E n)
  | _, _, _, .triv _ _ => []
  | _, _, _, .val V _ => V.leaves

/-- Kept input support used only for requested-index exposure. -/
def SRes.pendingLeaves : {a b T : Expr Nat} → SRes R Γ a b T → List (Jd E n)
  | _, _, _, .triv D pending => D.leaves ++ pending.leaves
  | _, _, _, .val _ pending => pending.leaves

/-- Restore the complete chain exactly once, at the requested index. -/
def SRes.toValley : {a b T : Expr Nat} → SRes R Γ a b T → Valley R Γ a b T
  | _, _, _, .triv D pending => (⟨_, .refl D, .refl D, D, D⟩ : Valley R Γ _ _ _).conv pending
  | _, _, _, .val V pending => V.conv pending

def SRes.isVal : {a b T : Expr Nat} → SRes R Γ a b T → Bool
  | _, _, _, .triv _ _ => false
  | _, _, _, .val _ _ => true

def SRes.symm : {a b T : Expr Nat} → SRes R Γ a b T → SRes R Γ b a T
  | _, _, _, .triv D pending => .triv D pending
  | _, _, _, .val V pending => .val V.symm pending

theorem SRes.symm_leaves_mem : {a b T : Expr Nat} → (r : SRes R Γ a b T) →
    ∀ ℓ ∈ r.symm.leaves, ℓ ∈ r.leaves
  | _, _, _, .triv _ _ => fun _ h => h
  | _, _, _, .val V _ => fun ℓ h => V.symm_leaves ℓ h

theorem SRes.symm_pendingLeaves : {a b T : Expr Nat} → (r : SRes R Γ a b T) →
    r.symm.pendingLeaves = r.pendingLeaves
  | _, _, _, .triv _ _ => rfl
  | _, _, _, .val _ _ => rfl

theorem SRes.isVal_symm : {a b T : Expr Nat} → (r : SRes R Γ a b T) → r.symm.isVal = r.isVal
  | _, _, _, .triv _ _ => rfl
  | _, _, _, .val _ _ => rfl

def SRes.wk (d : LocalDecl) (k : Nat) : {a b T : Expr Nat} → SRes R Γ a b T →
    SRes R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T)
  | _, _, _, .triv D pending => .triv (.wk d k D) (.wk d k pending)
  | _, _, _, .val V pending => .val (V.wk d k) (.wk d k pending)

theorem SRes.wk_leaves (d : LocalDecl) (k : Nat) : {a b T : Expr Nat} → (r : SRes R Γ a b T) →
    (r.wk d k).leaves = r.leaves
  | _, _, _, .triv _ _ => rfl
  | _, _, _, .val V _ => Valley.wk_leaves d k V

theorem SRes.wk_pendingLeaves (d : LocalDecl) (k : Nat) : {a b T : Expr Nat} →
    (r : SRes R Γ a b T) → (r.wk d k).pendingLeaves = r.pendingLeaves
  | _, _, _, .triv _ _ => rfl
  | _, _, _, .val _ _ => rfl

theorem SRes.isVal_wk (d : LocalDecl) (k : Nat) : {a b T : Expr Nat} → (r : SRes R Γ a b T) →
    (r.wk d k).isVal = r.isVal
  | _, _, _, .triv _ _ => rfl
  | _, _, _, .val _ _ => rfl

/-- Accumulate an index conversion without applying it to the strict core. -/
def SRes.rety {a b T T' : Expr Nat} (r : SRes R Γ a b T) (c : EvTc R Γ T T') : SRes R Γ a b T' :=
  match r with
  | .triv D pending => .triv D (.trans pending c)
  | .val V pending => .val V (.trans pending c)

theorem SRes.rety_leaves {a b T T' : Expr Nat} (r : SRes R Γ a b T) (c : EvTc R Γ T T') :
    (r.rety c).leaves = r.leaves := by cases r <;> rfl

theorem SRes.rety_pendingLeaves {a b T T' : Expr Nat} (r : SRes R Γ a b T) (c : EvTc R Γ T T') :
    (r.rety c).pendingLeaves = r.pendingLeaves ++ c.leaves := by
  cases r <;> simp only [SRes.rety, SRes.pendingLeaves, EvTc.leaves, List.append_assoc]

theorem SRes.isVal_rety {a b T T' : Expr Nat} (r : SRes R Γ a b T) (c : EvTc R Γ T T') :
    (r.rety c).isVal = r.isVal := by cases r <;> rfl

/-- Every exposed leaf is from the core or the separately retained support. -/
theorem SRes.toValley_leaves : {a b T : Expr Nat} → (r : SRes R Γ a b T) →
    ∀ ℓ ∈ r.toValley.leaves, ℓ ∈ r.leaves ++ r.pendingLeaves
  | _, _, _, .triv D pending => fun ℓ hℓ => by
      rcases List.mem_append.mp ((⟨_, .refl D, .refl D, D, D⟩ : Valley R Γ _ _ _).conv_leaves pending ℓ hℓ) with hd | hp
      · simp only [Valley.leaves, EvParStar.leaves, List.mem_append] at hd
        simp only [SRes.leaves, SRes.pendingLeaves, List.nil_append, List.mem_append]
        rcases hd with ((hd | hd) | hd) | hd <;> exact .inl hd
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr hp)))
  | _, _, _, .val V pending => fun ℓ hℓ => V.conv_leaves pending ℓ hℓ

/-- the route's output: the result, the U/D callee bundles, the J literals called. -/
structure SOut (R : List (Jd E n)) (Γ : LCtx) (a b T : Expr Nat) where
  res : SRes R Γ a b T
  calls : List (List (Jd E n))
  jcalls : List (Jd E n)

/-- Expose a valley at the caller's requested index. -/
def SOut.toValley {a b T : Expr Nat} (o : SOut R Γ a b T) : Valley R Γ a b T := o.res.toValley

/-- The original strict core/call/J bounds, plus the separately retained input support.
Pending support is only `Below`; it is never admitted into a strict U/D/S bundle. -/
def SOut.Bound {a b T : Expr Nat} (o : SOut R Γ a b T) (L : List (Jd E n)) : Prop :=
  (∀ ℓ ∈ o.res.leaves, Strict ℓ L) ∧ (∀ C ∈ o.calls, ∀ ℓ ∈ C, Strict ℓ L) ∧
  (∀ j ∈ o.jcalls, Below j L) ∧ (∀ j ∈ o.jcalls, JAtom j) ∧
  (o.res.isVal = true → o.jcalls ≠ []) ∧ (o.calls ≠ [] → o.jcalls ≠ []) ∧
  (∀ ℓ ∈ o.res.pendingLeaves, Below ℓ L)

theorem SOut.toValley_below {a b T : Expr Nat} {o : SOut R Γ a b T} {L : List (Jd E n)}
    (h : o.Bound L) : ∀ ℓ ∈ o.toValley.leaves, Below ℓ L := by
  intro ℓ hℓ
  rcases List.mem_append.mp (o.res.toValley_leaves ℓ hℓ) with hc | hp
  · exact below_of_strict (h.1 ℓ hc)
  · exact h.2.2.2.2.2.2 ℓ hp

theorem SOut.bound_left {a b T : Expr Nat} {o : SOut R Γ a b T} {L L' : List (Jd E n)}
    (h : o.Bound L) : o.Bound (L ++ L') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨fun ℓ hℓ => strict_left (h1 ℓ hℓ), fun C hC ℓ hℓ => strict_left (h2 C hC ℓ hℓ),
    fun j hj => below_left (h3 j hj), h4, h5, h6, fun ℓ hℓ => below_left (h7 ℓ hℓ)⟩

theorem SOut.bound_right {a b T : Expr Nat} {o : SOut R Γ a b T} {L L' : List (Jd E n)}
    (h : o.Bound L') : o.Bound (L ++ L') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨fun ℓ hℓ => strict_right (h1 ℓ hℓ), fun C hC ℓ hℓ => strict_right (h2 C hC ℓ hℓ),
    fun j hj => below_right (h3 j hj), h4, h5, h6, fun ℓ hℓ => below_right (h7 ℓ hℓ)⟩

theorem SOut.bound_of_eq {a b T : Expr Nat} {o : SOut R Γ a b T} {L L' : List (Jd E n)}
    (h : o.Bound L) (e : L = L') : o.Bound L' := e ▸ h

/-- A reflexive input retains its typing for eventual requested-index exposure. -/
theorem SOut.bound_triv {a T : Expr Nat} (D : EvTy R Γ a T) (L : List (Jd E n))
    (hD : ∀ ℓ ∈ D.leaves, Below ℓ L) :
    (⟨.triv D (.refl Γ T), [], []⟩ : SOut R Γ a a T).Bound L := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact absurd h (List.not_mem_nil _)
  · intro C hC; exact absurd hC (List.not_mem_nil _)
  · intro _ hj; exact absurd hj (List.not_mem_nil _)
  · intro _ hj; exact absurd hj (List.not_mem_nil _)
  · intro hv; simp [SRes.isVal] at hv
  · intro hne; exact absurd rfl hne
  · simpa only [SRes.pendingLeaves, EvTc.leaves, List.append_nil] using hD

/-- Same calls and pending chain, with the core turned around. -/
def SOut.symm {a b T : Expr Nat} (o : SOut R Γ a b T) : SOut R Γ b a T :=
  ⟨o.res.symm, o.calls, o.jcalls⟩

theorem SOut.bound_symm {a b T : Expr Nat} {o : SOut R Γ a b T} {L : List (Jd E n)}
    (h : o.Bound L) : o.symm.Bound L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun ℓ hℓ => h1 ℓ (o.res.symm_leaves_mem ℓ hℓ), h2, h3, h4, ?_, h6, ?_⟩
  · intro hv
    exact h5 (by simpa only [SOut.symm, SRes.isVal_symm] using hv)
  · simpa only [SOut.symm, SRes.symm_pendingLeaves] using h7

/-- Same calls, with both core and pending chain weakened. -/
def SOut.wk (d : LocalDecl) (k : Nat) {a b T : Expr Nat} (o : SOut R Γ a b T) :
    SOut R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T) := ⟨o.res.wk d k, o.calls, o.jcalls⟩

theorem SOut.bound_wk (d : LocalDecl) (k : Nat) {a b T : Expr Nat} {o : SOut R Γ a b T}
    {L : List (Jd E n)} (h : o.Bound L) : (o.wk d k).Bound L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun ℓ hℓ => h1 ℓ (by simpa only [SOut.wk, SRes.wk_leaves] using hℓ), h2, h3, h4, ?_, h6, ?_⟩
  · intro hv
    exact h5 (by simpa only [SOut.wk, SRes.isVal_wk] using hv)
  · simpa only [SOut.wk, SRes.wk_pendingLeaves] using h7

/-- Defer an index chain; call records and strict core are unchanged. -/
def SOut.rety {a b T T' : Expr Nat} (o : SOut R Γ a b T) (c : EvTc R Γ T T') : SOut R Γ a b T' :=
  ⟨o.res.rety c, o.calls, o.jcalls⟩

theorem SOut.bound_rety {a b T T' : Expr Nat} {o : SOut R Γ a b T} {L : List (Jd E n)}
    (h : o.Bound L) (c : EvTc R Γ T T') : (o.rety c).Bound (L ++ c.leaves) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, fun C hC ℓ hℓ => strict_left (h2 C hC ℓ hℓ),
    fun j hj => below_left (h3 j hj), h4, ?_, h6, ?_⟩
  · intro ℓ hℓ
    exact strict_left (h1 ℓ (by simpa only [SOut.rety, SRes.rety_leaves] using hℓ))
  · intro hv
    exact h5 (by simpa only [SOut.rety, SRes.isVal_rety] using hv)
  · intro ℓ hℓ
    rw [SOut.rety, SRes.rety_pendingLeaves] at hℓ
    rcases List.mem_append.mp hℓ with hl | hc
    · exact below_left (h7 ℓ hl)
    · exact below_right (below_of_mem hc)

/-- A bounded result at its demanded index, or a refusal. -/
abbrev SOutB (R : List (Jd E n)) (Γ : LCtx) (a b T : Expr Nat) (L : List (Jd E n)) : Type :=
  Σ' o : SOut R Γ a b T, o.Bound L

/-! ### the join: U aligns the actual indices, D closes; both bundles strict; or a refusal -/

/-- U-then-D join of two strict valleys at their own indices, with the two callee bundles and
    their strictness; or a refusal. -/
def ValleyOps.sjoin (X : ValleyOps E n) {a b c T₁ T₂ : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (V₁ : Valley R Γ a b T₁) (h₁ : ∀ ℓ ∈ V₁.leaves, Strict ℓ L₁)
    (V₂ : Valley R Γ b c T₂) (h₂ : ∀ ℓ ∈ V₂.leaves, Strict ℓ L₂) :
    Option (Σ' (W : Valley R Γ a c T₁) (calls : List (List (Jd E n))),
      (∀ ℓ ∈ W.leaves, Strict ℓ (L₁ ++ L₂)) ∧ (∀ C ∈ calls, ∀ ℓ ∈ C, Strict ℓ (L₁ ++ L₂))) :=
  match hu : X.U R V₁.ty₂ V₂.ty₁ with
  | none => none
  | some u =>
      have hu' : ∀ ℓ ∈ u.leaves, Strict ℓ (L₁ ++ L₂) := fun ℓ hℓ =>
        strict_of_below (X.hU R V₁.ty₂ V₂.ty₁ u hu ℓ hℓ) (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact strict_left (h₁ y (V₁.below_ty₂ hy))
          · exact strict_right (h₂ y (V₂.below_ty₁ hy)))
      have h₂' : ∀ ℓ ∈ (V₂.conv (.symm u)).leaves, Strict ℓ (L₁ ++ L₂) := fun ℓ hℓ => by
        rcases List.mem_append.mp (V₂.conv_leaves _ ℓ hℓ) with hℓ | hℓ
        · exact strict_right (h₂ ℓ hℓ)
        · exact hu' ℓ (by simpa only [EvTc.leaves] using hℓ)
      match hd : X.D R V₁.right (V₂.conv (.symm u)).left with
      | none => none
      | some d =>
          have hd' : ∀ ℓ ∈ d.2.1.leaves ++ d.2.2.leaves, Strict ℓ (L₁ ++ L₂) := fun ℓ hℓ =>
            strict_of_below (X.hD R _ _ d hd ℓ hℓ) (fun y hy => by
              rcases List.mem_append.mp hy with hy | hy
              · exact strict_left (h₁ y (V₁.below_right hy))
              · exact h₂' y ((V₂.conv _).below_left hy))
          some ⟨⟨d.1, .trans V₁.left d.2.1, .trans (V₂.conv (.symm u)).right d.2.2, V₁.ty₁,
              (V₂.conv (.symm u)).ty₂⟩,
            [V₁.ty₂.leaves ++ V₂.ty₁.leaves, V₁.right.leaves ++ (V₂.conv (.symm u)).left.leaves],
            fun ℓ hℓ => by
              simp only [Valley.leaves, EvParStar.leaves, List.mem_append] at hℓ
              rcases hℓ with (((hℓ | hℓ) | (hℓ | hℓ)) | hℓ) | hℓ
              · exact strict_left (h₁ ℓ (V₁.below_left hℓ))
              · exact hd' ℓ (List.mem_append.mpr (.inl hℓ))
              · rcases hℓ with hℓ | hℓ
                · exact strict_right (h₂ ℓ (V₂.below_right hℓ))
                · exact hu' ℓ (by simpa only [EvTc.leaves] using hℓ)
              · exact hd' ℓ (List.mem_append.mpr (.inr hℓ))
              · exact strict_left (h₁ ℓ (V₁.below_ty₁ hℓ))
              · exact h₂' ℓ ((V₂.conv _).below_ty₂ hℓ),
            fun C hC ℓ hℓ => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
              rcases hC with rfl | rfl
              · rcases List.mem_append.mp hℓ with hℓ | hℓ
                · exact strict_left (h₁ ℓ (V₁.below_ty₂ hℓ))
                · exact strict_right (h₂ ℓ (V₂.below_ty₁ hℓ))
              · rcases List.mem_append.mp hℓ with hℓ | hℓ
                · exact strict_left (h₁ ℓ (V₁.below_right hℓ))
                · exact h₂' ℓ ((V₂.conv _).below_left hℓ)⟩

/-- Compatibility specialization of the shared operational helper. -/
def sjoin (X : Suppliers E n) {a b c T₁ T₂ : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (V₁ : Valley R Γ a b T₁) (h₁ : ∀ ℓ ∈ V₁.leaves, Strict ℓ L₁)
    (V₂ : Valley R Γ b c T₂) (h₂ : ∀ ℓ ∈ V₂.leaves, Strict ℓ L₂) :
    Option (Σ' (W : Valley R Γ a c T₁) (calls : List (List (Jd E n))),
      (∀ ℓ ∈ W.leaves, Strict ℓ (L₁ ++ L₂)) ∧ (∀ C ∈ calls, ∀ ℓ ∈ C, Strict ℓ (L₁ ++ L₂))) :=
  ValleyOps.sjoin X.toValleyOps V₁ h₁ V₂ h₂

/-- Combine strict cores without restoring either pending chain. A heterogeneous prefix
selects the demanded index of the retained side; equal-index conversion trans collapses the sum. -/
def ValleyOps.scombine (X : ValleyOps E n) {a b c T₁ T₂ : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (o₁ : SOut R Γ a b T₁) (h₁ : o₁.Bound L₁) (o₂ : SOut R Γ b c T₂) (h₂ : o₂.Bound L₂) :
    Option (SOutB R Γ a c T₁ (L₁ ++ L₂) ⊕ SOutB R Γ a c T₂ (L₁ ++ L₂)) := by
  obtain ⟨r₁, c₁, j₁⟩ := o₁
  obtain ⟨r₂, c₂, j₂⟩ := o₂
  obtain ⟨h11, h12, h13, h14, h15, h16, h17⟩ := h₁
  obtain ⟨h21, h22, h23, h24, h25, h26, h27⟩ := h₂
  simp only at h11 h12 h13 h14 h15 h16 h17 h21 h22 h23 h24 h25 h26 h27
  have hc : ∀ C ∈ c₁ ++ c₂, ∀ ℓ ∈ C, Strict ℓ (L₁ ++ L₂) := fun C hC ℓ hℓ => by
    rcases List.mem_append.mp hC with hC | hC
    · exact strict_left (h12 C hC ℓ hℓ)
    · exact strict_right (h22 C hC ℓ hℓ)
  have hj : ∀ j ∈ j₁ ++ j₂, Below j (L₁ ++ L₂) := fun j hj => by
    rcases List.mem_append.mp hj with hj | hj
    · exact below_left (h13 j hj)
    · exact below_right (h23 j hj)
  have hja : ∀ j ∈ j₁ ++ j₂, JAtom j := fun j hj => by
    rcases List.mem_append.mp hj with hj | hj
    · exact h14 j hj
    · exact h24 j hj
  have hcj : c₁ ++ c₂ ≠ [] → j₁ ++ j₂ ≠ [] := fun hne => by
    cases hc1 : c₁ with
    | nil =>
        subst hc1
        exact ne_nil_append_right (h26 (by simpa using hne))
    | cons C cs =>
        exact ne_nil_append_left (h16 (by rw [hc1]; exact List.cons_ne_nil _ _))
  cases r₁ with
  | triv D₁ pending₁ =>
      exact some (.inr ⟨⟨r₂, c₁ ++ c₂, j₁ ++ j₂⟩,
        fun ℓ hℓ => strict_right (h21 ℓ hℓ), hc, hj, hja,
        fun hv => ne_nil_append_right (h25 hv), hcj, fun ℓ hℓ => below_right (h27 ℓ hℓ)⟩)
  | val V₁ pending₁ =>
      cases r₂ with
      | triv D₂ pending₂ =>
          exact some (.inl ⟨⟨.val V₁ pending₁, c₁ ++ c₂, j₁ ++ j₂⟩,
            fun ℓ hℓ => strict_left (h11 ℓ hℓ), hc, hj, hja,
            fun _ => ne_nil_append_left (h15 rfl), hcj, fun ℓ hℓ => below_left (h17 ℓ hℓ)⟩)
      | val V₂ pending₂ =>
          exact (ValleyOps.sjoin X V₁ h11 V₂ h21).map (fun r =>
            .inl ⟨⟨.val r.1 pending₁, c₁ ++ c₂ ++ r.2.1, j₁ ++ j₂⟩, r.2.2.1,
              fun C hC ℓ hℓ => by
                rcases List.mem_append.mp hC with hC | hC
                · exact hc C hC ℓ hℓ
                · exact r.2.2.2 C hC ℓ hℓ,
              hj, hja, fun _ => ne_nil_append_left (h15 rfl),
              fun _ => ne_nil_append_left (h15 rfl), fun ℓ hℓ => below_left (h17 ℓ hℓ)⟩)

/-! ### the route on conversions, links and prefixes -/

/-- Compatibility specialization of the shared operational helper. -/
def scombine (X : Suppliers E n) {a b c T₁ T₂ : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (o₁ : SOut R Γ a b T₁) (h₁ : o₁.Bound L₁) (o₂ : SOut R Γ b c T₂) (h₂ : o₂.Bound L₂) :
    Option (SOutB R Γ a c T₁ (L₁ ++ L₂) ⊕ SOutB R Γ a c T₂ (L₁ ++ L₂)) :=
  ValleyOps.scombine X.toValleyOps o₁ h₁ o₂ h₂

/-- The strict route retains the demanded index. Index conversions accumulate only in the
pending chain; `toValley` restores it once, after all strict calls. A reflexive core makes no call. -/
def svalleyCv (X : Suppliers E n) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    CtxWfT E n Γ → bCv c = true → Option (SOutB R Γ a b T c.leaves)
  | _, _, _, _, .lit h hsub, hΓ, _ =>
      match hJ : X.J R hΓ h hsub with
      | none => none
      | some V => some ⟨⟨.val V (.refl _ _), [], [.cv h]⟩, by
          refine ⟨fun ℓ hℓ => ⟨.cv h, ?_, X.hJ R hΓ h hsub V hJ ℓ hℓ⟩,
            fun C hC => absurd hC (List.not_mem_nil _), fun j hj => ?_, fun j hj => ?_,
            fun _ => List.cons_ne_nil _ _, fun hne => absurd rfl hne,
            fun ℓ hℓ => absurd hℓ (List.not_mem_nil _)⟩
          · simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil, or_false]
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            subst hj
            exact ⟨.cv h, by simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil, or_false], .inl rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            subst hj
            exact ⟨_, _, _, _, h, rfl⟩⟩
  | _, _, _, _, .refl D, _, _ =>
      some ⟨⟨.triv D (.refl _ _), [], []⟩, SOut.bound_triv D _ (fun ℓ hℓ => below_of_mem hℓ)⟩
  | _, _, _, _, .symm c, hΓ, h =>
      (svalleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.symm, SOut.bound_of_eq (SOut.bound_symm r.2) (by simp only [EvCv.leaves])⟩)
  | _, _, _, _, .trans c₁ c₂, hΓ, h =>
      have h' : bCv c₁ = true ∧ bCv c₂ = true := by
        simpa only [bCv, Bool.and_eq_true] using h
      match svalleyCv X c₁ hΓ h'.1, svalleyCv X c₂ hΓ h'.2 with
      | some r₁, some r₂ =>
          (scombine X r₁.1 r₁.2 r₂.1 r₂.2).map (fun r =>
            r.elim (fun r => ⟨r.1, SOut.bound_of_eq r.2 (by simp only [EvCv.leaves])⟩)
              (fun r => ⟨r.1, SOut.bound_of_eq r.2 (by simp only [EvCv.leaves])⟩))
      | _, _ => none
  | _, _, _, _, .tyConv u' c cA, hΓ, h =>
      (svalleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.rety (.ofCv u' cA), SOut.bound_of_eq (SOut.bound_rety r.2 (.ofCv u' cA))
          (by simp only [EvCv.leaves, EvTc.leaves])⟩)
  | _, _, _, _, @EvCv.wk _ _ _ Γ₀ a₀ b₀ T₀ d k c, hΓ, h => by
      cases k with
      | zero =>
          exact (svalleyCv X c (ctxWfT_tail hΓ) (by simpa only [bCv] using h)).map (fun r =>
            ⟨r.1.wk d 0, SOut.bound_of_eq (SOut.bound_wk d 0 r.2) (by simp only [EvCv.leaves])⟩)
      | succ k => exact nomatch h
  | _, _, _, _, .esub .., _, h => nomatch h
  | _, _, _, _, .subst0 .., _, h => nomatch h
  | _, _, _, _, .substLet .., _, h => nomatch h
  -- Native level conversions remain inadmissible. Both index wrappers retain their full
  -- pending chain for one-shot restoration; its leaves enter no strict call.
  | _, _, _, _, .sorts .., _, h => nomatch h
  | _, _, _, _, .consts .., _, h => nomatch h
  | _, _, _, _, .rety c cA, hΓ, h =>
      (svalleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.rety cA, SOut.bound_of_eq (SOut.bound_rety r.2 cA) (by simp only [EvCv.leaves])⟩)

/-- A link's valley retains the requested index selected by that link. -/
def slinkValley (X : Suppliers E n) : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    CtxWfT E n Γ → bLink l = true → Option (Σ T : Expr Nat, SOutB R Γ A B T l.leaves)
  | _, _, _, .ofCv u c, hΓ, hb =>
      (svalleyCv X c hΓ (by simpa only [bLink] using hb)).map (fun r =>
        ⟨.sort u, r.1, SOut.bound_of_eq r.2 (by simp only [EvTc.leaves])⟩)
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k l, hΓ, hb => by
      cases k with
      | zero =>
          exact (slinkValley X l (ctxWfT_tail hΓ) (by simpa only [bLink] using hb)).map (fun r =>
            ⟨lift 0 1 r.1, r.2.1.wk d 0,
              SOut.bound_of_eq (SOut.bound_wk d 0 r.2.2) (by simp only [EvTc.leaves])⟩)
      | succ k => exact nomatch hb
  | _, _, _, .piCod .., _, hb => nomatch hb
  | _, _, _, .subst0 .., _, hb => nomatch hb
  | _, _, _, .substLet .., _, hb => nomatch hb
  | _, _, _, .lit .., _, hb => nomatch hb
  | _, _, _, .refl .., _, hb => nomatch hb
  | _, _, _, .symm .., _, hb => nomatch hb
  | _, _, _, .trans .., _, hb => nomatch hb

/-- A heterogeneous prefix keeps the demanded index of the selected nontrivial side. -/
def sprefixValley (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P M B : Expr Nat} →
    (l : EvTc R Γ P M) → bLink l = true → (rest : Flat R Γ M B) → rest.bPrefix = true →
    Option (Σ T : Expr Nat, SOutB R Γ P B T (l.leaves ++ rest.leaves))
  | _, _, _, l, hb, .nil _, _ =>
      (slinkValley X l hΓ hb).map (fun r => ⟨r.1, r.2.1, SOut.bound_left r.2.2⟩)
  | _, _, _, l, hb, .cons l' hl' rest', hb' =>
      have h' : bLink l' = true ∧ rest'.bPrefix = true := by
        simpa only [Flat.bPrefix, Bool.and_eq_true] using hb'
      match slinkValley X l hΓ hb, sprefixValley X hΓ l' h'.1 rest' h'.2 with
      | some r₁, some r₂ =>
          (scombine X r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2).map (fun r =>
            r.elim (fun r => ⟨r₁.1, r.1, SOut.bound_of_eq r.2 (by simp only [Flat.leaves])⟩)
              (fun r => ⟨r₂.1, r.1, SOut.bound_of_eq r.2 (by simp only [Flat.leaves])⟩))
      | _, _ => none

/-! ### reading a valley, with the S calls recorded -/

/-- `readStar` with the S calls recorded: each step's leaves; or a refusal. -/
def ValleyOps.readStarC (X : ValleyOps E n) : {Γ : LCtx} → {p q T : Expr Nat} → (hs : EvParStar R Γ p q T) →
    ∀ {A B : Expr Nat}, p = .pi A B →
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×'
      Σ' (o : XOut R Γ A B A' B') (sc : List (List (Jd E n))),
        (∀ ℓ ∈ XOut.leaves o, Below ℓ hs.leaves) ∧ (∀ C ∈ sc, ∀ ℓ ∈ C, ℓ ∈ hs.leaves))
  | _, _, _, _, @EvParStar.refl _ _ _ Γ a T h, A, B, hp => by
      subst hp
      exact some ⟨A, B, rfl, (.refl Γ A, .refl _ B), [], fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ,
        fun C hC => absurd hC (List.not_mem_nil _)⟩
  | _, _, _, _, @EvParStar.tail _ _ _ Γ a b c T h hs, A, B, hp => by
      let h' : EvPar R Γ (.pi A B) b T := hp ▸ h
      rcases hS : X.S R h' with _ | ⟨A₁, B₁, hb, pay⟩
      · exact none
      · rcases ValleyOps.readStarC X hs hb with _ | ⟨A', B', hq, o₂, sc₂, bd₂, hsc₂⟩
        · exact none
        · have hpay : ∀ ℓ ∈ pay.hc.leaves ++ pay.hcB.leaves, Below ℓ h.leaves := by
            have := X.hS R h' _ hS
            subst hp
            exact this
          refine some ⟨A', B', hq, (.trans (.ofCv pay.u pay.hc) o₂.1,
            .trans (.ofCv pay.v pay.hcB) (X.K R (.ofCv pay.u pay.hc) o₂.2)), h.leaves :: sc₂,
            fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_⟩
          · simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
            simp only [EvParStar.leaves]
            rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
            · exact below_left (hpay ℓ (List.mem_append.mpr (.inl hℓ)))
            · exact below_right (XOut.below_fst bd₂ hℓ)
            · exact below_left (hpay ℓ (List.mem_append.mpr (.inr hℓ)))
            · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
              · exact below_left (hpay ℓ (List.mem_append.mpr (.inl (by simpa only [EvTc.leaves] using hℓ))))
              · exact below_right (XOut.below_snd bd₂ hℓ)
          · simp only [EvParStar.leaves, List.mem_append]
            rcases List.mem_cons.mp hC with rfl | hC
            · exact .inl hℓ
            · exact .inr (hsc₂ C hC ℓ hℓ)
  | _, _, _, _, @EvParStar.conv _ _ _ Γ a b T T' hs c, A, B, hp => by
      rcases ValleyOps.readStarC X hs hp with _ | ⟨A', B', hq, o, sc, bd, hsc⟩
      · exact none
      · exact some ⟨A', B', hq, o, sc, fun ℓ hℓ => by
          simp only [EvParStar.leaves]
          exact below_left (bd ℓ hℓ), fun C hC ℓ hℓ => by
          simp only [EvParStar.leaves, List.mem_append]
          exact .inl (hsc C hC ℓ hℓ)⟩
  | _, _, _, _, @EvParStar.wk _ _ _ Γ a b T d k hs, A, B, hp => by
      have ha : isPi a = true := by
        have := isPi_lift k 1 a
        rw [hp] at this
        exact this.symm
      obtain ⟨A₀, B₀, ha'⟩ := isPiD a ha
      rcases ValleyOps.readStarC X hs ha' with _ | ⟨A₀', B₀', hb, o₀, sc₀, bd₀, hsc₀⟩
      · exact none
      · subst ha'
        subst hb
        have hp' : Expr.pi (lift k 1 A₀) (lift (k + 1) 1 B₀) = .pi A B := hp
        injection hp' with h1 h2
        subst h1; subst h2
        exact some ⟨lift k 1 A₀', lift (k + 1) 1 B₀', rfl, (.wk d k o₀.1, .wk d (k + 1) o₀.2), sc₀,
          fun ℓ hℓ => by
            simp only [XOut.leaves, EvTc.leaves] at hℓ
            simp only [EvParStar.leaves]
            exact bd₀ ℓ hℓ,
          fun C hC ℓ hℓ => by
            simp only [EvParStar.leaves]
            exact hsc₀ C hC ℓ hℓ⟩
  | _, _, _, _, @EvParStar.trans _ _ _ Γ a b c T h₁ h₂, A, B, hp => by
      rcases ValleyOps.readStarC X h₁ hp with _ | ⟨A₁, B₁, hm, o₁, sc₁, bd₁, hsc₁⟩
      · exact none
      · rcases ValleyOps.readStarC X h₂ hm with _ | ⟨A', B', hq, o₂, sc₂, bd₂, hsc₂⟩
        · exact none
        · refine some ⟨A', B', hq, (.trans o₁.1 o₂.1, .trans o₁.2 (X.K R o₁.1 o₂.2)), sc₁ ++ sc₂,
            fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_⟩
          · simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
            simp only [EvParStar.leaves]
            rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
            · exact below_left (XOut.below_fst bd₁ hℓ)
            · exact below_right (XOut.below_fst bd₂ hℓ)
            · exact below_left (XOut.below_snd bd₁ hℓ)
            · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
              · exact below_left (XOut.below_fst bd₁ hℓ)
              · exact below_right (XOut.below_snd bd₂ hℓ)
          · simp only [EvParStar.leaves, List.mem_append]
            rcases List.mem_append.mp hC with hC | hC
            · exact .inl (hsc₁ C hC ℓ hℓ)
            · exact .inr (hsc₂ C hC ℓ hℓ)
  | _, _, _, _, @EvParStar.subst0 _ _ _ Γ a b T t v j hs hget hv, A, B, hp => by
      obtain (⟨A₀, B₀, h₁, hA, hB⟩ | ⟨_, _⟩) := instShape_pi hp
      · subst hA; subst hB
        rcases ValleyOps.readStarC X hs h₁ with _ | ⟨A₀', B₀', hq, o₀, sc₀, bd₀, hsc₀⟩
        · exact none
        · subst hq
          refine some ⟨instantiate j (lift 0 j v) A₀',
            instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀', rfl,
            (.subst0 j o₀.1 hget hv,
             EvTc.cast rfl
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
               (.subst0 (j + 1) o₀.2 (by simpa using hget)
                 (substBinderArg (d := .assumption A₀) hv))),
            sc₀, fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_⟩
          · simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
              List.mem_append] at hℓ
            simp only [EvParStar.leaves]
            rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
            · exact below_left (XOut.below_fst bd₀ hℓ)
            · exact below_right (below_of_mem hℓ)
            · exact below_left (XOut.below_snd bd₀ hℓ)
            · exact below_right (below_of_mem hℓ)
          · simp only [EvParStar.leaves, List.mem_append]
            exact .inl (hsc₀ C hC ℓ hℓ)
      · exact none
  | _, _, _, _, @EvParStar.substLet _ _ _ Γ a b T t w j hs hget hv, A, B, hp => by
      obtain (⟨A₀, B₀, h₁, hA, hB⟩ | ⟨_, _⟩) := instShape_pi hp
      · subst hA; subst hB
        rcases ValleyOps.readStarC X hs h₁ with _ | ⟨A₀', B₀', hq, o₀, sc₀, bd₀, hsc₀⟩
        · exact none
        · subst hq
          refine some ⟨instantiate j (lift 0 j w) A₀',
            instantiate (j + 1) (lift 0 1 (lift 0 j w)) B₀', rfl,
            (.substLet j o₀.1 hget hv,
             EvTc.cast rfl
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
               (.substLet (j + 1) o₀.2 (by simpa using hget)
                 (substBinderArg (d := .assumption A₀) hv))),
            sc₀, fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_⟩
          · simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
              List.mem_append] at hℓ
            simp only [EvParStar.leaves]
            rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
            · exact below_left (XOut.below_fst bd₀ hℓ)
            · exact below_right (below_of_mem hℓ)
            · exact below_left (XOut.below_snd bd₀ hℓ)
            · exact below_right (below_of_mem hℓ)
          · simp only [EvParStar.leaves, List.mem_append]
            exact .inl (hsc₀ C hC ℓ hℓ)
      · exact none

/-- Compatibility specialization of the shared operational helper. -/
def readStarC (X : Suppliers E n) : {Γ : LCtx} → {p q T : Expr Nat} → (hs : EvParStar R Γ p q T) →
    ∀ {A B : Expr Nat}, p = .pi A B →
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×'
      Σ' (o : XOut R Γ A B A' B') (sc : List (List (Jd E n))),
        (∀ ℓ ∈ XOut.leaves o, Below ℓ hs.leaves) ∧ (∀ C ∈ sc, ∀ ℓ ∈ C, ℓ ∈ hs.leaves)) :=
  ValleyOps.readStarC X.toValleyOps

/-- `readValley` with the S calls recorded; or a refusal. -/
def ValleyOps.readValleyC (X : ValleyOps E n) {A B A' B' T : Expr Nat}
    (W : Valley R Γ (.pi A B) (.pi A' B') T) :
    Option (Σ' (o : XOut R Γ A B A' B') (sc : List (List (Jd E n))),
      (∀ ℓ ∈ XOut.leaves o, Below ℓ W.leaves) ∧ (∀ C ∈ sc, ∀ ℓ ∈ C, ℓ ∈ W.leaves)) := by
  rcases ValleyOps.readStarC X W.left rfl with _ | ⟨AN, BN, hN, oL, scL, bdL, hscL⟩
  · exact none
  · rcases ValleyOps.readStarC X W.right rfl with _ | ⟨AN', BN', hN', oR, scR, bdR, hscR⟩
    · exact none
    · have hNN : Expr.pi AN BN = .pi AN' BN' := hN.symm.trans hN'
      injection hNN with h1 h2
      subst h1; subst h2
      refine some ⟨(.trans oL.1 (.symm oR.1),
        .trans oL.2 (X.K R (.trans oL.1 (.symm oR.1)) (.symm oR.2))), scL ++ scR,
        fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_⟩
      · have hL : ∀ x ∈ W.left.leaves, Below x W.leaves := fun x hx => below_of_mem (W.below_left hx)
        have hR : ∀ x ∈ W.right.leaves, Below x W.leaves := fun x hx => below_of_mem (W.below_right hx)
        simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
        · exact below_trans (XOut.below_fst bdL hℓ) hL
        · exact below_trans (XOut.below_fst bdR hℓ) hR
        · exact below_trans (XOut.below_snd bdL hℓ) hL
        · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
          · simp only [EvTc.leaves, List.mem_append] at hℓ
            rcases hℓ with hℓ | hℓ
            · exact below_trans (XOut.below_fst bdL hℓ) hL
            · exact below_trans (XOut.below_fst bdR hℓ) hR
          · exact below_trans (XOut.below_snd bdR (by simpa only [EvTc.leaves] using hℓ)) hR
      · rcases List.mem_append.mp hC with hC | hC
        · exact W.below_left (hscL C hC ℓ hℓ)
        · exact W.below_right (hscR C hC ℓ hℓ)

/-! ### segments, with the census -/

/-- Compatibility specialization of the shared operational helper. -/
def readValleyC (X : Suppliers E n) {A B A' B' T : Expr Nat}
    (W : Valley R Γ (.pi A B) (.pi A' B') T) :
    Option (Σ' (o : XOut R Γ A B A' B') (sc : List (List (Jd E n))),
      (∀ ℓ ∈ XOut.leaves o, Below ℓ W.leaves) ∧ (∀ C ∈ sc, ∀ ℓ ∈ C, ℓ ∈ W.leaves)) :=
  ValleyOps.readValleyC X.toValleyOps W

/-- a segment's census output: components, U/D/S bundles, J literals, and the bounds. -/
abbrev SegOut (R : List (Jd E n)) (Γ : LCtx) (A B A' B' : Expr Nat) (L : List (Jd E n)) : Type :=
  Σ' (o : XOut R Γ A B A' B') (calls : List (List (Jd E n))) (jcalls : List (Jd E n)),
    (∀ ℓ ∈ XOut.leaves o, Below ℓ L) ∧ (∀ C ∈ calls, ∀ ℓ ∈ C, Strict ℓ L) ∧
    (∀ j ∈ jcalls, Below j L) ∧ (∀ j ∈ jcalls, JAtom j) ∧ (calls ≠ [] → jcalls ≠ [])

/-- the Stratum-A output of a segment or tile: no calls. -/
def SegOut.ofA {A B A' B' : Expr Nat} {L : List (Jd E n)} (o : XOut R Γ A B A' B')
    (h : ∀ ℓ ∈ XOut.leaves o, Below ℓ L) : SegOut R Γ A B A' B' L :=
  ⟨o, [], [], h, fun C hC => absurd hC (List.not_mem_nil _), fun j hj => absurd hj (List.not_mem_nil _),
    fun j hj => absurd hj (List.not_mem_nil _), fun hne => absurd rfl hne⟩

/-- Read the strict core at Π endpoints, as in Devin desktop's #7115 design. The requested-index
valley is exposed by `toValley`; its pending chain never enters S (readers ignore index wrappers). -/
def ValleyOps.sread (X : ValleyOps E n) {P M T : Expr Nat} {L : List (Jd E n)} (o : SOut R Γ P M T) (h : o.Bound L)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') : Option (SegOut R Γ A B A' B' L) := by
  obtain ⟨r, cs, js⟩ := o
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  cases r with
  | triv D pending =>
      subst hP
      injection hM with e1 e2
      subst e1; subst e2
      exact some ⟨(.refl _ _, .refl _ _), cs, js, fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ, h2, h3, h4, h6⟩
  | val V pending =>
      subst hP; subst hM
      rcases ValleyOps.readValleyC X V with _ | ⟨out, sc, hout, hsc⟩
      · exact none
      · refine some ⟨out, cs ++ sc, js, fun ℓ hℓ => below_trans (hout ℓ hℓ) (fun x hx => below_of_strict (h1 x hx)),
          fun C hC ℓ hℓ => ?_, h3, h4, fun _ => h5 rfl⟩
        rcases List.mem_append.mp hC with hC | hC
        · exact h2 C hC ℓ hℓ
        · exact h1 ℓ (hsc C hC ℓ hℓ)

/-- Compatibility specialization of the shared operational helper. -/
def sread (X : Suppliers E n) {P M T : Expr Nat} {L : List (Jd E n)} (o : SOut R Γ P M T) (h : o.Bound L)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') : Option (SegOut R Γ A B A' B' L) :=
  ValleyOps.sread X.toValleyOps o h hP hM

/-- X on one segment, with the census; or a refusal. A single Π-spined link is Stratum A: no call. -/
def xSegS (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P M : Expr Nat} → (p : Flat R Γ P M) →
    p.segAdm = true → ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (SegOut R Γ A B A' B' p.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hM =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hM
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, .cons l hl (.nil _), hadm, A, B, A', B', hP, hM =>
      if hp : piSpinedTc l = true then
        some (SegOut.ofA (xStructTc X.K X.hK X.hsep l hp hP hM) (fun ℓ hℓ => by
          simp only [Flat.leaves, List.append_nil]
          exact xStructTc_leaves X.K X.hK X.hsep l hp hP hM ℓ hℓ))
      else
        have hb : bLink l = true := by
          have h' : (piSpinedTc l || bLink l) = true := by simpa only [Flat.segAdm] using hadm
          simpa only [Bool.or_eq_true, hp, Bool.false_eq_true, false_or] using h'
        match slinkValley X l hΓ hb with
        | none => none
        | some ⟨_, o, ho⟩ =>
            sread X o (SOut.bound_of_eq ho (by simp only [Flat.leaves, List.append_nil])) hP hM
  | _, _, .cons l hl (.cons l' hl' rest'), hadm, A, B, A', B', hP, hM =>
      have h' : bLink l = true ∧ (Flat.cons l' hl' rest').bPrefix = true := by
        simpa only [Flat.segAdm, Bool.and_eq_true] using hadm
      match sprefixValley X hΓ l h'.1 (Flat.cons l' hl' rest') h'.2 with
      | none => none
      | some ⟨_, o, ho⟩ => sread X o (SOut.bound_of_eq ho (by simp only [Flat.leaves])) hP hM

/-- composing two segment outputs: components by `trans`, codomains moved by `K`, censuses
    appended. -/
def ValleyOps.comp (X : ValleyOps E n) {A B A₁ B₁ A' B' : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (r₁ : SegOut R Γ A B A₁ B₁ L₁) (r₂ : SegOut R Γ A₁ B₁ A' B' L₂) :
    SegOut R Γ A B A' B' (L₁ ++ L₂) := by
  obtain ⟨o₁, c₁, j₁, b₁, s₁, jb₁, ja₁, cj₁⟩ := r₁
  obtain ⟨o₂, c₂, j₂, b₂, s₂, jb₂, ja₂, cj₂⟩ := r₂
  refine ⟨(.trans o₁.1 o₂.1, .trans o₁.2 (X.K R o₁.1 o₂.2)), c₁ ++ c₂, j₁ ++ j₂,
    fun ℓ hℓ => ?_, fun C hC ℓ hℓ => ?_, fun j hj => ?_, fun j hj => ?_, fun hne => ?_⟩
  · simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
    rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
    · exact below_left (XOut.below_fst b₁ hℓ)
    · exact below_right (XOut.below_fst b₂ hℓ)
    · exact below_left (XOut.below_snd b₁ hℓ)
    · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
      · exact below_left (XOut.below_fst b₁ hℓ)
      · exact below_right (XOut.below_snd b₂ hℓ)
  · rcases List.mem_append.mp hC with hC | hC
    · exact strict_left (s₁ C hC ℓ hℓ)
    · exact strict_right (s₂ C hC ℓ hℓ)
  · rcases List.mem_append.mp hj with hj | hj
    · exact below_left (jb₁ j hj)
    · exact below_right (jb₂ j hj)
  · rcases List.mem_append.mp hj with hj | hj
    · exact ja₁ j hj
    · exact ja₂ j hj
  · cases hc1 : c₁ with
    | nil =>
        subst hc1
        exact ne_nil_append_right (cj₂ (by simpa using hne))
    | cons C cs =>
        exact ne_nil_append_left (cj₁ (by rw [hc1]; exact List.cons_ne_nil _ _))

/-- Compatibility specialization of the shared operational helper. -/
def SegOut.comp (X : Suppliers E n) {A B A₁ B₁ A' B' : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (r₁ : SegOut R Γ A B A₁ B₁ L₁) (r₂ : SegOut R Γ A₁ B₁ A' B' L₂) :
    SegOut R Γ A B A' B' (L₁ ++ L₂) :=
  ValleyOps.comp X.toValleyOps r₁ r₂

/-- rebasing a segment output's bound. -/
def SegOut.cast {A B A' B' : Expr Nat} {L L' : List (Jd E n)} (e : L = L')
    (r : SegOut R Γ A B A' B' L) : SegOut R Γ A B A' B' L' := e ▸ r

/-- X on the segments, with the census; or a refusal. -/
def xSegsS (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    s.adm = true → ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (SegOut R Γ A B A' B' s.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hQ =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hQ
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, A, B, A', B', hP, hQ =>
      have h' : p.segAdm = true ∧ rest.adm = true := by
        simpa only [Segs.adm, Bool.and_eq_true] using hadm
      match isPiD M hM with
      | ⟨A₁, B₁, hM'⟩ =>
        match xSegS X hΓ p h'.1 hP hM', xSegsS X hΓ rest h'.2 hM' hQ with
        | some r₁, some r₂ => some (SegOut.cast (by simp only [Segs.leaves]) (SegOut.comp X r₁ r₂))
        | _, _ => none

/-! ### the strict X route and its census -/

/-- the strict X route on an admissible input: components, U/D/S bundles, J literals, bounds; or
    a refusal. -/
def xValleyS? (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  (xSegsS X hΓ ((flattenTc c).segment rfl) hadm rfl rfl).map (fun r => by
    obtain ⟨o, calls, jcalls, h1, h2, h3, h4, h5⟩ := r
    rw [Flat.segment_leaves] at h1 h2 h3
    exact ⟨o, calls, jcalls, fun ℓ hℓ => below_trans (h1 ℓ hℓ) (flattenTc_leaves c),
      fun C hC ℓ hℓ => strict_of_strict_below (h2 C hC ℓ hℓ) (flattenTc_leaves c),
      fun j hj => below_trans (h3 j hj) (flattenTc_leaves c), h4, h5⟩)

/-- `XContractWf`'s clause for every answer of the strict route. -/
theorem xValleyS_contract (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleyS? X hΓ c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  r.2.2.2.1

/-! ### Stratum A answers for every supplier bundle -/

theorem xSegS_isSome_of_spined (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {P M : Expr Nat}
    (l : EvTc R Γ P M) (hl : isLink l = true) (hadm : (Flat.cons l hl (Flat.nil M)).segAdm = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') :
    (xSegS X hΓ (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome = true := by
  rw [xSegS, dif_pos hp]
  rfl

theorem xSegsS_isSome_of_stratumA (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P Q : Expr Nat} →
    (s : Segs R Γ P Q) → (hadm : s.adm = true) → s.stratumA = true →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    (xSegsS X hΓ s hadm hP hQ).isSome = true
  | _, _, .nil _, _, _, A, B, A', B', hP, hQ => rfl
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, hsA, A, B, A', B', hP, hQ => by
      cases p with
      | nil _ => simp only [Segs.stratumA, Bool.false_eq_true] at hsA
      | cons l hl rest' =>
          cases rest' with
          | cons _ _ _ => simp only [Segs.stratumA, Bool.false_eq_true] at hsA
          | nil _ =>
              simp only [Segs.stratumA, Bool.and_eq_true] at hsA
              obtain ⟨hp, hsA'⟩ := hsA
              have h' : (Flat.cons l hl (Flat.nil M)).segAdm = true ∧ rest.adm = true := by
                simpa only [Segs.adm, Bool.and_eq_true] using hadm
              obtain ⟨A₁, B₁, hM'⟩ := isPi_true hM
              have h1 := xSegS_isSome_of_spined X hΓ l hl h'.1 hp hP hM'
              have h2 := xSegsS_isSome_of_stratumA X hΓ rest h'.2 hsA' hM' hQ
              subst hM'
              rw [xSegsS]
              simp only [isPiD]
              split
              · rfl
              · rename_i hne
                exfalso
                rcases e1 : xSegS X hΓ (Flat.cons l hl (Flat.nil _)) h'.1 hP rfl with _ | r₁
                · rw [e1] at h1; simp at h1
                · rcases e2 : xSegsS X hΓ rest h'.2 rfl hQ with _ | r₂
                  · rw [e2] at h2; simp at h2
                  · exact hne r₁ r₂ e1 e2

/-- Stratum A is answered by every supplier bundle (nothing here is vacuous). -/
theorem xValleyS?_isSome_of_piSpined (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xValleyS? X hΓ c (xAdm_of_piSpined c hp)).isSome = true := by
  simp only [xValleyS?, isSome_map']
  exact xSegsS_isSome_of_stratumA X hΓ _ _
    (segmentF_stratumA_of_spined _ (flattenTc c) rfl (Nat.le_refl _) (flattenTc_spined c hp rfl rfl))
    rfl rfl

/-! ### the edges -/

/-- E2 with a drop: a J literal equal to an input leaf, with another atom present
    (`L = s ++ j :: t`, `s ++ t ≠ []`; no decidable equality on atoms is needed). -/
theorem om3_edge_drop_to {L Z s t : List (Jd E n)} {j : Jd E n} (hL : L = s ++ j :: t)
    (hne : s ++ t ≠ []) : OM3_edge (L ++ Z) ([j] ++ Z) := by
  unfold OM3_edge
  refine ⟨(s ++ t).map Jd.wt, [], ([j] ++ Z).map Jd.wt, ?_, ?_, List.Perm.refl _,
    fun _ h => absurd h (List.not_mem_nil _)⟩
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · rw [← List.map_append]
    refine List.Perm.map Jd.wt ?_
    subst hL
    have h1 : (s ++ j :: t ++ Z).Perm (j :: (s ++ (t ++ Z))) := by
      rw [List.append_assoc, List.cons_append]
      exact List.perm_middle
    have h2 : (j :: (s ++ (t ++ Z))).Perm (s ++ t ++ ([j] ++ Z)) := by
      rw [List.singleton_append, ← List.append_assoc]
      exact List.perm_middle.symm
    exact h1.trans h2

theorem EvTy.size_pos : {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) → 1 ≤ D.size
  | _, _, _, .lit _ _ => by simp only [EvTy.size]; omega
  | _, _, _, .wk _ _ _ => by simp only [EvTy.size]; omega
  | _, _, _, .esub .. => by simp only [EvTy.size]; omega
  | _, _, _, .subst0 .. => by simp only [EvTy.size]; omega
  | _, _, _, .substLet .. => by simp only [EvTy.size]; omega
  | _, _, _, .rety _ _ => by simp only [EvTy.size]; omega
  | _, _, _, .var .. => by simp only [EvTy.size]; omega
  | _, _, _, .sort _ => by simp only [EvTy.size]; omega
  | _, _, _, .const .. => by simp only [EvTy.size]; omega

theorem EvCv.size_pos : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) → 1 ≤ c.size
  | _, _, _, _, .lit _ _ => by simp only [EvCv.size]; omega
  | _, _, _, _, .refl _ => by simp only [EvCv.size]; omega
  | _, _, _, _, .symm _ => by simp only [EvCv.size]; omega
  | _, _, _, _, .trans _ _ => by simp only [EvCv.size]; omega
  | _, _, _, _, .tyConv .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .wk .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .esub .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .subst0 .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .substLet .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .sorts .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .consts .. => by simp only [EvCv.size]; omega
  | _, _, _, _, .rety .. => by simp only [EvCv.size]; omega

/-- a `cv` atom among a chain's leaves sits under a node (`ofCv`, …), so the chain has size ≥ 2. -/
theorem EvTc.size_ge_two_of_cv_mem : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    {Γ' : LCtx} → {a b T : Expr Nat} → {h : ConvT E n Γ' a b T} → Jd.cv h ∈ c.leaves → 2 ≤ c.size
  | _, _, _, .lit d _, _, _, _, _, _, hm => by
      simp only [EvTc.leaves, List.mem_cons, List.not_mem_nil, or_false] at hm
      cases hm
  | _, _, _, .refl _ _, _, _, _, _, _, hm => by
      simp only [EvTc.leaves, List.not_mem_nil] at hm
  | _, _, _, .ofCv _ c, _, _, _, _, _, _ => by
      have := EvCv.size_pos c
      simp only [EvTc.size]; omega
  | _, _, _, .symm c, _, _, _, _, _, _ => by
      have := EvTc.size_ge_two_of_cv_mem c (by assumption)
      simp only [EvTc.size]; omega
  | _, _, _, .trans c₁ c₂, _, _, _, _, _, hm => by
      simp only [EvTc.leaves, List.mem_append] at hm
      rcases hm with hm | hm
      · have := EvTc.size_ge_two_of_cv_mem c₁ hm
        simp only [EvTc.size]; omega
      · have := EvTc.size_ge_two_of_cv_mem c₂ hm
        simp only [EvTc.size]; omega
  | _, _, _, .piCod _ hA c, _, _, _, _, _, _ => by
      have := EvTy.size_pos hA
      simp only [EvTc.size]; omega
  | _, _, _, .subst0 _ c _ hv, _, _, _, _, _, _ => by
      have := EvTy.size_pos hv
      simp only [EvTc.size]; omega
  | _, _, _, .substLet _ c _ hv, _, _, _, _, _, _ => by
      have := EvTy.size_pos hv
      simp only [EvTc.size]; omega
  | _, _, _, .wk _ _ h, _, _, _, _, _, hm => by
      have := EvTc.size_ge_two_of_cv_mem h (by simpa only [EvTc.leaves] using hm)
      simp only [EvTc.size]; omega

/-- the census of an answer: every recorded call as a (caller, callee) measure pair; U/D/S
    bundles with size 0 (a `DMStep` needs no size), J literals with the literal node's size 1. -/
def census {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (r : SegOut R Γ A B A' B' c.leaves) (Z : List (Jd E n)) :
    List (CallMeasure E n × CallMeasure E n) :=
  r.2.1.map (fun C => ((c.leaves ++ Z, c.size), (C ++ Z, 0))) ++
  r.2.2.1.map (fun j => ((c.leaves ++ Z, c.size), ([j] ++ Z, 1)))

/-- every call of a bounded output is a lex edge from the caller `(c.leaves ++ Z, c.size)`: U/D/S
    by strictness, a J literal strictly below an input leaf likewise (E1), equal to one by a drop
    (E2) or by the size step when it is the only atom (E-X-LONE). -/
theorem census_edges {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (r : SegOut R Γ A B A' B' c.leaves) (Z : List (Jd E n)) : EdgeContractLex (census c r Z) := by
  intro p hp
  obtain ⟨_, hstrict, hjb, hja, hcj⟩ := r.2.2.2
  simp only [census, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨C, hC, rfl⟩ | ⟨j, hj, rfl⟩
  · have hne : r.2.2.1 ≠ [] := hcj (List.ne_nil_of_mem hC)
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hne
    have hX : c.leaves ≠ [] := below_ne_nil (hjb j hj)
    exact om3_edgeLex_of_edge (om3_edge_of_strictLeaves hX (fun ℓ hℓ => hstrict C hC ℓ hℓ)) _ _
  · obtain ⟨x, hx, hs⟩ := hjb j hj
    have hX : c.leaves ≠ [] := List.ne_nil_of_mem hx
    rcases hs with heq | hsub
    · subst heq
      obtain ⟨s, t, hL⟩ := List.append_of_mem hx
      cases hst : s ++ t with
      | nil =>
          obtain ⟨hs0, ht0⟩ := List.append_eq_nil.mp hst
          subst hs0; subst ht0
          simp only [List.nil_append] at hL
          rw [hL]
          obtain ⟨_, _, _, _, h, rfl⟩ := hja j hj
          exact om3_edgeLex_lone _ (by have := EvTc.size_ge_two_of_cv_mem c hx; omega)
      | cons y ys =>
          exact om3_edgeLex_of_edge (om3_edge_drop_to hL (by rw [hst]; exact List.cons_ne_nil _ _)) _ _
    · exact om3_edgeLex_of_edge (om3_edge_of_strictLeaves hX (L := [j]) (fun ℓ hℓ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
        subst hℓ
        exact ⟨x, hx, hsub⟩)) _ _

/-- the strict route's answers carry a lex-edge census. -/
theorem xValleyS_edges (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleyS? X hΓ c hadm = some r) (Z : List (Jd E n)) : EdgeContractLex (census c r Z) :=
  census_edges c r Z

/-! ### pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the etaK request is answered by the declining suppliers through the strict route (Stratum A),
    and the answer's census — empty — is a lex census. -/
theorem pin_request_answered_strict (hsep : SepAll emptyEnv 0) :
    (xValleyS? (Suppliers.declining hsep) CtxWfT.nil request pin_request_xAdm).isSome = true :=
  xValleyS?_isSome_of_piSpined (Suppliers.declining hsep) CtxWfT.nil request pin_request_piSpined

/-- the β fixture through the strict route, for any suppliers: every answer's census is lex edges. -/
theorem pin_betaMiddle_edges (X : Suppliers emptyEnv 0) (r) (hr : xValleyS? X CtxWfT.nil
      (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
        EvTc [Jd.tc betaMiddleT] [] piX piX) pin_betaMiddle_xAdm = some r) (Z : List (Jd emptyEnv 0)) :
    EdgeContractLex (census _ r Z) :=
  xValleyS_edges X CtxWfT.nil _ pin_betaMiddle_xAdm r hr Z

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.Strict
#print axioms Rcic.Declarative.F8Measure.strict_left
#print axioms Rcic.Declarative.F8Measure.strict_right
#print axioms Rcic.Declarative.F8Measure.below_of_strict
#print axioms Rcic.Declarative.F8Measure.strict_of_below
#print axioms Rcic.Declarative.F8Measure.strict_of_strict_below
#print axioms Rcic.Declarative.F8Measure.ne_nil_append_left
#print axioms Rcic.Declarative.F8Measure.ne_nil_append_right
#print axioms Rcic.Declarative.F8Measure.below_ne_nil
#print axioms Rcic.Declarative.F8Measure.JAtom
#print axioms Rcic.Declarative.F8Measure.SRes
#print axioms Rcic.Declarative.F8Measure.SRes.leaves
#print axioms Rcic.Declarative.F8Measure.SRes.isVal
#print axioms Rcic.Declarative.F8Measure.SRes.symm
#print axioms Rcic.Declarative.F8Measure.SRes.symm_leaves_mem
#print axioms Rcic.Declarative.F8Measure.SRes.isVal_symm
#print axioms Rcic.Declarative.F8Measure.SRes.wk
#print axioms Rcic.Declarative.F8Measure.SRes.wk_leaves
#print axioms Rcic.Declarative.F8Measure.SRes.isVal_wk
#print axioms Rcic.Declarative.F8Measure.SOut
#print axioms Rcic.Declarative.F8Measure.SOut.Bound
#print axioms Rcic.Declarative.F8Measure.SOut.bound_left
#print axioms Rcic.Declarative.F8Measure.SOut.bound_right
#print axioms Rcic.Declarative.F8Measure.SOut.bound_of_eq
#print axioms Rcic.Declarative.F8Measure.SOut.bound_triv
#print axioms Rcic.Declarative.F8Measure.SOut.symm
#print axioms Rcic.Declarative.F8Measure.SOut.bound_symm
#print axioms Rcic.Declarative.F8Measure.SOut.wk
#print axioms Rcic.Declarative.F8Measure.SOut.bound_wk
#print axioms Rcic.Declarative.F8Measure.SOutB
#print axioms Rcic.Declarative.F8Measure.sjoin
#print axioms Rcic.Declarative.F8Measure.scombine
#print axioms Rcic.Declarative.F8Measure.svalleyCv
#print axioms Rcic.Declarative.F8Measure.slinkValley
#print axioms Rcic.Declarative.F8Measure.sprefixValley
#print axioms Rcic.Declarative.F8Measure.readStarC
#print axioms Rcic.Declarative.F8Measure.readValleyC
#print axioms Rcic.Declarative.F8Measure.SegOut
#print axioms Rcic.Declarative.F8Measure.SegOut.ofA
#print axioms Rcic.Declarative.F8Measure.sread
#print axioms Rcic.Declarative.F8Measure.xSegS
#print axioms Rcic.Declarative.F8Measure.SegOut.comp
#print axioms Rcic.Declarative.F8Measure.SegOut.cast
#print axioms Rcic.Declarative.F8Measure.xSegsS
#print axioms Rcic.Declarative.F8Measure.xValleyS?
#print axioms Rcic.Declarative.F8Measure.xValleyS_contract
#print axioms Rcic.Declarative.F8Measure.xSegS_isSome_of_spined
#print axioms Rcic.Declarative.F8Measure.xSegsS_isSome_of_stratumA
#print axioms Rcic.Declarative.F8Measure.xValleyS?_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.om3_edge_drop_to
#print axioms Rcic.Declarative.F8Measure.EvTy.size_pos
#print axioms Rcic.Declarative.F8Measure.EvCv.size_pos
#print axioms Rcic.Declarative.F8Measure.EvTc.size_ge_two_of_cv_mem
#print axioms Rcic.Declarative.F8Measure.census
#print axioms Rcic.Declarative.F8Measure.census_edges
#print axioms Rcic.Declarative.F8Measure.xValleyS_edges
#print axioms Rcic.Declarative.F8Measure.pin_request_answered_strict
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_edges

#print axioms Rcic.Declarative.F8Measure.SRes.pendingLeaves
#print axioms Rcic.Declarative.F8Measure.SRes.toValley
#print axioms Rcic.Declarative.F8Measure.SRes.symm_pendingLeaves
#print axioms Rcic.Declarative.F8Measure.SRes.wk_pendingLeaves
#print axioms Rcic.Declarative.F8Measure.SRes.rety
#print axioms Rcic.Declarative.F8Measure.SRes.rety_leaves
#print axioms Rcic.Declarative.F8Measure.SRes.rety_pendingLeaves
#print axioms Rcic.Declarative.F8Measure.SRes.isVal_rety
#print axioms Rcic.Declarative.F8Measure.SRes.toValley_leaves
#print axioms Rcic.Declarative.F8Measure.SOut.toValley
#print axioms Rcic.Declarative.F8Measure.SOut.toValley_below
#print axioms Rcic.Declarative.F8Measure.SOut.rety
#print axioms Rcic.Declarative.F8Measure.SOut.bound_rety
