import rcic.RcicF8EvParStar

/-!
# `RcicF8DTileBase` — the D tile, slice D1 (generic layer)

S0: `research/rcic/d-tile/S0_D_TILE.md` (#7060), cc ruling 11:44Z on #7060 (Q1 D1 approved,
Q3 derived spine view, no pushing `.wk` into payloads).

* `DProcWf` / `DContractWf` — the context-conditional H-D (cc ruling 1, #7035: a typing may be
  materialized inside D, so the caller supplies `CtxWfT E n Γ`; suppliers take `EnvWfT E` at the
  module boundary). The Γ-unconditional `DProc`/`DContract` of `RcicF8EvParStar` are untouched.
* `EvPar.rightTy` — every landed `EvPar` step carries a typing of its right endpoint at its
  own index, with leaves among the step's.
* The DERIVED spine view (cc Q3). `DStep` is a single `EvPar` step under a stack of the
  star's own lazy transports (`conv`, `wk`); `DSpine` is a `refl`/`tail` list of `DStep`s.
  `EvParStar.spine` distributes `.conv` and `.wk` over the steps of a star; no `EvPar`
  payload is rewritten and no carrier constructor is added. Leaf laws:
  `DSpine.wk` preserves leaves EXACTLY (`DSpine.wk_leaves`), `EvParStar.spine` invents no
  leaf (`EvParStar.spine_leaves`: every spine leaf is a leaf of the star; `.conv` may repeat
  its chain's leaves at every step, `.trans` drops the joint's `refl` typing), and
  `DSpine.toStar` back to `EvParStar` invents no leaf either (`DSpine.toStar_leaves`).
* `DStepDiamondWf` — a CERTIFIED 0-or-1 step diamond on `DStep`s (the soundness clause is a
  field of the output, `DOptJoin.sound`). `dStripWf` (structural on the right spine) and
  `dStarWf` (structural on the left spine) lift it to spines with no measure, and
  `dProcWf_of_step` / `dContractWf_of_step` deliver `DProcWf` and `DContractWf`.

The step-diamond instance (the {proofIndex, structPi} 2×2 table, S0 §2) is the next slice;
this module takes the step diamond as an ARGUMENT of a combinator, not as a premise of any
sealed statement about `EvPar`. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### the context-conditional H-D -/

/-- H-D (context-conditional): the diamond on provenance stars at a common index, in a
    well-formed context. -/
abbrev DProcWf (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, CtxWfT E n Γ → EvParStar R Γ a b T →
    EvParStar R Γ a c T → Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T

/-- H-D's leaf contract for `DProcWf`: every leaf of the two closing legs is `SubEq` a leaf
    of the two input stars. -/
def DContractWf (D : ∀ R : List (Jd E n), DProcWf R) : Prop :=
  ∀ R {Γ : LCtx} {a b c T : Expr Nat} (hΓ : CtxWfT E n Γ) (h₁ : EvParStar R Γ a b T)
    (h₂ : EvParStar R Γ a c T),
    ∀ ℓ ∈ (D R hΓ h₁ h₂).2.1.leaves ++ (D R hΓ h₁ h₂).2.2.leaves,
      ∃ ℓ' ∈ h₁.leaves ++ h₂.leaves, SubEq ℓ ℓ'

/-! ### `SubEq` bookkeeping -/

theorem dSubEq_trans {x y z : Jd E n} (hxy : SubEq x y) (hyz : SubEq y z) : SubEq x z := by
  cases hxy with
  | inl h => subst h; exact hyz
  | inr h => exact .inr (subOf_trans_subEq h hyz)

/-- membership gives `SubEq` into the list. -/
theorem dSubEq_of_mem {ℓ : Jd E n} {L : List (Jd E n)} (h : ℓ ∈ L) :
    ∃ ℓ' ∈ L, SubEq ℓ ℓ' :=
  ⟨ℓ, h, .inl rfl⟩

/-- `SubEq`-covering is transitive through an intermediate list. -/
theorem dCover_trans {L M N : List (Jd E n)}
    (hLM : ∀ ℓ ∈ L, ∃ m ∈ M, SubEq ℓ m) (hMN : ∀ m ∈ M, ∃ k ∈ N, SubEq m k) :
    ∀ ℓ ∈ L, ∃ k ∈ N, SubEq ℓ k := by
  intro ℓ hℓ
  obtain ⟨m, hm, h₁⟩ := hLM ℓ hℓ
  obtain ⟨k, hk, h₂⟩ := hMN m hm
  exact ⟨k, hk, dSubEq_trans h₁ h₂⟩

/-! ### the right-endpoint typing of a step -/

/-- the typing of a step's right endpoint at the step's own index. -/
def EvPar.rightTy : {Γ : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T → EvTy R Γ b T
  | _, _, _, _, .proofIndex p => p.rightTy
  | _, _, _, _, .structPi p => .rety p.hrt p.idx
  | _, _, _, _, .sortEq p => .rety p.hr p.idx
  | _, _, _, _, .consts p => .rety p.hr p.idx
  | _, _, _, _, .lit p => .rety p.hexp p.idx
  | _, _, _, _, .refl p => .rety p.h p.idx

/-- its leaves are among the step's. -/
theorem EvPar.rightTy_leaves : {Γ : LCtx} → {a b T : Expr Nat} → (D : EvPar R Γ a b T) →
    ∀ ℓ ∈ D.rightTy.leaves, ℓ ∈ D.leaves
  | _, _, _, _, .proofIndex p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, ProofIndexPayload.leaves, List.mem_append] at hℓ ⊢
      exact .inr hℓ
  | _, _, _, _, .structPi p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, StructPiPayload.leaves, EvTy.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, _, .sortEq p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, SortEqPayload.leaves, EvTy.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, _, .consts p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, ConstsPayload.leaves, EvTy.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, _, .lit p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, LitPayload.leaves, EvTy.leaves,
        List.mem_append] at hℓ ⊢
      exact hℓ
  | _, _, _, _, .refl p => fun ℓ hℓ => by
      simp only [EvPar.rightTy, EvPar.leaves, ReflPayload.leaves, EvTy.leaves,
        List.mem_append] at hℓ ⊢
      exact hℓ

def DeltaPayload.rightTy {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : EvTy R Γ (instantiateLevels ls body) T :=
  .rety p.hr p.idx

theorem DeltaPayload.rightTy_leaves {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : ∀ ℓ ∈ p.rightTy.leaves, ℓ ∈ p.leaves := by
  intro ℓ hℓ
  simp only [DeltaPayload.rightTy, DeltaPayload.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with h | h
  · exact .inl (.inr h)
  · exact .inr h

def BVarZetaPayload.rightTy {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : EvTy R Γ (lift 0 (i + 1) v') T :=
  .rety p.hr p.idx

theorem BVarZetaPayload.rightTy_leaves {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : ∀ ℓ ∈ p.rightTy.leaves, ℓ ∈ p.leaves := by
  intro ℓ hℓ
  simp only [BVarZetaPayload.rightTy, BVarZetaPayload.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with h | h
  · exact .inl (.inr h)
  · exact .inr h

def LamPayload.rightTy {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : EvTy R Γ (.lam A' body') T :=
  .rety p.hrt p.idx

theorem LamPayload.rightTy_leaves {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : ∀ ℓ ∈ p.rightTy.leaves, ℓ ∈ p.leaves := by
  intro ℓ hℓ
  simp only [LamPayload.rightTy, LamPayload.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with h | h
  · exact .inl (.inr h)
  · exact .inr h

def AppPayload.rightTy {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : EvTy R Γ (.app f' a') T :=
  .rety p.hr p.idx

theorem AppPayload.rightTy_leaves {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : ∀ ℓ ∈ p.rightTy.leaves, ℓ ∈ p.leaves := by
  intro ℓ hℓ
  simp only [AppPayload.rightTy, AppPayload.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with h | h
  · exact .inl (.inr h)
  · exact .inr h

def LetEPayload.rightTy {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) : EvTy R Γ (.letE A' value' body') T :=
  .rety p.hrt p.idx

theorem LetEPayload.rightTy_leaves {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) : ∀ ℓ ∈ p.rightTy.leaves, ℓ ∈ p.leaves := by
  intro ℓ hℓ
  simp only [LetEPayload.rightTy, LetEPayload.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with h | h
  · exact .inl (.inr h)
  · exact .inr h

/-! ### the derived spine view (cc Q3) -/

/-- one `EvPar` step under a stack of the star's lazy transports. -/
inductive DStep (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | base {Γ : LCtx} {a b T : Expr Nat} (h : EvPar R Γ a b T) : DStep R Γ a b T
  | conv {Γ : LCtx} {a b T T' : Expr Nat} (s : DStep R Γ a b T) (c : EvTc R Γ T T') :
      DStep R Γ a b T'
  | wk {Γ : LCtx} {a b T : Expr Nat} (d : LocalDecl) (k : Nat) (s : DStep R Γ a b T) :
      DStep R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T)
  /-- the star's lazy substitutions (W-X-SUBST slice 1), as transports of one step. -/
  | subst0 {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (s : DStep R Γ a b T)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      DStep R (substRemove v j Γ) (instantiate j (lift 0 j v) a)
        (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  | substLet {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat) (s : DStep R Γ a b T)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
      DStep R (substRemove w j Γ) (instantiate j (lift 0 j w) a)
        (instantiate j (lift 0 j w) b) (instantiate j (lift 0 j w) T)

/-- literal leaves of a transported step. -/
def DStep.leaves : {Γ : LCtx} → {a b T : Expr Nat} → DStep R Γ a b T → List (Jd E n)
  | _, _, _, _, .base h => h.leaves
  | _, _, _, _, .conv s c => s.leaves ++ c.leaves
  | _, _, _, _, .wk _ _ s => s.leaves
  | _, _, _, _, .subst0 _ s _ hv => s.leaves ++ hv.leaves
  | _, _, _, _, .substLet _ s _ hv => s.leaves ++ hv.leaves

/-- the right-endpoint typing, transported lazily. -/
def DStep.rightTy : {Γ : LCtx} → {a b T : Expr Nat} → DStep R Γ a b T → EvTy R Γ b T
  | _, _, _, _, .base h => h.rightTy
  | _, _, _, _, .conv s c => .rety s.rightTy c
  | _, _, _, _, .wk d k s => .wk d k s.rightTy
  | _, _, _, _, .subst0 j s hget hv => .subst0 j s.rightTy hget hv
  | _, _, _, _, .substLet j s hget hv => .substLet j s.rightTy hget hv

theorem DStep.rightTy_leaves : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    ∀ ℓ ∈ s.rightTy.leaves, ℓ ∈ s.leaves
  | _, _, _, _, .base h => h.rightTy_leaves
  | _, _, _, _, .conv s c => fun ℓ hℓ => by
      simp only [DStep.rightTy, DStep.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.rightTy_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .wk _ _ s => fun ℓ hℓ => by
      simp only [DStep.rightTy, DStep.leaves, EvTy.leaves] at hℓ ⊢
      exact s.rightTy_leaves ℓ hℓ
  | _, _, _, _, .subst0 _ s _ _ => fun ℓ hℓ => by
      simp only [DStep.rightTy, DStep.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.rightTy_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .substLet _ s _ _ => fun ℓ hℓ => by
      simp only [DStep.rightTy, DStep.leaves, EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.rightTy_leaves ℓ h)
      · exact .inr h

/-- a transported step as a one-step star, through the star's own constructors. -/
def DStep.star1 : {Γ : LCtx} → {a b T : Expr Nat} → DStep R Γ a b T → EvParStar R Γ a b T
  | _, _, _, _, .base h => .tail h (.refl h.rightTy)
  | _, _, _, _, .conv s c => .conv s.star1 c
  | _, _, _, _, .wk d k s => .wk d k s.star1
  | _, _, _, _, .subst0 j s hget hv => .subst0 j s.star1 hget hv
  | _, _, _, _, .substLet j s hget hv => .substLet j s.star1 hget hv

theorem DStep.star1_leaves : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    ∀ ℓ ∈ s.star1.leaves, ℓ ∈ s.leaves
  | _, _, _, _, .base h => fun ℓ hℓ => by
      simp only [DStep.star1, DStep.leaves, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h' | h'
      · exact h'
      · exact h.rightTy_leaves ℓ h'
  | _, _, _, _, .conv s c => fun ℓ hℓ => by
      simp only [DStep.star1, DStep.leaves, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.star1_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .wk _ _ s => fun ℓ hℓ => by
      simp only [DStep.star1, DStep.leaves, EvParStar.leaves] at hℓ ⊢
      exact s.star1_leaves ℓ hℓ
  | _, _, _, _, .subst0 _ s _ _ => fun ℓ hℓ => by
      simp only [DStep.star1, DStep.leaves, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.star1_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .substLet _ s _ _ => fun ℓ hℓ => by
      simp only [DStep.star1, DStep.leaves, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.star1_leaves ℓ h)
      · exact .inr h

/-- a `refl`/`tail` spine of transported steps. -/
inductive DSpine (R : List (Jd E n)) (Γ : LCtx) (T : Expr Nat) :
    Expr Nat → Expr Nat → Type where
  | refl {a : Expr Nat} (h : EvTy R Γ a T) : DSpine R Γ T a a
  | tail {a b c : Expr Nat} (s : DStep R Γ a b T) (hs : DSpine R Γ T b c) :
      DSpine R Γ T a c

def DSpine.leaves {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} → DSpine R Γ T a b → List (Jd E n)
  | _, _, .refl h => h.leaves
  | _, _, .tail s hs => s.leaves ++ hs.leaves

/-- the typing of the spine's right endpoint (its terminal `refl`). -/
def DSpine.rightTy {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} → DSpine R Γ T a b → EvTy R Γ b T
  | _, _, .refl h => h
  | _, _, .tail _ hs => hs.rightTy

theorem DSpine.rightTy_leaves {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    (hs : DSpine R Γ T a b) → ∀ ℓ ∈ hs.rightTy.leaves, ℓ ∈ hs.leaves
  | _, _, .refl _ => fun _ h => h
  | _, _, .tail _ hs => fun ℓ hℓ => by
      simp only [DSpine.rightTy, DSpine.leaves, List.mem_append] at hℓ ⊢
      exact .inr (hs.rightTy_leaves ℓ hℓ)

/-- concatenation (the joint's `refl` typing is dropped). -/
def DSpine.append {Γ : LCtx} {T : Expr Nat} : {a b c : Expr Nat} → DSpine R Γ T a b →
    DSpine R Γ T b c → DSpine R Γ T a c
  | _, _, _, .refl _, h₂ => h₂
  | _, _, _, .tail s hs, h₂ => .tail s (hs.append h₂)

theorem DSpine.append_leaves {Γ : LCtx} {T : Expr Nat} : {a b c : Expr Nat} →
    (h₁ : DSpine R Γ T a b) → (h₂ : DSpine R Γ T b c) →
    ∀ ℓ ∈ (h₁.append h₂).leaves, ℓ ∈ h₁.leaves ++ h₂.leaves
  | _, _, _, .refl _, _ => fun _ h => List.mem_append.mpr (.inr h)
  | _, _, _, .tail s hs, h₂ => fun ℓ hℓ => by
      simp only [DSpine.append, DSpine.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (.inl h)
      · rcases List.mem_append.mp (hs.append_leaves h₂ ℓ h) with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

/-- `.wk` distributed over the steps. -/
def DSpine.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    DSpine R Γ T a b → DSpine R (insertAt d k Γ) (lift k 1 T) (lift k 1 a) (lift k 1 b)
  | _, _, .refl h => .refl (.wk d k h)
  | _, _, .tail s hs => .tail (.wk d k s) (hs.wk d k)

/-- `.wk` distribution preserves the leaves EXACTLY. -/
theorem DSpine.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (hs : DSpine R Γ T a b) → (hs.wk d k).leaves = hs.leaves
  | _, _, .refl _ => rfl
  | _, _, .tail _ hs => by
      simp only [DSpine.wk, DSpine.leaves, DStep.leaves, hs.wk_leaves d k]

/-- `.conv` distributed over the steps (and the terminal typing). -/
def DSpine.conv {Γ : LCtx} {T T' : Expr Nat} (c : EvTc R Γ T T') : {a b : Expr Nat} →
    DSpine R Γ T a b → DSpine R Γ T' a b
  | _, _, .refl h => .refl (.rety h c)
  | _, _, .tail s hs => .tail (.conv s c) (hs.conv c)

/-- `.conv` distribution only repeats the chain's own leaves. -/
theorem DSpine.conv_leaves {Γ : LCtx} {T T' : Expr Nat} (c : EvTc R Γ T T') :
    {a b : Expr Nat} → (hs : DSpine R Γ T a b) →
    ∀ ℓ ∈ (hs.conv c).leaves, ℓ ∈ hs.leaves ++ c.leaves
  | _, _, .refl _ => fun ℓ hℓ => by
      simpa only [DSpine.conv, DSpine.leaves, EvTy.leaves] using hℓ
  | _, _, .tail s hs => fun ℓ hℓ => by
      simp only [DSpine.conv, DSpine.leaves, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr h
      · rcases List.mem_append.mp (hs.conv_leaves c ℓ h) with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

/-- the lazy substitution distributed over the steps (and the terminal typing); the value's
    typing is repeated per step, like `.conv`'s chain. -/
def DSpine.subst0 {Γ : LCtx} {T t v : Expr Nat} (j : Nat) (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) : {a b : Expr Nat} →
    DSpine R Γ T a b → DSpine R (substRemove v j Γ) (instantiate j (lift 0 j v) T)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
  | _, _, .refl h => .refl (.subst0 j h hget hv)
  | _, _, .tail s hs => .tail (.subst0 j s hget hv) (hs.subst0 j hget hv)

theorem DSpine.subst0_leaves {Γ : LCtx} {T t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) : {a b : Expr Nat} →
    (hs : DSpine R Γ T a b) → ∀ ℓ ∈ (hs.subst0 j hget hv).leaves, ℓ ∈ hs.leaves ++ hv.leaves
  | _, _, .refl _ => fun ℓ hℓ => by
      simpa only [DSpine.subst0, DSpine.leaves, EvTy.leaves] using hℓ
  | _, _, .tail s hs => fun ℓ hℓ => by
      simp only [DSpine.subst0, DSpine.leaves, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr h
      · rcases List.mem_append.mp (hs.subst0_leaves j hget hv ℓ h) with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

def DSpine.substLet {Γ : LCtx} {T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) : {a b : Expr Nat} →
    DSpine R Γ T a b → DSpine R (substRemove w j Γ) (instantiate j (lift 0 j w) T)
      (instantiate j (lift 0 j w) a) (instantiate j (lift 0 j w) b)
  | _, _, .refl h => .refl (.substLet j h hget hv)
  | _, _, .tail s hs => .tail (.substLet j s hget hv) (hs.substLet j hget hv)

theorem DSpine.substLet_leaves {Γ : LCtx} {T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) : {a b : Expr Nat} →
    (hs : DSpine R Γ T a b) → ∀ ℓ ∈ (hs.substLet j hget hv).leaves, ℓ ∈ hs.leaves ++ hv.leaves
  | _, _, .refl _ => fun ℓ hℓ => by
      simpa only [DSpine.substLet, DSpine.leaves, EvTy.leaves] using hℓ
  | _, _, .tail s hs => fun ℓ hℓ => by
      simp only [DSpine.substLet, DSpine.leaves, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr h
      · rcases List.mem_append.mp (hs.substLet_leaves j hget hv ℓ h) with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

/-- the derived spine view of a star: transports distributed over the steps. -/
def EvParStar.spine : {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T →
    DSpine R Γ T a b
  | _, _, _, _, .refl h => .refl h
  | _, _, _, _, .tail h hs => .tail (.base h) hs.spine
  | _, _, _, _, .conv hs c => hs.spine.conv c
  | _, _, _, _, .wk d k hs => hs.spine.wk d k
  | _, _, _, _, .trans h₁ h₂ => h₁.spine.append h₂.spine
  | _, _, _, _, .subst0 j hs hget hv => hs.spine.subst0 j hget hv
  | _, _, _, _, .substLet j hs hget hv => hs.spine.substLet j hget hv

/-- the spine view invents no leaf. -/
theorem EvParStar.spine_leaves : {Γ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ a b T) → ∀ ℓ ∈ hs.spine.leaves, ℓ ∈ hs.leaves
  | _, _, _, _, .refl _ => fun _ h => h
  | _, _, _, _, .tail h hs => fun ℓ hℓ => by
      simp only [EvParStar.spine, DSpine.leaves, DStep.leaves, EvParStar.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h' | h'
      · exact .inl h'
      · exact .inr (hs.spine_leaves ℓ h')
  | _, _, _, _, .conv hs c => fun ℓ hℓ => by
      simp only [EvParStar.spine, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (hs.spine.conv_leaves c ℓ hℓ) with h' | h'
      · exact .inl (hs.spine_leaves ℓ h')
      · exact .inr h'
  | _, _, _, _, .wk d k hs => fun ℓ hℓ => by
      simp only [EvParStar.spine, EvParStar.leaves, DSpine.wk_leaves] at hℓ ⊢
      exact hs.spine_leaves ℓ hℓ
  | _, _, _, _, .trans h₁ h₂ => fun ℓ hℓ => by
      simp only [EvParStar.spine, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (h₁.spine.append_leaves h₂.spine ℓ hℓ) with h' | h'
      · exact .inl (h₁.spine_leaves ℓ h')
      · exact .inr (h₂.spine_leaves ℓ h')
  | _, _, _, _, .subst0 j hs hget hv => fun ℓ hℓ => by
      simp only [EvParStar.spine, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (hs.spine.subst0_leaves j hget hv ℓ hℓ) with h' | h'
      · exact .inl (hs.spine_leaves ℓ h')
      · exact .inr h'
  | _, _, _, _, .substLet j hs hget hv => fun ℓ hℓ => by
      simp only [EvParStar.spine, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (hs.spine.substLet_leaves j hget hv ℓ hℓ) with h' | h'
      · exact .inl (hs.spine_leaves ℓ h')
      · exact .inr h'

/-- back to a star, through the star's own `refl` / `trans`. -/
def DSpine.toStar {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} → DSpine R Γ T a b →
    EvParStar R Γ a b T
  | _, _, .refl h => .refl h
  | _, _, .tail s hs => .trans s.star1 hs.toStar

/-- ... inventing no leaf. -/
theorem DSpine.toStar_leaves {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    (hs : DSpine R Γ T a b) → ∀ ℓ ∈ hs.toStar.leaves, ℓ ∈ hs.leaves
  | _, _, .refl _ => fun _ h => h
  | _, _, .tail s hs => fun ℓ hℓ => by
      simp only [DSpine.toStar, DSpine.leaves, EvParStar.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact .inl (s.star1_leaves ℓ h)
      · exact .inr (hs.toStar_leaves ℓ h)

/-! ### the certified 0-or-1 step diamond -/

/-- zero steps (with the endpoint typing) or one transported step. -/
inductive DOpt (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | stay {Γ : LCtx} {b T : Expr Nat} (h : EvTy R Γ b T) : DOpt R Γ b b T
  | step {Γ : LCtx} {b d T : Expr Nat} (s : DStep R Γ b d T) : DOpt R Γ b d T

def DOpt.leaves : {Γ : LCtx} → {b d T : Expr Nat} → DOpt R Γ b d T → List (Jd E n)
  | _, _, _, _, .stay h => h.leaves
  | _, _, _, _, .step s => s.leaves

def DOpt.toSpine : {Γ : LCtx} → {b d T : Expr Nat} → DOpt R Γ b d T → DSpine R Γ T b d
  | _, _, _, _, .stay h => .refl h
  | _, _, _, _, .step s => .tail s (.refl s.rightTy)

theorem DOpt.toSpine_leaves : {Γ : LCtx} → {b d T : Expr Nat} → (o : DOpt R Γ b d T) →
    ∀ ℓ ∈ o.toSpine.leaves, ℓ ∈ o.leaves
  | _, _, _, _, .stay _ => fun _ h => h
  | _, _, _, _, .step s => fun ℓ hℓ => by
      simp only [DOpt.toSpine, DOpt.leaves, DSpine.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with h | h
      · exact h
      · exact s.rightTy_leaves ℓ h

/-- a 0-or-1 step join of `b` and `c`, certified against the input leaves `L`. -/
structure DOptJoin (R : List (Jd E n)) (Γ : LCtx) (b c T : Expr Nat) (L : List (Jd E n)) where
  d : Expr Nat
  left : DOpt R Γ b d T
  right : DOpt R Γ c d T
  sound : ∀ ℓ ∈ left.leaves ++ right.leaves, ∃ ℓ' ∈ L, SubEq ℓ ℓ'

/-- A step solver at one fixed source context, independent of its premise. -/
abbrev DStepDiamondAt (R : List (Jd E n)) (Γ : LCtx) : Type :=
  ∀ {a b c T : Expr Nat}, (s₁ : DStep R Γ a b T) →
    (s₂ : DStep R Γ a c T) → DOptJoin R Γ b c T (s₁.leaves ++ s₂.leaves)

/-- the certified step diamond on transported steps, in a well-formed context. -/
abbrev DStepDiamondWf (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, CtxWfT E n Γ → (s₁ : DStep R Γ a b T) →
    (s₂ : DStep R Γ a c T) → DOptJoin R Γ b c T (s₁.leaves ++ s₂.leaves)

/-- a spine join of `b` and `c`, certified against the input leaves `L`. -/
structure DSpineJoin (R : List (Jd E n)) (Γ : LCtx) (b c T : Expr Nat) (L : List (Jd E n)) where
  d : Expr Nat
  left : DSpine R Γ T b d
  right : DSpine R Γ T c d
  sound : ∀ ℓ ∈ left.leaves ++ right.leaves, ∃ ℓ' ∈ L, SubEq ℓ ℓ'

/-! ### strip and star: structural, no measure -/

section Strip
variable {Γ : LCtx} (S : DStepDiamondAt R Γ) {T : Expr Nat}

/-- the strip lemma: one step against a spine, by recursion on the spine. -/
def dStripAt : {a b c : Expr Nat} → (s : DStep R Γ a b T) → (hs : DSpine R Γ T a c) →
    DSpineJoin R Γ b c T (s.leaves ++ hs.leaves)
  | _, _, _, s, .refl _ =>
      { d := _, left := .refl s.rightTy, right := .tail s (.refl s.rightTy),
        sound := fun ℓ hℓ => by
          simp only [DSpine.leaves, List.mem_append] at hℓ
          refine dSubEq_of_mem (List.mem_append.mpr (.inl ?_))
          rcases hℓ with h | h | h
          · exact s.rightTy_leaves ℓ h
          · exact h
          · exact s.rightTy_leaves ℓ h }
  | _, _, _, s, .tail t rest => by
      obtain ⟨d₁, o₁, o₂, hJ⟩ := S s t
      have h₁ : ∀ ℓ ∈ o₁.toSpine.leaves, ∃ ℓ' ∈ s.leaves ++ (DSpine.tail t rest).leaves,
          SubEq ℓ ℓ' := fun ℓ hℓ => by
        obtain ⟨ℓ', hm, hs⟩ := hJ ℓ (List.mem_append.mpr (.inl (o₁.toSpine_leaves ℓ hℓ)))
        refine ⟨ℓ', ?_, hs⟩
        simp only [DSpine.leaves, List.mem_append] at hm ⊢
        rcases hm with h | h
        · exact .inl h
        · exact .inr (.inl h)
      cases o₂ with
      | stay h =>
          exact
            { d := _
              left := o₁.toSpine.append rest
              right := .refl rest.rightTy
              sound := fun ℓ hℓ => by
                simp only [DSpine.leaves, List.mem_append] at hℓ
                rcases hℓ with hℓ | hℓ
                · rcases List.mem_append.mp (o₁.toSpine.append_leaves rest ℓ hℓ) with h' | h'
                  · exact h₁ ℓ h'
                  · exact dSubEq_of_mem (by
                      simp only [DSpine.leaves, List.mem_append]; exact .inr (.inr h'))
                · exact dSubEq_of_mem (by
                    simp only [DSpine.leaves, List.mem_append]
                    exact .inr (.inr (rest.rightTy_leaves ℓ hℓ))) }
      | step u =>
          let r := dStripAt u rest
          exact
            { d := r.d
              left := o₁.toSpine.append r.left
              right := r.right
              sound := fun ℓ hℓ => by
                have hu : ∀ m ∈ u.leaves ++ rest.leaves,
                    ∃ k ∈ s.leaves ++ (DSpine.tail t rest).leaves, SubEq m k := by
                  intro m hm
                  rcases List.mem_append.mp hm with hm | hm
                  · obtain ⟨k, hk, hs⟩ := hJ m (List.mem_append.mpr (.inr hm))
                    refine ⟨k, ?_, hs⟩
                    simp only [DSpine.leaves, List.mem_append] at hk ⊢
                    rcases hk with h | h
                    · exact .inl h
                    · exact .inr (.inl h)
                  · exact dSubEq_of_mem (by
                      simp only [DSpine.leaves, List.mem_append]; exact .inr (.inr hm))
                rcases List.mem_append.mp hℓ with hℓ | hℓ
                · rcases List.mem_append.mp (o₁.toSpine.append_leaves r.left ℓ hℓ) with h' | h'
                  · exact h₁ ℓ h'
                  · exact dCover_trans r.sound hu ℓ (List.mem_append.mpr (.inl h'))
                · exact dCover_trans r.sound hu ℓ (List.mem_append.mpr (.inr hℓ)) }

/-- the star diamond: recursion on the left spine, the strip lemma at each step. -/
def dStarAt : {a b c : Expr Nat} → (h₁ : DSpine R Γ T a b) → (h₂ : DSpine R Γ T a c) →
    DSpineJoin R Γ b c T (h₁.leaves ++ h₂.leaves)
  | _, _, _, .refl h, h₂ =>
      { d := _, left := h₂, right := .refl h₂.rightTy,
        sound := fun ℓ hℓ => by
          refine dSubEq_of_mem (List.mem_append.mpr (.inr ?_))
          rcases List.mem_append.mp hℓ with h' | h'
          · exact h'
          · exact h₂.rightTy_leaves ℓ h' }
  | _, _, _, .tail s rest, h₂ =>
      let J := dStripAt S s h₂
      let K := dStarAt rest J.left
      { d := K.d, left := K.left, right := J.right.append K.right,
        sound := by
          have hK : ∀ m ∈ rest.leaves ++ J.left.leaves,
              ∃ k ∈ (DSpine.tail s rest).leaves ++ h₂.leaves, SubEq m k := by
            intro m hm
            rcases List.mem_append.mp hm with hm | hm
            · exact dSubEq_of_mem (by
                simp only [DSpine.leaves, List.mem_append]; exact .inl (.inr hm))
            · obtain ⟨k, hk, hs⟩ := J.sound m (List.mem_append.mpr (.inl hm))
              refine ⟨k, ?_, hs⟩
              simp only [DSpine.leaves, List.mem_append] at hk ⊢
              rcases hk with h | h
              · exact .inl (.inl h)
              · exact .inr h
          intro ℓ hℓ
          rcases List.mem_append.mp hℓ with hℓ | hℓ
          · exact dCover_trans K.sound hK ℓ (List.mem_append.mpr (.inl hℓ))
          · rcases List.mem_append.mp (J.right.append_leaves K.right ℓ hℓ) with h' | h'
            · obtain ⟨k, hk, hs⟩ := J.sound ℓ (List.mem_append.mpr (.inr h'))
              refine ⟨k, ?_, hs⟩
              simp only [DSpine.leaves, List.mem_append] at hk ⊢
              rcases hk with h | h
              · exact .inl (.inl h)
              · exact .inr h
            · exact dCover_trans K.sound hK ℓ (List.mem_append.mpr (.inr h')) }

end Strip

/-- The landed strip signature, instantiated at the caller's real premise. -/
def dStripWf (S : DStepDiamondWf R) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {a b c : Expr Nat} (s : DStep R Γ a b T)
    (hs : DSpine R Γ T a c) : DSpineJoin R Γ b c T (s.leaves ++ hs.leaves) :=
  dStripAt (S hΓ) s hs

/-- The landed star signature, using the same fixed-context fold. -/
def dStarWf (S : DStepDiamondWf R) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {a b c : Expr Nat} (h₁ : DSpine R Γ T a b)
    (h₂ : DSpine R Γ T a c) : DSpineJoin R Γ b c T (h₁.leaves ++ h₂.leaves) :=
  dStarAt (S hΓ) h₁ h₂

/-- One source-context star procedure from the shared fold. -/
def dProcAt {Γ : LCtx} (S : DStepDiamondAt R Γ) {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T :=
  let J := dStarAt S h₁.spine h₂.spine
  ⟨J.d, J.left.toStar, J.right.toStar⟩

/-- The shared fold preserves the complete source leaf contract. -/
theorem dContractAt {Γ : LCtx} (S : DStepDiamondAt R Γ) {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    ∀ ℓ ∈ (dProcAt S h₁ h₂).2.1.leaves ++ (dProcAt S h₁ h₂).2.2.leaves,
      ∃ k ∈ h₁.leaves ++ h₂.leaves, SubEq ℓ k := by
  intro ℓ hℓ
  have hm : ℓ ∈ (dStarAt S h₁.spine h₂.spine).left.leaves ++
      (dStarAt S h₁.spine h₂.spine).right.leaves := by
    rcases List.mem_append.mp hℓ with h | h
    · exact List.mem_append.mpr (.inl (DSpine.toStar_leaves _ ℓ h))
    · exact List.mem_append.mpr (.inr (DSpine.toStar_leaves _ ℓ h))
  obtain ⟨k, hk, hs⟩ := (dStarAt S h₁.spine h₂.spine).sound ℓ hm
  refine ⟨k, ?_, hs⟩
  rcases List.mem_append.mp hk with h | h
  · exact List.mem_append.mpr (.inl (h₁.spine_leaves k h))
  · exact List.mem_append.mpr (.inr (h₂.spine_leaves k h))

/-! ### the H-D supplier from a certified step diamond -/

/-- `DProcWf` from a certified step diamond: spine views in, stars out. -/
def dProcWf_of_step (S : DStepDiamondWf R) : DProcWf R := fun hΓ h₁ h₂ =>
  dProcAt (S hΓ) h₁ h₂

/-- ... and its leaf contract. -/
theorem dContractWf_of_step (S : ∀ R : List (Jd E n), DStepDiamondWf R) :
    DContractWf (fun R => dProcWf_of_step (S R)) := by
  intro R Γ a b c T hΓ h₁ h₂
  exact dContractAt (S R hΓ) h₁ h₂

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.DProcWf
#print axioms Rcic.Declarative.F8Measure.DContractWf
#print axioms Rcic.Declarative.F8Measure.dSubEq_trans
#print axioms Rcic.Declarative.F8Measure.dSubEq_of_mem
#print axioms Rcic.Declarative.F8Measure.dCover_trans
#print axioms Rcic.Declarative.F8Measure.EvPar.rightTy
#print axioms Rcic.Declarative.F8Measure.EvPar.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.DeltaPayload.rightTy
#print axioms Rcic.Declarative.F8Measure.DeltaPayload.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.rightTy
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.LamPayload.rightTy
#print axioms Rcic.Declarative.F8Measure.LamPayload.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.AppPayload.rightTy
#print axioms Rcic.Declarative.F8Measure.AppPayload.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.LetEPayload.rightTy
#print axioms Rcic.Declarative.F8Measure.LetEPayload.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.DStep
#print axioms Rcic.Declarative.F8Measure.DStep.leaves
#print axioms Rcic.Declarative.F8Measure.DStep.rightTy
#print axioms Rcic.Declarative.F8Measure.DStep.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.DStep.star1
#print axioms Rcic.Declarative.F8Measure.DStep.star1_leaves
#print axioms Rcic.Declarative.F8Measure.DSpine
#print axioms Rcic.Declarative.F8Measure.DSpine.leaves
#print axioms Rcic.Declarative.F8Measure.DSpine.rightTy
#print axioms Rcic.Declarative.F8Measure.DSpine.rightTy_leaves
#print axioms Rcic.Declarative.F8Measure.DSpine.append
#print axioms Rcic.Declarative.F8Measure.DSpine.append_leaves
#print axioms Rcic.Declarative.F8Measure.DSpine.wk
#print axioms Rcic.Declarative.F8Measure.DSpine.wk_leaves
#print axioms Rcic.Declarative.F8Measure.DSpine.conv
#print axioms Rcic.Declarative.F8Measure.DSpine.conv_leaves
#print axioms Rcic.Declarative.F8Measure.EvParStar.spine
#print axioms Rcic.Declarative.F8Measure.EvParStar.spine_leaves
#print axioms Rcic.Declarative.F8Measure.DSpine.toStar
#print axioms Rcic.Declarative.F8Measure.DSpine.toStar_leaves
#print axioms Rcic.Declarative.F8Measure.DOpt
#print axioms Rcic.Declarative.F8Measure.DOpt.leaves
#print axioms Rcic.Declarative.F8Measure.DOpt.toSpine
#print axioms Rcic.Declarative.F8Measure.DOpt.toSpine_leaves
#print axioms Rcic.Declarative.F8Measure.DOptJoin
#print axioms Rcic.Declarative.F8Measure.DStepDiamondWf
#print axioms Rcic.Declarative.F8Measure.DSpineJoin
#print axioms Rcic.Declarative.F8Measure.dStripWf
#print axioms Rcic.Declarative.F8Measure.dStarWf
#print axioms Rcic.Declarative.F8Measure.dProcWf_of_step
#print axioms Rcic.Declarative.F8Measure.dContractWf_of_step

#print axioms Rcic.Declarative.F8Measure.DStepDiamondAt
#print axioms Rcic.Declarative.F8Measure.dStripAt
#print axioms Rcic.Declarative.F8Measure.dStarAt
#print axioms Rcic.Declarative.F8Measure.dProcAt
#print axioms Rcic.Declarative.F8Measure.dContractAt
