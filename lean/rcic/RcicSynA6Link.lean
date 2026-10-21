import rcic.RcicSynDisplayRoute
import rcic.RcicSynCctx
import rcic.RcicSynBvarView

/-!
# A6 — the forward link decoder: action words, survivors, hits

`BELOWC_A6_LINK_DECODER.md` §2 (ChatGPT J line, docs PR #7450), implemented against
the landed syntactic layer (fable-step ITEM 6, 2026-10-17). `closure_claim = 0`.

The question A6 asks of a paired birth is *why* its two operands are linked. For the
main ordinary class — two actual `bvar` sources whose forward native traces reach one
common context and subject — this module decodes the link constructively, with no
semantic answer and no `Before`:

* `Word d₀ D` — the **forward action word**: the chain of enclosing original
  transport / conversion nodes above a tracked inner node `d₀`, in application order,
  each constructor carrying that node's OWN payload (`wk d c`, `esub`/`lsub` with
  `hget`/`hv`/`hvT`, `linst ls`, `ewk`, `cctx hA`, `conv hc`). Nothing is stored about
  indices: `Word.idx` computes the tracked index and `Word.survives` says the word has
  no substitution hit on it (§2.2's table, one row per constructor).
* `Word.subject_eq` — a surviving word from a `bvar` node ends at the subject
  `bvar (w.idx i₀)` (`lift_bvar_lt/ge`, `instantiate_bvar_lt/gt`, `instantiateLevels`
  fixes a `bvar`).
* `Word.survivor` — the **survivor theorem** (§2.3): a surviving word determines a
  successful final lookup `lookupType Γ* j = some B` (the four landed lookup
  commutations `lookupType_insertAt_*` / `lookupType_substRemove_*` /
  `lookupType_instLvlsCtx_some`, plus the two `cctx` rows) and the **terminal domain
  representative** `J : TyP E n Γ* B (sort u)`: the original regularity view `H`
  pushed through its full continuation, except at an *affected* zero-`cctx`, where the
  representative is replaced by the right endpoint of that bridge under its lift
  (`wk₀ hA.dr`) — exactly the spec's terminal representative.
* `Word.bridges` / `Word.bridges_at` — every nonidentity segment of the forward domain
  chain is an original `cctx` bridge at index `0`; `bridges` lists them with their
  forest address relative to the outer node and `bridges_at` proves each address reads
  exactly that bridge (`RawForest.at`). `Bridge.lifted` is the lifted segment
  `lift 0 1 A ≡ lift 0 1 A' : sort u` at the converted context (`CvP.wk … 0 hA`).
* `terminalPair` — the **pair theorem**: two survivors reaching the same `Γ*`, `e*`
  have `j_L = j_R` (`Expr.bvar.inj` on the subject) and `B_L = B_R` (lookup
  determinism, no inversion of any substitution); the terminal representatives `J_L`,
  `J_R` then type ONE subject `B` at ONE context — the C-comparison operands.
* `hitPacket` / `hitEsub` / `hitLsub` — the **hit theorem** (§2.4): at an `esub`/`lsub`
  hit the original `V`/`W` packet is selected with the two native equations
  (`instantiate_bvar_eq`, `instantiate_lift_cancel`) and the three direct one-hit
  operand pairs are emitted — qValue (the hit node vs `V`, subject `lift 0 j v`), qReg
  (`V.reg.2` vs `W`), qType (the source domain view through this node's view vs `W`;
  the domain never contains the hit variable, so this is the P5 cancel, not a
  reapplication of the hit). `V` is entered as it is, at the packet's target context.

What is NOT here (recorded, not claimed): that every intended paired A6 request is
emitted and owns these operands (issuance lives in the `Demand`/`Issues` grammar), the
semantic C/Mixed answers, and the ownership/payment ledger (`RcicSynA6Owner` recovers
the owners). Residues carried: W-A6-SOURCE-VIEW-ISSUANCE, W-A6-NESTED-HE-QTYPE.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 — the forward action word over an actual derivation -/

/-- **The forward action word.** `Word d₀ D`: the derivation `D` is built from the
    tracked inner node `d₀` by exactly this chain of enclosing original nodes, innermost
    first. Every constructor is the corresponding `TyP` constructor's own payload
    (`d`/`c`, `t`/`v`/`j` + `hget`/`hv`/`hvT`, `ls` + bounds, `hext`, `hA`, `hc`) — a
    position in one actual derivation, not an abstract operation code. -/
inductive Word {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    (d₀ : TyP E₀ n₀ Γ₀ e₀ T₀) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → TyP E n Γ e T → Type where
  | nil : Word d₀ d₀
  | wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E n Γ e T}
      (w : Word d₀ D) (d : LocalDecl) (c : Nat) : Word d₀ (.wk E n Γ e T d c D)
  | esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {u : Level}
      {D : TyP E n Γ e T} (t v : Expr Nat) (j : Nat) (w : Word d₀ D)
      (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      Word d₀ (.esub E n Γ e T t v j u D hget hv hvT)
  | lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {u : Level}
      {D : TyP E n Γ e T} (t v : Expr Nat) (j : Nat) (w : Word d₀ D)
      (hget : Γ[j]? = some (.letBinding t v))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      Word d₀ (.lsub E n Γ e T t v j u D hget hv hvT)
  | linst {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E a Γ e T}
      (ls : List Level) (w : Word d₀ D)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
      Word d₀ (.linst E a n Γ e T ls hls hlen D)
  | ewk {E₁ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E₁ n Γ e T}
      (w : Word d₀ D) (hext : EnvExt E₁ E) : Word d₀ (.ewk E₁ E n Γ e T hext D)
  | cctx {E : ResolvedEnv} {n : Nat} {Γt : LCtx} {e T : Expr Nat} {u : Level}
      (A A' : Expr Nat) {D : TyP E n (.assumption A :: Γt) e T} (w : Word d₀ D)
      (hA : CvP E n Γt A A' (.sort u)) : Word d₀ (.cctx E n Γt e T A A' u D hA)
  | conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
      {D : TyP E n Γ e A} (w : Word d₀ D) (hc : CvP E n Γ A B (.sort u)) :
      Word d₀ (.conv E n Γ e A B u D hc)

/-- §2.2's index column: the tracked variable's index after the word, starting from
    `i₀` at the inner node. `wk d c`: `i` below `c`, else `i + 1`; `esub`/`lsub` at
    `j`: `i` below `j`, `i - 1` above it (at `i = j` the word has a hit and `idx` is not
    consulted — `survives` is false there); the rest keep the index. -/
def Word.idx {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} (i₀ : Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    Word d₀ D → Nat
  | _, _, _, _, _, _, .nil => i₀
  | _, _, _, _, _, _, .wk w _ c =>
      if Word.idx i₀ w < c then Word.idx i₀ w else Word.idx i₀ w + 1
  | _, _, _, _, _, _, .esub _ _ j w _ _ _ =>
      if Word.idx i₀ w < j then Word.idx i₀ w else Word.idx i₀ w - 1
  | _, _, _, _, _, _, .lsub _ _ j w _ _ _ =>
      if Word.idx i₀ w < j then Word.idx i₀ w else Word.idx i₀ w - 1
  | _, _, _, _, _, _, .linst _ w _ _ => Word.idx i₀ w
  | _, _, _, _, _, _, .ewk w _ => Word.idx i₀ w
  | _, _, _, _, _, _, .cctx _ _ w _ => Word.idx i₀ w
  | _, _, _, _, _, _, .conv w _ => Word.idx i₀ w

/-- The word has no substitution hit on the tracked variable: at every `esub`/`lsub`
    the current index differs from the cutoff `j`. -/
def Word.survives {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} (i₀ : Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    Word d₀ D → Prop
  | _, _, _, _, _, _, .nil => True
  | _, _, _, _, _, _, .wk w _ _ => Word.survives i₀ w
  | _, _, _, _, _, _, .esub _ _ j w _ _ _ => Word.survives i₀ w ∧ Word.idx i₀ w ≠ j
  | _, _, _, _, _, _, .lsub _ _ j w _ _ _ => Word.survives i₀ w ∧ Word.idx i₀ w ≠ j
  | _, _, _, _, _, _, .linst _ w _ _ => Word.survives i₀ w
  | _, _, _, _, _, _, .ewk w _ => Word.survives i₀ w
  | _, _, _, _, _, _, .cctx _ _ w _ => Word.survives i₀ w
  | _, _, _, _, _, _, .conv w _ => Word.survives i₀ w

/-- A surviving word from a `bvar i₀` node ends at the subject `bvar (w.idx i₀)`: the
    subject injection is forward, one landed index lemma per row. -/
theorem Word.subject_eq {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} {i₀ : Nat} (he₀ : e₀ = .bvar i₀) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    (w : Word d₀ D) → Word.survives i₀ w → e = .bvar (Word.idx i₀ w)
  | _, _, _, _, _, _, .nil, _ => he₀
  | _, _, _, _, _, _, .wk w _ c, hs => by
      have ih := Word.subject_eq he₀ w hs
      simp only [Word.idx]
      refine (congrArg (lift c 1) ih).trans ?_
      by_cases h : Word.idx i₀ w < c
      · rw [if_pos h, lift_bvar_lt h]
      · rw [if_neg h, lift_bvar_ge (Nat.le_of_not_lt h)]
  | _, _, _, _, _, _, .esub _ v j w _ _ _, hs => by
      have ih := Word.subject_eq he₀ w hs.1
      simp only [Word.idx]
      refine (congrArg (instantiate j (lift 0 j v)) ih).trans ?_
      by_cases h : Word.idx i₀ w < j
      · rw [if_pos h, instantiate_bvar_lt h]
      · have hgt : j < Word.idx i₀ w :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm hs.2)
        rw [if_neg h, instantiate_bvar_gt hgt]
  | _, _, _, _, _, _, .lsub _ v j w _ _ _, hs => by
      have ih := Word.subject_eq he₀ w hs.1
      simp only [Word.idx]
      refine (congrArg (instantiate j (lift 0 j v)) ih).trans ?_
      by_cases h : Word.idx i₀ w < j
      · rw [if_pos h, instantiate_bvar_lt h]
      · have hgt : j < Word.idx i₀ w :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm hs.2)
        rw [if_neg h, instantiate_bvar_gt hgt]
  | _, _, _, _, _, _, .linst ls w _ _, hs => by
      have ih := Word.subject_eq he₀ w hs
      simp only [Word.idx]
      exact (congrArg (instantiateLevels ls) ih).trans rfl
  | _, _, _, _, _, _, .ewk w _, hs => Word.subject_eq he₀ w hs
  | _, _, _, _, _, _, .cctx _ _ w _, hs => Word.subject_eq he₀ w hs
  | _, _, _, _, _, _, .conv w _, hs => Word.subject_eq he₀ w hs

/-! ## §2 — the survivor theorem: final lookup and terminal representative -/

/-- A positive index reads the tail on both sides of a converted innermost binder:
    the lookup is unchanged by `cctx` there. -/
theorem lookupType_cctx_pos {A A' : Expr Nat} {Γt : LCtx} {i : Nat} {B : Expr Nat}
    (hi : i ≠ 0) (h : lookupType (.assumption A :: Γt) i = some B) :
    lookupType (.assumption A' :: Γt) i = some B := by
  cases i with
  | zero => exact absurd rfl hi
  | succ k =>
      rw [lookupType_cons_succ] at h ⊢
      exact h

/-- What a surviving trace determines at its end context: the final index `j` (the
    structure's index), the successful final lookup `dom`, and the terminal domain
    representative `rep : TyP E n Γ dom (sort u)`. -/
structure Survivor (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (j : Nat) : Type where
  dom : Expr Nat
  hlook : lookupType Γ j = some dom
  u : Level
  rep : TyP E n Γ dom (.sort u)

/-- **The survivor theorem** (§2.3). From the inner node's lookup `hl₀` and its
    regularity view `H : TyP E₀ n₀ Γ₀ A₀ (sort u₀)`, a surviving word yields the final
    lookup and the terminal representative: `wk`/`esub`/`lsub`/`linst`/`ewk` push the
    representative through the node's own transport (the lookup commutes by the landed
    lemmas); `conv` and a positive `cctx` keep the lookup (`lookupType_cons_succ` on
    both sides of the converted binder); an **affected zero `cctx`** replaces the
    representative by the bridge's right endpoint under its lift, `wk₀ hA.dr`, whose
    subject `lift 0 1 A'` IS the new lookup at index `0`. -/
def Word.survivor {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level}
    (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀)) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    (w : Word d₀ D) → Word.survives i₀ w → Survivor E n Γ (Word.idx i₀ w)
  | _, _, _, _, _, _, .nil, _ => ⟨A₀, hl₀, u₀, H⟩
  | _, _, _, _, _, _, .wk w d c, hs =>
      let s := Word.survivor hl₀ H w hs
      if h : Word.idx i₀ w < c then
        ⟨lift c 1 s.dom,
         by simp only [Word.idx]; rw [if_pos h]; exact lookupType_insertAt_lt d h s.hlook,
         s.u, .wk _ _ _ _ _ d c s.rep⟩
      else
        ⟨lift c 1 s.dom,
         by
           simp only [Word.idx]
           rw [if_neg h]
           exact lookupType_insertAt_ge d (Nat.le_of_not_lt h) s.hlook,
         s.u, .wk _ _ _ _ _ d c s.rep⟩
  | _, _, _, _, _, _, .esub t v j w hget hv hvT, hs =>
      let s := Word.survivor hl₀ H w hs.1
      if h : Word.idx i₀ w < j then
        ⟨instantiate j (lift 0 j v) s.dom,
         by simp only [Word.idx]; rw [if_pos h]; exact lookupType_substRemove_lt h s.hlook,
         s.u, .esub _ _ _ _ _ t v j _ s.rep hget hv hvT⟩
      else
        have hgt : j < Word.idx i₀ w :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm hs.2)
        ⟨instantiate j (lift 0 j v) s.dom,
         by simp only [Word.idx]; rw [if_neg h]; exact lookupType_substRemove_gt hgt s.hlook,
         s.u, .esub _ _ _ _ _ t v j _ s.rep hget hv hvT⟩
  | _, _, _, _, _, _, .lsub t v j w hget hv hvT, hs =>
      let s := Word.survivor hl₀ H w hs.1
      if h : Word.idx i₀ w < j then
        ⟨instantiate j (lift 0 j v) s.dom,
         by simp only [Word.idx]; rw [if_pos h]; exact lookupType_substRemove_lt h s.hlook,
         s.u, .lsub _ _ _ _ _ t v j _ s.rep hget hv hvT⟩
      else
        have hgt : j < Word.idx i₀ w :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm hs.2)
        ⟨instantiate j (lift 0 j v) s.dom,
         by simp only [Word.idx]; rw [if_neg h]; exact lookupType_substRemove_gt hgt s.hlook,
         s.u, .lsub _ _ _ _ _ t v j _ s.rep hget hv hvT⟩
  | _, _, _, _, _, _, .linst ls w hls hlen, hs =>
      let s := Word.survivor hl₀ H w hs
      ⟨instantiateLevels ls s.dom,
       by simp only [Word.idx]; exact lookupType_instLvlsCtx_some ls s.hlook,
       instLevel ls s.u, .linst _ _ _ _ _ _ ls hls hlen s.rep⟩
  | _, _, _, _, _, _, .ewk w hext, hs =>
      let s := Word.survivor hl₀ H w hs
      ⟨s.dom, by simp only [Word.idx]; exact s.hlook, s.u, .ewk _ _ _ _ _ _ hext s.rep⟩
  | _, _, _, _, _, _, .cctx A A' w hA, hs =>
      let s := Word.survivor hl₀ H w hs
      if h : Word.idx i₀ w = 0 then
        ⟨lift 0 1 A',
         by simp only [Word.idx]; rw [h]; rfl,
         _, (TyP.wk _ _ _ _ _ (.assumption A') 0 hA.dr :
              TyP _ _ (.assumption A' :: _) (lift 0 1 A') (.sort _))⟩
      else
        ⟨s.dom,
         by simp only [Word.idx]; exact lookupType_cctx_pos h s.hlook,
         s.u, .cctx _ _ _ _ _ A A' _ s.rep hA⟩
  | _, _, _, _, _, _, .conv w _, hs =>
      let s := Word.survivor hl₀ H w hs
      ⟨s.dom, by simp only [Word.idx]; exact s.hlook, s.u, s.rep⟩

/-! ## §3 — the nonidentity segments: original `cctx` bridges and their addresses -/

/-- A nonidentity segment of the forward domain chain: an original `cctx` bridge
    `hA : A ≡ A' : sort u` crossed while the tracked variable sat at index `0`, with
    its forest address `addr` relative to the outer node of the word. -/
structure Bridge : Type where
  {E : ResolvedEnv} {n : Nat} {Γt : LCtx} {A A' : Expr Nat} {u : Level}
  hA : CvP E n Γt A A' (.sort u)
  addr : List Nat

/-- The lifted segment the chain actually uses: the bridge weakened under the converted
    binder, `lift 0 1 A ≡ lift 0 1 A' : sort u` at `A' :: Γt` — its left endpoint is the
    old lookup, its right endpoint the new one; its middle is reflexive on the
    bridge's own recorded sort. -/
def Bridge.lifted (b : Bridge) :
    CvP b.E b.n (.assumption b.A' :: b.Γt) (lift 0 1 b.A) (lift 0 1 b.A') (.sort b.u) :=
  CvP.wk _ _ _ _ _ _ (.assumption b.A') 0 b.hA

/-- One enclosing node up: the inner derivation is child `0` of every transport /
    conversion node, so every recorded address gains a leading `0`. -/
def Bridge.under (b : Bridge) : Bridge := { b with addr := 0 :: b.addr }

/-- The bridges of a word, innermost first, with their addresses relative to the
    outer node: a `cctx` at tracked index `0` contributes its own `hA` (child `1` of
    the `cctx` node); every other node only deepens the addresses below it. -/
def Word.bridges {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} (i₀ : Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    Word d₀ D → List Bridge
  | _, _, _, _, _, _, .nil => []
  | _, _, _, _, _, _, .wk w _ _ => (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .esub _ _ _ w _ _ _ => (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .lsub _ _ _ w _ _ _ => (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .linst _ w _ _ => (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .ewk w _ => (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .cctx _ _ w hA =>
      (if Word.idx i₀ w = 0 then [⟨hA, [1]⟩] else []) ++ (Word.bridges i₀ w).map Bridge.under
  | _, _, _, _, _, _, .conv w _ => (Word.bridges i₀ w).map Bridge.under

/-! The inner derivation is child `0` of every transport / conversion node and the
`cctx` bridge is child `1`: one definitional address lemma per constructor. -/

theorem at_wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {d : LocalDecl} {c : Nat}
    {D : TyP E n Γ e T} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.wk E n Γ e T d c D))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e T} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.esub E n Γ e T t v j u D hget hv hvT))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e T} {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.lsub E n Γ e T t v j u D hget hv hvT))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_linst {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e T : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a} {D : TyP E a Γ e T} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.linst E a n Γ e T ls hls hlen D))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_ewk {E₁ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {hext : EnvExt E₁ E}
    {D : TyP E₁ n Γ e T} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.ewk E₁ E n Γ e T hext D))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_cctx {E : ResolvedEnv} {n : Nat} {Γt : LCtx} {e T A A' : Expr Nat} {u : Level}
    {D : TyP E n (.assumption A :: Γt) e T} {hA : CvP E n Γt A A' (.sort u)} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.cctx E n Γt e T A A' u D hA))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

theorem at_cctx_bridge {E : ResolvedEnv} {n : Nat} {Γt : LCtx} {e T A A' : Expr Nat} {u : Level}
    {D : TyP E n (.assumption A :: Γt) e T} {hA : CvP E n Γt A A' (.sort u)} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.cctx E n Γt e T A A' u D hA))).at (1 :: p) =
      (RawForest.cv hA.toCvNode).at p := rfl

theorem at_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    {D : TyP E n Γ e A} {hc : CvP E n Γ A B (.sort u)} (p : List Nat) :
    (RawForest.ty (TyP.toTyNode (.conv E n Γ e A B u D hc))).at (0 :: p) =
      (RawForest.ty D.toTyNode).at p := rfl

/-- **The occurrence theorem**: every recorded bridge address, read from the outer
    node's forest image, is exactly that bridge's node. -/
theorem Word.bridges_at {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} (i₀ : Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → {D : TyP E n Γ e T} →
    (w : Word d₀ D) → ∀ b ∈ Word.bridges i₀ w,
      (RawForest.ty D.toTyNode).at b.addr = some (.cv b.hA.toCvNode)
  | _, _, _, _, _, _, .nil, b, hb => by simp [Word.bridges] at hb
  | _, _, _, _, _, _, .wk w d c, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_wk]
      exact ih
  | _, _, _, _, _, _, .esub _ _ _ w _ _ _, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_esub]
      exact ih
  | _, _, _, _, _, _, .lsub _ _ _ w _ _ _, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_lsub]
      exact ih
  | _, _, _, _, _, _, .linst _ w _ _, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_linst]
      exact ih
  | _, _, _, _, _, _, .ewk w _, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_ewk]
      exact ih
  | _, _, _, _, _, _, .cctx _ _ w hA, b, hb => by
      simp only [Word.bridges, List.mem_append, List.mem_map] at hb
      rcases hb with hb | ⟨b', hb', rfl⟩
      · split at hb
        · simp only [List.mem_singleton] at hb
          subst hb
          exact at_cctx_bridge []
        · simp at hb
      · have ih := Word.bridges_at i₀ w b' hb'
        simp only [Bridge.under]
        rw [at_cctx]
        exact ih
  | _, _, _, _, _, _, .conv w _, b, hb => by
      simp only [Word.bridges, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have ih := Word.bridges_at i₀ w b' hb'
      simp only [Bridge.under]
      rw [at_conv]
      exact ih

/-! ## §4 — the pair theorem: two survivors at one subject -/

/-- Two surviving words ending at the SAME subject have the same final index: the
    subject injection is forward on both sides, then `Expr.bvar.inj`. -/
theorem Word.idx_eq_of_subject
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat} {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀}
    {i₀ : Nat} (he₀ : e₀ = .bvar i₀)
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx} {e₀' T₀' : Expr Nat}
    {d₀' : TyP E₀' n₀' Γ₀' e₀' T₀'} {i₀' : Nat} (he₀' : e₀' = .bvar i₀')
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e TL TR : Expr Nat}
    {DL : TyP E n Γ e TL} {DR : TyP E n Γ e TR}
    (wL : Word d₀ DL) (hL : Word.survives i₀ wL)
    (wR : Word d₀' DR) (hR : Word.survives i₀' wR) :
    Word.idx i₀ wL = Word.idx i₀' wR :=
  Expr.bvar.inj ((Word.subject_eq he₀ wL hL).symm.trans (Word.subject_eq he₀' wR hR))

/-- The C-comparison operands of a common-target pair: one subject `B` (the common
    final lookup) typed by both terminal representatives at one context. -/
structure TerminalPair (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Type where
  j : Nat
  B : Expr Nat
  hlook : lookupType Γ j = some B
  uL : Level
  uR : Level
  JL : TyP E n Γ B (.sort uL)
  JR : TyP E n Γ B (.sort uR)

/-- **The pair theorem** (§2.3). Two survivors reaching the same `Γ*`, `e*`: equal final
    indices, equal final lookups (deterministic lookup; no substitution is inverted),
    and the two terminal representatives as a same-subject, same-context pair. -/
def terminalPair
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat} {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀}
    {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level} (he₀ : e₀ = .bvar i₀)
    (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀))
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx} {e₀' T₀' : Expr Nat}
    {d₀' : TyP E₀' n₀' Γ₀' e₀' T₀'} {i₀' : Nat} {A₀' : Expr Nat} {u₀' : Level}
    (he₀' : e₀' = .bvar i₀') (hl₀' : lookupType Γ₀' i₀' = some A₀')
    (H' : TyP E₀' n₀' Γ₀' A₀' (.sort u₀'))
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e TL TR : Expr Nat}
    {DL : TyP E n Γ e TL} {DR : TyP E n Γ e TR}
    (wL : Word d₀ DL) (hL : Word.survives i₀ wL)
    (wR : Word d₀' DR) (hR : Word.survives i₀' wR) : TerminalPair E n Γ :=
  let sL := Word.survivor hl₀ H wL hL
  let sR := Word.survivor hl₀' H' wR hR
  have hj : Word.idx i₀ wL = Word.idx i₀' wR := Word.idx_eq_of_subject he₀ he₀' wL hL wR hR
  have hlL : lookupType Γ (Word.idx i₀' wR) = some sL.dom := by rw [← hj]; exact sL.hlook
  have hB : sL.dom = sR.dom := Option.some.inj (hlL.symm.trans sR.hlook)
  ⟨Word.idx i₀ wL, sL.dom, sL.hlook, sL.u, sR.u, sL.rep, by rw [hB]; exact sR.rep⟩

/-- The pair's subject is the common lookup read on either side. -/
theorem terminalPair_dom_left
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat} {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀}
    {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level} (he₀ : e₀ = .bvar i₀)
    (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀))
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx} {e₀' T₀' : Expr Nat}
    {d₀' : TyP E₀' n₀' Γ₀' e₀' T₀'} {i₀' : Nat} {A₀' : Expr Nat} {u₀' : Level}
    (he₀' : e₀' = .bvar i₀') (hl₀' : lookupType Γ₀' i₀' = some A₀')
    (H' : TyP E₀' n₀' Γ₀' A₀' (.sort u₀'))
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e TL TR : Expr Nat}
    {DL : TyP E n Γ e TL} {DR : TyP E n Γ e TR}
    (wL : Word d₀ DL) (hL : Word.survives i₀ wL)
    (wR : Word d₀' DR) (hR : Word.survives i₀' wR) :
    (terminalPair he₀ hl₀ H he₀' hl₀' H' wL hL wR hR).B = (Word.survivor hl₀ H wL hL).dom :=
  rfl

/-! ## §5 — the hit theorem: the original replacement packet -/

/-- A real entry read gives the lookup: an `assumption t` at `j` looks up as
    `lift 0 (j+1) t`. -/
theorem lookupType_of_getElem_assumption {Γ : LCtx} {j : Nat} {t : Expr Nat}
    (h : Γ[j]? = some (.assumption t)) : lookupType Γ j = some (lift 0 (j+1) t) := by
  unfold lookupType
  rw [List.get?_eq_getElem?, h]

/-- A real entry read gives the lookup: a `letBinding t v` at `j` looks up as
    `lift 0 (j+1) t`. -/
theorem lookupType_of_getElem_letBinding {Γ : LCtx} {j : Nat} {t v : Expr Nat}
    (h : Γ[j]? = some (.letBinding t v)) : lookupType Γ j = some (lift 0 (j+1) t) := by
  unfold lookupType
  rw [List.get?_eq_getElem?, h]

/-- The second native hit equation: instantiating at `j` inside the gap `lift 0 (j+1)`
    opened consumes one unit of the gap (`instantiate_lift_cancel`, P5); the replacement
    is never consulted. -/
theorem instantiate_lift_succ_cancel (j : Nat) (r t : Expr Nat) :
    instantiate j r (lift 0 (j+1) t) = lift 0 j t := by
  rw [instantiate_lift_cancel (j+1) 0 j r (Nat.zero_le j) (by omega), Nat.add_sub_cancel]

/-- §2.4's selected packet at a hit of `esub`/`lsub` at `j`: the node's own `V`/`W`
    (already at the target context, lifted by `j`), the lookup the hit replaces, and
    the two native equations. -/
structure HitPacket (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (j : Nat) (t v : Expr Nat) :
    Type where
  u : Level
  V : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  W : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)
  hlook : lookupType Γ j = some (lift 0 (j+1) t)
  eqSubj : instantiate j (lift 0 j v) (.bvar j) = lift 0 j v
  eqDom : instantiate j (lift 0 j v) (lift 0 (j+1) t) = lift 0 j t

/-- The packet of an `esub` node: read off its fields. -/
def hitPacket {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat} {u : Level}
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) : HitPacket E n Γ j t v :=
  ⟨u, hv, hvT, lookupType_of_getElem_assumption hget, instantiate_bvar_eq j _,
   instantiate_lift_succ_cancel j _ t⟩

/-- The packet of an `lsub` node: read off its fields. -/
def hitPacketLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat} {u : Level}
    (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) : HitPacket E n Γ j t v :=
  ⟨u, hv, hvT, lookupType_of_getElem_letBinding hget, instantiate_bvar_eq j _,
   instantiate_lift_succ_cancel j _ t⟩

/-- The three direct one-hit operand pairs at the packet's target context `Γ'`, on the
    replacement `vj = lift 0 j v` and its type `tj = lift 0 j t`:
    qValue `X` vs `V` (same subject `vj`), qReg `Vreg = V.reg.2` vs `W` (same subject
    `tj`), qType `J` (the source domain view through the hit node's view) vs `W`. -/
structure HitOperands (E : ResolvedEnv) (n : Nat) (Γ' : LCtx) (vj tj : Expr Nat) : Type where
  {TX : Expr Nat}
  X : TyP E n Γ' vj TX
  V : TyP E n Γ' vj tj
  {uW : Level}
  W : TyP E n Γ' tj (.sort uW)
  {uV : Level}
  Vreg : TyP E n Γ' tj (.sort uV)
  {uJ : Level}
  J : TyP E n Γ' tj (.sort uJ)

/-- The operands from the hit node `X'` (subject still written as the instantiated
    original subject) and the pushed source view `J'`: both subjects are rewritten by
    the native equations only. -/
def hitOperandsOf {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T t v : Expr Nat} {j : Nat}
    {uJ : Level} {dom : Expr Nat}
    (he : e = .bvar j) (hdom : dom = lift 0 (j+1) t)
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    {uW : Level} (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort uW))
    (X' : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) e)
      (instantiate j (lift 0 j v) T))
    (J' : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) dom) (.sort uJ)) :
    HitOperands E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
  have X : TyP E n (substRemove v j Γ) (lift 0 j v) (instantiate j (lift 0 j v) T) := by
    rw [he, instantiate_bvar_eq] at X'
    exact X'
  have J : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort uJ) := by
    rw [hdom, instantiate_lift_succ_cancel] at J'
    exact J'
  ⟨X, hv, hvT, hv.reg.2, J⟩

/-- **The hit theorem** at an `esub` node (§2.4). A surviving word `w` from a `bvar`
    node whose tracked index at the node equals the cutoff `j` has hit the substituted
    entry: the packet is the node's own `hv`/`hvT`, the replaced lookup is the
    survivor's final lookup, and the operands are emitted — `X` is the node itself,
    `J` is the terminal representative pushed through the node's own `esub` (the P5
    cancel: the domain never contains the hit variable). -/
def Word.hitEsub {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level}
    (he₀ : e₀ = .bvar i₀) (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀))
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E n Γ e T}
    (w : Word d₀ D) (hs : Word.survives i₀ w)
    {t v : Expr Nat} {j : Nat} {u : Level} (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hidx : Word.idx i₀ w = j) :
    HitPacket E n Γ j t v × HitOperands E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
  let s := Word.survivor hl₀ H w hs
  have he : e = .bvar j := by rw [Word.subject_eq he₀ w hs, hidx]
  have hlj : lookupType Γ (Word.idx i₀ w) = some (lift 0 (j+1) t) := by
    rw [hidx]
    exact lookupType_of_getElem_assumption hget
  have hdom : s.dom = lift 0 (j+1) t := Option.some.inj (s.hlook.symm.trans hlj)
  ⟨hitPacket hget hv hvT,
   hitOperandsOf he hdom hv hvT (TyP.esub E n Γ e T t v j u D hget hv hvT)
     (TyP.esub E n Γ s.dom (.sort s.u) t v j u s.rep hget hv hvT)⟩

/-- **The hit theorem** at an `lsub` node (§2.4), the let-binding form. -/
def Word.hitLsub {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level}
    (he₀ : e₀ = .bvar i₀) (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀))
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E n Γ e T}
    (w : Word d₀ D) (hs : Word.survives i₀ w)
    {t v : Expr Nat} {j : Nat} {u : Level} (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hidx : Word.idx i₀ w = j) :
    HitPacket E n Γ j t v × HitOperands E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
  let s := Word.survivor hl₀ H w hs
  have he : e = .bvar j := by rw [Word.subject_eq he₀ w hs, hidx]
  have hlj : lookupType Γ (Word.idx i₀ w) = some (lift 0 (j+1) t) := by
    rw [hidx]
    exact lookupType_of_getElem_letBinding hget
  have hdom : s.dom = lift 0 (j+1) t := Option.some.inj (s.hlook.symm.trans hlj)
  ⟨hitPacketLet hget hv hvT,
   hitOperandsOf he hdom hv hvT (TyP.lsub E n Γ e T t v j u D hget hv hvT)
     (TyP.lsub E n Γ s.dom (.sort s.u) t v j u s.rep hget hv hvT)⟩

/-- The emitted qValue operand of an `esub` hit IS the node (its subject rewritten by
    the first native equation only): the hit is never reapplied. -/
theorem hitEsub_packet_V {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d₀ : TyP E₀ n₀ Γ₀ e₀ T₀} {i₀ : Nat} {A₀ : Expr Nat} {u₀ : Level}
    (he₀ : e₀ = .bvar i₀) (hl₀ : lookupType Γ₀ i₀ = some A₀) (H : TyP E₀ n₀ Γ₀ A₀ (.sort u₀))
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {D : TyP E n Γ e T}
    (w : Word d₀ D) (hs : Word.survives i₀ w)
    {t v : Expr Nat} {j : Nat} {u : Level} (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hidx : Word.idx i₀ w = j) :
    (Word.hitEsub he₀ hl₀ H w hs hget hv hvT hidx).1.V = hv ∧
    (Word.hitEsub he₀ hl₀ H w hs hget hv hvT hidx).2.V = hv :=
  ⟨rfl, rfl⟩

end Rcic.Syn
