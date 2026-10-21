import rcic.RcicConvPlus
import rcic.RcicSynE
import rcic.RcicERPiSlot
import rcic.RcicERLocalize

/-!
# Syntactic sortRow, build step 3c — derivation-relative erasure

`research/rcic/semantic/S0_SORTROW_SYNTACTIC.md` §2.1 and §3, and
`S3_ES_ARMS.md` §6. `TyP.eps` sends an enriched typing to an erased term `ETm`.

The proof-bit is **head-determined**, read off the derivation, not off `TyP.reg`.
`reg` follows the ascribed type, so a `conv` node would make erasure depend on the
converted type. Two typings of one sort — the canonical `sort` node and a `conv` that
retypes it at a `Prop` — would then erase to `sort l` and to `★`, and `★` and `sort l`
are both E-normal, so CL would fail. Following the inner derivation at `conv` keeps
erasure type-independent; PB is what later ties it to the ascribed sort (S0 §7.2).

What the head reads:
* `sort` and `pi` are never proofs. A `pi` keeps its domain and extends the context
  for the codomain by `drop` when the domain sort is `eqN` 0, by `keep` otherwise.
* `lam` deletes a proof domain (`drop`) and deletes the `λ` itself when the body is a
  proof. A relevant domain is `keep`, and the domain expression is not stored (S0 §2.1).
* `app` deletes a proof argument. A proof function erases to `★`, so the application does
  too.
* `letE` inlines a relevant value and drops a proof value. There is no `letE` in `ETm`.
* `bvar` is `★` when its recorded binder sort is `eqN` 0; otherwise `resolve` reads the
  erased context (a relevant assumption is a shifted index, a let is the inlined value).
* `const` is `★` when its recorded type sort is `eqN` 0.
* `lit` follows `natExpand`. `ewk` and `cctx` do not change the term. `cctx`'s two
  domains are converted at one sort, so the binder bit agrees and the same `ρ` is used.
* `wk` and `esub` are the O5 renaming: a `drop`/`inline` binder takes no erased slot, a
  `keep` does. `linst` recomputes bits under `instLevel`, because a bit is not stable
  under level instantiation (`S1` §3.4).

`CtxP.disp` builds `ρ` for a whole context, inlining let values. ES itself (the 18 arms,
by `WellFounded.fix` on `lexDM_wf`) is the next carrier. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the erased context (O5's index map) -/

/-- What one source binder becomes in the erased term. `keep` is a relevant assumption
    (it occupies an erased de Bruijn slot). `drop` is a proof assumption (no slot).
    `inline v` is a let, already erased in the context outside this binder. -/
inductive Disp : Type
  | keep
  | drop
  | inline : ETm → Disp
  deriving DecidableEq

/-- How many erased slots a context prefix occupies. -/
def countKeep : List Disp → Nat
  | [] => 0
  | .keep :: ρ => countKeep ρ + 1
  | .drop :: ρ => countKeep ρ
  | .inline _ :: ρ => countKeep ρ

/-- Insert a disposition at source position `j` (newest-first, as `LCtx`). -/
def insertDisp (d : Disp) : Nat → List Disp → List Disp
  | 0, ρ => d :: ρ
  | _ + 1, [] => [d]
  | k + 1, d' :: ρ => d' :: insertDisp d k ρ

/-- Remove the disposition at source position `c`. -/
def removeAt : List Disp → Nat → List Disp
  | [], _ => []
  | _ :: ρ, 0 => ρ
  | d :: ρ, k + 1 => d :: removeAt ρ k

/-- The erased image of source de Bruijn index `i`. A `keep` shifts; a `drop` or an
    `inline` does not. The inlined value is lifted as the walk passes a `keep`. -/
def resolve : List Disp → Nat → ETm
  | [], i => .bvar i
  | .keep :: _, 0 => .bvar 0
  | .keep :: ρ, i + 1 => (resolve ρ i).lift 0 1
  | .drop :: _, 0 => .star
  | .drop :: ρ, i + 1 => resolve ρ i
  | .inline v :: _, 0 => v
  | .inline _ :: ρ, i + 1 => resolve ρ i

theorem resolve_nil (i : Nat) : resolve [] i = .bvar i := rfl

theorem resolve_keep_zero (ρ : List Disp) : resolve (.keep :: ρ) 0 = .bvar 0 := rfl

theorem resolve_keep_succ (ρ : List Disp) (i : Nat) :
    resolve (.keep :: ρ) (i + 1) = (resolve ρ i).lift 0 1 := rfl

theorem resolve_drop_zero (ρ : List Disp) : resolve (.drop :: ρ) 0 = .star := rfl

theorem resolve_drop_succ (ρ : List Disp) (i : Nat) :
    resolve (.drop :: ρ) (i + 1) = resolve ρ i := rfl

theorem resolve_inline_zero (v : ETm) (ρ : List Disp) : resolve (.inline v :: ρ) 0 = v := rfl

theorem resolve_inline_succ (v : ETm) (ρ : List Disp) (i : Nat) :
    resolve (.inline v :: ρ) (i + 1) = resolve ρ i := rfl

/-- Inserting `drop` at source index `j` makes `j` erase to `★`, when `j` is in range.
    A short context puts the `drop` at the end and the index misses it. -/
theorem resolve_insertDisp_drop (j : Nat) (ρ : List Disp) (hj : j ≤ ρ.length) :
    resolve (insertDisp .drop j ρ) j = .star := by
  induction j generalizing ρ with
  | zero =>
    simp only [insertDisp, resolve]
  | succ j ih =>
    cases ρ with
    | nil => exact absurd hj (Nat.not_succ_le_zero j)
    | cons d ρ =>
      have hj' : j ≤ ρ.length := by
        simp only [List.length_cons] at hj
        omega
      cases d with
      | keep =>
        simp only [insertDisp, resolve, ih ρ hj', ETm.lift]
      | drop =>
        simp only [insertDisp, resolve, ih ρ hj']
      | inline v =>
        simp only [insertDisp, resolve, ih ρ hj']

/-- Inserting `keep` at source index `j` makes `j` erase to the erased slot of that prefix. -/
theorem resolve_insertDisp_keep (j : Nat) (ρ : List Disp) (hj : j ≤ ρ.length) :
    resolve (insertDisp .keep j ρ) j = .bvar (countKeep (ρ.take j)) := by
  induction j generalizing ρ with
  | zero =>
    simp only [insertDisp, resolve, List.take_zero, countKeep]
  | succ j ih =>
    cases ρ with
    | nil => exact absurd hj (Nat.not_succ_le_zero j)
    | cons d ρ =>
      have hj' : j ≤ ρ.length := by
        simp only [List.length_cons] at hj
        omega
      cases d with
      | keep =>
        simp only [insertDisp, resolve, ih ρ hj', List.take_succ_cons, countKeep, ETm.lift,
          if_pos (Nat.zero_le _)]
      | drop =>
        simp only [insertDisp, resolve, ih ρ hj', List.take_succ_cons, countKeep]
      | inline v =>
        simp only [insertDisp, resolve, ih ρ hj', List.take_succ_cons, countKeep]

/-- `inst` hits the variable it was built for. -/
theorem inst_bvar_hit (j : Nat) (r : ETm) : ETm.inst j r (.bvar j) = r := by
  simp only [ETm.inst]
  split
  · rfl
  · rename_i h
    exact absurd trivial h

theorem insertDisp_zero (d : Disp) (ρ : List Disp) : insertDisp d 0 ρ = d :: ρ := rfl

theorem removeAt_zero (d : Disp) (ρ : List Disp) : removeAt (d :: ρ) 0 = ρ := rfl

/-! ## §2 erasure -/

/-- Erasure. `σ` is the pending level substitution (`linst` composes it; the top call
    uses `id`). `ρ` is the erased image of the derivation's context. -/
def TyP.eps (σ : Level → Level) (ρ : List Disp) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → ETm
  | _, _, _, _, _, .sort _ _ _ l _ _ => ETm.sort (σ l)
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _ =>
      match levelIsZero (σ u) with
      | true => ETm.star
      | false => resolve ρ i
  | _, _, _, _, _, .const _ _ _ r ls _ _ u _ _ _ _ _ =>
      match levelIsZero (σ u) with
      | true => ETm.star
      | false => ETm.const r (ls.map σ)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB =>
      match levelIsZero (σ u) with
      | true => ETm.pi (hA.eps σ ρ) (piSlot true (hB.eps σ (.drop :: ρ)))
      | false => ETm.pi (hA.eps σ ρ) (hB.eps σ (.keep :: ρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ _ hbody _ =>
      match levelIsZero (σ u) with
      | true => hbody.eps σ (.drop :: ρ)
      | false =>
          match hbody.eps σ (.keep :: ρ) with
          | .star => ETm.star
          | eb => ETm.lam eb
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ =>
      match hf.eps σ ρ with
      | .star => ETm.star
      | ef =>
          match ha.eps σ ρ with
          | .star => ef
          | ea => ETm.app ef ea
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ =>
      match hv.eps σ ρ with
      | .star => hb.eps σ (.drop :: ρ)
      | ev => hb.eps σ (.inline ev :: ρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.eps σ ρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.eps σ ρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D =>
      let inner := D.eps σ (removeAt ρ c)
      match ρ[c]? with
      | some .keep => inner.lift (countKeep (ρ.take c)) 1
      | _ => inner
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _ =>
      match levelIsZero (σ u) with
      | true => D.eps σ (insertDisp .drop j ρ)
      | false =>
          ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ) (D.eps σ (insertDisp .keep j ρ))
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D _ hv _ =>
      let r := hv.eps σ ρ
      match r with
      | .star => D.eps σ (insertDisp .drop j ρ)
      | r => D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) r)) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D =>
      D.eps (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.eps σ ρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.eps σ ρ

/-- Disposition of an `lsub` payload at cutoff `κ` (`★` becomes `.drop`, any other `r`
    becomes `.inline (localize κ r)` — the R2 scope repair). -/
def lsubDisp (κ : Nat) : ETm → Disp
  | .star => .drop
  | r => .inline (localize κ r)

/-! ## §3 clause equations -/

theorem eps_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k : Level} (h : eqN k (.succ l))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.sort E n Γ l k h).eps σ ρ = .sort (σ l) := rfl

theorem eps_bvar_proof {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u : Level} {h : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.bvar E n Γ i A u h hA).eps σ ρ = .star := by
  simp only [TyP.eps, hu]

theorem eps_bvar_rel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u : Level} {h : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = false) :
    (TyP.bvar E n Γ i A u h hA).eps σ ρ = resolve ρ i := by
  simp only [TyP.eps, hu]

theorem eps_const_proof {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u : Level} {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).eps σ ρ = .star := by
  simp only [TyP.eps, hu]

theorem eps_const_rel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u : Level} {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = false) :
    (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).eps σ ρ = .const r (ls.map σ) := by
  simp only [TyP.eps, hu]

theorem eps_pi_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)} {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) :
    (TyP.pi E n Γ A u B v hA hB).eps σ ρ =
      .pi (hA.eps σ ρ) (piSlot true (hB.eps σ (.drop :: ρ))) := by
  simp only [TyP.eps, hu]

theorem eps_pi_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)} {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) :
    (TyP.pi E n Γ A u B v hA hB).eps σ ρ =
      .pi (hA.eps σ ρ) (hB.eps σ (.keep :: ρ)) := by
  simp only [TyP.eps, hu]

theorem eps_lam_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)} {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) :
    (TyP.lam E n Γ A u body B v hA hbody hB).eps σ ρ = hbody.eps σ (.drop :: ρ) := by
  simp only [TyP.eps, hu]

theorem eps_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    {h : TyP E n Γ e A} {hc : CvP E n Γ A B (.sort u)} (σ : Level → Level) (ρ : List Disp) :
    (TyP.conv E n Γ e A B u h hc).eps σ ρ = h.eps σ ρ := rfl

theorem eps_lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
    {hexp : TyP E n Γ (natExpand t) T} (σ : Level → Level) (ρ : List Disp) :
    (TyP.lit E n Γ t T hexp).eps σ ρ = hexp.eps σ ρ := rfl

theorem eps_ewk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {hext : EnvExt E₀ E}
    {D : TyP E₀ n Γ e A} (σ : Level → Level) (ρ : List Disp) :
    (TyP.ewk E₀ E n Γ e A hext D).eps σ ρ = D.eps σ ρ := rfl

theorem eps_cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u : Level}
    {D : TyP E n (.assumption A :: Γ) e T} {hA : CvP E n Γ A A' (.sort u)}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.cctx E n Γ e T A A' u D hA).eps σ ρ = D.eps σ ρ := rfl

theorem eps_linst {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a} {D : TyP E a Γ e A}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.linst E a n Γ e A ls hls hlen D).eps σ ρ =
      D.eps (fun l => σ (instLevel ls l)) ρ := rfl

theorem eps_esub_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = false) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ) (D.eps σ (insertDisp .keep j ρ)) := by
  simp only [TyP.eps, hu]

theorem eps_lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      match hv.eps σ ρ with
      | .star => D.eps σ (insertDisp .drop j ρ)
      | ev => D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) ev)) j ρ) := rfl

theorem eps_esub_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      D.eps σ (insertDisp .drop j ρ) := by
  simp only [TyP.eps, hu]

theorem eps_wk_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl}
    {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? = some .keep) :
    (TyP.wk E n Γ e A d c D).eps σ ρ =
      (D.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
  simp only [TyP.eps, hk]

theorem eps_wk_not_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl}
    {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = D.eps σ (removeAt ρ c) := by
  simp only [TyP.eps]
  rcases hk with hk | hk | ⟨v, hk⟩
  · simp only [hk]
  · simp only [hk]
  · simp only [hk]

/-- The erased context of an enriched context. Let values are inlined; a proof assumption
    is `drop`; a relevant assumption is `keep`. -/
def CtxP.disp (σ : Level → Level) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → List Disp
  | _, _, _, .nil _ _ => []
  | _, _, _, .assumption _ _ _ _ u hΓ _ =>
      match levelIsZero (σ u) with
      | true => .drop :: hΓ.disp σ
      | false => .keep :: hΓ.disp σ
  | _, _, _, .letBinding _ _ _ _ _ _ hΓ _ hv =>
      .inline (hv.eps σ (hΓ.disp σ)) :: hΓ.disp σ

theorem disp_nil {E : ResolvedEnv} {n : Nat} (σ : Level → Level) :
    (CtxP.nil E n).disp σ = [] := rfl

theorem disp_assumption_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} {σ : Level → Level}
    (hu : levelIsZero (σ u) = true) :
    (CtxP.assumption E n Γ A u hΓ hA).disp σ = .drop :: hΓ.disp σ := by
  simp only [CtxP.disp, hu]

theorem disp_assumption_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} {σ : Level → Level}
    (hu : levelIsZero (σ u) = false) :
    (CtxP.assumption E n Γ A u hΓ hA).disp σ = .keep :: hΓ.disp σ := by
  simp only [CtxP.disp, hu]

/-! ## §4 pins -/

/-- S0 §5's closed β, erased. The domain `sort 0` is a type (`sort 1`), so the λ is kept
    and its domain is deleted; the argument `∀ P : Prop, P` is a proposition, not a proof,
    so it is kept. The two endpoints are one β step apart. -/
theorem pinBetaP_lhs_eps :
    pinBetaP.dl.eps id [] = .app (.lam (.sort .zero)) (.pi (.sort .zero) (.bvar 0)) := rfl

theorem pinBetaP_rhs_eps : pinBetaP.dr.eps id [] = .sort .zero := rfl

theorem pinBetaP_eps_beta :
    RStep [] (pinBetaP.dl.eps id []) (pinBetaP.dr.eps id []) := by
  rw [pinBetaP_lhs_eps, pinBetaP_rhs_eps]
  exact .beta _ _

/-- `λ h : (∀ P : Prop, P). h`, a proof of a proof-proposition. The domain is a proof
    binder and the body is that proof variable, so the λ erases to `★` (S0 §6.1). -/
def forallPExpr : Expr Nat := .pi (.sort .zero) (.bvar 0)

def pinForallWk : TyP emptyEnv 0 [.assumption forallPExpr]
    (lift 0 1 forallPExpr) (.sort .zero) :=
  .wk emptyEnv 0 [] forallPExpr (.sort .zero) (.assumption forallPExpr) 0 pinForallP

def pinProofId : TyP emptyEnv 0 [] (.lam forallPExpr (.bvar 0))
    (.pi forallPExpr (lift 0 1 forallPExpr)) :=
  .lam emptyEnv 0 [] forallPExpr .zero (.bvar 0) (lift 0 1 forallPExpr) .zero pinForallP
    (.bvar emptyEnv 0 [.assumption forallPExpr] 0 (lift 0 1 forallPExpr) .zero rfl pinForallWk)
    pinForallWk

theorem pinProofId_eps : pinProofId.eps id [] = .star := rfl

end Rcic.Syn

#print axioms Rcic.Syn.resolve_keep_succ
#print axioms Rcic.Syn.resolve_drop_succ
#print axioms Rcic.Syn.resolve_inline_succ
#print axioms Rcic.Syn.resolve_insertDisp_drop
#print axioms Rcic.Syn.resolve_insertDisp_keep
#print axioms Rcic.Syn.inst_bvar_hit
#print axioms Rcic.Syn.eps_bvar_proof
#print axioms Rcic.Syn.eps_bvar_rel
#print axioms Rcic.Syn.eps_const_proof
#print axioms Rcic.Syn.eps_const_rel
#print axioms Rcic.Syn.eps_pi_drop
#print axioms Rcic.Syn.eps_pi_keep
#print axioms Rcic.Syn.eps_lam_drop
#print axioms Rcic.Syn.eps_esub_keep
#print axioms Rcic.Syn.eps_esub_drop
#print axioms Rcic.Syn.eps_wk_keep
#print axioms Rcic.Syn.eps_wk_not_keep
#print axioms Rcic.Syn.disp_assumption_drop
#print axioms Rcic.Syn.disp_assumption_keep
#print axioms Rcic.Syn.pinBetaP_lhs_eps
#print axioms Rcic.Syn.pinBetaP_rhs_eps
#print axioms Rcic.Syn.pinBetaP_eps_beta
#print axioms Rcic.Syn.pinProofId_eps
