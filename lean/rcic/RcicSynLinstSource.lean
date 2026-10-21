import rcic.RcicSynAdm
import rcic.RcicSynLetInline
import rcic.RcicTypedLevels
import rcic.RcicPinEqEraseWf
import rcic.RcicIotaWitnessTyped
import rcic.RcicIA021HTEnvWfT

/-!
# Syntactic sortRow — S8/C6: the `linst` source-context counterexample

Specification: `research/rcic/sortrow/S8_SOURCE_CONTEXT_RESOLUTION.md` §4
(approved ChatGPT S8, #7338, measured at main `cbc4bfad4c`). `closure_claim = 0`.

`linst` has **no term cutoff** — it changes the universe arity `a → n`
(`instLvlsCtx`, `instantiateLevels`). The source-`CtxP` supply question is
therefore not a prefix-reflection problem, and §4 gives the concrete instance
where it is genuinely impossible:

* §4.2 `TyP.constLevelsBounded`: every `TyP` of `.const r ls` carries
  `levelsBounded n ls = true`. Structural induction — `.const` reads `hwf`;
  `.conv`/`.ewk`/`.cctx` recurse; `.wk` keeps the head via `lift_eq_const_k`;
  `.esub`/`.lsub` decompose via `instantiate_eq_const_or` (source derivation or
  the actual replacement `hv`); `.linst` inverts the source constant list
  (`instantiateLevels_eq_const_ex`), applies the IH at the source arity and
  pushes the bound through `levelsBounded_map_instLevel`; every other root
  dies by term-constructor contradiction. **No `hcoh`, no `SortUnique`.**
* §4.1/§4.3 the `Eq` recursor at arity 1: `eqEnvT`'s member 65 is `eqRecT`
  (`.recursorM`, arity 1). With `p = param 0`, `T = instantiateLevels [p]
  eqRecT.mtype`, `v = const 65 [p]`, `Γ = [.letBinding T v]`:
  - `target_native_wf`: `CtxWfT eqEnvT 1 Γ` from the real admission — the
    `envWfT_cellHT` cell that `IA021T_hT_of_envWfT_ext` reads, lifted by
    `hasTyTExt` and instantiated by `hasTyT_instLevels`, no `SortUnique`;
  - `linstSourceD1`: `D₁ = linst … [] D₀` at arity 1, a **public AP** input in
    the natively well-formed target;
  - `no_source_ctxP`: any `CtxP eqEnvT 0 Γ` would carry `hv : TyP eqEnvT 0 []
    (const 65 [param 0]) T`, and `constLevelsBounded` computes
    `levelsBounded 0 [param 0] = false` — impossible;
  - `no_unconditional_source_linst_resolution`: the universal resolver —
    "every `linst` in a native-wf target yields a source `CtxP`" — is refuted
    by this instance. Rebasing the environment cannot help: same `eqEnvT`
    both sides; the gap is arity 0 vs 1, not an `.ewk` member gap. New wall:
    **C6 — W-COV-LINST-SOURCE-ARITY**.
* The display side is untouched: `D₁`'s public sort conclusion is still a
  real derivation in the native target (`linst_public_conclusion`) — the
  refusal is about *source resolution*, never about `D₁`'s own semantics.

Credit: ChatGPT's S8 (#7338).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the constant level-list invariant -/

private theorem constLevelsBounded_aux {r : Nat} : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T : Expr Nat} → (D : TyP E n Γ e T) → ∀ {ls},
    e = .const r ls → levelsBounded n ls = true
  | _, _, _, _, _, .sort .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .bvar .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .const (hwf := hwf) .., _, h => by
      cases h
      exact hwf
  | _, _, _, _, _, .pi .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .lam .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .app .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .letE .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .lit .., _, h => Expr.noConfusion h
  | _, _, _, _, _, .conv (h := D) .., _, h => constLevelsBounded_aux D h
  | _, _, _, _, _, .wk (D := D) .., _, h =>
      constLevelsBounded_aux D (lift_eq_const_k h)
  | _, _, _, _, _, .esub (D := D) (hv := hv) .., _, h => by
      rcases instantiate_eq_const_or h with h1 | h2
      · exact constLevelsBounded_aux D h1
      · exact constLevelsBounded_aux hv h2
  | _, _, _, _, _, .lsub (D := D) (hv := hv) .., _, h => by
      rcases instantiate_eq_const_or h with h1 | h2
      · exact constLevelsBounded_aux D h1
      · exact constLevelsBounded_aux hv h2
  | _, _, _, _, _, .linst (ls := ls') (hls := hls) (hlen := hlen) (D := D) .., _,
      h => by
      obtain ⟨ms, hm⟩ := instantiateLevels_eq_const_ex h
      have hih := constLevelsBounded_aux D hm
      rw [hm] at h
      simp only [instantiateLevels] at h
      cases h
      exact levelsBounded_map_instLevel hls ms (hlen ▸ hih)
  | _, _, _, _, _, .ewk (D := D) .., _, h => constLevelsBounded_aux D h
  | _, _, _, _, _, .cctx (D := D) .., _, h => constLevelsBounded_aux D h

/-- S8 §4.2: every `TyP` of `.const r ls` is level-bounded at its own arity.
    Independent structural induction — no `hcoh`, no `SortUnique`. -/
theorem TyP.constLevelsBounded {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {T : Expr Nat}
    (D : TyP E n Γ (.const r ls) T) : levelsBounded n ls = true :=
  constLevelsBounded_aux D rfl

/-! ## §2 the `Eq` instance at arity 1 -/

/-- `p = param 0` (S8 §4.1). -/
def linstP : Level := .param 0

/-- `T = instantiateLevels [p] eqRecT.mtype` (S8 §4.1). -/
def linstTy : Expr Nat := instantiateLevels [linstP] eqRecT.mtype

/-- `v = const 65 [p]` (S8 §4.1). -/
def linstVal : Expr Nat := .const 65 [linstP]

/-- `Γ = [let z : T := v]` (S8 §4.1). -/
def linstΓ : LCtx := [.letBinding linstTy linstVal]

/-- member 65 is `eqRecT` — `eqEnvT := extendEnv eqPrefixT 65 eqRecT`. -/
theorem linst_eqEnvT_mem : eqEnvT.members 65 = some eqRecT :=
  members_extend_self eqPrefixT 65 eqRecT

/-- `v : T` at arity 1 from the real member fields. -/
def linstVal_typed : HasTyT eqEnvT 1 [] linstVal linstTy :=
  HasTyT.const [] 65 [linstP] eqRecT linst_eqEnvT_mem rfl rfl

/-- the recursor cell for member 65 — the witness `IA021T_hT_of_envWfT_ext`
    reads (`u`, `hT` at the derivation prefix). -/
def linstCell : RecursorCellHT eqEnvT 65 eqRecT :=
  envWfT_cellHT pinEqGroupWfT linst_eqEnvT_mem rfl

/-- the instantiated cell sort `instLevel [p] u` — the `u` of the admission. -/
def linstU : Level := instLevel [linstP] linstCell.u

/-- `T : sort u` at arity 1 — the cell's `hT` lifted by `hasTyTExt` (the same
    composition `IA021T_hT_of_envWfT_ext` performs) and instantiated by
    `hasTyT_instLevels`. No `SortUnique`. -/
def linstTy_typed : HasTyT eqEnvT 1 [] linstTy (.sort linstU) :=
  hasTyT_instLevels (envWfT_levels pinEqGroupWfT) (iotaLevelsT_of_envWfT pinEqGroupWfT)
    (n := 1) (ls := [linstP]) rfl rfl
    (hasTyTExt linstCell.cell.env_extends linstCell.hT)

/-- S8 §4.1(a): the target context `Γ` is natively well formed at arity 1. -/
def target_native_wf : CtxWfT eqEnvT 1 linstΓ :=
  CtxWfT.letBinding [] linstTy linstU linstVal .nil linstTy_typed linstVal_typed

/-- the source typing `D₀`: a legal `TyP` at arity 0 — the `sort` rule does
    not require `Γ` well formed. -/
def linstSourceD0 : TyP eqEnvT 0 linstΓ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort eqEnvT 0 linstΓ .zero (.succ .zero) (eqN_refl _)

/-- `D₁ = linst … [] D₀` — the public AP `linst` at arity 1 (`[].length = 0`,
    `levelsBounded 1 []`, `instLvlsCtx [] Γ` displayed on the way out). -/
def linstSourceD1 : TyP eqEnvT 1 (instLvlsCtx [] linstΓ)
    (instantiateLevels [] (.sort .zero)) (instantiateLevels [] (.sort (.succ .zero))) :=
  TyP.linst eqEnvT 0 1 linstΓ (.sort .zero) (.sort (.succ .zero)) [] rfl rfl
    linstSourceD0

/-- `D₁` is a public AP input: `linst`'s `AssumpPref` is its child's, and
    `sort`'s is `True`. -/
theorem public_linst_AP : linstSourceD1.AssumpPref := trivial

/-- `instLvlsCtx` by the empty list is the identity on any `Γ`. -/
theorem instLvlsCtx_empty : (Γ : LCtx) → instLvlsCtx [] Γ = Γ
  | [] => rfl
  | d :: t => by
      show instLvlsDecl [] d :: instLvlsCtx [] t = d :: t
      rw [instLvlsCtx_empty t]
      cases d <;> simp [instLvlsDecl, instantiateLevels_nil]

/-- display side: `D₁`'s public sort conclusion is still a real derivation in
    the native target — the source refusal never touches `D₁`'s own semantic
    conclusion (S8 §4.3's terminal-clause branch: a sort reads no context). -/
def linst_public_conclusion :
    TyP eqEnvT 1 linstΓ (.sort .zero) (.sort (.succ .zero)) := by
  have D := linstSourceD1
  rwa [instLvlsCtx_empty, instantiateLevels_nil, instantiateLevels_nil] at D

/-! ## §3 the source refusal -/

/-- S8 §4.2: no source `CtxP` exists. Any `CtxP eqEnvT 0 Γ` must be a
    `letBinding` node whose value field types `const 65 [param 0]` at arity 0,
    and `constLevelsBounded` computes `levelsBounded 0 [param 0] = false`. -/
theorem no_source_ctxP (C : CtxP eqEnvT 0 linstΓ) : False := by
  cases C with
  | letBinding _ _ _ _ _ _ hv =>
      have hb := TyP.constLevelsBounded hv
      exact absurd hb (by decide)

/-- C6 — W-COV-LINST-SOURCE-ARITY: the unconditional source resolver cannot
    exist. A function turning every `linst` in a natively well-formed target
    into a source `CtxP` refuted by the arity-0/arity-1 `Eq` instance — this
    is not an environment-member gap, so no environment rebase repairs it. -/
theorem no_unconditional_source_linst_resolution :
    ¬ (∀ {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat}
        {ls : List Level} {hls : levelsBounded n ls = true}
        {hlen : ls.length = a} {D : TyP E a Γ e A},
        CtxWfT E n (instLvlsCtx ls Γ) → Nonempty (CtxP E a Γ)) := fun f => by
  have h := f (E := eqEnvT) (a := 0) (n := 1) (Γ := linstΓ)
    (e := .sort .zero) (A := .sort (.succ .zero)) (ls := [])
    (hls := rfl) (hlen := rfl) (D := linstSourceD0) target_native_wf
  obtain ⟨C⟩ := h
  exact no_source_ctxP C

end Rcic.Syn

#print axioms Rcic.Syn.TyP.constLevelsBounded
#print axioms Rcic.Syn.linst_eqEnvT_mem
#print axioms Rcic.Syn.linstVal_typed
#print axioms Rcic.Syn.linstCell
#print axioms Rcic.Syn.linstU
#print axioms Rcic.Syn.linstTy_typed
#print axioms Rcic.Syn.target_native_wf
#print axioms Rcic.Syn.linstSourceD0
#print axioms Rcic.Syn.linstSourceD1
#print axioms Rcic.Syn.public_linst_AP
#print axioms Rcic.Syn.instLvlsCtx_empty
#print axioms Rcic.Syn.linst_public_conclusion
#print axioms Rcic.Syn.no_source_ctxP
#print axioms Rcic.Syn.no_unconditional_source_linst_resolution
