import rcic.RcicSynClosedUconstlit
import rcic.RcicSynClosedEsapp
import rcic.RcicSynTableBuildI

/-!
# `RcicSynSRConsts` — sortRow closure row `es_consts`: kernel refutation + restated wall

Census row 1 of `research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`
(wall `W-COV-CONST-ASCRIPTION-LEVELS`, named missing lemmas `consts_canon_cl`
and the shape-indexed reg-occ path for transport heads).

## Result

* `pL pR`/`occL occR` — **refuted**. `TyP.RegSubAt D` (the receipt shape the
  ports need: `D.reg.2` at a `DNode.subAt` child path) is true exactly on the
  heads where `TyP.reg` returns a *stored* field — `bvar`/`const`/`app`/`letE`,
  and `conv` with a rule-headed conversion (`ty_reg_subAt_*`,
  `RcicSynClosedEsapp.lean:136`). For a transport head the regularity is a
  freshly built node (`TyP.reg`, `RcicConvPlus.lean:441–458`) that contains
  the node's own children (`hv`/`hvT`, `R.2`) — it is never a forest member.
  `toothEwk_regSubAt_refuted` + `es_consts_occL_ewk_refuted` give the kernel
  counterexample at a real `ewk` endpoint (`toothEwkDl`), with `AssumpPref`
  inhabited (`toothEwkDl_assumpPref`).

* `leftCl`/`rightCl` (`consts_canon_cl`) — **not refuted** (kept inside the
  restated wall). Every transport's `eps` forwards or re-displays the inner
  erasure and a `.const` subject has no bvars, so `dl.eps σ ρ` reduces to the
  canonical formula — *provided* the stored sort-levels are `eqN`-coherent
  under `LevelHom σ`, i.e. sort-level uniqueness through `esub`/`lsub`
  substitution. That uniqueness is not a landed lemma (`SortUnique` is an
  explicit premise in `RcicA2SortSupport`), so the CL side stays a named wall.

The row's deliverable: `EsConstsWall` restates the wall as ONE named Prop,
`es_consts_of_wall`/`es_consts_tableI` close the field under it at an
arbitrary table and at `tableOfI hW`, and `es_consts_wall_ewk_false` shows
the wall is genuinely uninhabitable for transport endpoints.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 discriminants and the `ewk` fixture -/

/-- The subject index of a `TyP` node — a disequality discriminant for the
    forest (read off the type index, no reduction of `reg` needed). -/
def TyP.subjE {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (_ : TyP E n Γ e T) : Expr Nat := e

/-- The subject of a `TyP` forest node, `none` for conversions. -/
def DNode.tySubj : DNode → Option (Expr Nat)
  | .ty D => some D.subjE
  | .cv _ => none

/-- The forest-children count of a node — a constructor-shape discriminant. -/
def DNode.nChildren (d : DNode) : Nat := d.children.length

/-- An `ewk`-headed `.const`-subject endpoint at `toothEnv`: the transport-head
    case of `es_consts`'s `dl`. -/
def toothEwkDl : TyP toothEnv 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  TyP.ewk toothEnv toothEnv 0 [] (.const 0 []) (.sort (.succ .zero))
    (envExt_refl toothEnv) toothH

/-- The fixture satisfies `AssumpPref` (transports' cutoff `[]` is trivial;
    `ewk` forwards the child's). -/
theorem toothEwkDl_assumpPref : toothEwkDl.AssumpPref := trivial

/-- `toothH`'s regularity level: `reg`'s `const` arm returns `⟨u, hT⟩` — the
    WF-recursive `reg` reduces via its equation lemmas, not `rfl`. -/
theorem toothH_reg_fst : toothH.reg.1 = .succ (.succ .zero) := by
  simp only [toothH, TyP.reg]

/-! ## §2 node disequalities -/

/-- `.ty toothEwkDl ≠ .ty toothEwkDl.reg.2`: subjects `.const 0 []` vs
    `.sort 1`. -/
theorem toothEwk_reg_ne_self :
    DNode.ty toothEwkDl ≠ DNode.ty toothEwkDl.reg.2 := by
  intro h
  have hs := congrArg DNode.tySubj h
  simp only [DNode.tySubj, TyP.subjE, Option.some.injEq] at hs
  exact Expr.noConfusion hs

/-- `.ty toothH ≠ .ty toothEwkDl.reg.2`: subjects `.const 0 []` vs
    `.sort 1` — ctor discrimination, no `reg` reduction needed. -/
theorem toothH_reg_ne :
    DNode.ty toothH ≠ DNode.ty toothEwkDl.reg.2 := by
  intro h
  have hs := congrArg DNode.tySubj h
  simp only [DNode.tySubj, TyP.subjE, Option.some.injEq] at hs
  exact Expr.noConfusion hs

/-- `.ty toothST ≠ .ty toothEwkDl.reg.2`: subject and type indexes coincide
    (`.sort 1 : .sort 2` — `reg`'s `ewk` arm passes the parent's type as
    subject), but child counts differ — `sort` has none, `ewk` keeps `D`. -/
theorem toothST_reg_ne :
    DNode.ty toothST ≠ DNode.ty toothEwkDl.reg.2 := by
  intro h
  have hs := congrArg DNode.nChildren h
  simp only [DNode.nChildren, DNode.children, toothST, toothEwkDl, toothH,
    TyP.reg, TyP.dchildren, List.length] at hs
  omega

/-- `.cv c ≠ .ty toothEwkDl.reg.2`: different `DNode` constructors. -/
theorem cv_reg_ne (c : CvP E n Γ a b T) :
    DNode.cv c ≠ DNode.ty toothEwkDl.reg.2 := by
  intro h
  exact DNode.noConfusion h

/-! ## §3 the refutation -/

/-- **Kernel refutation of `TyP.RegSubAt toothEwkDl`** — the `ewk` endpoint's
    rebuilt regularity is at no child path: the whole reachable set is
    `{toothEwkDl, toothH, toothST}`. -/
theorem toothEwk_regSubAt_refuted : ¬ TyP.RegSubAt toothEwkDl := by
  rintro ⟨_ | ⟨i, rest⟩, hp⟩
  · exact toothEwk_reg_ne_self (Option.some.inj hp)
  · match i with
    | 0 =>
        match rest with
        | [] => exact toothH_reg_ne (Option.some.inj hp)
        | j :: rest' =>
            match j with
            | 0 =>
                match rest' with
                | [] => exact toothST_reg_ne (Option.some.inj hp)
                | _ :: _ => exact Option.noConfusion hp
            | _ + 1 => exact Option.noConfusion hp
    | _ + 1 => exact Option.noConfusion hp

/-- The `es_consts` `occL` port at the `ewk` fixture: no path reaches
    `toothEwkDl.reg.2` inside the `CvP.consts` payload either — the `dr`
    subtree adds only `{toothH, toothST}`. -/
theorem es_consts_occL_ewk_refuted
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ∀ p : List Nat,
      P2Query.subAt
        (.es (CvP.consts toothEnv 0 [] 0 [] [] toothMember
          (members_extend_self emptyEnv 0 toothMember) rfl rfl rfl
          (eqNList_refl []) toothEwkDl toothH) S σ ρ)
        0 p ≠ some (.ty toothEwkDl.reg.2) := by
  intro p hp
  match p with
  | [] => exact cv_reg_ne _ (Option.some.inj hp)
  | i :: rest =>
      match i with
      | 0 =>
          match rest with
          | [] => exact toothEwk_reg_ne_self (Option.some.inj hp)
          | j :: rest' =>
              match j with
              | 0 =>
                  match rest' with
                  | [] => exact toothH_reg_ne (Option.some.inj hp)
                  | k :: rest'' =>
                      match k with
                      | 0 =>
                          match rest'' with
                          | [] => exact toothST_reg_ne (Option.some.inj hp)
                          | _ :: _ => exact Option.noConfusion hp
                      | _ + 1 => exact Option.noConfusion hp
              | _ + 1 => exact Option.noConfusion hp
      | 1 =>
          match rest with
          | [] => exact toothH_reg_ne (Option.some.inj hp)
          | j :: rest' =>
              match j with
              | 0 =>
                  match rest' with
                  | [] => exact toothST_reg_ne (Option.some.inj hp)
                  | _ :: _ => exact Option.noConfusion hp
              | _ + 1 => exact Option.noConfusion hp
      | _ + 2 => exact Option.noConfusion hp

/-! ## §4 the restated wall and the pinned field -/

/-- **The exact restated wall** `W-COV-CONST-ASCRIPTION-LEVELS` for
    `es_consts` at a given table: the two `reg.2` occurrence receipts
    (`occL`/`occR`) and the two canonical-surface `CL`s (`leftCl`/`rightCl`). -/
def EsConstsWall (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop :=
  ∃ pL pR : List Nat,
    P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      dl dr) S σ ρ) 0 pL = some (.ty dl.reg.2) ∧
    P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      dl dr) S σ ρ) 0 pR = some (.ty dr.reg.2) ∧
    CL tbl σ ρ dl (constsCanonLeft hres hlen hwf dl) ∧
    CL tbl σ ρ dr (constsCanonRight hres hlen hwf' hls dr)

/-- `es_consts` at an arbitrary table, under exactly the named wall —
    repackaging of the landed `es_consts_closed`. -/
theorem es_consts_of_wall
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (w : EsConstsWall tbl hres hlen hwf hwf' hls dl dr S σ ρ) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      dl dr) S σ ρ) := by
  obtain ⟨pL, pR, occL, occR, leftCl, rightCl⟩ := w
  exact es_consts_closed Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ
    pL pR occL occR leftCl rightCl

/-- `es_consts` at `tableOfI hW`, under exactly the named wall. -/
theorem es_consts_tableI (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (w : EsConstsWall (tableOfI hW) hres hlen hwf hwf' hls dl dr S σ ρ) :
    CaseStep Aw (tableOfI hW) (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf
      hwf' hls dl dr) S σ ρ) :=
  es_consts_of_wall Aw (tableOfI hW) hres hlen hwf hwf' hls dl dr S σ ρ w

/-- The wall is **uninhabitable at the `ewk` fixture**: `occL` already fails —
    the `RegSubAt` receipt for a transport head is refuted above. -/
theorem es_consts_wall_ewk_false
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ EsConstsWall (E := toothEnv) (n := 0) (Γ := []) (r := 0) (ls := [])
        (ls' := []) (m := toothMember) tbl
        (members_extend_self emptyEnv 0 toothMember) rfl rfl rfl
        (eqNList_refl []) toothEwkDl toothH S σ ρ := by
  rintro ⟨pL, _, occL, -⟩
  exact es_consts_occL_ewk_refuted S σ ρ pL occL

/-- Non-vacuity of the CL side: at the `ewk` fixture the canonical-surface
    `CL` IS inhabited (`refl` — `ewk` forwards `toothH`'s erasure and the
    stored level `.succ (.succ .zero)` is not `Prop` under `id`). -/
theorem consts_canon_cl_ewk (ρ : List Disp) :
    CL tbl id ρ toothEwkDl
      (constsCanonLeft (E := toothEnv) (n := 0) (Γ := []) (r := 0) (ls := [])
        (m := toothMember)
        (members_extend_self emptyEnv 0 toothMember) rfl rfl
        toothEwkDl) := by
  simp only [CL, toothEwkDl, toothH, constsCanonLeft, TyP.reg, TyP.eps]
  exact .refl _

#print axioms Rcic.Syn.TyP.subjE
#print axioms Rcic.Syn.DNode.tySubj
#print axioms Rcic.Syn.DNode.nChildren
#print axioms Rcic.Syn.toothH_reg_fst
#print axioms Rcic.Syn.toothEwkDl
#print axioms Rcic.Syn.toothEwkDl_assumpPref
#print axioms Rcic.Syn.toothEwk_reg_ne_self
#print axioms Rcic.Syn.toothH_reg_ne
#print axioms Rcic.Syn.toothST_reg_ne
#print axioms Rcic.Syn.cv_reg_ne
#print axioms Rcic.Syn.toothEwk_regSubAt_refuted
#print axioms Rcic.Syn.es_consts_occL_ewk_refuted
#print axioms Rcic.Syn.EsConstsWall
#print axioms Rcic.Syn.es_consts_of_wall
#print axioms Rcic.Syn.es_consts_tableI
#print axioms Rcic.Syn.es_consts_wall_ewk_false
#print axioms Rcic.Syn.consts_canon_cl_ewk
