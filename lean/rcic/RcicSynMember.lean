import rcic.RcicTypedEnvEntry
import rcic.RcicTypedLevelsExt
import rcic.RcicSynTyAt

/-!
# RcicSynMember — a stored member type under a transport skeleton (step 3n)

S3 §15. `TyP.const` does not store closedness or `exprLevelsBounded`.
Both are theorems of `EnvWfT`:

* `envClosed_of_envWfT` (`RcicTypedEnvEntry`) — `∀ k, lift k 1 m.mtype = m.mtype`;
* `envWfT_levels` (`RcicTypedLevels`) — `exprLevelsBounded m.arity m.mtype = true`,
  and the same for a body.

`app_instantiateLevels_closed` is the skeleton equation those two premises
discharge. The const arm of `tyAt` rewrites the ascribed type
`instantiateLevels ls₀ m.mtype` by `app_instantiateLevels_memberOf`; δ
rewrites the body and the type, both instantiated at the rule's own `ls`,
by `app_instantiateLevels_body` and `app_instantiateLevels_member`.
`tySort` rebuilds a sort node. `tyConst` rebuilds a const node once the
ascribed member type has been retyped. `tyAt` itself is still not defined.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Level instantiation does not change the length of a level list. -/
theorem appLevels_length :
    (ss : List Skel) → (ls : List Level) → (Skels.appLevels ss ls).length = ls.length
  | [], _ => rfl
  | .wk _ _ :: ss, ls => appLevels_length ss ls
  | .esub _ _ :: ss, ls => appLevels_length ss ls
  | .linst ls₀ :: ss, ls => by
      simp only [Skels.appLevels]
      rw [appLevels_length ss (ls.map (instLevel ls₀)), List.length_map]
  | .cctx _ _ :: ss, ls => appLevels_length ss ls

theorem length_appLevels_of {ss : List Skel} {ls : List Level} {a : Nat}
    (h : ls.length = a) : (Skels.appLevels ss ls).length = a :=
  (appLevels_length ss ls).trans h

/-- The environment data the conversion walks actually consume: member
    closedness (`tyConst`/`cvDelta`/`cvConsts` casts), member
    level-boundedness (the same casts), level-free stored bodies and
    per-member arity-coherence certificates (`IotaLevelsT`). `EnvWfT E`
    supplies all four (`cvWalkHyp_of_envWfT`); a `GroupMembersT` cons step
    extends them (`cvWalkHyp_cons`), so the walks run at group-intermediate
    environments that never carry an `EnvWfT`. -/
structure CvWalkHyp (E : ResolvedEnv) : Type where
  closed : EnvClosed E
  levels : EnvLevelsT E
  bodyLvl0 : ∀ r m b, E.members r = some m → m.body = some b →
    exprLevelsBounded 0 b = true
  declArities : DeclAritiesT E

/-- `EnvWfT` induces a `CvWalkHyp` — the four projections the emitters
    already read through it. -/
noncomputable def cvWalkHyp_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    CvWalkHyp E :=
  ⟨envClosed_of_envWfT hW, envWfT_levels hW, envWfT_body_lvl0 hW,
    envWfT_declArities hW⟩

/-- One `GroupMembersT.cons` step: `hfresh`/`hnobody`/`hclT`/`hlvlB`/
    `harities` are exactly the fields the cons node carries. Twin of the
    `hbase` updates inside `groupMembersT_levels` / `groupMembersT_body_lvl0`
    / `groupMembersT_declArities`. -/
def cvWalkHyp_cons {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (w : CvWalkHyp E) (hfresh : E.members r = none) (hnobody : m.body = none)
    (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
    (hlvlB : exprLevelsBounded m.arity m.mtype = true)
    (harities : groupArityCoherent E m = true) :
    CvWalkHyp (extendEnv E r m) where
  closed := fun r' m' hm' => by
    by_cases hrr : r' = r
    · subst hrr
      rw [members_extend_eq] at hm'
      cases hm'
      exact ⟨hclT, fun b hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
    · rw [members_extend_ne E m hrr] at hm'
      exact w.closed r' m' hm'
  levels := fun r' m' hm' => by
    by_cases hrr : r' = r
    · subst hrr
      rw [members_extend_eq] at hm'
      cases hm'
      exact ⟨hlvlB, fun b hb => by rw [hnobody] at hb; cases hb⟩
    · rw [members_extend_ne E m hrr] at hm'
      exact w.levels r' m' hm'
  bodyLvl0 := fun r' m' b hm' hb => by
    by_cases hrr : r' = r
    · subst hrr
      rw [members_extend_eq] at hm'
      cases hm'
      rw [hnobody] at hb
      exact Option.noConfusion hb
    · rw [members_extend_ne E m hrr] at hm'
      exact w.bodyLvl0 r' m' b hm' hb
  declArities := fun r' m' hm' => by
    by_cases hrr : r' = r
    · rw [hrr, members_extend_eq] at hm'
      cases hm'
      exact ⟨E, harities, members_extend_preserved hfresh⟩
    · rw [members_extend_ne E m hrr] at hm'
      obtain ⟨E0, ha, hsub⟩ := w.declArities r' m' hm'
      exact ⟨E0, ha, fun r'' m'' h0 =>
        members_extend_preserved hfresh r'' m'' (hsub r'' m'' h0)⟩

/-- `IotaLevelsT` off a `CvWalkHyp` — routes through the projection-
    parameterized discharge `iotaLevelsT_of`. -/
theorem iotaLevelsT_of_cvWalkHyp {E : ResolvedEnv} (w : CvWalkHyp E) :
    IotaLevelsT E :=
  iotaLevelsT_of w.levels w.bodyLvl0 w.declArities

/-- An `IotaPack` off a `CvWalkHyp` — same shape as `iotaPack_of_envWfT`. -/
def iotaPack_of_cvWalkHyp {E : ResolvedEnv} (w : CvWalkHyp E) : IotaPack E :=
  ⟨iotaLift E, iotaSubst E,
    fun ls _ _ h => derivedIota_instLevels (iotaLevelsT_of_cvWalkHyp w) h ls⟩

/-- The stored type, instantiated at a list of the member's arity, ignores
`wk` and `esub`. `linst` is `instantiateLevels_compose`. -/
theorem app_instantiateLevels_member {E : ResolvedEnv} (hE : CvWalkHyp E)
    {r : Nat} {m : CheckedMember} (hres : E.members r = some m)
    (ss : List Skel) (ls : List Level) (hlen : ls.length = m.arity) :
    Skels.app ss (instantiateLevels ls m.mtype) =
      instantiateLevels (Skels.appLevels ss ls) m.mtype := by
  have hcl : ∀ c, lift c 1 m.mtype = m.mtype :=
    (hE.closed r m hres).1
  have hbnd : exprLevelsBounded ls.length m.mtype = true :=
    hlen.symm ▸ (hE.levels r m hres).1
  exact app_instantiateLevels_closed ss ls m.mtype hcl hbnd

/-- `TyP.const` ascribes `instantiateLevels ls₀ m.mtype`, and `ls =ₙ ls₀`.
The lengths agree, so the member equation applies at `ls₀`. -/
theorem app_instantiateLevels_memberOf {E : ResolvedEnv} (hE : CvWalkHyp E)
    {r : Nat} {m : CheckedMember} (hres : E.members r = some m)
    (ss : List Skel) {ls ls₀ : List Level}
    (hlen : ls.length = m.arity) (heq : eqNList ls ls₀) :
    Skels.app ss (instantiateLevels ls₀ m.mtype) =
      instantiateLevels (Skels.appLevels ss ls₀) m.mtype :=
  app_instantiateLevels_member hE hres ss ls₀
    ((eqNList_length ls ls₀ heq).symm.trans hlen)

/-- A stored body, instantiated at a list of the member's arity. δ's
right-hand side. -/
theorem app_instantiateLevels_body {E : ResolvedEnv} (hE : CvWalkHyp E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hb : m.body = some b)
    (ss : List Skel) (ls : List Level) (hlen : ls.length = m.arity) :
    Skels.app ss (instantiateLevels ls b) =
      instantiateLevels (Skels.appLevels ss ls) b := by
  have hcl : ∀ c, lift c 1 b = b :=
    (hE.closed r m hres).2 b hb
  have hbnd : exprLevelsBounded ls.length b = true :=
    hlen.symm ▸ (hE.levels r m hres).2 b hb
  exact app_instantiateLevels_closed ss ls b hcl hbnd

/-- A `sort` node under the skeleton. `linst` is the only step that moves
the level; `eqN` is preserved, and `succ` commutes with it. -/
def tySort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (l k : Level)
    (h : eqN k (.succ l)) (ss : List Skel) :
    TyP E n Γ (Skels.app ss (.sort l)) (Skels.app ss (.sort k)) :=
  tyCast (app_sort ss l).symm (app_sort ss k).symm <|
    TyP.sort E n Γ (Skels.appLevel ss l) (Skels.appLevel ss k)
      ((appLevel_succ ss l) ▸ eqN_appLevel ss h)

/-- A `const` node under the skeleton. The recursive call has already
retyped `instantiateLevels ls₀ m.mtype`; this casts that typing onto the
stored member (`app_instantiateLevels_memberOf`) and rebuilds the node.
The conclusion is the skeleton applied to the original constant and to
its ascribed type. -/
def tyConst {E : ResolvedEnv} (hE : CvWalkHyp E) {n nIn : Nat} {Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true) (hls : eqNList ls ls₀)
    (ss : List (PStep E n)) (hfuel : FuelRel ss nIn)
    (hT : TyP E n Γ
        (Skels.app (steps ss) (instantiateLevels ls₀ m.mtype))
        (.sort (Skels.appLevel (steps ss) u))) :
    TyP E n Γ
      (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls₀ m.mtype)) :=
  let hTy := tyCast (app_instantiateLevels_memberOf hE hres (steps ss) hlen hls) rfl hT
  let node := TyP.const E n Γ r
      (Skels.appLevels (steps ss) ls) (Skels.appLevels (steps ss) ls₀) m
      (Skels.appLevel (steps ss) u) hres (length_appLevels_of hlen)
      (levelsBounded_steps ss nIn hfuel ls hwf)
      (eqNList_appLevels (steps ss) hls) hTy
  tyCast (app_const (steps ss) r ls).symm
    (app_instantiateLevels_memberOf hE hres (steps ss) hlen hls).symm node

/-- A `pi` node. The codomain typing is already under the shifted skeleton.
`imax` commutes with `appLevel`; the binder shift does not change a level. -/
def tyPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (A B : Expr Nat) (u v : Level)
    (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) B)
        (.sort (Skels.appLevel (ss.map Skel.shift) v))) :
    TyP E n Γ (Skels.app ss (.pi A B)) (Skels.app ss (.sort (.imax u v))) :=
  let node := TyP.pi E n Γ (Skels.app ss A) (Skels.appLevel ss u)
      (Skels.app (ss.map Skel.shift) B) (Skels.appLevel (ss.map Skel.shift) v) hA hB
  tyCast (app_pi ss A B).symm
    (by
      rw [appLevel_shift ss v]
      rw [← appLevel_imax ss u v]
      rw [← app_sort ss (.imax u v)])
    node

/-- A `lam` node. Domain, body, and codomain are already retyped. -/
def tyLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A body B : Expr Nat) (u v : Level) (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hbody : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) B)
        (.sort (Skels.appLevel (ss.map Skel.shift) v))) :
    TyP E n Γ (Skels.app ss (.lam A body)) (Skels.app ss (.pi A B)) :=
  let node := TyP.lam E n Γ (Skels.app ss A) (Skels.appLevel ss u)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)
      (Skels.appLevel (ss.map Skel.shift) v) hA hbody hB
  tyCast (app_lam ss A body).symm (app_pi ss A B).symm node

/-- An `app` node. The instantiated codomain is `app_inst0`. -/
def tyApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (f a A B : Expr Nat) (w : Level) (ss : List Skel)
    (hf : TyP E n Γ (Skels.app ss f)
        (.pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)))
    (ha : TyP E n Γ (Skels.app ss a) (Skels.app ss A))
    (hT : TyP E n Γ (Skels.app ss (instantiate0 a B)) (.sort (Skels.appLevel ss w))) :
    TyP E n Γ (Skels.app ss (.app f a)) (Skels.app ss (instantiate0 a B)) :=
  let hTy := tyCast (app_inst0 ss a B) rfl hT
  let node := TyP.app E n Γ (Skels.app ss f) (Skels.app ss a) (Skels.app ss A)
      (Skels.app (ss.map Skel.shift) B) (Skels.appLevel ss w) hf ha hTy
  tyCast (app_app ss f a).symm (app_inst0 ss a B).symm node

/-- A `let` node. The body is under the shifted skeleton; the ascribed type
is `instantiate0`, so it uses `app_inst0` like `app`. -/
def tyLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A value B body : Expr Nat) (u w : Level) (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hv : TyP E n Γ (Skels.app ss value) (Skels.app ss A))
    (hb : TyP E n (.letBinding (Skels.app ss A) (Skels.app ss value) :: Γ)
        (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (hT : TyP E n Γ (Skels.app ss (instantiate0 value B)) (.sort (Skels.appLevel ss w))) :
    TyP E n Γ (Skels.app ss (.letE A value body)) (Skels.app ss (instantiate0 value B)) :=
  let hTy := tyCast (app_inst0 ss value B) rfl hT
  let node := TyP.letE E n Γ (Skels.app ss A) (Skels.appLevel ss u)
      (Skels.app ss value) (Skels.app (ss.map Skel.shift) B)
      (Skels.app (ss.map Skel.shift) body) (Skels.appLevel ss w) hA hv hb hTy
  tyCast (app_letE ss A value body).symm (app_inst0 ss value B).symm node

/-- A `lit` node. The literal is fixed by every step; `natExpand` is too. -/
def tyLit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (ss : List Skel) (hexp : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T)) :
    TyP E n Γ (Skels.app ss (.lit t)) (Skels.app ss T) :=
  let hExp := tyCast (app_natExpand ss t) rfl hexp
  let node := TyP.lit E n Γ t (Skels.app ss T) hExp
  tyCast (app_lit ss t).symm rfl node

end Rcic.Syn
