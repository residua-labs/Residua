import rcic.RcicSynCtxSet
import rcic.RcicSynHeadView

/-!
# Syntactic sortRow, build step 3l — renaming under a transport skeleton

`research/rcic/semantic/S3_ES_ARMS.md` §13. `tyCctxAt` is not yet this
module. What is here is the renaming a non-commuting transport forces:
`c > k` is not `TyP.wk` of an inner `setAssump`, so the pending transports
are a skeleton, applied head-innermost, and `foundUnder` says what a lookup
becomes. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## A skeleton of the transports that move a term

The proof-carrying steps come later. Term and context equations depend only
on the indices, so they live on this skeleton. Head is innermost: it is
applied to the term first.
-/

inductive Skel : Type where
  | wk (c : Nat) (d : LocalDecl)
  | esub (j : Nat) (v : Expr Nat)
  | linst (ls : List Level)
  | cctx (p : Nat) (A' : Expr Nat)

def Skel.app1 : Skel → Expr Nat → Expr Nat
  | .wk c _, e => lift c 1 e
  | .esub j v, e => instantiate j (lift 0 j v) e
  | .linst ls, e => instantiateLevels ls e
  | .cctx _ _, e => e

def Skel.ctx1 : Skel → LCtx → LCtx
  | .wk c d, Γ => insertAt d c Γ
  | .esub j v, Γ => substRemove v j Γ
  | .linst ls, Γ => instLvlsCtx ls Γ
  | .cctx p A', Γ => setAssump p A' Γ

def Skel.onDecl : Skel → LocalDecl → LocalDecl
  | .wk c _, d => liftDecl c d
  | .esub j v, d => instDecl j v d
  | .linst ls, d => instLvlsDecl ls d
  | .cctx _ _, d => d

/-- A binder at position 0 pushes every cutoff and every hole one deeper. -/
def Skel.shift : Skel → Skel
  | .wk c d => .wk (c + 1) d
  | .esub j v => .esub (j + 1) v
  | .linst ls => .linst ls
  | .cctx p A' => .cctx (p + 1) A'

def Skels.app : List Skel → Expr Nat → Expr Nat
  | [], e => e
  | s :: ss, e => Skels.app ss (Skel.app1 s e)

def Skels.ctx : List Skel → LCtx → LCtx
  | [], Γ => Γ
  | s :: ss, Γ => Skels.ctx ss (Skel.ctx1 s Γ)

def Skels.onDecl : List Skel → LocalDecl → LocalDecl
  | [], d => d
  | s :: ss, d => Skels.onDecl ss (Skel.onDecl s d)

def Skels.appLevel : List Skel → Level → Level
  | [], l => l
  | .linst ls :: ss, l => Skels.appLevel ss (instLevel ls l)
  | _ :: ss, l => Skels.appLevel ss l

def Skels.appLevels : List Skel → List Level → List Level
  | [], ls => ls
  | .linst ls₀ :: ss, ls => Skels.appLevels ss (ls.map (instLevel ls₀))
  | _ :: ss, ls => Skels.appLevels ss ls

theorem ctx1_shift (s : Skel) (d : LocalDecl) (Γ : LCtx) :
    Skel.ctx1 (Skel.shift s) (d :: Γ) = Skel.onDecl s d :: Skel.ctx1 s Γ := by
  cases s with
  | wk c d0 =>
      simp only [Skel.shift, Skel.ctx1, Skel.onDecl, insertAt_succ_cons]
  | esub j v =>
      simp only [Skel.shift, Skel.ctx1, Skel.onDecl, substRemove_succ_cons]
  | linst ls =>
      simp only [Skel.shift, Skel.ctx1, Skel.onDecl, instLvlsCtx_cons]
  | cctx p A' =>
      simp only [Skel.shift, Skel.ctx1, Skel.onDecl, setAssump_succ]

theorem ctx_shift (d : LocalDecl) :
    (ss : List Skel) → (Γ : LCtx) →
      Skels.ctx (ss.map Skel.shift) (d :: Γ) =
        Skels.onDecl ss d :: Skels.ctx ss Γ
  | [], _ => rfl
  | s :: ss, Γ => by
      rw [List.map_cons, Skels.ctx, ctx1_shift, Skels.ctx, Skels.onDecl]
      exact ctx_shift (Skel.onDecl s d) ss (Skel.ctx1 s Γ)

theorem get?_shift (ss : List Skel) (d : LocalDecl) (Γ : LCtx) (k : Nat) :
    (Skels.ctx (ss.map Skel.shift) (d :: Γ)).get? (k + 1) =
      (Skels.ctx ss Γ).get? k := by
  rw [ctx_shift d ss Γ, List.get?_cons_succ]

theorem drop_shift (ss : List Skel) (d : LocalDecl) (Γ : LCtx) (k : Nat) :
    (Skels.ctx (ss.map Skel.shift) (d :: Γ)).drop (k + 2) =
      (Skels.ctx ss Γ).drop (k + 1) := by
  rw [ctx_shift d ss Γ, List.drop_succ_cons]

theorem onDecl_assumption :
    (ss : List Skel) → (A : Expr Nat) →
      Skels.onDecl ss (.assumption A) = .assumption (Skels.app ss A)
  | [], A => rfl
  | .wk c d :: ss, A => by
      simp only [Skels.onDecl, Skel.onDecl, liftDecl, Skels.app, Skel.app1]
      exact onDecl_assumption ss _
  | .esub j v :: ss, A => by
      simp only [Skels.onDecl, Skel.onDecl, instDecl, Skels.app, Skel.app1]
      exact onDecl_assumption ss _
  | .linst ls :: ss, A => by
      simp only [Skels.onDecl, Skel.onDecl, instLvlsDecl, Skels.app, Skel.app1]
      exact onDecl_assumption ss _
  | .cctx p A' :: ss, A => by
      simp only [Skels.onDecl, Skel.onDecl, Skels.app, Skel.app1]
      exact onDecl_assumption ss _

theorem app_pi :
    (ss : List Skel) → (A B : Expr Nat) →
      Skels.app ss (.pi A B) =
        .pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)
  | [], _, _ => rfl
  | .wk _ _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, lift]
      rw [app_pi ss]
  | .esub j v :: ss, A, B => by
      have hrep :
          lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiate, hrep]
      rw [app_pi ss]
  | .linst _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiateLevels]
      rw [app_pi ss]
  | .cctx _ _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [app_pi ss]

theorem app_lam :
    (ss : List Skel) → (A B : Expr Nat) →
      Skels.app ss (.lam A B) =
        .lam (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)
  | [], _, _ => rfl
  | .wk _ _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, lift]
      rw [app_lam ss]
  | .esub j v :: ss, A, B => by
      have hrep :
          lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiate, hrep]
      rw [app_lam ss]
  | .linst _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiateLevels]
      rw [app_lam ss]
  | .cctx _ _ :: ss, A, B => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [app_lam ss]

theorem app_app :
    (ss : List Skel) → (f a : Expr Nat) →
      Skels.app ss (.app f a) = .app (Skels.app ss f) (Skels.app ss a)
  | [], _, _ => rfl
  | .wk _ _ :: ss, f, a => by
      simp only [Skels.app, Skel.app1, lift]
      rw [app_app ss]
  | .esub _ _ :: ss, f, a => by
      simp only [Skels.app, Skel.app1, instantiate]
      rw [app_app ss]
  | .linst _ :: ss, f, a => by
      simp only [Skels.app, Skel.app1, instantiateLevels]
      rw [app_app ss]
  | .cctx _ _ :: ss, f, a => by
      simp only [Skels.app, Skel.app1]
      rw [app_app ss]

theorem app_letE :
    (ss : List Skel) → (A v b : Expr Nat) →
      Skels.app ss (.letE A v b) =
        .letE (Skels.app ss A) (Skels.app ss v)
          (Skels.app (ss.map Skel.shift) b)
  | [], _, _, _ => rfl
  | .wk _ _ :: ss, A, v, b => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, lift]
      rw [app_letE ss]
  | .esub j r :: ss, A, v, b => by
      have hrep :
          lift 0 1 (lift 0 j r) = lift 0 (j + 1) r :=
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) r
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiate, hrep]
      rw [app_letE ss]
  | .linst _ :: ss, A, v, b => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiateLevels]
      rw [app_letE ss]
  | .cctx _ _ :: ss, A, v, b => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [app_letE ss]

theorem app_sort :
    (ss : List Skel) → (l : Level) →
      Skels.app ss (.sort l) = .sort (Skels.appLevel ss l)
  | [], _ => rfl
  | .wk _ _ :: ss, l => by
      simp only [Skels.app, Skel.app1, lift, Skels.appLevel]
      rw [app_sort ss]
  | .esub _ _ :: ss, l => by
      simp only [Skels.app, Skel.app1, instantiate, Skels.appLevel]
      rw [app_sort ss]
  | .linst ls :: ss, l => by
      simp only [Skels.app, Skel.app1, instantiateLevels, Skels.appLevel]
      rw [app_sort ss]
  | .cctx _ _ :: ss, l => by
      simp only [Skels.app, Skel.app1, Skels.appLevel]
      rw [app_sort ss]

theorem app_const :
    (ss : List Skel) → (r : Nat) → (ls : List Level) →
      Skels.app ss (.const r ls) = .const r (Skels.appLevels ss ls)
  | [], _, _ => rfl
  | .wk _ _ :: ss, r, ls => by
      simp only [Skels.app, Skel.app1, lift, Skels.appLevels]
      rw [app_const ss]
  | .esub _ _ :: ss, r, ls => by
      simp only [Skels.app, Skel.app1, instantiate, Skels.appLevels]
      rw [app_const ss]
  | .linst ls₀ :: ss, r, ls => by
      simp only [Skels.app, Skel.app1, instantiateLevels, Skels.appLevels]
      rw [app_const ss]
  | .cctx _ _ :: ss, r, ls => by
      simp only [Skels.app, Skel.app1, Skels.appLevels]
      rw [app_const ss]

theorem app_lit :
    (ss : List Skel) → (t : Nat) → Skels.app ss (.lit t) = .lit t
  | [], _ => rfl
  | .wk _ _ :: ss, t => by
      simp only [Skels.app, Skel.app1, lift]
      rw [app_lit ss]
  | .esub _ _ :: ss, t => by
      simp only [Skels.app, Skel.app1, instantiate]
      rw [app_lit ss]
  | .linst _ :: ss, t => by
      simp only [Skels.app, Skel.app1, instantiateLevels]
      rw [app_lit ss]
  | .cctx _ _ :: ss, t => by
      simp only [Skels.app, Skel.app1]
      rw [app_lit ss]

/-- `app` passes through `instantiate 0`. The body is shifted one binder. -/
theorem app_inst0 :
    (ss : List Skel) → (v e : Expr Nat) →
      Skels.app ss (instantiate 0 v e) =
        instantiate 0 (Skels.app ss v) (Skels.app (ss.map Skel.shift) e)
  | [], _, _ => rfl
  | .wk c _ :: ss, v, e => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [lift_instantiate_low 1 c 0 v (Nat.zero_le c), app_inst0 ss]
  | .esub j r :: ss, v, e => by
      have hcomp :=
        instantiate_instantiate 0 j v (lift 0 j r) (Nat.zero_le j) e
      have hrep :
          lift 0 1 (lift 0 j r) = lift 0 (j + 1) r :=
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) r
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, hcomp, hrep]
      rw [app_inst0 ss]
  | .linst ls :: ss, v, e => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [instantiateLevels_instantiate ls e 0 v, app_inst0 ss]
  | .cctx _ _ :: ss, v, e => by
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [app_inst0 ss]

theorem app_natExpand :
    (ss : List Skel) → (t : Nat) → Skels.app ss (natExpand t) = natExpand t
  | [], _ => rfl
  | .wk c _ :: ss, t => by
      simp only [Skels.app, Skel.app1]
      rw [natExpand_lift c 1 t, app_natExpand ss]
  | .esub j v :: ss, t => by
      simp only [Skels.app, Skel.app1]
      rw [natExpand_instantiate j (lift 0 j v) t, app_natExpand ss]
  | .linst ls :: ss, t => by
      simp only [Skels.app, Skel.app1]
      rw [instantiateLevels_natExpand ls t, app_natExpand ss]
  | .cctx _ _ :: ss, t => by
      simp only [Skels.app, Skel.app1]
      rw [app_natExpand ss]

theorem eq_cons_of_get?_zero {Γ : LCtx} {d : LocalDecl}
    (h : Γ.get? 0 = some d) : Γ = d :: Γ.drop 1 := by
  match Γ with
  | [] => simp [List.get?] at h
  | _ :: _ =>
      simp [List.get?] at h
      exact h ▸ rfl

/-- `setAssump` overwrites the stored declaration, whatever it was. A lookup
that existed at `i` becomes `lift 0 (i + 1)` of the new stored type. -/
theorem lookupType_setAssump_at (A' : Expr Nat) :
    (Γ : LCtx) → (i : Nat) → {A : Expr Nat} → lookupType Γ i = some A →
      lookupType (setAssump i A' Γ) i = some (lift 0 (i + 1) A')
  | [], _, _, h => by
      unfold lookupType at h
      rw [List.get?_nil] at h
      cases h
  | _ :: _, 0, _, _ => by
      rw [setAssump_zero, lookupType, List.get?_cons_zero]
  | d :: Γ, i + 1, _, h => by
      rw [lookupType_cons_succ] at h
      cases hlu : lookupType Γ i with
      | none =>
          rw [hlu, Option.map_none'] at h
          cases h
      | some _ =>
          rw [hlu, Option.map_some'] at h
          cases h
          rw [setAssump_succ, lookupType_cons_succ,
            lookupType_setAssump_at A' Γ i hlu, Option.map_some']
          exact congrArg some
            (lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) A')

theorem lookupType_instLvlsCtx_some (ls : List Level) {Γ : LCtx} {i : Nat}
    {A : Expr Nat} (h : lookupType Γ i = some A) :
    lookupType (instLvlsCtx ls Γ) i = some (instantiateLevels ls A) := by
  rw [lookupType_instLvlsCtx, h, Option.map_some']

theorem lift_bvar_lt {c i : Nat} (hi : i < c) :
    lift c 1 (Expr.bvar i : Expr Nat) = .bvar i := by
  simp only [lift]
  rw [if_neg (Nat.not_le.mpr hi)]

theorem lift_bvar_ge {c i : Nat} (hi : c ≤ i) :
    lift c 1 (Expr.bvar i : Expr Nat) = .bvar (i + 1) := by
  simp only [lift]
  rw [if_pos hi]

theorem instantiate_bvar_lt {j i : Nat} {r : Expr Nat} (hi : i < j) :
    instantiate j r (Expr.bvar i : Expr Nat) = .bvar i := by
  simp only [instantiate]
  rw [if_neg (Nat.ne_of_lt hi), if_neg (Nat.not_lt.mpr (Nat.le_of_lt hi))]

theorem instantiate_bvar_gt {j i : Nat} {r : Expr Nat} (hj : j < i) :
    instantiate j r (Expr.bvar i : Expr Nat) = .bvar (i - 1) := by
  simp only [instantiate]
  rw [if_neg (Nat.ne_of_gt hj), if_pos hj]

theorem instantiate_bvar_eq (j : Nat) (r : Expr Nat) :
    instantiate j r (Expr.bvar j : Expr Nat) = r := by
  unfold instantiate
  have hpos : (j = j) := rfl
  rw [if_pos hpos]

/-- What a lookup becomes under a skeleton.
`keep`: the index was renamed and the lookup is the renamed type.
`hit`: an `esub` wrote over this index; the caller supplies the replacement.
`retype`: a `cctx` changed the stored type. `ty` is still the renamed old
lookup; the new lookup is `B`. -/
inductive Found (Γf : LCtx) (ty : Expr Nat) : Type where
  | keep (i : Nat) (h : lookupType Γf i = some ty)
  | hit (j : Nat) (v : Expr Nat)
  | retype (i : Nat) (B : Expr Nat) (h : lookupType Γf i = some B)

/-- The lookup was already replaced by a newer type `newTy`. Report that as
a retype against the original renamed type, unless a later `esub` erased
the variable. -/
def Found.retypeOf {Γf : LCtx} {newTy : Expr Nat} (oldTy : Expr Nat) :
    Found Γf newTy → Found Γf oldTy
  | .keep i h => .retype i newTy h
  | .hit j v => .hit j v
  | .retype i B h => .retype i B h

def foundUnder :
    (ss : List Skel) → (i : Nat) → (A : Expr Nat) → (Γ : LCtx) →
      lookupType Γ i = some A → Found (Skels.ctx ss Γ) (Skels.app ss A)
  | [], i, _, _, h => .keep i h
  | .wk c d :: ss, i, A, Γ, h =>
      if hi : i < c then
        foundUnder ss i (lift c 1 A) (insertAt d c Γ) (lookupType_insertAt_lt d hi h)
      else
        foundUnder ss (i + 1) (lift c 1 A) (insertAt d c Γ)
          (lookupType_insertAt_ge d (Nat.le_of_not_lt hi) h)
  | .esub j v :: ss, i, A, Γ, h =>
      if hi : i < j then
        foundUnder ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
          (lookupType_substRemove_lt hi h)
      else if hj : j < i then
        foundUnder ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
          (lookupType_substRemove_gt hj h)
      else
        .hit j v
  | .linst ls :: ss, i, A, Γ, h =>
      foundUnder ss i (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (lookupType_instLvlsCtx_some ls h)
  | .cctx p A' :: ss, i, A, Γ, h =>
      if hi : i = p then
        Found.retypeOf (Skels.app ss A)
          (foundUnder ss p (lift 0 (p + 1) A') (setAssump p A' Γ)
            (lookupType_setAssump_at A' Γ p (hi ▸ h)))
      else
        foundUnder ss i A (setAssump p A' Γ) (lookupType_setAssump_ne hi h)

end Rcic.Syn
