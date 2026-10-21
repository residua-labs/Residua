/-
RCIC level calculus — the `instantiateLevels` commutation infrastructure
for 02 §5's FOURTH structural operation, the level analogue of
`RcicSubstCalc`'s lift/instantiate development.

INFRASTRUCTURE, not interface mechanization (00 §20.6): the definitions
`levelParamSubst` / `instLevel` / `instantiateLevels` live in
`RcicDeclarative` (the judgments mention them); their lemmas live here so
that `RcicSubstCalc`'s M-002a pin ("every definition in these statements
is the pinned entry set of RcicDeclarative's carrier guards") stays exact
and so the downstream waves are file-disjoint.

THE FALSE LEMMA THIS FILE REFUSES (00 §20.6, tripwire): there is no
unmapped-args `applyTel` commutation
`applyTel args (instantiateLevels ls T) = (applyTel args T).map (instantiateLevels ls)`.
`applyTel (a :: as) (.pi A B) = applyTel as (instantiate0 a B)`, so the two
sides differ by exactly `instantiateLevels ls a` versus `a`. Only the
MAPPED-args form below is true; a proof of the unmapped form is a proof of
something false and is bounced on sight.

PLACEMENT MEASURED, not chosen (two lemmas of 00 §20.6's list cannot live
here, because the definitions they speak about are DOWNSTREAM of this file
in the import DAG; they land with their own file's wave):
  * `exprSize_instantiateLevels` — `exprSize` is defined in
    `RcicParRedWeight`, which imports `RcicParRedCore`; it belongs there.
  * `instantiateLevels_subst_closed` — its proof needs
    `lift_id_instantiate`, which is defined in `RcicEnv`; it belongs there
    as a corollary of `instantiateLevels_closed` below.
Everything else on the list is stated and proved here.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

/-! ## Boolean plumbing (self-contained; no `simp` set is trusted) -/

theorem boolAnd_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact Bool.noConfusion h

theorem boolAnd_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-! ## §5 defining equations of `instLevel` (all `rfl`; they exist so no
proof below has to unfold `lvlSubst` and `levelParamSubst` by hand) -/

theorem instLevel_zero (ls : List Level) : instLevel ls .zero = .zero := rfl

theorem instLevel_succ (ls : List Level) (l : Level) :
    instLevel ls (.succ l) = .succ (instLevel ls l) := rfl

theorem instLevel_max (ls : List Level) (a b : Level) :
    instLevel ls (.max a b) = .max (instLevel ls a) (instLevel ls b) := rfl

theorem instLevel_imax (ls : List Level) (a b : Level) :
    instLevel ls (.imax a b) = .imax (instLevel ls a) (instLevel ls b) := rfl

/-- The ONLY point where the level list is read; identity out of range
(02 §8: arity mismatch is REFUSED upstream, never repaired here). -/
theorem instLevel_param (ls : List Level) (i : Nat) :
    instLevel ls (.param i) = (ls[i]?).getD (.param i) := rfl

/-! ## L0 — level algebra -/

/-- DT-002's `eval_lvlSubst` at `σ := levelParamSubst ls`, verbatim: this
is the whole reason `instLevel` is defined THROUGH `lvlSubst`. -/
theorem eval_instLevel (ls : List Level) (ρ : Nat → Option Nat) (l : Level) :
    eval ρ (instLevel ls l) = eval (fun i => eval ρ ((ls[i]?).getD (.param i))) l :=
  eval_lvlSubst (levelParamSubst ls) ρ l

/-- §2 `eval` only ever reads ρ at `.param` leaves. -/
theorem eval_congr_val {ρ₁ ρ₂ : Nat → Option Nat} (h : ∀ i, ρ₁ i = ρ₂ i) :
    (l : Level) → eval ρ₁ l = eval ρ₂ l
  | .zero => rfl
  | .succ l => by simp only [eval, eval_congr_val h l]
  | .max a b => by simp only [eval, eval_congr_val h a, eval_congr_val h b]
  | .imax a b => by simp only [eval, eval_congr_val h a, eval_congr_val h b]
  | .param i => h i

/-- Instantiating by the empty list is the identity — NO side condition.
This is what leaves every arity-0 member (04's axiom / definition /
theorem / opaque) level-inert by PROOF rather than by convention. -/
theorem instLevel_nil (l : Level) : instLevel [] l = l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [instLevel_succ, ih]
  | max a b iha ihb => rw [instLevel_max, iha, ihb]
  | imax a b iha ihb => rw [instLevel_imax, iha, ihb]
  | param i => rw [instLevel_param, List.getElem?_nil]; rfl

theorem instLevel_nil_map : (ms : List Level) → ms.map (instLevel []) = ms
  | [] => rfl
  | m :: t => by rw [List.map_cons, instLevel_nil m, instLevel_nil_map t]

theorem eqNList_length : (ls ls' : List Level) → eqNList ls ls' →
    ls.length = ls'.length
  | [], [], _ => rfl
  | _ :: t, _ :: t', h => congrArg Nat.succ (eqNList_length t t' (And.right h))
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- Listwise `=ₙ` transported to the point read by `levelParamSubst`, at
an arbitrary COMMON default. The default must be generalized: the caller
uses `.param i`, and the `i+1` recursion step would otherwise be asked for
`.param (i+1)` on one side and `.param i` on the other. -/
theorem eqNList_getD : (i : Nat) → (ls ls' : List Level) → eqNList ls ls' →
    (d : Level) → eqN ((ls[i]?).getD d) ((ls'[i]?).getD d)
  | _, [], [], _, _ => fun _ => rfl
  | 0, _ :: _, _ :: _, h, d => by
      simp only [List.getElem?_cons_zero]
      exact And.left h
  | i + 1, _ :: t, _ :: t', h, d => by
      simp only [List.getElem?_cons_succ]
      exact eqNList_getD i t t' (And.right h) d
  | _, [], _ :: _, h, _ => False.elim h
  | _, _ :: _, [], h, _ => False.elim h

/-- The σ-side congruence: fixed level, extensionally equal level LISTS.
NOT DT-002, which is the l-side congruence (fixed σ, `eqN a b`); the two
are duals sharing only `eval_lvlSubst`. -/
theorem instLevel_eqNList {ls ls' : List Level} (h : eqNList ls ls') (l : Level) :
    eqN (instLevel ls l) (instLevel ls' l) := by
  intro ρ
  rw [eval_instLevel, eval_instLevel]
  exact eval_congr_val (fun i => eqNList_getD i ls ls' h (.param i) ρ) l

theorem instLevel_eqNList_map {ls ls' : List Level} (h : eqNList ls ls') :
    (ms : List Level) → eqNList (ms.map (instLevel ls)) (ms.map (instLevel ls'))
  | [] => True.intro
  | m :: t => ⟨instLevel_eqNList h m, instLevel_eqNList_map h t⟩

/-! ## L0b — IDX-R2 `hopen` supply. The declaration-side transport
`recIdxTySrcWalk_instantiateLevels` (and its `idxSrcTy` / `idxSrcAlign`
siblings) carries a side condition

    hopen : ∀ ls0, levelsOpen ls0 = true →
      levelsOpen (ls0.map (instLevel lvls)) = true

stating that level instantiation preserves `levelsOpen`. That condition
is NOT a new assumption: it follows from `levelsOpen lvls` alone, because
`levelParamSubst` sends every in-range `param i` to `lvls[i]` (open by
hypothesis) and leaves every out-of-range `param i` visible (open). This
is the piece of the IDX-R2 `n = 0` supply that is a level-algebra fact;
the remaining piece — `levelsOpen w.ls` itself — is read off the redex's
own typing (`hT`). -/

/-- `levelsOpen` is a membership predicate on the list's elements. -/
theorem levelOpen_of_mem (ls : List Level) (h : levelsOpen ls = true) :
    (l : Level) → l ∈ ls → levelOpen l = true
  | l, hl => by
      induction ls with
      | nil => cases hl
      | cons a t ih =>
          simp only [levelsOpen, Bool.and_eq_true] at h
          rcases List.mem_cons.mp hl with rfl | hl
          · exact h.1
          · exact ih h.2 hl

/-- `eval (fun _ => none)` of an open list's in-range substitution target
is `none`: in range it is `eval` of an open element, out of range it is
the read-off `param`, whose empty valuation is `none`. -/
theorem eval_levelParamSubst_param_none (lvls : List Level)
    (h : levelsOpen lvls = true) (i : Nat) :
    eval (fun _ => none) (levelParamSubst lvls (.param i)) = none := by
  cases hget : lvls[i]? with
  | none => simp only [levelParamSubst, hget, Option.getD_none, eval]
  | some a =>
      have ha : a ∈ lvls := List.mem_iff_getElem?.mpr ⟨i, hget⟩
      have hsub : levelParamSubst lvls (.param i) = a := by
        simp only [levelParamSubst, hget, Option.getD_some]
      rw [hsub]
      exact levelOpen_eval (levelOpen_of_mem lvls h a ha)

/-- IDX-R2: level instantiation preserves `levelOpen` when the
instantiation list is itself open. -/
theorem levelOpen_instLevel (lvls : List Level) (h : levelsOpen lvls = true)
    (l : Level) : levelOpen (instLevel lvls l) = levelOpen l := by
  have hev : eval (fun _ => none) (instLevel lvls l) = eval (fun _ => none) l := by
    rw [instLevel, eval_lvlSubst]
    exact eval_congr_val (fun i => eval_levelParamSubst_param_none lvls h i) l
  simp only [levelOpen, hev]

/-- IDX-R2: listwise version of `levelOpen_instLevel`. -/
theorem levelsOpen_map_instLevel (lvls : List Level) (h : levelsOpen lvls = true) :
    (ls0 : List Level) → levelsOpen (ls0.map (instLevel lvls)) = levelsOpen ls0
  | [] => rfl
  | a :: t => by
      simp only [List.map_cons, levelsOpen, levelOpen_instLevel lvls h a,
        levelsOpen_map_instLevel lvls h t]

/-- IDX-R2: the EXACT `hopen` side condition of the declaration-side
transport, discharged from `levelsOpen lvls`. This is what makes the
instance-view openness rest on a single supply — `levelsOpen w.ls` from
the redex's typing — rather than on a second hypothesis. -/
theorem hopen_of_levelsOpen (lvls : List Level) (h : levelsOpen lvls = true) :
    ∀ ls0, levelsOpen ls0 = true →
      levelsOpen (ls0.map (instLevel lvls)) = true :=
  fun ls0 h0 => by rw [levelsOpen_map_instLevel lvls h ls0]; exact h0

/-! IDX-R2 controls: the `hopen` supply's footprint and its two
read-offs. -/
#eval (if levelOpen (instLevel [.param 7] (.param 0)) = true then 0
  else panic "pin: open list keeps a param open")
#eval (if levelOpen (instLevel [.zero] (.param 0)) = false then 0
  else panic "pin: open list is required (ground list grounds the param)")
#eval (if levelOpen (instLevel [.param 7] (.zero)) = false then 0
  else panic "pin: closed level stays closed")
#print axioms levelOpen_of_mem
#print axioms eval_levelParamSubst_param_none
#print axioms levelOpen_instLevel
#print axioms levelsOpen_map_instLevel
#print axioms hopen_of_levelsOpen

/-! ## L1 — level boundedness and `take`

Level-boundedness (`levelBounded` / `levelsBounded` / `exprLevelsBounded`) lives in
`RcicDeclarative` since GLM-2 (single owner; the typed judgment's `const` rule reads
it and `RcicTypedJ` must not force a cycle through this file). This section keeps
its lemmas; the names resolve transitively through `RcicDeclarative`. -/

/-- A term closed at `c` is fixed by lifting at every greater cutoff. -/
theorem lift_eq_of_exprClosedAt_le {c d : Nat} {e : Expr Nat}
    (h : exprClosedAt c e = true) (hcd : c ≤ d) : lift d 1 e = e := by
  induction e generalizing c d with
  | bvar i =>
      simp only [exprClosedAt] at h
      have hi : i < c := of_decide_eq_true h
      exact if_neg (Nat.not_le.mpr (Nat.lt_of_lt_of_le hi hcd))
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f a ihf iha =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihf h.1 hcd, iha h.2 hcd]
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hcd, ihB h.2 (Nat.succ_le_succ hcd)]
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hcd, ihB h.2 (Nat.succ_le_succ hcd)]
  | letE A v B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hv⟩, hb⟩ := h
      simp only [lift, ihA ha hcd, ihv hv hcd,
        ihB hb (Nat.succ_le_succ hcd)]

/-- A closed term is fixed by lifting at every cutoff. -/
theorem lift_id_of_exprClosedAt_zero {e : Expr Nat}
    (h : exprClosedAt 0 e = true) : ∀ k, lift k 1 e = e :=
  fun k => lift_eq_of_exprClosedAt_le h (Nat.zero_le k)

/-- The constants a source names as `.constNotFam`. -/
def idxSrcConsts : IdxSrc → List Nat
  | .constNotFam r => [r]
  | .app sf sa => idxSrcConsts sf ++ idxSrcConsts sa
  | _ => []

/-- All `.constNotFam` constants named by a walk's sources. -/
def idxSrcConstsAll (pss : List (List IdxSrc)) : List Nat :=
  pss.flatMap (fun ss => ss.flatMap idxSrcConsts)

/-- The members that a walk's sources read are closed for the σ stage. -/
def SrcMembersClosed (E : ResolvedEnv) (rs : List Nat) : Prop :=
  ∀ r ∈ rs, ∀ m, E.members r = some m →
    ∀ k, lift k 1 m.mtype = m.mtype

/-- The members that a walk's sources read are level-bounded for the L stage. -/
def SrcMembersBounded (E : ResolvedEnv) (rs : List Nat) : Prop :=
  ∀ r ∈ rs, ∀ m, E.members r = some m →
    exprLevelsBounded m.arity m.mtype = true

/-- The members that a walk's sources read are view-stable: closed (σ stage) and level-bounded (L stage). -/
def SrcMembersStable (E : ResolvedEnv) (rs : List Nat) : Prop :=
  SrcMembersClosed E rs ∧ SrcMembersBounded E rs

/-- Decidable form, for the admission Bool (S1-d2). A missing member fails closed. -/
def srcMembersStableB (E : ResolvedEnv) (rs : List Nat) : Bool :=
  rs.all fun r =>
    match E.members r with
    | some m => exprClosedAt 0 m.mtype && exprLevelsBounded m.arity m.mtype
    | none => false

theorem srcMembersStable_of_B {E : ResolvedEnv} {rs : List Nat}
    (h : srcMembersStableB E rs = true) : SrcMembersStable E rs := by
  have hboth : ∀ r ∈ rs, ∀ m, E.members r = some m →
      (∀ k, lift k 1 m.mtype = m.mtype) ∧
        exprLevelsBounded m.arity m.mtype = true := by
    intro r hr m hm
    simp only [srcMembersStableB, List.all_eq_true] at h
    have hb := h r hr
    simp only [hm, Bool.and_eq_true] at hb
    exact ⟨lift_id_of_exprClosedAt_zero hb.1, hb.2⟩
  exact ⟨fun r hr m hm => (hboth r hr m hm).1,
    fun r hr m hm => (hboth r hr m hm).2⟩

theorem srcMembersStable_hext {E E' : ResolvedEnv} {rs : List Nat}
    (h : srcMembersStableB E rs = true)
    (hext : ∀ r' m', E.members r' = some m' → E'.members r' = some m') :
    SrcMembersStable E' rs := by
  have hboth : ∀ r ∈ rs, ∀ m', E'.members r = some m' →
      (∀ k, lift k 1 m'.mtype = m'.mtype) ∧
        exprLevelsBounded m'.arity m'.mtype = true := by
    intro r hr m' hm'
    simp only [srcMembersStableB, List.all_eq_true] at h
    have hb := h r hr
    cases hm : E.members r with
    | none =>
        simp only [hm] at hb
        nomatch hb
    | some m =>
        have hmE' := hext r m hm
        rw [hm'] at hmE'
        have hmm : m' = m := Option.some.inj hmE'
        subst m'
        simp only [hm, Bool.and_eq_true] at hb
        exact ⟨lift_id_of_exprClosedAt_zero hb.1, hb.2⟩
  exact ⟨fun r hr m hm => (hboth r hr m hm).1,
    fun r hr m hm => (hboth r hr m hm).2⟩

theorem srcMembersClosed_of_envClosed {E : ResolvedEnv} {rs : List Nat}
    (hcl : EnvClosed E) : SrcMembersClosed E rs := by
  intro r _ m hm
  exact (hcl r m hm).1

theorem srcMembersBounded_of_global {E : ResolvedEnv} {rs : List Nat}
    (hbound : ∀ r m, E.members r = some m →
      exprLevelsBounded m.arity m.mtype = true) :
    SrcMembersBounded E rs := by
  intro r _ m hm
  exact hbound r m hm

/-- Below the cut point, `take` does not move the lookup. Note there is NO
`k ≤ ls.length` side condition: out of range both sides return `none`. -/
theorem getElem?_take_lt : (k : Nat) → (l : List Level) → (i : Nat) → i < k →
    (l.take k)[i]? = l[i]?
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ + 1, [], _, _ => rfl
  | _ + 1, a :: t, 0, _ => by
      show (a :: t.take _)[0]? = (a :: t)[0]?
      rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
  | k + 1, a :: t, i + 1, hi => by
      show (a :: t.take k)[i + 1]? = (a :: t)[i + 1]?
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
      exact getElem?_take_lt k t i (Nat.lt_of_succ_lt_succ hi)

theorem instLevel_take (k : Nat) (ls : List Level) :
    (l : Level) → levelBounded k l = true →
    instLevel ls l = instLevel (ls.take k) l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih => intro hb; rw [instLevel_succ, instLevel_succ, ih hb]
  | max a b iha ihb =>
      intro hb
      rw [instLevel_max, instLevel_max, iha (boolAnd_left hb), ihb (boolAnd_right hb)]
  | imax a b iha ihb =>
      intro hb
      rw [instLevel_imax, instLevel_imax, iha (boolAnd_left hb), ihb (boolAnd_right hb)]
  | param i =>
      intro hb
      rw [instLevel_param, instLevel_param,
        getElem?_take_lt k ls i (of_decide_eq_true hb)]

theorem instLevel_take_map (k : Nat) (ls : List Level) :
    (ms : List Level) → levelsBounded k ms = true →
    ms.map (instLevel ls) = ms.map (instLevel (ls.take k))
  | [], _ => rfl
  | m :: t, hb => by
      rw [List.map_cons, List.map_cons, instLevel_take k ls m (boolAnd_left hb),
        instLevel_take_map k ls t (boolAnd_right hb)]

/-- 00 §20.6 STORED-TYPE VIEWS: this is what lets a witness be WRITTEN at
`w.ls` and READ at `w.ls.take nU`. -/
theorem instantiateLevels_take (k : Nat) (ls : List Level) :
    (e : Expr Nat) → exprLevelsBounded k e = true →
    instantiateLevels ls e = instantiateLevels (ls.take k) e := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | sort l =>
      intro hb
      simp only [instantiateLevels, instLevel_take k ls l hb]
  | const r ms =>
      intro hb
      simp only [instantiateLevels, instLevel_take_map k ls ms hb]
  | app f x ihf ihx =>
      intro hb
      simp only [instantiateLevels, ihf (boolAnd_left hb), ihx (boolAnd_right hb)]
  | lam a b iha ihb =>
      intro hb
      simp only [instantiateLevels, iha (boolAnd_left hb), ihb (boolAnd_right hb)]
  | pi a b iha ihb =>
      intro hb
      simp only [instantiateLevels, iha (boolAnd_left hb), ihb (boolAnd_right hb)]
  | letE a v b iha ihv ihb =>
      intro hb
      simp only [instantiateLevels,
        iha (boolAnd_left (boolAnd_left hb)),
        ihv (boolAnd_right (boolAnd_left hb)),
        ihb (boolAnd_right hb)]
  | lit t => intro _; rfl

/-- The highest-leverage lemma of the segment: it discharges every arity-0
member and every level-free fixture with NO hypothesis. -/
theorem instantiateLevels_nil : (e : Expr Nat) → instantiateLevels [] e = e := by
  intro e
  induction e with
  | bvar i => rfl
  | sort l => simp only [instantiateLevels, instLevel_nil]
  | const r ms => simp only [instantiateLevels, instLevel_nil_map]
  | app f x ihf ihx => simp only [instantiateLevels, ihf, ihx]
  | lam a b iha ihb => simp only [instantiateLevels, iha, ihb]
  | pi a b iha ihb => simp only [instantiateLevels, iha, ihb]
  | letE a v b iha ihv ihb => simp only [instantiateLevels, iha, ihv, ihb]
  | lit t => rfl

/-- 05 §2 / 00 §20.6: instantiating the CANONICAL universe vector
`[param 0, …, param (k-1)]` — the vector every stored family occurrence
carries — with `ls` yields `ls.take k`. The `k ≤ ls.length` side
condition is real (out of range `instLevel` keeps `param i` visible
while `take` drops the slot) and is supplied at every iota site by
`HasTy.const`'s `hlen` together with 05 §3's group arity coherence
(`famMember.arity ≤ recMember.arity = ls.length`). This is the bridge
from the POLYMORPHIC stored head to the redex's own universe list, and
so the reason `hmajorTy` / `ctorResultParamShape` can pin the canonical
vector instead of asserting `ls`. -/
theorem map_instLevel_canonical (k : Nat) (ls : List Level)
    (h : k ≤ ls.length) :
    ((List.range k).map Level.param).map (instLevel ls) = ls.take k := by
  refine List.ext_getElem? (fun i => ?_)
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hi : i < k
  · have hlt : i < ls.length := Nat.lt_of_lt_of_le hi h
    rw [List.getElem?_range hi, List.getElem?_take_of_lt hi,
      List.getElem?_eq_getElem hlt]
    show some (instLevel ls (Level.param i)) = some ls[i]
    rw [instLevel_param, List.getElem?_eq_getElem hlt]
    rfl
  · have hk : k ≤ i := Nat.le_of_not_lt hi
    have h1 : (List.range k)[i]? = none := by
      refine List.getElem?_eq_none ?_
      rw [List.length_range]
      exact hk
    rw [h1, List.getElem?_take_eq_none hk]
    rfl

/-- de Bruijn spines are level-blind: a list built as `bvar (g i)` is
fixed by `instantiateLevels`. Used to push the substitution through
`majorTyExpr` / `recBodyExpr`, whose arguments are pure `bvar`s. -/
theorem map_instantiateLevels_bvars (lvls : List Level) (g : Nat → Nat) :
    (xs : List Nat) →
    (xs.map (fun i => (Expr.bvar (g i) : Expr Nat))).map
        (instantiateLevels lvls) =
      xs.map (fun i => (Expr.bvar (g i) : Expr Nat))
  | [] => rfl
  | a :: t => by
      simp only [List.map_cons, instantiateLevels,
        map_instantiateLevels_bvars lvls g t]

/-! ## L2 — de Bruijn commutation -/

/-- NO cutoff side condition (unlike `lift_instantiate_low/high`):
`instantiateLevels` never reads or writes a `bvar` and never opens a
binder scope, so it commutes with `lift` at every cutoff. -/
theorem lift_instantiateLevels (ls : List Level) (a : Nat) :
    (e : Expr Nat) → (c : Nat) →
    lift c a (instantiateLevels ls e) = instantiateLevels ls (lift c a e) := by
  intro e
  induction e with
  | bvar i =>
      intro c
      by_cases h : c ≤ i
      · simp only [instantiateLevels, lift, if_pos h]
      · simp only [instantiateLevels, lift, if_neg h]
  | sort l => intro c; simp only [instantiateLevels, lift]
  | const r ms => intro c; simp only [instantiateLevels, lift]
  | app f x ihf ihx => intro c; simp only [instantiateLevels, lift, ihf, ihx]
  | lam a' b iha ihb => intro c; simp only [instantiateLevels, lift, iha, ihb]
  | pi a' b iha ihb => intro c; simp only [instantiateLevels, lift, iha, ihb]
  | letE a' v b iha ihv ihb =>
      intro c; simp only [instantiateLevels, lift, iha, ihv, ihb]
  | lit t => intro c; simp only [instantiateLevels, lift]

theorem instantiateLevels_instantiate (ls : List Level) :
    (e : Expr Nat) → (j : Nat) → (v : Expr Nat) →
    instantiateLevels ls (instantiate j v e)
      = instantiate j (instantiateLevels ls v) (instantiateLevels ls e) := by
  intro e
  induction e with
  | bvar i =>
      intro j v
      simp only [instantiateLevels, instantiate]
      by_cases h1 : i = j
      · simp only [if_pos h1]
      · by_cases h2 : j < i
        · simp only [if_neg h1, if_pos h2, instantiateLevels]
        · simp only [if_neg h1, if_neg h2, instantiateLevels]
  | sort l => intro j v; simp only [instantiateLevels, instantiate]
  | const r ms => intro j v; simp only [instantiateLevels, instantiate]
  | app f x ihf ihx =>
      intro j v; simp only [instantiateLevels, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      intro j v
      simp only [instantiateLevels, instantiate, iha, ihb, lift_instantiateLevels]
  | pi a b iha ihb =>
      intro j v
      simp only [instantiateLevels, instantiate, iha, ihb, lift_instantiateLevels]
  | letE a w b iha ihw ihb =>
      intro j v
      simp only [instantiateLevels, instantiate, iha, ihw, ihb, lift_instantiateLevels]
  | lit t => intro j v; simp only [instantiateLevels, instantiate]

theorem instantiateLevels_instantiate0 (ls : List Level) (v e : Expr Nat) :
    instantiateLevels ls (instantiate0 v e)
      = instantiate0 (instantiateLevels ls v) (instantiateLevels ls e) :=
  instantiateLevels_instantiate ls e 0 v

/-- Closedness (04's `envWf_closed` shape) survives level instantiation. -/
theorem instantiateLevels_closed {e : Expr Nat} (h : ∀ c, lift c 1 e = e)
    (ls : List Level) (c : Nat) :
    lift c 1 (instantiateLevels ls e) = instantiateLevels ls e := by
  rw [lift_instantiateLevels, h c]

/-! ## L3 — telescope and spine commutation -/

theorem piCount_instantiateLevels (ls : List Level) (T : Expr Nat) :
    piCount (instantiateLevels ls T) = piCount T := by
  induction T with
  | bvar i => rfl
  | sort l => rfl
  | const r ms => rfl
  | app f x _ _ => rfl
  | lam a b _ _ => rfl
  | pi a b _ ihb => simp only [instantiateLevels, piCount, ihb]
  | letE a v b _ _ _ => rfl
  | lit t => rfl

/-- `peelPis` never substitutes, so the commutation is unconditional. -/
theorem peelPis_instantiateLevels (ls : List Level) :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) →
    peelPis n (instantiateLevels ls T)
      = some (ds.map (instantiateLevels ls), instantiateLevels ls r)
  | 0, T, ds, r, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds hr
      subst hds
      subst hr
      rfl
  | n + 1, .pi A B, ds, r, h => by
      cases hpeel : peelPis n B with
      | none =>
          simp only [peelPis, hpeel] at h
          exact Option.noConfusion h
      | some pr =>
          cases pr with
          | mk ds' r' =>
              simp only [peelPis, hpeel] at h
              injection h with hp
              injection hp with hds hr
              subst hds
              subst hr
              simp only [instantiateLevels, peelPis,
                peelPis_instantiateLevels ls n B hpeel, List.map_cons]
  | _ + 1, .bvar _, _, _, h => Option.noConfusion h
  | _ + 1, .sort _, _, _, h => Option.noConfusion h
  | _ + 1, .const _ _, _, _, h => Option.noConfusion h
  | _ + 1, .app _ _, _, _, h => Option.noConfusion h
  | _ + 1, .lam _ _, _, _, h => Option.noConfusion h
  | _ + 1, .letE _ _ _, _, _, h => Option.noConfusion h
  | _ + 1, .lit _, _, _, h => Option.noConfusion h

theorem foldApps_instantiateLevels (ls : List Level) :
    (xs : List (Expr Nat)) → (f : Expr Nat) →
    instantiateLevels ls (foldApps f xs)
      = foldApps (instantiateLevels ls f) (xs.map (instantiateLevels ls))
  | [], f => rfl
  | x :: t, f => by
      simp only [foldApps, List.map_cons]
      rw [foldApps_instantiateLevels ls t (.app f x)]
      simp only [instantiateLevels]

theorem appsSpine_instantiateLevels (ls : List Level) (e : Expr Nat) :
    appsSpine (instantiateLevels ls e)
      = (instantiateLevels ls (appsSpine e).1,
         (appsSpine e).2.map (instantiateLevels ls)) := by
  induction e with
  | bvar i => rfl
  | sort l => rfl
  | const r ms => rfl
  | app f x ihf _ =>
      simp only [instantiateLevels, appsSpine, ihf, List.map_append,
        List.map_cons, List.map_nil]
  | lam a b _ _ => rfl
  | pi a b _ _ => rfl
  | letE a v b _ _ _ => rfl
  | lit t => rfl

/-- THE MAPPED-ARGS FORM, and the only true one (see the file header). -/
theorem applyTel_instantiateLevels (ls : List Level) :
    (args : List (Expr Nat)) → (T : Expr Nat) →
    applyTel (args.map (instantiateLevels ls)) (instantiateLevels ls T)
      = (applyTel args T).map (instantiateLevels ls)
  | [], _ => rfl
  | a :: as, .pi A B => by
      show applyTel (as.map (instantiateLevels ls))
             (instantiate0 (instantiateLevels ls a) (instantiateLevels ls B))
           = (applyTel as (instantiate0 a B)).map (instantiateLevels ls)
      rw [← instantiateLevels_instantiate0]
      exact applyTel_instantiateLevels ls as (instantiate0 a B)
  | _ :: _, .bvar _ => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const _ _ => rfl
  | _ :: _, .app _ _ => rfl
  | _ :: _, .lam _ _ => rfl
  | _ :: _, .letE _ _ _ => rfl
  | _ :: _, .lit _ => rfl

/-! ## L4 — the `Conv` congruence in the level list

After the 00 §20.6 rule change `.const r ls` and `.const r ls'` no longer
share a type: they are typed at `instantiateLevels ls m.mtype` and
`instantiateLevels ls' m.mtype`. `Conv.consts` is coherent with
`HasTy.const` ONLY through the congruence below, which is why this is
load-bearing rather than a convenience.

Measured about the binder cases: `Conv.lam` / `Conv.pi` take their body
premise in `LocalDecl.assumption A :: Γ` and `Conv.letE` in
`LocalDecl.letBinding A v :: Γ`, where `A`/`v` are the LEFT sides — which
is exactly the context the recursive call is made in. So NO
context-conversion lemma is needed. The derivation uses only
`refl`/`sorts`/`consts` and the four congruences: no `Conv.step`, no
`Conv.eta`, no `Conv.irr`, hence no `EnvWf`, no `CtxWf`, no confluence —
it is outside the F-05b ring. -/

/-! ### L3b — the 05 declaration-shape recognizers are level-blind.

`spineHeadConst` / `directRecConstHead` / `resultConstHead` inspect only
Π structure and head CONSTRUCTORS; `instantiateLevels` changes neither.
These are what let a witness transport re-derive its `hfamTel` /
`hresTel` at the 00 §20.6 instantiated view of the stored constructor
type from the RAW declaration facts, without an
`analyzeFields`-invariance lemma. -/

theorem spineHeadConst_instantiateLevels (ls : List Level) (e : Expr Nat) :
    spineHeadConst (instantiateLevels ls e) = spineHeadConst e := by
  unfold spineHeadConst
  rw [appsSpine_instantiateLevels]
  cases (appsSpine e).1 <;> rfl

theorem directRecConstHead_instantiateLevels (ls : List Level) :
    (ks : List RecKind) → (T : Expr Nat) →
    directRecConstHead ks (instantiateLevels ls T) = directRecConstHead ks T
  | [], _ => rfl
  | .plain :: ks, .pi A B => by
      simp only [instantiateLevels, directRecConstHead,
        directRecConstHead_instantiateLevels ls ks B]
  | .directRec :: ks, .pi A B => by
      simp only [instantiateLevels, directRecConstHead,
        spineHeadConst_instantiateLevels ls A,
        directRecConstHead_instantiateLevels ls ks B]
  | .plain :: _, .bvar _ => rfl
  | .plain :: _, .sort _ => rfl
  | .plain :: _, .const _ _ => rfl
  | .plain :: _, .app _ _ => rfl
  | .plain :: _, .lam _ _ => rfl
  | .plain :: _, .letE _ _ _ => rfl
  | .plain :: _, .lit _ => rfl
  | .directRec :: _, .bvar _ => rfl
  | .directRec :: _, .sort _ => rfl
  | .directRec :: _, .const _ _ => rfl
  | .directRec :: _, .app _ _ => rfl
  | .directRec :: _, .lam _ _ => rfl
  | .directRec :: _, .letE _ _ _ => rfl
  | .directRec :: _, .lit _ => rfl

theorem resultConstHead_instantiateLevels (ls : List Level) :
    (ks : List RecKind) → (T : Expr Nat) →
    resultConstHead ks (instantiateLevels ls T) = resultConstHead ks T
  | [], T => spineHeadConst_instantiateLevels ls T
  | .plain :: ks, .pi A B => by
      simp only [instantiateLevels, resultConstHead,
        resultConstHead_instantiateLevels ls ks B]
  | .directRec :: ks, .pi A B => by
      simp only [instantiateLevels, resultConstHead,
        resultConstHead_instantiateLevels ls ks B]
  | .plain :: _, .bvar i => spineHeadConst_instantiateLevels ls (.bvar i)
  | .plain :: _, .sort l => spineHeadConst_instantiateLevels ls (.sort l)
  | .plain :: _, .const r ms => spineHeadConst_instantiateLevels ls (.const r ms)
  | .plain :: _, .app f x => spineHeadConst_instantiateLevels ls (.app f x)
  | .plain :: _, .lam A b => spineHeadConst_instantiateLevels ls (.lam A b)
  | .plain :: _, .letE A v b => spineHeadConst_instantiateLevels ls (.letE A v b)
  | .plain :: _, .lit t => spineHeadConst_instantiateLevels ls (.lit t)
  | .directRec :: _, .bvar i => spineHeadConst_instantiateLevels ls (.bvar i)
  | .directRec :: _, .sort l => spineHeadConst_instantiateLevels ls (.sort l)
  | .directRec :: _, .const r ms =>
      spineHeadConst_instantiateLevels ls (.const r ms)
  | .directRec :: _, .app f x => spineHeadConst_instantiateLevels ls (.app f x)
  | .directRec :: _, .lam A b => spineHeadConst_instantiateLevels ls (.lam A b)
  | .directRec :: _, .letE A v b =>
      spineHeadConst_instantiateLevels ls (.letE A v b)
  | .directRec :: _, .lit t => spineHeadConst_instantiateLevels ls (.lit t)

def convInstantiateLevels {E : ResolvedEnv} {n : Nat} :
    (T : Expr Nat) → {ls ls' : List Level} → eqNList ls ls' →
    (Γ : LCtx) → Conv E n Γ (instantiateLevels ls T) (instantiateLevels ls' T)
  | .bvar i, _, _, _, Γ => Conv.refl Γ (.bvar i)
  | .sort l, ls, ls', h, Γ =>
      Conv.sorts Γ (instLevel ls l) (instLevel ls' l) (instLevel_eqNList h l)
  | .const r ms, ls, ls', h, Γ =>
      Conv.consts Γ r (ms.map (instLevel ls)) (ms.map (instLevel ls'))
        (instLevel_eqNList_map h ms)
  | .app f x, _, _, h, Γ =>
      Conv.app Γ _ _ _ _ (convInstantiateLevels f h Γ) (convInstantiateLevels x h Γ)
  | .lam A b, ls, _, h, Γ =>
      Conv.lam Γ _ _ _ _ (convInstantiateLevels A h Γ)
        (convInstantiateLevels b h (LocalDecl.assumption (instantiateLevels ls A) :: Γ))
  | .pi A B, ls, _, h, Γ =>
      Conv.pi Γ _ _ _ _ (convInstantiateLevels A h Γ)
        (convInstantiateLevels B h (LocalDecl.assumption (instantiateLevels ls A) :: Γ))
  | .letE A v b, ls, _, h, Γ =>
      Conv.letE Γ _ _ _ _ _ _ (convInstantiateLevels A h Γ)
        (convInstantiateLevels v h Γ)
        (convInstantiateLevels b h
          (LocalDecl.letBinding (instantiateLevels ls A) (instantiateLevels ls v) :: Γ))
  | .lit t, _, _, _, Γ => Conv.refl Γ (.lit t)


/-! ### L5 — 00 §20.7 STAGE L (`X_instantiateLevels`), M-L02 … M-L16.

The INNER half of the admission bundle's two-stage transport: the declared
05 checks are run on a RAW stored type, the `IotaTyping` fields read the
00 §20.6 view `instantiateLevels w.ls (stored type)`, and these lemmas move
a declared `= true` across that view. The OUTER half (`X_instPrefix`) is
00 §20.7 stage σ and lives with its own subject.

DIRECTION (00 §20.7 STAGE L, and the batch's own stop rule). Five of the
sixteen stage-L lemmas are EQUALITIES; the other ELEVEN are FORWARD
implications, `= true → = true`, and the converse must never be assumed:
`instantiateLevels` is NOT injective (`instantiateLevels [zero, zero]
(.sort (param 0)) = instantiateLevels [zero, zero] (.sort (param 1))`), so
a `decide (a = b)` comparison transports declared ⇒ instance only. A proof
here that wants injectivity means the conjunct is SITED wrong, not that the
lemma is too weak. M-L01 (`bvarSpine_instantiateLevels`) is not in this
file: `bvarSpine` is defined DOWNSTREAM of it, in `RcicIota`, so M-L01
lands beside its own subject (00 §20.7 PLACEMENT, D1).

NO GUARDS, unlike the `instantiate` siblings in `RcicIota`. Those carry
`isPiTel` / `directRecConstHead` / `resultConstHead` premises because a
substitution can turn a `bvar` into a `pi` and a spine head into an app —
the M-001 hazard. `instantiateLevels` PRESERVES the head constructor at
every node, so `familyIdx` commutes unconditionally (M-L03) and the walks'
fall-through arms are reached on the same shape on both sides. The two
lemmas that DO carry a premise are M-L15 and M-L16, and it is the SAME one
in both: `hnU : nU ≤ lvls.length`, read (never re-derived) into
`map_instLevel_canonical`.

The three already-present level-blindness equalities
(`spineHeadConst_instantiateLevels`, `directRecConstHead_instantiateLevels`,
`resultConstHead_instantiateLevels`) are CONSUMED by the bundle beside
M-L02; they are not restated here. -/

/-- M-L02. Π-telescope length is level-blind: `instantiateLevels` maps
`.pi` to `.pi` and every other constructor to its own head. An EQUALITY,
the sibling of the three recognizers above. -/
theorem isPiTel_instantiateLevels (lvls : List Level) :
    (n : Nat) → (T : Expr Nat) →
    isPiTel n (instantiateLevels lvls T) = isPiTel n T
  | 0, _ => rfl
  | n + 1, .pi _ B => by
      simp only [instantiateLevels, isPiTel]
      exact isPiTel_instantiateLevels lvls n B
  | _ + 1, .bvar _ => rfl
  | _ + 1, .sort _ => rfl
  | _ + 1, .const _ _ => rfl
  | _ + 1, .app _ _ => rfl
  | _ + 1, .lam _ _ => rfl
  | _ + 1, .letE _ _ _ => rfl
  | _ + 1, .lit _ => rfl

/-- M-L03. UNCONDITIONAL, where the `instantiate` sibling
(`familyIdx_instantiate_const`) needs a const-head guard: a level
substitution can never turn a spine head into an application (M-001).
This is why M-L04 carries no guards at all. -/
theorem familyIdx_instantiateLevels (lvls : List Level) (nparams : Nat)
    (A : Expr Nat) :
    familyIdx nparams (instantiateLevels lvls A)
      = (familyIdx nparams A).map (instantiateLevels lvls) := by
  simp only [familyIdx]
  rw [appsSpine_instantiateLevels]
  exact (List.map_drop (instantiateLevels lvls) (appsSpine A).2 nparams).symm

/-- M-L04. The 05 §12 minor telescope commutes with `instantiateLevels`,
with NO guards (M-L03 is unconditional and `lift` commutes at every
cutoff, `lift_instantiateLevels`). `hbase` is the base body, shared by the
`[]` arm and by every fall-through arm — the fall-through of `minorTel`
IS the base body, so the two are the same obligation. -/
theorem minorTel_instantiateLevels (lvls : List Level) (nparams : Nat)
    (ks : List RecKind) (M ctorAcc T : Expr Nat) :
    instantiateLevels lvls (minorTel M nparams ctorAcc ks T)
      = minorTel (instantiateLevels lvls M) nparams
          (instantiateLevels lvls ctorAcc) ks (instantiateLevels lvls T) := by
  have hbase : ∀ (M' acc' T' : Expr Nat),
      instantiateLevels lvls
          (Expr.app (foldApps M' (familyIdx nparams T')) acc')
        = Expr.app (foldApps (instantiateLevels lvls M')
            (familyIdx nparams (instantiateLevels lvls T')))
            (instantiateLevels lvls acc') := by
    intro M' acc' T'
    rw [familyIdx_instantiateLevels]
    simp only [instantiateLevels, foldApps_instantiateLevels]
  induction ks generalizing M ctorAcc T with
  | nil => exact hbase M ctorAcc T
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              simp only [minorTel, instantiateLevels]
              apply congrArg (Expr.pi (instantiateLevels lvls A))
              rw [ih (lift 0 1 M) (.app (lift 0 1 ctorAcc) (.bvar 0)) B]
              simp only [instantiateLevels, ← lift_instantiateLevels]
          | bvar i => exact hbase M ctorAcc (.bvar i)
          | sort l => exact hbase M ctorAcc (.sort l)
          | const r ms => exact hbase M ctorAcc (.const r ms)
          | app f x => exact hbase M ctorAcc (.app f x)
          | lam A b => exact hbase M ctorAcc (.lam A b)
          | letE A v b => exact hbase M ctorAcc (.letE A v b)
          | lit t => exact hbase M ctorAcc (.lit t)
      | directRec =>
          cases T with
          | pi A B =>
              simp only [minorTel, instantiateLevels]
              apply congrArg (Expr.pi (instantiateLevels lvls A))
              rw [ih (lift 0 2 M) (.app (lift 0 2 ctorAcc) (.bvar 1))
                (lift 0 1 B), familyIdx_instantiateLevels]
              simp only [instantiateLevels, ← lift_instantiateLevels,
                foldApps_instantiateLevels]
          | bvar i => exact hbase M ctorAcc (.bvar i)
          | sort l => exact hbase M ctorAcc (.sort l)
          | const r ms => exact hbase M ctorAcc (.const r ms)
          | app f x => exact hbase M ctorAcc (.app f x)
          | lam A b => exact hbase M ctorAcc (.lam A b)
          | letE A v b => exact hbase M ctorAcc (.letE A v b)
          | lit t => exact hbase M ctorAcc (.lit t)

/-- M-L05. FORWARD only. The level list and the parameter list are FREE on
both sides — `directRecFamilySpine` reads neither (its `.directRec` arm is
`| .const r _ => decide (r = fam)`, so `ls` and `params` are discarded),
which is exactly the asymmetry that keeps the level-arity premise off
`hfamSpine` and puts it on `hfamSpineExact`. -/
theorem directRecFamilySpine_instantiateLevels (lvls : List Level)
    (fam : Nat) (ls ls' : List Level) (nparams : Nat)
    (params params' : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    directRecFamilySpine fam ls nparams params ks T fs = true →
    directRecFamilySpine fam ls' nparams params' ks
      (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi _ B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, instantiateLevels]
        at h ⊢
      rw [← instantiateLevels_instantiate0]
      exact directRecFamilySpine_instantiateLevels lvls fam ls ls' nparams
        params params' ks (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, instantiateLevels]
        at h ⊢
      have hhead := boolAnd_left h
      have hrest := boolAnd_right h
      rw [appsSpine_instantiateLevels]
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          simp only [hconst, instantiateLevels] at hhead ⊢
          rw [hhead, ← instantiateLevels_instantiate0]
          exact directRecFamilySpine_instantiateLevels lvls fam ls ls'
            nparams params params' ks (instantiate0 f B) fs hrest
      | bvar _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: _, .pi _ _, [], _ => by
      simp only [directRecFamilySpine, List.map_nil, instantiateLevels]
  | .directRec :: _, .pi _ _, [], _ => by
      simp only [directRecFamilySpine, List.map_nil, instantiateLevels]
  | .plain :: _, .bvar _, _, _ => rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

/-- M-L06. FORWARD, and the one level-MOVING congruence: unlike
`directRecFamilySpineExact_instantiate`, which holds `ls` fixed, the EXACT
walk's comparand `decide (lsA = ls)` moves with the substitution, so the
conclusion is at `ls.map (instLevel lvls)`. M-L15 is this lemma at the
canonical vector. -/
theorem directRecFamilySpineExact_instantiateLevels (lvls : List Level)
    (fam : Nat) (ls : List Level) (nparams : Nat)
    (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    directRecFamilySpineExact fam ls nparams params ks T fs = true →
    directRecFamilySpineExact fam (ls.map (instLevel lvls)) nparams
      (params.map (instantiateLevels lvls)) ks (instantiateLevels lvls T)
      (fs.map (instantiateLevels lvls)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi _ B, f :: fs, h => by
      simp only [directRecFamilySpineExact, List.map_cons, instantiateLevels]
        at h ⊢
      rw [← instantiateLevels_instantiate0]
      exact directRecFamilySpineExact_instantiateLevels lvls fam ls nparams
        params ks (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpineExact, List.map_cons, instantiateLevels]
        at h ⊢
      have hh := boolAnd_left h
      have hrest := boolAnd_right h
      have hhead := boolAnd_left hh
      have htake := boolAnd_right hh
      have hte : (appsSpine A).2.take nparams = params :=
        of_decide_eq_true htake
      have htake' :
          decide ((((appsSpine A).2.map (instantiateLevels lvls)).take
            nparams) = params.map (instantiateLevels lvls)) = true := by
        rw [← List.map_take, hte]
        exact decide_eq_true rfl
      rw [appsSpine_instantiateLevels]
      cases hconst : (appsSpine A).1 with
      | const r lsA =>
          simp only [hconst, instantiateLevels] at hhead ⊢
          have hr : decide (r = fam) = true := boolAnd_left hhead
          have hlsA : decide (lsA = ls) = true := boolAnd_right hhead
          have hlsA' : decide (lsA.map (instLevel lvls)
              = ls.map (instLevel lvls)) = true := by
            rw [of_decide_eq_true hlsA]
            exact decide_eq_true rfl
          rw [hr, hlsA', htake', ← instantiateLevels_instantiate0]
          exact directRecFamilySpineExact_instantiateLevels lvls fam ls
            nparams params ks (instantiate0 f B) fs hrest
      | bvar _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | sort _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | app _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lam _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | pi _ _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | letE _ _ _ =>
          simp only [hconst] at hhead; exact Bool.noConfusion hhead
      | lit _ => simp only [hconst] at hhead; exact Bool.noConfusion hhead
  | .plain :: _, .pi _ _, [], _ => by
      simp only [directRecFamilySpineExact, List.map_nil, instantiateLevels]
  | .directRec :: _, .pi _ _, [], _ => by
      simp only [directRecFamilySpineExact, List.map_nil, instantiateLevels]
  | .plain :: _, .bvar _, _, _ => rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

/-- M-L07. FORWARD; `nindices` and the paramsFields POSITIONS are
untouched. The index-count `decide` transports by `List.length_map` after
M-L03, and the `idxFamFree` `all` by `all_idxFamFree_map_instantiateLevels`. -/
theorem recIdxFromSpineWalk_instantiateLevels (fam : Nat) (lvls : List Level)
    (nparams nindices : Nat) (pf : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    recIdxFromSpineWalk fam nparams nindices pf ks T fs = true →
    recIdxFromSpineWalk fam nparams nindices (pf.map (instantiateLevels lvls))
      ks (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi _ B, f :: fs, h => by
      simp only [recIdxFromSpineWalk, List.map_cons, instantiateLevels]
        at h ⊢
      rw [← instantiateLevels_instantiate0]
      exact recIdxFromSpineWalk_instantiateLevels fam lvls nparams nindices pf
        ks (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [recIdxFromSpineWalk, List.map_cons, instantiateLevels]
        at h ⊢
      have hlenall := boolAnd_left h
      have hrest := boolAnd_right h
      have hlen := boolAnd_left hlenall
      have hall := boolAnd_right hlenall
      have hlen' :
          decide ((familyIdx nparams (instantiateLevels lvls A)).length
            = nindices) = true := by
        rw [familyIdx_instantiateLevels, List.length_map]
        exact hlen
      have hall' : ((familyIdx nparams A).map (instantiateLevels lvls)).all
          (fun y => idxFamFree fam (pf.map (instantiateLevels lvls)) y) = true := by
        exact all_idxFamFree_map_instantiateLevels fam lvls
          (familyIdx nparams A) pf hall
      rw [← familyIdx_instantiateLevels] at hall'
      have hrest' := recIdxFromSpineWalk_instantiateLevels fam lvls nparams
        nindices pf ks (instantiate0 f B) fs hrest
      rw [← instantiateLevels_instantiate0]
      simp only [hlen', hall', hrest']
      rfl
  | .plain :: _, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, instantiateLevels]
  | .directRec :: _, .pi _ _, [], _ => by
      simp only [recIdxFromSpineWalk, List.map_nil, instantiateLevels]
  | .plain :: _, .bvar _, _, _ => rfl
  | .plain :: _, .sort _, _, _ => rfl
  | .plain :: _, .const _ _, _, _ => rfl
  | .plain :: _, .app _ _, _, _ => rfl
  | .plain :: _, .lam _ _, _, _ => rfl
  | .plain :: _, .letE _ _ _, _, _ => rfl
  | .plain :: _, .lit _, _, _ => rfl
  | .directRec :: _, .bvar _, _, _ => rfl
  | .directRec :: _, .sort _, _, _ => rfl
  | .directRec :: _, .const _ _, _, _ => rfl
  | .directRec :: _, .app _ _, _, _ => rfl
  | .directRec :: _, .lam _ _, _, _ => rfl
  | .directRec :: _, .letE _ _ _, _, _ => rfl
  | .directRec :: _, .lit _, _, _ => rfl

/-- M-L08. FORWARD, POSITIONS UNCHANGED. `idxPosZip` CHECKS
`decide (paramsFields[i]? = some x)`; it does NOT recompute `listIndexOf`,
so the step is the transport `paramsFields[i]? = some x →
(paramsFields.map iL)[i]? = some (iL x)` (`List.getElem?_map`) and never a
re-derivation. That is why M-L09 needs no injectivity of
`instantiateLevels` — which it does not have. -/
theorem idxPosZip_instantiateLevels (lvls : List Level)
    (pf xs : List (Expr Nat)) (pos : List Nat)
    (h : idxPosZip pf xs pos = true) :
    idxPosZip (pf.map (instantiateLevels lvls))
      (xs.map (instantiateLevels lvls)) pos = true := by
  induction xs generalizing pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons _ _ => simp only [idxPosZip] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil => simp only [idxPosZip] at h; nomatch h
      | cons i is =>
          simp only [idxPosZip] at h
          have hx := boolAnd_left h
          have hrest := boolAnd_right h
          have hx' : (pf.map (instantiateLevels lvls))[i]?
              = some (instantiateLevels lvls x) := by
            rw [List.getElem?_map, of_decide_eq_true hx]
            rfl
          have hrest' := ih is hrest
          simp only [idxPosZip, List.map_cons, hx', decide_eq_true rfl,
            hrest']
          rfl

/-- M-L09. FORWARD; the stored position lists `pss` are UNTOUCHED in both
stages. M-L08 for the zip, M-L03 for the index list. -/
theorem recIdxPosWalk_instantiateLevels (lvls : List Level) (nparams : Nat)
    (pf : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat)) (pss : List (List Nat))
    (h : recIdxPosWalk nparams pf ks T fs pss = true) :
    recIdxPosWalk nparams (pf.map (instantiateLevels lvls)) ks
      (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) pss
      = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxPosWalk, List.map_nil]
          | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxPosWalk, List.map_cons,
                            instantiateLevels] at h ⊢
                          rw [← instantiateLevels_instantiate0]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxPosWalk] at h; nomatch h
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      simp only [recIdxPosWalk, List.map_cons,
                        instantiateLevels] at h ⊢
                      have hzip := boolAnd_left h
                      have hrest := boolAnd_right h
                      have hfi := familyIdx_instantiateLevels lvls nparams A
                      have hzip' : idxPosZip
                          (pf.map (instantiateLevels lvls))
                          (familyIdx nparams (instantiateLevels lvls A))
                          pos = true := by
                        rw [hfi]
                        exact idxPosZip_instantiateLevels lvls pf
                          (familyIdx nparams A) pos hzip
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [← instantiateLevels_instantiate0]
                      simp only [hzip', hrest']
                      rfl
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h

/-- M-L10. FORWARD, and — unlike `idxTyAlignPosGo_instantiate` — with NO
closedness premise on either stored type: BOTH pass under the SAME `iL`,
so `applyTel_instantiateLevels` (the MAPPED-args form, the only true one)
moves each side and the `decide (Ac = Ar)` comparison is symmetric. -/
theorem idxTyAlignPosGo_instantiateLevels (lvls : List Level)
    (recType ctorType : Expr Nat)
    (recPre paramsFields pre rest : List (Expr Nat)) (pos : List Nat)
    (h : idxTyAlignPosGo recType ctorType recPre paramsFields pre rest pos
      = true) :
    idxTyAlignPosGo (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType)
      (recPre.map (instantiateLevels lvls))
      (paramsFields.map (instantiateLevels lvls))
      (pre.map (instantiateLevels lvls))
      (rest.map (instantiateLevels lvls)) pos = true := by
  induction rest generalizing pre pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons i is =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre [] (i :: is) = false := rfl
          rw [hf] at h; nomatch h
  | cons x xs ih =>
      cases pos with
      | nil =>
          have hf : idxTyAlignPosGo recType ctorType recPre paramsFields
              pre (x :: xs) [] = false := rfl
          rw [hf] at h; nomatch h
      | cons i is =>
          simp only [idxTyAlignPosGo] at h
          simp only [List.map_append, List.map_cons, List.map_nil]
          cases happR : applyTel (recPre ++ pre) recType with
          | none => simp only [happR] at h; nomatch h
          | some Ur =>
              match Ur with
              | .pi Ar Br =>
                  simp only [happR] at h
                  cases happC : applyTel (paramsFields.take i) ctorType with
                  | none => simp only [happC] at h; nomatch h
                  | some Uc =>
                      match Uc with
                      | .pi Ac Bc =>
                          simp only [happC] at h
                          have heq := boolAnd_left h
                          have hrest := boolAnd_right h
                          have hAcAr : Ac = Ar := of_decide_eq_true heq
                          have happR' :
                              applyTel (recPre.map (instantiateLevels lvls)
                                  ++ pre.map (instantiateLevels lvls))
                                (instantiateLevels lvls recType)
                                = some (Expr.pi (instantiateLevels lvls Ar)
                                    (instantiateLevels lvls Br)) := by
                            rw [← List.map_append,
                              applyTel_instantiateLevels, happR]
                            rfl
                          have happC' :
                              applyTel ((paramsFields.map
                                  (instantiateLevels lvls)).take i)
                                (instantiateLevels lvls ctorType)
                                = some (Expr.pi (instantiateLevels lvls Ac)
                                    (instantiateLevels lvls Bc)) := by
                            rw [← List.map_take,
                              applyTel_instantiateLevels, happC]
                            rfl
                          have heq' :
                              decide (instantiateLevels lvls Ac
                                = instantiateLevels lvls Ar) = true := by
                            rw [hAcAr]
                            exact decide_eq_true rfl
                          have ih' := ih (pre ++ [x]) is hrest
                          rw [List.map_append, List.map_cons, List.map_nil]
                            at ih'
                          simp only [idxTyAlignPosGo, happR', happC', heq',
                            ih']
                          rfl
                      | .bvar _ => simp only [happC] at h; nomatch h
                      | .sort _ => simp only [happC] at h; nomatch h
                      | .const _ _ => simp only [happC] at h; nomatch h
                      | .app _ _ => simp only [happC] at h; nomatch h
                      | .lam _ _ => simp only [happC] at h; nomatch h
                      | .letE _ _ _ => simp only [happC] at h; nomatch h
                      | .lit _ => simp only [happC] at h; nomatch h
              | .bvar _ => simp only [happR] at h; nomatch h
              | .sort _ => simp only [happR] at h; nomatch h
              | .const _ _ => simp only [happR] at h; nomatch h
              | .app _ _ => simp only [happR] at h; nomatch h
              | .lam _ _ => simp only [happR] at h; nomatch h
              | .letE _ _ _ => simp only [happR] at h; nomatch h
              | .lit _ => simp only [happR] at h; nomatch h

/-- M-L11. The `[]`-seeded wrapper of M-L10. -/
theorem idxTyAlignPos_instantiateLevels (lvls : List Level)
    (recType ctorType : Expr Nat)
    (recPre paramsFields idx : List (Expr Nat)) (pos : List Nat)
    (h : idxTyAlignPos recType ctorType recPre paramsFields idx pos = true) :
    idxTyAlignPos (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType)
      (recPre.map (instantiateLevels lvls))
      (paramsFields.map (instantiateLevels lvls))
      (idx.map (instantiateLevels lvls)) pos = true := by
  simp only [idxTyAlignPos] at h ⊢
  have hgo := idxTyAlignPosGo_instantiateLevels lvls recType ctorType
    recPre paramsFields [] idx pos h
  simp only [List.map_nil] at hgo
  exact hgo

/-- M-L12. FORWARD. ONE `iL` serves BOTH prefixes: the recursor prefix and
the params-fields list move under the same substitution, which is what
lets `hidxTy` be reached with a single transport per stage. -/
theorem recIdxTyWalkPos_instantiateLevels (lvls : List Level)
    (recType ctorType : Expr Nat) (nparams : Nat)
    (recPre paramsFields : List (Expr Nat)) (ks : List RecKind)
    (T : Expr Nat) (fs : List (Expr Nat)) (pss : List (List Nat))
    (h : recIdxTyWalkPos recType ctorType nparams recPre paramsFields ks T
      fs pss = true) :
    recIdxTyWalkPos (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType) nparams
      (recPre.map (instantiateLevels lvls))
      (paramsFields.map (instantiateLevels lvls)) ks
      (instantiateLevels lvls T) (fs.map (instantiateLevels lvls)) pss
      = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTyWalkPos, List.map_nil]
          | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | cons _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxTyWalkPos, List.map_cons,
                            instantiateLevels] at h ⊢
                          rw [← instantiateLevels_instantiate0]
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxTyWalkPos] at h; nomatch h
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxTyWalkPos] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxTyWalkPos] at h; nomatch h
                  | cons pos pss =>
                      simp only [recIdxTyWalkPos, List.map_cons,
                        instantiateLevels] at h ⊢
                      have halign := boolAnd_left h
                      have hrest := boolAnd_right h
                      have hfi := familyIdx_instantiateLevels lvls nparams A
                      have halign' : idxTyAlignPos
                          (instantiateLevels lvls recType)
                          (instantiateLevels lvls ctorType)
                          (recPre.map (instantiateLevels lvls))
                          (paramsFields.map (instantiateLevels lvls))
                          (familyIdx nparams (instantiateLevels lvls A))
                          pos = true := by
                        rw [hfi]
                        exact idxTyAlignPos_instantiateLevels lvls recType
                          ctorType recPre paramsFields
                          (familyIdx nparams A) pos halign
                      have hrest' := ih (instantiate0 f B) fs pss hrest
                      rw [← instantiateLevels_instantiate0]
                      simp only [halign', hrest']
                      rfl
          | bvar _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | sort _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos] at h; nomatch h

/-- M-L13. FORWARD, NO closedness premise and NO arity premise: the SAME
`pre` is applied to BOTH stored types and both move under the same `iL`
(cf. `recCtorParamAlignGo_instantiate`, which must hold the types fixed
and therefore carries two closedness hypotheses). -/
theorem recCtorParamAlignGo_instantiateLevels (lvls : List Level)
    (recType ctorType : Expr Nat) (pre rest : List (Expr Nat))
    (h : recCtorParamAlignGo recType ctorType pre rest = true) :
    recCtorParamAlignGo (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType) (pre.map (instantiateLevels lvls))
      (rest.map (instantiateLevels lvls)) = true := by
  induction rest generalizing pre with
  | nil => rfl
  | cons x xs ih =>
      simp only [recCtorParamAlignGo] at h
      simp only [List.map_cons]
      cases happR : applyTel pre recType with
      | none => simp only [happR] at h; nomatch h
      | some Ur =>
          match Ur with
          | .pi Ar Br =>
              simp only [happR] at h
              cases happC : applyTel pre ctorType with
              | none => simp only [happC] at h; nomatch h
              | some Uc =>
                  match Uc with
                  | .pi Ac Bc =>
                      simp only [happC] at h
                      have heq := boolAnd_left h
                      have hrest := boolAnd_right h
                      have hAcAr : Ac = Ar := of_decide_eq_true heq
                      have happR' :
                          applyTel (pre.map (instantiateLevels lvls))
                            (instantiateLevels lvls recType)
                            = some (Expr.pi (instantiateLevels lvls Ar)
                                (instantiateLevels lvls Br)) := by
                        rw [applyTel_instantiateLevels, happR]
                        rfl
                      have happC' :
                          applyTel (pre.map (instantiateLevels lvls))
                            (instantiateLevels lvls ctorType)
                            = some (Expr.pi (instantiateLevels lvls Ac)
                                (instantiateLevels lvls Bc)) := by
                        rw [applyTel_instantiateLevels, happC]
                        rfl
                      have heq' :
                          decide (instantiateLevels lvls Ac
                            = instantiateLevels lvls Ar) = true := by
                        rw [hAcAr]
                        exact decide_eq_true rfl
                      have ih' := ih (pre ++ [x]) hrest
                      rw [List.map_append, List.map_cons, List.map_nil]
                        at ih'
                      simp only [recCtorParamAlignGo, happR', happC', heq',
                        ih']
                      rfl
                  | .bvar _ => simp only [happC] at h; nomatch h
                  | .sort _ => simp only [happC] at h; nomatch h
                  | .const _ _ => simp only [happC] at h; nomatch h
                  | .app _ _ => simp only [happC] at h; nomatch h
                  | .lam _ _ => simp only [happC] at h; nomatch h
                  | .letE _ _ _ => simp only [happC] at h; nomatch h
                  | .lit _ => simp only [happC] at h; nomatch h
          | .bvar _ => simp only [happR] at h; nomatch h
          | .sort _ => simp only [happR] at h; nomatch h
          | .const _ _ => simp only [happR] at h; nomatch h
          | .app _ _ => simp only [happR] at h; nomatch h
          | .lam _ _ => simp only [happR] at h; nomatch h
          | .letE _ _ _ => simp only [happR] at h; nomatch h
          | .lit _ => simp only [happR] at h; nomatch h

/-- M-L14. The `[]`-seeded wrapper of M-L13, and the fact that keeps
`hparamAlign` OFF the level-arity premise: both stored types pass under the
SAME `iL`, so the two maps cancel and no `hnU` is needed — which is why the
00 §20.7 field table's `hparamAlign` row says "no arity premise" while
`hfamSpineExact` and `hminTel` carry one. -/
theorem recCtorParamAlign_instantiateLevels (lvls : List Level)
    (recType ctorType : Expr Nat) (params : List (Expr Nat))
    (h : recCtorParamAlign recType ctorType params = true) :
    recCtorParamAlign (instantiateLevels lvls recType)
      (instantiateLevels lvls ctorType)
      (params.map (instantiateLevels lvls)) = true := by
  simp only [recCtorParamAlign] at h ⊢
  have hgo := recCtorParamAlignGo_instantiateLevels lvls recType ctorType
    [] params h
  simp only [List.map_nil] at hgo
  exact hgo

/-- M-L15. M-L06 at the CANONICAL universe vector, concluding at
`lvls.take nU`. One of the two stage-L lemmas carrying the level-arity
premise `hnU : nU ≤ lvls.length`, which is READ (00 §20.7 pinning chain
step 9), never re-derived: `map_instLevel_canonical` is false without it,
because out of range `instLevel` keeps `param i` visible while `take`
drops the slot. -/
theorem directRecFamilySpineExact_canonical_take (lvls : List Level)
    (fam nU nparams : Nat) (hnU : nU ≤ lvls.length)
    (params : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat)
    (fs : List (Expr Nat))
    (h : directRecFamilySpineExact fam ((List.range nU).map Level.param)
      nparams params ks T fs = true) :
    directRecFamilySpineExact fam (lvls.take nU) nparams
      (params.map (instantiateLevels lvls)) ks (instantiateLevels lvls T)
      (fs.map (instantiateLevels lvls)) = true := by
  rw [← map_instLevel_canonical nU lvls hnU]
  exact directRecFamilySpineExact_instantiateLevels lvls fam
    ((List.range nU).map Level.param) nparams params ks T fs h

/-- M-L16. M-L04 at the seed `iotaMdom` demands — the constructor at the
CANONICAL vector, which the instantiated view carries as `lvls.take nU`.
An EQUALITY, and the second of the two stage-L lemmas carrying
`hnU : nU ≤ lvls.length`. -/
theorem iotaMdom_canonical_seed (lvls : List Level) (nU nparams ctorRef : Nat)
    (hnU : nU ≤ lvls.length) (M : Expr Nat) (P : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) :
    instantiateLevels lvls
        (minorTel M nparams
          (foldApps (.const ctorRef ((List.range nU).map Level.param)) P)
          ks T)
      = minorTel (instantiateLevels lvls M) nparams
          (foldApps (.const ctorRef (lvls.take nU))
            (P.map (instantiateLevels lvls))) ks
          (instantiateLevels lvls T) := by
  rw [minorTel_instantiateLevels, foldApps_instantiateLevels]
  simp only [instantiateLevels, map_instLevel_canonical nU lvls hnU]
end Rcic.Declarative
