import rcic.RcicModelDenote
import rcic.RcicTypedEnv
import rcic.RcicEnv
import rcic.RcicLevelCalc

/-!
# RcicModelEnv — `μ` over `EnvWfT` (S5a: skeleton + singleton machinery)

`μ r nls` is the member interpretation `⟦const r⟧` at instantiated
universe list `nls`.  `muOf` builds it by recursion on the `EnvWfT`
derivation: singleton steps install the member's denotation
(`definitionM` → `⟦body⟧` at the prefix μ — δ fires only there —
every other class gets `J₀`, free by `MemAt`'s junk disjunct), and
group steps delegate to the `GDen` interface the group layer (S5b)
fills with the lfp/ctor/tag-tested-fold construction.

Structural lemmas delivered here:

- `denRefs` — the member refs `den` actually touches (`.const` nodes,
  plus the `natExpand` consts behind `.lit`: `denLit` reads `μ 1 []`
  and, from `t + 1` up, `μ 2 []`), with `den_consts_agree` (pointwise
  `=` on `denRefs` suffices for `den` equality) and `hasTyT_denRefs`
  (a typed term's `denRefs` are env members).
- `evalTotal_of_levelBounded` / `map_evalTotal_of_levelsBounded` /
  `den_levels_closed` — σ-independence at `levelBounded 0` /
  `exprLevelsBounded 0`: member bodies and types are level-closed
  (`hlvlB`), so the σ `muOf` picks inside a definition's denotation is
  irrelevant.
- `GDen`/`GDenOk` — the group-layer interface: `gden hmem μ` extends
  `μ` on exactly the group's refs, preserving base members and every
  ref outside the group.
- `muStepAt`, `muOf`, `muOf_agree_singleton`/`muOf_agree_group`
  (one-step prefix agreement), `muOf_gden_irrel` (a `NoGroupEnv` env
  never calls `gden`), `muOf_nonmember`, and the packaged
  `den_prefix_agree`.
-/

namespace Rcic.Model

namespace PS

/-! ### the refs `den` touches -/

/-- the `natExpand` consts `denLit` reads at `t` — `denRefs (lit t)`
factors through this so `denRefs` stays structural. -/
def denRefsLit : Nat → List Nat
  | 0 => [1]
  | t + 1 => 2 :: denRefsLit t

/-- the member refs `den` can reach in `e`: every `.const r`, plus the
`denRefsLit` consts behind `.lit` (1 = zero always; 2 = succ from
`t + 1` up — exactly the refs `denLit` reads). -/
def denRefs : Declarative.Expr Nat → List Nat
  | .bvar _ => []
  | .sort _ => []
  | .const r _ => [r]
  | .app f x => denRefs f ++ denRefs x
  | .lam a b => denRefs a ++ denRefs b
  | .pi a b => denRefs a ++ denRefs b
  | .letE a v b => denRefs a ++ denRefs v ++ denRefs b
  | .lit t => denRefsLit t

/-- `denRefsLit` is `denRefs` of the expansion — the transport lemma
for `lit` arms. -/
theorem denRefs_natExpand : (t : Nat) →
    denRefs (Declarative.natExpand t) = denRefsLit t
  | 0 => rfl
  | t + 1 => by
      show 2 :: denRefs (Declarative.natExpand t) = 2 :: denRefsLit t
      exact congrArg (2 :: ·) (denRefs_natExpand t)

/-- `denLit` agreement: `lit` reaches only the `denRefsLit` consts. -/
theorem denLit_agree {μ₁ μ₂ : Nat → List Nat → PS} (t : Nat)
    (h : ∀ r nls, r ∈ denRefsLit t → μ₁ r nls = μ₂ r nls) :
    denLit μ₁ t = denLit μ₂ t := by
  induction t with
  | zero =>
      show μ₁ 1 [] = μ₂ 1 []
      exact h 1 [] (List.mem_singleton_self 1)
  | succ t ih =>
      have h' : ∀ r nls, r ∈ denRefsLit t → μ₁ r nls = μ₂ r nls :=
        fun r nls hr => h r nls (List.Mem.tail 2 hr)
      have h2 : μ₁ 2 [] = μ₂ 2 [] := h 2 [] (List.Mem.head _)
      show fapp (payloadOf (μ₁ 2 [])) (denLit μ₁ t) =
           fapp (payloadOf (μ₂ 2 [])) (denLit μ₂ t)
      rw [h2, ih h']

/-- `den` needs `μ` only on `denRefs`. -/
theorem den_consts_agree {μ₁ μ₂ : Nat → List Nat → PS} (σ : Nat → Nat)
    (ν : Nat → PS) (e : Declarative.Expr Nat)
    (h : ∀ r nls, r ∈ denRefs e → μ₁ r nls = μ₂ r nls) :
    den μ₁ σ ν e = den μ₂ σ ν e := by
  induction e generalizing ν with
  | bvar i => rfl
  | sort l => rfl
  | const r ls =>
      show μ₁ r (ls.map (Declarative.evalTotal σ)) =
           μ₂ r (ls.map (Declarative.evalTotal σ))
      exact h r _ (List.mem_singleton_self r)
  | app f x ihf ihx =>
      show fapp (payloadOf (den μ₁ σ ν f)) (den μ₁ σ ν x) =
           fapp (payloadOf (den μ₂ σ ν f)) (den μ₂ σ ν x)
      rw [ihf ν (fun r nls hr => h r nls (List.mem_append_left _ hr)),
          ihx ν (fun r nls hr => h r nls (List.mem_append_right _ hr))]
  | lam A b ihA ihb =>
      have hA := ihA ν (fun r nls hr => h r nls (List.mem_append_left _ hr))
      have hb0 := ihb (νcons junk₀ ν)
        (fun r nls hr => h r nls (List.mem_append_right _ hr))
      have hbg : (fun a => den μ₁ σ (νcons a ν) b) =
          (fun a => den μ₂ σ (νcons a ν) b) :=
        funext fun a => ihb (νcons a ν)
          (fun r nls hr => h r nls (List.mem_append_right _ hr))
      show ordPair
            (imaxTag (tagOf (den μ₁ σ ν A)) (tagOf (den μ₁ σ (νcons junk₀ ν) b)))
            (mkLam (fun a => den μ₁ σ (νcons a ν) b) (payloadOf (den μ₁ σ ν A))) =
           ordPair
            (imaxTag (tagOf (den μ₂ σ ν A)) (tagOf (den μ₂ σ (νcons junk₀ ν) b)))
            (mkLam (fun a => den μ₂ σ (νcons a ν) b) (payloadOf (den μ₂ σ ν A)))
      rw [hA, hb0, hbg]
  | pi A B ihA ihB =>
      have hA := ihA ν (fun r nls hr => h r nls (List.mem_append_left _ hr))
      have hB0 := ihB (νcons junk₀ ν)
        (fun r nls hr => h r nls (List.mem_append_right _ hr))
      have hBg : (fun a => payloadOf (den μ₁ σ (νcons a ν) B)) =
          (fun a => payloadOf (den μ₂ σ (νcons a ν) B)) :=
        funext fun a => congrArg payloadOf
          (ihB (νcons a ν) (fun r nls hr => h r nls (List.mem_append_right _ hr)))
      show ordPair
            (imaxTag1 (tagOf (den μ₁ σ ν A)) (tagOf (den μ₁ σ (νcons junk₀ ν) B)))
            (piSet (payloadOf (den μ₁ σ ν A))
              (fun a => payloadOf (den μ₁ σ (νcons a ν) B))) =
           ordPair
            (imaxTag1 (tagOf (den μ₂ σ ν A)) (tagOf (den μ₂ σ (νcons junk₀ ν) B)))
            (piSet (payloadOf (den μ₂ σ ν A))
              (fun a => payloadOf (den μ₂ σ (νcons a ν) B)))
      rw [hA, hB0, hBg]
  | letE A v b ihA ihv ihb =>
      have hv := ihv ν (fun r nls hr => h r nls
        (List.mem_append_left (denRefs b) (List.mem_append_right (denRefs A) hr)))
      have hb := ihb (νcons (den μ₂ σ ν v) ν)
        (fun r nls hr => h r nls
          (List.mem_append_right (denRefs A ++ denRefs v) hr))
      show den μ₁ σ (νcons (den μ₁ σ ν v) ν) b =
           den μ₂ σ (νcons (den μ₂ σ ν v) ν) b
      rw [hv]
      exact hb
  | lit t =>
      show denLit μ₁ t = denLit μ₂ t
      exact denLit_agree t h

/-- a typed term's `denRefs` are env members. -/
theorem hasTyT_denRefs {E : Declarative.ResolvedEnv} {n : Nat} :
    {Γ : Declarative.LCtx} → {e T : Declarative.Expr Nat} →
    Declarative.HasTyT E n Γ e T →
    ∀ r ∈ denRefs e, (E.members r).isSome
  | _, _, _, .sort _ _ => fun r hr => absurd hr (List.not_mem_nil r)
  | _, _, _, .bvar _ _ _ _ => fun r hr => absurd hr (List.not_mem_nil r)
  | _, _, _, .const _ r _ m hres _ _ => fun r' hr' => by
      simp only [denRefs, List.mem_singleton] at hr'
      subst hr'
      exact Option.isSome_iff_exists.mpr ⟨m, hres⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => fun r hr => by
      rcases List.mem_append.mp hr with hA' | hB'
      · exact hasTyT_denRefs hA r hA'
      · exact hasTyT_denRefs hB r hB'
  | _, _, _, .lam _ _ _ _ _ hA hb => fun r hr => by
      rcases List.mem_append.mp hr with hA' | hb'
      · exact hasTyT_denRefs hA r hA'
      · exact hasTyT_denRefs hb r hb'
  | _, _, _, .app _ _ _ _ _ hf ha => fun r hr => by
      rcases List.mem_append.mp hr with hf' | ha'
      · exact hasTyT_denRefs hf r hf'
      · exact hasTyT_denRefs ha r ha'
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => fun r hr => by
      rcases List.mem_append.mp hr with hAv | hb'
      · rcases List.mem_append.mp hAv with hA' | hv'
        · exact hasTyT_denRefs hA r hA'
        · exact hasTyT_denRefs hv r hv'
      · exact hasTyT_denRefs hb r hb'
  | _, _, _, .lit _ t _ hexp => fun r hr => by
      have hrn : r ∈ denRefs (Declarative.natExpand t) := by
        rw [denRefs_natExpand t]
        exact hr
      exact hasTyT_denRefs hexp r hrn
  | _, _, _, .conv _ _ _ _ _ h _ => fun r hr => hasTyT_denRefs h r hr

/-! ### level-closed denotations -/

/-- `levelBounded 0` levels have no `.param` leaves, so `evalTotal`
is σ-independent on them. -/
theorem evalTotal_of_levelBounded {σ τ : Nat → Nat} :
    (l : Declarative.Level) → Declarative.levelBounded 0 l = true →
      Declarative.evalTotal σ l = Declarative.evalTotal τ l
  | .zero, _ => rfl
  | .succ l, h => congrArg Nat.succ (evalTotal_of_levelBounded l h)
  | .max a b, h => by
      show max (Declarative.evalTotal σ a) (Declarative.evalTotal σ b) =
           max (Declarative.evalTotal τ a) (Declarative.evalTotal τ b)
      rw [evalTotal_of_levelBounded a (Declarative.boolAnd_left h),
          evalTotal_of_levelBounded b (Declarative.boolAnd_right h)]
  | .imax a b, h => by
      have ha : Declarative.evalTotal σ a = Declarative.evalTotal τ a :=
        evalTotal_of_levelBounded a (Declarative.boolAnd_left h)
      have hb : Declarative.evalTotal σ b = Declarative.evalTotal τ b :=
        evalTotal_of_levelBounded b (Declarative.boolAnd_right h)
      show (let y := Declarative.evalTotal σ b
            if y = 0 then 0 else max (Declarative.evalTotal σ a) y) =
           (let y := Declarative.evalTotal τ b
            if y = 0 then 0 else max (Declarative.evalTotal τ a) y)
      rw [ha, hb]
  | .param i, h => absurd (of_decide_eq_true h) (Nat.not_lt_zero i)

theorem map_evalTotal_of_levelsBounded {σ τ : Nat → Nat} :
    (ls : List Declarative.Level) → Declarative.levelsBounded 0 ls = true →
      ls.map (Declarative.evalTotal σ) = ls.map (Declarative.evalTotal τ)
  | [], _ => rfl
  | l :: t, h => by
      rw [List.map_cons, List.map_cons,
          evalTotal_of_levelBounded l (Declarative.boolAnd_left h),
          map_evalTotal_of_levelsBounded t (Declarative.boolAnd_right h)]

/-- `den` is σ-independent on level-closed expressions. -/
theorem den_levels_closed {μ : Nat → List Nat → PS} {σ τ : Nat → Nat}
    (e : Declarative.Expr Nat)
    (h : Declarative.exprLevelsBounded 0 e = true) (ν : Nat → PS) :
    den μ σ ν e = den μ τ ν e := by
  induction e generalizing ν with
  | bvar i => rfl
  | sort l =>
      show ordPair (ord (Declarative.evalTotal σ l + 2))
             (ord (Declarative.evalTotal σ l)) =
           ordPair (ord (Declarative.evalTotal τ l + 2))
             (ord (Declarative.evalTotal τ l))
      rw [evalTotal_of_levelBounded l h]
  | const r ls =>
      show μ r (ls.map (Declarative.evalTotal σ)) =
           μ r (ls.map (Declarative.evalTotal τ))
      rw [map_evalTotal_of_levelsBounded ls h]
  | app f x ihf ihx =>
      show fapp (payloadOf (den μ σ ν f)) (den μ σ ν x) =
           fapp (payloadOf (den μ τ ν f)) (den μ τ ν x)
      rw [ihf (Declarative.boolAnd_left h) ν,
          ihx (Declarative.boolAnd_right h) ν]
  | lam A b ihA ihb =>
      have hA := ihA (Declarative.boolAnd_left h) ν
      have hb0 := ihb (Declarative.boolAnd_right h) (νcons junk₀ ν)
      have hbg : (fun a => den μ σ (νcons a ν) b) =
          (fun a => den μ τ (νcons a ν) b) :=
        funext fun a => ihb (Declarative.boolAnd_right h) (νcons a ν)
      show ordPair
            (imaxTag (tagOf (den μ σ ν A)) (tagOf (den μ σ (νcons junk₀ ν) b)))
            (mkLam (fun a => den μ σ (νcons a ν) b) (payloadOf (den μ σ ν A))) =
           ordPair
            (imaxTag (tagOf (den μ τ ν A)) (tagOf (den μ τ (νcons junk₀ ν) b)))
            (mkLam (fun a => den μ τ (νcons a ν) b) (payloadOf (den μ τ ν A)))
      rw [hA, hb0, hbg]
  | pi A B ihA ihB =>
      have hA := ihA (Declarative.boolAnd_left h) ν
      have hB0 := ihB (Declarative.boolAnd_right h) (νcons junk₀ ν)
      have hBg : (fun a => payloadOf (den μ σ (νcons a ν) B)) =
          (fun a => payloadOf (den μ τ (νcons a ν) B)) :=
        funext fun a => congrArg payloadOf
          (ihB (Declarative.boolAnd_right h) (νcons a ν))
      show ordPair
            (imaxTag1 (tagOf (den μ σ ν A)) (tagOf (den μ σ (νcons junk₀ ν) B)))
            (piSet (payloadOf (den μ σ ν A))
              (fun a => payloadOf (den μ σ (νcons a ν) B))) =
           ordPair
            (imaxTag1 (tagOf (den μ τ ν A)) (tagOf (den μ τ (νcons junk₀ ν) B)))
            (piSet (payloadOf (den μ τ ν A))
              (fun a => payloadOf (den μ τ (νcons a ν) B)))
      rw [hA, hB0, hBg]
  | letE A v b ihA ihv ihb =>
      have hv := ihv (Declarative.boolAnd_right (Declarative.boolAnd_left h)) ν
      have hb := ihb (Declarative.boolAnd_right h) (νcons (den μ τ ν v) ν)
      show den μ σ (νcons (den μ σ ν v) ν) b =
           den μ τ (νcons (den μ τ ν v) ν) b
      rw [hv]
      exact hb
  | lit t => rfl

/-! ### `μ` over `EnvWfT` -/

/-- the group-layer interface: given the group's member derivation and
the base μ, produce the extended μ.  `RcicModelGroup` (S5b) supplies
the lfp/ctor/tag-tested-fold implementation; `muOf` only ever calls it
at `group` steps. -/
abbrev GDen :=
  {S E E' : Declarative.ResolvedEnv} →
  {ms : List (Nat × Declarative.CheckedMember)} →
  Declarative.GroupMembersT S E ms E' →
  (Nat → List Nat → PS) → Nat → List Nat → PS

/-- what the group layer owes: `gden hmem μ` extends `μ` on exactly the
group's refs — it preserves base members and every ref that is neither
a base member nor among the group's refs. -/
def GDenOk (gden : GDen) : Prop :=
  ∀ {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)}
    (hmem : Declarative.GroupMembersT S E ms E') (μ : Nat → List Nat → PS),
    (∀ r' m', E.members r' = some m' → ∀ nls,
      gden hmem μ r' nls = μ r' nls) ∧
    (∀ r', E.members r' = none → r' ∉ ms.map Prod.fst → ∀ nls,
      gden hmem μ r' nls = μ r' nls)

/-- override `μ` at `r` with `d`. -/
def muStepAt (μ : Nat → List Nat → PS) (r : Nat) (d : List Nat → PS) :
    Nat → List Nat → PS :=
  fun r' nls => if r' = r then d nls else μ r' nls

theorem muStepAt_eq (μ : Nat → List Nat → PS) (r : Nat) (d : List Nat → PS)
    (nls : List Nat) : muStepAt μ r d r nls = d nls :=
  if_pos rfl

theorem muStepAt_ne (μ : Nat → List Nat → PS) (r : Nat) (d : List Nat → PS)
    {r' : Nat} (h : r' ≠ r) (nls : List Nat) :
    muStepAt μ r d r' nls = μ r' nls :=
  if_neg h

/-- member interpretation over an `EnvWfT` derivation: singleton steps
install the member's denotation at the prefix μ (`definitionM` →
`⟦body⟧`, the only class δ fires for; everything else `J₀`), group
steps delegate to `gden`. -/
def muOf (gden : GDen) {E : Declarative.ResolvedEnv} :
    Declarative.EnvWfT E → Nat → List Nat → PS
  | .empty => fun _ _ => junk₀
  | .axiom _ r _ _ hE .. => muStepAt (muOf gden hE) r (fun _ => junk₀)
  | .definition _ r _ v _ hE .. =>
      muStepAt (muOf gden hE) r
        (fun _ => den (muOf gden hE) (fun _ => 0) (fun _ => junk₀) v)
  | .thm _ r _ _ hE .. => muStepAt (muOf gden hE) r (fun _ => junk₀)
  | .opaque _ r _ _ _ hE .. => muStepAt (muOf gden hE) r (fun _ => junk₀)
  | .group _ _ _ _ _ _ _ hE _ _ _ hmem => gden hmem (muOf gden hE)

/-! ### group-step member bookkeeping -/

/-- a `GroupMembersT` chain only extends: the growing env keeps every
member it starts with. -/
theorem groupMembersT_preserve {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)} :
    Declarative.GroupMembersT S E ms E' →
    ∀ r m, E.members r = some m → E'.members r = some m := by
  intro hmem
  induction hmem with
  | nil _ => intro r m h; exact h
  | cons E r m rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r' m' hm'
      exact ih _ _ (Declarative.members_extend_preserved hfresh _ _ hm')

/-- every listed group member lands in the final env. -/
theorem groupMembersT_installed {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)}
    (hmem : Declarative.GroupMembersT S E ms E') {r m}
    (hin : (r, m) ∈ ms) : E'.members r = some m := by
  induction hmem with
  | nil _ => exact absurd hin (List.not_mem_nil _)
  | cons E r' m' rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      rcases List.mem_cons.mp hin with heq | htl
      · injection heq with hr hm
        subst hr
        subst hm
        exact groupMembersT_preserve hrest _ _
          (Declarative.members_extend_eq _ _ _)
      · exact ih htl

/-- the contrapositive of `groupMembersT_preserve`: `none` in the
final env is `none` at the base. -/
theorem groupMembersT_none {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)}
    (hmem : Declarative.GroupMembersT S E ms E') {r' : Nat}
    (h : E'.members r' = none) : E.members r' = none := by
  cases hm : E.members r' with
  | some m' =>
      have hE' := groupMembersT_preserve hmem _ _ hm
      rw [h] at hE'
      cases hE'
  | none => rfl

/-- `none` in the final env is off every group ref. -/
theorem groupMembersT_ref_none {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)}
    (hmem : Declarative.GroupMembersT S E ms E') {r' : Nat}
    (h : E'.members r' = none) : r' ∉ ms.map Prod.fst := by
  intro hr
  rcases List.mem_map.mp hr with ⟨⟨r'', m''⟩, hin, hfst⟩
  have hr'' : r'' = r' := hfst
  subst hr''
  rw [groupMembersT_installed hmem hin] at h
  cases h

/-- a singleton extension of a `NoGroupEnv` env stays `NoGroupEnv`. -/
theorem noGroupEnv_of_extend {E : Declarative.ResolvedEnv} {r m}
    (hfresh : E.members r = none)
    (hng : Declarative.NoGroupEnv (Declarative.extendEnv E r m)) :
    Declarative.NoGroupEnv E :=
  fun r' m' hm' =>
    hng r' m' (Declarative.members_extend_preserved hfresh _ _ hm')

/-- `none` in an extended env is `none` in the base, off the step's
ref. -/
theorem extendEnv_ne_none {E : Declarative.ResolvedEnv} {r : Nat}
    {m : Declarative.CheckedMember} {r' : Nat}
    (h : (Declarative.extendEnv E r m).members r' = none) :
    r' ≠ r ∧ E.members r' = none := by
  have hne : r' ≠ r := by
    intro he
    subst he
    rw [Declarative.members_extend_eq] at h
    cases h
  refine ⟨hne, ?_⟩
  rw [Declarative.members_extend_ne E r m r' hne] at h
  exact h

/-! ### `muOf` structural lemmas -/

/-- a singleton `muOf` step agrees with its prefix μ on prefix members
(the step's `hstep` equation is `muOf`'s own clause, so `hstep` is
`rfl` at every use site). -/
theorem muOf_agree_singleton {gden : GDen} {E E' : Declarative.ResolvedEnv}
    {r : Nat} {d : List Nat → PS} (hE : Declarative.EnvWfT E)
    (h' : Declarative.EnvWfT E') (hfresh : E.members r = none)
    (hstep : muOf gden h' = muStepAt (muOf gden hE) r d)
    {r' : Nat} {m' : Declarative.CheckedMember}
    (hm' : E.members r' = some m') (nls : List Nat) :
    muOf gden h' r' nls = muOf gden hE r' nls := by
  have hne : r' ≠ r := by
    intro he
    subst he
    rw [hfresh] at hm'
    cases hm'
  rw [hstep, muStepAt_ne _ _ _ hne]

/-- a `group` `muOf` step agrees with its prefix μ on prefix members —
this is `GDenOk`'s first conjunct. -/
theorem muOf_agree_group {gden : GDen} (hg : GDenOk gden)
    {S E E' : Declarative.ResolvedEnv}
    {ms : List (Nat × Declarative.CheckedMember)}
    (hmem : Declarative.GroupMembersT S E ms E') (μ : Nat → List Nat → PS)
    {r' : Nat} {m' : Declarative.CheckedMember}
    (hm' : E.members r' = some m') (nls : List Nat) :
    gden hmem μ r' nls = μ r' nls :=
  (hg hmem μ).1 _ _ hm' nls

/-- a `NoGroupEnv` env never calls `gden`: `muOf` is pointwise
independent of the group-layer implementation. -/
theorem muOf_gden_irrel (g₁ g₂ : GDen) {E : Declarative.ResolvedEnv} :
    (h : Declarative.EnvWfT E) → Declarative.NoGroupEnv E →
      ∀ r nls, muOf g₁ h r nls = muOf g₂ h r nls
  | .empty, _ => fun _ _ => rfl
  | .axiom _ r _ _ hE hfresh .., hng => fun r' nls => by
      by_cases hr : r' = r
      · rw [hr]
        show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r nls
        rw [muStepAt_eq, muStepAt_eq]
      · show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r' nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r' nls
        rw [muStepAt_ne _ _ _ hr, muStepAt_ne _ _ _ hr]
        exact muOf_gden_irrel g₁ g₂ hE
          (noGroupEnv_of_extend hfresh hng) r' nls
  | .definition _ r _ v _ hE hfresh .., hng => fun r' nls => by
      by_cases hr : r' = r
      · rw [hr]
        show muStepAt (muOf g₁ hE) r _ r nls =
             muStepAt (muOf g₂ hE) r _ r nls
        rw [muStepAt_eq, muStepAt_eq]
        show den (muOf g₁ hE) _ _ v = den (muOf g₂ hE) _ _ v
        exact den_consts_agree _ _ v
          (fun r' nls _ => muOf_gden_irrel g₁ g₂ hE
            (noGroupEnv_of_extend hfresh hng) r' nls)
      · show muStepAt (muOf g₁ hE) r _ r' nls =
             muStepAt (muOf g₂ hE) r _ r' nls
        rw [muStepAt_ne _ _ _ hr, muStepAt_ne _ _ _ hr]
        exact muOf_gden_irrel g₁ g₂ hE
          (noGroupEnv_of_extend hfresh hng) r' nls
  | .thm _ r _ _ hE hfresh .., hng => fun r' nls => by
      by_cases hr : r' = r
      · rw [hr]
        show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r nls
        rw [muStepAt_eq, muStepAt_eq]
      · show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r' nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r' nls
        rw [muStepAt_ne _ _ _ hr, muStepAt_ne _ _ _ hr]
        exact muOf_gden_irrel g₁ g₂ hE
          (noGroupEnv_of_extend hfresh hng) r' nls
  | .opaque _ r _ _ _ hE hfresh .., hng => fun r' nls => by
      by_cases hr : r' = r
      · rw [hr]
        show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r nls
        rw [muStepAt_eq, muStepAt_eq]
      · show muStepAt (muOf g₁ hE) r (fun _ => junk₀) r' nls =
             muStepAt (muOf g₂ hE) r (fun _ => junk₀) r' nls
        rw [muStepAt_ne _ _ _ hr, muStepAt_ne _ _ _ hr]
        exact muOf_gden_irrel g₁ g₂ hE
          (noGroupEnv_of_extend hfresh hng) r' nls
  | .group _ f fm _ _ _ E' hE hfam _ _ hmem, hng => fun r' nls => by
      have hmemf : E'.members f = some fm :=
        groupMembersT_installed hmem (List.mem_cons_self _ _)
      exact absurd hfam (hng f fm hmemf).1

/-- `muOf` is `J₀` at non-members. -/
theorem muOf_nonmember {gden : GDen} (hg : GDenOk gden)
    {E : Declarative.ResolvedEnv} :
    (h : Declarative.EnvWfT E) → ∀ r', E.members r' = none →
      ∀ nls, muOf gden h r' nls = junk₀
  | .empty => fun _ _ _ => rfl
  | .axiom _ r _ _ hE _ .. => fun r' hr' nls => by
      obtain ⟨hne, hEn⟩ := extendEnv_ne_none hr'
      show muStepAt (muOf gden hE) r (fun _ => junk₀) r' nls = junk₀
      rw [muStepAt_ne _ _ _ hne]
      exact muOf_nonmember hg hE r' hEn nls
  | .definition _ r _ _ _ hE _ .. => fun r' hr' nls => by
      obtain ⟨hne, hEn⟩ := extendEnv_ne_none hr'
      show muStepAt (muOf gden hE) r _ r' nls = junk₀
      rw [muStepAt_ne _ _ _ hne]
      exact muOf_nonmember hg hE r' hEn nls
  | .thm _ r _ _ hE _ .. => fun r' hr' nls => by
      obtain ⟨hne, hEn⟩ := extendEnv_ne_none hr'
      show muStepAt (muOf gden hE) r (fun _ => junk₀) r' nls = junk₀
      rw [muStepAt_ne _ _ _ hne]
      exact muOf_nonmember hg hE r' hEn nls
  | .opaque _ r _ _ _ hE _ .. => fun r' hr' nls => by
      obtain ⟨hne, hEn⟩ := extendEnv_ne_none hr'
      show muStepAt (muOf gden hE) r (fun _ => junk₀) r' nls = junk₀
      rw [muStepAt_ne _ _ _ hne]
      exact muOf_nonmember hg hE r' hEn nls
  | .group E f fm ctors rr rm _ hE _ _ _ hmem => fun r' hr' nls => by
      have hEn : E.members r' = none := groupMembersT_none hmem hr'
      have hnr : r' ∉ ((f, fm) :: ctors ++ [(rr, rm)]).map Prod.fst :=
        groupMembersT_ref_none hmem hr'
      show gden hmem (muOf gden hE) r' nls = junk₀
      exact ((hg hmem (muOf gden hE)).2 r' hEn hnr nls).trans
        (muOf_nonmember hg hE r' hEn nls)

/-- packaged: `den` at an extended μ equals `den` at a prefix μ, on a
term whose `denRefs` are prefix members. -/
theorem den_prefix_agree {μ₁ μ₂ : Nat → List Nat → PS}
    {E : Declarative.ResolvedEnv} {e : Declarative.Expr Nat} (σ ν)
    (hrefs : ∀ r ∈ denRefs e, (E.members r).isSome)
    (hagree : ∀ r' m', E.members r' = some m' → ∀ nls, μ₂ r' nls = μ₁ r' nls) :
    den μ₂ σ ν e = den μ₁ σ ν e :=
  den_consts_agree σ ν e fun r nls hr => by
    have hm := hrefs r hr
    cases hmem : E.members r with
    | some m' => exact hagree r m' hmem nls
    | none => rw [hmem] at hm; exact absurd hm (by decide)

end PS

end Rcic.Model
