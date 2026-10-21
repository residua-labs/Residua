import rcic.RcicModelOps
import rcic.RcicLevelDec

/-!
# RcicModelDenote — the `⟦·⟧` evaluator and `⟦Γ⟧⁺` assignments

Lane R1-b segment S3 (scope: `sortRow` + consistency only;
`piRow`/`famAppRow` remain `W-F05b-PiRow`).

Denotation discipline (resolves the `U`-Cantor problem without a
universe set): every denotation is `⟨level-tag, payload⟩`-shaped —
`ordPair (ord lvl) payload` — where `lvl` is the level of the
denoted thing's *type*: `e : T`, `T : sort u` ⇒ `tagOf ⟦e⟧ ≈ ord u`
(the `uniform_taint`/`level-faithfulness` invariant is stated as
`tagOf ⟦e⟧ ≈ sUnion (tagOf ⟦T⟧)`, which is also what junk
propagates: `tagOf ∅ = ∅`).

- `⟦sort l⟧ = ⟨Declarative.evalTotal σ l + 2, ord (Declarative.evalTotal σ l)⟩` — sort
  denotations are injective in level by `ordPair_equiv`+`ord_inj`
  (the `sortRow` tooth).
- `⟦pi A B⟧ = ⟨imax+1, piSet'⟩`, `⟦lam A b⟧ = ⟨imax, graph⟩` —
  `imax` computed on tags by `imaxTag*` (`select` is the
  Prop-conditional on sets; `Equiv` is not decidable, so it goes
  through `sep`).
- `⟦app⟧ = fapp (payloadOf ⟦f⟧) ⟦x⟧`, `⟦letE⟧` substitutes,
  `⟦lit t⟧` unfolds `natExpand` into `μ`-applications,
  `⟦bvar⟧ = ν i`, `⟦const r ls⟧ = μ r (ls.map evalTotal)` where `μ`
  is the member interpretation supplied by `RcicModelEnv` (S4).

Membership is `MemAt`, not bare `∈`: `x ∈ payloadOf T`, or `x` is
junk, or `T` is a sort-code and `x` carries the matching level tag
(the sort arm needs no enumeration of level-`u` denotations — the
syntax-indexed universe was the Cantor wall).

`⟦Γ⟧⁺` is `Asn`: at `assumption A`, `ν i` is a `MemAt` of `⟦A⟧`
(evaluated at the `shiftν (i+1)` tail assignment) and `J₀` when
`⟦A⟧` is Prop-denoting; at `letBinding`, `ν i = ⟦v⟧` exactly.
`asnDefault` inhabits every context (junk at assumptions,
denotations at let bindings) — `⟦Γ⟧⁺` is never vacuous.

`closure_claim = 0`.
-/

namespace Rcic.Model

namespace PS

/-! ### Assignment combinators -/

/-- Push a value under a binder (de Bruijn). -/
def νcons (a : PS) (ν : Nat → PS) : Nat → PS
  | 0 => a
  | i + 1 => ν i

/-- Drop `k` leading bindings: the tail assignment for `Γ[i]`. -/
def shiftν (k : Nat) (ν : Nat → PS) (i : Nat) : PS := ν (i + k)

/-- `ν[j ↦ a]` with reindexing — the `instantiate` assignment:
`i = j ↦ a`, `i > j ↦ ν (i-1)`, `i < j ↦ ν i`. -/
def νinsert (j : Nat) (a : PS) (ν : Nat → PS) (i : Nat) : PS :=
  if i = j then a else if j < i then ν (i - 1) else ν i

/-! ### Level-tag operations -/

/-- Set-conditional on a `Prop`: `select c A B ≈ A` if `c`, else
`≈ B`. `sep` keeps candidate elements satisfying the implication. -/
def select (c : Prop) (A B : PS) : PS :=
  sUnion (sep (fun z => (c → z ∈ A) ∧ (¬ c → z ∈ B)) (sUnion (pair A B)))

/-- `imax u v` on *level-of-type* tags `ta = ord (u+1)`,
`tb = ord (v+1)`, producing `ord (imax u v)` — the element-level tag
for `lam`. `v = 0` collapses to `ord 0`. -/
def imaxTag (ta tb : PS) : PS :=
  select (Equiv (sUnion tb) pempty) pempty (sUnion (sUnion (pair ta tb)))

/-- `imax u v + 1` on the same tags — the type-level tag for `pi`. -/
def imaxTag1 (ta tb : PS) : PS :=
  select (Equiv (sUnion tb) pempty) (ord 1) (sUnion (pair ta tb))

/-! ### The denotation -/

/-- `⟦lit t⟧` unfolds `natExpand`: `litZero = const 1 []`,
`litSucc e = app (const 2 []) e`. -/
def denLit (μ : Nat → List Nat → PS) (t : Nat) : PS :=
  Nat.rec (μ 1 []) (fun _ acc => fapp (payloadOf (μ 2 [])) acc) t

/-- `⟦e⟧ μ σ ν` — member interpretation `μ`, level assignment `σ`
(for `evalTotal` on `Level`), bvar assignment `ν`. -/
def den (μ : Nat → List Nat → PS) (σ : Nat → Nat) (ν : Nat → PS) :
    Declarative.Expr Nat → PS
  | .bvar i => ν i
  | .sort l =>
      ordPair (ord (Declarative.evalTotal σ l + 2)) (ord (Declarative.evalTotal σ l))
  | .const r ls => μ r (ls.map (Declarative.evalTotal σ))
  | .app f x => fapp (payloadOf (den μ σ ν f)) (den μ σ ν x)
  | .lam A b =>
      ordPair
        (imaxTag (tagOf (den μ σ ν A)) (tagOf (den μ σ (νcons junk₀ ν) b)))
        (mkLam (fun a => den μ σ (νcons a ν) b) (payloadOf (den μ σ ν A)))
  | .pi A B =>
      ordPair
        (imaxTag1 (tagOf (den μ σ ν A)) (tagOf (den μ σ (νcons junk₀ ν) B)))
        (piSet (payloadOf (den μ σ ν A))
          (fun a => payloadOf (den μ σ (νcons a ν) B)))
  | .letE _ v b => den μ σ (νcons (den μ σ ν v) ν) b
  | .lit t => denLit μ t

/-- `den` commutes with `natExpand`: the `lit` clause computes the
expansion directly. -/
theorem den_natExpand (μ : Nat → List Nat → PS) (σ : Nat → Nat) (ν : Nat → PS) :
    ∀ t, den μ σ ν (Declarative.natExpand t) = denLit μ t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      show den μ σ ν (.app (.const 2 []) (Declarative.natExpand n)) = _
      rw [den, ih]
      rfl

/-! ### Membership and `⟦Γ⟧⁺` -/

/-- `x` is a `⁺`-element of `T`: a payload member, junk (`J₀`/`J₁`),
or — when `T` is a sort-code `⟨u+2, ord u⟩` — a `u+1`-tagged value
(level-`u` type). -/
def MemAt (x T : PS) : Prop :=
  x ∈ payloadOf T ∨ Equiv x junk₀ ∨ Equiv x junk₁ ∨
    ∃ u : Nat, Equiv T (ordPair (ord (u + 2)) (ord u)) ∧
      Equiv (tagOf x) (ord (u + 1))

/-- `T` denotes a Prop (`T : sort 0` ⇒ `tagOf T ≈ ord 1`). -/
def PropDen (T : PS) : Prop := Equiv (tagOf T) (ord 1)

/-- One context entry's assignment obligation: assumptions bind a
`MemAt` (forced to `J₀` at Prop), let bindings bind the value's
denotation exactly (`zetaLocal`). -/
def AsnAt (μ : Nat → List Nat → PS) (σ : Nat → Nat) (ν : Nat → PS)
    (i : Nat) : Declarative.LocalDecl → Prop
  | .assumption A =>
      MemAt (ν i) (den μ σ (shiftν (i + 1) ν) A) ∧
      (PropDen (den μ σ (shiftν (i + 1) ν) A) → Equiv (ν i) junk₀)
  | .letBinding _ v => Equiv (ν i) (den μ σ (shiftν (i + 1) ν) v)

/-- `⟦Γ⟧⁺` — every binder position satisfies `AsnAt`. -/
def Asn (μ : Nat → List Nat → PS) (σ : Nat → Nat) (ν : Nat → PS)
    (Γ : Declarative.LCtx) : Prop :=
  ∀ i d, Γ.get? i = some d → AsnAt μ σ ν i d

/-- The default `⟦Γ⟧⁺` assignment: junk at assumptions, the bound
value's denotation at let bindings. -/
noncomputable def asnDefault (μ : Nat → List Nat → PS) (σ : Nat → Nat) :
    Declarative.LCtx → Nat → PS
  | [] => fun _ => junk₀
  | .assumption _ :: Γ =>
      fun i => match i with | 0 => junk₀ | i + 1 => asnDefault μ σ Γ i
  | .letBinding _ v :: Γ =>
      fun i => match i with
        | 0 => den μ σ (asnDefault μ σ Γ) v
        | i + 1 => asnDefault μ σ Γ i

/-! ### `≈`-congruence for the evaluator's combinators -/

/-- `sImage` congruence: pointwise `≈` on elements. -/
theorem sImage_congr {h h' : PS → PS} {s s' : PS}
    (hh : ∀ a a', Equiv a a' → Equiv (h a) (h' a')) (hs : Equiv s s') :
    Equiv (sImage h s) (sImage h' s') := by
  apply ext; intro x; constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hs.exists_mem_left i
    exact ⟨j, (hh _ _ hj).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hs.exists_mem_right i
    exact ⟨j, (hh _ _ hj).trans hi⟩

/-- `sep` congruence: predicate transports along `≈`. -/
theorem sep_congr {p p' : PS → Prop} {s s' : PS}
    (hp : ∀ a b, Equiv a b → (p a → p' b))
    (hp' : ∀ a b, Equiv a b → (p' a → p b))
    (hs : Equiv s s') :
    Equiv (sep p s) (sep p' s') := by
  apply ext; intro x; constructor
  · intro hx
    obtain ⟨i, hpi, hix⟩ := mem_sep.mp hx
    obtain ⟨j, hj⟩ := hs.exists_mem_left i
    exact mem_sep.mpr ⟨j, hp _ _ hj hpi, hj.symm.trans hix⟩
  · intro hx
    obtain ⟨i, hpi, hix⟩ := mem_sep.mp hx
    obtain ⟨j, hj⟩ := hs.exists_mem_right i
    exact mem_sep.mpr ⟨j, hp' _ _ hj.symm hpi, hj.trans hix⟩

/-- `fapp` congruence. -/
theorem fapp_congr {F F' a a' : PS}
    (hF : Equiv F F') (ha : Equiv a a') :
    Equiv (fapp F a) (fapp F' a') :=
  sUnion_congr (sep_congr
    (fun _ _ hb hab =>
      mem_congr_right hF (mem_congr_left (ordPair_congr ha hb) hab))
    (fun _ _ hb hab =>
      mem_congr_right hF.symm
        (mem_congr_left (ordPair_congr ha.symm hb) hab))
    (sUnion_congr (sUnion_congr hF)))

/-- `mkLam` congruence. -/
theorem mkLam_congr {g g' : PS → PS} {A A' : PS}
    (hg : ∀ a a', Equiv a a' → Equiv (g a) (g' a')) (hA : Equiv A A') :
    Equiv (mkLam g A) (mkLam g' A') :=
  sImage_congr (fun _ _ h => ordPair_congr h (hg _ _ h)) hA

/-- `payloadOf` congruence. -/
theorem payloadOf_congr {s s' : PS} (hs : Equiv s s') :
    Equiv (payloadOf s) (payloadOf s') :=
  sUnion_congr (sep_congr
    (fun _ _ hz ⟨c, hc⟩ =>
      ⟨c, (hs.symm.trans (hc.trans (ordPair_congr Equiv.rfl hz)))⟩)
    (fun _ _ hz ⟨c, hc⟩ =>
      ⟨c, (hs.trans (hc.trans (ordPair_congr Equiv.rfl hz)))⟩)
    (sUnion_congr hs))

/-- `select` congruence, `c`/`c'` iff-variant. -/
theorem select_congr' {c c' : Prop} {A A' B B' : PS}
    (hc : c ↔ c') (hA : Equiv A A') (hB : Equiv B B') :
    Equiv (select c A B) (select c' A' B') :=
  sUnion_congr (sep_congr
    (fun _ _ hz h =>
      ⟨fun hcc => mem_congr_right hA
          (mem_congr_left hz (h.1 (hc.mpr hcc))),
       fun hnc => mem_congr_right hB
          (mem_congr_left hz (h.2 (fun hcc => hnc (hc.mp hcc))))⟩)
    (fun _ _ hz h =>
      ⟨fun hcc => mem_congr_right hA.symm
          (mem_congr_left hz (h.1 (hc.mp hcc))),
       fun hnc => mem_congr_right hB.symm
          (mem_congr_left hz (h.2 (fun hcc => hnc (hc.mpr hcc))))⟩)
    (sUnion_congr (pair_congr hA hB)))

/-- `imaxTag` congruence. -/
theorem imaxTag_congr {ta ta' tb tb' : PS}
    (ha : Equiv ta ta') (hb : Equiv tb tb') :
    Equiv (imaxTag ta tb) (imaxTag ta' tb') :=
  select_congr'
    ⟨(fun h => (sUnion_congr hb).symm.trans h),
     (fun h => (sUnion_congr hb).trans h)⟩
    Equiv.rfl (sUnion_congr (sUnion_congr (pair_congr ha hb)))

/-- `imaxTag1` congruence. -/
theorem imaxTag1_congr {ta ta' tb tb' : PS}
    (ha : Equiv ta ta') (hb : Equiv tb tb') :
    Equiv (imaxTag1 ta tb) (imaxTag1 ta' tb') :=
  select_congr'
    ⟨(fun h => (sUnion_congr hb).symm.trans h),
     (fun h => (sUnion_congr hb).trans h)⟩
    Equiv.rfl (sUnion_congr (pair_congr ha hb))

/-- Membership in `powerset` is subset inclusion. -/
theorem mem_powerset {x s : PS} :
    x ∈ powerset s ↔ (∀ y, y ∈ x → y ∈ s) := by
  cases s with
  | mk α f =>
    constructor
    · rintro ⟨P, hP⟩ y hy
      obtain ⟨a, ha⟩ := hy
      obtain ⟨⟨a', hPa'⟩, hfa'⟩ := hP.exists_mem_right a
      exact mem_congr_left (hfa'.trans ha) ⟨a', Equiv.refl _⟩
    · intro hsub
      refine ⟨fun a => f a ∈ x, ?_⟩
      apply ext; intro z; constructor
      · rintro ⟨⟨a, hPa⟩, hfa⟩
        obtain ⟨i, hi⟩ := hPa
        exact mem_congr_left (hi.trans hfa) ⟨i, Equiv.refl _⟩
      · rintro ⟨i, hi⟩
        obtain ⟨a, ha⟩ := hsub (x.Func i) ⟨i, Equiv.refl _⟩
        exact ⟨⟨a, mem_congr_left ha.symm ⟨i, Equiv.refl _⟩⟩,
          ha.trans hi⟩

/-- `powerset` congruence. -/
theorem powerset_congr {s s' : PS} (hs : Equiv s s') :
    Equiv (powerset s) (powerset s') :=
  ext fun _x => (mem_powerset.trans
    ⟨(fun h y hy => mem_congr_right hs (h y hy)),
     (fun h y hy => mem_congr_right hs.symm (h y hy))⟩).trans
    mem_powerset.symm

/-- `prod` congruence. -/
theorem prod_congr {A A' B B' : PS}
    (hA : Equiv A A') (hB : Equiv B B') :
    Equiv (prod A B) (prod A' B') :=
  sUnion_congr (sImage_congr
    (fun _ _ h => sImage_congr (fun _ _ h' => ordPair_congr h h') hB) hA)

/-- `isFuncOnDep` transports along `≈`. -/
theorem isFuncOnDep_equiv {A A' : PS} {B B' : PS → PS} {g g' : PS}
    (hA : Equiv A A') (hB : ∀ a a', Equiv a a' → Equiv (B a) (B' a'))
    (hg : Equiv g g')
    (h : isFuncOnDep A B g) : isFuncOnDep A' B' g' := by
  obtain ⟨hdom, hcod, huniq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hdom a (mem_congr_right hA.symm ha)
    exact ⟨b, mem_congr_right (hB _ _ Equiv.rfl) hb,
      mem_congr_right hg hab⟩
  · intro p hp
    obtain ⟨a, ha, b, hb, hp'⟩ := hcod p (mem_congr_right hg.symm hp)
    exact ⟨a, mem_congr_right hA ha, b,
      mem_congr_right (hB _ _ Equiv.rfl) hb, hp'⟩
  · intro a b b' h1 h2
    exact huniq a b b' (mem_congr_right hg.symm h1)
      (mem_congr_right hg.symm h2)

/-- `piSet` congruence. -/
theorem piSet_congr {A A' : PS} {B B' : PS → PS}
    (hA : Equiv A A') (hB : ∀ a a', Equiv a a' → Equiv (B a) (B' a')) :
    Equiv (piSet A B) (piSet A' B') :=
  sep_congr
    (fun _ _ haa' h => isFuncOnDep_equiv hA hB haa' h)
    (fun _ _ haa' h =>
      isFuncOnDep_equiv hA.symm
        (fun a a' he => (hB a' a he.symm).symm) haa' h)
    (powerset_congr (prod_congr hA
      (sUnion_congr (sImage_congr hB hA))))

/-! ### Assignment algebra -/

/-- The `lift` assignment: `lift k j e` read at `ν` is `e` read at
`liftν k j ν` (positions ≥ `k` shifted by `j`). -/
def liftν (k j : Nat) (ν : Nat → PS) (i : Nat) : PS :=
  if i < k then ν i else ν (i + j)

/-- `liftν 0 j` is `shiftν j`. -/
theorem liftν_zero (j : Nat) (ν : Nat → PS) :
    liftν 0 j ν = shiftν j ν :=
  funext fun i => if_neg (Nat.not_lt_zero i)

/-- `liftν` commutes with `νcons`. -/
theorem liftν_cons (k j : Nat) (a : PS) (ν : Nat → PS) :
    liftν (k + 1) j (νcons a ν) = νcons a (liftν k j ν) := by
  funext i; cases i with
  | zero =>
    show (if 0 < k + 1 then νcons a ν 0 else νcons a ν (0 + j)) = _
    rw [if_pos (Nat.zero_lt_succ k)]; rfl
  | succ i =>
    show (if i + 1 < k + 1 then νcons a ν (i + 1) else
        νcons a ν (i + 1 + j)) = (if i < k then ν i else ν (i + j))
    by_cases h : i + 1 < k + 1
    · rw [if_pos h, if_pos (Nat.lt_of_succ_lt_succ h)]; rfl
    · rw [if_neg h, if_neg (fun hc => h (Nat.succ_lt_succ hc))]
      show νcons a ν (i + 1 + j) = ν (i + j)
      rw [Nat.add_comm (i + 1) j, Nat.add_one, Nat.add_succ,
        Nat.add_comm j i]; rfl

/-- `νinsert` commutes with `νcons` (index pushed past the binder). -/
theorem νinsert_succ_cons (j : Nat) (a v : PS) (ν : Nat → PS) :
    νinsert (j + 1) a (νcons v ν) = νcons v (νinsert j a ν) := by
  funext i; cases i with
  | zero =>
    show (if 0 = j + 1 then a else if j + 1 < 0 then
        νcons v ν (0 - 1) else νcons v ν 0) = v
    rw [if_neg (Ne.symm (Nat.succ_ne_zero j)),
        if_neg (Nat.not_lt_zero _)]; rfl
  | succ i =>
    show (if i + 1 = j + 1 then a else if j + 1 < i + 1 then
        νcons v ν (i + 1 - 1) else νcons v ν (i + 1)) =
        (if i = j then a else if j < i then ν (i - 1) else ν i)
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (mt Nat.add_right_cancel hij), if_neg hij]
      by_cases hji : j < i
      · rw [if_pos (Nat.succ_lt_succ hji), if_pos hji]
        cases i with
        | zero => exact absurd hji (Nat.not_lt_zero j)
        | succ i => rfl
      · rw [if_neg (mt Nat.lt_of_succ_lt_succ hji), if_neg hji]; rfl

/-- `shiftν` at zero is the identity. -/
theorem shiftν_zero (ν : Nat → PS) : shiftν 0 ν = ν := rfl

/-- `shiftν` past a `νcons` drops the cons. -/
theorem shiftν_succ_cons (k : Nat) (a : PS) (ν : Nat → PS) :
    shiftν (k + 1) (νcons a ν) = shiftν k ν := rfl

/-! ### `den` commutation lemmas -/

/-- `evalTotal` commutes with `lvlSubst` (the total-evaluator form
of `eval_lvlSubst`). -/
theorem evalTotal_lvlSubst (σ : Nat → Nat)
    (τ : Declarative.Level → Declarative.Level) (l : Declarative.Level) :
    Declarative.evalTotal σ (Declarative.lvlSubst τ l) =
      Declarative.evalTotal
        (fun i => Declarative.evalTotal σ (τ (.param i))) l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [Declarative.lvlSubst, Declarative.evalTotal, ih]
  | max a b iha ihb =>
      simp only [Declarative.lvlSubst, Declarative.evalTotal, iha, ihb]
  | imax a b iha ihb =>
      simp only [Declarative.lvlSubst, Declarative.evalTotal, iha, ihb]
  | param i => rfl

/-- Level evaluation commutes with `instLevel`. -/
theorem evalTotal_instLevel (σ : Nat → Nat) (ls : List Declarative.Level)
    (l : Declarative.Level) :
    Declarative.evalTotal σ (Declarative.instLevel ls l) =
      Declarative.evalTotal
        (fun i => ((ls.map (Declarative.evalTotal σ))[i]?).getD (σ i)) l := by
  show Declarative.evalTotal σ
      (Declarative.lvlSubst (Declarative.levelParamSubst ls) l) = _
  rw [evalTotal_lvlSubst]
  congr 1
  funext i
  show Declarative.evalTotal σ ((ls[i]?).getD (.param i)) =
      ((ls.map (Declarative.evalTotal σ))[i]?).getD (σ i)
  rw [List.getElem?_map]
  cases h : ls[i]? with
  | none => rfl
  | some l' => rfl

/-- `νcons` then `shiftν 1` collapses to the tail. -/
theorem shiftν_one_cons (a : PS) (ν : Nat → PS) :
    shiftν 1 (νcons a ν) = ν :=
  funext fun _ => rfl

/-- Pointwise `≈` on assignments. -/
def νeq (ν ν' : Nat → PS) : Prop := ∀ i, Equiv (ν i) (ν' i)

theorem νeq_refl (ν : Nat → PS) : νeq ν ν := fun _ => Equiv.refl _

/-- `νcons` preserves pointwise `≈`. -/
theorem νeq_cons {a a' : PS} {ν ν' : Nat → PS}
    (h : Equiv a a') (hν : νeq ν ν') : νeq (νcons a ν) (νcons a' ν') := by
  intro i; cases i with
  | zero => exact h
  | succ i => exact hν i

/-- `tagOf` congruence (first projection). -/
theorem tagOf_congr {s s' : PS} (hs : Equiv s s') :
    Equiv (tagOf s) (tagOf s') := pfst_congr hs

/-- `den` respects pointwise-`≈` assignments. -/
theorem den_congr (μ : Nat → List Nat → PS) (σ : Nat → Nat)
    (e : Declarative.Expr Nat) :
    ∀ {ν ν' : Nat → PS}, νeq ν ν' →
      Equiv (den μ σ ν e) (den μ σ ν' e) := by
  induction e with
  | bvar i => intro _ _ hν; exact hν i
  | sort l => intro _ _ _; exact Equiv.refl _
  | const r ms => intro _ _ _; exact Equiv.refl _
  | lit t => intro _ _ _; exact Equiv.refl _
  | app f x ihf ihx =>
    intro _ _ hν
    exact fapp_congr (payloadOf_congr (ihf hν)) (ihx hν)
  | lam A b ihA ihb =>
    intro _ _ hν
    exact ordPair_congr
      (imaxTag_congr (tagOf_congr (ihA hν))
        (tagOf_congr (ihb (νeq_cons (Equiv.refl junk₀) hν))))
      (mkLam_congr (fun _ _ haa' => ihb (νeq_cons haa' hν))
        (payloadOf_congr (ihA hν)))
  | pi A B ihA ihB =>
    intro _ _ hν
    exact ordPair_congr
      (imaxTag1_congr (tagOf_congr (ihA hν))
        (tagOf_congr (ihB (νeq_cons (Equiv.refl junk₀) hν))))
      (piSet_congr (payloadOf_congr (ihA hν))
        (fun _ _ haa' => payloadOf_congr (ihB (νeq_cons haa' hν))))
  | letE _ v b _ ihv ihb =>
    intro _ _ hν
    exact ihb (νeq_cons (ihv hν) hν)

/-- `den` commutes with `lift` via `liftν`. -/
theorem den_lift (μ : Nat → List Nat → PS) (σ : Nat → Nat)
    (e : Declarative.Expr Nat) :
    ∀ {ν : Nat → PS} {k j : Nat},
      den μ σ ν (Declarative.lift k j e) =
        den μ σ (liftν k j ν) e := by
  induction e with
  | bvar i =>
    intro ν k j
    show den μ σ ν (ite (k ≤ i) (.bvar (i + j)) (.bvar i)) = _
    by_cases h : k ≤ i
    · rw [if_pos h]
      show ν (i + j) = (if i < k then ν i else ν (i + j))
      rw [if_neg (Nat.not_lt_of_le h)]
    · rw [if_neg h]
      show ν i = (if i < k then ν i else ν (i + j))
      rw [if_pos (Nat.lt_of_not_le h)]
  | sort l => intro _ _ _; rfl
  | const r ms => intro _ _ _; rfl
  | lit t => intro _ _ _; rfl
  | app f x ihf ihx =>
    intro _ _ _
    simp only [Declarative.lift, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro _ _ _
    simp only [Declarative.lift, den, ihA, ihb, liftν_cons]
  | pi A B ihA ihB =>
    intro _ _ _
    simp only [Declarative.lift, den, ihA, ihB, liftν_cons]
  | letE _ v b _ ihv ihb =>
    intro _ _ _
    simp only [Declarative.lift, den, ihv, ihb, liftν_cons]

/-- `den` commutes with `instantiate` via `νinsert`. -/
theorem den_instantiate (μ : Nat → List Nat → PS) (σ : Nat → Nat)
    (e : Declarative.Expr Nat) :
    ∀ {ν : Nat → PS} {j : Nat} {rep : Declarative.Expr Nat},
      den μ σ ν (Declarative.instantiate j rep e) =
        den μ σ (νinsert j (den μ σ ν rep) ν) e := by
  induction e with
  | bvar i =>
    intro ν j rep
    show den μ σ ν (ite (i = j) rep
        (ite (j < i) (.bvar (i - 1)) (.bvar i))) =
        νinsert j (den μ σ ν rep) ν i
    by_cases hij : i = j
    · rw [if_pos hij]
      show den μ σ ν rep = (if i = j then den μ σ ν rep
          else if j < i then ν (i - 1) else ν i)
      rw [if_pos hij]
    · rw [if_neg hij]
      by_cases hji : j < i
      · rw [if_pos hji]
        show ν (i - 1) = (if i = j then den μ σ ν rep
            else if j < i then ν (i - 1) else ν i)
        rw [if_neg hij, if_pos hji]
      · rw [if_neg hji]
        show ν i = (if i = j then den μ σ ν rep
            else if j < i then ν (i - 1) else ν i)
        rw [if_neg hij, if_neg hji]
  | sort l => intro _ _ _; rfl
  | const r ms => intro _ _ _; rfl
  | lit t => intro _ _ _; rfl
  | app f x ihf ihx =>
    intro _ _ _
    simp only [Declarative.instantiate, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro ν j rep
    have hrep : ∀ x : PS,
        den μ σ (νcons x ν) (Declarative.lift 0 1 rep) =
          den μ σ ν rep := by
      intro x
      rw [den_lift, liftν_zero, shiftν_one_cons]
    simp only [Declarative.instantiate, den, ihA, ihb, hrep,
      νinsert_succ_cons]
  | pi A B ihA ihB =>
    intro ν j rep
    have hrep : ∀ x : PS,
        den μ σ (νcons x ν) (Declarative.lift 0 1 rep) =
          den μ σ ν rep := by
      intro x
      rw [den_lift, liftν_zero, shiftν_one_cons]
    simp only [Declarative.instantiate, den, ihA, ihB, hrep,
      νinsert_succ_cons]
  | letE _ v b _ ihv ihb =>
    intro ν j rep
    have hrep : ∀ x : PS,
        den μ σ (νcons x ν) (Declarative.lift 0 1 rep) =
          den μ σ ν rep := by
      intro x
      rw [den_lift, liftν_zero, shiftν_one_cons]
    simp only [Declarative.instantiate, den, ihv, ihb, hrep,
      νinsert_succ_cons]

/-- `den` commutes with `instantiateLevels` via `evalTotal_instLevel`. -/
theorem den_instantiateLevels (μ : Nat → List Nat → PS) (σ : Nat → Nat)
    (e : Declarative.Expr Nat) :
    ∀ {ν : Nat → PS} (ls : List Declarative.Level),
      den μ σ ν (Declarative.instantiateLevels ls e) =
        den μ (fun i =>
          ((ls.map (Declarative.evalTotal σ))[i]?).getD (σ i)) ν e := by
  induction e with
  | bvar i => intro _ _; rfl
  | lit t => intro _ _; rfl
  | sort l =>
    intro ν ls
    simp only [Declarative.instantiateLevels, den, evalTotal_instLevel]
  | const r ms =>
    intro ν ls
    simp only [Declarative.instantiateLevels, den]
    congr 1
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      simp only [List.map_cons, Function.comp, evalTotal_instLevel, ih]
  | app f x ihf ihx =>
    intro _ _
    simp only [Declarative.instantiateLevels, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro _ _
    simp only [Declarative.instantiateLevels, den, ihA, ihb]
  | pi A B ihA ihB =>
    intro _ _
    simp only [Declarative.instantiateLevels, den, ihA, ihB]
  | letE _ v b _ ihv ihb =>
    intro _ _
    simp only [Declarative.instantiateLevels, den, ihv, ihb]

end PS
end Rcic.Model
