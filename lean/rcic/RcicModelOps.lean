import rcic.RcicModelPSet

/-!
# RcicModelOps — semantic operations on `PS`

Lane R1-b segment S2 (scope: `sortRow` + consistency only;
`piRow`/`famAppRow` remain `W-F05b-PiRow`). Risk-arm segment:
function application and graphs (eta), constructor tags (iota),
the `∈⁺`-well-founded recursor fold (junk fold), and `equivAt`
(level-flagged semantic equality — irr).

Encoding choices (see `R1B_S0_PLAN.md`):
- sorts denote by ordinal codes `sortCode u = ord u` — injective by
  `ord_inj`, cumulative via `ord_mem_iff`.
- functions are sets of Kuratowski pairs;
  `fapp F a = ⋃{b ∈ ⋃⋃F | ⟨a,b⟩ ∈ F}`.
- constructor values are `ctorVal c args = ⟨ord c, args⟩`: the level
  tag sits in the first projection; extraction is by `pfst` plus
  payload separation — junk values fold through to whatever `step`
  returns on junk extracts.
- `recFold` recurses on `TransGen elemOf` so it can fold constructor
  payloads below the surface (`arg ∈ t ∈ u ∈ s`).
- `equivAt u x y := u = 0 ∨ x ≈ y`: at sort-0 (Prop) all elements are
  identified; elsewhere extensional. This is `≈_T` with `PropDen`
  folded into the level flag (irr trivial; `sortRow` stays real
  because sort-types live at level ≥ 1).

`closure_claim = 0`.
-/

namespace Rcic.Model

namespace PS

/-! ### Congruence of the small combinators -/

theorem singleton_congr {a a' : PS} (h : Equiv a a') :
    Equiv (singleton a) (singleton a') := by
  apply ext; intro z
  constructor
  · intro hz; exact mem_singleton.mpr ((mem_singleton.mp hz).trans h)
  · intro hz; exact mem_singleton.mpr ((mem_singleton.mp hz).trans h.symm)

theorem pair_congr {a a' b b' : PS} (h₁ : Equiv a a') (h₂ : Equiv b b') :
    Equiv (pair a b) (pair a' b') := by
  apply ext; intro z
  constructor
  · intro hz
    rcases mem_pair.mp hz with h | h
    · exact mem_pair.mpr (Or.inl (h.trans h₁))
    · exact mem_pair.mpr (Or.inr (h.trans h₂))
  · intro hz
    rcases mem_pair.mp hz with h | h
    · exact mem_pair.mpr (Or.inl (h.trans h₁.symm))
    · exact mem_pair.mpr (Or.inr (h.trans h₂.symm))

theorem ordPair_congr {a a' b b' : PS} (h₁ : Equiv a a') (h₂ : Equiv b b') :
    Equiv (ordPair a b) (ordPair a' b') :=
  pair_congr (singleton_congr h₁) (pair_congr h₁ h₂)

/-- `⋃` respects `≈`. -/
theorem sUnion_congr {s s' : PS} (h : Equiv s s') :
    Equiv (sUnion s) (sUnion s') := by
  apply ext; intro z
  constructor <;> intro hz <;> obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
  · exact mem_sUnion.mpr ⟨t, mem_congr_right h ht, hz'⟩
  · exact mem_sUnion.mpr ⟨t, mem_congr_right h.symm ht, hz'⟩

/-! ### Membership lemmas -/

/-- `sep`'s members are members of `s`. -/
theorem mem_sep_subset {x : PS} {p : PS → Prop} {s : PS} :
    x ∈ sep p s → x ∈ s := by
  rintro ⟨⟨i, _⟩, hi⟩
  exact ⟨i, hi⟩

/-- `⋃{x} ≈ x`. -/
theorem sUnion_singleton {x : PS} : Equiv (sUnion (singleton x)) x := by
  apply ext; intro z
  constructor
  · intro h
    obtain ⟨t, ht, hz⟩ := mem_sUnion.mp h
    exact mem_congr_right (mem_singleton.mp ht) hz
  · intro h
    exact mem_sUnion.mpr ⟨x, mem_singleton.mpr Equiv.rfl, h⟩

/-- `⋃{A,B}` sees the members of `A` and of `B`. -/
theorem mem_sUnion_pair {z A B : PS} :
    z ∈ sUnion (pair A B) ↔ z ∈ A ∨ z ∈ B := by
  constructor
  · intro h
    obtain ⟨t, ht, hz⟩ := mem_sUnion.mp h
    rcases mem_pair.mp ht with ht | ht
    · exact Or.inl (mem_congr_right ht hz)
    · exact Or.inr (mem_congr_right ht hz)
  · rintro (h | h)
    · exact mem_sUnion.mpr ⟨A, mem_pair.mpr (Or.inl Equiv.rfl), h⟩
    · exact mem_sUnion.mpr ⟨B, mem_pair.mpr (Or.inr Equiv.rfl), h⟩

/-- The second component of a Kuratowski pair in `F` lives in `⋃⋃F`. -/
theorem mem_sUnion_sUnion_of_pair {F a b : PS} (h : ordPair a b ∈ F) :
    b ∈ sUnion (sUnion F) :=
  mem_sUnion.mpr ⟨pair a b,
    mem_sUnion.mpr ⟨ordPair a b, h, mem_pair.mpr (Or.inr Equiv.rfl)⟩,
    mem_pair.mpr (Or.inr Equiv.rfl)⟩

/-- Likewise the first component. -/
theorem mem_sUnion_sUnion_of_pair_left {F a b : PS} (h : ordPair a b ∈ F) :
    a ∈ sUnion (sUnion F) :=
  mem_sUnion.mpr ⟨pair a b,
    mem_sUnion.mpr ⟨ordPair a b, h, mem_pair.mpr (Or.inr Equiv.rfl)⟩,
    mem_pair.mpr (Or.inl Equiv.rfl)⟩

/-! ### Ordered-pair projections -/

/-- Intersection `⋂ s` = elements of `⋃ s` living in every member. -/
def sInter (s : PS) : PS :=
  sep (fun x => ∀ t, t ∈ s → x ∈ t) (sUnion s)

/-- First projection of a Kuratowski pair (junk-safe):
`pfst p = ⋃ ⋂ p`. -/
def pfst (p : PS) : PS := sUnion (sInter p)

theorem mem_sInter {x s : PS} :
    x ∈ sInter s ↔ x ∈ sUnion s ∧ ∀ t, t ∈ s → x ∈ t := by
  constructor
  · rintro ⟨⟨i, hi⟩, hx⟩
    exact ⟨⟨i, hx⟩, fun t ht => mem_congr_left hx (hi t ht)⟩
  · rintro ⟨⟨i, hi⟩, hall⟩
    exact ⟨⟨i, fun t ht => mem_congr_left hi.symm (hall t ht)⟩, hi⟩

/-- `sInter` respects `≈`. -/
theorem sInter_congr {s s' : PS} (h : Equiv s s') :
    Equiv (sInter s) (sInter s') := by
  apply ext; intro z
  rw [mem_sInter, mem_sInter]
  constructor <;> rintro ⟨hz, hall⟩
  · exact ⟨mem_congr_right (sUnion_congr h) hz,
      fun t ht => hall t (mem_congr_right h.symm ht)⟩
  · exact ⟨mem_congr_right (sUnion_congr h.symm) hz,
      fun t ht => hall t (mem_congr_right h ht)⟩

theorem singleton_equiv {a b : PS} (h : Equiv (singleton a) (singleton b)) :
    Equiv a b :=
  mem_singleton.mp (mem_congr_right h (mem_singleton.mpr Equiv.rfl))

/-- The two-set case of Kuratowski injectivity: `{a,b} ≈ {c,d}` forces
the diagonal or the cross match (possibly both, when collapsed). -/
theorem pair_equiv {a b c d : PS}
    (h : Equiv (pair a b) (pair c d)) :
    (Equiv a c ∧ Equiv b d) ∨ (Equiv a d ∧ Equiv b c) := by
  have ha : a ∈ pair c d :=
    mem_congr_right h (mem_pair.mpr (Or.inl Equiv.rfl))
  have hb : b ∈ pair c d :=
    mem_congr_right h (mem_pair.mpr (Or.inr Equiv.rfl))
  rcases mem_pair.mp ha with hac | had
  · rcases mem_pair.mp hb with hbc | hbd
    · -- a≈c, b≈c: use d ∈ {a,b} to collapse
      have hd : d ∈ pair a b :=
        mem_congr_right h.symm (mem_pair.mpr (Or.inr Equiv.rfl))
      rcases mem_pair.mp hd with hda | hdb
      · -- d ≈ a ≈ c ⇒ c ≈ d; b ≈ c ⇒ b ≈ d
        exact Or.inl ⟨hac, hbc.trans (hda.trans hac).symm⟩
      · exact Or.inl ⟨hac, hdb.symm⟩
    · exact Or.inl ⟨hac, hbd⟩
  · rcases mem_pair.mp hb with hbc | hbd
    · exact Or.inr ⟨had, hbc⟩
    · -- a≈d, b≈d: use c ∈ {a,b} to collapse
      have hc : c ∈ pair a b :=
        mem_congr_right h.symm (mem_pair.mpr (Or.inl Equiv.rfl))
      rcases mem_pair.mp hc with hca | hcb
      · -- c ≈ a ≈ d ⇒ d ≈ c; b ≈ d ⇒ b ≈ c
        exact Or.inr ⟨had, hbd.trans (hca.trans had).symm⟩
      · exact Or.inr ⟨had, hcb.symm⟩

/-- Kuratowski-pair injectivity. -/
theorem ordPair_equiv {a b c d : PS}
    (h : Equiv (ordPair a b) (ordPair c d)) : Equiv a c ∧ Equiv b d := by
  rcases pair_equiv h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- {a}≈{c}, {a,b}≈{c,d}
    have hac : Equiv a c := singleton_equiv h1
    rcases pair_equiv h2 with ⟨_, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hac, hbd⟩
    · -- a≈d, b≈c; with a≈c: b ≈ c ≈ a ≈ d
      exact ⟨hac, hbc.trans (hac.symm.trans had)⟩
  · -- {a}≈{c,d}, {a,b}≈{c}: everything collapses
    have hca : Equiv c a :=
      mem_singleton.mp (mem_congr_right h1.symm
        (mem_pair.mpr (Or.inl Equiv.rfl)))
    have hda : Equiv d a :=
      mem_singleton.mp (mem_congr_right h1.symm
        (mem_pair.mpr (Or.inr Equiv.rfl)))
    have hbc : Equiv b c :=
      mem_singleton.mp (mem_congr_right h2
        (mem_pair.mpr (Or.inr Equiv.rfl)))
    exact ⟨hca.symm, hbc.trans hca |>.trans hda.symm⟩

/-- `⋂⟨a,b⟩ ≈ {a}`. -/
theorem sInter_ordPair {a b : PS} :
    Equiv (sInter (ordPair a b)) (singleton a) := by
  apply ext; intro z
  constructor
  · intro hz
    exact (mem_sInter.mp hz).2 _ (mem_pair.mpr (Or.inl Equiv.rfl))
  · intro hz
    have hza : Equiv z a := mem_singleton.mp hz
    refine mem_sInter.mpr ⟨?_, ?_⟩
    · exact mem_sUnion.mpr ⟨singleton a,
        mem_pair.mpr (Or.inl Equiv.rfl), mem_singleton.mpr hza⟩
    · intro t ht
      rcases mem_pair.mp ht with ht | ht
      · exact mem_congr_right ht.symm (mem_singleton.mpr hza)
      · exact mem_congr_right ht.symm (mem_pair.mpr (Or.inl hza))

/-- `pfst ⟨a,b⟩ ≈ a`. -/
theorem pfst_pair {a b : PS} : Equiv (pfst (ordPair a b)) a :=
  (sUnion_congr sInter_ordPair).trans sUnion_singleton

/-- `pfst` respects `≈`. -/
theorem pfst_congr {p q : PS} (h : Equiv p q) : Equiv (pfst p) (pfst q) :=
  sUnion_congr (sInter_congr h)

/-! ### Function space and application -/

/-- Function application: `fapp F a = ⋃{b ∈ ⋃⋃F | ⟨a,b⟩ ∈ F}` — the
value of a functional graph, junk-safe otherwise. -/
def fapp (F a : PS) : PS :=
  sUnion (sep (fun b => ordPair a b ∈ F) (sUnion (sUnion F)))

/-- Graph of `g` on `A`: `{⟨a, g a⟩ | a ∈ A}`. -/
def mkLam (g : PS → PS) (A : PS) : PS :=
  sImage (fun a => ordPair a (g a)) A

/-- `g` is a functional graph on `A` with values in `B`. -/
def isFuncOn (A B : PS) (g : PS) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B ∧ ordPair a b ∈ g) ∧
  (∀ p, p ∈ g → ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ Equiv p (ordPair a b)) ∧
  (∀ a b b', ordPair a b ∈ g → ordPair a b' ∈ g → Equiv b b')

/-- Dependent variant: values land in `B a`. -/
def isFuncOnDep (A : PS) (B : PS → PS) (g : PS) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B a ∧ ordPair a b ∈ g) ∧
  (∀ p, p ∈ g → ∃ a, a ∈ A ∧ ∃ b, b ∈ B a ∧ Equiv p (ordPair a b)) ∧
  (∀ a b b', ordPair a b ∈ g → ordPair a b' ∈ g → Equiv b b')

/-- Cartesian product `A × B` as a set of pairs. -/
def prod (A B : PS) : PS :=
  sUnion (sImage (fun a => sImage (ordPair a) B) A)

/-- Powerset `𝒫 s` = all `≈`-representable subsets, indexed by
predicates on the index type. -/
def powerset : PS → PS
  | mk α f => mk (α → Prop) fun P => mk { a : α // P a } fun ⟨a, _⟩ => f a

/-- Dependent function space. -/
def piSet (A : PS) (B : PS → PS) : PS :=
  sep (isFuncOnDep A B) (powerset (prod A (sUnion (sImage B A))))

/-- Cartesian product membership. -/
theorem mem_prod {p A B : PS} :
    p ∈ prod A B ↔ ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ Equiv p (ordPair a b) := by
  constructor
  · rintro ⟨⟨i, j⟩, hp⟩
    exact ⟨_, ⟨i, Equiv.refl _⟩, _, ⟨j, Equiv.refl _⟩, hp.symm⟩
  · rintro ⟨a, ⟨i, hi⟩, b, ⟨j, hj⟩, hp⟩
    exact ⟨⟨i, j⟩, (ordPair_congr hi hj).trans hp.symm⟩

/-- The value of a functional graph at `a`, given `⟨a,b⟩ ∈ F`, is `b`. -/
theorem fapp_eq_of_pair {A B F a b : PS} (hF : isFuncOn A B F)
    (hab : ordPair a b ∈ F) : Equiv (fapp F a) b := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
    obtain ⟨⟨i, hi⟩, ht'⟩ := ht
    -- hi : ordPair a (Func i) ∈ F; uniqueness ⇒ Func i ≈ b
    have hb : Equiv ((sUnion (sUnion F)).Func i) b := hF.2.2 a _ b hi hab
    exact mem_congr_right (ht'.symm.trans hb) hz'
  · intro hz
    -- b ∈ sep: rep-level via ⋃⋃F membership and ⟨a,b⟩ ∈ F
    obtain ⟨i, hi⟩ := mem_sUnion_sUnion_of_pair hab
    have hQi : ordPair a ((sUnion (sUnion F)).Func i) ∈ F :=
      mem_congr_left (ordPair_congr Equiv.rfl hi.symm) hab
    refine mem_sUnion.mpr ⟨(sUnion (sUnion F)).Func i, ⟨⟨i, hQi⟩, ?_⟩,
      ?_⟩
    · exact Equiv.refl _
    · exact mem_congr_right hi.symm hz

/-- Applying a graph built by `mkLam` at `a ∈ A` gives `g a`. -/
theorem fapp_mkLam {g : PS → PS}
    (hg : ∀ x y : PS, Equiv x y → Equiv (g x) (g y))
    {A a : PS} (ha : a ∈ A) :
    Equiv (fapp (mkLam g A) a) (g a) := by
  -- ⟨a, g a⟩ ∈ mkLam g A, and every ⟨a,·⟩ ∈ mkLam has · ≈ g a
  obtain ⟨i, hi⟩ := ha
  have hpair : ordPair a (g a) ∈ mkLam g A :=
    ⟨i, ordPair_congr hi (hg _ _ hi)⟩
  have hF : isFuncOn A (sImage g A) (mkLam g A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj⟩ := hx
      exact ⟨g (A.Func j), ⟨j, Equiv.refl _⟩,
        ⟨j, ordPair_congr hj Equiv.rfl⟩⟩
    · intro p hp
      obtain ⟨j, hj⟩ := hp
      exact ⟨A.Func j, ⟨j, Equiv.refl _⟩, g (A.Func j), ⟨j, Equiv.refl _⟩,
        hj.symm⟩
    · intro x b b' hb hb'
      obtain ⟨j, hj⟩ := hb
      obtain ⟨j', hj'⟩ := hb'
      obtain ⟨hxj, hbj⟩ := ordPair_equiv hj
      obtain ⟨hxj', hbj'⟩ := ordPair_equiv hj'
      -- b ≈ g(Aj) , b' ≈ g(Aj') , Aj ≈ x ≈ Aj' ⇒ b ≈ b'
      exact hbj.symm.trans ((hg _ _ (hxj.trans hxj'.symm)).trans hbj')
  exact fapp_eq_of_pair hF hpair

/-- Eta for graphs: re-graphing `fapp F` over `A` recovers `F`. -/
theorem mkLam_fapp {A B F : PS} (hF : isFuncOn A B F) :
    Equiv (mkLam (fun a => fapp F a) A) F := by
  apply ext; intro p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := hp
    -- hi : Equiv (ordPair (A.Func i) (fapp F (A.Func i))) p
    obtain ⟨b, _, hab⟩ := hF.1 (A.Func i) ⟨i, Equiv.refl _⟩
    have hfapp : Equiv (fapp F (A.Func i)) b := fapp_eq_of_pair hF hab
    exact mem_congr_left ((ordPair_congr Equiv.rfl hfapp.symm).trans hi) hab
  · intro hp
    obtain ⟨a, ha, b, _, hp'⟩ := hF.2.1 p hp
    obtain ⟨i, hi⟩ := ha
    -- ⟨Ai, b⟩ ∈ F by transport, so fapp (Ai) ≈ b
    have hab' : ordPair (A.Func i) b ∈ F :=
      mem_congr_left (hp'.trans (ordPair_congr hi.symm Equiv.rfl)) hp
    have hfapp : Equiv (fapp F (A.Func i)) b := fapp_eq_of_pair hF hab'
    exact ⟨i, (ordPair_congr hi hfapp).trans hp'.symm⟩

/-! ### Constructor tags and the recursor fold -/

/-- The denotation of `sort u`: the finite ordinal `u`. -/
def sortCode (u : Nat) : PS := ord u

/-- Constructor value: `⟨ord c, args⟩` — an ordered pair whose first
projection is the level/ctor tag ordinal. -/
def ctorVal (c : Nat) (args : PS) : PS := ordPair (ord c) args

/-- Tag extraction: the first projection. -/
def tagOf (s : PS) : PS := pfst s

/-- Payload extraction: elements `z` of `⋃ s` completing `s` as a
pair `⟨ord c, z⟩` — for `ctorVal c args` this is exactly `{args}`,
unioned back to `args`; junk `s` yields whatever survives. -/
def payloadOf (s : PS) : PS :=
  sUnion (sep (fun z => ∃ c, Equiv s (ordPair (ord c) z)) (sUnion s))

/-- `tagOf ⟨ord c, args⟩ ≈ ord c`. -/
theorem tagOf_ctorVal {c : Nat} {args : PS} :
    Equiv (tagOf (ctorVal c args)) (ord c) :=
  pfst_pair

/-- `payloadOf ⟨ord c, args⟩ ≈ args`. -/
theorem payloadOf_ctorVal {c : Nat} {args : PS} :
    Equiv (payloadOf (ctorVal c args)) args := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
    obtain ⟨⟨i, hi⟩, ht'⟩ := ht
    obtain ⟨c', hc'⟩ := hi
    obtain ⟨_, hw⟩ := ordPair_equiv hc'
    exact mem_congr_right (ht'.symm.trans hw.symm) hz'
  · intro hz
    -- args ∈ ⋃(ctorVal c args): args ∈ {ord c, args} ∈ s
    have hargs : args ∈ sUnion (ctorVal c args) :=
      mem_sUnion.mpr ⟨pair (ord c) args,
        mem_pair.mpr (Or.inr Equiv.rfl), mem_pair.mpr (Or.inr Equiv.rfl)⟩
    obtain ⟨i, hi⟩ := hargs
    have hQ : ∃ c', Equiv (ctorVal c args)
        (ordPair (ord c') ((sUnion (ctorVal c args)).Func i)) :=
      ⟨c, (ordPair_congr Equiv.rfl hi).symm⟩
    exact mem_sUnion.mpr ⟨(sUnion (ctorVal c args)).Func i,
      ⟨⟨i, hQ⟩, Equiv.refl _⟩, mem_congr_right hi.symm hz⟩

/-- Members of `payloadOf s` sit `TransGen elemOf`-below `s`:
`a ∈ t`, `t ∈ u`, `u ∈ s`. -/
theorem payload_tc {s : PS} {a : PS} (h : a ∈ payloadOf s) :
    Relation.TransGen elemOf a s := by
  obtain ⟨t, ht, ha⟩ := mem_sUnion.mp h
  obtain ⟨u, hu, ht'⟩ := mem_sUnion.mp (mem_sep_subset ht)
  exact .tail (.tail (.single ha) ht') hu

/-- The recursor fold: at `s`, `step` sees the tag, the payload, and
`{fold a | a ∈ payloadOf s}` as a family. Junk `s` gets junk extracts —
no case analysis, no choice. -/
noncomputable def recFold (step : PS → PS → PS → PS) : PS → PS :=
  mem_wf.transGen.fix fun s ih =>
    step (tagOf s) (payloadOf s)
      (mk (payloadOf s).Idx fun i =>
        ih _ (payload_tc ⟨i, Equiv.refl _⟩))

/-- Unfolding equation for `recFold`. -/
theorem recFold_eq (step : PS → PS → PS → PS) (s : PS) :
    recFold step s =
      step (tagOf s) (payloadOf s)
        (mk (payloadOf s).Idx fun i => recFold step ((payloadOf s).Func i)) := by
  show mem_wf.transGen.fix _ s = _
  rw [WellFounded.fix_eq]
  rfl

/-! ### Level-flagged semantic equality (irr) -/

/-- `x ≈_u y`: at level `u = 0` (Prop) all elements are identified —
proof irrelevance; at `u ≥ 1` it is extensional `≈`. -/
def equivAt (u : Nat) (x y : PS) : Prop := u = 0 ∨ Equiv x y

theorem equivAt.refl (u : Nat) (x : PS) : equivAt u x x :=
  Or.inr (Equiv.refl x)

theorem equivAt.symm {u : Nat} {x y : PS} : equivAt u x y → equivAt u y x
  | Or.inl h => Or.inl h
  | Or.inr h => Or.inr h.symm

theorem equivAt.trans {u : Nat} {x y z : PS} :
    equivAt u x y → equivAt u y z → equivAt u x z
  | Or.inl h, _ => Or.inl h
  | Or.inr _, Or.inl h => Or.inl h
  | Or.inr h, Or.inr e => Or.inr (h.trans e)

/-- At `u ≥ 1` the flag never fires: `equivAt` is exactly `≈`. -/
theorem equivAt_succ {u : Nat} {x y : PS} :
    equivAt (u + 1) x y ↔ Equiv x y :=
  ⟨fun | Or.inl h => (Nat.succ_ne_zero _ h).elim | Or.inr h => h,
   Or.inr⟩

/-- Sort codes are distinct at distinct levels: the tooth of the model. -/
theorem sortCode_ne {u v : Nat} (h : u ≠ v) :
    ¬ Equiv (sortCode u) (sortCode v) :=
  ord_ne h

end PS
end Rcic.Model
