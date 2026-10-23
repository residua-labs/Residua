/-!
# AH-005 over presented histories: `H_G` removes external generation authority

`closure_claim = 0`.

Law: `docs/rcic/10_AUTHORITY_HANDOFF.md` §4 (row AH-005), read over the
generation history rather than over the store alone.

* A generation event is an Annex 26.9 `GenerationRunOccurrence`. Its statement is
  a 09 §15 `ExecutionStatement`, which carries `history_parent_ref`. `Run`
  keeps the four fields `H_G` reads: the occurrence ref, `history_parent_ref`,
  the generator (`wasm_binary_ref`) and the produced object (`outcome_ref`).
* The history is **derived** from the store, never read from a caller list:
  it is the walk from the genesis ref along `history_parent_ref`
  (11 §17: predecessor continuity and exact append), it covers every stored
  run (no orphan, no side branch), it repeats no ref, and the store is
  content-addressed (a ref names at most one run).
* The only presented history object is the 11 §17 accumulator
  `(genesis, terminal, count, ordered root)`. `H_G` requires it to equal the
  accumulator of the derived history. Its authenticity is SP-016 / SP-020
  (11 §21), not this row.
* `L` is 26.16: a content-derived seed set closed over the history's runs
  (a run whose generator is Lean-identified makes its output Lean-identified).
  `T` is 26.31's `T_active`.

The theorems below state: the derived history is unique for a store; an
accepted history has no external generator after the handoff; any accepted
history's terminal run is native, so external generation cannot be re-acquired
by an exact append; omitting an interior generation event from the store
leaves no derivable history; a store whose derived ordered ref list differs
from the bound one (including a trailing omission) is refused under the bound
accumulator; and, when the two stores are jointly content-addressed (a ref
names at most one run across both, as the scm digest ref gives), a store whose
derived history differs from the bound one in any event, in any of the four
fields, is refused. Without joint content addressing that last statement fails:
two stores with the same refs and a different produced object are both accepted
under one accumulator (`ex_same_refs_both_accepted`).
-/

namespace Rcic.AuthHGHistory

/-- A 26.9 generation-run occurrence, projected to the fields `H_G` reads. -/
structure Run where
  ref : String
  parent : String
  gen : String
  out : String
deriving DecidableEq

/-- Predecessor continuity and exact append, from a starting ref. -/
def ChainFrom : String → List Run → Prop
  | _, [] => True
  | p, r :: rs => r.parent = p ∧ ChainFrom r.ref rs

/-- No ref occurs twice. -/
def NoRepeat : List String → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ NoRepeat xs

/-- The store is content-addressed: a ref names at most one run. -/
def RefsUnique (S : List Run) : Prop :=
  ∀ r ∈ S, ∀ s ∈ S, r.ref = s.ref → r = s

/-- The history derived from the store `S` by the walk from genesis `g`. -/
structure DerivedHistory (S : List Run) (g : String) (runs : List Run) : Prop where
  chain : ChainFrom g runs
  sub : ∀ r ∈ runs, r ∈ S
  cover : ∀ r ∈ S, r ∈ runs
  noRepeat : NoRepeat (runs.map Run.ref)
  genesisFresh : g ∉ runs.map Run.ref
  uniq : RefsUnique S

/-- The 11 §17 authority-accumulator shape: genesis, terminal occurrence,
transition count and the ordered history root (the ordered ref image; its
digest is the content address of that image). -/
structure Acc where
  genesis : String
  terminal : String
  count : Nat
  root : List String
deriving DecidableEq

/-- The accumulator of a history. -/
def accOf (g : String) (runs : List Run) : Acc :=
  { genesis := g
    terminal := (runs.getLast?.map Run.ref).getD g
    count := runs.length
    root := runs.map Run.ref }

/-- 26.16 `L`: the content-derived seed `L2` closed over the history's runs. -/
inductive LeanId (L2 : String → Prop) (runs : List Run) : String → Prop
  | seed {x : String} : L2 x → LeanId L2 runs x
  | step {r : Run} : r ∈ runs → LeanId L2 runs r.gen → LeanId L2 runs r.out

/-- A native generation run: generator in `T_active`, not Lean-identified. -/
def Native (T L2 : String → Prop) (runs : List Run) (r : Run) : Prop :=
  T r.gen ∧ ¬ LeanId L2 runs r.gen

/-- The handoff split: the last external run produces `le`, the next run
produces `fn`, and every run from there on is native. -/
def Handoff (T L2 : String → Prop) (runs : List Run) (le fn : String) : Prop :=
  ∃ pre r s post, runs = pre ++ r :: s :: post ∧ r.out = le ∧
    ¬ Native T L2 runs r ∧ s.out = fn ∧ ∀ x ∈ s :: post, Native T L2 runs x

/-- `H_G` over the presented accumulator `a` and the store `S`. -/
def HG (T L2 : String → Prop) (S : List Run) (g le fn : String) (a : Acc) : Prop :=
  ∃ runs, DerivedHistory S g runs ∧ accOf g runs = a ∧ Handoff T L2 runs le fn

/-! ## Chain lemmas -/

theorem chainFrom_parent {p : String} :
    ∀ {l : List Run}, ChainFrom p l → ∀ {z : Run}, z ∈ l →
      z.parent = p ∨ ∃ w ∈ l, z.parent = w.ref
  | [], _, _, hz => by cases hz
  | r :: rs, h, z, hz => by
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact Or.inl h.1
    · rcases chainFrom_parent h.2 hz' with e | ⟨w, hw, e⟩
      · exact Or.inr ⟨r, List.mem_cons_self _ _, e⟩
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, e⟩

theorem mem_map_ref {l : List Run} {w : Run} (hw : w ∈ l) : w.ref ∈ l.map Run.ref :=
  List.mem_map_of_mem _ hw

/-- Two chains from the same start, both repeat-free, neither containing the
start ref, with the same members, are equal. -/
theorem chain_unique :
    ∀ (a : List Run) {p : String} {b : List Run},
      ChainFrom p a → ChainFrom p b →
      p ∉ a.map Run.ref → p ∉ b.map Run.ref →
      NoRepeat (a.map Run.ref) → NoRepeat (b.map Run.ref) →
      (∀ r, r ∈ a ↔ r ∈ b) → a = b
  | [], _, b, _, _, _, _, _, _, hm => by
    cases b with
    | nil => rfl
    | cons y b' => exact absurd ((hm y).mpr (List.mem_cons_self _ _)) (by simp)
  | x :: a', p, b, ha, hb, hpa, hpb, hna, hnb, hm => by
    cases b with
    | nil => exact absurd ((hm x).mp (List.mem_cons_self _ _)) (by simp)
    | cons y b' =>
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_self _ _)) with e | hx'
        · exact e
        · exfalso
          rcases chainFrom_parent hb.2 hx' with e | ⟨w, hw, e⟩
          · exact hpb (by rw [← ha.1, e]; exact List.mem_cons_self _ _)
          · exact hpb (by
              rw [← ha.1, e]
              exact List.mem_cons_of_mem _ (mem_map_ref hw))
      subst hxy
      have hxa : x.ref ∉ a'.map Run.ref := hna.1
      have hxb : x.ref ∉ b'.map Run.ref := hnb.1
      have tail : a' = b' := by
        refine chain_unique a' ha.2 hb.2 hxa hxb hna.2 hnb.2 ?_
        intro r
        constructor
        · intro hr
          rcases List.mem_cons.mp ((hm r).mp (List.mem_cons_of_mem _ hr)) with e | h
          · subst e; exact absurd (mem_map_ref hr) hxa
          · exact h
        · intro hr
          rcases List.mem_cons.mp ((hm r).mpr (List.mem_cons_of_mem _ hr)) with e | h
          · subst e; exact absurd (mem_map_ref hr) hxb
          · exact h
      rw [tail]

/-- The derived history is a function of the store and the genesis ref. -/
theorem derivedHistory_unique {S : List Run} {g : String} {a b : List Run}
    (ha : DerivedHistory S g a) (hb : DerivedHistory S g b) : a = b :=
  chain_unique a ha.chain hb.chain ha.genesisFresh hb.genesisFresh
    ha.noRepeat hb.noRepeat
    (fun r => ⟨fun h => hb.cover r (ha.sub r h), fun h => ha.cover r (hb.sub r h)⟩)

/-! ## The handoff -/

/-- AH-005, history form: an accepted `H_G` splits its derived history at the
handoff. The last external run produces `le`, the first native run produces
`fn`, and no run from the handoff on has an external or Lean-identified
generator. -/
theorem hg_no_external_after_handoff {T L2 : String → Prop} {S : List Run}
    {g le fn : String} {a : Acc} (h : HG T L2 S g le fn a)
    {runs : List Run} (hd : DerivedHistory S g runs) :
    accOf g runs = a ∧
    ∃ pre r s post, runs = pre ++ r :: s :: post ∧ r.out = le ∧
      ¬ Native T L2 runs r ∧ s.out = fn ∧
      ∀ x ∈ s :: post, T x.gen ∧ ¬ LeanId L2 runs x.gen := by
  rcases h with ⟨runs', hd', hacc, pre, r, s, post, hsplit, hle, hext, hfn, hnat⟩
  have e : runs' = runs := derivedHistory_unique hd' hd
  subst e
  exact ⟨hacc, pre, r, s, post, hsplit, hle, hext, hfn, hnat⟩

/-- Every non-native run of an accepted history lies at or before the last
external run: external generation occurs only before the handoff. -/
theorem hg_external_before_handoff {T L2 : String → Prop} {S : List Run}
    {g le fn : String} {a : Acc} (h : HG T L2 S g le fn a)
    {runs : List Run} (hd : DerivedHistory S g runs) :
    ∃ pre r s post, runs = pre ++ r :: s :: post ∧ r.out = le ∧ s.out = fn ∧
      ∀ x ∈ runs, ¬ Native T L2 runs x → x ∈ pre ++ [r] := by
  rcases h with ⟨runs', hd', _, pre, r, s, post, hsplit, hle, _, hfn, hnat⟩
  have e : runs' = runs := derivedHistory_unique hd' hd
  subst e
  refine ⟨pre, r, s, post, hsplit, hle, hfn, ?_⟩
  intro x hx hxn
  rw [hsplit] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · rcases List.mem_cons.mp hx with e | hx
    · subst e; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact absurd (hnat x hx) hxn

/-- No output of a Lean-identified generator generates anything after the
handoff: a Lean-descended generator is still external authority. -/
theorem hg_no_lean_descendant_after_handoff {T L2 : String → Prop}
    {S : List Run} {g le fn : String} {a : Acc} (h : HG T L2 S g le fn a)
    {runs : List Run} (hd : DerivedHistory S g runs) :
    ∃ pre r s post, runs = pre ++ r :: s :: post ∧
      ∀ y ∈ runs, LeanId L2 runs y.gen → ∀ x ∈ s :: post, x.gen ≠ y.out := by
  rcases hg_no_external_after_handoff h hd with ⟨_, pre, r, s, post, hsplit, _, _, _, hnat⟩
  refine ⟨pre, r, s, post, hsplit, ?_⟩
  intro y hy hly x hx e
  exact (hnat x hx).2 (e ▸ LeanId.step hy hly)

theorem getLast_mem_split {pre post : List Run} {r s t : Run}
    (ht : (pre ++ r :: s :: post).getLast? = some t) : t ∈ s :: post := by
  have h1 : (pre ++ r :: s :: post).getLast? = (s :: post).getLast? := by
    rw [List.getLast?_append]
    cases hp : (r :: s :: post).getLast? with
    | none => simp at hp
    | some v =>
      have : (r :: s :: post).getLast? = (s :: post).getLast? := by
        simp [List.getLast?_cons]
      rw [← this, hp]; rfl
  rw [h1] at ht
  exact List.mem_of_getLast?_eq_some ht

/-- The terminal run of an accepted history is native. Every accumulator step
appends exactly one run (11 §17), so each accepted step past the handoff
appends a native run: external generation authority cannot be re-acquired. -/
theorem hg_terminal_native {T L2 : String → Prop} {S : List Run}
    {g le fn : String} {a : Acc} (h : HG T L2 S g le fn a)
    {runs : List Run} (hd : DerivedHistory S g runs)
    {t : Run} (ht : runs.getLast? = some t) : Native T L2 runs t := by
  rcases hg_no_external_after_handoff h hd with ⟨_, pre, r, s, post, hsplit, _, _, _, hnat⟩
  rw [hsplit] at ht
  exact hnat t (getLast_mem_split ht)

/-- An exact append of an external run is refused: no accumulator that
extends an accepted history by an external run is accepted. -/
theorem hg_append_external_refused {T L2 : String → Prop} {S : List Run}
    {g le fn : String} {runs : List Run} {e : Run}
    (hd : DerivedHistory S g (runs ++ [e])) (hx : ¬ Native T L2 (runs ++ [e]) e)
    (a : Acc) : ¬ HG T L2 S g le fn a := by
  intro h
  exact hx (hg_terminal_native h hd (by simp))

/-! ## Omission -/

/-- Omitting an interior generation event from the store leaves no derivable
history: its successor is an orphan. No accumulator is accepted on the
smaller store. -/
theorem omit_interior_underivable {S S' : List Run} {g : String}
    {pre post : List Run} {r c : Run}
    (hd : DerivedHistory S g (pre ++ r :: c :: post))
    (hsub : ∀ x ∈ S', x ∈ S) (hc : c ∈ S') (hr : r ∉ S') :
    ¬ ∃ runs', DerivedHistory S' g runs' := by
  rintro ⟨runs', hd'⟩
  have hch : ChainFrom r.ref (c :: post) := by
    have : ∀ (q : List Run) {p : String}, ChainFrom p (q ++ r :: c :: post) →
        ChainFrom r.ref (c :: post) := by
      intro q
      induction q with
      | nil => intro p h; exact h.2
      | cons y q ih => intro p h; exact ih h.2
    exact this pre hd.chain
  have hcp : c.parent = r.ref := hch.1
  have hrS : r ∈ S := hd.sub r (by simp)
  rcases chainFrom_parent hd'.chain (hd'.cover c hc) with e | ⟨w, hw, e⟩
  · exact hd.genesisFresh (by
      rw [← e, hcp]; exact mem_map_ref (show r ∈ pre ++ r :: c :: post by simp))
  · have hwS : w ∈ S := hsub w (hd'.sub w hw)
    have : w = r := hd.uniq w hwS r hrS (by rw [← e, hcp])
    exact hr (this ▸ hd'.sub w hw)

/-- Under one bound accumulator, a store whose derived ordered ref list differs
from the bound history's (an omitted trailing event, an added side event, a
successor under a new ref) is refused. The verdict is bound to the history root,
not to the store. -/
theorem hg_root_binds_ref_list {T L2 : String → Prop} {S S' : List Run}
    {g le fn le' fn' : String} {a : Acc} {h h' : List Run}
    (hd : DerivedHistory S g h) (hd' : DerivedHistory S' g h')
    (hne : h.map Run.ref ≠ h'.map Run.ref)
    (hacc : HG T L2 S g le fn a) : ¬ HG T L2 S' g le' fn' a := by
  rintro ⟨r2, hd2, hacc2, _⟩
  rcases hacc with ⟨r1, hd1, hacc1, _⟩
  have e1 : r1 = h := derivedHistory_unique hd1 hd
  have e2 : r2 = h' := derivedHistory_unique hd2 hd'
  subst e1; subst e2
  apply hne
  have := congrArg Acc.root (hacc1.trans hacc2.symm)
  simpa [accOf] using this

/-- Lists whose members are identified by ref are equal when their ref images are. -/
theorem map_ref_inj : ∀ {h h' : List Run},
    (∀ r ∈ h, ∀ s ∈ h', r.ref = s.ref → r = s) →
      h.map Run.ref = h'.map Run.ref → h = h'
  | [], [], _, _ => rfl
  | [], _ :: _, _, e => by simp at e
  | _ :: _, [], _, e => by simp at e
  | r :: rs, s :: ss, hu, e => by
    simp only [List.map_cons, List.cons.injEq] at e
    have h1 : r = s := hu r (List.mem_cons_self _ _) s (List.mem_cons_self _ _) e.1
    have h2 : rs = ss := map_ref_inj
      (fun x hx y hy => hu x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) e.2
    rw [h1, h2]

/-- Under one bound accumulator, when the two stores are jointly
content-addressed, a store whose derived history differs from the bound history
in any event (any of ref, parent, generator, produced object; an omitted,
re-minted, appended or side event) is refused. -/
theorem hg_root_binds_history {T L2 : String → Prop} {S S' : List Run}
    {g le fn le' fn' : String} {a : Acc} {h h' : List Run}
    (hd : DerivedHistory S g h) (hd' : DerivedHistory S' g h')
    (hq : RefsUnique (S ++ S'))
    (hne : h ≠ h')
    (hacc : HG T L2 S g le fn a) : ¬ HG T L2 S' g le' fn' a := by
  refine hg_root_binds_ref_list hd hd' (fun hr => hne (map_ref_inj ?_ hr)) hacc
  intro r hr s hs e
  exact hq r (List.mem_append_left _ (hd.sub r hr)) s (List.mem_append_right _ (hd'.sub s hs)) e

/-- A string produced by no run and outside the seed is not Lean-identified. -/
theorem leanId_not_of_outs {L2 : String → Prop} {runs : List Run} {x : String}
    (hs : ¬ L2 x) (ho : ∀ r ∈ runs, r.out ≠ x) : ¬ LeanId L2 runs x := by
  intro hx
  cases hx with
  | seed h => exact hs h
  | step hr _ => exact ho _ hr rfl

/-! ## Non-vacuity: an inhabited instance -/

/-- External run: Lean generates the last external artifact. -/
def exRun0 : Run := { ref := "r0", parent := "g", gen := "lean", out := "le" }
/-- First native run: the active toolchain generates the first native artifact. -/
def exRun1 : Run := { ref := "r1", parent := "r0", gen := "t", out := "fn" }
/-- A later native run. -/
def exRun2 : Run := { ref := "r2", parent := "r1", gen := "t", out := "b" }

def exT (x : String) : Prop := x = "t"
def exL2 (x : String) : Prop := x = "lean"

def exRuns : List Run := [exRun0, exRun1, exRun2]

theorem ex_leanId_ne_t : ∀ {x : String}, LeanId exL2 exRuns x → x ≠ "t" := by
  intro x hx
  cases hx with
  | seed h => rw [h]; decide
  | step hr _ =>
    simp only [exRuns, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide

theorem ex_native_t (r : Run) (hg : r.gen = "t") : Native exT exL2 exRuns r :=
  ⟨hg, fun h => ex_leanId_ne_t h hg⟩

theorem ex_derived : DerivedHistory exRuns "g" exRuns where
  chain := by simp [ChainFrom, exRuns, exRun0, exRun1, exRun2]
  sub := fun _ h => h
  cover := fun _ h => h
  noRepeat := by simp (config := { decide := true }) [NoRepeat, exRuns, exRun0, exRun1, exRun2]
  genesisFresh := by simp (config := { decide := true }) [exRuns, exRun0, exRun1, exRun2]
  uniq := by
    intro r hr s hs e
    simp only [exRuns, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr hs
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
      first | rfl | (simp [exRun0, exRun1, exRun2] at e)

/-- The instance is accepted under its own accumulator. -/
theorem ex_hg : HG exT exL2 exRuns "g" "le" "fn" (accOf "g" exRuns) := by
  refine ⟨exRuns, ex_derived, rfl, [], exRun0, exRun1, [exRun2], rfl, rfl, ?_, rfl, ?_⟩
  · intro h; exact absurd h.1 (by simp [exT, exRun0])
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ex_native_t _ rfl
    · exact ex_native_t _ rfl

/-- Omitting the interior run `exRun1` from the store leaves no history. -/
theorem ex_omit_interior :
    ¬ ∃ runs', DerivedHistory [exRun0, exRun2] "g" runs' :=
  omit_interior_underivable (pre := [exRun0]) (post := []) ex_derived
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      simp only [exRuns, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      rcases hx with rfl | rfl <;> simp)
    (by simp)
    (by simp [exRun0, exRun1, exRun2])

/-- The store without the trailing run still derives a history. -/
theorem ex_derived_short : DerivedHistory [exRun0, exRun1] "g" [exRun0, exRun1] where
  chain := by simp [ChainFrom, exRun0, exRun1]
  sub := fun _ h => h
  cover := fun _ h => h
  noRepeat := by simp (config := { decide := true }) [NoRepeat, exRun0, exRun1]
  genesisFresh := by simp (config := { decide := true }) [exRun0, exRun1]
  uniq := by
    intro r hr s hs e
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr hs
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
      first | rfl | (simp [exRun0, exRun1] at e)

/-- Omitting the trailing run is derivable but refused under the bound
accumulator of the full history. -/
theorem ex_omit_trailing_refused :
    ¬ HG exT exL2 [exRun0, exRun1] "g" "le" "fn" (accOf "g" exRuns) :=
  hg_root_binds_history ex_derived ex_derived_short
    (by
      intro r hr s hs e
      simp only [exRuns, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hr hs
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rcases hs with rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (simp [exRun0, exRun1, exRun2] at e))
    (by simp [exRuns, exRun0, exRun1, exRun2]) ex_hg

/-- The last run re-minted with a different produced object under the same ref. -/
def exRun2b : Run := { ref := "r2", parent := "r1", gen := "t", out := "b2" }

def exRunsB : List Run := [exRun0, exRun1, exRun2b]

/-- Joint content addressing is load-bearing: without it, two stores with the
same refs and a different produced object are both accepted under one
accumulator. -/
theorem ex_same_refs_both_accepted :
    HG exT exL2 exRuns "g" "le" "fn" (accOf "g" exRuns) ∧
      HG exT exL2 exRunsB "g" "le" "fn" (accOf "g" exRuns) ∧ exRuns ≠ exRunsB := by
  refine ⟨ex_hg, ?_, by simp [exRuns, exRunsB, exRun2, exRun2b]⟩
  have hd : DerivedHistory exRunsB "g" exRunsB :=
    { chain := by simp [ChainFrom, exRunsB, exRun0, exRun1, exRun2b]
      sub := fun _ h => h
      cover := fun _ h => h
      noRepeat := by
        simp (config := { decide := true }) [NoRepeat, exRunsB, exRun0, exRun1, exRun2b]
      genesisFresh := by simp (config := { decide := true }) [exRunsB, exRun0, exRun1, exRun2b]
      uniq := by
        intro r hr s hs e
        simp only [exRunsB, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hr hs
        rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
          first | rfl | (simp [exRun0, exRun1, exRun2b] at e) }
  have hn : ∀ r ∈ [exRun1, exRun2b], Native exT exL2 exRunsB r := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      refine ⟨rfl, leanId_not_of_outs (by simp [exL2, exRun1, exRun2b]) ?_⟩ <;>
      (intro q hq
       simp only [exRunsB, List.mem_cons, List.mem_singleton, List.not_mem_nil,
         or_false] at hq
       rcases hq with rfl | rfl | rfl <;> simp [exRun0, exRun1, exRun2b])
  refine ⟨exRunsB, hd, by simp [accOf, exRuns, exRunsB, exRun0, exRun1, exRun2, exRun2b],
    [], exRun0, exRun1, [exRun2b], rfl, rfl, ?_, rfl, hn⟩
  intro h; exact absurd h.1 (by simp [exT, exRun0])

end Rcic.AuthHGHistory
