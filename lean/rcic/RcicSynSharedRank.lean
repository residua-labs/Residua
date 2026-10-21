import rcic.RcicSynWorkOrder
import rcic.RcicSynSlotKind
import rcic.RcicSynAdm
import rcic.RcicSynRegStep

/-!
# Wall B §7–§9 — the occurrence ledger, the original-owner cut, the shared key

`research/rcic/sortrow/BELOWC_MIXED_STEP_AND_LEDGER.md` Part II. Nothing here
changes the landed `P2Query.rank` / `Before` (`RcicSynBelowCFix`); the new key
and its order are added alongside. `closure_claim` stays 0.

* **§7 original identity.** A frozen root forest `RootForest := List DNode`
  (public payload positions, receipt entry fields, selected admission
  occurrences — each a landed `DNode`); an occurrence `Occ` is a root tag plus
  a child path, read by `DNode.subAt` (the landed K1 occurrence receipt). Its
  weight is the weight of the node it names (`DNode.wt`, i.e. `TyP.wt`/`CvP.wt`,
  const nodes paying their admission weight); an occurrence off the forest
  weighs 0 and is never live.
* **§8.1 the original-owner cut (`frontier_cut`).** Replace a non-empty part
  `X` of live occurrences by any list `Y` of actual proper descendants (root
  equal, path strictly extended) and keep `Z`: the frontier weights make one
  `DMStep`. Every literal field is lighter than its parent
  (`TyP.dchildren_wt_lt` / `CvP.dchildren_wt_lt`, all 15 + 24 arms, from the
  landed weight equations), composed along the path (`DNode.subAt_wt_lt`).
  `antichain_cut`: the result is again a prefix antichain when `Y` is one and
  the old frontier was prefix-free and `X`, `Z` disjoint.
* **§8.1 admission credit.** `admission_credit_type` / `admission_credit_def`:
  selecting the stored type / body admission of a `const` / `δ` occurrence is
  one `DMStep` paid by `TypeAdm.lt` / `DefAdm.lt`. `no_defAdm_zero` /
  `no_typeAdm_zero`: at `Aw ≡ 0` no admission can be selected at all — the
  §9 calibration is a solver calibration of the weight, not a public premise.
* **§8.3 the key.** `SharedKey := (original suffix length, frontier weights,
  pending source-work multiset)`, ordered by `SharedLT := Prod.Lex (<)
  (Prod.Lex DMStep WorkStep)`; `sharedLT_wf` by two `Prod.lexAccessible`s over
  `Nat.lt`, `dmStep_wf` and `workStep_wf`. `BeforeSharedL L` is the order
  pulled back along any ledger `L : Q → SharedKey`; it is well-founded and
  irreflexive for every ledger (so a self-edge is never strict, whatever the
  ledger — §9.5).
* **§9 controls** as kernel fixtures on the explicit keys of the document:
  double materialization `[7,11,1] → [1,11,1,1,11,1]` rejected,
  `→ [1,1,11,1]` accepted; bridge endpoint `[2,7,2] → [1,7,5,2]` rejected,
  focused `[1,5,2]` accepted; pure focus with the bvar cut `[1,2,1] → [1,1,1]`;
  admission calibration `[12] → [5]` strict and `([5],5)` flat.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 weights of forest nodes; every literal field is lighter than its parent -/

/-- The weight of a forest node: the landed `TyP.wt` / `CvP.wt` (a `const` node
    pays its admission weight `Aw r`). -/
def DNode.wt (Aw : Nat → Nat) : DNode → Nat
  | .ty D => D.wt Aw
  | .cv c => c.wt Aw

theorem DNode.wt_pos (Aw : Nat → Nat) : ∀ d : DNode, 0 < d.wt Aw
  | .ty D => TyP.wt_pos Aw D
  | .cv c => CvP.wt_pos Aw c

/-- Every derivation field of a typing node is strictly lighter than the node
    (all 15 arms; `parent = 1 + Σ fields (+ Aw r)`). -/
theorem TyP.dchildren_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) : ∀ c ∈ D.dchildren, c.wt Aw < D.wt Aw := by
  cases D <;> simp only [TyP.dchildren, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, false_implies, implies_true, DNode.wt, TyP.wt, CvP.wt] <;>
    (repeat' apply And.intro) <;> omega

/-- Every derivation field of a conversion node is strictly lighter than the node
    (all 24 arms). -/
theorem CvP.dchildren_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) : ∀ c ∈ h.dchildren, c.wt Aw < h.wt Aw := by
  cases h <;> simp only [CvP.dchildren, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, false_implies, implies_true, DNode.wt, TyP.wt, CvP.wt] <;>
    (repeat' apply And.intro) <;> omega

theorem DNode.children_wt_lt (Aw : Nat → Nat) :
    ∀ (d c : DNode), c ∈ d.children → c.wt Aw < d.wt Aw
  | .ty D, c, hc => TyP.dchildren_wt_lt Aw D c hc
  | .cv h, c, hc => CvP.dchildren_wt_lt Aw h c hc

/-- Along any child path the weight does not increase. -/
theorem DNode.subAt_wt_le (Aw : Nat → Nat) : ∀ (p : List Nat) (d d' : DNode),
    d.subAt p = some d' → d'.wt Aw ≤ d.wt Aw
  | [], d, d', h => by
      simp only [DNode.subAt, Option.some.injEq] at h
      subst h; exact Nat.le_refl _
  | i :: p, d, d', h => by
      simp only [DNode.subAt] at h
      obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some.mp h
      have h1 := DNode.children_wt_lt Aw d c (List.getElem?_mem hc)
      have h2 := DNode.subAt_wt_le Aw p c d' hc'
      omega

/-- Along a non-empty child path the weight strictly decreases: the composition
    of `DNode.children_wt_lt` along the path. -/
theorem DNode.subAt_wt_lt (Aw : Nat → Nat) : ∀ (p : List Nat), p ≠ [] → ∀ (d d' : DNode),
    d.subAt p = some d' → d'.wt Aw < d.wt Aw
  | [], hp, _, _, _ => absurd rfl hp
  | i :: p, _, d, d', h => by
      simp only [DNode.subAt] at h
      obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some.mp h
      have h1 := DNode.children_wt_lt Aw d c (List.getElem?_mem hc)
      have h2 := DNode.subAt_wt_le Aw p c d' hc'
      omega

/-- Paths compose. -/
theorem DNode.subAt_append : ∀ (p q : List Nat) (d : DNode),
    d.subAt (p ++ q) = (d.subAt p).bind (·.subAt q)
  | [], _, _ => rfl
  | i :: p, q, d => by
      simp only [List.cons_append, DNode.subAt]
      generalize d.children[i]? = o
      cases o with
      | none => rfl
      | some c => exact DNode.subAt_append p q c

/-! ## §2 original occurrences: root tag + child path -/

/-- An original occurrence: a root tag (a position in the frozen root forest)
    and a child path. Separately supplied fields are different occurrences
    even when definitionally equal; roles selecting the same path share one. -/
structure Occ where
  root : Nat
  path : List Nat
  deriving DecidableEq, Repr

/-- The frozen root forest: public payload positions, receipt entry type/value
    fields, selected admission occurrences — one `DNode` per root. -/
abbrev RootForest := List DNode

/-- The node an occurrence names (`none` off the forest). -/
def Occ.node (F : RootForest) (o : Occ) : Option DNode :=
  (F[o.root]?).bind (·.subAt o.path)

/-- The weight of an occurrence: the weight of the node it names; `0` off the
    forest (such an occurrence is never live). -/
def Occ.wt (Aw : Nat → Nat) (F : RootForest) (o : Occ) : Nat :=
  ((o.node F).map (DNode.wt Aw)).getD 0

theorem Occ.wt_of_node {Aw : Nat → Nat} {F : RootForest} {o : Occ} {d : DNode}
    (h : o.node F = some d) : o.wt Aw F = d.wt Aw := by
  simp [Occ.wt, h]

theorem Occ.wt_of_none {Aw : Nat → Nat} {F : RootForest} {o : Occ}
    (h : o.node F = none) : o.wt Aw F = 0 := by
  simp [Occ.wt, h]

/-- `x` covers `y`: same root, `x.path` a prefix of `y.path` (a node covers its subtree). -/
def Occ.Covers (x y : Occ) : Prop := x.root = y.root ∧ ∃ p, y.path = x.path ++ p

/-- `y` is an actual proper descendant of `x`: same root, `x.path` a strict prefix. -/
def Occ.ProperDesc (y x : Occ) : Prop := y.root = x.root ∧ ∃ p, p ≠ [] ∧ y.path = x.path ++ p

/-- A frontier is a prefix antichain: two comparable members are equal. -/
def Antichain (X : List Occ) : Prop := ∀ x ∈ X, ∀ y ∈ X, x.Covers y → x = y

theorem Occ.covers_of_properDesc {y x : Occ} (h : y.ProperDesc x) : x.Covers y :=
  ⟨h.1.symm, h.2.elim fun p hp => ⟨p, hp.2⟩⟩

theorem Occ.covers_trans {a b c : Occ} (h1 : a.Covers b) (h2 : b.Covers c) : a.Covers c := by
  obtain ⟨hr1, p, hp⟩ := h1
  obtain ⟨hr2, q, hq⟩ := h2
  exact ⟨hr1.trans hr2, p ++ q, by rw [hq, hp, List.append_assoc]⟩

/-- A proper descendant never covers its ancestor (path lengths). -/
theorem Occ.not_covers_of_properDesc {y x : Occ} (h : y.ProperDesc x) : ¬ y.Covers x := by
  rintro ⟨_, q, hq⟩
  obtain ⟨_, p, hp, hpath⟩ := h
  have h1 := congrArg List.length hq
  have h2 := congrArg List.length hpath
  simp only [List.length_append] at h1 h2
  have hp0 : p.length = 0 := by omega
  exact hp (List.length_eq_zero.mp hp0)

/-- Two occurrences covering one occurrence are comparable. -/
theorem Occ.covers_comparable {a x b : Occ} (h1 : a.Covers b) (h2 : x.Covers b) :
    a.Covers x ∨ x.Covers a := by
  obtain ⟨hr1, p, hp⟩ := h1
  obtain ⟨hr2, q, hq⟩ := h2
  have hroot : a.root = x.root := hr1.trans hr2.symm
  rcases List.prefix_or_prefix_of_prefix (⟨p, hp.symm⟩ : a.path <+: b.path)
      (⟨q, hq.symm⟩ : x.path <+: b.path) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨hroot, t, ht.symm⟩
  · exact Or.inr ⟨hroot.symm, t, ht.symm⟩

/-- The node of a proper descendant is read below the ancestor's node along the
    extra path. -/
theorem Occ.node_of_properDesc {F : RootForest} {x y : Occ} (h : y.ProperDesc x) {dx : DNode}
    (hx : x.node F = some dx) : ∃ p, p ≠ [] ∧ y.node F = dx.subAt p := by
  obtain ⟨hr, p, hp, hpath⟩ := h
  have hx' : (F[x.root]?).bind (fun d => d.subAt x.path) = some dx := hx
  obtain ⟨r, hF, hsub⟩ := Option.bind_eq_some.mp hx'
  have hsub' : r.subAt x.path = some dx := hsub
  refine ⟨p, hp, ?_⟩
  show (F[y.root]?).bind (fun d => d.subAt y.path) = dx.subAt p
  rw [hr, hpath, hF, Option.some_bind, DNode.subAt_append, hsub', Option.some_bind]

/-- **Every proper descendant of a live occurrence is strictly lighter.** -/
theorem Occ.wt_lt_of_properDesc (Aw : Nat → Nat) {F : RootForest} {x y : Occ}
    (h : y.ProperDesc x) {dx : DNode} (hx : x.node F = some dx) : y.wt Aw F < x.wt Aw F := by
  obtain ⟨p, hp, hy⟩ := Occ.node_of_properDesc h hx
  rw [Occ.wt_of_node hx]
  cases hdy : dx.subAt p with
  | none => rw [Occ.wt_of_none (hy.trans hdy)]; exact DNode.wt_pos Aw dx
  | some dy => rw [Occ.wt_of_node (hy.trans hdy)]; exact DNode.subAt_wt_lt Aw p hp dx dy hdy

/-! ## §3 the original-owner cut -/

/-- The frontier weights `w[X]`. -/
def frontierW (Aw : Nat → Nat) (F : RootForest) (X : List Occ) : List Nat :=
  X.map (Occ.wt Aw F)

theorem frontierW_append (Aw : Nat → Nat) (F : RootForest) (X Z : List Occ) :
    frontierW Aw F (X ++ Z) = frontierW Aw F X ++ frontierW Aw F Z := by
  simp [frontierW, List.map_append]

/-- **§8.1 the original-owner cut.** Old frontier `X ⊎ Z` with `X ≠ ∅` live;
    replace `X` by any finite list `Y` of actual proper descendants of members of
    `X`: `w[Y] ⊎ w[Z] <DM w[X] ⊎ w[Z]` — every literal field is lighter than its
    parent, composed along the path. Copies in `Y` are allowed (a shared packet
    may be used twice without a second primary occurrence). -/
theorem frontier_cut (Aw : Nat → Nat) (F : RootForest) {X Y Z : List Occ} (hX : X ≠ [])
    (hlive : ∀ x ∈ X, ∃ d, x.node F = some d)
    (hY : ∀ y ∈ Y, ∃ x ∈ X, y.ProperDesc x) :
    DMStep (frontierW Aw F (Y ++ Z)) (frontierW Aw F (X ++ Z)) := by
  rw [frontierW_append, frontierW_append]
  refine ⟨frontierW Aw F X, frontierW Aw F Y, frontierW Aw F Z, ?_, List.Perm.refl _,
    List.Perm.refl _, ?_⟩
  · intro h
    have h' : X.map (Occ.wt Aw F) = [] := h
    exact hX (List.map_eq_nil_iff.mp h')
  · intro w hw
    have hw' : w ∈ Y.map (Occ.wt Aw F) := hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨x, hx, hdesc⟩ := hY y hy
    obtain ⟨dx, hdx⟩ := hlive x hx
    exact ⟨x.wt Aw F, List.mem_map.mpr ⟨x, hx, rfl⟩, Occ.wt_lt_of_properDesc Aw hdesc hdx⟩

/-- The cut keeps the frontier a prefix antichain: `Y` an antichain of proper
    descendants of `X`, the old frontier prefix-free with `X` and `Z` disjoint. -/
theorem antichain_cut {X Y Z : List Occ} (hXZ : Antichain (X ++ Z))
    (hdisj : ∀ x ∈ X, x ∉ Z) (hYa : Antichain Y)
    (hY : ∀ y ∈ Y, ∃ x ∈ X, y.ProperDesc x) : Antichain (Y ++ Z) := by
  intro a ha b hb hab
  rcases List.mem_append.mp ha with haY | haZ <;> rcases List.mem_append.mp hb with hbY | hbZ
  · exact hYa a haY b hbY hab
  · obtain ⟨x, hx, hxa⟩ := hY a haY
    have hxb : x.Covers b := Occ.covers_trans (Occ.covers_of_properDesc hxa) hab
    have hxb' : x = b := hXZ x (List.mem_append_left Z hx) b (List.mem_append_right X hbZ) hxb
    have hab' : a.Covers x := by rw [hxb']; exact hab
    exact absurd hab' (Occ.not_covers_of_properDesc hxa)
  · obtain ⟨x, hx, hxb⟩ := hY b hbY
    rcases Occ.covers_comparable hab (Occ.covers_of_properDesc hxb) with hax | hxa
    · have hax' : a = x := hXZ a (List.mem_append_right X haZ) x (List.mem_append_left Z hx) hax
      have hxZ : x ∈ Z := by rw [← hax']; exact haZ
      exact absurd hxZ (hdisj x hx)
    · have hxa' : x = a := hXZ x (List.mem_append_left Z hx) a (List.mem_append_right X haZ) hxa
      have hxZ : x ∈ Z := by rw [hxa']; exact haZ
      exact absurd hxZ (hdisj x hx)
  · exact hXZ a (List.mem_append_right X haZ) b (List.mem_append_right X hbZ) hab

/-! ## §4 admission credit: the selected admission is paid by `TypeAdm.lt` / `DefAdm.lt` -/

/-- Selecting the stored-type admission of a `const` occurrence: the admission
    derivation's atoms replace the const atom in one `DMStep`
    (`a.hT.wt < Aw r < 1 + hT.wt + Aw r`). -/
theorem admission_credit_type (Aw : Nat → Nat) {E E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u))
    (a : TypeAdm E' Aw r m) (Z : List Nat) :
    DMStep (a.hT.atoms Aw ++ Z)
      ((TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).wt Aw :: Z) :=
  dmStep_of_below fun y hy => by
    have h1 := TyP.atoms_le Aw a.hT y hy
    have h2 := a.lt
    simp only [TyP.wt]; omega

/-- Selecting the body admission at a `δ` occurrence: the admission derivation's
    atoms replace the δ atom in one `DMStep` (`a.hv.wt < Aw r < dl.wt < δ.wt`). -/
theorem admission_credit_def (Aw : Nat → Nat) {E E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (a : DefAdm E' Aw r m b) (Z : List Nat) :
    DMStep (a.hv.atoms Aw ++ Z)
      ((CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw :: Z) :=
  dmStep_of_below fun y hy => by
    have h1 := TyP.atoms_le Aw a.hv y hy
    have h2 := a.lt
    have h3 := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
    simp only [CvP.wt]; omega

/-- **§9 calibration.** At `Aw ≡ 0` no body admission exists: the credit edge is
    empty, so the descent must use the calibrated admission weight. -/
theorem no_defAdm_zero {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (a : DefAdm E (fun _ => 0) r m b) : False :=
  Nat.not_lt_zero _ a.lt

theorem no_typeAdm_zero {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : TypeAdm E (fun _ => 0) r m) : False :=
  Nat.not_lt_zero _ a.lt

/-! ## §5 the shared key and its order -/

/-- The shared key: `(original suffix length, shared frontier weights, pending
    source-work multiset)`. -/
abbrev SharedKey := Nat × (List Nat × List SourceKey)

/-- Inside one frame: a frontier `DMStep` first, else a `WorkStep` at an
    unchanged frontier. -/
abbrev InnerLT : List Nat × List SourceKey → List Nat × List SourceKey → Prop :=
  Prod.Lex DMStep WorkStep

/-- The full order: strict suffix step, then `InnerLT`. -/
abbrev SharedLT : SharedKey → SharedKey → Prop :=
  Prod.Lex (fun p' p : Nat => p' < p) InnerLT

theorem innerLT_wf : WellFounded InnerLT :=
  ⟨fun ⟨M, J⟩ => Prod.lexAccessible (dmStep_wf.apply M) (fun J => workStep_wf.apply J) J⟩

/-- `SharedLT` is well-founded: two `Prod.lexAccessible`s over `Nat.lt`,
    `dmStep_wf` and `workStep_wf`. -/
theorem sharedLT_wf : WellFounded SharedLT :=
  ⟨fun ⟨p, B⟩ => Prod.lexAccessible (Nat.lt_wfRel.wf.apply p) (fun b => innerLT_wf.apply b) B⟩

theorem sharedLT_irrefl (k : SharedKey) : ¬ SharedLT k k :=
  accR_irrefl (sharedLT_wf.apply k)

/-- `BeforeShared` relative to a ledger `L` assigning each query its shared key. -/
def BeforeSharedL {Q : Type} (L : Q → SharedKey) (q' q : Q) : Prop :=
  SharedLT (L q') (L q)

theorem beforeSharedL_wf {Q : Type} (L : Q → SharedKey) : WellFounded (BeforeSharedL L) :=
  InvImage.wf L sharedLT_wf

/-- **§9.5.** Under every ledger a self-edge is never strict: strictness is a
    property of the concrete worker port, not of `Issues` membership. -/
theorem beforeSharedL_irrefl {Q : Type} (L : Q → SharedKey) (q : Q) : ¬ BeforeSharedL L q q :=
  accR_irrefl ((beforeSharedL_wf L).apply q)

/-- Same frame, frontier step. -/
theorem sharedLT_of_frontier {p : Nat} {M' M : List Nat} {J' J : List SourceKey}
    (h : DMStep M' M) : SharedLT (p, (M', J')) (p, (M, J)) :=
  Prod.Lex.right _ (Prod.Lex.left _ _ h)

/-- Same frame, same frontier, work step. -/
theorem sharedLT_of_work {p : Nat} {M : List Nat} {J' J : List SourceKey}
    (h : WorkStep J' J) : SharedLT (p, (M, J')) (p, (M, J)) :=
  Prod.Lex.right _ (Prod.Lex.right _ h)

/-- Strictly shorter original suffix. -/
theorem sharedLT_of_suffix {p' p : Nat} {B' B : List Nat × List SourceKey} (h : p' < p) :
    SharedLT (p', B') (p, B) :=
  Prod.Lex.left _ _ h

/-! ## §6 the §9 controls, as kernel fixtures on the document's explicit keys -/

/-- **§9 double materialization, rejected.** `at(P) = [7, 11, 1]`; materializing
    two transported `H` proofs gives `[1, 11, 1, 1, 11, 1]`, which is not
    `DM`-below: the second `11` has no owner above it (the only `11` of `P` is
    not strictly above `11`). -/
theorem pin_double_materialization_rejected : ¬ DMStep [1, 11, 1, 1, 11, 1] [7, 11, 1] := by
  rintro ⟨X, Y, Z, _, hM, hM', hdom⟩
  have h1 : List.count 11 (X ++ Z) = 1 := by rw [← hM.count_eq]; decide
  have h2 : List.count 11 (Y ++ Z) = 2 := by rw [← hM'.count_eq]; decide
  rw [List.count_append] at h1 h2
  have h11 : 11 ∈ Y := List.count_pos_iff.mp (by omega)
  obtain ⟨x, hx, hlt⟩ := hdom 11 h11
  have hxM : x ∈ [7, 11, 1] := hM.symm.mem_iff.mp (List.mem_append_left Z hx)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxM
  omega

/-- **§9 double materialization, the correct child support.** `[1, 1, 11, 1]`:
    `X = [7]`, `Y = [1, 1]` (the two endpoint `H` fields), `Z = [11, 1]` shared. -/
theorem pin_double_materialization_accepted : DMStep [1, 1, 11, 1] [7, 11, 1] :=
  ⟨[7], [1, 1], [11, 1], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨7, List.mem_cons_self _ _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega⟩⟩

/-- **§9 bridge endpoint, rejected.** Frontier `[2, 7, 2]` (middle a cctx bridge
    whose left endpoint weighs 5): keeping the bridge and adding its endpoint,
    `[1, 7, 5, 2]`, is not a `DM` step — `7` must be retained (nothing in
    `[2, 7, 2]` is above it, so it cannot be re-added), hence the removed part is
    inside `[2, 2]`, and `5` is paid by nothing. -/
theorem pin_bridge_endpoint_rejected : ¬ DMStep [1, 7, 5, 2] [2, 7, 2] := by
  rintro ⟨X, Y, Z, _, hM, hM', hdom⟩
  have hXsub : ∀ x ∈ X, x ∈ [2, 7, 2] :=
    fun x hx => hM.symm.mem_iff.mp (List.mem_append_left Z hx)
  have hYle : ∀ y ∈ Y, y ≤ 6 := by
    intro y hy
    obtain ⟨x, hx, hlt⟩ := hdom y hy
    have := hXsub x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have h7 : 7 ∈ Y ++ Z := hM'.mem_iff.mp (by decide)
  have h7Z : 7 ∈ Z := by
    rcases List.mem_append.mp h7 with h | h
    · have := hYle 7 h; omega
    · exact h
  have hc : List.count 7 (X ++ Z) = 1 := by rw [← hM.count_eq]; decide
  rw [List.count_append] at hc
  have hZpos : 0 < List.count 7 Z := List.count_pos_iff.mpr h7Z
  have hX7 : 7 ∉ X := List.count_eq_zero.mp (by omega)
  have hYle1 : ∀ y ∈ Y, y ≤ 1 := by
    intro y hy
    obtain ⟨x, hx, hlt⟩ := hdom y hy
    have hx' := hXsub x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · omega
    · exact absurd hx hX7
    · omega
  have h5 : 5 ∈ Y ++ Z := hM'.mem_iff.mp (by decide)
  rcases List.mem_append.mp h5 with h | h
  · have := hYle1 5 h; omega
  · have := hM.symm.mem_iff.mp (List.mem_append_right X h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega

/-- **§9 bridge endpoint, focused.** `[2, 7, 2] → [1, 5, 2]`: the bridge owner
    pays its endpoint (`5 < 7`) and one bvar owner pays its `H` (`1 < 2`). -/
theorem pin_bridge_focus_accepted : DMStep [1, 5, 2] [2, 7, 2] :=
  ⟨[2, 7], [1, 5], [2], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨7, by decide, by decide⟩⟩

/-- **§9 pure focus is local administration.** The strict request combines the
    focus with the bvar cut: `[1, 2, 1] → [1, 1, 1]` (`X = [2]`, `Y = [1]`). -/
theorem pin_focus_with_cut : DMStep [1, 1, 1] [1, 2, 1] :=
  ⟨[2], [1], [1, 1], List.cons_ne_nil _ _, List.Perm.swap 2 1 [1], List.Perm.refl _,
    fun y hy => ⟨2, List.mem_cons_self _ _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega⟩⟩

/-- **§9 admission calibration.** At the actual receipt weight the δ atom is
    `12` and the selected body `D_b` weighs `5`: strict. -/
theorem pin_admission_strict : DMStep [5] [12] :=
  ⟨[12], [5], [], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨12, List.mem_cons_self _ _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega⟩⟩

/-- **§9 admission calibration at `Aw ≡ 0`.** Both empty-frame keys are
    `([5], 5)`: no strict edge. -/
theorem pin_admission_zero_flat : ¬ LexDM ([5], 5) ([5], 5) :=
  accR_irrefl (lexDM_wf.apply _)

end Rcic.Syn

#print axioms Rcic.Syn.TyP.dchildren_wt_lt
#print axioms Rcic.Syn.CvP.dchildren_wt_lt
#print axioms Rcic.Syn.DNode.subAt_wt_lt
#print axioms Rcic.Syn.Occ.wt_lt_of_properDesc
#print axioms Rcic.Syn.frontier_cut
#print axioms Rcic.Syn.antichain_cut
#print axioms Rcic.Syn.admission_credit_type
#print axioms Rcic.Syn.admission_credit_def
#print axioms Rcic.Syn.no_defAdm_zero
#print axioms Rcic.Syn.sharedLT_wf
#print axioms Rcic.Syn.beforeSharedL_wf
#print axioms Rcic.Syn.beforeSharedL_irrefl
#print axioms Rcic.Syn.pin_double_materialization_rejected
#print axioms Rcic.Syn.pin_double_materialization_accepted
#print axioms Rcic.Syn.pin_bridge_endpoint_rejected
#print axioms Rcic.Syn.pin_bridge_focus_accepted
#print axioms Rcic.Syn.pin_focus_with_cut
#print axioms Rcic.Syn.pin_admission_strict
#print axioms Rcic.Syn.pin_admission_zero_flat

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §7 the A6 `C` payment, abstractly: two bvar owners pay the two `H` fields -/

/-- **A6 C (§10 table).** Two surviving bvar owners `[1 + w(H_L)]`, `[1 + w(H_R)]`
    pay the two `H` fields in one `DMStep` (`dmStep_two_sided`), the shared rest `K`
    kept once. The A6 pair query itself is not on this branch (`RcicSynA6Link` lands
    separately); this is the frontier edge its `C` request will use. -/
theorem a6_c_edge (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {iL iR : Nat}
    {AL AR : Expr Nat} {uL uR : Level}
    (hlL : lookupType Γ iL = some AL) (hAL : TyP E n Γ AL (.sort uL))
    (hlR : lookupType Γ iR = some AR) (hAR : TyP E n Γ AR (.sort uR)) (K : List Nat) :
    DMStep (hAL.atoms Aw ++ hAR.atoms Aw ++ K)
      ((TyP.bvar E n Γ iL AL uL hlL hAL).wt Aw :: (TyP.bvar E n Γ iR AR uR hlR hAR).wt Aw :: K) := by
  have h := dmStep_two_sided (x₁ := (TyP.bvar E n Γ iL AL uL hlL hAL).wt Aw)
    (x₂ := (TyP.bvar E n Γ iR AR uR hlR hAR).wt Aw)
    (Y₁ := hAL.atoms Aw) (Y₂ := hAR.atoms Aw) (Z₁ := []) (Z₂ := K)
    (fun y hy => Nat.lt_of_le_of_lt (TyP.atoms_le Aw hAL y hy) (by simp only [TyP.wt]; omega))
    (fun y hy => Nat.lt_of_le_of_lt (TyP.atoms_le Aw hAR y hy) (by simp only [TyP.wt]; omega))
  rw [List.append_nil] at h
  refine dmStep_perm_left ?_ h
  rw [List.append_assoc]

end Rcic.Syn

#print axioms Rcic.Syn.a6_c_edge
