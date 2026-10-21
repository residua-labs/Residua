import rcic.RcicDeclarative
import rcic.RcicParRedCore
import rcic.RcicLevelZero
import rcic.RcicLevelCalc
import rcic.RcicTypedLevels
import rcic.RcicLevelDec

/-!
# Syntactic sortRow, build step 1a — the level treatment (`≈`, confluence modulo `≈`)

`research/rcic/semantic/S0_SORTROW_SYNTACTIC.md` §2.1 ("Levels") and
`S1_ORDER_ENRICHED_LEVELS.md` §2. The erased system E keeps levels VERBATIM. There is no level
canonical form: the on-tree `nf` is sealed-incomplete (`canon_sep_counter_*`,
`RcicLevelDec.lean:6881-6909`). Conversion is taken modulo `≈`, the level congruence on erased terms.
The final step of sortRow needs only `sort l ↔*_{E∪≈} sort l' → eqN l l'`
(`eqN_of_convMod_sort`). It holds for ANY rewrite relation `R` that
* is confluent;
* is strongly simulated by `≈` (`StrongSim`): `a ≈ a'` and `a → b` give some `b'` with `a' → b'`
  and `b ≈ b'`;
* has the sorts as normal forms.

These are Huet's confluence-modulo conditions in the strongly coherent case. E itself is build
step 2; here `R` is a hypothesis.

Also here:
* the erased syntax `ETm`, with its `lift`/`inst`/`instLevels`;
* the `≈` congruences that E's strong simulation consumes (substitution, level instantiation at
  `≈` lists);
* the tag facts. A tag is `levelIsZero`, and it is `eqN`-invariant.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 erased terms -/

/-- Erased terms. λ-domains are erased; Π-domains are kept. `star` is a maximal proof. There are no
    `letE` (inlined) and no `lit` (erased through `natExpand`). Levels are verbatim. -/
inductive ETm : Type
  | bvar : Nat → ETm
  | star : ETm
  | sort : Level → ETm
  | const : Nat → List Level → ETm
  | app : ETm → ETm → ETm
  | lam : ETm → ETm
  | pi : ETm → ETm → ETm
  deriving DecidableEq

namespace ETm

def lift (c k : Nat) : ETm → ETm
  | .bvar i => if c ≤ i then .bvar (i + k) else .bvar i
  | .star => .star
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (lift c k f) (lift c k a)
  | .lam b => .lam (lift (c + 1) k b)
  | .pi a b => .pi (lift c k a) (lift (c + 1) k b)

/-- `bvar j ↦ r`, the indices above `j` shift down, and `r` is lifted under binders (as `instantiate`). -/
def inst (j : Nat) (r : ETm) : ETm → ETm
  | .bvar i => if i = j then r else if j < i then .bvar (i - 1) else .bvar i
  | .star => .star
  | .sort l => .sort l
  | .const c ls => .const c ls
  | .app f a => .app (inst j r f) (inst j r a)
  | .lam b => .lam (inst (j + 1) (lift 0 1 r) b)
  | .pi a b => .pi (inst j r a) (inst (j + 1) (lift 0 1 r) b)

/-- level instantiation, through the landed `instLevel` (as `instantiateLevels`). -/
def instLevels (ls : List Level) : ETm → ETm
  | .bvar i => .bvar i
  | .star => .star
  | .sort l => .sort (instLevel ls l)
  | .const r ms => .const r (ms.map (instLevel ls))
  | .app f a => .app (instLevels ls f) (instLevels ls a)
  | .lam b => .lam (instLevels ls b)
  | .pi a b => .pi (instLevels ls a) (instLevels ls b)

end ETm

/-! ## §2 the level congruence `≈` -/

/-- `≈`: the same shape, `sort` levels pairwise `eqN`, `const` level lists `eqNList`. It is
    an equivalence (`lvlEq_equivalence`), never a canonical form. -/
inductive LvlEq : ETm → ETm → Prop
  | bvar (i : Nat) : LvlEq (.bvar i) (.bvar i)
  | star : LvlEq .star .star
  | sort {l l' : Level} (h : eqN l l') : LvlEq (.sort l) (.sort l')
  | const (r : Nat) {ls ls' : List Level} (h : eqNList ls ls') : LvlEq (.const r ls) (.const r ls')
  | app {f f' a a' : ETm} (hf : LvlEq f f') (ha : LvlEq a a') : LvlEq (.app f a) (.app f' a')
  | lam {b b' : ETm} (hb : LvlEq b b') : LvlEq (.lam b) (.lam b')
  | pi {a a' b b' : ETm} (ha : LvlEq a a') (hb : LvlEq b b') : LvlEq (.pi a b) (.pi a' b')

theorem LvlEq.rfl' : (t : ETm) → LvlEq t t
  | .bvar i => .bvar i
  | .star => .star
  | .sort l => .sort (eqN_refl l)
  | .const r ls => .const r (eqNList_refl ls)
  | .app f a => .app (LvlEq.rfl' f) (LvlEq.rfl' a)
  | .lam b => .lam (LvlEq.rfl' b)
  | .pi a b => .pi (LvlEq.rfl' a) (LvlEq.rfl' b)

theorem LvlEq.symm' {t t' : ETm} (h : LvlEq t t') : LvlEq t' t := by
  induction h with
  | bvar i => exact .bvar i
  | star => exact .star
  | sort h => exact .sort (eqN_symm h)
  | const r h => exact .const r (eqNList_symm h)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ ih => exact .lam ih
  | pi _ _ iha ihb => exact .pi iha ihb

theorem LvlEq.trans' {t t' t'' : ETm} (h1 : LvlEq t t') (h2 : LvlEq t' t'') : LvlEq t t'' := by
  induction h1 generalizing t'' with
  | bvar i => exact h2
  | star => exact h2
  | sort h =>
      cases h2 with
      | sort h' => exact .sort (eqN_trans h h')
  | const r h =>
      cases h2 with
      | const _ h' => exact .const r (eqNList_trans h h')
  | app _ _ ihf iha =>
      cases h2 with
      | app hf' ha' => exact .app (ihf hf') (iha ha')
  | lam _ ih =>
      cases h2 with
      | lam hb' => exact .lam (ih hb')
  | pi _ _ iha ihb =>
      cases h2 with
      | pi ha' hb' => exact .pi (iha ha') (ihb hb')

theorem lvlEq_equivalence : Equivalence LvlEq :=
  ⟨LvlEq.rfl', LvlEq.symm', LvlEq.trans'⟩

/-- a sort is `≈` only to a sort, at an `eqN` level. -/
theorem lvlEq_sort_left {l : Level} {x : ETm} (h : LvlEq (.sort l) x) :
    ∃ l', x = .sort l' ∧ eqN l l' := by
  cases h with
  | sort h => exact ⟨_, rfl, h⟩

theorem eqN_of_lvlEq_sort {l l' : Level} (h : LvlEq (.sort l) (.sort l')) : eqN l l' := by
  cases h with
  | sort h => exact h

theorem LvlEq.lift' {t t' : ETm} (h : LvlEq t t') (c k : Nat) :
    LvlEq (t.lift c k) (t'.lift c k) := by
  induction h generalizing c with
  | bvar i =>
      simp only [ETm.lift]
      split
      · exact .bvar _
      · exact .bvar _
  | star => exact .star
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ ihf iha => exact .app (ihf c) (iha c)
  | lam _ ih => exact .lam (ih (c + 1))
  | pi _ _ iha ihb => exact .pi (iha c) (ihb (c + 1))

/-- `≈` is a congruence for substitution, in both the body and the replacement. This is what E's
    β/ι/unfold right-hand sides need for the strong simulation. -/
theorem LvlEq.inst' {t t' : ETm} (h : LvlEq t t') :
    ∀ (j : Nat) {r r' : ETm}, LvlEq r r' → LvlEq (ETm.inst j r t) (ETm.inst j r' t') := by
  induction h with
  | bvar i =>
      intro j r r' hr
      simp only [ETm.inst]
      split
      · exact hr
      · split
        · exact .bvar _
        · exact .bvar _
  | star => intro _ _ _ _; exact .star
  | sort h => intro _ _ _ _; exact .sort h
  | const c h => intro _ _ _ _; exact .const c h
  | app _ _ ihf iha => intro j r r' hr; exact .app (ihf j hr) (iha j hr)
  | lam _ ih => intro j r r' hr; exact .lam (ih (j + 1) (hr.lift' 0 1))
  | pi _ _ iha ihb => intro j r r' hr; exact .pi (iha j hr) (ihb (j + 1) (hr.lift' 0 1))

/-- `≈` is preserved by instantiating both sides at one list (DT-002's `eqN_instLevel`). -/
theorem LvlEq.instLevels' {t t' : ETm} (h : LvlEq t t') (ls : List Level) :
    LvlEq (t.instLevels ls) (t'.instLevels ls) := by
  induction h with
  | bvar i => exact .bvar i
  | star => exact .star
  | sort h => exact .sort (eqN_instLevel h ls)
  | const r h => exact .const r (eqNList_map_instLevel ls _ _ h)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ ih => exact .lam ih
  | pi _ _ iha ihb => exact .pi iha ihb

/-- one schema instantiated at two `eqNList` lists gives `≈` terms (`instLevel_eqNList`). This is the
    level half of E's strong simulation for the level-polymorphic rule schemas. -/
theorem lvlEq_instLevels_of_eqNList {ls ls' : List Level} (h : eqNList ls ls') :
    (t : ETm) → LvlEq (t.instLevels ls) (t.instLevels ls')
  | .bvar i => .bvar i
  | .star => .star
  | .sort l => .sort (instLevel_eqNList h l)
  | .const r ms => .const r (instLevel_eqNList_map h ms)
  | .app f a => .app (lvlEq_instLevels_of_eqNList h f) (lvlEq_instLevels_of_eqNList h a)
  | .lam b => .lam (lvlEq_instLevels_of_eqNList h b)
  | .pi a b => .pi (lvlEq_instLevels_of_eqNList h a) (lvlEq_instLevels_of_eqNList h b)

/-! ## §3 tags: `levelIsZero` is `eqN`-invariant -/

/-- the tag of a recorded sort is `eqN`-invariant (`levelIsZero_iff`, `RcicLevelZero.lean:151`). -/
theorem levelIsZero_congr {l l' : Level} (h : eqN l l') : levelIsZero l = levelIsZero l' := by
  cases hl : levelIsZero l <;> cases hl' : levelIsZero l'
  · exact rfl
  · have hz : levelIsZero l = true :=
      (levelIsZero_iff l).mpr (eqN_trans h ((levelIsZero_iff l').mp hl'))
    rw [hl] at hz; exact hz
  · have hz : levelIsZero l' = true :=
      (levelIsZero_iff l').mpr (eqN_trans (eqN_symm h) ((levelIsZero_iff l).mp hl))
    rw [hl'] at hz; exact hz.symm
  · exact rfl

/-- the imax fact, structurally: `Π A B` is a Prop iff `B` is. -/
theorem levelIsZero_imax (u v : Level) : levelIsZero (.imax u v) = levelIsZero v := rfl

/-- a schema's tags agree at `eqNList` instantiations (R1: `Box.{u}`'s field tag at `ls` vs `ls'`). -/
theorem levelIsZero_instLevel_congr {ls ls' : List Level} (h : eqNList ls ls') (u : Level) :
    levelIsZero (instLevel ls u) = levelIsZero (instLevel ls' u) :=
  levelIsZero_congr (instLevel_eqNList h u)

/-! ## §4 confluence modulo `≈`, abstractly (Huet, strongly coherent case) -/

/-- reflexive-transitive closure. -/
inductive RStar {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : RStar R a a
  | step {a b c : α} (h : R a b) (hs : RStar R b c) : RStar R a c

/-- conversion modulo `Q`: the equivalence closure of `R ∪ Q`. -/
inductive ConvMod {α : Type} (R Q : α → α → Prop) : α → α → Prop
  | refl (a : α) : ConvMod R Q a a
  | fwd {a b : α} (h : R a b) : ConvMod R Q a b
  | bwd {a b : α} (h : R b a) : ConvMod R Q a b
  | eqv {a b : α} (h : Q a b) : ConvMod R Q a b
  | trans {a b c : α} (h1 : ConvMod R Q a b) (h2 : ConvMod R Q b c) : ConvMod R Q a c

/-- `Q` strongly simulates `R`: one `R` step on one side is matched by one on the other. -/
def StrongSim {α : Type} (Q R : α → α → Prop) : Prop :=
  ∀ {a a' b : α}, Q a a' → R a b → ∃ b', R a' b' ∧ Q b b'

/-- confluence (the Church–Rosser property of `R*`). -/
def Confluent {α : Type} (R : α → α → Prop) : Prop :=
  ∀ {a b c : α}, RStar R a b → RStar R a c → ∃ d, RStar R b d ∧ RStar R c d

/-- joinable modulo `Q`: `a →* c Q d *← b`. -/
def JoinMod {α : Type} (R Q : α → α → Prop) (a b : α) : Prop :=
  ∃ c d, RStar R a c ∧ Q c d ∧ RStar R b d

theorem RStar.trans' {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : RStar R a b) (h2 : RStar R b c) : RStar R a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem RStar.single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : RStar R a b :=
  .step h (.refl b)

/-- the strong simulation lifts to `R*`. -/
theorem strongSim_star {α : Type} {Q R : α → α → Prop} (hsim : StrongSim Q R) :
    ∀ {a a' b : α}, Q a a' → RStar R a b → ∃ b', RStar R a' b' ∧ Q b b' := by
  intro a a' b hq hs
  induction hs generalizing a' with
  | refl => exact ⟨a', .refl a', hq⟩
  | step h _ ih =>
      obtain ⟨m', hm', hqm⟩ := hsim hq h
      obtain ⟨b', hb', hqb⟩ := ih hqm
      exact ⟨b', .step hm' hb', hqb⟩

/-- `JoinMod` is transitive, under confluence and the strong simulation. -/
theorem joinMod_trans {α : Type} {R Q : α → α → Prop} (hQ : Equivalence Q)
    (hsim : StrongSim Q R) (hcr : Confluent R) {a b c : α}
    (h1 : JoinMod R Q a b) (h2 : JoinMod R Q b c) : JoinMod R Q a c := by
  obtain ⟨c1, d1, ha1, hq1, hb1⟩ := h1
  obtain ⟨c2, d2, hb2, hq2, hc2⟩ := h2
  obtain ⟨e, hd1e, hc2e⟩ := hcr hb1 hb2
  obtain ⟨e1, hc1e1, hqe1⟩ := strongSim_star hsim (hQ.symm hq1) hd1e
  obtain ⟨e2, hd2e2, hqe2⟩ := strongSim_star hsim hq2 hc2e
  exact ⟨e1, e2, ha1.trans' hc1e1, hQ.trans (hQ.symm hqe1) hqe2, hc2.trans' hd2e2⟩

/-- CONFLUENCE MODULO `Q`: every conversion `(R ∪ R⁻¹ ∪ Q)*` is a join modulo `Q`. -/
theorem joinMod_of_convMod {α : Type} {R Q : α → α → Prop} (hQ : Equivalence Q)
    (hsim : StrongSim Q R) (hcr : Confluent R) {a b : α} (h : ConvMod R Q a b) :
    JoinMod R Q a b := by
  induction h with
  | refl a => exact ⟨a, a, .refl a, hQ.refl a, .refl a⟩
  | fwd h => exact ⟨_, _, .single h, hQ.refl _, .refl _⟩
  | bwd h => exact ⟨_, _, .refl _, hQ.refl _, .single h⟩
  | eqv h => exact ⟨_, _, .refl _, h, .refl _⟩
  | trans _ _ ih1 ih2 => exact joinMod_trans hQ hsim hcr ih1 ih2

/-- an `R`-normal term reduces only to itself. -/
theorem rstar_of_normal {α : Type} {R : α → α → Prop} {x y : α} (hn : ∀ z, ¬ R x z)
    (h : RStar R x y) : y = x := by
  cases h with
  | refl => rfl
  | step h _ => exact absurd h (hn _)

/-- SORT SEPARATION modulo `≈`, the final step of sortRow (cc ruling (a)). It holds for any `R` that
    is confluent, is strongly simulated by `≈`, and has the sorts as normal forms. -/
theorem eqN_of_convMod_sort {R : ETm → ETm → Prop} (hsim : StrongSim LvlEq R)
    (hcr : Confluent R) (hnf : ∀ (l : Level) (t : ETm), ¬ R (.sort l) t) {l l' : Level}
    (h : ConvMod R LvlEq (.sort l) (.sort l')) : eqN l l' := by
  obtain ⟨c, d, hc, hq, hd⟩ := joinMod_of_convMod lvlEq_equivalence hsim hcr h
  have hc' := rstar_of_normal (hnf l) hc
  have hd' := rstar_of_normal (hnf l') hd
  subst hc'; subst hd'
  exact eqN_of_lvlEq_sort hq

/-! ## §5 pins -/

/-- PIN (ds-refute #6777 §3.1's closed counterexample, now one `≈` step). `imax 1 u =ₙ u` has two
    distinct `IsCanon` forms, so no canonical-form erasure relates them. `≈` does, from the
    sealed `canon_sep_counter_eqN`. -/
theorem lvlEq_canon_sep_counter :
    LvlEq (.sort (.imax (.succ .zero) (.param 0))) (.sort (.param 0)) :=
  .sort canon_sep_counter_eqN

/-- PIN (non-vacuity of sort separation): `sort 0` and `sort 1` are not convertible modulo `≈`
    under the empty relation, which is trivially confluent and simulated. -/
theorem not_convMod_sort_zero_one :
    ¬ ConvMod (fun _ _ : ETm => False) LvlEq (.sort .zero) (.sort (.succ .zero)) := by
  intro h
  have hsim : StrongSim LvlEq (fun _ _ : ETm => False) := fun _ hr => hr.elim
  have hcr : Confluent (fun _ _ : ETm => False) := by
    intro a b c hb hc
    cases hb with
    | refl => exact ⟨c, hc, .refl c⟩
    | step hr _ => exact hr.elim
  have he := eqN_of_convMod_sort hsim hcr (fun _ _ hr => hr) h
  have h0 : (some 0 : Option Nat) = some 1 := he (fun _ => none)
  injection h0 with h1
  exact Nat.noConfusion h1

end Rcic.Syn

#print axioms Rcic.Syn.LvlEq.rfl'
#print axioms Rcic.Syn.LvlEq.symm'
#print axioms Rcic.Syn.LvlEq.trans'
#print axioms Rcic.Syn.lvlEq_equivalence
#print axioms Rcic.Syn.lvlEq_sort_left
#print axioms Rcic.Syn.eqN_of_lvlEq_sort
#print axioms Rcic.Syn.LvlEq.lift'
#print axioms Rcic.Syn.LvlEq.inst'
#print axioms Rcic.Syn.LvlEq.instLevels'
#print axioms Rcic.Syn.lvlEq_instLevels_of_eqNList
#print axioms Rcic.Syn.levelIsZero_congr
#print axioms Rcic.Syn.levelIsZero_imax
#print axioms Rcic.Syn.levelIsZero_instLevel_congr
#print axioms Rcic.Syn.RStar.trans'
#print axioms Rcic.Syn.RStar.single
#print axioms Rcic.Syn.strongSim_star
#print axioms Rcic.Syn.joinMod_trans
#print axioms Rcic.Syn.joinMod_of_convMod
#print axioms Rcic.Syn.rstar_of_normal
#print axioms Rcic.Syn.eqN_of_convMod_sort
#print axioms Rcic.Syn.lvlEq_canon_sep_counter
#print axioms Rcic.Syn.not_convMod_sort_zero_one
