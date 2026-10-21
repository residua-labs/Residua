/-! `RcicClosurePiRow` — `closure ⇒ piRow`, standalone (cc ruling on
#6293, 05:15Z, item (1); r1b).

The check-#10 wall: `LR.convClosed_idx` — conversion-closure of the
logical relation at the index level — would **imply the Π-row itself**.
This file makes the implication mechanical and sealed, in an
import-free abstraction:

* `Cv` is the abstract conversion. Every constructor is Π-head
  preserving — that absence is exactly "Π is whnf and not a K-core":
  whnf-ness says no contraction arm leaves the Π head, and the
  excluded K-core clause is the singleton-K escape that would relate
  a Π to a non-Π by proof-irrelevance. `cv_pi_both` is the induced
  two-sided inversion.
* `Clo` is the hypothetical closure at a code `Cod`: the sort-code
  clause (`sorts`), the Π clause (`pi`; `Pi(bot,bot)` is the instance
  the theorem uses), the base conversion row (`ofCv`), and
  conversion-closure on both sides (`convL`/`convR`).
* `closure_implies_piRow`: given self-relatedness of a typed Π, any
  `Cv (pi A B) (pi A' B')` yields `Cv A A' ∧ Cv B B'` — the Π-row.

So the missing premise is exactly the `Clo` — a conversion-closed
relation containing the typed Π and decomposing at the Π clause.
`closure_claim` stays 0. Axioms: none beyond the ambient core. -/

namespace Rcic

/-- Terms: sorts and Π's — the two head forms the rows read. -/
inductive Trow where
  | sort : Nat → Trow
  | pi : Trow → Trow → Trow
  deriving DecidableEq

/-- Relation codes: `bot` is the conversion row itself; `pi wA wB`
    is the Π clause with component rows `wA`/`wB`. -/
inductive Cod where
  | bot : Cod
  | pi : Cod → Cod → Cod
  deriving DecidableEq

/-- Abstract conversion: the sort-code clause (`sorts`), the Π
    congruence (`pi`), and the equivalence rules. No constructor
    relates a `pi` to a non-`pi` — the head form is a `Cv` invariant. -/
inductive Cv : Trow → Trow → Prop where
  | refl (a : Trow) : Cv a a
  | symm {a b : Trow} : Cv a b → Cv b a
  | trans {a b c : Trow} : Cv a b → Cv b c → Cv a c
  | pi {A A' B B' : Trow} : Cv A A' → Cv B B' → Cv (.pi A B) (.pi A' B')
  | sorts (u v : Nat) (h : u = v) : Cv (.sort u) (.sort v)

/-- Two-sided Π inversion for `Cv`: out of a Π on either side, the
    other side is a Π whose components convert pointwise. `trans` legs
    recurse through the (forced Π-headed) middle. -/
theorem cv_pi_both {a c : Trow} (h : Cv a c) :
    (∀ {A B}, a = .pi A B → ∃ A' B', c = .pi A' B' ∧ Cv A A' ∧ Cv B B') ∧
    (∀ {C D}, c = .pi C D → ∃ A B, a = .pi A B ∧ Cv A C ∧ Cv B D) := by
  induction h with
  | refl x =>
      exact ⟨fun e => ⟨_, _, e, .refl _, .refl _⟩,
             fun e => ⟨_, _, e, .refl _, .refl _⟩⟩
  | symm h ih =>
      exact ⟨fun e =>
                let ⟨P, Q, eq, hp, hq⟩ := ih.2 e
                ⟨P, Q, eq, hp.symm, hq.symm⟩,
             fun e =>
                let ⟨P, Q, eq, hp, hq⟩ := ih.1 e
                ⟨P, Q, eq, hp.symm, hq.symm⟩⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ⟨fun e =>
                let ⟨M₁, M₂, em, ha₁, hb₁⟩ := ih₁.1 e
                let ⟨C', D', ec, ha₂, hb₂⟩ := ih₂.1 em
                ⟨C', D', ec, ha₁.trans ha₂, hb₁.trans hb₂⟩,
             fun e =>
                let ⟨M₁, M₂, em, ha₂, hb₂⟩ := ih₂.2 e
                let ⟨A₀, B₀, ea, ha₁, hb₁⟩ := ih₁.2 em
                ⟨A₀, B₀, ea, ha₁.trans ha₂, hb₁.trans hb₂⟩⟩
  | pi hA hB =>
      exact ⟨fun e => by
                obtain ⟨eX, eY⟩ := Trow.pi.inj e
                subst eX; subst eY; exact ⟨_, _, rfl, hA, hB⟩,
             fun e => by
                obtain ⟨eC, eD⟩ := Trow.pi.inj e
                subst eC; subst eD; exact ⟨_, _, rfl, hA, hB⟩⟩
  | sorts u v huv =>
      exact ⟨fun e => Trow.noConfusion e, fun e => Trow.noConfusion e⟩

theorem cv_pi_invL {A B c : Trow} (h : Cv (.pi A B) c) :
    ∃ A' B', c = .pi A' B' ∧ Cv A A' ∧ Cv B B' :=
  (cv_pi_both h).1 rfl

theorem cv_pi_invR {a C D : Trow} (h : Cv a (.pi C D)) :
    ∃ A B, a = .pi A B ∧ Cv A C ∧ Cv B D :=
  (cv_pi_both h).2 rfl

/-- The hypothetical conversion-closed relation at a code: sort-code
    clause (`sorts`), Π clause (`pi`), conversion row at `bot`
    (`ofCv`), conversion-closure on both sides (`convL`/`convR`). -/
inductive Clo : Trow → Trow → Cod → Prop where
  | sorts (u v : Nat) (h : u = v) : Clo (.sort u) (.sort v) .bot
  | ofCv {a b : Trow} : Cv a b → Clo a b .bot
  | pi {A A' B B' : Trow} {wA wB : Cod} :
      Clo A A' wA → Clo B B' wB → Clo (.pi A B) (.pi A' B') (.pi wA wB)
  | convL {a a' b : Trow} {w : Cod} : Cv a a' → Clo a' b w → Clo a b w
  | convR {a b b' : Trow} {w : Cod} : Clo a b' w → Cv b' b → Clo a b w

/-- Π-code inversion: every path to a Π-pair at a Π code decomposes
    through the `pi` clause; `convL`/`convR` wrap Π-headed conversions
    only, so the component rows stay at the sub-codes. -/
theorem clo_pi_gen {a c : Trow} {w : Cod} (h : Clo a c w) :
    ∀ {A B A' B' wA wB}, a = .pi A B → c = .pi A' B' → w = .pi wA wB →
      Clo A A' wA ∧ Clo B B' wB := by
  induction h with
  | sorts u v huv => intro _ _ _ _ _ _ ea _ _; exact Trow.noConfusion ea
  | ofCv hcv => intro _ _ _ _ _ _ _ _ ew; exact Cod.noConfusion ew
  | pi hA hB ihA ihB =>
      intro _ _ _ _ _ _ ea ec ew
      obtain ⟨eX, eY⟩ := Trow.pi.inj ea
      obtain ⟨eX', eY'⟩ := Trow.pi.inj ec
      obtain ⟨ewA, ewB⟩ := Cod.pi.inj ew
      subst eX; subst eY; subst eX'; subst eY'; subst ewA; subst ewB
      exact ⟨hA, hB⟩
  | convL hc h ih =>
      intro _ _ _ _ _ _ ea ec ew
      obtain ⟨A₀, B₀, e₀, hA₀, hB₀⟩ := cv_pi_invL (ea ▸ hc)
      obtain ⟨hA', hB'⟩ := ih e₀ ec ew
      exact ⟨Clo.convL hA₀ hA', Clo.convL hB₀ hB'⟩
  | convR h hc ih =>
      intro _ _ _ _ _ _ ea ec ew
      obtain ⟨A₀, B₀, e₀, hA₀, hB₀⟩ := cv_pi_invR (ec ▸ hc)
      obtain ⟨hA', hB'⟩ := ih ea e₀ ew
      exact ⟨Clo.convR hA' hA₀, Clo.convR hB' hB₀⟩

/-- Base-code inversion: the `bot` row is exactly `Cv` (conv-closure
    legs collapse by `Cv.trans`). -/
theorem clo_bot_gen {a c : Trow} {w : Cod} (h : Clo a c w) :
    w = .bot → Cv a c := by
  induction h with
  | sorts u v huv => intro _; exact .sorts u v huv
  | ofCv hcv => intro _; exact hcv
  | pi hA hB ihA ihB => intro e; exact Cod.noConfusion e
  | convL hc h ih => intro e; exact hc.trans (ih e)
  | convR h hc ih => intro e; exact (ih e).trans hc

/-- THE TOOTH: a conv-closed `Clo` decomposing at `Pi(bot,bot)` and
    containing the self-pair of every typed Π forces the Π-row —
    `Cv (pi A B) (pi A' B') → Cv A A' ∧ Cv B B'`. `Ty` is the ambient
    typing (abstract; only self-relatedness is consumed). -/
theorem closure_implies_piRow {Ty : Trow → Prop}
    (hself : ∀ {A B}, Ty (.pi A B) → Clo (.pi A B) (.pi A B) (.pi .bot .bot))
    {A B A' B' : Trow} (hty : Ty (.pi A B))
    (h : Cv (.pi A B) (.pi A' B')) : Cv A A' ∧ Cv B B' :=
  let hcl := Clo.convR (hself hty) h
  let ⟨hA, hB⟩ := clo_pi_gen hcl rfl rfl rfl
  ⟨clo_bot_gen hA rfl, clo_bot_gen hB rfl⟩

#print axioms closure_implies_piRow

end Rcic
