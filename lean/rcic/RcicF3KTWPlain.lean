import rcic.RcicF3KTWSum

/-!
# F3 S7 KT-2b-3c-2: the plain telescope

The plain telescope: shapes of a constructor whose recursive-field domains depend
only on earlier plain fields (non-IR); discharges `SpecCover.shape`/`domCons`/`domEmpty`.

`PTel domP kinds 0 []` is the dependent telescope over the plain positions of `kinds`:
at a plain position `k` it chooses an index of the small domain `domP k spre`
(`spre` = small plain prefix so far); recursive positions add nothing.  `PlainDoms`
packs `kinds` with the small domains `domP` (plain) and `domR` (recursive); `D.layout tag`
assembles the `Layout` whose shapes are telescope elements, whose `nr` is the chosen
plain values, and whose `dom`/`pt` read off `kinds[k]?`.

`PlainHyp` states what the big-universe semantics must satisfy against the small
domains: plain field values land in `lift (domP k spre)`, `fn` domains lift to
`domBig`, `direct` domains are the one-element domain.  Under it:

- `PTel.exists_of_InPhi` builds a telescope element from any `InPhi`-derivable tuple
  (the induction; no choice);
- `PlainDoms.cover` gives `SpecCover (D.layout tag) Sm B` from a `covers` hypothesis;
- `PlainDoms.wshaped` combines it with `wshaped_phiSpec`.

Theory-agnostic.  closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v

namespace PSet

/-- The dependent telescope of plain choices: at a plain position `k` with small plain prefix `pre`,
an index of `domP k pre`; recursive positions add nothing. -/
def PTel (domP : Nat → List PSet.{u} → PSet.{u}) : List PKind → Nat → List PSet.{u} → Type u
  | [], _, _ => PUnit
  | .plain :: ps, k, pre => Σ i : (domP k pre).Idx, PTel domP ps (k + 1) (pre ++ [(domP k pre).Func i])
  | .direct :: ps, k, pre => PTel domP ps (k + 1) pre
  | .fn :: ps, k, pre => PTel domP ps (k + 1) pre

/-- The plain values chosen by a telescope element. -/
def PTel.vals (domP : Nat → List PSet.{u} → PSet.{u}) :
    (ps : List PKind) → (k : Nat) → (pre : List PSet.{u}) → PTel domP ps k pre → List PSet.{u}
  | [], _, _, _ => []
  | .plain :: ps, k, pre, ⟨i, t⟩ => (domP k pre).Func i :: PTel.vals domP ps (k + 1) (pre ++ [(domP k pre).Func i]) t
  | .direct :: ps, k, pre, t => PTel.vals domP ps (k + 1) pre t
  | .fn :: ps, k, pre, t => PTel.vals domP ps (k + 1) pre t

/-- The domain at one position: `domR` at `fn`, the one-element domain at `direct`,
empty elsewhere. -/
def domOf (domR : Nat → List PSet.{u} → PSet.{u}) : Option PKind → Nat → List PSet.{u} → PSet.{u}
  | some .fn, k, spre => domR k spre
  | some .direct, _, _ => singleton pempty
  | _, _, _ => pempty

/-- The class index at one position: the single class at `direct`, none elsewhere. -/
def ptOf (domR : Nat → List PSet.{u} → PSet.{u}) :
    (o : Option PKind) → (k : Nat) → (spre : List PSet.{u}) → Option (FBr (domOf domR o k spre))
  | some .direct, _, _ => some (Quotient.mk _ PUnit.unit)
  | _, _, _ => none

/-- Small per-position domains for a constructor. -/
structure PlainDoms where
  kinds : List PKind
  domP : Nat → List PSet.{u} → PSet.{u}
  domR : Nat → List PSet.{u} → PSet.{u}

/-- The layout of a `PlainDoms`: shapes are telescope elements, `nr` the chosen
plain values, `dom`/`pt` read off `kinds[k]?`. -/
def PlainDoms.layout (D : PlainDoms.{u}) (tag : Nat) : Layout (PTel D.domP D.kinds 0 []) where
  tag := tag
  kinds := D.kinds
  dom := fun k s => domOf D.domR D.kinds[k]? k (takePlain (D.kinds.take k) (PTel.vals D.domP D.kinds 0 [] s))
  pt := fun k s => ptOf D.domR D.kinds[k]? k (takePlain (D.kinds.take k) (PTel.vals D.domP D.kinds 0 [] s))
  nr := fun s => PTel.vals D.domP D.kinds 0 [] s

/-- What the big-universe semantics must satisfy against the small domains. -/
structure PlainHyp (D : PlainDoms.{u}) (Sm : Sem.{max u v}) : Prop where
  plain : ∀ (k : Nat) (pre : List PSet.{max u v}) (spre : List PSet.{u}) (x : PSet.{max u v}),
    D.kinds[k]? = some .plain → pre.length = k →
    LEq (List.map lift.{u, v} spre) (plainVals (D.kinds.take k) pre) →
    Sm.nonrecOk k pre x → x ∈ lift.{u, v} (D.domP k spre)
  fn : ∀ (k : Nat) (pre : List PSet.{max u v}) (spre : List PSet.{u}),
    D.kinds[k]? = some .fn → pre.length = k →
    LEq (List.map lift.{u, v} spre) (plainVals (D.kinds.take k) pre) →
    Equiv (lift.{u, v} (D.domR k spre)) (Sm.domBig k pre)
  direct : ∀ (k : Nat) (pre : List PSet.{max u v}),
    D.kinds[k]? = some .direct → Equiv (lift.{u, v} (singleton pempty)) (Sm.domBig k pre)

/-- Building a telescope element from fitting big values (the induction; no choice). -/
theorem PTel.exists_of_InPhi (D : PlainDoms.{u}) (Sm : Sem.{max u v}) (H : PlainHyp D Sm) (X : PSet.{max u v}) :
    ∀ (done ps : List PKind) (spre : List PSet.{u}) (pre xs : List PSet.{max u v}),
      D.kinds = done ++ ps → pre.length = done.length →
      LEq (List.map lift.{u, v} spre) (plainVals done pre) →
      Sm.InPhi X ps xs done.length pre →
      ∃ t : PTel D.domP ps done.length spre,
        LEq (List.map lift.{u, v} (PTel.vals D.domP ps done.length spre t)) (plainVals ps xs) := by
  suffices key : ∀ (n : Nat) (done ps : List PKind) (spre : List PSet.{u})
      (pre xs : List PSet.{max u v}), n = done.length →
      D.kinds = done ++ ps → pre.length = done.length →
      LEq (List.map lift.{u, v} spre) (plainVals done pre) →
      Sm.InPhi X ps xs n pre →
      ∃ t : PTel D.domP ps n spre,
        LEq (List.map lift.{u, v} (PTel.vals D.domP ps n spre t)) (plainVals ps xs) by
    intro done ps spre pre xs hD hlen hle hin
    exact key done.length done ps spre pre xs rfl hD hlen hle hin
  intro n done ps
  induction ps generalizing n done with
  | nil =>
      intro spre pre xs hn hD hlen hle hin
      cases xs with
      | nil => exact ⟨⟨⟩, trivial⟩
      | cons x xs =>
          exact Nat.noConfusion (Sem.InPhi.length Sm [] (x :: xs) n pre hin)
  | cons p ps ih =>
      intro spre pre xs hn hD hlen hle hin
      cases xs with
      | nil => exact Nat.noConfusion (Sem.InPhi.length Sm (p :: ps) [] n pre hin)
      | cons x xs =>
          have hn' : n + 1 = (done ++ [p]).length := by
            rw [List.length_append, hn, List.length_singleton]
          have hD' : D.kinds = (done ++ [p]) ++ ps := by
            rw [hD]; exact (List.append_assoc done [p] ps).symm
          have hlen' : (pre ++ [x]).length = (done ++ [p]).length := by
            rw [List.length_append, List.length_append, hlen, List.length_singleton,
              List.length_singleton]
          cases p with
          | plain =>
              obtain ⟨hnok, hrest⟩ := hin
              have hk : D.kinds[n]? = some .plain := by
                rw [hD, hn, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
                  List.getElem?_cons_zero]
              have htake : D.kinds.take n = done := by
                rw [hD, hn]; exact List.take_left' rfl
              have hle' : LEq (List.map lift.{u, v} spre) (plainVals (D.kinds.take n) pre) :=
                htake ▸ hle
              obtain ⟨y, hy, hxy⟩ := mem_lift.mp
                (H.plain n pre spre x hk (hlen.trans hn.symm) hle' hnok)
              obtain ⟨i, hi⟩ := hy
              have hle2 : LEq (List.map lift.{u, v} (spre ++ [(D.domP n spre).Func i]))
                  (plainVals (done ++ [.plain]) (pre ++ [x])) := by
                rw [List.map_append, plainVals_append done [.plain] pre [x] hlen]
                exact LEq_append hle ⟨(lift_equiv.{u, v} hi).trans hxy.symm, trivial⟩
              obtain ⟨t', ht'⟩ := ih (n + 1) (done ++ [.plain]) (spre ++ [(D.domP n spre).Func i])
                (pre ++ [x]) xs hn' hD' hlen' hle2 hrest
              exact ⟨⟨i, t'⟩, ⟨(lift_equiv.{u, v} hi).trans hxy.symm, ht'⟩⟩
          | direct =>
              obtain ⟨_, hrest⟩ := hin
              have hle2 : LEq (List.map lift.{u, v} spre) (plainVals (done ++ [.direct]) (pre ++ [x])) := by
                rw [plainVals_append done [.direct] pre [x] hlen]
                have hz : plainVals [.direct] [x] = ([] : List PSet.{max u v}) := rfl
                rw [hz, List.append_nil]; exact hle
              obtain ⟨t', ht'⟩ := ih (n + 1) (done ++ [.direct]) spre
                (pre ++ [x]) xs hn' hD' hlen' hle2 hrest
              exact ⟨t', ht'⟩
          | fn =>
              obtain ⟨_, hrest⟩ := hin
              have hle2 : LEq (List.map lift.{u, v} spre) (plainVals (done ++ [.fn]) (pre ++ [x])) := by
                rw [plainVals_append done [.fn] pre [x] hlen]
                have hz : plainVals [.fn] [x] = ([] : List PSet.{max u v}) := rfl
                rw [hz, List.append_nil]; exact hle
              obtain ⟨t', ht'⟩ := ih (n + 1) (done ++ [.fn]) spre
                (pre ++ [x]) xs hn' hD' hlen' hle2 hrest
              exact ⟨t', ht'⟩

/-- The assembled cover: `SpecCover` for a plain-telescope layout from `PlainHyp`
plus a `covers` hypothesis. -/
theorem PlainDoms.cover (D : PlainDoms.{u}) (tag : Nat) (Sm : Sem.{max u v}) (H : PlainHyp D Sm)
    {B : PSet.{max u v}}
    (hcov : ∀ (X : PSet.{u}) (xs : List PSet.{max u v}),
      Sm.InPhi (lift.{u, v} X) D.kinds xs 0 [] → dataVal tag xs ∈ B) :
    SpecCover (D.layout tag) Sm B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X xs hin
    exact hcov X xs hin
  · intro X xs hin
    obtain ⟨t, ht⟩ := PTel.exists_of_InPhi D Sm H (lift.{u, v} X) [] D.kinds [] [] xs
      rfl rfl trivial hin
    refine ⟨t, ht, ?_⟩
    intro k hk
    have hk' : D.kinds[k]? = some .direct := hk
    show (ptOf D.domR D.kinds[k]? k _).isSome
    rw [hk']
    rfl
  · intro s k pre hr hplen hle
    have hr' : D.kinds[k]? = some .direct ∨ D.kinds[k]? = some .fn := hr
    show Equiv (lift.{u, v}
      (domOf D.domR D.kinds[k]? k (takePlain (D.kinds.take k) (PTel.vals D.domP D.kinds 0 [] s))))
      (Sm.domBig k pre)
    rcases hr' with hk | hk
    · rw [hk]; exact H.direct k pre hk
    · rw [hk]; exact H.fn k pre _ hk hplen hle
  · intro s k hni
    have hni' : ¬ (D.kinds[k]? = some .direct ∨ D.kinds[k]? = some .fn) := hni
    show (domOf D.domR D.kinds[k]? k
      (takePlain (D.kinds.take k) (PTel.vals D.domP D.kinds 0 [] s))).Idx → False
    cases hko : D.kinds[k]? with
    | none => intro i; exact PEmpty.elim i
    | some pk =>
        cases pk with
        | plain => intro i; exact PEmpty.elim i
        | direct => intro _; exact hni' (Or.inl hko)
        | fn => intro _; exact hni' (Or.inr hko)

/-- The semantic spec of a plain-telescope layout is W-shaped. -/
theorem PlainDoms.wshaped (D : PlainDoms.{u}) (tag : Nat) (Sm : Sem.{max u v}) (H : PlainHyp D Sm)
    {B : PSet.{max u v}}
    (hcov : ∀ (X : PSet.{u}) (xs : List PSet.{max u v}),
      Sm.InPhi (lift.{u, v} X) D.kinds xs 0 [] → dataVal tag xs ∈ B) (ch : Choice.{u}) :
    WShaped.{u, v} (phiSpec (D.layout tag) Sm B) ((D.layout tag).sig Sm) :=
  wshaped_phiSpec (D.layout tag) Sm (D.cover tag Sm H hcov) ch

end PSet

end Rcic.F3
