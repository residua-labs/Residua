import rcic.RcicF3KTWPlain

/-!
# F3 S7 KT-2b-3c-2b: small domains chosen from big ones

`BigDoms` carries the big-universe domains (`bigP` for plain fields, `bigR` for
recursive fields) together with `Small` witnesses; `G.toPlain ch` picks a small
representative of each big domain by `Choice`, producing a `PlainDoms`.

`fillPlain` reconstructs a big prefix from small plain values: lifted at plain
positions, `∅` at recursive ones.  `BigHyp` is the non-IR locality hypothesis:
each big domain depends only on the plain prefix (`plainLoc`/`fnLoc`), plain
values land in `bigP`, `fn` domains equal `domBig`, `direct` domains are the
one-element domain.  `BigHyp.toPlain` discharges `PlainHyp` for the chosen
representatives; `BigDoms.wshaped` is then one line over `PlainDoms.wshaped`.

Theory-agnostic.  closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v

namespace PSet

/-- Big prefix from small plain values: lifted at plain positions, `∅` at recursive ones. -/
def fillPlain : List PKind → List PSet.{u} → List PSet.{max u v}
  | [], _ => []
  | .plain :: ps, spre => lift.{u, v} (spre.headD pempty) :: fillPlain ps spre.tail
  | .direct :: ps, spre => pempty :: fillPlain ps spre
  | .fn :: ps, spre => pempty :: fillPlain ps spre

theorem fillPlain_length : (ps : List PKind) → (spre : List PSet.{u}) →
    (fillPlain.{u, v} ps spre).length = ps.length
  | [], _ => rfl
  | p :: ps, spre => by cases p <;> exact congrArg Nat.succ (fillPlain_length ps _)

theorem plainVals_fillPlain : (ps : List PKind) → (spre : List PSet.{u}) →
    spre.length = plainCount ps →
    LEq (plainVals ps (fillPlain.{u, v} ps spre)) (List.map lift.{u, v} spre)
  | [], spre, h => by
      cases spre with
      | nil => exact trivial
      | cons v spre' => exact Nat.noConfusion h
  | .plain :: ps, spre, h => by
      cases spre with
      | nil => exact Nat.noConfusion h
      | cons v spre' =>
          exact ⟨Equiv.refl _, plainVals_fillPlain ps spre' (Nat.succ.inj h)⟩
  | .direct :: ps, spre, h => plainVals_fillPlain ps spre h
  | .fn :: ps, spre, h => plainVals_fillPlain ps spre h

/-- A small representative of a small set, chosen by `Choice`. -/
def smallRep (ch : Choice.{u}) (x : PSet.{max u v}) (hx : Small.{u, v} x) : PSet.{u} :=
  (ch (α := PSet.{u}) (fun y => Equiv x (lift.{u, v} y)) hx).1

theorem smallRep_spec (ch : Choice.{u}) (x : PSet.{max u v}) (hx : Small.{u, v} x) :
    Equiv x (lift.{u, v} (smallRep ch x hx)) :=
  (ch (α := PSet.{u}) (fun y => Equiv x (lift.{u, v} y)) hx).2

/-- Big-universe domains for a constructor, with smallness witnesses. -/
structure BigDoms where
  kinds : List PKind
  bigP : Nat → List PSet.{max u v} → PSet.{max u v}
  bigR : Nat → List PSet.{max u v} → PSet.{max u v}
  smallP : ∀ k pre, Small.{u, v} (bigP k pre)
  smallR : ∀ k pre, Small.{u, v} (bigR k pre)

/-- Small domains chosen from the big ones: the representative of `bigX k` evaluated
on the reconstructed big prefix. -/
def BigDoms.toPlain (ch : Choice.{u}) (G : BigDoms.{u, v}) : PlainDoms.{u} where
  kinds := G.kinds
  domP := fun k spre => smallRep ch (G.bigP k (fillPlain.{u, v} (G.kinds.take k) spre)) (G.smallP _ _)
  domR := fun k spre => smallRep ch (G.bigR k (fillPlain.{u, v} (G.kinds.take k) spre)) (G.smallR _ _)

/-- Semantic locality (non-IR): each big domain depends only on the plain prefix. -/
structure BigHyp (G : BigDoms.{u, v}) (Sm : Sem.{max u v}) : Prop where
  plain : ∀ k pre x, G.kinds[k]? = some .plain → pre.length = k → Sm.nonrecOk k pre x → x ∈ G.bigP k pre
  plainLoc : ∀ k pre pre', G.kinds[k]? = some .plain → pre.length = k → pre'.length = k →
    LEq (plainVals (G.kinds.take k) pre) (plainVals (G.kinds.take k) pre') → Equiv (G.bigP k pre) (G.bigP k pre')
  fn : ∀ k pre, G.kinds[k]? = some .fn → pre.length = k → Equiv (G.bigR k pre) (Sm.domBig k pre)
  fnLoc : ∀ k pre pre', G.kinds[k]? = some .fn → pre.length = k → pre'.length = k →
    LEq (plainVals (G.kinds.take k) pre) (plainVals (G.kinds.take k) pre') → Equiv (G.bigR k pre) (G.bigR k pre')
  direct : ∀ k pre, G.kinds[k]? = some .direct → Equiv (lift.{u, v} (singleton pempty)) (Sm.domBig k pre)

/-- `PlainHyp` for the chosen small representatives. -/
theorem BigHyp.toPlain (ch : Choice.{u}) {G : BigDoms.{u, v}} {Sm : Sem.{max u v}} (H : BigHyp G Sm) :
    PlainHyp (G.toPlain ch) Sm := by
  refine ⟨?_, ?_, ?_⟩
  · intro k pre spre x hk hlen hle hnok
    have hk' : G.kinds[k]? = some .plain := hk
    have hle' : LEq (List.map lift.{u, v} spre) (plainVals (G.kinds.take k) pre) := hle
    have hmem : x ∈ G.bigP k pre := H.plain k pre x hk' hlen hnok
    have hklt : k < G.kinds.length := (List.getElem?_eq_some.mp hk').1
    have htk : (G.kinds.take k).length = k := by
      rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hklt)
    have hspre : spre.length = plainCount (G.kinds.take k) := by
      have h1 := LEq.length hle'
      rw [List.length_map,
        plainVals_length (G.kinds.take k) pre (by rw [hlen, htk])] at h1
      exact h1
    have hpv : LEq (plainVals (G.kinds.take k) pre)
        (plainVals (G.kinds.take k) (fillPlain.{u, v} (G.kinds.take k) spre)) :=
      hle'.symm.trans (plainVals_fillPlain (G.kinds.take k) spre hspre).symm
    have e1 : Equiv (G.bigP k pre)
        (G.bigP k (fillPlain.{u, v} (G.kinds.take k) spre)) :=
      H.plainLoc k pre _ hk' hlen (by rw [fillPlain_length]; exact htk) hpv
    exact mem_congr_right
      (e1.trans (smallRep_spec ch _ (G.smallP k _))) hmem
  · intro k pre spre hk hlen hle
    have hk' : G.kinds[k]? = some .fn := hk
    have hle' : LEq (List.map lift.{u, v} spre) (plainVals (G.kinds.take k) pre) := hle
    have hklt : k < G.kinds.length := (List.getElem?_eq_some.mp hk').1
    have htk : (G.kinds.take k).length = k := by
      rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hklt)
    have hspre : spre.length = plainCount (G.kinds.take k) := by
      have h1 := LEq.length hle'
      rw [List.length_map,
        plainVals_length (G.kinds.take k) pre (by rw [hlen, htk])] at h1
      exact h1
    have hpv : LEq (plainVals (G.kinds.take k) pre)
        (plainVals (G.kinds.take k) (fillPlain.{u, v} (G.kinds.take k) spre)) :=
      hle'.symm.trans (plainVals_fillPlain (G.kinds.take k) spre hspre).symm
    have e1 : Equiv (G.bigR k pre)
        (G.bigR k (fillPlain.{u, v} (G.kinds.take k) spre)) :=
      H.fnLoc k pre _ hk' hlen (by rw [fillPlain_length]; exact htk) hpv
    exact ((e1.trans (smallRep_spec ch _ (G.smallR k _))).symm).trans
      (H.fn k pre hk' hlen)
  · intro k pre hk
    exact H.direct k pre hk

/-- The semantic spec of a big-domain layout is W-shaped. -/
theorem BigDoms.wshaped (ch : Choice.{u}) (G : BigDoms.{u, v}) (tag : Nat) (Sm : Sem.{max u v}) (H : BigHyp G Sm)
    {B : PSet.{max u v}}
    (hcov : ∀ (X : PSet.{u}) (xs : List PSet.{max u v}),
      Sm.InPhi (lift.{u, v} X) G.kinds xs 0 [] → dataVal tag xs ∈ B) :
    WShaped.{u, v} (phiSpec ((G.toPlain ch).layout tag) Sm B) (((G.toPlain ch).layout tag).sig Sm) :=
  PlainDoms.wshaped _ tag Sm (BigHyp.toPlain ch H) hcov ch

end PSet

end Rcic.F3
