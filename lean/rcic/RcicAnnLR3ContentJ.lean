import rcic.RcicAnnLR3ContentCodes

/-!
# The J Ty arm in the content model

`recCode r u rf` is the content code of the type of the AnySort Eq recursor
(`EqLargeFixture`, reference 65), for the Eq family `r`, motive level `u` and
the raw image `rf` of `refl A a`:

`Π (A : Sort 1) (a : A) (P : Π b : A, Eq A a b → Sort u) (m : P a (refl A a))
  (b : A) (h : Eq A a b), P b h`.

It is closed and kinded when `rf` is well formed (`recCode_wfc`).

**`rec_member`.** Every K-like operator (`KLikeOp`: its six-fold
application is the minor premise; the K-like Eq hook computes the recursor
constant to such an operator, `EqKLikeHook.kTerm_apply`) is related to itself
by the reading of the recursor type, at every motive level, in every
saturated environment. The proof is the content of Eq: a proof `h` of
`Eq A a b` relates `a` and `b` in `A`, and the motive's candidate family is
invariant along `Π b : A, Eq A a b → Sort u`, so the minor moves from
`P a (refl A a)` to `P b h`. The motive's codomain is any `Sort u`
(large elimination).

Not claimed: the image of the actual recursor type of the environment is
the image of `recCode` (a Target judgment), a reader, or a Fundamental.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ContentJ

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe (REnv rcons Sat)
open CandidateTowerCoherence (upd)
open ContentCodes

/-- The term image of a bound variable, as the evaluator reads it. -/
def wb (i : Nat) : TImg := fun σ => withBot (σ i)

theorem wb_tok (i : Nat) : TOk (wb i) := ⟨LevelGirard.var_cont i, fun _ => Or.inl rfl⟩

theorem wb_closed {n i : Nat} (h : i < n) : TClosed n (wb i) := fun σ σ' hσ => by
  show withBot (σ i) = withBot (σ' i)
  rw [hσ i h]

theorem wb_upd {i j : Nat} (h : i ≠ j) (σ : REnv) (v : Value) : wb i (upd σ j v) = wb i σ := by
  show withBot (upd σ j v i) = withBot (σ i)
  rw [upd_ne σ v h]

/-- The motive type `Π (b : A), Eq A a b → Sort u`, in the context `[a, A]`. -/
def motiveTy (r u : Nat) := DCode.pi (.var 1 1 []) (.pi (.eq r (.var 1 2 []) (wb 1) (wb 0)) (.univ u))

/-- The type of the AnySort Eq recursor, for the index-retaining Eq family
`r`, motive level `u`, and the raw image `rf` of `refl A a` in the context
`[P, a, A]`:
`Π (A : Sort 1) (a : A) (P : Π b : A, Eq A a b → Sort u) (m : P a (refl A a))
  (b : A) (h : Eq A a b), P b h`. -/
def recCode (r u : Nat) (rf : TImg) :=
  DCode.pi (.univ 1) (.pi (.var 1 0 []) (.pi (motiveTy r u)
    (.pi (.var u 0 [wb 1, rf]) (.pi (.var 1 3 [])
      (.pi (.eq r (.var 1 4 []) (wb 3) (wb 0)) (.var u 3 [wb 1, wb 0]))))))

theorem motiveTy_kind (r u : Nat) : kindOf (motiveTy r u) = some (u, 2) := rfl

theorem kinded_var_nil {κ : List (Option (Nat × Nat))} {k i : Nat}
    (h : κ[i]? = some (some (k, 0))) : Kinded κ (DCode.var k i []) :=
  ⟨h, by simp, fun _ _ => rfl⟩

theorem mem_two {α : Type} {x a b : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  exact h

/-- The recursor type is a closed, kinded code when the refl image is well
formed, reads only the first three slots and not the motive's slot. -/
theorem recCode_wfc (r u : Nat) {rf : TImg} (hrf : TOk rf) (hcl : TClosed 3 rf)
    (hfree : ∀ σ v, rf (upd σ 0 v) = rf σ) : WFc (recCode r u rf) := by
  have hmot : Kinded [none, some (1, 0)] (motiveTy r u) :=
    ⟨kinded_var_nil rfl, (⟨kinded_var_nil rfl, wb_tok 1, wb_tok 0⟩ :
      Kinded [none, none, some (1, 0)] (DCode.eq r (.var 1 2 []) (wb 1) (wb 0))), trivial⟩
  have hm : Kinded [some (u, 2), none, some (1, 0)] (DCode.var u 0 [wb 1, rf]) := by
    refine ⟨rfl, fun t ht => ?_, fun σ v => ?_⟩
    · rcases mem_two ht with rfl | rfl
      · exact wb_tok 1
      · exact hrf
    · show [wb 1 (upd σ 0 v), rf (upd σ 0 v)] = [wb 1 σ, rf σ]
      rw [wb_upd (by decide) σ v, hfree]
  have hbody : Kinded [none, none, none, some (u, 2), none, some (1, 0)]
      (DCode.var u 3 [wb 1, wb 0]) := by
    refine ⟨rfl, fun t ht => ?_, fun σ v => ?_⟩
    · rcases mem_two ht with rfl | rfl
      · exact wb_tok 1
      · exact wb_tok 0
    · show [wb 1 (upd σ 3 v), wb 0 (upd σ 3 v)] = [wb 1 σ, wb 0 σ]
      rw [wb_upd (by decide) σ v, wb_upd (by decide) σ v]
  have hh : Kinded [none, none, some (u, 2), none, some (1, 0)]
      (DCode.eq r (.var 1 4 []) (wb 3) (wb 0)) := ⟨kinded_var_nil rfl, wb_tok 3, wb_tok 0⟩
  have hk : Kinded [] (recCode r u rf) :=
    ⟨trivial, kinded_var_nil rfl, hmot, hm, kinded_var_nil rfl, hh, hbody⟩
  have cmot : ClosedAt 2 (motiveTy r u) :=
    ⟨⟨by decide, by simp⟩, (⟨⟨by decide, by simp⟩, wb_closed (by decide), wb_closed (by decide)⟩ :
      ClosedAt 3 (DCode.eq r (.var 1 2 []) (wb 1) (wb 0))), trivial⟩
  have cm : ClosedAt 3 (DCode.var u 0 [wb 1, rf]) := by
    refine ⟨by decide, fun t ht => ?_⟩
    rcases mem_two ht with rfl | rfl
    · exact wb_closed (by decide)
    · exact hcl
  have cbody : ClosedAt 6 (DCode.var u 3 [wb 1, wb 0]) := by
    refine ⟨by decide, fun t ht => ?_⟩
    rcases mem_two ht with rfl | rfl
    · exact wb_closed (by decide)
    · exact wb_closed (by decide)
  have ch : ClosedAt 5 (DCode.eq r (.var 1 4 []) (wb 3) (wb 0)) :=
    ⟨⟨by decide, by simp⟩, wb_closed (by decide), wb_closed (by decide)⟩
  exact ⟨hk, trivial, ⟨Nat.zero_lt_one, by simp⟩, cmot, cm, ⟨by decide, by simp⟩, ch, cbody⟩

/-! ## The J Ty arm -/

/-- Introducing a product: the fibre at either related argument. -/
theorem el_pi_intro {σ : REnv} {ρ : FEnv} {a b : Nat} {A : DCode a} {B : DCode b} {f g : Value}
    (hf : f .bot) (hg : g .bot)
    (h : ∀ x y, El σ ρ A x y → ∀ F, SatFam F → Inv σ ρ A F F → ∀ z, (z = x ∨ z = y) →
      El (rcons z σ) (fcons F ρ) B (NeutralPi.applyValue f x) (NeutralPi.applyValue g y)) :
    El σ ρ (DCode.pi A B) f g :=
  ⟨hf, hg, fun x y hxy F hF hI => ⟨h x y hxy F hF hI x (Or.inl rfl), h x y hxy F hF hI y (Or.inr rfl)⟩⟩

/-- A family variable's reading moves along equal candidate relations. -/
theorem el_var_of_same {u i i' : Nat} {args args' : List TImg} {σ σ' : REnv} {ρ ρ' : FEnv}
    {x y : Value} (h : Same (ρ i (argVals args σ)) (ρ' i' (argVals args' σ')))
    (hxy : El σ ρ (DCode.var u i args) x y) : El σ' ρ' (DCode.var u i' args') x y := by
  cases u with
  | zero => exact ⟨(h x x).mp hxy.1, (h y y).mp hxy.2⟩
  | succ u => exact (h x y).mp hxy

theorem withBot_id {v : Value} (h : v .bot) : withBot v = v := CandidateSubstitution.withBot_eq h

theorem withBot_bot (v : Value) : withBot v .bot := Or.inl rfl

/-- A K-like operator: its six-fold application is its fourth argument, the
minor premise. -/
def KLikeOp (K : Value) : Prop :=
  K .bot ∧ ∀ xA xa xP xm xb xh : Value, xA .bot → xa .bot → xP .bot → xm .bot → xb .bot →
    xh .bot → IotaRecursor.applyAll K [xA, xa, xP, xm, xb, xh] = xm

/-- **The J Ty arm in the content model.** Every K-like operator realizes the
AnySort Eq recursor type, at every motive level `u`, for every Eq family `r`
and every refl image. The minor premise lives at `P a (refl A a)`; a proof
`h` of `Eq A a b` relates `a` and `b` in `A` (content), and the motive's
invariance moves the minor to `P b h`. -/
theorem rec_member (r u : Nat) (rf : TImg) (hrf : ∀ σ, rf σ .bot) {K : Value} (hK : KLikeOp K)
    (σ : REnv) (ρ : FEnv) (hs : SatEnv σ ρ) : El σ ρ (recCode r u rf) K K := by
  refine el_pi_intro hK.1 hK.1 (fun xA yA hA FA hFA _ zA hzA => ?_)
  have bA : xA .bot ∧ yA .bot := ⟨el_saturated σ ρ hs _ _ _ hA,
    el_saturated σ ρ hs _ _ _ ((el_laws _ σ ρ hs).symm hA)⟩
  have hzA : zA .bot := by rcases hzA with rfl | rfl; exact bA.1; exact bA.2
  have s1 := satEnv_rcons hs hzA hFA
  refine el_pi_intro (applyValue_bot _ _) (applyValue_bot _ _)
    (fun xa ya ha Fa hFa _ za hza => ?_)
  have ba : xa .bot ∧ ya .bot := ⟨el_saturated _ _ s1 _ _ _ ha,
    el_saturated _ _ s1 _ _ _ ((el_laws _ _ _ s1).symm ha)⟩
  have hza : za .bot := by rcases hza with rfl | rfl; exact ba.1; exact ba.2
  have s2 := satEnv_rcons s1 hza hFa
  refine el_pi_intro (applyValue_bot _ _) (applyValue_bot _ _)
    (fun xP yP hP FP hFP hIP zP hzP => ?_)
  have bP : xP .bot ∧ yP .bot := ⟨hP.1, hP.2.1⟩
  have hzP : zP .bot := by rcases hzP with rfl | rfl; exact bP.1; exact bP.2
  have s3 := satEnv_rcons s2 hzP hFP
  refine el_pi_intro (applyValue_bot _ _) (applyValue_bot _ _)
    (fun xm ym hm Fm hFm _ zm hzm => ?_)
  have bm : xm .bot ∧ ym .bot := ⟨el_saturated _ _ s3 _ _ _ hm,
    el_saturated _ _ s3 _ _ _ ((el_laws _ _ _ s3).symm hm)⟩
  have hzm : zm .bot := by rcases hzm with rfl | rfl; exact bm.1; exact bm.2
  have s4 := satEnv_rcons s3 hzm hFm
  refine el_pi_intro (applyValue_bot _ _) (applyValue_bot _ _)
    (fun xb yb hb Fb hFb _ zb hzb => ?_)
  have bb : xb .bot ∧ yb .bot := ⟨el_saturated _ _ s4 _ _ _ hb,
    el_saturated _ _ s4 _ _ _ ((el_laws _ _ _ s4).symm hb)⟩
  have hzb : zb .bot := by rcases hzb with rfl | rfl; exact bb.1; exact bb.2
  refine el_pi_intro (applyValue_bot _ _) (applyValue_bot _ _)
    (fun xh yh hh Fh hFh _ zh hzh => ?_)
  have bh : xh .bot ∧ yh .bot := ⟨hh.1, hh.2.1⟩
  have hzh : zh .bot := by rcases hzh with rfl | rfl; exact bh.1; exact bh.2
  -- the K-like computation
  show El _ _ _ (IotaRecursor.applyAll K [xA, xa, xP, xm, xb, xh])
    (IotaRecursor.applyAll K [yA, ya, yP, ym, yb, yh])
  rw [hK.2 _ _ _ _ _ _ bA.1 ba.1 bP.1 bm.1 bb.1 bh.1, hK.2 _ _ _ _ _ _ bA.2 ba.2 bP.2 bm.2 bb.2 bh.2]
  -- content of the Eq proof: `a` and `b` are related in `A`
  have hab : FA [] za zb := by
    have h3 := hh.2.2
    simp only [El, rcons, wb, fcons] at h3
    rw [withBot_id hza, withBot_id hzb] at h3
    exact h3
  -- the motive's invariance, at `(b, h)` and `(a, refl A a)`
  have hInv := hIP zb za ((hFA []).1.symm hab) (fun _ _ _ => False) emptyFam_sat trivial
    zh (rf (rcons zP (rcons za (rcons zA σ))))
    ⟨hzh, hrf _, by
      show FA [] (withBot za) (withBot zb)
      rw [withBot_id hza, withBot_id hzb]
      exact hab⟩
    (fun _ _ _ => False) emptyFam_sat trivial
  have hsame : Same (FP [za, rf (rcons zP (rcons za (rcons zA σ)))]) (FP [zb, zh]) :=
    fun x y => ((hInv x y).symm)
  refine el_var_of_same (args := [wb 1, rf]) (σ := rcons zP (rcons za (rcons zA σ)))
    (ρ := fcons FP (fcons Fa (fcons FA ρ))) (i := 0) ?_ hm
  show Same (FP [withBot za, rf _]) (FP [withBot zb, withBot zh])
  rw [withBot_id hza, withBot_id hzb, withBot_id hzh]
  exact hsame

end Rcic.Declarative.Ann.LR3.ContentJ
