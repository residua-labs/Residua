import rcic.RcicF3PiSmallCompile

/-!
# Small choices for finite dependent telescopes

The choice space lives at the exact selected small universe. It reads each
successive domain at the actual preceding decoded values. Conditional small
representatives make the construction total; completeness uses the literal
SmallAlong witness of the tuple being represented, not global soundness.

This is the ordinary-field enumeration component of a data signature. It
does not delete recursive values from later environments, prove non-IR from
admission, or make constructor result indices independent of those values.
The four W4 wrappers retain stages 1, 2, 3 and k+4 separately.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiSmallTuple

open Rcic.Declarative
universe u v

/-- The fallback has no completeness claim outside the small domain. -/
noncomputable def rep (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (D : PSet.{max (u+1) v}) : PSet.{u} :=
  @dite _ (Small.{u,max (u+1) v} D) (M.dec _)
    (fun h => smallRep.{u,max (u+1) v} ch D h) (fun _ => pempty)

theorem rep_spec (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (D : PSet.{max (u+1) v}) (hD : Small.{u,max (u+1) v} D) :
    Equiv D (lift.{u,max (u+1) v} (rep M ch D)) := by
  unfold rep
  rw [dif_pos hD]
  exact smallRep_spec.{u,max (u+1) v} ch D hD

/-- Only small branch addresses are stored. The tail remains fully
dependent on the preceding address's large decoded value. -/
noncomputable def Space (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : (Ds : List (Expr Nat)) → (Nat → PSet.{max (u+1) v}) → Type u
  | [], _ => ULift.{u} Unit
  | A :: Ds, ρ =>
      (q : FBr (rep M ch (Ed M (den M σ ρ A)))) ×
        Space M ch σ Ds
          (vcons (lift.{u,max (u+1) v} (PiCompile.classValue _ q)) ρ)

noncomputable def values (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{max (u+1) v}) →
      Space M ch σ Ds ρ → List PSet.{max (u+1) v}
  | [], _, _ => []
  | A :: Ds, ρ, s =>
      lift.{u,max (u+1) v} (PiCompile.classValue (rep M ch (Ed M (den M σ ρ A))) s.1) ::
        values M ch σ Ds
          (vcons (lift.{u,max (u+1) v} (PiCompile.classValue _ s.1)) ρ) s.2

theorem values_length (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ Ds ρ (s : Space M ch σ Ds ρ),
      (values M ch σ Ds ρ s).length = Ds.length
  | [], _, _ => rfl
  | _ :: Ds, _, s => congrArg Nat.succ (values_length M ch σ Ds _ s.2)

/-- A populated representative cannot have come from the empty fallback. -/
theorem small_of_rep_mem (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (D : PSet.{max (u+1) v}) (q : FBr (rep M ch D)) :
    Small.{u,max (u+1) v} D := by
  cases hd : M.dec (Small.{u,max (u+1) v} D) with
  | isTrue h => exact h
  | isFalse h =>
      have hex : ∃ z : PSet.{u}, z ∈ rep M ch D :=
        ⟨_, PiCompile.classValue_mem _ q⟩
      unfold rep at hex
      rw [dif_neg h] at hex
      obtain ⟨z, hz⟩ := hex
      exact (not_mem_pempty hz).elim

/-- Every address decodes to a fitting tuple with the literal selected
smallness bound. The fallback creates no spurious tuple. -/
theorem sound (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ Ds ρ (s : Space M ch σ Ds ρ),
      TelFits M σ Ds ρ (values M ch σ Ds ρ s) ∧
      SmallAlong M σ (univIn.{u,v}) Ds ρ (values M ch σ Ds ρ s)
  | [], _, _ => ⟨True.intro, True.intro⟩
  | A :: Ds, ρ, s => by
      let D := Ed M (den M σ ρ A)
      have hD : Small.{u,max (u+1) v} D := small_of_rep_mem M ch D s.1
      have hx : lift.{u,max (u+1) v} (PiCompile.classValue (rep M ch D) s.1) ∈ D :=
        mem_congr_right (rep_spec M ch D hD).symm
          (lift_mem_lift.{u,max (u+1) v}.mpr (PiCompile.classValue_mem _ s.1))
      obtain ⟨ht, hs⟩ := sound M ch σ Ds _ s.2
      exact ⟨⟨hx, ht⟩, mem_univIn.{u,v}.mpr hD, hs⟩

/-- Completeness is local to the supplied fitting tuple and its exact
domain-size witnesses. No choices of arbitrary quotient keys are made. -/
theorem complete_congr (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ (Ds : List (Expr Nat))
      (ρ ρ' : Nat → PSet.{max (u+1) v}) (xs : List PSet.{max (u+1) v}),
      (∀ k, Equiv (ρ k) (ρ' k)) → TelFits M σ Ds ρ xs →
      SmallAlong M σ (univIn.{u,v}) Ds ρ xs →
      ∃ s : Space M ch σ Ds ρ', LEq xs (values M ch σ Ds ρ' s)
  | [], _, _, [], _, _, _ => ⟨⟨()⟩, True.intro⟩
  | [], _, _, _ :: _, _, h, _ => False.elim h
  | _ :: _, _, _, [], _, h, _ => False.elim h
  | A :: Ds, ρ, ρ', x :: xs, hρ, hx, hs => by
      let D := Ed M (den M σ ρ' A)
      let S := rep M ch D
      have hden : Equiv (Ed M (den M σ ρ A)) D :=
        ed_congr M (den_congr M σ A hρ)
      have hD : Small.{u,max (u+1) v} D :=
        mem_univIn.{u,v}.mp (mem_congr_left hden hs.1)
      have hxD : x ∈ D := mem_congr_right hden hx.1
      have hxS : x ∈ lift.{u,max (u+1) v} S :=
        mem_congr_right (rep_spec M ch D hD) hxD
      obtain ⟨y, ⟨a, ha⟩, hy⟩ := mem_lift.{u,max (u+1) v}.mp hxS
      let q : FBr S := Quotient.mk (FSetoid S) a
      let x' : PSet.{max (u+1) v} := lift.{u,max (u+1) v} (PiCompile.classValue S q)
      have he : Equiv x x' := hy.trans
        ((lift_equiv.{u,max (u+1) v} ha).symm.trans
          (lift_equiv.{u,max (u+1) v} (PiCompile.classValue_at S a)).symm)
      obtain ⟨tail, ht⟩ := complete_congr M ch σ Ds
        (vcons x ρ) (vcons x' ρ') xs (vcons_congr he hρ) hx.2 hs.2
      exact ⟨⟨q, tail⟩, he, ht⟩

theorem complete (M : Interp.{max (u+1) v}) (ch : Choice.{u}) (σ : Nat → Nat)
    (Ds : List (Expr Nat)) (ρ : Nat → PSet.{max (u+1) v})
    (xs : List PSet.{max (u+1) v}) (hx : TelFits M σ Ds ρ xs)
    (hs : SmallAlong M σ (univIn.{u,v}) Ds ρ xs) :
    ∃ s : Space M ch σ Ds ρ, LEq xs (values M ch σ Ds ρ s) :=
  complete_congr M ch σ Ds ρ ρ xs (fun _ => Equiv.rfl) hx hs

/-- Decoding preserves the complete dependent tuple and all result
expressions, rather than only a tuple's length or an erased index. -/
theorem complete_with_result (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (Ds result : List (Expr Nat))
    (ρ : Nat → PSet.{max (u+1) v}) (xs : List PSet.{max (u+1) v})
    (hx : TelFits M σ Ds ρ xs)
    (hs : SmallAlong M σ (univIn.{u,v}) Ds ρ xs) :
    ∃ s : Space M ch σ Ds ρ,
      LEq xs (values M ch σ Ds ρ s) ∧
      TelFits M σ Ds ρ (values M ch σ Ds ρ s) ∧
      LEq (result.map (den M σ (push xs ρ)))
        (result.map (den M σ (push (values M ch σ Ds ρ s) ρ))) := by
  obtain ⟨s, he⟩ := complete M ch σ Ds ρ xs hx hs
  exact ⟨s, he, TelFits_congr M σ Ds (fun _ => Equiv.rfl) he hx,
    LEq_map_den M σ (push_congr he (fun _ => Equiv.rfl)) result⟩

/-- Exact result stage one uses Choice0 and a Type0 choice space. -/
theorem complete_stage_one (P : Premises4) (M : Interp.{4}) (σ : Nat → Nat)
    (Ds : List (Expr Nat)) (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hx : TelFits M σ Ds ρ xs) (hs : SmallAlong M σ (W4 1) Ds ρ xs) :
    ∃ s : Space.{0,4} M P.c0 σ Ds ρ,
      LEq xs (values M P.c0 σ Ds ρ s) :=
  complete M P.c0 σ Ds ρ xs hx hs

/-- Exact result stage two uses Choice1 and a Type1 choice space. -/
theorem complete_stage_two (P : Premises4) (M : Interp.{4}) (σ : Nat → Nat)
    (Ds : List (Expr Nat)) (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hx : TelFits M σ Ds ρ xs) (hs : SmallAlong M σ (W4 2) Ds ρ xs) :
    ∃ s : Space.{1,4} M P.c1 σ Ds ρ,
      LEq xs (values M P.c1 σ Ds ρ s) :=
  complete M P.c1 σ Ds ρ xs hx hs

/-- Exact result stage three uses Choice2 and a Type2 choice space. -/
theorem complete_stage_three (P : Premises4) (M : Interp.{4}) (σ : Nat → Nat)
    (Ds : List (Expr Nat)) (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hx : TelFits M σ Ds ρ xs) (hs : SmallAlong M σ (W4 3) Ds ρ xs) :
    ∃ s : Space.{2,4} M P.c2 σ Ds ρ,
      LEq xs (values M P.c2 σ Ds ρ s) :=
  complete M P.c2 σ Ds ρ xs hx hs

/-- A saturated result stage uses Choice3. Its literal stage remains k+4. -/
theorem complete_stage_four_plus (P : Premises4) (M : Interp.{4})
    (σ : Nat → Nat) (k : Nat) (Ds : List (Expr Nat))
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hx : TelFits M σ Ds ρ xs) (hs : SmallAlong M σ (W4 (k + 4)) Ds ρ xs) :
    ∃ s : Space.{3,4} M P.c3 σ Ds ρ,
      LEq xs (values M P.c3 σ Ds ρ s) :=
  complete M P.c3 σ Ds ρ xs hx hs

end Rcic.F3.PSet.PiSmallTuple
