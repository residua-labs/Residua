import rcic.RcicAnnLR3DecodedPi
import rcic.RcicAnnLR3FunctionSaturation
import rcic.RcicAnnLR3InductiveFamily

/-!
# Positive relational codes with native dependent products and a Nat base

The product constructor carries element relations as ordinary indices.
Its recursive code premises occur only positively. The codomain is a raw
closure value, and finite product observations retain its application on
finite demands. No dependent Descriptor constructor or selected fibre is
used. The old code fragment is retained under a separate constructor.
A fixed Nat family clause carries the represented legal-tree PER; its
fresh type tag is not identified with the current source constant image.
The general admitted-family constructor is not claimed by that base case.

The relation of all these codes is defined after the inductive relation.
An old universe clause is not silently identified with that enlarged
relation. Universe closure and full neutral reflection are separate
obligations; no source fundamental theorem is claimed. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveCodes

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

def imaxLevel (u v : Option Nat) : Option Nat :=
  eval (fun i => if i = 0 then u else v) (.imax (.param 0) (.param 1))

def taggedValue (k : Option Nat) (payload : Value) : Value := fun c =>
  c = .bot ∨ ∃ a p, c = .spine 10 [a, p] ∧
    (a = .bot ∨ a = .spine (levelRef k) []) ∧ payload p

def piPayload (A C : Value) : Value := fun c =>
  c = .bot ∨ ∃ a g, c = .pi a g ∧ A a ∧
    ∀ s ∈ g, NeutralPi.applyValue C (demand s.1) s.2

def piValue (k : Option Nat) (A C : Value) : Value :=
  taggedValue k (piPayload A C)

theorem imaxLevel_eval (ν : Valuation) (u v : Level) :
    imaxLevel (eval ν u) (eval ν v) = eval ν (.imax u v) := by
  simp [imaxLevel, eval]

theorem taggedValue_denI (ρ : EnvI) (k : Option Nat) (p : Expr Nat) :
    ValueEq (taggedValue k (denI ρ p)) (denI ρ (taggedTerm k p)) := by
  intro c
  constructor
  · rintro (hc | ⟨a, q, hc, ha, hp⟩)
    · subst c
      exact ApproxI.bot _ _
    · subst c
      refine approxI_famApp 10 [] (xs := [levelTerm k, p]) (.cons ?_ (.cons hp .nil))
      rcases ha with rfl | rfl
      · exact ApproxI.bot _ _
      · exact ApproxI.const _ _ _
  · intro hc
    rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm k, p]) hc with hb | ⟨us, hu, hs⟩
    · exact Or.inl hb
    · cases hs with
      | cons ha hs =>
        cases hs with
        | cons hp hs =>
          cases hs
          exact Or.inr ⟨_, _, hu, approxI_const_inv ha, hp⟩

theorem piPayload_native (ρ : EnvI) (A B : Expr Nat) :
    ValueEq (piPayload (denI ρ A) (denI ρ (.lam A B))) (denI ρ (.pi A B)) := by
  intro c
  constructor
  · rintro (hc | ⟨a, g, hc, ha, hg⟩)
    · subst c
      exact ApproxI.bot _ _
    · subst c
      exact ApproxI.pi ha (fun s hs =>
        (FunctionEval.native_lambda_application ρ A B (demand s.1) s.2).mp (hg s hs))
  · intro hc
    rcases approxI_pi_inv hc with hb | ⟨a, g, he, ha, hg⟩
    · exact Or.inl hb
    · exact Or.inr ⟨a, g, he, ha, fun s hs =>
        (FunctionEval.native_lambda_application ρ A B (demand s.1) s.2).mpr (hg s hs)⟩

theorem piValue_native (ρ : EnvI) (k : Option Nat) (A B : Expr Nat) :
    ValueEq (piValue k (denI ρ A) (denI ρ (.lam A B)))
      (denI ρ (taggedTerm k (.pi A B))) := by
  rw [piValue, NeutralCodes.valueEq_eq (piPayload_native ρ A B)]
  exact taggedValue_denI ρ k (.pi A B)

theorem piValue_annotated (ν : Valuation) (ρ : EnvI)
    (A B : ExprA) (u v : Level) :
    ValueEq
      (piValue (imaxLevel (eval ν u) (eval ν v)) (UnitModel.denote ν ρ A)
        (UnitModel.denote ν ρ (.lam A u B)))
      (UnitModel.denote ν ρ (.pi A u B v)) := by
  rw [imaxLevel_eval]
  exact piValue_native ρ _ (translate ν A) (translate ν B)

theorem taggedValue_full (k : Option Nat) (P : Value) (p : CptI) :
    taggedValue k P (NeutralCodes.fullTag k p) ↔ P p := by
  constructor
  · rintro (hbot | ⟨a, q, he, _, hp⟩)
    · cases hbot
    · have he' : .spine (levelRef k) [] = a ∧ p = q := by
        simpa [NeutralCodes.fullTag] using he
      rcases he' with ⟨rfl, rfl⟩
      exact hp
  · intro hp
    exact Or.inr ⟨.spine (levelRef k) [], p, rfl, Or.inr rfl, hp⟩

theorem piPayload_pi (A C : Value) (a : CptI) (g : NeutralPi.Graph) :
    piPayload A C (.pi a g) ↔
      A a ∧ ∀ s ∈ g, NeutralPi.applyValue C (demand s.1) s.2 := by
  constructor
  · rintro (hbot | ⟨b, f, he, ha, hf⟩)
    · cases hbot
    · cases he
      exact ⟨ha, hf⟩
  · rintro ⟨ha, hf⟩
    exact Or.inr ⟨a, g, rfl, ha, hf⟩

theorem piValue_full (k : Option Nat) (A C : Value)
    (a : CptI) (g : NeutralPi.Graph) :
    piValue k A C (NeutralCodes.fullTag k (.pi a g)) ↔
      A a ∧ ∀ s ∈ g, NeutralPi.applyValue C (demand s.1) s.2 :=
  (taggedValue_full k (piPayload A C) (.pi a g)).trans (piPayload_pi A C a g)

theorem piValue_level (k : Option Nat) (A C : Value) :
    SortMember k (piValue k A C) := by
  rintro c (rfl | ⟨a, p, rfl, ha, _⟩)
  · exact .bot
  · exact .tagged a p ha

theorem piValue_defined (k : Option Nat) (A C : Value) :
    TypeDefined (piValue k A C) :=
  ⟨k, .bot, (taggedValue_full k (piPayload A C) .bot).mpr (Or.inl rfl)⟩

theorem application_finite (C x : Value) (c : CptI) :
    NeutralPi.applyValue C x c ↔
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ NeutralPi.applyValue C (demand us) c := by
  constructor
  · rintro (hc | ⟨g, s, hc, hg, hs, ha⟩ | ⟨r, args, u, hc, hr, hu⟩)
    · exact ⟨[], by simp, Or.inl hc⟩
    · exact ⟨s.1, ha, Or.inr (Or.inl ⟨g, s, hc, hg, hs, fun _ h => h⟩)⟩
    · refine ⟨[u], ?_, Or.inr (Or.inr ⟨r, args, u, hc, hr, by simp [demand]⟩)⟩
      intro v hv
      obtain rfl := List.mem_singleton.mp hv
      exact hu
  · rintro ⟨us, hus, hc⟩
    exact NeutralPi.applyValue_mono (fun _ h => h) (fun u hu => hus u hu) c hc

theorem piValue_injective {k l : Option Nat} {A B C D : Value}
    (hA : A .bot) (hB : B .bot) (h : ValueEq (piValue k A C) (piValue l B D)) :
    k = l ∧ ValueEq A B ∧ ∀ x, ValueEq (NeutralPi.applyValue C x) (NeutralPi.applyValue D x) := by
  have hkl : k = l := sortMember_unique (piValue_level k A C)
    (sortMember_congr h.symm (piValue_level l B D)) (piValue_defined k A C)
  subst l
  have domains : ValueEq A B := by
    intro a
    simpa [piValue_full] using
      h (NeutralCodes.fullTag k (.pi a []))
  refine ⟨rfl, domains, ?_⟩
  have rows : ∀ us c, NeutralPi.applyValue C (demand us) c ↔
      NeutralPi.applyValue D (demand us) c := by
    intro us c
    simpa only [piValue_full, List.mem_singleton, forall_eq, hA, hB, true_and] using
      h (NeutralCodes.fullTag k (.pi .bot [(us, c)]))
  intro x c
  rw [application_finite, application_finite]
  constructor
  · rintro ⟨us, hus, hc⟩
    exact ⟨us, hus, (rows us c).mp hc⟩
  · rintro ⟨us, hus, hc⟩
    exact ⟨us, hus, (rows us c).mpr hc⟩

theorem reify_not_pi_observation (d : NeutralCodes.Descriptor) (k : Option Nat)
    (a : CptI) (g : NeutralPi.Graph) :
    ¬ NeutralCodes.reify d (NeutralCodes.fullTag k (.pi a g)) := by
  cases d with
  | neutralType l name => simp [NeutralCodes.reify, NeutralCodes.neutralTypeValue,
      NeutralCodes.fullTag, NeutralCodes.neutralPayload]
  | proof P => simp [NeutralCodes.reify, NeutralCodes.proofCodeValue, NeutralCodes.fullTag]
  | univ j =>
    intro h
    rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm (j.map Nat.succ), .app (.const 11 []) (levelTerm j)]) h
      with hb | ⟨us, hu, hs⟩
    · cases hb
    · cases hs with
      | cons ha hs =>
        cases hs with
        | cons hp hs =>
          cases hs
          cases hu
          rcases approxI_foldApps_const_inv (r := 11) (ls := [])
            (xs := [levelTerm j]) hp with hb | ⟨vs, hv, _⟩
          · cases hb
          · cases hv

theorem old_code_bot {k : Option Nat} {V : Value} {R : Relation}
    (h : NeutralCodes.Code k V R) : V .bot := by
  obtain ⟨d, _, hv, _⟩ := h
  apply (hv .bot).mpr
  cases d with
  | neutralType k name => exact Or.inl rfl
  | proof P => exact Or.inl rfl
  | univ k => exact ApproxI.bot _ _

theorem old_code_not_pi {k l : Option Nat} {V A C : Value} {R : Relation}
    (h : NeutralCodes.Code k V R) (hA : A .bot) : ¬ ValueEq V (piValue l A C) := by
  obtain ⟨d, _, hv, _⟩ := h
  intro he
  apply reify_not_pi_observation d l .bot []
  exact (hv _).mp ((he _).mpr ((piValue_full l A C .bot []).mpr ⟨hA, by simp⟩))

theorem old_code_not_nat {k : Option Nat} {V : Value} {R : Relation}
    (h : NeutralCodes.Code k V R) : ¬ ValueEq V InductiveFamily.NatCode.typeValue := by
  obtain ⟨d, _, hv, _⟩ := h
  intro he
  exact InductiveFamily.NatCode.typeValue_not_old d (he.symm.trans hv)

theorem nat_not_pi (k : Option Nat) (A C : Value) (hA : A .bot) :
    ¬ ValueEq InductiveFamily.NatCode.typeValue (piValue k A C) := by
  intro he
  have ho := (he (NeutralCodes.fullTag k (.pi .bot []))).mpr
    ((piValue_full k A C .bot []).mpr ⟨hA, by simp⟩)
  simp [InductiveFamily.NatCode.typeValue, NeutralCodes.fullTag] at ho

theorem nat_saturated : FunctionSaturation.Saturated InductiveFamily.NatCode.PER := by
  intro x hx
  rw [NeutralCodes.valueEq_eq (FunctionSaturation.withBottom_eq_of_bot
    (InductiveFamily.NatCode.per_member_bot hx))]
  exact hx

/-- All occurrences of CodeI in constructor premises are positive.
The fibres RB are indices, not extracted data or recursively decoded fields. -/
inductive CodeI : Option Nat → Value → Relation → Prop
  | old {k : Option Nat} {V : Value} {R : Relation}
      (h : NeutralCodes.Code k V R) : CodeI k V R
  | nat {V : Value} {R : Relation}
      (value : ValueEq V InductiveFamily.NatCode.typeValue)
      (carrier : Same R InductiveFamily.NatCode.PER) : CodeI (some 1) V R
  | pi {kA kB : Option Nat} {A C V : Value} {RA R : Relation} {RB : Value → Relation}
      (domain : CodeI kA A RA)
      (fibres : ∀ x y, RA x y → CodeI kB (NeutralPi.applyValue C x) (RB x))
      (coherent : FamilyCoherent RA RB)
      (value : ValueEq V (piValue (imaxLevel kA kB) A C))
      (carrier : Same R (FunctionPER NeutralPi.applyValue RA RB)) :
      CodeI (imaxLevel kA kB) V R

theorem code_laws {k : Option Nat} {V : Value} {R : Relation} (h : CodeI k V R) : Laws R := by
  induction h with
  | old h => exact NeutralCodes.code_lawful h
  | nat hv hr =>
    exact ⟨fun hxy => (hr _ _).mpr (InductiveFamily.NatCode.per_laws.symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr (InductiveFamily.NatCode.per_laws.trans
        ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩
  | pi hA hB hc hv hr ihA ihB =>
    have hf := functionPER_laws NeutralPi.applyValue ihA (fun x hx => ihB x x hx) hc
    exact ⟨fun hxy => (hr _ _).mpr (hf.symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr (hf.trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩

theorem code_level {k : Option Nat} {V : Value} {R : Relation} (h : CodeI k V R) :
    SortMember k V := by
  cases h with
  | old h => exact NeutralCodes.code_level h
  | nat hv hr => exact sortMember_congr hv.symm InductiveFamily.NatCode.typeValue_level
  | pi hA hB hc hv hr => exact sortMember_congr hv.symm (piValue_level _ _ _)

theorem code_defined {k : Option Nat} {V : Value} {R : Relation} (h : CodeI k V R) :
    TypeDefined V := by
  cases h with
  | old h => exact NeutralCodes.code_defined h
  | nat hv hr => exact typeDefined_congr hv.symm InductiveFamily.NatCode.typeValue_defined
  | pi hA hB hc hv hr => exact typeDefined_congr hv.symm (piValue_defined _ _ _)

theorem code_bot {k : Option Nat} {V : Value} {R : Relation} (h : CodeI k V R) : V .bot := by
  cases h with
  | old h => exact old_code_bot h
  | nat hv hr => exact (hv .bot).mpr (Or.inl rfl)
  | pi hA hB hc hv hr => exact (hv .bot).mpr (Or.inl rfl)

theorem code_saturated {k : Option Nat} {V : Value} {R : Relation} (h : CodeI k V R) :
    FunctionSaturation.Saturated R := by
  cases h with
  | old h => exact FunctionSaturation.code_saturated h
  | nat hv hr =>
    exact FunctionSaturation.saturated_of_same
      (fun x y => (hr x y).symm) nat_saturated
  | pi hA hB hc hv hr =>
    exact FunctionSaturation.saturated_of_same (fun x y => (hr x y).symm)
      (FunctionSaturation.functionPER_saturated _ _)

theorem functionPER_same {D E : Relation} {C F : Value → Relation}
    (hD : Laws D) (hDE : Same D E)
    (hCF : ∀ x, Member D x → Same (C x) (F x)) :
    Same (FunctionPER NeutralPi.applyValue D C) (FunctionPER NeutralPi.applyValue E F) := by
  intro f g
  constructor
  · intro h x y hxy
    have hxy' := (hDE x y).mpr hxy
    exact (hCF x (left_member hD hxy') _ _).mp (h x y hxy')
  · intro h x y hxy
    exact (hCF x (left_member hD hxy) _ _).mpr (h x y ((hDE x y).mp hxy))

theorem code_coherent_values {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeI k V R) : ∀ {l : Option Nat} {W : Value} {S : Relation},
      CodeI l W S → ValueEq V W → Same R S := by
  induction h with
  | old h =>
    intro l W S g he
    cases g with
    | old g =>
      have g' : NeutralCodes.Code l _ S := g
      rw [← NeutralCodes.valueEq_eq he] at g'
      exact NeutralCodes.code_coherent h g'
    | pi hA hB hc hv hr =>
      exact (old_code_not_pi h (code_bot hA) (he.trans hv)).elim
    | nat hv hr => exact (old_code_not_nat h (he.trans hv)).elim
  | nat hv hr =>
    intro l W S g he
    cases g with
    | old g => exact (old_code_not_nat g (he.symm.trans hv)).elim
    | nat hv' hr' => exact fun x y => (hr x y).trans (hr' x y).symm
    | pi hA hB hc hv' hr' =>
      exact (nat_not_pi _ _ _ (code_bot hA) (hv.symm.trans (he.trans hv'))).elim
  | @pi kA kB A C V RA R RB hA hB hc hv hr ihA ihB =>
    intro l W S g he
    cases g with
    | old g =>
      exact (old_code_not_pi g (code_bot hA) (he.symm.trans hv)).elim
    | nat hv' hr' =>
      exact (nat_not_pi _ _ _ (code_bot hA) (hv'.symm.trans (he.symm.trans hv))).elim
    | @pi kA' kB' A' C' W RA' S RB' hA' hB' hc' hv' hr' =>
      obtain ⟨_, heA, heC⟩ := piValue_injective (code_bot hA) (code_bot hA')
        (hv.symm.trans (he.trans hv'))
      have hRA : Same RA RA' := ihA hA' heA
      have hRB : ∀ x, Member RA x → Same (RB x) (RB' x) := by
        intro x hx
        exact ihB x x hx (hB' x x ((hRA x x).mp hx)) (heC x)
      have hF := functionPER_same (code_laws hA) hRA hRB
      exact fun f g => (hr f g).trans ((hF f g).trans (hr' f g).symm)

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : CodeI k V R) (g : CodeI l V S) : Same R S :=
  code_coherent_values h g (ValueEq.refl V)

theorem code_value_eq {k : Option Nat} {V W : Value} {R : Relation}
    (h : CodeI k V R) (he : ValueEq V W) : CodeI k W R := by
  rw [← NeutralCodes.valueEq_eq he]
  exact h

theorem code_same {k : Option Nat} {V : Value} {R S : Relation}
    (h : CodeI k V R) (he : Same R S) : CodeI k V S := by
  cases h with
  | old h =>
    obtain ⟨d, hd, hv, hr⟩ := h
    exact .old ⟨d, hd, hv, fun x y => (he x y).symm.trans (hr x y)⟩
  | nat hv hr => exact .nat hv (fun x y => (he x y).symm.trans (hr x y))
  | pi hA hB hc hv hr =>
    exact .pi hA hB hc hv (fun x y => (he x y).symm.trans (hr x y))

/-- Inversion retains the actual domain and closure. It does not choose
an element relation for use as data. -/
theorem code_pi_view {k l : Option Nat} {A C : Value} {R : Relation}
    (hA : A .bot) (h : CodeI k (piValue l A C) R) :
    ∃ kA kB RA RB, CodeI kA A RA ∧
      (∀ x y, RA x y → CodeI kB (NeutralPi.applyValue C x) (RB x)) ∧
      FamilyCoherent RA RB ∧ Same R (FunctionPER NeutralPi.applyValue RA RB) := by
  cases h with
  | old h => exact (old_code_not_pi h hA (ValueEq.refl _)).elim
  | nat hv hr => exact (nat_not_pi _ _ _ hA hv.symm).elim
  | pi hD hB hc hv hr =>
    obtain ⟨_, hd, hb⟩ := piValue_injective hA (code_bot hD) hv
    exact ⟨_, _, _, _, code_value_eq hD hd.symm,
      fun x y hxy => code_value_eq (hB x y hxy) (hb x).symm, hc, hr⟩

theorem denote_pi_view {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level}
    {k : Option Nat} {R : Relation}
    (h : CodeI k (UnitModel.denote ν ρ (.pi A u B v)) R) :
    ∃ kA kB RA RB, CodeI kA (UnitModel.denote ν ρ A) RA ∧
      (∀ x y, RA x y → CodeI kB (UnitModel.denote ν (EnvI.cons x ρ) B) (RB x)) ∧
      FamilyCoherent RA RB ∧ Same R (FunctionPER NeutralPi.applyValue RA RB) := by
  obtain ⟨kA, kB, RA, RB, hA, hB, hc, hr⟩ := code_pi_view (ApproxI.bot _ _)
    (code_value_eq h (piValue_annotated ν ρ A B u v).symm)
  exact ⟨kA, kB, RA, RB, hA, fun x y hxy => code_value_eq (hB x y hxy)
    (FunctionEval.denote_lambda_application ν ρ A B u x), hc, hr⟩

/-- Decoding remains a Prop-valued union of coherent presentations. -/
def decodedEl (k : Option Nat) (V : Value) : Relation := fun x y =>
  ∃ R, CodeI k V R ∧ R x y

theorem decodedEl_same {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeI k V R) : Same (decodedEl k V) R := by
  intro x y
  constructor
  · rintro ⟨S, hS, hxy⟩
    exact (code_coherent hS h x y).mp hxy
  · intro hxy
    exact ⟨R, h, hxy⟩

theorem decodedEl_code {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeI k V R) : CodeI k V (decodedEl k V) :=
  code_same h (fun x y => (decodedEl_same h x y).symm)

theorem decodedEl_laws (k : Option Nat) (V : Value) : Laws (decodedEl k V) where
  symm := by
    rintro x y ⟨R, hR, hxy⟩
    exact ⟨R, hR, (code_laws hR).symm hxy⟩
  trans := by
    rintro x y z ⟨R, hR, hxy⟩ ⟨S, hS, hyz⟩
    exact ⟨R, hR, (code_laws hR).trans hxy ((code_coherent hS hR y z).mp hyz)⟩

theorem nat_code : CodeI (some 1) InductiveFamily.NatCode.typeValue
    InductiveFamily.NatCode.PER := .nat (ValueEq.refl _) (fun _ _ => Iff.rfl)

theorem nat_reflected_member (name : Nat) :
    Member (decodedEl (some 1) InductiveFamily.NatCode.typeValue)
      (InductiveFamily.NatCode.leafValue () name) :=
  ⟨_, nat_code, InductiveFamily.NatCode.reflect_member name⟩

/-- Exact conservative extension at every old type value. This does not
identify the old universe carrier with the relation of all new codes. -/
theorem old_fragment_iff {k : Option Nat} {V : Value} {R S : Relation}
    (hS : NeutralCodes.Code k V S) : CodeI k V R ↔ NeutralCodes.Code k V R := by
  constructor
  · intro h
    have hRS := code_coherent h (.old hS)
    obtain ⟨d, hd, hv, hs⟩ := hS
    exact ⟨d, hd, hv, fun x y => (hRS x y).trans (hs x y)⟩
  · exact CodeI.old

/-- Related type images have explicitly related element-PER indices.
This is the enlarged universe relation, defined after CodeI. -/
def UniverseI (k : Option Nat) (V W : Value) : Prop :=
  ∃ R S, CodeI k V R ∧ CodeI k W S ∧ Same R S

theorem universeI_laws (k : Option Nat) : Laws (UniverseI k) where
  symm := by
    rintro V W ⟨R, S, hR, hS, hRS⟩
    exact ⟨S, R, hS, hR, fun x y => (hRS x y).symm⟩
  trans := by
    rintro V W X ⟨R, S, hR, hS, hRS⟩ ⟨T, U, hT, hU, hTU⟩
    have hST := code_coherent hS hT
    exact ⟨R, U, hR, hU, fun x y =>
      (hRS x y).trans ((hST x y).trans (hTU x y))⟩

theorem code_member_universeI {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeI k V R) : Member (UniverseI k) V :=
  ⟨R, R, h, h, fun _ _ => Iff.rfl⟩

theorem universeI_decode {k : Option Nat} {V : Value}
    (h : Member (UniverseI k) V) : ∃ R, CodeI k V R := by
  obtain ⟨R, _, hR, _, _⟩ := h
  exact ⟨R, hR⟩

theorem universeI_el_transport {k l m : Option Nat} {V W : Value} {R S : Relation}
    (hR : CodeI l V R) (hS : CodeI m W S) (h : UniverseI k V W) : Same R S := by
  obtain ⟨T, U, hT, hU, hTU⟩ := h
  exact fun x y => (code_coherent hR hT x y).trans
    ((hTU x y).trans (code_coherent hU hS x y))

/-- This algebra retains the old universe carriers. Its exact source Π
formation obstruction is tested separately; it is not the full producer. -/
def legacyUniverseSystem : CodeSystem where
  Code := CodeI
  universePER := NeutralCodes.UniversePER
  lawful := code_laws
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := fun k => .old (NeutralCodes.code_universe k)
  universe_member := NeutralCodes.universe_member
  universe_elim := by
    intro k l R x h hx
    have hR := code_coherent h (.old (NeutralCodes.code_universe k))
    exact NeutralCodes.universe_elim (NeutralCodes.code_universe k) ((hR x x).mp hx)

def legacyUniverseTransport : PairedStatements.UniverseTransport legacyUniverseSystem where
  relate := by
    intro k V W h
    obtain ⟨R, S, hR, hS, hRS⟩ := NeutralCodes.universe_transport h
    exact ⟨R, S, ⟨CodeI.old hR, CodeI.old hS, hRS⟩⟩

end Rcic.Declarative.Ann.LR3.InductiveCodes
