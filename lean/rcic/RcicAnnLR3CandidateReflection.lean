import rcic.RcicAnnLR3CandidateSubstitution
import rcic.RcicAnnLR3NeutralExtraction
import rcic.RcicAnnLR3EnvironmentPi
import rcic.RcicAnnLR3SemanticMemberAdmissionReadback

/-!
# CR3 for the open Girard system, and its `NeutralSupport`

In the open system (`El = ElA SatFor`), a candidate for a bound variable
contains the reflections of its two raw arguments. Reflection is the
observation-directed `ObservationReflection.reflV`.

**CR3** (`el_reflect`). For every kinded code, in a saturated environment
whose type-variable candidates are coupled to their raw entries, the
reflections of any two reflectable neutrals at the code's two raw images are
related. The cases follow the reflection laws: at a universe both
reflections are the image of the closed code `neutral k 13`, at a neutral
type they are the neutrals themselves (neutral types relate all neutrals),
and products go through `refl_pi` and the codomain at the extended
environment.

**`NeutralSupport`** (`neutralSupport`). For every environment `E` and family
syntax `H`, the open code system `codeSystem` has the `NeutralSupport` of
`EnvironmentEval.annSemantics codeSystem E H`. Decoding reads a universe
member as a closed kinded code. Reflection is `reflV V (atom (a + 12))`. At
finite levels membership is CR3. At the none level, a reflected universe
element is the named none-ordinary type `13`.

Contrast `EqTracer.girard_no_neutralSupport`: the closed system (plain
saturated candidates, `codeSystemS`) has an empty code and so has no
`NeutralSupport`. `neutralSupport_target` is the instance at the skeleton's
Target shape `annSemantics codeSystem (view E) (hook hE F)`. Consistency of the open system is a statement about closed
realizers. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateReflection

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot Head11Free)
open CandidateTowerProbe CandidateTowerCoherence CandidateCodeSystem CandidateSubstitution
open ObservationReflection

theorem head11Free_app {n : Value} (h : Head11Free n) (hn : CandidatePi.Neutral n) (x : Value) :
    Head11Free (NeutralPi.applyValue n x) := by
  intro args hc
  rcases hc with hb | ⟨g, _, _, hf, _, _⟩ | ⟨r, as, u, hc, hf, _⟩
  · cases hb
  · rcases CandidatePi.neutral_spineOnly hn _ hf with h' | ⟨_, _, h'⟩ <;> cases h'
  · have hr : 11 = r := (CptI.spine.inj hc).1
    subst hr
    exact h as hf

theorem ntr_app {n : Value} (hn : Ntr n) {x : Value} (hx : x .bot) :
    Ntr (NeutralPi.applyValue n x) :=
  ⟨.app hn.1 x ⟨_, hx⟩, head11Free_app hn.2 hn.1 x⟩

theorem atom_head11Free {name : Nat} (h : name ≠ 11) : Head11Free (NeutralPER.neutralAtom name) := by
  intro args hc
  rcases approxI_const_inv hc with h' | h'
  · cases h'
  · exact h (CptI.spine.inj h').1.symm

theorem ntr_atom {name : Nat} (h : name ≠ 11) : Ntr (NeutralPER.neutralAtom name) :=
  ⟨.atom name, atom_head11Free h⟩

theorem atom_bot (name : Nat) : NeutralPER.neutralAtom name .bot := .bot _ _

theorem neutral_image (σ : REnv) (k name : Nat) :
    image σ (GCode.neutral k name) =
      InductiveCodes.taggedValue (some k) (withBot (NeutralPER.neutralAtom name)) := by
  rw [withBot_eq (atom_bot name)]
  exact NeutralCodes.valueEq_eq (TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.neutral k name))

theorem image_bot_any {k : Nat} (σ : REnv) : (c : GCode k) → image σ c .bot
  | .var _ _ => Or.inl rfl
  | .univ _ => .bot _ _
  | .neutral _ _ => NativeMemberValues.value_bot _ _
  | .pi _ _ => Or.inl rfl

/-- CR3: reflections are related at every kinded code. -/
theorem el_reflect : {k : Nat} → (c : GCode k) → ∀ (κ : List (Option Nat)) (σ σ' : REnv)
    (ρ : CEnv), Kinded κ c → SatEnv σ ρ → (∀ i, σ' i .bot) →
    (∀ i j, κ[i]? = some (some j) → SatFor (σ i) (σ' i) (ρ i)) →
    ∀ n m, Ntr n → Ntr m → El σ ρ c (reflV (image σ c) n) (reflV (image σ' c) m)
  | _, .var 0 i, _, σ, σ', ρ, hc, hS, hσ', hcp, n, m, hn, hm => by
      obtain ⟨hs, hR⟩ := hcp i 0 hc
      show ρ i (reflV (withBot (σ i)) n) (reflV (withBot (σ i)) n) ∧
        ρ i (reflV (withBot (σ' i)) m) (reflV (withBot (σ' i)) m)
      rw [withBot_eq (hS.2 i), withBot_eq (hσ' i)]
      exact ⟨hs.1.trans (hR n m hn hm) (hs.1.symm (hR n m hn hm)),
        hs.1.trans (hs.1.symm (hR n m hn hm)) (hR n m hn hm)⟩
  | _, .var (j + 1) i, _, σ, σ', ρ, hc, hS, hσ', hcp, n, m, hn, hm => by
      obtain ⟨_, hR⟩ := hcp i (j + 1) hc
      show ρ i (reflV (withBot (σ i)) n) (reflV (withBot (σ' i)) m)
      rw [withBot_eq (hS.2 i), withBot_eq (hσ' i)]
      exact hR n m hn hm
  | _, .univ k, _, _, _, _, _, _, _, _, n, m, _, _ =>
      ⟨GCode.neutral k 13, (by decide : (13 : Nat) ≠ 11), refl_universe (some k) n,
        refl_universe (some k) m⟩
  | _, .neutral k name, _, σ, σ', _, hc, _, _, _, n, m, hn, hm => by
      show CandidatePi.Neutral (reflV (image σ (GCode.neutral k name)) n) ∧
        CandidatePi.Neutral (reflV (image σ' (GCode.neutral k name)) m)
      rw [neutral_image, neutral_image]
      exact ⟨CandidatePi.neutral_congr (refl_ntype k (.atom name) (atom_head11Free hc) hn.1).symm hn.1,
        CandidatePi.neutral_congr (refl_ntype k (.atom name) (atom_head11Free hc) hm.1).symm hm.1⟩
  | _, @GCode.pi a b A B, κ, σ, σ', ρ, hc, hS, hσ', hcp, n, m, hn, hm => by
      refine ⟨.bot _ _, .bot _ _, fun x y hxy R hR => ?_⟩
      have hx : x .bot := el_saturated σ ρ hS A x y hxy
      have hy : y .bot := el_saturated σ ρ hS A y x ((el_laws_open satFor_laws A σ ρ hS).symm hxy)
      have e1 : NeutralPi.applyValue (reflV (image σ (GCode.pi A B)) n) x =
          reflV (image (rcons x σ) B) (NeutralPi.applyValue n x) :=
        NeutralCodes.valueEq_eq (refl_pi (k := some (imaxN a b)) (A := image σ A)
          (F := fun x => image (rcons x σ) B) (image_bot σ hS.2 A) (codomain_finite B σ)
          (fun z => image_bot_any (rcons z σ) B) n x)
      have e2 : NeutralPi.applyValue (reflV (image σ' (GCode.pi A B)) m) y =
          reflV (image (rcons y σ') B) (NeutralPi.applyValue m y) :=
        NeutralCodes.valueEq_eq (refl_pi (k := some (imaxN a b)) (A := image σ' A)
          (F := fun x => image (rcons x σ') B) (image_bot σ' hσ' A) (codomain_finite B σ')
          (fun z => image_bot_any (rcons z σ') B) m y)
      have ih := el_reflect B (kindOfCode A :: κ) (rcons x σ) (rcons y σ') (ccons R ρ) hc.2
        (satEnv_rcons hS hx hR.1)
        (fun i => by cases i; exact hy; exact hσ' _)
        (fun i j hi => by
          cases i with
          | zero => exact hR
          | succ i => exact hcp i j (by simpa using hi))
        _ _ (ntr_app hn hx) (ntr_app hm hy)
      rw [e1, e2]
      exact ⟨ih, (el_raw B (rcons x σ) (rcons y σ) (ccons R ρ) _ _).mp ih⟩

/-! ## `NeutralSupport` for the open code system -/

/-- The reflected value of a type image at a context level. -/
def reflectAt (V : Value) (a : Nat) : Value := reflV V (NeutralPER.neutralAtom (a + 12))

theorem ntr_reflectAtom (a : Nat) : Ntr (NeutralPER.neutralAtom (a + 12)) :=
  ntr_atom (by omega)

theorem decode_universe (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    {k l : Option Nat} {R : Relation} {x : Value}
    (hc : (EnvironmentEval.annSemantics codeSystem E H).Code l (universeValue k) R)
    (hx : Member R x) : ∃ S, (EnvironmentEval.annSemantics codeSystem E H).Code k x S := by
  have hs := family.code_coherent hc (family.universe_code k)
  have hu := (hs x x).mp hx
  cases k with
  | none =>
      obtain ⟨b, hb, _⟩ := hu
      exact ⟨_, ⟨b, hb, fun _ _ => Iff.rfl⟩⟩
  | some j =>
      obtain ⟨c, hc', hxc, _⟩ := hu
      exact ⟨_, family.ok_code (c := c) hc' hxc⟩

theorem reflect_member (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    {k : Option Nat} {V : Value} {R : Relation}
    (hc : (EnvironmentEval.annSemantics codeSystem E H).Code k V R) (a : Nat) :
    Member R (reflectAt V a) := by
  have hn := ntr_reflectAtom a
  cases k with
  | none =>
      obtain ⟨b, hV, hR⟩ := (hc : OptionSoundUniverse.NoneRawCode V R)
      refine (hR _ _).mpr ?_
      cases b with
      | some _ => exact True.intro
      | none =>
          have hV' : V = universeValue none := NeutralCodes.valueEq_eq hV
          refine ⟨some (OptionSoundUniverse.NoneOrdinary.named 13), ?_, ?_⟩ <;>
            (show ValueEq (reflectAt V a) _
             rw [hV']
             exact refl_universe none _)
  | some j =>
      obtain ⟨⟨c, hc', hV⟩, hR⟩ := (hc : family.FCode j V R)
      refine (hR _ _).mpr ⟨c, hc', hV, ?_⟩
      rw [NeutralCodes.valueEq_eq hV]
      exact el_reflect c [] σ0 σ0 ρ0 hc' sat0 (fun _ => rfl) (fun i j h => by simp at h) _ _ hn hn

/-- The open Girard code system has a `NeutralSupport`. -/
def neutralSupport (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) :
    NeutralExtraction.NeutralSupport (EnvironmentEval.annSemantics codeSystem E H) where
  decode := decode_universe E H
  reflect := reflectAt
  reflect_member := reflect_member E H

/-- The same support on the skeleton's Target shape
`annSemantics codeSystem (view E) (hook hE F)`. -/
def neutralSupport_target {E : ResolvedEnvA} (hE : EnvWfA (iotaIfaceA E) E)
    (F : EnvironmentEval.FamilySyntax) :
    NeutralExtraction.NeutralSupport
      (EnvironmentEval.annSemantics codeSystem (SemanticMemberEval.view E)
        (AdmissionUniverseReadback.hook hE F)) :=
  neutralSupport _ _

end Rcic.Declarative.Ann.LR3.CandidateReflection
