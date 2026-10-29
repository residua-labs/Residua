import rcic.RcicAnnLR3LevelGirard

/-!
# The level-Girard code system: `UniverseAlgebra`, CR3 and `NeutralSupport`

The image-keyed code system of closed, kinded level codes (`LevelGirard`),
read with candidates that contain the reflections of their raw arguments
(`SatFor`):

- `coherent`: image-equal kinded codes have the same reading, because they
  are twins (`imageEq_twin`, `el_twin`);
- `codeSystem`, `universeTransport`, `propIrrelevance`: the skeleton's
  `UniverseAlgebra`;
- `el_reflect`: CR3 at every kinded code. Level-zero codes and neutral types
  are chaotic; at a universe, both reflections are the image of the closed
  code `named13`;
- `neutralSupport`, `neutralSupport_target`: `NeutralSupport` for
  `annSemantics codeSystem E H`, in particular on every Target shape
  `annSemantics codeSystem (view E) (hook hE F)` (for example
  `F := EqKLikeHook.eqKHook`);
- `el_app_univ`: a related type-valued function sends related arguments to
  type images of its codomain's level. This is what the chaotic Π of
  `LevelCodeSystem` could not carry.

Every proposition is chaotic here, so a transport between apart Eq indices
only moves values between chaotic relations; above level zero, a type's
reading depends on its level-zero parts not at all (`el_twin`). This is the
typing-half model; it is not a consistency model. The Fundamental for it is
not claimed here. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelGirardSystem

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open TypeZeroTowerProbe (withBot Head11Free)
open CandidateTowerProbe (REnv CEnv rcons ccons Sat Adm AdmLaws SatFor satFor_laws Ntr SatEnv
  satEnv_rcons)
open CandidateTowerCoherence (BotEnv constEnv)
open CandidateCodeSystem (σ0 ρ0 sat0 botRel botRel_sat)
open ObservationReflection
open LevelGirard

/-! ## Coherence -/

theorem coherent {adm : Adm} {k l : Nat} (c : LCode k) (d : LCode l) (κ : List (Option Nat))
    (hc : Kinded κ c) (hd : Kinded κ d) (h : ImageEq c d) (σ : REnv) (ρ : CEnv) :
    Same (ElA adm σ ρ c) (ElA adm σ ρ d) :=
  el_twin (imageEq_twin c d κ hc hd h) σ ρ

/-! ## The image-keyed family -/

theorem wfc_not_var {k i : Nat} (h : WFc (LCode.var k i)) : False := by
  have h1 : ([] : List (Option Nat))[i]? = some (some (k + 1)) := h.1
  simp at h1

theorem wfc_not_var0 {i : Nat} (h : WFc (LCode.var0 i)) : False := by
  have h1 : ([] : List (Option Nat))[i]? = some (some 0) := h.1
  simp at h1

theorem wfc_nonvar {k : Nat} : (c : LCode k) → WFc c → NonVar c
  | .var0 _, h => wfc_not_var0 h
  | .var _ _, h => wfc_not_var h
  | .prop _, _ => trivial
  | .pi0 _ _, _ => trivial
  | .univ _, _ => trivial
  | .neutral _ _, _ => trivial
  | .pi _ _ _, _ => trivial

def familyA (adm : Adm) (ha : AdmLaws adm) : ImageKeyedCodeSystem.Family where
  Cd := LCode
  ok := fun c => WFc c
  img := fun c => image σ0 c
  rel := fun c => ElA adm σ0 ρ0 c
  laws := fun c _ => el_laws ha c σ0 ρ0 sat0
  level := fun c hc => (nonvar_level σ0 c [] hc.1 (wfc_nonvar c hc)).1
  defined := fun c hc => (nonvar_level σ0 c [] hc.1 (wfc_nonvar c hc)).2
  coherent := fun c d hc hd h => coherent c d [] hc.1 hd.1 (wfc_imageEq hc hd σ0 h) σ0 ρ0
  univ := LCode.univ
  univ_ok := fun _ => ⟨trivial, trivial⟩
  univ_img := fun _ => ValueEq.refl _
  univ_member := fun k => ⟨LCode.univ k, LCode.univ k, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    twin_refl _, ValueEq.refl _, ValueEq.refl _⟩
  univ_decode := by
    rintro k V W ⟨c, d, hc, hd, ht, hV, hW⟩
    exact ⟨c, d, hc, hd, hV, hW, el_twin ht σ0 ρ0⟩

/-- The level model with candidates containing reflections. -/
def family : ImageKeyedCodeSystem.Family := familyA SatFor satFor_laws

def codeSystem : CodeSystem := family.codeSystem

theorem universeTransport : PairedStatements.UniverseTransport codeSystem :=
  family.universeTransport

theorem propIrrelevance : PairedStatements.PropIrrelevance codeSystem :=
  family.propIrrelevance (fun c _ x y hx hy => by
    have hx' : ElA SatFor σ0 ρ0 c x x := hx
    have hy' : ElA SatFor σ0 ρ0 c y y := hy
    show ElA SatFor σ0 ρ0 c x y
    rw [el_zero σ0 ρ0 c] at hx' hy' ⊢
    exact ⟨hx'.1, hy'.1⟩)

/-! ## CR3 and `NeutralSupport` -/

/-- A constant level-zero type image is well formed. -/
theorem propImg_const (V : Value) (hl : SortMember (some 0) V) (hd : TypeDefined V)
    (hb : V .bot) : PropImg (fun _ => V) :=
  ⟨fun _ _ hd' => ⟨[], by simp, fun _ _ => hd'⟩, fun _ => hl, fun _ => hd, fun _ => hb⟩

/-- The closed code of the named neutral type `13` at level `k`. -/
def named13 : (k : Nat) → LCode k
  | 0 => .prop (fun _ => NativeMemberValues.value (some 0) 13)
  | j + 1 => .neutral j 13

theorem named13_wfc : (k : Nat) → WFc (named13 k)
  | 0 => ⟨propImg_const _ (NativeMemberValues.value_level _ _) (NativeMemberValues.value_defined _ _)
      (NativeMemberValues.value_bot _ _), fun _ _ _ => rfl⟩
  | _ + 1 => ⟨(by decide : (13 : Nat) ≠ 11), trivial⟩

theorem named13_image (σ : REnv) : (k : Nat) →
    image σ (named13 k) = NativeMemberValues.value (some k) 13
  | 0 => rfl
  | _ + 1 => rfl

theorem withBot_eq {v : Value} (h : v .bot) : withBot v = v := by
  funext c
  exact propext ⟨fun h' => h'.elim (fun e => e ▸ h) id, Or.inr⟩

/-- CR3: reflections are related at every kinded code. -/
theorem el_reflect : {k : Nat} → (c : LCode k) → ∀ (κ : List (Option Nat)) (σ σ' : REnv)
    (ρ : CEnv), Kinded κ c → SatEnv σ ρ → (∀ i, σ' i .bot) →
    (∀ i j, κ[i]? = some (some (j + 1)) → SatFor (σ i) (σ' i) (ρ i)) →
    ∀ n m, Ntr n → Ntr m → ElA SatFor σ ρ c (reflV (image σ c) n) (reflV (image σ' c) m)
  | _, .var0 _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨.bot _ _, .bot _ _⟩
  | _, .prop _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨.bot _ _, .bot _ _⟩
  | _, .pi0 _ _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨.bot _ _, .bot _ _⟩
  | _, .neutral _ _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨.bot _ _, .bot _ _⟩
  | _, .var k i, _, σ, σ', ρ, hc, hS, hσ', hcp, n, m, hn, hm => by
      obtain ⟨_, hR⟩ := hcp i k hc
      show ρ i (reflV (withBot (σ i)) n) (reflV (withBot (σ' i)) m)
      rw [withBot_eq (hS.2 i), withBot_eq (hσ' i)]
      exact hR n m hn hm
  | _, .univ k, _, _, _, _, _, _, _, _, n, m, _, _ => by
      refine ⟨named13 k, named13 k, named13_wfc k, named13_wfc k, twin_refl _, ?_, ?_⟩
      · rw [named13_image]
        exact refl_universe (some k) n
      · rw [named13_image]
        exact refl_universe (some k) m
  | _, .pi c A B, κ, σ, σ', ρ, hc, hS, hσ', hcp, n, m, hn, hm => by
      refine ⟨.bot _ _, .bot _ _, fun x y hxy R hR => ?_⟩
      have hx : x .bot := el_saturated σ ρ hS A x y hxy
      have hy : y .bot := el_saturated σ ρ hS A y x ((el_laws satFor_laws A σ ρ hS).symm hxy)
      have e1 : NeutralPi.applyValue (reflV (image σ (LCode.pi c A B)) n) x =
          reflV (image (rcons x σ) B) (NeutralPi.applyValue n x) :=
        NeutralCodes.valueEq_eq (refl_pi (k := some (c + 1)) (A := image σ A)
          (F := fun x => image (rcons x σ) B) (image_bot σ A κ hc.1) (codomain_finite B _ hc.2 σ)
          (fun z => image_bot (rcons z σ) B _ hc.2) n x)
      have e2 : NeutralPi.applyValue (reflV (image σ' (LCode.pi c A B)) m) y =
          reflV (image (rcons y σ') B) (NeutralPi.applyValue m y) :=
        NeutralCodes.valueEq_eq (refl_pi (k := some (c + 1)) (A := image σ' A)
          (F := fun x => image (rcons x σ') B) (image_bot σ' A κ hc.1)
          (codomain_finite B _ hc.2 σ') (fun z => image_bot (rcons z σ') B _ hc.2) m y)
      have ih := el_reflect B (kindOf A :: κ) (rcons x σ) (rcons y σ') (ccons R ρ) hc.2
        (satEnv_rcons hS hx hR.1)
        (fun i => by cases i; exact hy; exact hσ' _)
        (fun i j hi => by
          cases i with
          | zero => exact hR
          | succ i => exact hcp i j (by simpa using hi))
        _ _ (CandidateReflection.ntr_app hn hx) (CandidateReflection.ntr_app hm hy)
      rw [e1, e2]
      exact ⟨ih, (el_raw B (rcons x σ) (rcons y σ) (ccons R ρ) _ _).mp ih⟩

def reflectAt (V : Value) (a : Nat) : Value := reflV V (NeutralPER.neutralAtom (a + 12))

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
      obtain ⟨c, _, hc', _, _, hxc, _⟩ := hu
      exact ⟨_, family.ok_code (c := c) hc' hxc⟩

theorem reflect_member (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    {k : Option Nat} {V : Value} {R : Relation}
    (hc : (EnvironmentEval.annSemantics codeSystem E H).Code k V R) (a : Nat) :
    Member R (reflectAt V a) := by
  have hn := CandidateReflection.ntr_reflectAtom a
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
      exact el_reflect c [] σ0 σ0 ρ0 hc'.1 sat0 (fun _ => rfl) (fun i j h => by simp at h) _ _ hn hn

/-- `NeutralSupport` for the level-Girard code system, on every Target shape. -/
def neutralSupport (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) :
    NeutralExtraction.NeutralSupport (EnvironmentEval.annSemantics codeSystem E H) where
  decode := decode_universe E H
  reflect := reflectAt
  reflect_member := reflect_member E H

def neutralSupport_target {E : ResolvedEnvA} (hE : EnvWfA (iotaIfaceA E) E)
    (F : EnvironmentEval.FamilySyntax) :
    NeutralExtraction.NeutralSupport
      (EnvironmentEval.annSemantics codeSystem (SemanticMemberEval.view E)
        (AdmissionUniverseReadback.hook hE F)) :=
  neutralSupport _ _

/-! ## Type-valued functions -/

/-- Applying a related type-valued function to related arguments gives type
images of the codomain universe's level (the content of `Ty_app` for
type-valued functions in the level model). -/
theorem el_app_univ {σ : REnv} {ρ : CEnv} {c a j : Nat} {A : LCode a} {f g x y : Value}
    (hf : ElA SatFor σ ρ (LCode.pi c A (LCode.univ j)) f g) (hx : ElA SatFor σ ρ A x y) :
    ElA SatFor σ ρ (LCode.univ j) (NeutralPi.applyValue f x) (NeutralPi.applyValue g y) ∧
      SortMember (some j) (NeutralPi.applyValue f x) ∧
      TypeDefined (NeutralPi.applyValue f x) := by
  have h1 := (hf.2.2 x y hx botRel (CandidateCodeSystem.botRel_satFor x y)).1
  have h2 := (el_raw (LCode.univ j) (rcons x σ) σ (ccons botRel ρ) _ _).mp h1
  obtain ⟨d, _, hd, _, _, hV, _⟩ := id h2
  have hl := nonvar_level σ d [] hd.1 (wfc_nonvar d hd)
  exact ⟨h2, sortMember_congr hV.symm hl.1, typeDefined_congr hV.symm hl.2⟩

end Rcic.Declarative.Ann.LR3.LevelGirardSystem
