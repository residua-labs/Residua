import rcic.RcicAnnLR3LevelGirard
import rcic.RcicAnnLR3IotaNativeRecursor

/-!
# A content model with term-indexed families and Eq (closed Girard codes)

Codes are data in `Type 0` (`DCode : Nat → Type`), extending the closed
Girard codes with term dependency:

- `var k i args`: a family variable of level `k` applied to term images
  `args` (a type variable is a family used at no arguments);
- `univ k`, `neutral k name`, `pi A B` as for the Girard codes;
- `eq r A s t`: the index-retaining family `r` (Eq) at the type `A` and the
  term images `s`, `t`. Its raw image is the image the index-retaining family
  hook computes for `r A s t`.

Term images (`TImg`) are raw-value functions of the raw environment, required
to be jointly continuous and bottom-carrying (`TOk`).

The reading `El` (mutually with family invariance `Inv`) is the closed
Girard reading, with content at Eq: an Eq code relates bottom-carrying
values exactly when its indices are related by the reading of its type.
Products quantify over every saturated candidate family that is invariant
along the bound variable's type, and relate applications in the fibre at
either argument, so the reading is a PER for every kinded code with no
condition on term images (`el_laws`).

Proved: images are jointly continuous (`image_cont`); image-equal kinded
codes have the same reading and invariance (`coherent`, with separation of
image shapes, neutral-spine injectivity and variable separation); level-zero
codes are proof-irrelevant (`el_irrelevant`). The closed, kinded codes form
an image-keyed code system (`family`, `codeSystem`) with universe transport
and Prop irrelevance.

Content (not chaotic): `∀ X : Prop, X` relates nothing (`falseCode_empty`),
so every relation the system gives its image is empty
(`falseCode_code_empty`) and the system admits no `NeutralSupport`
(`no_neutralSupport`). `Eq Prop P P` is inhabited and `Eq Prop P Q` is empty
for distinct named propositions (`eqProp_refl`, `eqProp_apart`).

Not claimed: a reader of source types into content codes, a Fundamental
theorem, or `FalseEmpty` for the image of the constant `False` of an
environment. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ContentCodes

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe (REnv rcons Sat)
open CandidateTowerCoherence (upd EnvLe envLe_rcons rcons_upd BotEnv botEnv_rcons constEnv
  applyValue_legalGraph_at pi_vs_tagged)
open LevelGirard (JointCont JointCont.mono JointCont.finite combine_reqs pi_cont var_cont
  const_cont)

/-- A term image: the raw value of a term in each raw environment. -/
abbrev TImg := REnv → Value

/-- A candidate family over lists of raw arguments. A type variable is a
family used at the empty list. -/
abbrev Fam := List Value → Relation

abbrev FEnv := Nat → Fam

def fcons (F : Fam) (ρ : FEnv) : FEnv
  | 0 => F
  | i + 1 => ρ i

/-- Content codes. -/
inductive DCode : Nat → Type
  | var (k i : Nat) (args : List TImg) : DCode k
  | univ (k : Nat) : DCode (k + 1)
  | neutral (k name : Nat) : DCode k
  | pi {a b : Nat} (A : DCode a) (B : DCode b) : DCode (imaxN a b)
  | eq (r : Nat) {a : Nat} (A : DCode a) (s t : TImg) : DCode 0

def argVals (args : List TImg) (σ : REnv) : List Value := args.map (fun t => t σ)

/-- The raw image of `r A s t` for an indexed family `r` with three
arguments, as the index-retaining family hook computes it. -/
def eqImage (r : Nat) (A s t : Value) : Value :=
  InductiveCodes.taggedValue (some 0) (IotaRecursor.applyAll (NeutralPER.neutralAtom r) [A, s, t])

def image : {k : Nat} → REnv → DCode k → Value
  | _, σ, .var _ i args => IotaRecursor.applyAll (withBot (σ i)) (argVals args σ)
  | _, _, .univ k => universeValue (some k)
  | _, _, .neutral k name => NativeMemberValues.value (some k) name
  | _, σ, @DCode.pi a b A B => InductiveCodes.piValue (some (imaxN a b)) (image σ A)
      (UnifiedPi.legalGraph (fun _ _ => True) (fun x => image (rcons x σ) B))
  | _, σ, .eq r A s t => eqImage r (image σ A) (s σ) (t σ)

/-! ## Kinds and well-formedness -/

/-- The kind a binder type gives its variable: a universe level and an arity
of first-order (non-kind) argument binders. -/
def kindPi : Option (Nat × Nat) → Option (Nat × Nat) → Option (Nat × Nat)
  | none, kb => kb.map (fun p => (p.1, p.2 + 1))
  | some _, _ => none

def kindOf : {k : Nat} → DCode k → Option (Nat × Nat)
  | _, .var _ _ _ => none
  | _, .univ j => some (j, 0)
  | _, .neutral _ _ => none
  | _, .pi A B => kindPi (kindOf A) (kindOf B)
  | _, .eq _ _ _ _ => none

/-- A well-formed term image: jointly continuous and bottom-carrying. -/
def TOk (t : TImg) : Prop := JointCont t ∧ ∀ σ, t σ .bot

/-- The arguments of a variable do not read the variable's own slot. -/
def HeadFree (i : Nat) (args : List TImg) : Prop :=
  ∀ σ v, argVals args (upd σ i v) = argVals args σ

def Kinded : {k : Nat} → List (Option (Nat × Nat)) → DCode k → Prop
  | _, κ, .var k i args => κ[i]? = some (some (k, args.length)) ∧ (∀ t ∈ args, TOk t) ∧
      HeadFree i args
  | _, _, .univ _ => True
  | _, _, .neutral _ name => name ≠ 11
  | _, κ, .pi A B => Kinded κ A ∧ Kinded (kindOf A :: κ) B
  | _, κ, .eq _ A s t => Kinded κ A ∧ TOk s ∧ TOk t

/-- A term image reads only the first `n` slots. -/
def TClosed (n : Nat) (t : TImg) : Prop := ∀ σ σ' : REnv, (∀ i, i < n → σ i = σ' i) → t σ = t σ'

def ClosedAt : {k : Nat} → Nat → DCode k → Prop
  | _, n, .var _ i args => i < n ∧ ∀ t ∈ args, TClosed n t
  | _, _, .univ _ => True
  | _, _, .neutral _ _ => True
  | _, n, .pi A B => ClosedAt n A ∧ ClosedAt (n + 1) B
  | _, n, .eq _ A s t => ClosedAt n A ∧ TClosed n s ∧ TClosed n t

/-! ## Joint continuity of images -/

theorem applyValue_cont {f x : REnv → Value} (hf : JointCont f) (hx : JointCont x) :
    JointCont (fun σ => NeutralPi.applyValue (f σ) (x σ)) := by
  intro σ d hd
  rcases hd with hb | ⟨g, s, hc, hfg, hs, hxs⟩ | ⟨r, args, u, hc, hfs, hxu⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hb⟩
  · obtain ⟨S₁, h₁, k₁⟩ := hf σ _ hfg
    obtain ⟨S₂, h₂, k₂⟩ := combine_reqs σ (fun σ' u => x σ' u) s.1
      (fun u hu => hx σ u (hxs u hu))
    refine ⟨S₁ ++ S₂, fun p hp => ?_, fun σ' hσ' => ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact h₁ p hp
      · exact h₂ p hp
    · exact Or.inr (Or.inl ⟨g, s, hc, k₁ σ' (fun p hp => hσ' p (List.mem_append_left _ hp)), hs,
        k₂ σ' (fun p hp => hσ' p (List.mem_append_right _ hp))⟩)
  · obtain ⟨S₁, h₁, k₁⟩ := hf σ _ hfs
    obtain ⟨S₂, h₂, k₂⟩ := hx σ u hxu
    refine ⟨S₁ ++ S₂, fun p hp => ?_, fun σ' hσ' => ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact h₁ p hp
      · exact h₂ p hp
    · exact Or.inr (Or.inr ⟨r, args, u, hc, k₁ σ' (fun p hp => hσ' p (List.mem_append_left _ hp)),
        k₂ σ' (fun p hp => hσ' p (List.mem_append_right _ hp))⟩)

theorem applyAll_cont : (args : List TImg) → ∀ {f : REnv → Value}, JointCont f →
    (∀ t ∈ args, JointCont t) →
    JointCont (fun σ => IotaRecursor.applyAll (f σ) (argVals args σ))
  | [], _, hf, _ => hf
  | t :: args, _, hf, ht =>
      applyAll_cont args (applyValue_cont hf (ht t (by simp))) (fun t' h => ht t' (by simp [h]))

theorem tagged_cont {P : REnv → Value} (hP : JointCont P) (l : Option Nat) :
    JointCont (fun σ => InductiveCodes.taggedValue l (P σ)) := by
  intro σ d hd
  rcases hd with hb | ⟨a, p, he, ha, hp⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hb⟩
  · obtain ⟨S, hS, kS⟩ := hP σ p hp
    exact ⟨S, hS, fun σ' h => Or.inr ⟨a, p, he, ha, kS σ' h⟩⟩

theorem eqImage_cont {A s t : REnv → Value} (hA : JointCont A) (hs : JointCont s)
    (ht : JointCont t) (r : Nat) :
    JointCont (fun σ => eqImage r (A σ) (s σ) (t σ)) :=
  tagged_cont (applyAll_cont [A, s, t] (f := fun _ => NeutralPER.neutralAtom r) (const_cont _) (by
    intro u hu
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact hA
    · exact hs
    · exact ht)) _

/-- Every kinded code's image is jointly continuous. -/
theorem image_cont : {k : Nat} → (c : DCode k) → ∀ (κ : List (Option (Nat × Nat))), Kinded κ c →
    JointCont (fun σ => image σ c)
  | _, .var _ i args, _, hk => applyAll_cont args (var_cont i) (fun t ht => (hk.2.1 t ht).1)
  | _, .univ _, _, _ => const_cont _
  | _, .neutral _ _, _, _ => const_cont _
  | _, @DCode.pi a b A B, κ, hk =>
      have hB := image_cont B _ hk.2
      pi_cont (fun σ => image σ A) (fun σ => image σ B) (some (imaxN a b))
        (image_cont A κ hk.1) hB (fun σ σ' h d hd => hB.mono σ σ' h d hd)
  | _, .eq r A s t, κ, hk => eqImage_cont (image_cont A κ hk.1) hk.2.1.1 hk.2.2.1 r

theorem image_mono {k : Nat} (c : DCode k) (κ : List (Option (Nat × Nat))) (hk : Kinded κ c)
    {σ σ' : REnv} (h : EnvLe σ σ') (d : CptI) (hd : image σ c d) : image σ' c d :=
  (image_cont c κ hk).mono σ σ' h d hd

/-- The codomain's raw image function has finite demand. -/
theorem codomain_finite {k : Nat} (B : DCode k) (κ : List (Option (Nat × Nat))) (hB : Kinded κ B)
    (σ : REnv) :
    UnifiedPi.LegalFiniteDemand (fun _ _ => True) (fun x => image (rcons x σ) B) := by
  intro x _ c hc
  have he : ∀ y, upd (rcons x σ) 0 y = rcons y σ := fun y => by
    funext i
    cases i <;> rfl
  have hc' : image (upd (rcons x σ) 0 x) B c := by rw [he]; exact hc
  obtain ⟨us, hus, hfin⟩ := (image_cont B κ hB).finite (rcons x σ) 0 x c hc'
  refine ⟨us, hus, fun y _ hy => ?_⟩
  have h := hfin y hy
  rw [he] at h
  exact h

theorem applyValue_bot (f x : Value) : NeutralPi.applyValue f x .bot := Or.inl rfl

theorem applyAll_bot : (args : List Value) → ∀ (f : Value), f .bot →
    IotaRecursor.applyAll f args .bot
  | [], _, hf => hf
  | _ :: args, _, _ => applyAll_bot args _ (applyValue_bot _ _)

theorem image_bot {k : Nat} (σ : REnv) : (c : DCode k) → image σ c .bot
  | .var _ i args => applyAll_bot _ _ (Or.inl rfl)
  | .univ _ => .bot _ _
  | .neutral _ _ => .bot _ _
  | .pi _ _ => Or.inl rfl
  | .eq _ _ _ _ => Or.inl rfl

/-! ## The content reading -/

/-- Closed, kinded codes: the members of a universe. -/
def WFc {k : Nat} (c : DCode k) : Prop := Kinded [] c ∧ ClosedAt 0 c

/-- A family is saturated at every argument list. -/
def SatFam (F : Fam) : Prop := ∀ l, Sat (F l)

mutual
/-- The content reading. A level-zero family variable is read through the
irrelevant closure of its candidate at the argument values; a positive one
reads its candidate. Universes relate images of closed, kinded codes. A
product relates functions that send related arguments to related results,
for every admissible candidate family of the bound variable, in the fibre at
either argument. An Eq code relates bottom-carrying values exactly when its
two indices are related by the reading of its type: proofs are irrelevant,
and the type is empty at unrelated indices. -/
def El : {k : Nat} → REnv → FEnv → DCode k → Relation
  | _, σ, ρ, .var 0 i args => fun x y => ρ i (argVals args σ) x x ∧ ρ i (argVals args σ) y y
  | _, σ, ρ, .var (_ + 1) i args => ρ i (argVals args σ)
  | _, σ, _, .univ k => fun V W =>
      ∃ c : DCode k, WFc c ∧ ValueEq V (image σ c) ∧ ValueEq W (image σ c)
  | _, _, _, .neutral _ _ => fun x y => CandidatePi.Neutral x ∧ CandidatePi.Neutral y
  | _, σ, ρ, .pi A B => fun f g => f .bot ∧ g .bot ∧ ∀ x y, El σ ρ A x y →
      ∀ F : Fam, SatFam F → Inv σ ρ A F F →
        El (rcons x σ) (fcons F ρ) B (NeutralPi.applyValue f x) (NeutralPi.applyValue g y) ∧
        El (rcons y σ) (fcons F ρ) B (NeutralPi.applyValue f x) (NeutralPi.applyValue g y)
  | _, σ, ρ, .eq _ A s t => fun h h' => h .bot ∧ h' .bot ∧ El σ ρ A (s σ) (t σ)

/-- Invariance of candidate families along a binder type. At a universe the
two families agree on the empty argument list. Along a product, related
arguments give invariant families of the remaining arguments, in the fibre
at the first argument. Other binder types bind term variables, whose
candidates are never read. -/
def Inv : {k : Nat} → REnv → FEnv → DCode k → Fam → Fam → Prop
  | _, _, _, .univ _, F, F' => Same (F []) (F' [])
  | _, σ, ρ, .pi A B, F, F' => ∀ x y, El σ ρ A x y → ∀ G : Fam, SatFam G → Inv σ ρ A G G →
      Inv (rcons x σ) (fcons G ρ) B (fun l => F (x :: l)) (fun l => F' (y :: l))
  | _, _, _, .var _ _ _, _, _ => True
  | _, _, _, .neutral _ _, _, _ => True
  | _, _, _, .eq _ _ _ _, _, _ => True
end

def SatEnv (σ : REnv) (ρ : FEnv) : Prop := (∀ i, SatFam (ρ i)) ∧ ∀ i, σ i .bot

theorem satEnv_rcons {σ : REnv} {ρ : FEnv} (h : SatEnv σ ρ) {x : Value} (hx : x .bot)
    {F : Fam} (hF : SatFam F) : SatEnv (rcons x σ) (fcons F ρ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · cases i with
    | zero => exact hF
    | succ i => exact h.1 i
  · cases i with
    | zero => exact hx
    | succ i => exact h.2 i

theorem el_saturated {k : Nat} (σ : REnv) (ρ : FEnv) (h : SatEnv σ ρ) :
    (c : DCode k) → ∀ x y, El σ ρ c x y → x .bot
  | .var 0 i _ => fun _ _ hxy => (h.1 i _).2 _ _ hxy.1
  | .var (_ + 1) i _ => fun _ _ hxy => (h.1 i _).2 _ _ hxy
  | .univ _ => fun _ _ ⟨c, _, hx, _⟩ => (hx .bot).mpr (image_bot σ c)
  | .neutral _ _ => fun _ _ hxy => RCodeSoundPiControl.neutral_bot hxy.1
  | .pi _ _ => fun _ _ hxy => hxy.1
  | .eq _ _ _ _ => fun _ _ hxy => hxy.1

theorem irr_laws (R : Relation) :
    Laws (fun x y => R x x ∧ R y y) := ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, b⟩ => ⟨a, b⟩⟩

/-- Every reading is a PER in a saturated environment. -/
theorem el_laws : {k : Nat} → (c : DCode k) → ∀ σ ρ, SatEnv σ ρ → Laws (El σ ρ c)
  | _, .var 0 i _, _, _, h => irr_laws _
  | _, .var (_ + 1) i _, _, _, h => (h.1 i _).1
  | _, .univ _, _, _, _ => by
      refine ⟨?_, ?_⟩
      · rintro V W ⟨c, hc, hV, hW⟩
        exact ⟨c, hc, hW, hV⟩
      · rintro V W Z ⟨c, hc, hV, hW⟩ ⟨d, _, hW', hZ⟩
        exact ⟨c, hc, hV, hZ.trans (hW'.symm.trans hW)⟩
  | _, .neutral _ _, _, _, _ => CandidateTowerProbe.neutral_laws
  | _, .pi A B, σ, ρ, h => by
      have lA := el_laws A σ ρ h
      have bot : ∀ x y, El σ ρ A x y → x .bot := el_saturated σ ρ h A
      refine ⟨?_, ?_⟩
      · rintro f g ⟨hf, hg, hfg⟩
        refine ⟨hg, hf, fun x y hxy F hF hI => ?_⟩
        obtain ⟨h1, h2⟩ := hfg y x (lA.symm hxy) F hF hI
        exact ⟨(el_laws B _ _ (satEnv_rcons h (bot x y hxy) hF)).symm h2,
          (el_laws B _ _ (satEnv_rcons h (bot y x (lA.symm hxy)) hF)).symm h1⟩
      · rintro f g k ⟨hf, _, hfg⟩ ⟨_, hk, hgk⟩
        refine ⟨hf, hk, fun x y hxy F hF hI => ?_⟩
        have hxx := lA.trans hxy (lA.symm hxy)
        have hyy := lA.trans (lA.symm hxy) hxy
        exact ⟨(el_laws B _ _ (satEnv_rcons h (bot x y hxy) hF)).trans
            (hfg x x hxx F hF hI).1 (hgk x y hxy F hF hI).1,
          (el_laws B _ _ (satEnv_rcons h (bot y x (lA.symm hxy)) hF)).trans
            (hfg x y hxy F hF hI).2 (hgk y y hyy F hF hI).1⟩
  | _, .eq _ _ _ _, _, _, _ =>
      ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, _, c⟩ ⟨_, b, _⟩ => ⟨a, b, c⟩⟩

/-! ## Neutral spines -/

/-- Componentwise observations of an argument list. -/
def Obs : List Value → List CptI → Prop
  | [], [] => True
  | x :: xs, u :: us => x u ∧ Obs xs us
  | _, _ => False

/-- The raw value of a neutral head `n` applied to the arguments `xs`. -/
def spineVal (n : Nat) (xs : List Value) : Value := fun c =>
  c = .bot ∨ ∃ us, c = .spine n us ∧ Obs xs us

theorem obs_snoc_inv : (xs : List Value) → (x : Value) → (vs : List CptI) →
    Obs (xs ++ [x]) vs → ∃ us u, vs = us ++ [u] ∧ Obs xs us ∧ x u
  | [], _, [], h => h.elim
  | [], _, [v], h => ⟨[], v, rfl, trivial, h.1⟩
  | [], _, _ :: _ :: _, h => h.2.elim
  | _ :: _, _, [], h => h.elim
  | _ :: xs, x, v :: vs, h => by
      obtain ⟨us, u, he, ho, hu⟩ := obs_snoc_inv xs x vs h.2
      exact ⟨v :: us, u, by rw [he]; rfl, ⟨h.1, ho⟩, hu⟩

theorem obs_snoc_intro : (xs : List Value) → (x : Value) → (us : List CptI) → (u : CptI) →
    Obs xs us → x u → Obs (xs ++ [x]) (us ++ [u])
  | [], _, [], _, _, hu => ⟨hu, trivial⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim
  | _ :: xs, x, _ :: us, u, h, hu => ⟨h.1, obs_snoc_intro xs x us u h.2 hu⟩

theorem apply_spineVal (n : Nat) (xs : List Value) (x : Value) :
    NeutralPi.applyValue (spineVal n xs) x = spineVal n (xs ++ [x]) := by
  funext c
  apply propext
  constructor
  · rintro (h | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, hc, hf, hu⟩)
    · exact Or.inl h
    · rcases hf with h | ⟨_, h, _⟩ <;> cases h
    · rcases hf with h | ⟨us, h, ho⟩
      · cases h
      · injection h with h1 h2
        subst h1
        subst h2
        exact Or.inr ⟨args ++ [u], hc, obs_snoc_intro _ _ _ _ ho hu⟩
  · rintro (h | ⟨vs, hc, ho⟩)
    · exact Or.inl h
    · obtain ⟨us, u, rfl, ho', hu⟩ := obs_snoc_inv xs x vs ho
      exact Or.inr (Or.inr ⟨n, us, u, hc, Or.inr ⟨us, rfl, ho'⟩, hu⟩)

theorem atom_spineVal (n : Nat) : NeutralPER.neutralAtom n = spineVal n [] := by
  funext c
  apply propext
  constructor
  · intro h
    rcases approxI_const_inv h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨[], h, trivial⟩
  · rintro (h | ⟨us, h, ho⟩)
    · subst h
      exact ApproxI.bot _ _
    · cases us with
      | nil => subst h; exact NeutralPER.neutralAtom_observed n
      | cons _ _ => exact ho.elim

theorem applyAll_spineVal (n : Nat) : (ys xs : List Value) →
    IotaRecursor.applyAll (spineVal n xs) ys = spineVal n (xs ++ ys)
  | [], xs => by rw [List.append_nil]; rfl
  | y :: ys, xs => by
      show IotaRecursor.applyAll (NeutralPi.applyValue (spineVal n xs) y) ys = _
      rw [apply_spineVal, applyAll_spineVal n ys, List.append_assoc]
      rfl

theorem applyAll_atom (n : Nat) (xs : List Value) :
    IotaRecursor.applyAll (NeutralPER.neutralAtom n) xs = spineVal n xs := by
  rw [atom_spineVal, applyAll_spineVal]
  rfl

def bots (xs : List Value) : List CptI := xs.map (fun _ => .bot)

theorem obs_bots : (xs : List Value) → (∀ x ∈ xs, x .bot) → Obs xs (bots xs)
  | [], _ => trivial
  | x :: xs, h => ⟨h x (by simp), obs_bots xs (fun y hy => h y (by simp [hy]))⟩

theorem obs_inj : (xs ys : List Value) → (∀ x ∈ xs, x .bot) → (∀ y ∈ ys, y .bot) →
    (∀ us, Obs xs us ↔ Obs ys us) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hy, h => ((h (bots (y :: ys))).mpr (obs_bots _ hy)).elim
  | x :: xs, [], hx, _, h => ((h (bots (x :: xs))).mp (obs_bots _ hx)).elim
  | x :: xs, y :: ys, hx, hy, h => by
      have hx' : ∀ z ∈ xs, z .bot := fun z hz => hx z (by simp [hz])
      have hy' : ∀ z ∈ ys, z .bot := fun z hz => hy z (by simp [hz])
      have hxy : x = y := by
        funext u
        apply propext
        constructor
        · intro hu
          exact ((h (u :: bots xs)).mp ⟨hu, obs_bots xs hx'⟩).1
        · intro hu
          exact ((h (u :: bots ys)).mpr ⟨hu, obs_bots ys hy'⟩).1
      have htail : xs = ys := obs_inj xs ys hx' hy' (fun us =>
        ⟨fun ho => ((h (.bot :: us)).mp ⟨hx x (by simp), ho⟩).2,
          fun ho => ((h (.bot :: us)).mpr ⟨hy y (by simp), ho⟩).2⟩)
      rw [hxy, htail]

theorem spineVal_inj {n m : Nat} {xs ys : List Value} (hx : ∀ x ∈ xs, x .bot)
    (hy : ∀ y ∈ ys, y .bot) (h : ValueEq (spineVal n xs) (spineVal m ys)) : n = m ∧ xs = ys := by
  have hnm : n = m := by
    rcases (h _).mp (Or.inr ⟨bots xs, rfl, obs_bots xs hx⟩) with h1 | ⟨_, h1, _⟩
    · cases h1
    · injection h1
  subst hnm
  refine ⟨rfl, obs_inj xs ys hx hy (fun us => ⟨fun ho => ?_, fun ho => ?_⟩)⟩
  · rcases (h _).mp (Or.inr ⟨us, rfl, ho⟩) with h1 | ⟨vs, h1, ho'⟩
    · cases h1
    · injection h1 with _ h2
      subst h2
      exact ho'
  · rcases (h _).mpr (Or.inr ⟨us, rfl, ho⟩) with h1 | ⟨vs, h1, ho'⟩
    · cases h1
    · injection h1 with _ h2
      subst h2
      exact ho'

theorem tagged_inj {k l : Option Nat} {P Q : Value} (hP : P .bot)
    (h : ValueEq (InductiveCodes.taggedValue k P) (InductiveCodes.taggedValue l Q)) :
    k = l ∧ ValueEq P Q := by
  have hkl : k = l := by
    rcases (h _).mp ((InductiveCodes.taggedValue_full k P .bot).mpr hP) with h1 | ⟨a, p, he, ha, _⟩
    · cases h1
    · simp only [NeutralCodes.fullTag, CptI.spine.injEq, List.cons.injEq, and_true,
        true_and] at he
      rcases ha with ha | ha
      · rw [ha] at he
        exact (CptI.noConfusion he.1)
      · rw [ha] at he
        injection he.1 with h2
        exact levelRef_injective h2
  subst hkl
  refine ⟨rfl, fun p => ?_⟩
  rw [← InductiveCodes.taggedValue_full k P p, ← InductiveCodes.taggedValue_full k Q p]
  exact h _

theorem image_eq_tagged (σ : REnv) (r : Nat) {a : Nat} (A : DCode a) (s t : TImg) :
    image σ (DCode.eq r A s t) =
      InductiveCodes.taggedValue (some 0) (spineVal r [image σ A, s σ, t σ]) := by
  show eqImage _ _ _ _ = _
  unfold eqImage
  rw [applyAll_atom]

theorem image_univ_tagged (σ : REnv) (k : Nat) :
    ValueEq (image σ (DCode.univ k))
      (InductiveCodes.taggedValue (some (k + 1))
        (TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.univ k))) :=
  TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.univ k)

theorem image_neutral_tagged (σ : REnv) (k name : Nat) :
    ValueEq (image σ (DCode.neutral k name))
      (InductiveCodes.taggedValue (some k) (spineVal name [])) := by
  have h := TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.neutral k name)
  rw [show TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.neutral k name) =
    NeutralPER.neutralAtom name from rfl, atom_spineVal] at h
  exact h

theorem spineVal_spine (n : Nat) (xs : List Value) (p : CptI) (h : spineVal n xs p) :
    p = .bot ∨ ∃ r args, p = .spine r args := by
  rcases h with h | ⟨us, h, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨n, us, h⟩

theorem argVals_bot {args : List TImg} (h : ∀ t ∈ args, TOk t) (σ : REnv) :
    ∀ x ∈ argVals args σ, x .bot := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact (h t ht).2 σ

/-! ## Separation of image shapes -/

def ImageEq {k l : Nat} (c : DCode k) (d : DCode l) : Prop :=
  ∀ σ : REnv, BotEnv σ → ValueEq (image σ c) (image σ d)

theorem sep_univ_neutral {σ : REnv} {k l name : Nat}
    (h : ValueEq (image σ (DCode.univ k)) (image σ (DCode.neutral l name))) : False :=
  TypeZeroTowerProbe.not_univ_neutral (k := k) (l := l) (name := name) h

theorem sep_univ_pi {σ : REnv} {k a b : Nat} {A : DCode a} {B : DCode b}
    (h : ValueEq (image σ (DCode.univ k)) (image σ (DCode.pi A B))) : False :=
  pi_vs_tagged (image_bot σ A) (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
    (h.symm.trans (image_univ_tagged σ k))

theorem sep_neutral_pi {σ : REnv} {k name a b : Nat} {A : DCode a} {B : DCode b}
    (h : ValueEq (image σ (DCode.neutral k name)) (image σ (DCode.pi A B))) : False :=
  pi_vs_tagged (image_bot σ A) (fun p hp => spineVal_spine name [] p hp)
    (h.symm.trans (image_neutral_tagged σ k name))

theorem sep_univ_eq {σ : REnv} {k r a : Nat} {A : DCode a} {s t : TImg}
    (h : ValueEq (image σ (DCode.univ k)) (image σ (DCode.eq r A s t))) : False := by
  have h1 := (image_univ_tagged σ k).symm.trans h
  rw [image_eq_tagged] at h1
  have := (tagged_inj (ApproxI.bot _ _) h1).1
  injection this with h2
  exact Nat.succ_ne_zero k h2

theorem sep_neutral_eq {σ : REnv} {k name r a : Nat} {A : DCode a} {s t : TImg}
    (h : ValueEq (image σ (DCode.neutral k name)) (image σ (DCode.eq r A s t))) : False := by
  have h1 := (image_neutral_tagged σ k name).symm.trans h
  rw [image_eq_tagged] at h1
  have h2 := (tagged_inj (Or.inl rfl) h1).2
  rcases (h2 _).mp (Or.inr ⟨[], rfl, trivial⟩) with h3 | ⟨us, h3, ho⟩
  · cases h3
  · injection h3 with _ h4
    subst h4
    exact (show False from ho).elim

theorem sep_pi_eq {σ : REnv} {a b r a' : Nat} {A : DCode a} {B : DCode b} {A' : DCode a'}
    {s t : TImg} (h : ValueEq (image σ (DCode.pi A B)) (image σ (DCode.eq r A' s t))) : False := by
  rw [image_eq_tagged] at h
  exact pi_vs_tagged (image_bot σ A) (fun p hp => spineVal_spine r _ p hp) h

theorem apply_bottom (x : Value) : NeutralPi.applyValue bottom x = bottom := by
  funext c
  apply propext
  constructor
  · rintro (h | ⟨_, _, _, h, _, _⟩ | ⟨_, _, _, _, h, _⟩)
    · exact h
    · cases h
    · cases h
  · intro h
    exact Or.inl h

theorem applyAll_bottom : (xs : List Value) → IotaRecursor.applyAll bottom xs = bottom
  | [] => rfl
  | x :: xs => by
      show IotaRecursor.applyAll (NeutralPi.applyValue bottom x) xs = bottom
      rw [apply_bottom, applyAll_bottom xs]

/-- Non-variable codes. -/
def NonVar {k : Nat} : DCode k → Prop
  | .var _ _ _ => False
  | _ => True

theorem nonvar_obs {k : Nat} (σ : REnv) : (c : DCode k) → NonVar c →
    image σ c (.spine 10 [.bot, .bot])
  | .var _ _ _, h => h.elim
  | .univ _, _ => .appSpine (.appSpine (.const _ _ _) (.bot _ _)) (.bot _ _)
  | .neutral _ _, _ => .appSpine (.appSpine (.const _ _ _) (.bot _ _)) (.bot _ _)
  | .pi _ _, _ => Or.inr ⟨.bot, .bot, rfl, Or.inl rfl, Or.inl rfl⟩
  | .eq _ _ _ _, _ => Or.inr ⟨.bot, .bot, rfl, Or.inl rfl, applyAll_bot _ _ (ApproxI.bot _ _)⟩

theorem var_vs_nonvar {k l i : Nat} {args : List TImg} (d : DCode l) (hd : NonVar d)
    (h : ImageEq (DCode.var k i args) d) : False := by
  have h0 := (h (constEnv bottom) (fun _ => rfl) (.spine 10 [.bot, .bot])).mpr (nonvar_obs _ d hd)
  have he : image (constEnv bottom) (DCode.var k i args) = bottom := by
    show IotaRecursor.applyAll (withBot bottom) _ = bottom
    rw [CandidateSubstitution.withBot_eq (v := bottom) rfl, applyAll_bottom]
  rw [he] at h0
  cases h0

theorem var_vs_nonvar' {k l i : Nat} {args : List TImg} {d : DCode l}
    (h : ImageEq (DCode.var k i args) d) (hd : NonVar d) : False :=
  var_vs_nonvar d hd h

theorem atom_bot (n : Nat) : NeutralPER.neutralAtom n .bot := ApproxI.bot _ _

theorem image_var_atom {k i n : Nat} {args : List TImg} {σ : REnv}
    (hi : σ i = NeutralPER.neutralAtom n) :
    image σ (DCode.var k i args) = spineVal n (argVals args σ) := by
  show IotaRecursor.applyAll (withBot (σ i)) _ = _
  rw [hi, CandidateSubstitution.withBot_eq (atom_bot n), applyAll_atom]

theorem upd_self (σ : REnv) (j : Nat) (x : Value) : upd σ j x j = x := by
  show (if j = j then x else σ j) = x
  rw [if_pos rfl]

theorem upd_ne (σ : REnv) {i j : Nat} (x : Value) (h : i ≠ j) : upd σ j x i = σ i := by
  show (if i = j then x else σ i) = σ i
  rw [if_neg h]

theorem botEnv_upd {σ : REnv} (h : BotEnv σ) (j : Nat) {x : Value} (hx : x .bot) :
    BotEnv (upd σ j x) := by
  intro i
  by_cases hij : i = j
  · subst hij
    rw [upd_self]
    exact hx
  · rw [upd_ne σ x hij]
    exact h i

/-- Image-equal kinded variables are the same variable with the same
argument values. -/
theorem var_sep {κ : List (Option (Nat × Nat))} {k l i j : Nat} {args args' : List TImg}
    (hc : Kinded κ (DCode.var k i args)) (hd : Kinded κ (DCode.var l j args'))
    (h : ImageEq (DCode.var k i args) (DCode.var l j args')) :
    i = j ∧ ∀ σ, BotEnv σ → argVals args σ = argVals args' σ := by
  by_cases hij : i = j
  · subst hij
    refine ⟨rfl, fun σ hσ => ?_⟩
    have hb := botEnv_upd hσ i (atom_bot 100)
    have h1 := h _ hb
    rw [image_var_atom (upd_self σ i _), image_var_atom (upd_self σ i _), hc.2.2, hd.2.2] at h1
    exact (spineVal_inj (argVals_bot hc.2.1 σ) (argVals_bot hd.2.1 σ) h1).2
  · exfalso
    let σ : REnv := upd (upd (constEnv bottom) i (NeutralPER.neutralAtom 100)) j
      (NeutralPER.neutralAtom 101)
    have hb : BotEnv σ :=
      botEnv_upd (botEnv_upd (σ := constEnv bottom) (fun _ => rfl) i (atom_bot 100)) j (atom_bot 101)
    have hi : σ i = NeutralPER.neutralAtom 100 := by
      show upd _ j _ i = _
      rw [upd_ne _ _ hij, upd_self]
    have hj : σ j = NeutralPER.neutralAtom 101 := upd_self _ _ _
    have h1 := h σ hb
    rw [image_var_atom hi, image_var_atom hj] at h1
    have := (spineVal_inj (argVals_bot hc.2.1 σ) (argVals_bot hd.2.1 σ) h1).1
    cases this

theorem botEnv_const_bottom : BotEnv (constEnv bottom) := fun _ => rfl

/-- Image-equal products have image-equal domains and codomains. -/
theorem pi_parts {a b a' b' : Nat} {A : DCode a} {B : DCode b} {A' : DCode a'} {B' : DCode b'}
    {κ κ' : List (Option (Nat × Nat))} (hB : Kinded κ B) (hB' : Kinded κ' B')
    (h : ImageEq (DCode.pi A B) (DCode.pi A' B')) : ImageEq A A' ∧ ImageEq B B' := by
  refine ⟨fun σ' hσ' => ?_, fun σ' hσ' => ?_⟩
  · exact (InductiveCodes.piValue_injective (image_bot σ' A) (image_bot σ' A')
      (h σ' hσ')).2.1
  · have htail : BotEnv (fun i => σ' (i + 1)) := fun i => hσ' (i + 1)
    have he : rcons (σ' 0) (fun i => σ' (i + 1)) = σ' := by
      funext i
      cases i <;> rfl
    obtain ⟨_, _, hcod⟩ := InductiveCodes.piValue_injective
      (image_bot _ A) (image_bot _ A') (h _ htail)
    have h1 := applyValue_legalGraph_at (codomain_finite B κ hB (fun i => σ' (i + 1)))
      (x := σ' 0) (image_bot _ B)
    have h2 := applyValue_legalGraph_at (codomain_finite B' κ' hB' (fun i => σ' (i + 1)))
      (x := σ' 0) (image_bot _ B')
    rw [he] at h1 h2
    exact h1.symm.trans ((hcod (σ' 0)).trans h2)

theorem univ_level {k j : Nat} {σ : REnv}
    (h : ValueEq (image σ (DCode.univ k)) (image σ (DCode.univ j))) : k = j := by
  have := sort_code_injective h
  injection this

/-- Image-equal kinded codes give their binders the same kind. -/
theorem kind_eq : {k : Nat} → (c : DCode k) → {l : Nat} → (d : DCode l) →
    ∀ κ : List (Option (Nat × Nat)), Kinded κ c → Kinded κ d → ImageEq c d →
    kindOf c = kindOf d
  | _, .var _ _ _, _, .var _ _ _, _, _, _, _ => rfl
  | _, .var _ _ _, _, .univ _, _, _, _, h => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .neutral _ _, _, _, _, h => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .pi _ _, _, _, _, h => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .eq _ _ _ _, _, _, _, h => (var_vs_nonvar' h trivial).elim
  | _, .univ _, _, .var _ _ _, _, _, _, h =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .neutral _ _, _, .var _ _ _, _, _, _, h =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .pi _ _, _, .var _ _ _, _, _, _, h =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .eq _ _ _ _, _, .var _ _ _, _, _, _, h =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .univ _, _, .univ _, _, _, _, h => by
      rw [univ_level (h _ botEnv_const_bottom)]
  | _, .univ _, _, .neutral _ _, _, _, _, h => (sep_univ_neutral (h _ botEnv_const_bottom)).elim
  | _, .univ _, _, .pi _ _, _, _, _, h => (sep_univ_pi (h _ botEnv_const_bottom)).elim
  | _, .univ _, _, .eq _ _ _ _, _, _, _, h => (sep_univ_eq (h _ botEnv_const_bottom)).elim
  | _, .neutral _ _, _, .univ _, _, _, _, h =>
      (sep_univ_neutral (h _ botEnv_const_bottom).symm).elim
  | _, .neutral _ _, _, .neutral _ _, _, _, _, _ => rfl
  | _, .neutral _ _, _, .pi _ _, _, _, _, h => (sep_neutral_pi (h _ botEnv_const_bottom)).elim
  | _, .neutral _ _, _, .eq _ _ _ _, _, _, _, _ => rfl
  | _, .pi _ _, _, .univ _, _, _, _, h => (sep_univ_pi (h _ botEnv_const_bottom).symm).elim
  | _, .pi _ _, _, .neutral _ _, _, _, _, h =>
      (sep_neutral_pi (h _ botEnv_const_bottom).symm).elim
  | _, .pi _ _, _, .eq _ _ _ _, _, _, _, h => (sep_pi_eq (h _ botEnv_const_bottom)).elim
  | _, .eq _ _ _ _, _, .univ _, _, _, _, h => (sep_univ_eq (h _ botEnv_const_bottom).symm).elim
  | _, .eq _ _ _ _, _, .neutral _ _, _, _, _, _ => rfl
  | _, .eq _ _ _ _, _, .pi _ _, _, _, _, h => (sep_pi_eq (h _ botEnv_const_bottom).symm).elim
  | _, .eq _ _ _ _, _, .eq _ _ _ _, _, _, _, _ => rfl
  | _, .pi A B, _, .pi A' B', κ, hc, hd, h => by
      obtain ⟨hA, hB⟩ := pi_parts hc.2 hd.2 h
      have eA := kind_eq A A' κ hc.1 hd.1 hA
      have hd2 : Kinded (kindOf A :: κ) B' := by
        rw [eA]
        exact hd.2
      have eB := kind_eq B B' _ hc.2 hd2 hB
      show kindPi (kindOf A) (kindOf B) = kindPi (kindOf A') (kindOf B')
      rw [eA, eB]

/-! ## Coherence -/

theorem el_var_congr {k i : Nat} {args args' : List TImg} {σ : REnv} {ρ : FEnv}
    (h : argVals args σ = argVals args' σ) :
    El σ ρ (DCode.var k i args) = El σ ρ (DCode.var k i args') := by
  cases k with
  | zero =>
      show (fun x y => ρ i (argVals args σ) x x ∧ ρ i (argVals args σ) y y) =
        (fun x y => ρ i (argVals args' σ) x x ∧ ρ i (argVals args' σ) y y)
      rw [h]
  | succ k =>
      show ρ i (argVals args σ) = ρ i (argVals args' σ)
      rw [h]

theorem eq_args_bot {κ : List (Option (Nat × Nat))} {r a : Nat} {A : DCode a} {s t : TImg}
    (hc : Kinded κ (DCode.eq r A s t)) (σ : REnv) :
    ∀ x ∈ [image σ A, s σ, t σ], x .bot := by
  intro x hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact image_bot σ A
  · exact hc.2.1.2 σ
  · exact hc.2.2.2 σ

/-- Kinded codes with equal raw images in every bot-containing raw
environment have the same reading and the same invariance in every
saturated environment. -/
theorem coherent : {k : Nat} → (c : DCode k) → {l : Nat} → (d : DCode l) →
    ∀ κ : List (Option (Nat × Nat)), Kinded κ c → Kinded κ d → ImageEq c d →
    ∀ σ ρ, SatEnv σ ρ →
      Same (El σ ρ c) (El σ ρ d) ∧ ∀ F F', (Inv σ ρ c F F' ↔ Inv σ ρ d F F')
  | _, .var k i args, _, .var l j args', κ, hc, hd, h, σ, ρ, hs => by
      obtain ⟨rfl, ha⟩ := var_sep hc hd h
      have hkl : some (some (k, args.length)) = some (some (l, args'.length)) := hc.1.symm.trans hd.1
      injection hkl with hkl
      injection hkl with hkl
      injection hkl with hkl _
      subst hkl
      rw [el_var_congr (ha σ hs.2)]
      exact ⟨fun _ _ => Iff.rfl, fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | _, .var _ _ _, _, .univ _, _, _, _, h, _, _, _ => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .neutral _ _, _, _, _, h, _, _, _ => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .pi _ _, _, _, _, h, _, _, _ => (var_vs_nonvar' h trivial).elim
  | _, .var _ _ _, _, .eq _ _ _ _, _, _, _, h, _, _, _ => (var_vs_nonvar' h trivial).elim
  | _, .univ _, _, .var _ _ _, _, _, _, h, _, _, _ =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .neutral _ _, _, .var _ _ _, _, _, _, h, _, _, _ =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .pi _ _, _, .var _ _ _, _, _, _, h, _, _, _ =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .eq _ _ _ _, _, .var _ _ _, _, _, _, h, _, _, _ =>
      (var_vs_nonvar' (fun σ hσ => (h σ hσ).symm) trivial).elim
  | _, .univ _, _, .univ _, _, _, _, h, _, _, _ => by
      rw [univ_level (h _ botEnv_const_bottom)]
      exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | _, .univ _, _, .neutral _ _, _, _, _, h, _, _, _ =>
      (sep_univ_neutral (h _ botEnv_const_bottom)).elim
  | _, .univ _, _, .pi _ _, _, _, _, h, _, _, _ => (sep_univ_pi (h _ botEnv_const_bottom)).elim
  | _, .univ _, _, .eq _ _ _ _, _, _, _, h, _, _, _ =>
      (sep_univ_eq (h _ botEnv_const_bottom)).elim
  | _, .neutral _ _, _, .univ _, _, _, _, h, _, _, _ =>
      (sep_univ_neutral (h _ botEnv_const_bottom).symm).elim
  | _, .neutral _ _, _, .neutral _ _, _, _, _, _, _, _, _ =>
      ⟨fun _ _ => Iff.rfl, fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | _, .neutral _ _, _, .pi _ _, _, _, _, h, _, _, _ =>
      (sep_neutral_pi (h _ botEnv_const_bottom)).elim
  | _, .neutral _ _, _, .eq _ _ _ _, _, _, _, h, _, _, _ =>
      (sep_neutral_eq (h _ botEnv_const_bottom)).elim
  | _, .pi _ _, _, .univ _, _, _, _, h, _, _, _ =>
      (sep_univ_pi (h _ botEnv_const_bottom).symm).elim
  | _, .pi _ _, _, .neutral _ _, _, _, _, h, _, _, _ =>
      (sep_neutral_pi (h _ botEnv_const_bottom).symm).elim
  | _, .pi _ _, _, .eq _ _ _ _, _, _, _, h, _, _, _ => (sep_pi_eq (h _ botEnv_const_bottom)).elim
  | _, .eq _ _ _ _, _, .univ _, _, _, _, h, _, _, _ =>
      (sep_univ_eq (h _ botEnv_const_bottom).symm).elim
  | _, .eq _ _ _ _, _, .neutral _ _, _, _, _, h, _, _, _ =>
      (sep_neutral_eq (h _ botEnv_const_bottom).symm).elim
  | _, .eq _ _ _ _, _, .pi _ _, _, _, _, h, _, _, _ =>
      (sep_pi_eq (h _ botEnv_const_bottom).symm).elim
  | _, .eq r A s t, _, .eq r' A' s' t', κ, hc, hd, h, σ, ρ, hs => by
      have parts : ∀ σ', BotEnv σ' →
          r = r' ∧ [image σ' A, s σ', t σ'] = [image σ' A', s' σ', t' σ'] := fun σ' hσ' => by
        have h1 := h σ' hσ'
        rw [image_eq_tagged, image_eq_tagged] at h1
        exact spineVal_inj (eq_args_bot hc σ') (eq_args_bot hd σ')
          (tagged_inj (Or.inl rfl) h1).2
      have hA : ImageEq A A' := fun σ' hσ' => by
        have h1 := (parts σ' hσ').2
        injection h1 with h1 _
        rw [h1]
        exact ValueEq.refl _
      have he := (parts σ hs.2).2
      injection he with _ he
      injection he with hs' he
      injection he with ht' _
      have ihA := (coherent A A' κ hc.1 hd.1 hA σ ρ hs).1
      refine ⟨fun x y => ?_, fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
      show (x .bot ∧ y .bot ∧ El σ ρ A (s σ) (t σ)) ↔
        (x .bot ∧ y .bot ∧ El σ ρ A' (s' σ) (t' σ))
      rw [← hs', ← ht']
      exact and_congr Iff.rfl (and_congr Iff.rfl (ihA _ _))
  | _, .pi A B, _, .pi A' B', κ, hc, hd, h, σ, ρ, hs => by
      obtain ⟨hA, hB⟩ := pi_parts hc.2 hd.2 h
      have eA := kind_eq A A' κ hc.1 hd.1 hA
      have hd2 : Kinded (kindOf A :: κ) B' := by
        rw [eA]
        exact hd.2
      obtain ⟨sA, iA⟩ := coherent A A' κ hc.1 hd.1 hA σ ρ hs
      have sB : ∀ (z : Value), z .bot → ∀ G, SatFam G →
          Same (El (rcons z σ) (fcons G ρ) B) (El (rcons z σ) (fcons G ρ) B') ∧
            ∀ F F', (Inv (rcons z σ) (fcons G ρ) B F F' ↔ Inv (rcons z σ) (fcons G ρ) B' F F') :=
        fun z hz G hG => coherent B B' _ hc.2 hd2 hB _ _ (satEnv_rcons hs hz hG)
      have lA := el_laws A σ ρ hs
      have bx : ∀ x y, El σ ρ A x y → x .bot ∧ y .bot := fun x y hxy =>
        ⟨el_saturated σ ρ hs A x y hxy, el_saturated σ ρ hs A y x (lA.symm hxy)⟩
      refine ⟨fun f g => ⟨?_, ?_⟩, fun F F' => ⟨?_, ?_⟩⟩
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy G hG hI => ?_⟩
        have hxy' := (sA x y).mpr hxy
        obtain ⟨h1, h2⟩ := hfg x y hxy' G hG ((iA G G).mpr hI)
        exact ⟨((sB x (bx x y hxy').1 G hG).1 _ _).mp h1, ((sB y (bx x y hxy').2 G hG).1 _ _).mp h2⟩
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy G hG hI => ?_⟩
        obtain ⟨h1, h2⟩ := hfg x y ((sA x y).mp hxy) G hG ((iA G G).mp hI)
        exact ⟨((sB x (bx x y hxy).1 G hG).1 _ _).mpr h1, ((sB y (bx x y hxy).2 G hG).1 _ _).mpr h2⟩
      · intro hI x y hxy G hG hIG
        have hxy' := (sA x y).mpr hxy
        exact ((sB x (bx x y hxy').1 G hG).2 _ _).mp (hI x y hxy' G hG ((iA G G).mpr hIG))
      · intro hI x y hxy G hG hIG
        exact ((sB x (bx x y hxy).1 G hG).2 _ _).mpr (hI x y ((sA x y).mp hxy) G hG ((iA G G).mp hIG))

/-! ## Proof irrelevance at level zero -/

/-- Every level-zero code is proof-irrelevant in a saturated environment. -/
theorem el_irrelevant : {k : Nat} → (c : DCode k) → k = 0 → ∀ σ ρ, SatEnv σ ρ →
    ∀ x y, El σ ρ c x x → El σ ρ c y y → El σ ρ c x y
  | _, .var 0 _ _, _, _, _, _, _, _, hx, hy => ⟨hx.1, hy.1⟩
  | _, .var (_ + 1) _ _, hk, _, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hk).elim
  | _, .univ _, hk, _, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hk).elim
  | _, .neutral _ _, _, _, _, _, _, _, hx, hy => ⟨hx.1, hy.1⟩
  | _, .eq _ _ _ _, _, _, _, _, _, _, hx, hy => ⟨hx.1, hy.1, hx.2.2⟩
  | _, @DCode.pi a b A B, hk, σ, ρ, h, x, y, hx, hy => by
      have hb : b = 0 := CandidateTowerCoherence.imaxN_zero' hk
      have lA := el_laws A σ ρ h
      refine ⟨hx.1, hy.2.1, fun u v huv F hF hI => ?_⟩
      have hvu := lA.symm huv
      have hu : u .bot := el_saturated σ ρ h A u v huv
      have hv : v .bot := el_saturated σ ρ h A v u hvu
      have su := satEnv_rcons h hu hF
      have sv := satEnv_rcons h hv hF
      have lu := el_laws B _ _ su
      have lv := el_laws B _ _ sv
      have hxu := (hx.2.2 u u (lA.trans huv hvu) F hF hI).1
      have hyu : El (rcons u σ) (fcons F ρ) B (NeutralPi.applyValue y v)
          (NeutralPi.applyValue y v) := by
        have h2 := (hy.2.2 v u hvu F hF hI).2
        exact lu.trans h2 (lu.symm h2)
      have hxv : El (rcons v σ) (fcons F ρ) B (NeutralPi.applyValue x u)
          (NeutralPi.applyValue x u) := by
        have h2 := (hx.2.2 u v huv F hF hI).2
        exact lv.trans h2 (lv.symm h2)
      have hyv := (hy.2.2 v v (lA.trans hvu huv) F hF hI).1
      exact ⟨el_irrelevant B hb _ _ su _ _ hxu hyu, el_irrelevant B hb _ _ sv _ _ hxv hyv⟩

/-! ## Closed codes -/

theorem argVals_closed {n : Nat} {args : List TImg} (h : ∀ t ∈ args, TClosed n t)
    {σ σ' : REnv} (hσ : ∀ i, i < n → σ i = σ' i) : argVals args σ = argVals args σ' := by
  unfold argVals
  apply List.map_congr_left
  intro t ht
  exact h t ht σ σ' hσ

theorem image_closed : {k : Nat} → (c : DCode k) → ∀ (n : Nat) (σ σ' : REnv),
    ClosedAt n c → (∀ i, i < n → σ i = σ' i) → image σ c = image σ' c
  | _, .var _ i args, _, σ, σ', hc, h => by
      show IotaRecursor.applyAll (withBot (σ i)) (argVals args σ) =
        IotaRecursor.applyAll (withBot (σ' i)) (argVals args σ')
      rw [h i hc.1, argVals_closed hc.2 h]
  | _, .univ _, _, _, _, _, _ => rfl
  | _, .neutral _ _, _, _, _, _, _ => rfl
  | _, .pi A B, n, σ, σ', hc, h => by
      have hA := image_closed A n σ σ' hc.1 h
      have hB : (fun x => image (rcons x σ) B) = (fun x => image (rcons x σ') B) := by
        funext x
        exact image_closed B (n + 1) _ _ hc.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (Nat.lt_of_succ_lt_succ hi))
      show InductiveCodes.piValue _ (image σ A) _ = InductiveCodes.piValue _ (image σ' A) _
      rw [hA, hB]
  | _, .eq r A s t, n, σ, σ', hc, h => by
      show eqImage r (image σ A) (s σ) (t σ) = eqImage r (image σ' A) (s σ') (t σ')
      rw [image_closed A n σ σ' hc.1 h, hc.2.1 σ σ' h, hc.2.2 σ σ' h]

def σ0 : REnv := fun _ => bottom

def botRel : Relation := fun x y => x .bot ∧ y .bot

theorem botRel_sat : Sat botRel := ⟨⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩, fun _ _ h => h.1⟩

def ρ0 : FEnv := fun _ _ => botRel

theorem sat0 : SatEnv σ0 ρ0 := ⟨fun _ _ => botRel_sat, fun _ => rfl⟩

theorem closed_imageEq {k l : Nat} {c : DCode k} {d : DCode l} (hc : ClosedAt 0 c)
    (hd : ClosedAt 0 d) (h : ValueEq (image σ0 c) (image σ0 d)) : ImageEq c d := by
  intro σ _
  rw [image_closed c 0 σ σ0 hc (fun _ hi => absurd hi (Nat.not_lt_zero _)),
    image_closed d 0 σ σ0 hd (fun _ hi => absurd hi (Nat.not_lt_zero _))]
  exact h

theorem closed_level : {k : Nat} → (c : DCode k) → ClosedAt 0 c →
    SortMember (some k) (image σ0 c) ∧ TypeDefined (image σ0 c)
  | _, .var _ _ _, hc => absurd hc.1 (Nat.not_lt_zero _)
  | _, .univ k, _ => ⟨sort_member _ (some k), sort_defined _ (some k)⟩
  | _, .neutral k name, _ =>
      ⟨NativeMemberValues.value_level (some k) name, NativeMemberValues.value_defined (some k) name⟩
  | _, .pi _ _, _ => ⟨InductiveCodes.piValue_level _ _ _, InductiveCodes.piValue_defined _ _ _⟩
  | _, .eq _ _ _ _, _ => ⟨TypeZeroTowerProbe.tagged_level _ _,
      ⟨some 0, .bot, (InductiveCodes.taggedValue_full _ _ .bot).mpr (applyAll_bot _ _ (atom_bot _))⟩⟩

/-! ## The content code system -/

/-- The image-keyed family of closed, kinded content codes, read in the
fixed saturated environment. -/
def family : ImageKeyedCodeSystem.Family where
  Cd := DCode
  ok := fun c => WFc c
  img := fun c => image σ0 c
  rel := fun c => El σ0 ρ0 c
  laws := fun c _ => el_laws c σ0 ρ0 sat0
  level := fun c hc => (closed_level c hc.2).1
  defined := fun c hc => (closed_level c hc.2).2
  coherent := fun c d hc hd h =>
    (coherent c d [] hc.1 hd.1 (closed_imageEq hc.2 hd.2 h) σ0 ρ0 sat0).1
  univ := DCode.univ
  univ_ok := fun _ => ⟨trivial, trivial⟩
  univ_img := fun _ => ValueEq.refl _
  univ_member := fun k => ⟨DCode.univ k, ⟨trivial, trivial⟩, ValueEq.refl _, ValueEq.refl _⟩
  univ_decode := by
    rintro k V W ⟨c, hc, hV, hW⟩
    exact ⟨c, c, hc, hc, hV, hW, fun _ _ => Iff.rfl⟩

def codeSystem : CodeSystem := family.codeSystem

theorem universeTransport : PairedStatements.UniverseTransport codeSystem :=
  family.universeTransport

/-- Level-zero codes are proof-irrelevant. -/
theorem propIrrelevance : PairedStatements.PropIrrelevance codeSystem :=
  family.propIrrelevance (fun c _ x y hx hy => el_irrelevant c rfl σ0 ρ0 sat0 x y hx hy)

/-! ## Content: an empty `False`, and Eq with content -/

/-- `∀ X : Prop, X`. -/
def falseCode : DCode 0 := .pi (.univ 0) (.var 0 0 [])

theorem falseCode_wfc : WFc falseCode :=
  ⟨⟨trivial, rfl, by simp, fun _ _ => rfl⟩, ⟨trivial, Nat.zero_lt_one, by simp⟩⟩

def emptyFam : Fam := fun _ _ _ => False

theorem emptyFam_sat : SatFam emptyFam := fun _ =>
  ⟨⟨fun h => h.elim, fun h _ => h.elim⟩, fun _ _ h => h.elim⟩

theorem neutral_wfc (k : Nat) : WFc (DCode.neutral k 0) := ⟨(by decide : (0 : Nat) ≠ 11), trivial⟩

/-- `∀ X : Prop, X` relates nothing, in every environment. -/
theorem falseCode_empty (σ : REnv) (ρ : FEnv) (x : Value) : ¬ El σ ρ falseCode x x := by
  rintro ⟨_, _, h⟩
  have hu : El σ ρ (DCode.univ 0) (image σ (DCode.neutral 0 0)) (image σ (DCode.neutral 0 0)) :=
    ⟨DCode.neutral 0 0, neutral_wfc 0, ValueEq.refl _, ValueEq.refl _⟩
  exact (h _ _ hu emptyFam emptyFam_sat (fun _ _ => Iff.rfl)).1.1

/-- Every relation the content code system gives the image of `∀ X : Prop, X`
is empty. -/
theorem falseCode_code_empty {k : Option Nat} {R : Relation}
    (h : codeSystem.Code k (image σ0 falseCode) R) (x : Value) : ¬ Member R x := fun hx =>
  falseCode_empty σ0 ρ0 x ((codeSystem.coherent h
    (family.ok_code (c := falseCode) falseCode_wfc (ValueEq.refl _)) x x).mp hx)

/-- The closed content code system admits no `NeutralSupport`: it has a
code with no members. -/
theorem no_neutralSupport (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (S : NeutralExtraction.NeutralSupport (EnvironmentEval.annSemantics codeSystem E H)) :
    False :=
  falseCode_code_empty (family.ok_code (c := falseCode) falseCode_wfc (ValueEq.refl _)) _
    (S.reflect_member (family.ok_code (c := falseCode) falseCode_wfc (ValueEq.refl _)) 0)

/-- An Eq code relates bottom-carrying values exactly when its indices are
related by its type. -/
theorem el_eq_iff (σ : REnv) (ρ : FEnv) (r : Nat) {a : Nat} (A : DCode a) (s t : TImg)
    (h h' : Value) :
    El σ ρ (DCode.eq r A s t) h h' ↔ h .bot ∧ h' .bot ∧ El σ ρ A (s σ) (t σ) := Iff.rfl

theorem const_tok {V : Value} (hV : V .bot) : TOk (fun _ => V) := ⟨const_cont V, fun _ => hV⟩

/-- `Eq Prop P Q` for the named propositions `P`, `Q` (as an index-retaining
family `r`). -/
def eqProp (r p q : Nat) : DCode 0 :=
  .eq r (.univ 0) (fun _ => image σ0 (DCode.neutral 0 p)) (fun _ => image σ0 (DCode.neutral 0 q))

theorem eqProp_wfc (r p q : Nat) : WFc (eqProp r p q) :=
  ⟨⟨trivial, const_tok (image_bot _ _), const_tok (image_bot _ _)⟩,
    ⟨trivial, fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

theorem neutral_names {k n m : Nat} {σ : REnv}
    (h : ValueEq (image σ (DCode.neutral k n)) (image σ (DCode.neutral k m))) : n = m := by
  have h1 := (image_neutral_tagged σ k n).symm.trans (h.trans (image_neutral_tagged σ k m))
  exact (spineVal_inj (by simp) (by simp) (tagged_inj (Or.inl rfl) h1).2).1

/-- Content: `Eq Prop P P` is inhabited (by any bottom-carrying value),
`Eq Prop P Q` is empty for distinct named propositions. -/
theorem eqProp_refl (r : Nat) {p : Nat} (hp : p ≠ 11) : Member (El σ0 ρ0 (eqProp r p p)) bottom :=
  ⟨rfl, rfl, DCode.neutral 0 p, ⟨hp, trivial⟩, ValueEq.refl _, ValueEq.refl _⟩

theorem eqProp_apart (r : Nat) {p q : Nat} (hpq : p ≠ q) (h : Value) :
    ¬ Member (El σ0 ρ0 (eqProp r p q)) h := by
  rintro ⟨_, _, c, _, hV, hW⟩
  exact hpq (neutral_names (hV.trans hW.symm))

end Rcic.Declarative.Ann.LR3.ContentCodes
