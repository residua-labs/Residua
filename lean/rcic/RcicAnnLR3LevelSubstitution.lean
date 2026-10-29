import rcic.RcicAnnLR3LevelGirardSystem

/-!
# Renaming and substitution for level codes

Opaque level-zero codes `prop img` are carried by their image function, so
renaming and substitution act on them by precomposing `img` with an
environment map: `σ ↦ σ ∘ r` for renaming, and an environment transformer
`θ` for substitution, paired with the codes `τ` substituted for variables.

- Renaming: `image_ren`, `kinded_ren` (joint continuity is kept,
  `cont_ren`), `el_ren`; `kinded_mono`.
- Substitution `subst τ θ`: `image_subst` (the image is the image at the
  transformed environment, when `τ` and `θ` agree on kinded variables),
  `kinded_subst` (for a jointly continuous `θ`, `cont_comp`), `el_subst`
  (level-zero positions are chaotic on both sides).
- Single substitution at variable zero (`sub0`, `subT`): `kinded_subst0`,
  `image_subst0`, `el_subst0`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelSubstitution

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (withBot)
open CandidateTowerProbe (REnv CEnv rcons ccons Sat Adm AdmLaws SatFor satFor_laws SatEnv
  satEnv_rcons)
open CandidateSubstitution (rcons_lift ccons_lift)
open LevelGirard

/-! ## Renaming -/

def ren : {k : Nat} → (Nat → Nat) → LCode k → LCode k
  | _, r, .var0 i => .var0 (r i)
  | _, r, .prop img => .prop (fun σ => img (fun i => σ (r i)))
  | _, r, .pi0 A B => .pi0 (ren r A) (ren (CandidateSubstitution.lift r) B)
  | _, r, .var k i => .var k (r i)
  | _, _, .univ k => .univ k
  | _, _, .neutral k n => .neutral k n
  | _, r, .pi c A B => .pi c (ren r A) (ren (CandidateSubstitution.lift r) B)

theorem image_ren : {k : Nat} → (c : LCode k) → ∀ (r : Nat → Nat) (σ : REnv),
    image σ (ren r c) = image (fun i => σ (r i)) c
  | _, .var0 _, _, _ => rfl
  | _, .prop _, _, _ => rfl
  | _, .pi0 A B, r, σ => by
      have hB : (fun x => image (rcons x σ) (ren (CandidateSubstitution.lift r) B)) =
          (fun x => image (rcons x (fun i => σ (r i))) B) := by
        funext x
        rw [image_ren B (CandidateSubstitution.lift r) (rcons x σ), rcons_lift x σ r]
      show InductiveCodes.piValue _ (image σ (ren r A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (ren (CandidateSubstitution.lift r) B))) = _
      rw [image_ren A r σ, hB]
      rfl
  | _, .var _ _, _, _ => rfl
  | _, .univ _, _, _ => rfl
  | _, .neutral _ _, _, _ => rfl
  | _, .pi _ A B, r, σ => by
      have hB : (fun x => image (rcons x σ) (ren (CandidateSubstitution.lift r) B)) =
          (fun x => image (rcons x (fun i => σ (r i))) B) := by
        funext x
        rw [image_ren B (CandidateSubstitution.lift r) (rcons x σ), rcons_lift x σ r]
      show InductiveCodes.piValue _ (image σ (ren r A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (ren (CandidateSubstitution.lift r) B))) = _
      rw [image_ren A r σ, hB]
      rfl

theorem kindOf_ren {k : Nat} (r : Nat → Nat) (c : LCode k) : kindOf (ren r c) = kindOf c := by
  cases c <;> rfl

/-- Precomposition with a renaming keeps joint continuity. -/
theorem cont_ren {F : REnv → Value} (h : JointCont F) (r : Nat → Nat) :
    JointCont (fun σ => F (fun i => σ (r i))) := by
  intro σ d hd
  obtain ⟨S, hS, kS⟩ := h _ d hd
  refine ⟨S.map (fun p => (r p.1, p.2)), ?_, fun σ' hσ' => kS _ (fun p hp => ?_)⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hS q hq
  · exact hσ' _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem propImg_ren {img : REnv → Value} (h : PropImg img) (r : Nat → Nat) :
    PropImg (fun σ => img (fun i => σ (r i))) :=
  ⟨cont_ren h.cont r, fun _ => h.level _, fun _ => h.defined _, fun _ => h.bot _⟩

theorem kinded_ren : {k : Nat} → (c : LCode k) → ∀ (r : Nat → Nat) (κ κ' : List (Option Nat)),
    (∀ i, κ'[r i]? = κ[i]?) → Kinded κ c → Kinded κ' (ren r c)
  | _, .var0 i, _, _, _, h, hc => (h i).trans hc
  | _, .prop _, r, _, _, _, hc => propImg_ren hc r
  | _, .pi0 A B, r, κ, κ', h, hc => by
      refine ⟨kinded_ren A r κ κ' h hc.1, ?_⟩
      rw [kindOf_ren]
      exact kinded_ren B (CandidateSubstitution.lift r) _ _ (fun i => by
        cases i with
        | zero => simp [CandidateSubstitution.lift]
        | succ i => simpa [CandidateSubstitution.lift] using h i) hc.2
  | _, .var _ i, _, _, _, h, hc => (h i).trans hc
  | _, .univ _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, hc => hc
  | _, .pi _ A B, r, κ, κ', h, hc => by
      refine ⟨kinded_ren A r κ κ' h hc.1, ?_⟩
      rw [kindOf_ren]
      exact kinded_ren B (CandidateSubstitution.lift r) _ _ (fun i => by
        cases i with
        | zero => simp [CandidateSubstitution.lift]
        | succ i => simpa [CandidateSubstitution.lift] using h i) hc.2

theorem el_ren {adm : Adm} : {k : Nat} → (c : LCode k) → ∀ (r : Nat → Nat) (σ : REnv)
    (ρ : CEnv), Same (ElA adm σ ρ (ren r c)) (ElA adm σ (fun i => ρ (r i)) c)
  | _, .var0 _, _, _, _ => fun _ _ => Iff.rfl
  | _, .prop _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi0 _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .var _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .univ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .neutral _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi _ A B, r, σ, ρ => fun f g => by
      have sB : ∀ (x : Value) (R : Relation),
          Same (ElA adm (rcons x σ) (ccons R ρ) (ren (CandidateSubstitution.lift r) B))
            (ElA adm (rcons x σ) (ccons R (fun i => ρ (r i))) B) := by
        intro x R
        have h := el_ren (adm := adm) B (CandidateSubstitution.lift r) (rcons x σ) (ccons R ρ)
        rw [ccons_lift R ρ r] at h
        exact h
      constructor
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_ren A r σ ρ x y).mpr hxy) R hR
        exact ⟨(sB x R _ _).mp h1, (sB y R _ _).mp h2⟩
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_ren A r σ ρ x y).mp hxy) R hR
        exact ⟨(sB x R _ _).mpr h1, (sB y R _ _).mpr h2⟩

/-- Kinding is monotone in the kind context (only universe-bound entries
matter). -/
theorem kinded_mono : {k : Nat} → (c : LCode k) → ∀ (κ κ' : List (Option Nat)),
    (∀ (i j : Nat), κ[i]? = some (some j) → κ'[i]? = some (some j)) → Kinded κ c → Kinded κ' c
  | _, .var0 i, _, _, h, hc => h i _ hc
  | _, .prop _, _, _, _, hc => hc
  | _, .pi0 A B, κ, κ', h, hc =>
      ⟨kinded_mono A κ κ' h hc.1, kinded_mono B _ _ (fun i j => by
        cases i with
        | zero => simp
        | succ i => simpa using h i j) hc.2⟩
  | _, .var _ i, _, _, h, hc => h i _ hc
  | _, .univ _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, hc => hc
  | _, .pi _ A B, κ, κ', h, hc =>
      ⟨kinded_mono A κ κ' h hc.1, kinded_mono B _ _ (fun i j => by
        cases i with
        | zero => simp
        | succ i => simpa using h i j) hc.2⟩

/-! ## Substitution -/

abbrev LSubst := (k : Nat) → Nat → LCode k

/-- An environment transformer: how opaque images see a substituted
environment. -/
abbrev ETrans := REnv → REnv

/-- The variable code of a variable ranging over `Sort k`. -/
def varCode : (k : Nat) → Nat → LCode k
  | 0, i => .var0 i
  | k + 1, i => .var k i

theorem image_varCode (σ : REnv) : (k i : Nat) → image σ (varCode k i) = withBot (σ i)
  | 0, _ => rfl
  | _ + 1, _ => rfl

def liftS (τ : LSubst) : LSubst
  | k, 0 => varCode k 0
  | k, i + 1 => ren Nat.succ (τ k i)

def liftT (θ : ETrans) : ETrans := fun σ => rcons (σ 0) (θ (fun i => σ (i + 1)))

def subst : {k : Nat} → LSubst → ETrans → LCode k → LCode k
  | _, τ, _, .var0 i => τ 0 i
  | _, _, θ, .prop img => .prop (fun σ => img (θ σ))
  | _, τ, θ, .pi0 A B => .pi0 (subst τ θ A) (subst (liftS τ) (liftT θ) B)
  | _, τ, _, .var k i => τ (k + 1) i
  | _, _, _, .univ k => .univ k
  | _, _, _, .neutral k n => .neutral k n
  | _, τ, θ, .pi c A B => .pi c (subst τ θ A) (subst (liftS τ) (liftT θ) B)

theorem liftT_rcons (θ : ETrans) (x : Value) (σ : REnv) :
    liftT θ (rcons x σ) = rcons x (θ σ) := by
  funext i
  cases i <;> rfl

/-- Substitution for images. -/
theorem image_subst : {k : Nat} → (c : LCode k) → ∀ (τ : LSubst) (θ : ETrans)
    (κ : List (Option Nat)),
    (∀ σ j i, κ[i]? = some (some j) → image σ (τ j i) = withBot (θ σ i)) →
    Kinded κ c → ∀ σ, image σ (subst τ θ c) = image (θ σ) c
  | _, .var0 i, _, _, _, h, hc, σ => h σ 0 i hc
  | _, .prop _, _, _, _, _, _, _ => rfl
  | _, .pi0 A B, τ, θ, κ, h, hc, σ => by
      have hB : (fun x => image (rcons x σ) (subst (liftS τ) (liftT θ) B)) =
          (fun x => image (rcons x (θ σ)) B) := by
        funext x
        rw [image_subst B (liftS τ) (liftT θ) (kindOf A :: κ) (fun σ' j i hi => ?_) hc.2 (rcons x σ),
          liftT_rcons]
        cases i with
        | zero => exact image_varCode σ' j 0
        | succ i =>
            show image σ' (ren Nat.succ (τ j i)) = _
            rw [image_ren]
            exact h _ j i (by simpa using hi)
      show InductiveCodes.piValue _ (image σ (subst τ θ A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (subst (liftS τ) (liftT θ) B))) = _
      rw [image_subst A τ θ κ h hc.1 σ, hB]
      rfl
  | _, .var k i, _, _, _, h, hc, σ => h σ (k + 1) i hc
  | _, .univ _, _, _, _, _, _, _ => rfl
  | _, .neutral _ _, _, _, _, _, _, _ => rfl
  | _, .pi _ A B, τ, θ, κ, h, hc, σ => by
      have hB : (fun x => image (rcons x σ) (subst (liftS τ) (liftT θ) B)) =
          (fun x => image (rcons x (θ σ)) B) := by
        funext x
        rw [image_subst B (liftS τ) (liftT θ) (kindOf A :: κ) (fun σ' j i hi => ?_) hc.2 (rcons x σ),
          liftT_rcons]
        cases i with
        | zero => exact image_varCode σ' j 0
        | succ i =>
            show image σ' (ren Nat.succ (τ j i)) = _
            rw [image_ren]
            exact h _ j i (by simpa using hi)
      show InductiveCodes.piValue _ (image σ (subst τ θ A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (subst (liftS τ) (liftT θ) B))) = _
      rw [image_subst A τ θ κ h hc.1 σ, hB]
      rfl

theorem kindOf_subst {k j : Nat} (τ : LSubst) (θ : ETrans) (A : LCode k)
    (h : kindOf A = some j) : kindOf (subst τ θ A) = some j := by
  cases A with
  | univ _ => exact h
  | _ => exact Option.noConfusion h

/-- Composition with a jointly continuous transformer keeps joint continuity. -/
theorem cont_comp {F : REnv → Value} (hF : JointCont F) {θ : ETrans}
    (hθ : ∀ i, JointCont (fun σ => θ σ i)) : JointCont (fun σ => F (θ σ)) := by
  intro σ d hd
  obtain ⟨S, hS, kS⟩ := hF _ d hd
  obtain ⟨T, hT, kT⟩ := combine_reqs σ (fun σ' (p : Nat × CptI) => θ σ' p.1 p.2) S
    (fun p hp => hθ p.1 σ p.2 (hS p hp))
  exact ⟨T, hT, fun σ' hσ' => kS _ (kT σ' hσ')⟩

theorem liftT_cont {θ : ETrans} (hθ : ∀ i, JointCont (fun σ => θ σ i)) :
    ∀ i, JointCont (fun σ => liftT θ σ i)
  | 0 => by
      intro σ d hd
      exact ⟨[(0, d)], by simpa using hd, fun σ' h => h (0, d) (by simp)⟩
  | i + 1 => by
      intro σ d hd
      obtain ⟨S, hS, kS⟩ := hθ i (fun j => σ (j + 1)) d hd
      refine ⟨S.map (fun p => (p.1 + 1, p.2)), fun p hp => ?_, fun σ' hσ' => kS _ (fun p hp => ?_)⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hS q hq
      · exact hσ' _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- Substitution keeps kinding. -/
theorem kinded_subst : {k : Nat} → (c : LCode k) → ∀ (τ : LSubst) (θ : ETrans)
    (κ κ' : List (Option Nat)),
    (∀ j i, κ[i]? = some (some j) → Kinded κ' (τ j i)) → (∀ i, JointCont (fun σ => θ σ i)) →
    Kinded κ c → Kinded κ' (subst τ θ c)
  | _, .var0 i, _, _, _, _, h, _, hc => h 0 i hc
  | _, .prop _, _, _, _, _, _, hθ, hc =>
      ⟨cont_comp hc.cont hθ, fun _ => hc.level _, fun _ => hc.defined _, fun _ => hc.bot _⟩
  | _, .pi0 A B, τ, θ, κ, κ', h, hθ, hc => by
      refine ⟨kinded_subst A τ θ κ κ' h hθ hc.1, ?_⟩
      refine kinded_subst B (liftS τ) (liftT θ) (kindOf A :: κ) _ (fun j i hi => ?_)
        (liftT_cont hθ) hc.2
      cases i with
      | zero =>
          have hA : kindOf A = some j := by simpa using hi
          cases j with
          | zero => show (kindOf (subst τ θ A) :: κ')[0]? = _; rw [kindOf_subst τ θ A hA]; simp
          | succ j => show (kindOf (subst τ θ A) :: κ')[0]? = _; rw [kindOf_subst τ θ A hA]; simp
      | succ i => exact kinded_ren _ Nat.succ κ' _ (fun _ => by simp) (h j i (by simpa using hi))
  | _, .var k i, _, _, _, _, h, _, hc => h (k + 1) i hc
  | _, .univ _, _, _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, _, _, hc => hc
  | _, .pi _ A B, τ, θ, κ, κ', h, hθ, hc => by
      refine ⟨kinded_subst A τ θ κ κ' h hθ hc.1, ?_⟩
      refine kinded_subst B (liftS τ) (liftT θ) (kindOf A :: κ) _ (fun j i hi => ?_)
        (liftT_cont hθ) hc.2
      cases i with
      | zero =>
          have hA : kindOf A = some j := by simpa using hi
          cases j with
          | zero => show (kindOf (subst τ θ A) :: κ')[0]? = _; rw [kindOf_subst τ θ A hA]; simp
          | succ j => show (kindOf (subst τ θ A) :: κ')[0]? = _; rw [kindOf_subst τ θ A hA]; simp
      | succ i => exact kinded_ren _ Nat.succ κ' _ (fun _ => by simp) (h j i (by simpa using hi))

/-- Substitution for readings: positive variables go to codes whose readings
are their candidates. Level-zero positions are chaotic on both sides. -/
theorem el_subst {adm : Adm} : {k : Nat} → (c : LCode k) → ∀ (τ : LSubst) (θ : ETrans)
    (κ : List (Option Nat)) (σ : REnv) (ρ ρ' : CEnv),
    (∀ j i, κ[i]? = some (some (j + 1)) → Same (ElA adm σ ρ (τ (j + 1) i)) (ρ' i)) →
    Kinded κ c → Same (ElA adm σ ρ (subst τ θ c)) (ElA adm σ ρ' c)
  | _, .var0 i, τ, _, _, σ, ρ, _, _, _ => by
      show Same (ElA adm σ ρ (τ 0 i)) chaos
      rw [el_zero]
      exact fun _ _ => Iff.rfl
  | _, .prop _, _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi0 _ _, _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .var k i, _, _, _, _, _, _, h, hc => h k i hc
  | _, .univ _, _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .neutral _ _, _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi _ A B, τ, θ, κ, σ, ρ, ρ', h, hc => fun f g => by
      have sB : ∀ (x : Value) (R : Relation),
          Same (ElA adm (rcons x σ) (ccons R ρ) (subst (liftS τ) (liftT θ) B))
            (ElA adm (rcons x σ) (ccons R ρ') B) := by
        intro x R
        refine el_subst B (liftS τ) (liftT θ) (kindOf A :: κ) _ _ _ (fun j i hi => ?_) hc.2
        cases i with
        | zero => exact fun _ _ => Iff.rfl
        | succ i =>
            intro u v
            have h1 := el_ren (adm := adm) (τ (j + 1) i) Nat.succ (rcons x σ) (ccons R ρ) u v
            have h2 := el_raw (adm := adm) (τ (j + 1) i) (rcons x σ) σ ρ u v
            exact h1.trans (h2.trans (h j i (by simpa using hi) u v))
      have sA := el_subst A τ θ κ σ ρ ρ' h hc.1
      constructor
      · rintro ⟨hf, hg, k⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := k x y ((sA x y).mpr hxy) R hR
        exact ⟨(sB x R _ _).mp h1, (sB y R _ _).mp h2⟩
      · rintro ⟨hf, hg, k⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := k x y ((sA x y).mp hxy) R hR
        exact ⟨(sB x R _ _).mpr h1, (sB y R _ _).mpr h2⟩

/-! ## Single substitution at variable zero -/

def sub0 {a : Nat} (d : LCode a) : LSubst
  | k, 0 => if h : a = k then h ▸ d else varCode k 0
  | k, i + 1 => varCode k i

def subT {a : Nat} (d : LCode a) : ETrans := fun σ => rcons (image σ d) σ

theorem sub0_zero {a : Nat} (d : LCode a) : sub0 d a 0 = d := by
  simp [sub0]

theorem kinded_varCode {κ : List (Option Nat)} : (k i : Nat) → κ[i]? = some (some k) →
    Kinded κ (varCode k i)
  | 0, _, h => h
  | _ + 1, _, h => h

theorem withBot_eq {v : Value} (h : v .bot) : withBot v = v := by
  funext c
  exact propext ⟨fun h' => h'.elim (fun e => e ▸ h) id, Or.inr⟩

theorem subT_cont {a : Nat} (d : LCode a) (κ : List (Option Nat)) (hd : Kinded κ d) :
    ∀ i, JointCont (fun σ => subT d σ i)
  | 0 => image_cont d κ hd
  | i + 1 => by
      intro σ c hc
      exact ⟨[(i, c)], by simpa using hc, fun σ' h => h (i, c) (by simp)⟩

theorem kinded_subst0 {a b : Nat} {d : LCode a} {B : LCode b} {κ : List (Option Nat)}
    (hd : Kinded κ d) (hB : Kinded (some a :: κ) B) :
    Kinded κ (subst (sub0 d) (subT d) B) :=
  kinded_subst B (sub0 d) (subT d) _ κ (fun j i hi => by
    cases i with
    | zero =>
        have hj : a = j := by simpa using hi
        subst hj
        rw [sub0_zero]
        exact hd
    | succ i => exact kinded_varCode j i (by simpa using hi)) (subT_cont d κ hd) hB

theorem image_subst0 {a b : Nat} {d : LCode a} {B : LCode b} {κ : List (Option Nat)}
    (hd : Kinded κ d) (hB : Kinded (some a :: κ) B) (σ : REnv) :
    image σ (subst (sub0 d) (subT d) B) = image (rcons (image σ d) σ) B :=
  image_subst B (sub0 d) (subT d) _ (fun σ' j i hi => by
    cases i with
    | zero =>
        have hj : a = j := by simpa using hi
        subst hj
        rw [sub0_zero]
        exact (withBot_eq (image_bot σ' d κ hd)).symm
    | succ i => exact image_varCode σ' j i) hB σ

theorem el_subst0 {adm : Adm} {a b : Nat} {d : LCode a} {B : LCode b} {κ : List (Option Nat)}
    (hB : Kinded (some a :: κ) B) (σ : REnv) (ρ : CEnv) :
    Same (ElA adm σ ρ (subst (sub0 d) (subT d) B)) (ElA adm σ (ccons (ElA adm σ ρ d) ρ) B) :=
  el_subst B (sub0 d) (subT d) _ σ ρ _ (fun j i hi => by
    cases i with
    | zero =>
        have hj : a = j + 1 := by simpa using hi
        subst hj
        rw [sub0_zero]
        exact fun _ _ => Iff.rfl
    | succ i => exact fun _ _ => Iff.rfl) hB

end Rcic.Declarative.Ann.LR3.LevelSubstitution
