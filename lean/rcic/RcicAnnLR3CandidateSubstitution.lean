import rcic.RcicAnnLR3CandidateCodeSystem

/-!
# Renaming and substitution for open Girard codes

Syntactic renaming `ren` and level-respecting simultaneous substitution
`subst` on open codes, with their semantic laws.

- **Raw independence** (`el_raw`). The Girard reading does not depend on the
  raw environment: universes relate images of closed codes, and closed images
  are environment-independent.
- **Kinding** is monotone in the kind context (`kinded_mono`), and is
  preserved by renaming (`kinded_ren`, `kinded_ren_inv`) and by substitution
  (`kinded_subst`).
- **Images.** `image_ren`: renaming is precomposition of the raw
  environment. `image_subst`: substituting kinded variables by codes whose
  images are the environment's entries gives the image in that environment.
- **Interpretations.** `el_ren`: renaming is precomposition of the candidate
  environment. `el_subst`: substituting kinded variables by codes whose
  relations are the candidates' readings gives the reading in that
  candidate environment. `el_subst0`: the single substitution of a code `d`
  for variable zero is reading in the candidate environment extended by the
  relation of `d`, with proof irrelevance at level zero.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateSubstitution

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe CandidateTowerCoherence CandidateCodeSystem

/-! ## Raw independence -/

theorem el_raw {adm : Adm} : {k : Nat} → (c : GCode k) → ∀ (σ σ' : REnv) (ρ : CEnv),
    Same (ElA adm σ ρ c) (ElA adm σ' ρ c)
  | _, .var 0 _, _, _, _ => fun _ _ => Iff.rfl
  | _, .var (_ + 1) _, _, _, _ => fun _ _ => Iff.rfl
  | _, .univ _, σ, σ', _ => fun _ _ => by
      constructor
      · rintro ⟨c, hc, hV, hW⟩
        have he := image_closed c 0 σ σ' (kinded_closed c [] hc)
          (fun _ hi => absurd hi (Nat.not_lt_zero _))
        exact ⟨c, hc, he ▸ hV, he ▸ hW⟩
      · rintro ⟨c, hc, hV, hW⟩
        have he := image_closed c 0 σ' σ (kinded_closed c [] hc)
          (fun _ hi => absurd hi (Nat.not_lt_zero _))
        exact ⟨c, hc, he ▸ hV, he ▸ hW⟩
  | _, .neutral _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi A B, σ, σ', ρ => fun f g => by
      constructor
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_raw A σ σ' ρ x y).mpr hxy) R hR
        exact ⟨(el_raw B _ _ _ _ _).mp h1, (el_raw B _ _ _ _ _).mp h2⟩
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_raw A σ σ' ρ x y).mp hxy) R hR
        exact ⟨(el_raw B _ _ _ _ _).mp h1, (el_raw B _ _ _ _ _).mp h2⟩

/-! ## Renaming -/

def lift (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => r i + 1

def ren : {k : Nat} → (Nat → Nat) → GCode k → GCode k
  | _, r, .var k i => .var k (r i)
  | _, _, .univ k => .univ k
  | _, _, .neutral k name => .neutral k name
  | _, r, .pi A B => .pi (ren r A) (ren (lift r) B)

theorem rcons_lift (x : Value) (σ : Nat → Value) (r : Nat → Nat) :
    (fun i => rcons x σ (lift r i)) = rcons x (fun i => σ (r i)) := by
  funext i
  cases i <;> rfl

theorem ccons_lift (R : Relation) (ρ : CEnv) (r : Nat → Nat) :
    (fun i => ccons R ρ (lift r i)) = ccons R (fun i => ρ (r i)) := by
  funext i
  cases i <;> rfl

theorem image_ren : {k : Nat} → (c : GCode k) → ∀ (r : Nat → Nat) (σ : REnv),
    image σ (ren r c) = image (fun i => σ (r i)) c
  | _, .var _ _, _, _ => rfl
  | _, .univ _, _, _ => rfl
  | _, .neutral _ _, _, _ => rfl
  | _, .pi A B, r, σ => by
      have hB : (fun x => image (rcons x σ) (ren (lift r) B)) =
          (fun x => image (rcons x (fun i => σ (r i))) B) := by
        funext x
        rw [image_ren B (lift r) (rcons x σ), rcons_lift x σ r]
      show InductiveCodes.piValue _ (image σ (ren r A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (ren (lift r) B))) = _
      rw [image_ren A r σ, hB]
      rfl

theorem el_ren {adm : Adm} : {k : Nat} → (c : GCode k) → ∀ (r : Nat → Nat) (σ : REnv)
    (ρ : CEnv), Same (ElA adm σ ρ (ren r c)) (ElA adm σ (fun i => ρ (r i)) c)
  | _, .var 0 _, _, _, _ => fun _ _ => Iff.rfl
  | _, .var (_ + 1) _, _, _, _ => fun _ _ => Iff.rfl
  | _, .univ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .neutral _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi A B, r, σ, ρ => fun f g => by
      have sB : ∀ (x : Value) (R : Relation),
          Same (ElA adm (rcons x σ) (ccons R ρ) (ren (lift r) B))
            (ElA adm (rcons x σ) (ccons R (fun i => ρ (r i))) B) := by
        intro x R
        have h := el_ren (adm := adm) B (lift r) (rcons x σ) (ccons R ρ)
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

/-! ## Kinding -/

theorem kinded_mono : {k : Nat} → (c : GCode k) → ∀ (κ κ' : List (Option Nat)),
    (∀ (i j : Nat), κ[i]? = some (some j) → κ'[i]? = some (some j)) → Kinded κ c → Kinded κ' c
  | _, .var _ i, _, _, h, hc => h i _ hc
  | _, .univ _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, hc => hc
  | _, .pi A B, κ, κ', h, hc =>
      ⟨kinded_mono A κ κ' h hc.1, kinded_mono B _ _ (fun i j => by
        cases i with
        | zero => simp
        | succ i => simpa using h i j) hc.2⟩

theorem kinded_ren : {k : Nat} → (c : GCode k) → ∀ (r : Nat → Nat) (κ κ' : List (Option Nat)),
    (∀ i, κ'[r i]? = κ[i]?) → Kinded κ c → Kinded κ' (ren r c)
  | _, .var _ i, _, _, _, h, hc => (h i).trans hc
  | _, .univ _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, hc => hc
  | _, .pi A B, r, κ, κ', h, hc => by
      refine ⟨kinded_ren A r κ κ' h hc.1, ?_⟩
      have hk : kindOfCode (ren r A) = kindOfCode A := by cases A <;> rfl
      rw [hk]
      exact kinded_ren B (lift r) _ _ (fun i => by
        cases i with
        | zero => simp [lift]
        | succ i => simpa [lift] using h i) hc.2

theorem kinded_ren_inv : {k : Nat} → (c : GCode k) → ∀ (r : Nat → Nat) (κ κ' : List (Option Nat)),
    (∀ i, κ'[r i]? = κ[i]?) → Kinded κ' (ren r c) → Kinded κ c
  | _, .var _ i, _, _, _, h, hc => (h i).symm.trans hc
  | _, .univ _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, hc => hc
  | _, .pi A B, r, κ, κ', h, hc => by
      refine ⟨kinded_ren_inv A r κ κ' h hc.1, ?_⟩
      have hk : kindOfCode (ren r A) = kindOfCode A := by cases A <;> rfl
      have h2 := hc.2
      rw [hk] at h2
      exact kinded_ren_inv B (lift r) _ _ (fun i => by
        cases i with
        | zero => simp [lift]
        | succ i => simpa [lift] using h i) h2

/-! ## Substitution -/

abbrev Subst := (k : Nat) → Nat → GCode k

def liftS (τ : Subst) : Subst
  | k, 0 => .var k 0
  | k, i + 1 => ren Nat.succ (τ k i)

def subst : {k : Nat} → Subst → GCode k → GCode k
  | _, τ, .var k i => τ k i
  | _, _, .univ k => .univ k
  | _, _, .neutral k name => .neutral k name
  | _, τ, .pi A B => .pi (subst τ A) (subst (liftS τ) B)

theorem kindOf_subst {k j : Nat} (τ : Subst) (A : GCode k) (h : kindOfCode A = some j) :
    kindOfCode (subst τ A) = some j := by
  cases A with
  | univ _ => exact h
  | var _ _ => exact Option.noConfusion h
  | neutral _ _ => exact Option.noConfusion h
  | pi _ _ => exact Option.noConfusion h

theorem kinded_subst : {k : Nat} → (c : GCode k) → ∀ (τ : Subst) (κ κ' : List (Option Nat)),
    (∀ j i, κ[i]? = some (some j) → Kinded κ' (τ j i)) → Kinded κ c → Kinded κ' (subst τ c)
  | _, .var _ i, _, _, _, h, hc => h _ i hc
  | _, .univ _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, hc => hc
  | _, .pi A B, τ, κ, κ', h, hc => by
      refine ⟨kinded_subst A τ κ κ' h hc.1, ?_⟩
      refine kinded_subst B (liftS τ) (kindOfCode A :: κ) _ (fun j i hi => ?_) hc.2
      cases i with
      | zero =>
          have hA : kindOfCode A = some j := by simpa using hi
          show (kindOfCode (subst τ A) :: κ')[0]? = some (some j)
          rw [kindOf_subst τ A hA]
          simp
      | succ i =>
          exact kinded_ren _ Nat.succ κ' _ (fun _ => by simp) (h j i (by simpa using hi))

theorem withBot_eq {v : Value} (h : v .bot) : withBot v = v := by
  funext c
  exact propext ⟨fun h' => h'.elim (fun e => e ▸ h) id, Or.inr⟩

/-- Substitution for images: kinded variables go to codes whose images are
the environment's entries. -/
theorem image_subst : {k : Nat} → (c : GCode k) → ∀ (τ : Subst) (κ : List (Option Nat))
    (σ σ' : REnv), (∀ j i, κ[i]? = some (some j) → image σ (τ j i) = withBot (σ' i)) →
    Kinded κ c → image σ (subst τ c) = image σ' c
  | _, .var _ i, _, _, _, _, h, hc => h _ i hc
  | _, .univ _, _, _, _, _, _, _ => rfl
  | _, .neutral _ _, _, _, _, _, _, _ => rfl
  | _, .pi A B, τ, κ, σ, σ', h, hc => by
      have hB : (fun x => image (rcons x σ) (subst (liftS τ) B)) =
          (fun x => image (rcons x σ') B) := by
        funext x
        refine image_subst B (liftS τ) (kindOfCode A :: κ) _ _ (fun j i hi => ?_) hc.2
        cases i with
        | zero => rfl
        | succ i =>
            show image (rcons x σ) (ren Nat.succ (τ j i)) = withBot (σ' i)
            rw [image_ren]
            exact h j i (by simpa using hi)
      show InductiveCodes.piValue _ (image σ (subst τ A))
          (UnifiedPi.legalGraph _ (fun x => image (rcons x σ) (subst (liftS τ) B))) = _
      rw [image_subst A τ κ σ σ' h hc.1, hB]
      rfl

/-- Substitution for interpretations: kinded variables go to codes whose
relations are the readings of the candidates. -/
theorem el_subst {adm : Adm} : {k : Nat} → (c : GCode k) → ∀ (τ : Subst)
    (κ : List (Option Nat)) (σ : REnv) (ρ ρ' : CEnv),
    (∀ j i, κ[i]? = some (some j) → Same (ElA adm σ ρ (τ j i)) (ElA adm σ ρ' (.var j i))) →
    Kinded κ c → Same (ElA adm σ ρ (subst τ c)) (ElA adm σ ρ' c)
  | _, .var _ i, _, _, _, _, _, h, hc => h _ i hc
  | _, .univ _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .neutral _ _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi A B, τ, κ, σ, ρ, ρ', h, hc => fun f g => by
      have sB : ∀ (x : Value) (R : Relation),
          Same (ElA adm (rcons x σ) (ccons R ρ) (subst (liftS τ) B))
            (ElA adm (rcons x σ) (ccons R ρ') B) := by
        intro x R
        refine el_subst B (liftS τ) (kindOfCode A :: κ) _ _ _ (fun j i hi => ?_) hc.2
        cases i with
        | zero => cases j <;> exact fun _ _ => Iff.rfl
        | succ i =>
            intro u v
            have h1 := el_ren (adm := adm) (τ j i) Nat.succ (rcons x σ) (ccons R ρ) u v
            have h2 := el_raw (adm := adm) (τ j i) (rcons x σ) σ ρ u v
            have h3 := h j i (by simpa using hi) u v
            refine h1.trans (h2.trans (h3.trans ?_))
            cases j <;> exact Iff.rfl
      have sA := el_subst A τ κ σ ρ ρ' h hc.1
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

def sub0 {a : Nat} (d : GCode a) : Subst
  | k, 0 => if h : a = k then h ▸ d else .var k 0
  | k, i + 1 => .var k i

theorem sub0_zero {a : Nat} (d : GCode a) : sub0 d a 0 = d := by
  simp [sub0]

theorem kinded_subst0 {a b : Nat} {d : GCode a} {B : GCode b} {κ : List (Option Nat)}
    (hd : Kinded κ d) (hB : Kinded (some a :: κ) B) : Kinded κ (subst (sub0 d) B) :=
  kinded_subst B (sub0 d) _ κ (fun j i hi => by
    cases i with
    | zero =>
        have hj : a = j := by simpa using hi
        subst hj
        rw [sub0_zero]
        exact hd
    | succ i => exact (by simpa using hi : κ[i]? = some (some j))) hB

theorem image_subst0 {a b : Nat} {d : GCode a} {B : GCode b} {κ : List (Option Nat)}
    (hB : Kinded (some a :: κ) B) (σ : REnv) (hd : (image σ d) .bot) :
    image σ (subst (sub0 d) B) = image (rcons (image σ d) σ) B :=
  image_subst B (sub0 d) _ σ _ (fun j i hi => by
    cases i with
    | zero =>
        have hj : a = j := by simpa using hi
        subst hj
        rw [sub0_zero]
        exact (withBot_eq hd).symm
    | succ i => rfl) hB

/-- Reading the substituted code is reading in the candidate environment
extended by the relation of `d`. At level zero this uses proof
irrelevance. -/
theorem el_subst0 {adm : Adm} (ha : AdmLaws adm) {a b : Nat} {d : GCode a} {B : GCode b}
    {κ : List (Option Nat)} (hB : Kinded (some a :: κ) B) (σ : REnv) (ρ : CEnv)
    (hs : SatEnv σ ρ) :
    Same (ElA adm σ ρ (subst (sub0 d) B)) (ElA adm σ (ccons (ElA adm σ ρ d) ρ) B) :=
  el_subst B (sub0 d) _ σ ρ _ (fun j i hi => by
    cases i with
    | zero =>
        have hj : a = j := by simpa using hi
        subst hj
        rw [sub0_zero]
        cases a with
        | zero =>
            have lw := el_laws_open ha d σ ρ hs
            intro x y
            exact ⟨fun h => ⟨lw.trans h (lw.symm h), lw.trans (lw.symm h) h⟩,
              fun ⟨hx, hy⟩ => el_irrelevant ha d rfl σ ρ hs x y hx hy⟩
        | succ _ => exact fun _ _ => Iff.rfl
    | succ i => cases j <;> exact fun _ _ => Iff.rfl) hB

end Rcic.Declarative.Ann.LR3.CandidateSubstitution
