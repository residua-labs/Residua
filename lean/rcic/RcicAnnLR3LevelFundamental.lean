import rcic.RcicAnnLR3LevelReader
import rcic.RcicAnnLR3EqKLikeHook

/-!
# The Fundamental for the hereditary level model

`TypedL E H ν Γ e c` types a source expression `e` by a level code `c`, for
the evaluator `EnvironmentEval.denote E H ν`. Contexts hold type variables
(`ty k`) and term variables (`tm c`). Rules:

- term variables (`var`); type variables used as terms of their universe
  (`tyVar`); any readable type as a term of its universe (`typeTerm`);
- term and type abstraction into `Prop` (`lamTm0`, `lamTy0`) or into a
  positive codomain (`lamTm`, `lamTy`);
- term application at a positive codomain (`appTm`), type application
  (`appTy`, substituting the read argument);
- any term at any level-zero type (`prf`): every proposition is chaotic;
- the K-like J (`jK`): an Eq recursor call has its minor's type, up to twins.

**Fundamental** (`fundamental`), by induction on the derivation: for an
evaluator in which every Eq recursor call computes to its minor (`KLike`),
every saturated candidate environment and every pair of raw environments
realizing the context (`GRL`), the images of the term are related by the
level reading of its type. Type application uses substitution
(`LevelSubstitution`), CR3 (`LevelGirardSystem.el_reflect`) and
`univ_of_reads` (twin closed codes for type variables).

**Target judgments** (`closed_judgment`) in
`annSemantics LevelGirardSystem.codeSystem E H`. Instances: the type-valued
function `λ (X : Prop). X → X : Prop → Prop` (`tyFun_judgment`); its
application to `∀ X : Prop, X → X` is a proposition (`tyFunApp_judgment`),
the `Ty_app` case for type-valued functions; and, in the AnySort Eq
environment with the K-like hook (`eqK_klike`), a large elimination into
`Type` with minor `Prop` is a member of `Type` at every major
(`eq_large_elim_judgment`).

Not claimed: a translation of `HasTyA` derivations into `TypedL`,
conversion, constants other than the Eq recursor, or the remaining
inductive families. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelFundamental

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe (REnv CEnv rcons ccons Sat Adm AdmLaws SatFor satFor_laws Ntr SatEnv
  satEnv_rcons)
open CandidateCodeSystem (σ0 ρ0 sat0 botRel botRel_sat botRel_satFor)
open LevelGirard LevelSubstitution LevelReader

/-! ## Twins and closedness under renaming and substitution -/

theorem twin_ren {k l : Nat} {c : LCode k} {d : LCode l} (h : Twin c d) (r : Nat → Nat) :
    Twin (ren r c) (ren r d) := by
  induction h generalizing r with
  | zero => rename_i c d; cases c <;> cases d <;> exact .zero
  | var k i => exact .var k (r i)
  | univ k => exact .univ k
  | neutral k n => exact .neutral k n
  | pi _ _ ihA ihB => exact .pi (ihA r) (ihB _)

theorem closedAt_mono : {k : Nat} → (c : LCode k) → ∀ {n m : Nat}, n ≤ m → ClosedAt n c →
    ClosedAt m c
  | _, .var0 _, _, _, h, hc => Nat.lt_of_lt_of_le hc h
  | _, .prop _, _, _, h, hc => fun σ σ' hσ => hc σ σ' (fun i hi => hσ i (Nat.lt_of_lt_of_le hi h))
  | _, .pi0 A B, _, _, h, hc => ⟨closedAt_mono A h hc.1, closedAt_mono B (Nat.succ_le_succ h) hc.2⟩
  | _, .var _ _, _, _, h, hc => Nat.lt_of_lt_of_le hc h
  | _, .univ _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _ => trivial
  | _, .pi _ A B, _, _, h, hc => ⟨closedAt_mono A h hc.1, closedAt_mono B (Nat.succ_le_succ h) hc.2⟩

theorem closed_ren_gen : {k : Nat} → (c : LCode k) → ∀ (r : Nat → Nat) (n m : Nat),
    (∀ i, i < n → r i < m) → ClosedAt n c → ClosedAt m (ren r c)
  | _, .var0 _, _, _, _, hr, hc => hr _ hc
  | _, .prop _, r, _, _, hr, hc => fun σ σ' hσ => hc _ _ (fun i hi => hσ (r i) (hr i hi))
  | _, .pi0 A B, r, n, m, hr, hc =>
      ⟨closed_ren_gen A r n m hr hc.1, closed_ren_gen B (CandidateSubstitution.lift r) (n + 1)
        (m + 1) (fun i hi => by
          cases i with
          | zero => simp [CandidateSubstitution.lift]
          | succ i => simp [CandidateSubstitution.lift]; exact hr i (by omega)) hc.2⟩
  | _, .var _ _, _, _, _, hr, hc => hr _ hc
  | _, .univ _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, _ => trivial
  | _, .pi _ A B, r, n, m, hr, hc =>
      ⟨closed_ren_gen A r n m hr hc.1, closed_ren_gen B (CandidateSubstitution.lift r) (n + 1)
        (m + 1) (fun i hi => by
          cases i with
          | zero => simp [CandidateSubstitution.lift]
          | succ i => simp [CandidateSubstitution.lift]; exact hr i (by omega)) hc.2⟩

theorem closed_ren_succ {k : Nat} (c : LCode k) {n : Nat} (hc : ClosedAt n c) :
    ClosedAt (n + 1) (ren Nat.succ c) :=
  closed_ren_gen c Nat.succ n (n + 1) (fun _ hi => Nat.succ_lt_succ hi) hc

theorem closedAt_varCode {n : Nat} : (k i : Nat) → i < n → ClosedAt n (varCode k i)
  | 0, _, h => h
  | _ + 1, _, h => h

theorem closed_subst : {k : Nat} → (c : LCode k) → ∀ (τ : LSubst) (θ : ETrans)
    (κ : List (Option Nat)) (m : Nat),
    (∀ j i, κ[i]? = some (some j) → ClosedAt m (τ j i)) →
    (∀ σ σ' : REnv, (∀ i, i < m → σ i = σ' i) → θ σ = θ σ') →
    Kinded κ c → ClosedAt m (subst τ θ c)
  | _, .var0 i, _, _, _, _, h, _, hc => h 0 i hc
  | _, .prop _, _, _, _, _, _, hθ, _ => fun σ σ' hσ => by
      show _ = _
      simp only [hθ σ σ' hσ]
  | _, .pi0 A B, τ, θ, κ, m, h, hθ, hc =>
      ⟨closed_subst A τ θ κ m h hθ hc.1, closed_subst B (liftS τ) (liftT θ) _ (m + 1)
        (fun j i hi => by
          cases i with
          | zero => exact closedAt_varCode j 0 (Nat.succ_pos m)
          | succ i => exact closed_ren_succ _ (h j i (by simpa using hi)))
        (fun σ σ' hσ => by
          funext i
          cases i with
          | zero => exact hσ 0 (Nat.succ_pos m)
          | succ i =>
              show θ (fun j => σ (j + 1)) i = θ (fun j => σ' (j + 1)) i
              rw [hθ _ _ (fun j hj => hσ (j + 1) (Nat.succ_lt_succ hj))]) hc.2⟩
  | _, .var k i, _, _, _, _, h, _, hc => h (k + 1) i hc
  | _, .univ _, _, _, _, _, _, _, _ => trivial
  | _, .neutral _ _, _, _, _, _, _, _, _ => trivial
  | _, .pi _ A B, τ, θ, κ, m, h, hθ, hc =>
      ⟨closed_subst A τ θ κ m h hθ hc.1, closed_subst B (liftS τ) (liftT θ) _ (m + 1)
        (fun j i hi => by
          cases i with
          | zero => exact closedAt_varCode j 0 (Nat.succ_pos m)
          | succ i => exact closed_ren_succ _ (h j i (by simpa using hi)))
        (fun σ σ' hσ => by
          funext i
          cases i with
          | zero => exact hσ 0 (Nat.succ_pos m)
          | succ i =>
              show θ (fun j => σ (j + 1)) i = θ (fun j => σ' (j + 1)) i
              rw [hθ _ _ (fun j hj => hσ (j + 1) (Nat.succ_lt_succ hj))]) hc.2⟩

theorem twin_subst : {k : Nat} → (c : LCode k) → ∀ (τ τ' : LSubst) (θ θ' : ETrans)
    (κ : List (Option Nat)),
    (∀ j i, κ[i]? = some (some (j + 1)) → Twin (τ (j + 1) i) (τ' (j + 1) i)) →
    Kinded κ c → Twin (subst τ θ c) (subst τ' θ' c)
  | _, .var0 _, _, _, _, _, _, _, _ => .zero
  | _, .prop _, _, _, _, _, _, _, _ => .zero
  | _, .pi0 _ _, _, _, _, _, _, _, _ => .zero
  | _, .var k i, _, _, _, _, _, h, hc => h k i hc
  | _, .univ k, _, _, _, _, _, _, _ => .univ k
  | _, .neutral k n, _, _, _, _, _, _, _ => .neutral k n
  | _, .pi _ A B, τ, τ', θ, θ', κ, h, hc =>
      .pi (twin_subst A τ τ' θ θ' κ h hc.1)
        (twin_subst B (liftS τ) (liftS τ') (liftT θ) (liftT θ') _ (fun j i hi => by
          cases i with
          | zero => exact .var j 0
          | succ i => exact twin_ren (h j i (by simpa using hi)) Nat.succ) hc.2)


/-! ## Typing for the level model -/

inductive Entry where
  | ty (k : Nat)
  | tm {a : Nat} (c : LCode a)

def Entry.kind : Entry → Option Nat
  | .ty k => some k
  | .tm _ => none

def kinds (Γ : List Entry) : List (Option Nat) := Γ.map Entry.kind

def shiftBy (n : Nat) : Nat → Nat := fun j => j + n

/-- The evaluator computes every Eq recursor call to its minor (K-like). -/
def KLike (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (ρ : EnvI) (u : Level) (A a P m b e : ExprA),
    EnvironmentEval.denote E H ν ρ (EqReflectionChoice.jcall u A a P m b e) =
      EnvironmentEval.denote E H ν ρ m

section Typing

variable (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) (ν : Valuation)

inductive TypedL : List Entry → ExprA → {k : Nat} → LCode k → Prop
  | var {Γ : List Entry} {i a : Nat} {c : LCode a} (h : Γ[i]? = some (.tm c))
      (hc : Kinded (kinds (Γ.drop (i + 1))) c) :
      TypedL Γ (.bvar i) (ren (shiftBy (i + 1)) c)
  | tyVar {Γ : List Entry} {i k : Nat} (h : Γ[i]? = some (.ty k)) :
      TypedL Γ (.bvar i) (.univ k)
  | typeTerm {Γ : List Entry} {e : ExprA} {k : Nat} {cE : LCode k}
      (h : ReadsL E H ν (kinds Γ) e cE) : TypedL Γ e (.univ k)
  | lamTm0 {Γ : List Entry} {A body : ExprA} {u : Level} {a : Nat} {cA : LCode a}
      {cB : LCode 0} (hA : ReadsL E H ν (kinds Γ) A cA) (hk : kindOf cA = none)
      (hb : TypedL (.tm cA :: Γ) body cB) : TypedL Γ (.lam A u body) (.pi0 cA cB)
  | lamTm {Γ : List Entry} {A body : ExprA} {u : Level} {a b c : Nat} {cA : LCode a}
      {cB : LCode (b + 1)} (hA : ReadsL E H ν (kinds Γ) A cA) (hk : kindOf cA = none)
      (hb : TypedL (.tm cA :: Γ) body cB) : TypedL Γ (.lam A u body) (.pi c cA cB)
  | lamTy0 {Γ : List Entry} {l u : Level} {body : ExprA} {k : Nat} {cB : LCode 0}
      (hl : eval ν l = some k) (hb : TypedL (.ty k :: Γ) body cB) :
      TypedL Γ (.lam (.sort l) u body) (.pi0 (.univ k) cB)
  | lamTy {Γ : List Entry} {l u : Level} {body : ExprA} {k b c : Nat} {cB : LCode (b + 1)}
      (hl : eval ν l = some k) (hb : TypedL (.ty k :: Γ) body cB) :
      TypedL Γ (.lam (.sort l) u body) (.pi c (.univ k) cB)
  | appTm {Γ : List Entry} {f e : ExprA} {c a b : Nat} {cA : LCode a} {cB : LCode (b + 1)}
      (hf : TypedL Γ f (.pi c cA (ren Nat.succ cB))) (he : TypedL Γ e cA)
      (hcB : Kinded (kinds Γ) cB) : TypedL Γ (.app f e) cB
  | appTy {Γ : List Entry} {f T : ExprA} {c k b : Nat} {cB : LCode (b + 1)} {cT : LCode k}
      (hf : TypedL Γ f (.pi c (.univ k) cB)) (hT : ReadsL E H ν (kinds Γ) T cT) :
      TypedL Γ (.app f T) (subst (sub0 cT) (subT cT) cB)
  | prf {Γ : List Entry} {e : ExprA} {c : LCode 0} (hc : Kinded (kinds Γ) c) : TypedL Γ e c
  | jK {Γ : List Entry} {u : Level} {A a P m b e : ExprA} {k : Nat} {cR cR' : LCode (k + 1)}
      (hm : TypedL Γ m cR) (ht : Twin cR cR') (hk : Kinded (kinds Γ) cR') :
      TypedL Γ (EqReflectionChoice.jcall u A a P m b e) cR'

end Typing

theorem kinds_drop (Γ : List Entry) (n j : Nat) :
    (kinds Γ)[j + n]? = (kinds (Γ.drop n))[j]? := by
  simp [kinds, List.getElem?_drop, Nat.add_comm]

theorem typed_kinded {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {Γ : List Entry} {e : ExprA} {k : Nat} {c : LCode k} (h : TypedL E H ν Γ e c) :
    Kinded (kinds Γ) c := by
  induction h with
  | @var Γ i a c _ hc =>
      exact kinded_ren c (shiftBy (i + 1)) _ _ (fun j => kinds_drop Γ (i + 1) j) hc
  | tyVar _ => trivial
  | typeTerm _ => trivial
  | lamTm0 hA hk _ ih =>
      refine ⟨reads_kinded hA, ?_⟩
      rw [hk]
      exact ih
  | lamTm hA hk _ ih =>
      refine ⟨reads_kinded hA, ?_⟩
      rw [hk]
      exact ih
  | lamTy0 _ _ ih => exact ⟨trivial, ih⟩
  | lamTy _ _ ih => exact ⟨trivial, ih⟩
  | appTm _ _ hcB _ _ => exact hcB
  | appTy _ hT ihf => exact kinded_subst0 (reads_kinded hT) ihf.2
  | prf hc => exact hc
  | jK _ _ hk _ => exact hk

/-! ## Realizing environments -/

def tailV (s : EnvI) : EnvI := fun i => s (i + 1)

def tailC (ρ : CEnv) : CEnv := fun i => ρ (i + 1)

def GRL : List Entry → EnvI → EnvI → CEnv → Prop
  | [], _, _, _ => True
  | .ty k :: Γ, s, s', ρ => ElA SatFor σ0 ρ (.univ k) (s 0) (s' 0) ∧ SatFor (s 0) (s' 0) (ρ 0) ∧
      GRL Γ (tailV s) (tailV s') (tailC ρ)
  | .tm c :: Γ, s, s', ρ => ElA SatFor σ0 (tailC ρ) c (s 0) (s' 0) ∧
      GRL Γ (tailV s) (tailV s') (tailC ρ)

theorem gr_var : (Γ : List Entry) → (i : Nat) → ∀ {a : Nat} {c : LCode a} {s s' : EnvI}
    {ρ : CEnv}, Γ[i]? = some (.tm c) → GRL Γ s s' ρ →
    ElA SatFor σ0 (fun j => ρ (j + (i + 1))) c (s i) (s' i)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | .ty _ :: _, 0, _, _, _, _, _, h, _ => by simp at h
  | .tm c' :: _, 0, _, _, _, _, _, h, hG => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      cases h
      exact hG.1
  | .ty _ :: Γ, i + 1, _, _, _, _, _, h, hG => gr_var Γ i (by simpa using h) hG.2.2
  | .tm _ :: Γ, i + 1, _, _, _, _, _, h, hG => gr_var Γ i (by simpa using h) hG.2

theorem gr_ty : (Γ : List Entry) → (i : Nat) → ∀ {k : Nat} {s s' : EnvI} {ρ : CEnv},
    Γ[i]? = some (.ty k) → GRL Γ s s' ρ → ElA SatFor σ0 ρ0 (.univ k) (s i) (s' i)
  | [], _, _, _, _, _, h, _ => by simp at h
  | .tm _ :: _, 0, _, _, _, _, h, _ => by simp at h
  | .ty k' :: _, 0, _, _, _, _, h, hG => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Entry.ty.injEq] at h
      subst h
      exact hG.1
  | .ty _ :: Γ, i + 1, _, _, _, _, h, hG => gr_ty Γ i (by simpa using h) hG.2.2
  | .tm _ :: Γ, i + 1, _, _, _, _, h, hG => gr_ty Γ i (by simpa using h) hG.2

theorem satEnv0 {ρ : CEnv} (h : ∀ i, Sat (ρ i)) : SatEnv σ0 ρ := ⟨h, fun _ => rfl⟩

theorem gr_facts : (Γ : List Entry) → ∀ {s s' : EnvI} {ρ : CEnv}, (∀ i, Sat (ρ i)) →
    GRL Γ s s' ρ →
    (∀ i, i < Γ.length → s i .bot ∧ s' i .bot) ∧
    (∀ i j, (kinds Γ)[i]? = some (some (j + 1)) → SatFor (s i) (s' i) (ρ i))
  | [], _, _, _, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => by simp [kinds] at h⟩
  | .ty k :: Γ, s, s', ρ, hρ, hG => by
      obtain ⟨hU, hR, hT⟩ := hG
      obtain ⟨h1, h2⟩ := gr_facts Γ (fun i => hρ (i + 1)) hT
      have hs := satEnv0 hρ
      refine ⟨fun i hi => ?_, fun i j hi => ?_⟩
      · cases i with
        | zero =>
            exact ⟨el_saturated σ0 ρ hs (LCode.univ k) _ _ hU,
              el_saturated σ0 ρ hs (LCode.univ k) _ _ ((el_laws satFor_laws _ σ0 ρ hs).symm hU)⟩
        | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi)
      · cases i with
        | zero => exact hR
        | succ i => exact h2 i j (by simpa [kinds] using hi)
  | .tm c :: Γ, s, s', ρ, hρ, hG => by
      obtain ⟨hc, hT⟩ := hG
      obtain ⟨h1, h2⟩ := gr_facts Γ (fun i => hρ (i + 1)) hT
      have hs : SatEnv σ0 (tailC ρ) := satEnv0 (fun i => hρ (i + 1))
      refine ⟨fun i hi => ?_, fun i j hi => ?_⟩
      · cases i with
        | zero =>
            exact ⟨el_saturated σ0 _ hs c _ _ hc,
              el_saturated σ0 _ hs c _ _ ((el_laws satFor_laws c σ0 _ hs).symm hc)⟩
        | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi)
      · cases i with
        | zero => simp [kinds, Entry.kind] at hi
        | succ i => exact h2 i j (by simpa [kinds] using hi)

def consS {k : Nat} (d : LCode k) (τ : LSubst) : LSubst
  | j, 0 => if h : k = j then h ▸ d else varCode j 0
  | j, i + 1 => τ j i

def skipS (τ : LSubst) : LSubst
  | j, 0 => varCode j 0
  | j, i + 1 => τ j i

/-- The type variables of a realized context have closed twin codes, one
for each raw environment. -/
theorem gr_codes : (Γ : List Entry) → ∀ {s s' : EnvI} {ρ : CEnv}, GRL Γ s s' ρ →
    ∃ τ τ' : LSubst, ∀ j i, (kinds Γ)[i]? = some (some j) →
      WFc (τ j i) ∧ WFc (τ' j i) ∧ Twin (τ j i) (τ' j i) ∧
      image σ0 (τ j i) = withBot (s i) ∧ image σ0 (τ' j i) = withBot (s' i)
  | [], _, _, _, _ => ⟨fun j i => varCode j i, fun j i => varCode j i,
      fun _ _ h => by simp [kinds] at h⟩
  | .ty k :: Γ, s, s', _, hG => by
      obtain ⟨⟨c, d, hc, hd, ht, hV, hW⟩, _, hT⟩ := hG
      obtain ⟨τ, τ', hτ⟩ := gr_codes Γ hT
      refine ⟨consS c τ, consS d τ', fun j i hi => ?_⟩
      cases i with
      | zero =>
          have hj : k = j := by simpa [kinds, Entry.kind] using hi
          subst hj
          have e0 : consS c τ k 0 = c := by simp [consS]
          have e1 : consS d τ' k 0 = d := by simp [consS]
          rw [e0, e1, NeutralCodes.valueEq_eq hV, NeutralCodes.valueEq_eq hW,
            withBot_eq (image_bot σ0 c [] hc.1), withBot_eq (image_bot σ0 d [] hd.1)]
          exact ⟨hc, hd, ht, rfl, rfl⟩
      | succ i => exact hτ j i (by simpa [kinds] using hi)
  | .tm _ :: Γ, _, _, _, hG => by
      obtain ⟨τ, τ', hτ⟩ := gr_codes Γ hG.2
      refine ⟨skipS τ, skipS τ', fun j i hi => ?_⟩
      cases i with
      | zero => simp [kinds, Entry.kind] at hi
      | succ i => exact hτ j i (by simpa [kinds] using hi)

/-- The image of a read type at two realizing raw environments is
universe-related. -/
theorem univ_of_reads {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {Γ : List Entry} {s s' : EnvI} {ρ : CEnv} (hG : GRL Γ s s' ρ) {T : ExprA} {k : Nat}
    {cT : LCode k} (hT : ReadsL E H ν (kinds Γ) T cT) (ρ' : CEnv) :
    ElA SatFor σ0 ρ' (.univ k) (EnvironmentEval.denote E H ν s T)
      (EnvironmentEval.denote E H ν s' T) := by
  obtain ⟨τ, τ', hτ⟩ := gr_codes Γ hG
  have hκ := reads_kinded hT
  have himg : ∀ (t : LSubst) (r : EnvI), (∀ j i, (kinds Γ)[i]? = some (some j) →
      WFc (t j i) ∧ image σ0 (t j i) = withBot (r i)) →
      WFc (subst t (fun _ => r) cT) ∧ image σ0 (subst t (fun _ => r) cT) = image r cT := by
    intro t r ht
    refine ⟨⟨kinded_subst cT t (fun _ => r) _ [] (fun j i hi => (ht j i hi).1.1)
      (fun _ => const_cont _) hκ, closed_subst cT t (fun _ => r) _ 0
      (fun j i hi => (ht j i hi).1.2) (fun _ _ _ => rfl) hκ⟩, ?_⟩
    refine image_subst cT t (fun _ => r) _ (fun σ j i hi => ?_) hκ σ0
    rw [image_closed (t j i) 0 σ σ0 (ht j i hi).1.2 (fun _ hl => absurd hl (Nat.not_lt_zero _))]
    exact (ht j i hi).2
  obtain ⟨hd, e1⟩ := himg τ s (fun j i hi => ⟨(hτ j i hi).1, (hτ j i hi).2.2.2.1⟩)
  obtain ⟨hd', e2⟩ := himg τ' s' (fun j i hi => ⟨(hτ j i hi).2.1, (hτ j i hi).2.2.2.2⟩)
  refine ⟨_, _, hd, hd', twin_subst cT τ τ' _ _ _ (fun j i hi => (hτ (j + 1) i hi).2.2.1) hκ, ?_, ?_⟩
  · rw [e1]
    exact reads_image hT s
  · rw [e2]
    exact reads_image hT s'

/-! ## The Fundamental -/

theorem ccons_sat {ρ : CEnv} (h : ∀ i, Sat (ρ i)) {R : Relation} (hR : Sat R) :
    ∀ i, Sat (ccons R ρ i)
  | 0 => hR
  | i + 1 => h i

theorem fundamental {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} (hK : KLike E H)
    {ν : Valuation} {Γ : List Entry} {e : ExprA} {k : Nat} {c : LCode k}
    (h : TypedL E H ν Γ e c) :
    ∀ (s s' : EnvI) (ρ : CEnv), (∀ i, Sat (ρ i)) → GRL Γ s s' ρ →
      ElA SatFor σ0 ρ c (EnvironmentEval.denote E H ν s e) (EnvironmentEval.denote E H ν s' e) := by
  induction h with
  | @var Γ i a c hi _ =>
      intro s s' ρ hρ hG
      have hv := gr_var Γ i hi hG
      have hs : SatEnv σ0 (fun j => ρ (j + (i + 1))) := satEnv0 (fun j => hρ _)
      have hx := el_saturated σ0 _ hs c _ _ hv
      have hy := el_saturated σ0 _ hs c _ _ ((el_laws satFor_laws c σ0 _ hs).symm hv)
      rw [NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image E H ν s i),
        NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image E H ν s' i),
        withBot_eq hx, withBot_eq hy]
      exact (el_ren c (shiftBy (i + 1)) σ0 ρ _ _).mpr hv
  | @tyVar Γ i k hi =>
      intro s s' ρ hρ hG
      have hu := gr_ty Γ i hi hG
      have hs := satEnv0 (ρ := ρ0) (fun _ => botRel_sat)
      have hx := el_saturated σ0 ρ0 hs (LCode.univ k) _ _ hu
      have hy := el_saturated σ0 ρ0 hs (LCode.univ k) _ _
        ((el_laws satFor_laws (LCode.univ k) σ0 ρ0 hs).symm hu)
      rw [NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image E H ν s i),
        NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image E H ν s' i),
        withBot_eq hx, withBot_eq hy]
      exact hu
  | typeTerm hT =>
      intro s s' ρ _ hG
      exact univ_of_reads hG hT ρ
  | lamTm0 _ _ _ _ =>
      intro s s' ρ _ _
      exact ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _⟩
  | lamTy0 _ _ _ =>
      intro s s' ρ _ _
      exact ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _⟩
  | @lamTm Γ A body u a b c cA cB _ _ _ ih =>
      intro s s' ρ hρ hG
      refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _,
        fun x y hxy R hR => ?_⟩
      have hb := ih (EnvI.cons x s) (EnvI.cons y s') (ccons R ρ) (ccons_sat hρ hR.1) ⟨hxy, hG⟩
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application E H ν s A body u x),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application E H ν s' A body u y)]
      exact ⟨(el_raw cB σ0 _ _ _ _).mp hb, (el_raw cB σ0 _ _ _ _).mp hb⟩
  | @lamTy Γ l u body k b c cB _ _ ih =>
      intro s s' ρ hρ hG
      refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _,
        fun x y hxy R hR => ?_⟩
      have hb := ih (EnvI.cons x s) (EnvI.cons y s') (ccons R ρ) (ccons_sat hρ hR.1)
        ⟨hxy, hR, hG⟩
      rw [NeutralCodes.valueEq_eq
          (EnvironmentEval.denote_lambda_application E H ν s (.sort l) body u x),
        NeutralCodes.valueEq_eq
          (EnvironmentEval.denote_lambda_application E H ν s' (.sort l) body u y)]
      exact ⟨(el_raw cB σ0 _ _ _ _).mp hb, (el_raw cB σ0 _ _ _ _).mp hb⟩
  | @appTm Γ f e c a b cA cB _ _ _ ihf ihe =>
      intro s s' ρ hρ hG
      have hF := ihf s s' ρ hρ hG
      have hX := ihe s s' ρ hρ hG
      have h1 := (hF.2.2 _ _ hX botRel (botRel_satFor _ _)).1
      have h2 := (el_ren cB Nat.succ _ _ _ _).mp h1
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s f e),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s' f e)]
      exact (el_raw cB _ σ0 ρ _ _).mp h2
  | @appTy Γ f T c k b cB cT hf hT ihf =>
      intro s s' ρ hρ hG
      have hs := satEnv0 hρ
      have hF := ihf s s' ρ hρ hG
      have hU := univ_of_reads hG hT ρ
      have hκ := reads_kinded hT
      obtain ⟨hbots, hcoup⟩ := gr_facts Γ hρ hG
      have hlen : (kinds Γ).length = Γ.length := List.length_map _ _
      let s₁ : REnv := fun i => if i < Γ.length then s i else bottom
      let s₂ : REnv := fun i => if i < Γ.length then s' i else bottom
      have hcl : ClosedAt Γ.length cT := hlen ▸ reads_closed hT
      have e3 : image s₁ cT = image s cT :=
        image_closed cT _ s₁ s hcl (fun i hi => by simp [s₁, hi])
      have e4 : image s₂ cT = image s' cT :=
        image_closed cT _ s₂ s' hcl (fun i hi => by simp [s₂, hi])
      have hs₁ : SatEnv s₁ ρ := ⟨hρ, fun i => by
        by_cases hi : i < Γ.length
        · simp only [s₁, if_pos hi]
          exact (hbots i hi).1
        · simp only [s₁, if_neg hi]
          rfl⟩
      have hs₂ : ∀ i, s₂ i .bot := fun i => by
        by_cases hi : i < Γ.length
        · simp only [s₂, if_pos hi]
          exact (hbots i hi).2
        · simp only [s₂, if_neg hi]
          rfl
      have hcp : ∀ i j, (kinds Γ)[i]? = some (some (j + 1)) → SatFor (s₁ i) (s₂ i) (ρ i) := by
        intro i j hi
        have hlt : i < Γ.length := hlen ▸ CandidateCodeSystem.lt_of_getElem? _ i _ hi
        simp only [s₁, s₂, if_pos hlt]
        exact hcoup i j hi
      have hR : SatFor (EnvironmentEval.denote E H ν s T) (EnvironmentEval.denote E H ν s' T)
          (ElA SatFor σ0 ρ cT) := by
        refine ⟨⟨el_laws satFor_laws cT σ0 ρ hs, el_saturated σ0 ρ hs cT⟩, fun n m hn hm => ?_⟩
        rw [NeutralCodes.valueEq_eq (reads_image hT s), NeutralCodes.valueEq_eq (reads_image hT s'),
          ← e3, ← e4]
        exact (el_raw cT s₁ σ0 ρ _ _).mp
          (LevelGirardSystem.el_reflect cT (kinds Γ) s₁ s₂ ρ hκ hs₁ hs₂ hcp n m hn hm)
      have h1 := (hF.2.2 _ _ hU _ hR).1
      have h2 := (el_raw cB _ σ0 _ _ _).mp h1
      have hB : Kinded (some k :: kinds Γ) cB := (typed_kinded hf).2
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s f T),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s' f T)]
      exact (el_subst0 hB σ0 ρ _ _).mpr h2
  | @prf Γ e c _ =>
      intro s s' ρ _ _
      rw [el_zero]
      exact ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _⟩
  | jK _ ht _ ih =>
      intro s s' ρ hρ hG
      rw [hK, hK]
      exact (el_twin ht σ0 ρ _ _).mp (ih s s' ρ hρ hG)

/-! ## Target judgments -/

theorem closed_judgment {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} (hK : KLike E H)
    {ν : Valuation} {e T : ExprA} {k : Nat} {c : LCode k} (he : TypedL E H ν [] e c)
    (hT : ReadsL E H ν [] T c) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem E H) ν [] ρ e e T := by
  have hw : WFc c := ⟨reads_kinded hT, reads_closed hT⟩
  have himg : ValueEq (EnvironmentEval.denote E H ν ρ T) (image σ0 c) := by
    rw [image_closed c 0 σ0 ρ hw.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))]
    exact reads_image hT ρ
  have hc := LevelGirardSystem.family.ok_code (c := c) hw himg
  exact ⟨some k, ElA SatFor σ0 ρ0 c, hc, LevelGirardSystem.codeSystem.defined hc,
    fundamental hK he ρ ρ ρ0 (fun _ => botRel_sat) trivial⟩

/-- The K-like Eq hook computes every recursor call to its minor. -/
theorem eqK_klike (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) :
    KLike (SemanticMemberEval.view EqLargeFixture.env)
      (AdmissionUniverseReadback.hook hE EqKLikeHook.eqKHook) :=
  fun ν ρ u A a P m b e => EqKLikeHook.kcall_image hE ν ρ u A a P m b e

/-! ## Instances -/

section Instances

variable {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} {ν : Valuation}

/-- `λ (X : Prop). X → X`, a type-valued function. -/
def tyFun : ExprA := .lam (.sort .zero) (.succ .zero) (.pi (.bvar 0) .zero (.bvar 1) .zero)

/-- `Prop → Prop`. -/
def propToProp : ExprA := .pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)

theorem tyFun_typed : TypedL E H ν [] tyFun (.pi 0 (.univ 0) (.univ 0)) :=
  .lamTy rfl (.typeTerm (.pi0 rfl rfl (.bvar rfl) (.bvar rfl)))

theorem reads_propToProp : ReadsL E H ν [] propToProp (.pi 0 (.univ 0) (.univ 0)) :=
  .pi (u := .succ .zero) (v := .succ .zero) rfl rfl rfl (.sort (l := .zero) rfl)
    (.sort (l := .zero) rfl)

theorem reads_identityType :
    ReadsL E H ν [] ImpredicativePiProbe.identityType
      (.pi0 (.univ 0) (.pi0 (.var0 0) (.var0 1))) :=
  .pi0 (u := .succ .zero) (v := .imax .zero .zero) rfl rfl (.sort (l := .zero) rfl)
    (.pi0 (u := .zero) (v := .zero) rfl rfl (.bvar rfl) (.bvar rfl))

/-- `(λ (X : Prop). X → X) (∀ X : Prop, X → X)`. -/
def tyFunApp : ExprA := .app tyFun ImpredicativePiProbe.identityType

theorem tyFunApp_typed : TypedL E H ν [] tyFunApp (.univ 0) :=
  .appTy (cT := .pi0 (.univ 0) (.pi0 (.var0 0) (.var0 1))) tyFun_typed reads_identityType

/-- The type-valued function is a member of `Prop → Prop` in the Target. -/
theorem tyFun_judgment (hK : KLike E H) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem E H) ν [] ρ
      tyFun tyFun propToProp :=
  closed_judgment hK tyFun_typed reads_propToProp ρ

/-- Its application is a proposition in the Target: the evaluator image is a
level-zero type image. -/
theorem tyFunApp_judgment (hK : KLike E H) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem E H) ν [] ρ
      tyFunApp tyFunApp (.sort .zero) :=
  closed_judgment hK tyFunApp_typed (.sort (l := .zero) rfl) ρ

end Instances

/-- In the AnySort Eq environment, with the K-like hook, a large elimination
into `Type` with minor `Prop` is a member of `Type` at every major `e`. -/
theorem eq_large_elim_judgment (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env)
    (ν : Valuation) (ρ : EnvI) (u : Level) (A a P b e : ExprA) :
    Judgment (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem
        (SemanticMemberEval.view EqLargeFixture.env)
        (AdmissionUniverseReadback.hook hE EqKLikeHook.eqKHook)) ν [] ρ
      (EqReflectionChoice.jcall u A a P (.sort .zero) b e)
      (EqReflectionChoice.jcall u A a P (.sort .zero) b e) (.sort (.succ .zero)) :=
  closed_judgment (eqK_klike hE)
    (.jK (cR := .univ 1) (.typeTerm (.sort (l := .zero) rfl)) (twin_refl _) trivial)
    (.sort (l := .succ .zero) rfl) ρ

end Rcic.Declarative.Ann.LR3.LevelFundamental
