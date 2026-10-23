import rcic.RcicAnnLR3EnvironmentLambdaArms
import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3FunctionSaturation
import rcic.RcicAnnLR3EnvironmentTelescopeInsertion
import rcic.RcicAnnLR3EnvironmentTelescopePorts
import rcic.RcicAnnSubst
import rcic.RcicAnnEnvWf

/-!
# EnvironmentEval lookup/lifting arms — `Ty_bvar`, `Conv_zetaLocal`, `Conv_eta`

The paired lookup group for the environment-aware evaluator
`EnvironmentEval.denote E F ν ρ e = ∃ t, Translation E F ν e t ∧ denI ρ t c`
(the `image` of `annSemantics`).

## Evaluator laws proved here

* `env_denote_bvar` — `denote (.bvar i) = withBottom (ρ i)`: the `cut`
  translation contributes only `.bot`, so a variable's image is its entry
  `.bot`-adjoined, exactly as for the inherited `UnitModel.denote`.
* `env_denote_lift0` —
  `denote ρ (liftA 0 k e) = denote (EnvI.drop ρ k) e` — via the two
  translation-level laws `translation_lift`/`translation_unlift` and the
  inherited `approxI_liftN_intro`/`approxI_liftN_elim`.

## Named premises (discharged where possible)

The relational `Translation` makes both directions of the lift law
nontrivial: constants, literal expansions and family hooks produce native
terms that must be `lift`-fixed.

* `MemberBodyLiftId E` — admitted transparent bodies are `liftA`-fixed at
  every cutoff and amount.  **Discharged from `EnvWfA`** by
  `memberBodyLiftId_of_envWfA` (`envWfA_closed` gives `EnvClosedA`;
  `liftA_instantiateLevelsA_closed` carries closedness across level
  instantiation; the amount iteration is `liftA_zero`/`liftA_comp`, no
  `boundOkB_of_liftA` — that converse lemma is `Classical`-backed), and
  at `internalView E` by `memberBodyLiftId_internalView`
  (`EnvironmentTelescopePorts.internalView_body_conditions`).
* `FamilyLiftId E F` — hook-produced native terms are `lift`-fixed at
  `HookClass` members.  **Discharged** for `neutralFamilySyntax`
  (`familyLiftId_neutral`), for any hook satisfying the named
  `HookLiftFixed` port (`familyLiftId_of_hookLiftFixed`), and at
  `hook E neutralFamilySyntax` by `familyLiftId_hook_neutral`
  (`EnvironmentTelescopePorts.default_hook_conditions`).  Arbitrary hooks
  are NOT assumed — `open_hook_control_inhabited` refutes the raw ports
  for them; only the supplied default hook is instantiated.
* `EnvImageBvarRelL/R` — the `.bot`-adjunction (`withBottom`) closure
  residual, identical in shape to the `UnitModel` route: a property of
  the code relations the `CodePair` assigns, not of `AnnSemantics`.
  At `model E H` it is **discharged, not assumed** — the decoded fibres
  are `CodeI` codes, hence `Saturated` (`InductiveCodes.code_saturated`);
  `envBvarRel{L,R,}_of_code` move the adjunction through `Laws`-
  transitivity.  The contract-facing suppliers carry no residual.
* `Conv_eta`'s `hrt`/`ihrt` (eta-expansion typing IH) are kept in the
  contract but not consumed — matching `InductiveEtaArms.conv_eta_supplied`.

The level conditions (`StoredTypesLevelBounded`,
`StoredBodiesLevelBounded`, `MemberLevelCompatibility`,
`HookEqNCompatible`, `HookEvaluatedArgsCompatible`,
`HookLevelInstantiationCompatible`) are not consumed by the
lookup/lift/eta laws — they serve instantiation-level transport, not
variable lifting.  Hence no whole-expression law here needs the
hereditary `ConstsArityA` premise reserved for laws that do.

## Constant-free transfer

`EnvironmentEval.denote_core` is the landed transfer lemma
(`CoreFree e → ValueEq (denote e) (UnitModel.denote e)`).  `.bvar i` is
`CoreFree`, but the arm proofs stay `CoreFree`-free: `env_denote_bvar` is
a one-`cases` direct proof so no fragment hypothesis sneaks in.

All arm suppliers are conditional consumers — measurements of what each
contract actually needs at this evaluator, not supplies of the general
model contract.  `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvLookup

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open EnvironmentEval FunctionSaturation EnvironmentLambdaArms
open EnvironmentPortConditions EnvironmentTelescopeInsertion
open EnvironmentTelescopePorts

section ClosedAbove

/-- Closed above cutoff `c` as `liftA`-identity at that cutoff. -/
def ClosedAboveA (c : Nat) (e : ExprA) : Prop := ∀ k, liftA c k e = e

/-- Closed above cutoff `c` for native terms. -/
def ClosedAboveN (c : Nat) (t : Expr Nat) : Prop :=
  ∀ k, Rcic.Declarative.lift c k t = t

/-- Fully closed: `liftA`-fixed at every cutoff and amount. -/
def LiftIdA (e : ExprA) : Prop := ∀ c, ClosedAboveA c e

/-- Fully closed native: `lift`-fixed at every cutoff and amount. -/
def LiftIdN (t : Expr Nat) : Prop := ∀ c, ClosedAboveN c t

/-- `lift` of a bvar-sorted application spine with no variables reduces
trivially; the four named native code terms are `lift`-fixed. -/
theorem closedAboveN_cutTerm (c : Nat) : ClosedAboveN c cutTerm :=
  fun _ => rfl

theorem closedAboveN_levelTerm (c : Nat) (i : Option Nat) :
    ClosedAboveN c (levelTerm i) := fun _ => rfl

theorem closedAboveN_sortTerm (c : Nat) (i : Option Nat) :
    ClosedAboveN c (sortTerm i) := fun _ => rfl

theorem lift_taggedTerm (i : Option Nat) (p : Expr Nat) (c k : Nat) :
    Rcic.Declarative.lift c k (taggedTerm i p) =
      taggedTerm i (Rcic.Declarative.lift c k p) := rfl

theorem closedAboveN_app {c : Nat} {f a : Expr Nat}
    (hf : ClosedAboveN c f) (ha : ClosedAboveN c a) :
    ClosedAboveN c (.app f a) := by
  intro k
  show Expr.app (Rcic.Declarative.lift c k f) (Rcic.Declarative.lift c k a) =
    Expr.app f a
  rw [hf k, ha k]

theorem closedAboveN_lam {c : Nat} {A B : Expr Nat}
    (hA : ClosedAboveN c A) (hB : ClosedAboveN (c + 1) B) :
    ClosedAboveN c (.lam A B) := by
  intro k
  show Expr.lam (Rcic.Declarative.lift c k A)
      (Rcic.Declarative.lift (c + 1) k B) = Expr.lam A B
  rw [hA k, hB k]

theorem closedAboveN_pi {c : Nat} {A B : Expr Nat}
    (hA : ClosedAboveN c A) (hB : ClosedAboveN (c + 1) B) :
    ClosedAboveN c (.pi A B) := by
  intro k
  show Expr.pi (Rcic.Declarative.lift c k A)
      (Rcic.Declarative.lift (c + 1) k B) = Expr.pi A B
  rw [hA k, hB k]

theorem closedAboveN_letE {c : Nat} {A v B : Expr Nat}
    (hA : ClosedAboveN c A) (hv : ClosedAboveN c v)
    (hB : ClosedAboveN (c + 1) B) :
    ClosedAboveN c (.letE A v B) := by
  intro k
  show Expr.letE (Rcic.Declarative.lift c k A) (Rcic.Declarative.lift c k v)
      (Rcic.Declarative.lift (c + 1) k B) = Expr.letE A v B
  rw [hA k, hv k, hB k]

theorem closedAboveN_tagged {c : Nat} {i : Option Nat} {p : Expr Nat}
    (h : ClosedAboveN c p) : ClosedAboveN c (taggedTerm i p) := by
  intro k
  rw [lift_taggedTerm, h k]

theorem closedAboveA_app {c : Nat} {f a : ExprA}
    (h : ClosedAboveA c (.app f a)) : ClosedAboveA c f ∧ ClosedAboveA c a :=
  ⟨fun k => (ExprA.app.injEq .. ▸ h k).1, fun k => (ExprA.app.injEq .. ▸ h k).2⟩

theorem closedAboveA_lam {c : Nat} {a : ExprA} {u : Level} {b : ExprA}
    (h : ClosedAboveA c (.lam a u b)) :
    ClosedAboveA c a ∧ ClosedAboveA (c + 1) b :=
  ⟨fun k => (ExprA.lam.injEq .. ▸ h k).1,
    fun k => (ExprA.lam.injEq .. ▸ h k).2.2⟩

theorem closedAboveA_pi {c : Nat} {a : ExprA} {u : Level} {b : ExprA} {v : Level}
    (h : ClosedAboveA c (.pi a u b v)) :
    ClosedAboveA c a ∧ ClosedAboveA (c + 1) b :=
  ⟨fun k => (ExprA.pi.injEq .. ▸ h k).1,
    fun k => (ExprA.pi.injEq .. ▸ h k).2.2.1⟩

theorem closedAboveA_letE {c : Nat} {a w b : ExprA}
    (h : ClosedAboveA c (.letE a w b)) :
    ClosedAboveA c a ∧ ClosedAboveA c w ∧ ClosedAboveA (c + 1) b :=
  ⟨fun k => (ExprA.letE.injEq .. ▸ h k).1,
    fun k => (ExprA.letE.injEq .. ▸ h k).2.1,
    fun k => (ExprA.letE.injEq .. ▸ h k).2.2⟩

/-- `liftA c 0` is always the identity. -/
theorem liftA_zero (c : Nat) (e : ExprA) : liftA c 0 e = e := by
  induction e generalizing c with
  | bvar i =>
      simp only [liftA]
      split
      · exact congrArg ExprA.bvar (Nat.add_zero i)
      · rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA]; rw [ihf, ihx]
  | lam a u b iha ihb => simp only [liftA]; rw [iha, ihb]
  | pi a u b v iha ihb => simp only [liftA]; rw [iha, ihb]
  | letE a w b iha ihw ihb => simp only [liftA]; rw [iha, ihw, ihb]
  | lit n => rfl

/-- Successive same-cutoff lifts compose additively. -/
theorem liftA_comp (c a b : Nat) (e : ExprA) :
    liftA c a (liftA c b e) = liftA c (b + a) e := by
  induction e generalizing c a b with
  | bvar i =>
      simp only [liftA]
      split
      · next hci =>
          have hcb : c ≤ i + b := Nat.le_trans hci (Nat.le_add_right i b)
          simp only [liftA, if_pos hcb]
          exact congrArg ExprA.bvar (Nat.add_assoc i b a)
      · next hci =>
          simp only [liftA, if_neg hci]
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA]; rw [ihf, ihx]
  | lam a u bb iha ihb => simp only [liftA]; rw [iha, ihb]
  | pi a u bb v iha ihb => simp only [liftA]; rw [iha, ihb]
  | letE a w bb iha ihw ihb => simp only [liftA]; rw [iha, ihw, ihb]
  | lit n => rfl

/-- `∀ j, liftA j 1 e = e` fixes every cutoff and amount — the
`boundOkB`-free bridge (`boundOkB_of_liftA` is `Classical`-backed). -/
theorem liftIdA_of_lift1 {e : ExprA} (h : ∀ j, liftA j 1 e = e) : LiftIdA e := by
  intro c k
  induction k with
  | zero => exact liftA_zero c e
  | succ k ih =>
      rw [← liftA_comp c 1 k e, ih]
      exact h c

end ClosedAbove

section Premises

/-- Admitted-body closedness as `liftA`-identity of every transparent
`definitionBody` result.  Discharged from `EnvWfA`; the premise is named
so unrestricted instances of the lift law are not silently assumed. -/
def MemberBodyLiftId (E : ResolvedEnvA) : Prop :=
  ∀ r ls b, definitionBody E r ls = some b → LiftIdA b

/-- Family-hook coherence as `lift`-identity of hook-produced native
terms at `HookClass` members — the amount-lifted form of the supplied
`HookLiftFixed` port.  `neutralFamilySyntax` produces `.const r []`,
which is `lift`-fixed by reflexivity; arbitrary hooks carry the named
residual (`open_hook_control_inhabited` refutes the port for them). -/
def FamilyLiftId (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ ν r ls m, E.members r = some m → HookClass m → LiftIdN (F ν r ls m)

theorem familyLiftId_neutral (E : ResolvedEnvA) :
    FamilyLiftId E neutralFamilySyntax :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- Amount-1 `lift`-fixedness at every cutoff fixes every amount: the
native-side iteration uses the landed `lift_zero_idx` and
`lift_shift_comp_idx` (`Expr Nat` algebra). -/
theorem liftIdN_of_lift1 {t : Expr Nat}
    (h : ∀ c, Rcic.Declarative.lift c 1 t = t) : LiftIdN t := by
  intro c k
  induction k with
  | zero => exact lift_zero_idx c t
  | succ k ih =>
      rw [← lift_shift_comp_idx c k t, ih]
      exact h c

/-- The supplied `HookLiftFixed` port discharges `FamilyLiftId`. -/
theorem familyLiftId_of_hookLiftFixed {E : ResolvedEnvA} {F : FamilySyntax}
    (h : HookLiftFixed E F) : FamilyLiftId E F :=
  fun ν r ls m hm hc => liftIdN_of_lift1 (h ν r ls m hm hc)

theorem natExpandA_liftId (n : Nat) : LiftIdA (natExpandA n) :=
  liftIdA_of_lift1 (liftA_natExpandA_closed n)

theorem liftIdN_rigidTerm {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : FamilyLiftId E F) (ν : Valuation) (r : Nat) (ls : List Level) :
    ∀ c, ClosedAboveN c (rigidTerm E F ν r ls) := by
  intro c k
  unfold rigidTerm
  split
  · rfl
  · next m hm =>
      split
      · next hmc =>
          exact hF ν r ls m hm (.inl hmc) c k
      · next hmc =>
          exact hF ν r ls m hm (.inr (.inl hmc)) c k
      · next hmc =>
          exact hF ν r ls m hm (.inr (.inr hmc)) c k
      · rfl

/-- Admitted bodies are closed under `EnvWfA`: `envWfA_closed` gives the
member body's `liftA`-identity, and `liftA_instantiateLevelsA_closed`
carries it across the level instantiation `definitionBody` performs. -/
theorem memberBodyLiftId_of_envWfA {I : IotaIfaceA} {E : ResolvedEnvA}
    (hW : EnvWfA I E) : MemberBodyLiftId E := by
  intro r ls b hd
  unfold definitionBody at hd
  split at hd
  · nomatch hd
  · rename_i m hm
    split at hd
    · obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some.mp hd
      exact liftIdA_of_lift1
        (liftA_instantiateLevelsA_closed ((envWfA_closed hW r m hm).2 b0 hb0) ls)
    · nomatch hd

end Premises

section TranslationLaws

/-- `Translation` preserves native closedness: a source closed above `c`
translates to natives `lift`-fixed above `c`.  Member bodies come from
`MemberBodyLiftId`; family outputs from `FamilyLiftId`. -/
theorem translation_closedAt {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F) :
    ∀ {e : ExprA} {t : Expr Nat}, Translation E F ν e t →
    ∀ (c : Nat), ClosedAboveA c e → ClosedAboveN c t := by
  intro e t h
  induction h with
  | cut e => exact fun _ _ => closedAboveN_cutTerm _
  | bvar i =>
      intro c hcl
      have h1 := hcl 1
      by_cases hci : c ≤ i
      · simp only [liftA, if_pos hci] at h1
        exact absurd (ExprA.bvar.injEq .. ▸ h1 : i + 1 = i) (by omega)
      · exact fun k => by simp only [Rcic.Declarative.lift, if_neg hci]
  | sort l => exact fun _ _ => closedAboveN_sortTerm _ _
  | constBody hd htr ih => exact fun c _ => ih c (hB _ _ _ hd c)
  | constRigid hr => exact fun c _ => liftIdN_rigidTerm hF _ _ _ c
  | app hf ha ihf iha =>
      exact fun c hcl => closedAboveN_app
        (ihf c (closedAboveA_app hcl).1) (iha c (closedAboveA_app hcl).2)
  | lam hA hb ihA ihb =>
      exact fun c hcl => closedAboveN_lam
        (ihA c (closedAboveA_lam hcl).1) (ihb (c + 1) (closedAboveA_lam hcl).2)
  | pi hA hB' ihA ihB =>
      exact fun c hcl => closedAboveN_tagged
        (closedAboveN_pi (ihA c (closedAboveA_pi hcl).1)
          (ihB (c + 1) (closedAboveA_pi hcl).2))
  | letE hA hv hb ihA ihv ihb =>
      exact fun c hcl => closedAboveN_letE (ihA c (closedAboveA_letE hcl).1)
        (ihv c (closedAboveA_letE hcl).2.1) (ihb (c + 1) (closedAboveA_letE hcl).2.2)
  | lit expanded ih =>
      exact fun c _ => ih c (natExpandA_liftId _ c)

/-- Lift a translation: `Translation e t → Translation (liftA c k e)
(lift c k t)`. -/
theorem translation_lift {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F) :
    ∀ {e : ExprA} {t : Expr Nat}, Translation E F ν e t →
    ∀ c k, Translation E F ν (liftA c k e) (Rcic.Declarative.lift c k t) := by
  intro e t h
  induction h with
  | cut e => exact fun _ _ => .cut _
  | bvar i =>
      intro c k
      by_cases hci : c ≤ i
      · simp only [liftA, Rcic.Declarative.lift, if_pos hci]
        exact .bvar _
      · simp only [liftA, Rcic.Declarative.lift, if_neg hci]
        exact .bvar _
  | sort l => exact fun _ _ => .sort _
  | constBody hd htr ih =>
      intro c k
      exact .constBody hd ((hB _ _ _ hd _ _) ▸ ih c k)
  | constRigid hr =>
      intro c k
      rw [liftIdN_rigidTerm hF ν _ _ c k]
      exact .constRigid hr
  | app hf ha ihf iha => exact fun c k => .app (ihf c k) (iha c k)
  | lam hA hb ihA ihb => exact fun c k => .lam (ihA c k) (ihb (c + 1) k)
  | pi hA hB' ihA ihB =>
      intro c k
      rw [lift_taggedTerm]
      exact .pi (ihA c k) (ihB (c + 1) k)
  | letE hA hv hb ihA ihv ihb =>
      exact fun c k => .letE (ihA c k) (ihv c k) (ihb (c + 1) k)
  | lit expanded ih =>
      intro c k
      exact .lit ((natExpandA_liftId _ _ _) ▸ ih c k)

/-- Every translation of a lifted source is the lift of a translation. -/
theorem translation_unlift {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F) :
    ∀ {e : ExprA} {s : Expr Nat} {c k : Nat},
    Translation E F ν (liftA c k e) s →
    ∃ t, Translation E F ν e t ∧ s = Rcic.Declarative.lift c k t := by
  intro e s c k h
  induction e generalizing s c k with
  | bvar i =>
      by_cases hci : c ≤ i
      · simp only [liftA, if_pos hci] at h
        cases h with
        | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
        | bvar =>
            exact ⟨.bvar i, .bvar _, by
              simp only [Rcic.Declarative.lift, if_pos hci]⟩
      · simp only [liftA, if_neg hci] at h
        cases h with
        | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
        | bvar =>
            exact ⟨.bvar i, .bvar _, by
              simp only [Rcic.Declarative.lift, if_neg hci]⟩
  | sort l =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | sort =>
          exact ⟨sortTerm (eval ν l), .sort _,
            (closedAboveN_sortTerm _ _ _).symm⟩
  | const r ls =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | constBody hd htr =>
          exact ⟨_, .constBody hd htr,
            (translation_closedAt hB hF htr _ (hB _ _ _ hd _) _).symm⟩
      | constRigid hr =>
          exact ⟨_, .constRigid hr, (liftIdN_rigidTerm hF ν r ls _ _).symm⟩
  | app f a ihf iha =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | app hf ha =>
          obtain ⟨tf, htf, hsf⟩ := ihf hf
          obtain ⟨ta, hta, hsa⟩ := iha ha
          exact ⟨.app tf ta, .app htf hta, by
            rw [hsf, hsa]
            rfl⟩
  | lam A u b ihA ihb =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | lam hA' hb' =>
          obtain ⟨tA, htA, hsA⟩ := ihA hA'
          obtain ⟨tb, htb, hsb⟩ := ihb hb'
          exact ⟨.lam tA tb, .lam htA htb, by
            rw [hsA, hsb]
            rfl⟩
  | pi A u B v ihA ihB =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | pi hA' hB' =>
          obtain ⟨tA, htA, hsA⟩ := ihA hA'
          obtain ⟨tB, htB, hsB⟩ := ihB hB'
          exact ⟨taggedTerm (eval ν (.imax u v)) (.pi tA tB), .pi htA htB,
            by
              rw [hsA, hsB, lift_taggedTerm]
              rfl⟩
  | letE A v b ihA ihv ihb =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | letE hA' hv' hb' =>
          obtain ⟨tA, htA, hsA⟩ := ihA hA'
          obtain ⟨tv, htv, hsv⟩ := ihv hv'
          obtain ⟨tb, htb, hsb⟩ := ihb hb'
          exact ⟨.letE tA tv tb, .letE htA htv htb, by
            rw [hsA, hsv, hsb]
            rfl⟩
  | lit n =>
      cases h with
      | cut => exact ⟨cutTerm, .cut _, (closedAboveN_cutTerm _ _).symm⟩
      | lit expanded =>
          exact ⟨_, .lit expanded,
            (translation_closedAt hB hF expanded _
              (natExpandA_liftId _ _) _).symm⟩

end TranslationLaws

section DenoteLaws

/-- The actual environment-aware image of a variable is its entry
`.bot`-adjoined — identical in shape to the `UnitModel` law. -/
theorem env_denote_bvar (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (i : Nat) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.bvar i)) (withBottom (ρ i)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut => exact Or.inl (cutTerm_only_bottom hc)
    | bvar => exact approxI_bvar_inv hc
  · intro hc
    rcases hc with rfl | h
    · exact denote_bot E F ν ρ _
    · exact ⟨.bvar i, .bvar i, ApproxI.bvar h⟩

/-- The environment-aware image transports source lifts into dropped
environments, under the named closedness/coherence premises. -/
theorem env_denote_lift0 {E : ResolvedEnvA} {F : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F)
    (ν : Valuation) (ρ : EnvI) (k : Nat) (e : ExprA) :
    ValueEq (EnvironmentEval.denote E F ν ρ (liftA 0 k e))
      (EnvironmentEval.denote E F ν (EnvI.drop ρ k) e) := by
  intro c
  constructor
  · rintro ⟨s, htr, hc⟩
    obtain ⟨t, ht, rfl⟩ := translation_unlift hB hF htr
    exact ⟨t, ht, approxI_liftN_elim ρ k hc⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨Rcic.Declarative.lift 0 k t, translation_lift hB hF ht 0 k,
      approxI_liftN_intro ρ k hc⟩

end DenoteLaws

section ImageLaws

/-- Stored-type lift transport for a semantics `M`: `image` of the
`k`-lifted stored declaration equals `image` in the `k`-dropped tail
environment.  Same contract shape as the `UnitModel` route. -/
def EnvImageLiftLaw (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (k : Nat) (e : ExprA),
    M.image ν Γ ρ (liftA 0 k e) = M.image ν (Γ.drop k) (EnvI.drop ρ k) e

/-- Left entry-relatedness of variable images at `M`.  The named
residual: at `EnvironmentEval.denote` it is `withBottom`-closure of the
code relation on the left argument. -/
def EnvImageBvarRelL (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (i : Nat) (R : Relation)
    (x W : Value), ρ i = x → R x W → R (M.image ν Γ ρ (.bvar i)) W

/-- The mirror law on the right argument. -/
def EnvImageBvarRelR (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (i : Nat) (R : Relation)
    (W y : Value), ρ i = y → R W y → R W (M.image ν Γ ρ (.bvar i))

/-- `EnvImageLiftLaw` is discharged for the environment-aware image under
the named closedness/coherence premises. -/
theorem envImageLiftLaw {E : ResolvedEnvA} {F : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F) (C : CodeSystem) :
    EnvImageLiftLaw (annSemantics C E F) :=
  fun ν Γ ρ k e =>
    NeutralCodes.valueEq_eq (env_denote_lift0 hB hF ν ρ k e)

/-- At `EnvironmentEval.denote` the left residual is `withBottom`-closure
of the assigned relation — not derivable for arbitrary `R`; it holds for
relations between `.bot`-closed values. -/
theorem envBvarRelL_of_withBottom {C : CodeSystem} {E : ResolvedEnvA}
    {F : FamilySyntax}
    (hbot : ∀ (R : Relation) (x W : Value), R x W → R (withBottom x) W) :
    EnvImageBvarRelL (annSemantics C E F) :=
  fun ν Γ ρ i R x W hx hR => by
  subst hx
  change R (EnvironmentEval.denote E F ν ρ (.bvar i)) W
  exact NeutralCodes.valueEq_eq (env_denote_bvar E F ν ρ i) ▸ hbot _ _ _ hR

/-- The right-argument analogue. -/
theorem envBvarRelR_of_withBottom {C : CodeSystem} {E : ResolvedEnvA}
    {F : FamilySyntax}
    (hbot : ∀ (R : Relation) (W y : Value), R W y → R W (withBottom y)) :
    EnvImageBvarRelR (annSemantics C E F) :=
  fun ν Γ ρ i R W y hy hR => by
  subst hy
  change R W (EnvironmentEval.denote E F ν ρ (.bvar i))
  exact NeutralCodes.valueEq_eq (env_denote_bvar E F ν ρ i) ▸ hbot _ _ _ hR

/-- Left entry-relatedness of a variable image at `model E H`, discharged
with no residual premise: the decoded left fibre is a `CodeI` code, hence
`Saturated` (`InductiveCodes.code_saturated`), and `Laws`-transitivity
moves the `withBottom` adjunction through the entry relation. -/
theorem envBvarRelL_of_code {E : ResolvedEnvA} {H : FamilySyntax}
    {k : Option Nat} {V : Value} {R : Relation} (hcode : InductiveCodes.CodeI k V R)
    {ν : Valuation} {Γ : LCtxA} {ρ : EnvI} {i : Nat} {x W : Value}
    (hx : ρ i = x) (hR : R x W) :
    R ((model E H).image ν Γ ρ (.bvar i)) W := by
  subst hx
  change R (EnvironmentEval.denote E H ν ρ (.bvar i)) W
  rw [NeutralCodes.valueEq_eq (env_denote_bvar E H ν ρ i)]
  have hL : Laws R := InductiveCodes.code_laws hcode
  exact hL.trans (InductiveCodes.code_saturated hcode (ρ i)
    (TypedPER.left_member hL hR)) hR

/-- The right-argument analogue, discharged the same way. -/
theorem envBvarRelR_of_code {E : ResolvedEnvA} {H : FamilySyntax}
    {k : Option Nat} {V : Value} {R : Relation} (hcode : InductiveCodes.CodeI k V R)
    {ν : Valuation} {Γ : LCtxA} {ρ : EnvI} {i : Nat} {W y : Value}
    (hy : ρ i = y) (hR : R W y) :
    R W ((model E H).image ν Γ ρ (.bvar i)) := by
  subst hy
  change R W (EnvironmentEval.denote E H ν ρ (.bvar i))
  rw [NeutralCodes.valueEq_eq (env_denote_bvar E H ν ρ i)]
  have hL : Laws R := InductiveCodes.code_laws hcode
  exact hL.trans hR (hL.symm (InductiveCodes.code_saturated hcode (ρ i)
    (TypedPER.right_member hL hR)))

/-- Both-sided adjunction at once via `saturated_related`. -/
theorem envBvarRel_of_code {E : ResolvedEnvA} {H : FamilySyntax}
    {k : Option Nat} {V : Value} {R : Relation} (hcode : InductiveCodes.CodeI k V R)
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI} {i : Nat} {x y : Value}
    (hx : ρ i = x) (hy : σ i = y) (hR : R x y) :
    R ((model E H).image ν Γ ρ (.bvar i))
      ((model E H).image μ Γ σ (.bvar i)) := by
  subst hx; subst hy
  change R (EnvironmentEval.denote E H ν ρ (.bvar i))
    (EnvironmentEval.denote E H μ σ (.bvar i))
  rw [NeutralCodes.valueEq_eq (env_denote_bvar E H ν ρ i),
      NeutralCodes.valueEq_eq (env_denote_bvar E H μ σ i)]
  exact saturated_related (InductiveCodes.code_laws hcode)
    (InductiveCodes.code_saturated hcode) hR

end ImageLaws

section Lookup

/-- Paired entry extraction at an assumption declaration (model-generic,
ported from the `UnitModel` route). -/
theorem envPairedRealises_entry_assumption {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI}
    (h : PairedRealises M ν μ Γ ρ σ) :
    ∀ {i : Nat} {A : ExprA}, Γ.get? i = some (.assumption A) →
    ∃ (x y : Value) (k : Option Nat) (R S : Relation),
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) A)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) A) R S := by
  induction h with
  | nil ρ σ => intro i A hget; nomatch hget
  | @assumption Γᵢ ρᵢ σᵢ Aᵢ x y k R S tail codes related ih =>
    intro i A' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.assumption Aᵢ :: Γᵢ).get? 0 =
          some (.assumption Aᵢ) := rfl
      rw [hz] at hget
      obtain rfl : Aᵢ = A' := by simpa using hget
      exact ⟨x, y, k, R, S, rfl, rfl, related, codes⟩
    | succ j => exact ih hget
  | @letBinding Γᵢ ρᵢ σᵢ Aᵢ vᵢ x y k R S tail codes related lv rv ih =>
    intro i A' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.letBinding Aᵢ vᵢ :: Γᵢ).get? 0 =
          some (.letBinding Aᵢ vᵢ) := rfl
      rw [hz] at hget
      exact LocalDeclA.noConfusion (Option.some.inj hget)
    | succ j => exact ih hget

/-- Paired entry extraction at a stored-let declaration (model-generic). -/
theorem envPairedRealises_entry_letBinding {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI}
    (h : PairedRealises M ν μ Γ ρ σ) :
    ∀ {i : Nat} {A v : ExprA}, Γ.get? i = some (.letBinding A v) →
    ∃ (x y : Value) (k : Option Nat) (R S : Relation),
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) A)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) A) R S ∧
      R x (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) v) ∧
      S y (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) v) := by
  induction h with
  | nil ρ σ => intro i A v hget; nomatch hget
  | @assumption Γᵢ ρᵢ σᵢ Aᵢ x y k R S tail codes related ih =>
    intro i A' v' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.assumption Aᵢ :: Γᵢ).get? 0 =
          some (.assumption Aᵢ) := rfl
      rw [hz] at hget
      exact LocalDeclA.noConfusion (Option.some.inj hget)
    | succ j => exact ih hget
  | @letBinding Γᵢ ρᵢ σᵢ Aᵢ vᵢ x y k R S tail codes related lv rv ih =>
    intro i A' v' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.letBinding Aᵢ vᵢ :: Γᵢ).get? 0 =
          some (.letBinding Aᵢ vᵢ) := rfl
      rw [hz] at hget
      obtain ⟨rfl, rfl⟩ : Aᵢ = A' ∧ vᵢ = v' := by simpa using hget
      exact ⟨x, y, k, R, S, rfl, rfl, related, codes, lv, rv⟩
    | succ j => exact ih hget

/-- Paired lookup at `lookupTypeA` (model-generic). -/
theorem envPairedRealises_lookupType {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {i : Nat} {A : ExprA}
    (h : PairedRealises M ν μ Γ ρ σ) (hlook : lookupTypeA Γ i = some A) :
    ∃ (a : ExprA) (x y : Value) (k : Option Nat) (R S : Relation),
      A = liftA 0 (i + 1) a ∧ ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) a)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) a) R S := by
  unfold lookupTypeA at hlook
  cases hd : Γ.get? i with
  | none => rw [hd] at hlook; nomatch hlook
  | some d =>
    cases d with
    | assumption a =>
      rw [hd] at hlook
      simp only [Option.some.injEq] at hlook
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc⟩ :=
        envPairedRealises_entry_assumption h hd
      exact ⟨a, x, y, k, R, S, hlook.symm, hx, hy, hrel, hc⟩
    | letBinding a v =>
      rw [hd] at hlook
      simp only [Option.some.injEq] at hlook
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc, -, -⟩ :=
        envPairedRealises_entry_letBinding h hd
      exact ⟨a, x, y, k, R, S, hlook.symm, hx, hy, hrel, hc⟩

/-- Paired lookup at a stored-let (model-generic). -/
theorem envPairedRealises_lookupValueType {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {i : Nat} {A v : ExprA}
    (h : PairedRealises M ν μ Γ ρ σ)
    (hval : lookupValueA Γ i = some v) (hty : lookupTypeA Γ i = some A) :
    ∃ (a vd : ExprA) (x y : Value) (k : Option Nat) (R S : Relation),
      A = liftA 0 (i + 1) a ∧ v = liftA 0 (i + 1) vd ∧
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) a)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) a) R S ∧
      R x (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) vd) ∧
      S y (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) vd) := by
  unfold lookupValueA at hval
  unfold lookupTypeA at hty
  cases hd : Γ.get? i with
  | none => rw [hd] at hval; nomatch hval
  | some d =>
    cases d with
    | assumption a => rw [hd] at hval; nomatch hval
    | letBinding a vd =>
      rw [hd] at hval
      rw [hd] at hty
      simp only [Option.some.injEq] at hval hty
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc, hlv, hrv⟩ :=
        envPairedRealises_entry_letBinding h hd
      exact ⟨a, vd, x, y, k, R, S, hty.symm, hval.symm, hx, hy, hrel, hc,
        hlv, hrv⟩

end Lookup

section Arms

/-- `PairedArms.Ty_bvar` at the environment-aware model — conditional
consumer.  Same contract shape as the `UnitModel` route; the residual is
`EnvImageBvarRelL/R` (`withBottom`-closure of the code relations). -/
theorem paired_env_ty_bvar_of_laws {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hlift : EnvImageLiftLaw M) (hbL : EnvImageBvarRelL M)
    (hbR : EnvImageBvarRelR M) :
    PairedArms.Ty_bvar M E I n := by
  intro Γ i A u hlook _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, x, y, k, R, S, hA, hx, hy, hrel, hcode⟩ :=
    envPairedRealises_lookupType hreal hlook
  subst hA
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · rw [hlift]
    exact hcode.left_code
  · rw [hlift]
    exact hcode.right_code
  · exact hbR μ Γ σ i R _ y hy
      (hbL ν Γ ρ i R x y hx hrel)

/-- `PairedArms.Conv_zetaLocal` at the environment-aware model —
conditional consumer; `EnvImageBvarRelL` is the named residual. -/
theorem paired_env_conv_zetaLocal_of_laws {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hlift : EnvImageLiftLaw M) (hbL : EnvImageBvarRelL M) :
    PairedArms.Conv_zetaLocal M E I n := by
  intro Γ i A v hval hty _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, vd, x, y, k, R, S, hA, hv, hx, hy, hrel, hcode, _hlv, hrv⟩ :=
    envPairedRealises_lookupValueType hreal hval hty
  subst hA
  subst hv
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · rw [hlift]
    exact hcode.left_code
  · rw [hlift]
    exact hcode.right_code
  · rw [hlift]
    exact hbL ν Γ ρ i R x _ hx
      ((M.lawful hcode.left_code).trans hrel (hcode.to_left hrv))

/-- `Ty_bvar` at `model E H` — no `withBottom`-closure premise: the
decoded left fibre is a `CodeI` code, so `code_saturated` discharges the
adjunction at the entry relation.  The `withBottom`-adjunction shape used
by the generic `of_laws` consumer is what `code_saturated` supplies —
there is no missing supplier. -/
theorem paired_env_ty_bvar {E : ResolvedEnvA} {H : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E H)
    {I : IotaIfaceA} {n : Nat} :
    PairedArms.Ty_bvar (model E H) E I n := by
  intro Γ i A u hlook _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, x, y, k, R, S, hA, hx, hy, hrel, hcode⟩ :=
    envPairedRealises_lookupType hreal hlook
  subst hA
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · change InductiveCodes.CodeI k (EnvironmentEval.denote E H ν ρ (liftA 0 (i + 1) a)) R
    rw [NeutralCodes.valueEq_eq (env_denote_lift0 hB hF ν ρ (i + 1) a)]
    exact hcode.left_code
  · change InductiveCodes.CodeI k (EnvironmentEval.denote E H μ σ (liftA 0 (i + 1) a)) S
    rw [NeutralCodes.valueEq_eq (env_denote_lift0 hB hF μ σ (i + 1) a)]
    exact hcode.right_code
  · exact envBvarRel_of_code hcode.left_code hx hy hrel

/-- `Conv_zetaLocal` at `model E H` — same discharge, left adjunction only. -/
theorem paired_env_conv_zetaLocal {E : ResolvedEnvA} {H : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E H)
    {I : IotaIfaceA} {n : Nat} :
    PairedArms.Conv_zetaLocal (model E H) E I n := by
  intro Γ i A v hval hty _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, vd, x, y, k, R, S, hA, hv, hx, hy, hrel, hcode, _hlv, hrv⟩ :=
    envPairedRealises_lookupValueType hreal hval hty
  subst hA
  subst hv
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · change InductiveCodes.CodeI k (EnvironmentEval.denote E H ν ρ (liftA 0 (i + 1) a)) R
    rw [NeutralCodes.valueEq_eq (env_denote_lift0 hB hF ν ρ (i + 1) a)]
    exact hcode.left_code
  · change InductiveCodes.CodeI k (EnvironmentEval.denote E H μ σ (liftA 0 (i + 1) a)) S
    rw [NeutralCodes.valueEq_eq (env_denote_lift0 hB hF μ σ (i + 1) a)]
    exact hcode.right_code
  · change R (EnvironmentEval.denote E H ν ρ (.bvar i))
      (EnvironmentEval.denote E H μ σ (liftA 0 (i + 1) vd))
    rw [NeutralCodes.valueEq_eq (env_denote_bvar E H ν ρ i),
        NeutralCodes.valueEq_eq (env_denote_lift0 hB hF μ σ (i + 1) vd)]
    subst hx
    have hL : Laws R := InductiveCodes.code_laws hcode.left_code
    exact hL.trans (InductiveCodes.code_saturated hcode.left_code (ρ i)
      (TypedPER.left_member hL
        (hL.trans hrel (hcode.to_left hrv))))
      (hL.trans hrel (hcode.to_left hrv))

end Arms

section Eta

/-- Environment-aware eta application: `applyValue` of the eta-expanded
image at `x` is `applyValue` of the function's image at `withBottom x`.
The rewrite chain is `denote_lambda_application` → `denote_application`
→ `env_denote_lift0` (`drop (cons x ρ) 1 = ρ`) → `env_denote_bvar`. -/
theorem env_denote_eta_withBottom_application {E : ResolvedEnvA}
    {F : FamilySyntax} (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F)
    (ν : Valuation) (ρ : EnvI) (A f : ExprA) (u : Level) (x : Value) :
    ValueEq
      (NeutralPi.applyValue
        (EnvironmentEval.denote E F ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0)))) x)
      (NeutralPi.applyValue (EnvironmentEval.denote E F ν ρ f) (withBottom x)) := by
  apply (denote_lambda_application E F ν ρ A (.app (liftA 0 1 f) (.bvar 0))
      u x).trans
  apply (denote_application E F ν (EnvI.cons x ρ) (liftA 0 1 f)
      (.bvar 0)).trans
  apply NeutralPi.applyValue_congr
  · have hdrop : EnvI.drop (EnvI.cons x ρ) 1 = ρ :=
      (EnvI.drop_cons x ρ 0).trans (EnvI.drop_zero ρ)
    exact (env_denote_lift0 hB hF ν (EnvI.cons x ρ) 1 f).trans
      (hdrop ▸ ValueEq.refl
        (EnvironmentEval.denote E F ν (EnvI.drop (EnvI.cons x ρ) 1) f))
  · exact env_denote_bvar E F ν (EnvI.cons x ρ) 0

/-- Environment-aware eta in a lawful saturated domain — mirrors
`FunctionSaturation.denote_eta_related`. -/
theorem env_denote_eta_related {E : ResolvedEnvA} {F : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F)
    {D : Relation} (hD : Laws D) (hs : Saturated D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ν μ : Valuation} {ρ σ : EnvI} {A f g : ExprA} {u : Level}
    (hfg : FunctionPER NeutralPi.applyValue D C
      (EnvironmentEval.denote E F ν ρ f) (EnvironmentEval.denote E F μ σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (EnvironmentEval.denote E F ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0))))
      (EnvironmentEval.denote E F μ σ g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
    (env_denote_eta_withBottom_application hB hF ν ρ A f u x)]
  have hsx := hs x (left_member hD hxy)
  have hr := hfg (withBottom x) y (hD.trans hsx hxy)
  exact (hC (withBottom x) x hsx _ _).mp hr

/-- `PairedArms.Conv_eta` at the environment-aware model — the
lifting/eta port.  Mirrors `InductiveEtaArms.conv_eta_supplied`:
`EnvironmentLambdaArms.denote_pi_view` inverts the pi code,
`code_laws`/`InductiveCodes.code_saturated` supply the domain laws and
saturation, `env_denote_eta_related` is the eta step.  `hrt`/`ihrt` (the
eta-expansion typing IH) are kept in the contract but not consumed —
matching the old-model supplier. -/
theorem paired_env_conv_eta {E : ResolvedEnvA} {F : FamilySyntax}
    (hB : MemberBodyLiftId E) (hF : FamilyLiftId E F)
    (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_eta (model E F) E I n := by
  intro Γ f A B u v hf hrt ihf ihrt hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hp, hfg⟩ := ihf hΓ ν μ ρ σ hν hρ
  obtain ⟨kA, kB, RA, RB, hA, _hBd, hc, hR⟩ :=
    EnvironmentLambdaArms.denote_pi_view hp.left_code
  refine ⟨k, R, S, hp, (hR _ _).mpr ?_⟩
  exact env_denote_eta_related hB hF (InductiveCodes.code_laws hA)
    (InductiveCodes.code_saturated hA) hc ((hR _ _).mp hfg)

end Eta

section Instantiation

/-- `MemberBodyLiftId` at the composed telescope view — discharged by the
supplied `DefinitionBodiesClosed` leg of
`EnvironmentTelescopePorts.internalView_body_conditions` (itself sourced
from `admitted_body_conditions` at `EnvWfA`). -/
theorem memberBodyLiftId_internalView {E : ResolvedEnvA} {I : IotaIfaceA}
    (hW : EnvWfA I E) : MemberBodyLiftId (internalView E) := by
  obtain ⟨-, -, -, -, hdef, -⟩ := internalView_body_conditions hW
  exact fun r ls b hb => liftIdA_of_lift1 (hdef r ls b hb)

/-- `FamilyLiftId` at the default hook — discharged by the supplied
`HookLiftFixed` leg of `EnvironmentTelescopePorts.default_hook_conditions`.
Arbitrary hooks are not assumed; only the supplied neutral hook is
instantiated. -/
theorem familyLiftId_hook_neutral {E : ResolvedEnvA} {I : IotaIfaceA}
    (hW : EnvWfA I E) :
    FamilyLiftId (internalView E) (hook E neutralFamilySyntax) :=
  familyLiftId_of_hookLiftFixed (default_hook_conditions hW).1

/-- `Ty_bvar` at the supplied telescope view and default hook — every
premise discharged: closedness/coherence from `EnvWfA` via the supplied
ports, and the `withBottom` adjunction from `code_saturated` at the
`CodeI` grammar of `model`.  No extra premise remains. -/
theorem paired_env_ty_bvar_internal {E : ResolvedEnvA} {I : IotaIfaceA}
    (hW : EnvWfA I E) {n : Nat} :
    PairedArms.Ty_bvar
      (model (internalView E) (hook E neutralFamilySyntax))
      (internalView E) I n :=
  paired_env_ty_bvar (memberBodyLiftId_internalView hW)
    (familyLiftId_hook_neutral hW)

/-- `Conv_zetaLocal` at the supplied telescope view and default hook —
same zero-extra-premise discharge. -/
theorem paired_env_conv_zetaLocal_internal {E : ResolvedEnvA} {I : IotaIfaceA}
    (hW : EnvWfA I E) {n : Nat} :
    PairedArms.Conv_zetaLocal
      (model (internalView E) (hook E neutralFamilySyntax))
      (internalView E) I n :=
  paired_env_conv_zetaLocal (memberBodyLiftId_internalView hW)
    (familyLiftId_hook_neutral hW)

/-- `Conv_eta` at the supplied telescope view and default hook. -/
theorem paired_env_conv_eta_internal {E : ResolvedEnvA} {I : IotaIfaceA}
    (hW : EnvWfA I E) (n : Nat) :
    PairedArms.Conv_eta
      (model (internalView E) (hook E neutralFamilySyntax))
      (internalView E) I n :=
  paired_env_conv_eta (memberBodyLiftId_internalView hW)
    (familyLiftId_hook_neutral hW) I n

end Instantiation

#print axioms ClosedAboveA
#print axioms ClosedAboveN
#print axioms LiftIdA
#print axioms closedAboveN_cutTerm
#print axioms closedAboveN_levelTerm
#print axioms closedAboveN_sortTerm
#print axioms lift_taggedTerm
#print axioms closedAboveN_app
#print axioms closedAboveN_lam
#print axioms closedAboveN_pi
#print axioms closedAboveN_letE
#print axioms closedAboveN_tagged
#print axioms closedAboveA_app
#print axioms closedAboveA_lam
#print axioms closedAboveA_pi
#print axioms closedAboveA_letE
#print axioms liftA_zero
#print axioms liftA_comp
#print axioms liftIdA_of_lift1
#print axioms MemberBodyLiftId
#print axioms FamilyLiftId
#print axioms familyLiftId_neutral
#print axioms natExpandA_liftId
#print axioms liftIdN_rigidTerm
#print axioms memberBodyLiftId_of_envWfA
#print axioms translation_closedAt
#print axioms translation_lift
#print axioms translation_unlift
#print axioms env_denote_bvar
#print axioms env_denote_lift0
#print axioms EnvImageLiftLaw
#print axioms EnvImageBvarRelL
#print axioms EnvImageBvarRelR
#print axioms envImageLiftLaw
#print axioms envBvarRelL_of_withBottom
#print axioms envBvarRelR_of_withBottom
#print axioms envBvarRelL_of_code
#print axioms envBvarRelR_of_code
#print axioms envBvarRel_of_code
#print axioms envPairedRealises_entry_assumption
#print axioms envPairedRealises_entry_letBinding
#print axioms envPairedRealises_lookupType
#print axioms envPairedRealises_lookupValueType
#print axioms paired_env_ty_bvar_of_laws
#print axioms paired_env_conv_zetaLocal_of_laws
#print axioms paired_env_ty_bvar
#print axioms paired_env_conv_zetaLocal
#print axioms env_denote_eta_withBottom_application
#print axioms env_denote_eta_related
#print axioms paired_env_conv_eta
#print axioms memberBodyLiftId_internalView
#print axioms familyLiftId_hook_neutral
#print axioms paired_env_ty_bvar_internal
#print axioms paired_env_conv_zetaLocal_internal
#print axioms paired_env_conv_eta_internal
#print axioms liftIdN_of_lift1
#print axioms familyLiftId_of_hookLiftFixed

end Rcic.Declarative.Ann.LR3.EnvLookup
