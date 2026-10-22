import rcic.RcicAnnLR3SemanticMemberAdmissionReadback

/-!
# Actual admitted alias chains of arbitrary finite depth

Every chain is supplied as EnvWfA. The admission reader follows its
predecessors with no numeric evaluation budget. The source axiom and
its actual configured member image are supplied at every depth.
This is a constructive sort/delta control, not a general Ty_const arm.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.AdmissionUniverseControls
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements AdmissionUniverseReadback

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def body : Nat → ExprA
  | 0 => .sort .zero
  | n + 1 => .const n []

def aliasMember (n : Nat) : CheckedMemberA :=
  ⟨.definitionM, 0, .sort one, some (body n), 0, none⟩

def chainEnv : Nat → ResolvedEnvA
  | 0 => emptyEnvA
  | n + 1 => extendEnvA (chainEnv n) n (aliasMember n)

theorem absent (n q : Nat) (h : n ≤ q) : (chainEnv n).members q = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h
      have hne : q ≠ n := Nat.ne_of_gt hlt
      have hne' : n ≠ q := Ne.symm hne
      have hold : (chainEnv n).members q = none :=
        ih (Nat.le_trans (Nat.le_succ n) h)
      simpa [chainEnv, extendEnvA, hne, hne'] using hold

theorem last_lookup (n : Nat) :
    (chainEnv (n + 1)).members n = some (aliasMember n) :=
  members_extendEnvA_self (chainEnv n) n (aliasMember n)

def body_typed (I : IotaIfaceA) (Γ : LCtxA) :
    (n : Nat) → HasTyA (chainEnv n) I 0 Γ (body n) (.sort one)
  | 0 => .sort Γ .zero
  | n + 1 =>
      .const Γ n [] (aliasMember n) two (last_lookup n) rfl rfl (.sort Γ one)

def chain_admitted (I : IotaIfaceA) : (n : Nat) → EnvWfA I (chainEnv n)
  | 0 => .empty
  | n + 1 =>
      .definitionM (chainEnv n) n (.sort one) (body n) two
        (chain_admitted I n) (absent n n (Nat.le_refl n))
        (.sort [] one) (body_typed I [] n)
        (fun _ => rfl) (by cases n <;> exact fun _ => rfl)
        rfl (by cases n <;> rfl)

theorem read_last (I : IotaIfaceA) (n : Nat) (ν : Valuation) :
    readAdmitted (chain_admitted I (n + 1)) ν (.const n []) = some (some 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change addRead (readerOf (chain_admitted I (n + 1))).read
        (n + 1) (body (n + 1)) ν (.const (n + 1) []) = some (some 0)
      simpa only [addRead, if_pos rfl, body, instantiateLevelsA, readAdmitted] using ih

def probeMember (n : Nat) : CheckedMemberA :=
  ⟨.axiomM, 0, .const n [], none, 0, none⟩

def probeEnv (n : Nat) : ResolvedEnvA :=
  extendEnvA (chainEnv (n + 1)) (n + 1) (probeMember n)

def probe_admitted (I : IotaIfaceA) (n : Nat) : EnvWfA I (probeEnv n) :=
  .axiomM (chainEnv (n + 1)) (n + 1) (.const n []) one
    (chain_admitted I (n + 1)) (absent (n + 1) (n + 1) (Nat.le_refl _))
    (body_typed I [] (n + 1)) (fun _ => rfl) rfl

theorem probe_prefix (n : Nat) : PrefixA (chainEnv (n + 1)) (probeEnv n) :=
  prefixA_extend _ _ _ (absent (n + 1) (n + 1) (Nat.le_refl _))

def probe_type (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    HasTyA (probeEnv n) I 0 Γ (.const n []) (.sort one) :=
  .const Γ n [] (aliasMember n) two
    (probe_prefix n _ _ (last_lookup n)) rfl rfl (.sort Γ one)

def source_probe (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    HasTyA (probeEnv n) I 0 Γ (.const (n + 1) []) (.const n []) :=
  .const Γ (n + 1) [] (probeMember n) one
    (members_extendEnvA_self _ _ _) rfl rfl (probe_type I n Γ)

theorem read_probe_type (I : IotaIfaceA) (n : Nat) (ν : Valuation) :
    readAdmitted (probe_admitted I n) ν (.const n []) = some (some 0) :=
  read_last I n ν

theorem probe_type_image (I : IotaIfaceA) (n : Nat)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (image (probe_admitted I n) F ν ρ (.const n []))
      (universeValue (some 0)) :=
  stored_type_image (probe_admitted I n) F ν ρ _ _ (read_probe_type I n ν)

theorem probe_image (I : IotaIfaceA) (n : Nat)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (image (probe_admitted I n) F ν ρ (.const (n + 1) []))
      (NativeMemberValues.value (some 0) (n + 1)) :=
  axiom_image (m := probeMember n) (probe_admitted I n)
    (members_extendEnvA_self _ _ _) rfl F ν ρ (some 0) (read_probe_type I n ν)

theorem every_depth_inhabited (n : Nat) :
    Nonempty (EnvWfA (iotaIfaceA (probeEnv n)) (probeEnv n)) ∧
    Nonempty (HasTyA (probeEnv n) (iotaIfaceA (probeEnv n)) 0 []
      (.const (n + 1) []) (.const n [])) ∧
    (∀ ν ρ, ValueEq
      (image (probe_admitted (iotaIfaceA (probeEnv n)) n)
        EnvironmentEval.neutralFamilySyntax ν ρ (.const (n + 1) []))
      (NativeMemberValues.value (some 0) (n + 1))) :=
  ⟨⟨probe_admitted _ n⟩, ⟨source_probe _ n []⟩,
    fun ν ρ => probe_image _ n EnvironmentEval.neutralFamilySyntax ν ρ⟩

end Rcic.Declarative.Ann.LR3.AdmissionUniverseControls
