import rcic.RcicAnnLR3SemanticMemberReadback
import rcic.RcicAnnLREnv

/-!
# Constructive admission-indexed universe readback

The data-producing recursion follows EnvWfA : Type. Transparent bodies
are read in their admitted predecessor. Soundness is strengthened to
arbitrary prefix extensions and arbitrary final evaluator hooks. No
normalization assumption, choice or fixed fuel is used for a successful
result. This reads the sort/delta fragment; other stored types remain none.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.AdmissionUniverseReadback
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

structure Reader (E : ResolvedEnvA) where
  read : Valuation → ExprA → Option (Option Nat)
  sound : ∀ {W : ResolvedEnvA}, PrefixA E W →
    ∀ (ν : Valuation) (A : ExprA) (k : Option Nat), read ν A = some k →
    ∀ (F : EnvironmentEval.FamilySyntax) (ρ : EnvI),
      ValueEq (EnvironmentEval.denote (SemanticMemberEval.view W) F ν ρ A)
        (universeValue k)

def emptyRead (ν : Valuation) : ExprA → Option (Option Nat)
  | .sort l => some (eval ν l)
  | _ => none

def Reader.empty : Reader emptyEnvA where
  read := emptyRead
  sound := by
    intro W _ ν A k hk F ρ
    cases A with
    | sort l =>
        have he : eval ν l = k := Option.some.inj hk
        cases he
        exact (SemanticMemberEval.sortMeaning (SemanticMemberEval.view W) ν l).image F ρ
    | bvar i => cases hk
    | const r ls => cases hk
    | app f a => cases hk
    | lam A u b => cases hk
    | pi A u B v => cases hk
    | letE A v b => cases hk
    | lit n => cases hk

def Reader.weaken {E E' : ResolvedEnvA} (R : Reader E) (h : PrefixA E E') : Reader E' where
  read := R.read
  sound := by
    intro W hW ν A k hk F ρ
    exact R.sound (prefixA_trans h hW) ν A k hk F ρ

def addRead (old : Valuation → ExprA → Option (Option Nat)) (r : Nat) (b : ExprA)
    (ν : Valuation) : ExprA → Option (Option Nat)
  | .const q ls =>
      if q = r then old ν (instantiateLevelsA ls b) else old ν (.const q ls)
  | e => old ν e

def Reader.addTransparent {E E' : ResolvedEnvA} (R : Reader E)
    (h : PrefixA E E') {r : Nat} {m : CheckedMemberA} {b : ExprA}
    (hm : E'.members r = some m) (hb : m.bodyA = some b)
    (ht : transparent m.mclass = true) : Reader E' where
  read := addRead R.read r b
  sound := by
    intro W hW ν A k hk F ρ
    have hOld : PrefixA E W := prefixA_trans h hW
    cases A with
    | const q ls =>
        by_cases hqr : q = r
        · subst q
          have hread : R.read ν (instantiateLevelsA ls b) = some k := by
            simpa [addRead] using hk
          have hbody : EnvironmentEval.definitionBody (SemanticMemberEval.view W) r ls =
              some (instantiateLevelsA ls b) := by
            rw [SemanticMemberEval.definitionBody_preserved]
            exact EnvironmentEval.definitionBody_of_member (hW _ _ hm) hb ht
          exact (SemanticMemberReadback.denote_of_body hbody F ν ρ).trans
            (R.sound hOld ν (instantiateLevelsA ls b) k hread F ρ)
        · exact R.sound hOld ν (.const q ls) k
            (by simpa [addRead, hqr] using hk) F ρ
    | bvar i => exact R.sound hOld ν (.bvar i) k hk F ρ
    | sort l => exact R.sound hOld ν (.sort l) k hk F ρ
    | app f a => exact R.sound hOld ν (.app f a) k hk F ρ
    | lam A u b => exact R.sound hOld ν (.lam A u b) k hk F ρ
    | pi A u B v => exact R.sound hOld ν (.pi A u B v) k hk F ρ
    | letE A v b => exact R.sound hOld ν (.letE A v b) k hk F ρ
    | lit n => exact R.sound hOld ν (.lit n) k hk F ρ

def readerOf {I : IotaIfaceA} : {E : ResolvedEnvA} → EnvWfA I E → Reader E
  | _, .empty => Reader.empty
  | _, .axiomM E r _ _ hE hfresh _ _ _ =>
      Reader.weaken (readerOf hE) (prefixA_extend E r _ hfresh)
  | _, .definitionM E r _ v _ hE hfresh _ _ _ _ _ _ =>
      Reader.addTransparent (readerOf hE) (prefixA_extend E r _ hfresh)
        (members_extendEnvA_self E r _) (b := v) rfl rfl
  | _, .theoremM E r _ _ hE hfresh _ _ _ _ _ _ =>
      Reader.weaken (readerOf hE) (prefixA_extend E r _ hfresh)
  | _, .opaqueM E r _ _ _ hE hfresh _ _ _ _ _ _ =>
      Reader.weaken (readerOf hE) (prefixA_extend E r _ hfresh)
  | _, .group _ _ _ _ hE _ _ _ _ _ _ _ hfresh =>
      Reader.weaken (readerOf hE) (prefixA_groupEnvA hfresh)
  | _, .groupRec _ _ _ _ hE _ _ _ _ _ _ _ hfresh _ _ hrfresh =>
      Reader.weaken (readerOf hE)
        (prefixA_trans (prefixA_groupEnvA hfresh) (prefixA_extend _ _ _ hrfresh))

def readAdmitted {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E)
    (ν : Valuation) (A : ExprA) : Option (Option Nat) :=
  (readerOf hE).read ν A

theorem readAdmitted_sound {I : IotaIfaceA} {E W : ResolvedEnvA}
    (hE : EnvWfA I E) (hEW : PrefixA E W)
    (ν : Valuation) (A : ExprA) (k : Option Nat)
    (hk : readAdmitted hE ν A = some k)
    (F : EnvironmentEval.FamilySyntax) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote (SemanticMemberEval.view W) F ν ρ A)
      (universeValue k) :=
  (readerOf hE).sound hEW ν A k hk F ρ

def hook {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E)
    (F : EnvironmentEval.FamilySyntax) : EnvironmentEval.FamilySyntax :=
  fun ν r ls fallback =>
    match E.members r with
    | none => F ν r ls fallback
    | some m =>
        match readAdmitted hE ν (instantiateLevelsA ls m.mtypeA) with
        | some k => NativeMemberValues.term k r
        | none => F ν r ls m

def image {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote (SemanticMemberEval.view E) (hook hE F) ν ρ e

theorem stored_type_image {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A : ExprA) (k : Option Nat)
    (hk : readAdmitted hE ν A = some k) :
    ValueEq (image hE F ν ρ A) (universeValue k) :=
  readAdmitted_sound hE (prefixA_refl E) ν A k hk (hook hE F) ρ

theorem axiom_image {I : IotaIfaceA} {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hE : EnvWfA I E)
    (hm : E.members r = some m) (hc : m.mclass = .axiomM)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (k : Option Nat)
    (hk : readAdmitted hE ν (instantiateLevelsA ls m.mtypeA) = some k) :
    ValueEq (image hE F ν ρ (.const r ls)) (NativeMemberValues.value k r) := by
  have hd : EnvironmentEval.definitionBody (SemanticMemberEval.view E) r ls = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, hc, transparent]
  have ht : EnvironmentEval.rigidTerm (SemanticMemberEval.view E) (hook hE F) ν r ls =
      NativeMemberValues.term k r := by
    simp [EnvironmentEval.rigidTerm, SemanticMemberEval.view, hm,
      SemanticMemberEval.route, hc, hook, hk]
  exact (EnvironmentEval.denote_rigid hd (hook hE F) ν ρ).trans
    (by rw [ht]; exact NativeMemberValues.environment ρ k r)

end Rcic.Declarative.Ann.LR3.AdmissionUniverseReadback
