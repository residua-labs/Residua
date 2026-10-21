import rcic.RcicTypedEnv
import rcic.RcicTypedSubst
import rcic.RcicDTMetaTyped

/-!
# M3-b GLM — the typed environment entry fronts the structure properties

The typed substitution/DT009T cores read TWO structure properties and nothing
else: `EnvClosed E` and `EnvMembersSubstStable E` (the standalone form of
`envWf_subst_inst`'s conclusion). Both are `EnvWf` facts today, fronted by
`EnvWf`-wrappers — the OLD entry. This module supplies the SAME two properties
from the FORMAL TYPED entry `EnvWfT`, so a typed environment consumes the
substitution and conditional-endpoint results WITHOUT hand-attaching an old
`EnvWf` proof:

* `envClosed_of_envWfT` — mirrors `envWf_closed` constructor-for-constructor:
  the singleton steps carry their own lift-invariance premises; the atomic
  group step's members carry theirs inside `GroupMembersT.cons`
  (`hclT`, `hnobody`), read by an induction over the group-member chain.
* `envMembersSubstStable_of_envWfT` — COMPOSED, not re-proved, exactly as
  `envWf_subst_inst` composes for the raw entry: level instantiation preserves
  lift-closedness (`instantiateLevels_closed`, `RcicLevelCalc`), and
  lift-closedness at cutoff 0 gives instantiate-invariance
  (`lift_id_instantiate`, `RcicEnv`).
* `hasTyT_subst0_of_envWfT` / `convT_subst0_of_envWfT` — the front door,
  `EnvWfT`-fronted.
* `DT009T_endpoints_of_envWfT` — the conditional endpoint theorem, wrapped at
  the typed entry (the seven supplies remain explicit, unproven premises).

The end-condition pin: `pin_listEnv_subst0_via_typedEntry` consumes head
substitution on the REAL two-group environment `listEnvUT` through the typed
entry only — no `EnvWf` anywhere at the call site.
-/

namespace Rcic.Declarative

/-- the head cell of a group-member chain, with ALL its fields bindable
    (term-level match; `cases` clears the closedness field to an inaccessible). -/
def groupMembersT_consView : {S : ResolvedEnv} → {E : ResolvedEnv} →
    {r : Nat} → {m : CheckedMember} → {rest : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} →
    GroupMembersT S E ((r, m) :: rest) E' →
    GroupMembersT S (extendEnv E r m) rest E' ×'
    (∀ k, lift k 1 m.mtype = m.mtype) ×' m.body = none :=
  fun hmem =>
  match hmem with
  | .cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities hadm hidxAdmT
      u hT hTc htyped hrest =>
      ⟨hrest, hclT, hnobody⟩

/-- the group-member chain extends closedness: each cons cell carries the
    member's own lift-invariance and bodylessness. -/
def envClosed_of_groupMembersT : {S : ResolvedEnv} → {E : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    EnvClosed E → GroupMembersT S E ms E' → EnvClosed E' :=
  fun hcl hmem =>
  match hmem with
  | .nil _ => hcl
  | .cons E r m rest E' hfresh hnobody hclT _ _ _ _ _ _ _ _ _ _ hrest =>
      envClosed_of_groupMembersT
        (fun r' m' hm' => by
          by_cases hrr : r' = r
          · subst hrr
            simp only [extendEnv, if_pos rfl] at hm'
            cases hm'
            exact ⟨hclT, fun b hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
          · simp only [extendEnv, if_neg hrr] at hm'
            exact hcl r' m' hm') hrest

/-- the formal typed entry supplies closedness — the counterpart of
    `envWf_closed`, constructor-for-constructor. -/
def envClosed_of_envWfT : {E : ResolvedEnv} → EnvWfT E → EnvClosed E
  | _, .empty => fun r m hm => by
      simp only [emptyEnv] at hm
      cases hm
  | _, .axiom E r A u hE hfresh hA hcl hlvl =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hcl, fun b hb => by cases hb⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envClosed_of_envWfT hE r' m' hm'
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclv⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envClosed_of_envWfT hE r' m' hm'
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclp⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envClosed_of_envWfT hE r' m' hm'
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclv⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envClosed_of_envWfT hE r' m' hm'
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem => by
      obtain ⟨hrest, hclFm, hnbFm⟩ := groupMembersT_consView hmem
      have hbase : EnvClosed (extendEnv E f fm) :=
        fun r' m' hm' => by
          by_cases hrr : r' = f
          · subst hrr
            simp only [extendEnv, if_pos rfl] at hm'
            cases hm'
            exact ⟨hclFm, fun b hb => by
              rw [hnbFm] at hb; exact Option.noConfusion hb⟩
          · simp only [extendEnv, if_neg hrr] at hm'
            exact envClosed_of_envWfT hE r' m' hm'
      exact envClosed_of_groupMembersT hbase hrest

/-- the formal typed entry supplies member substitution stability — COMPOSED
    from the same two ingredients `envWf_subst_inst` uses (level instantiation
    preserves lift-closedness; lift-closedness at 0 gives instantiate-
    invariance), over `envClosed_of_envWfT` instead of `envWf_closed`. -/
def envMembersSubstStable_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    EnvMembersSubstStable E :=
  fun r m hm =>
    let ⟨hclT, hclB⟩ := envClosed_of_envWfT hW r m hm
    ⟨fun ls s k =>
        lift_id_instantiate (instantiateLevels ls m.mtype)
          (instantiateLevels_closed hclT ls 0) k (Nat.zero_le k) s,
     fun b hb ls s k =>
        lift_id_instantiate (instantiateLevels ls b)
          (instantiateLevels_closed (hclB b hb) ls 0) k (Nat.zero_le k) s⟩

/-- `envWf_subst_inst`, typed-entry-fronted: `EnvWfT → EnvMembersSubstStable`.
    Alias for `envMembersSubstStable_of_envWfT` under the name cc's S3
    signatures cite. -/
def envWfT_subst_inst {E : ResolvedEnv} (hW : EnvWfT E) :
    EnvMembersSubstStable E :=
  envMembersSubstStable_of_envWfT hW

/-- head substitution on the typed judgment, fronted by the FORMAL TYPED
    entry — no `EnvWf` at the call site. -/
def hasTyT_subst0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {v t : Expr Nat}
    {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT E n (LocalDecl.assumption t :: Γ) e A)
    (hv : HasTyT E n Γ v t) :
    HasTyT E n Γ (instantiate0 v e) (instantiate0 v A) :=
  hasTyT_subst0S (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) h hv

/-- the conversion side, typed-entry-fronted. -/
def convT_subst0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {v t : Expr Nat}
    {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n (LocalDecl.assumption t :: Γ) a b T)
    (hv : HasTyT E n Γ v t) :
    ConvT E n Γ (instantiate0 v a) (instantiate0 v b) (instantiate0 v T) :=
  convT_subst0S (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) h hv

/-- the conditional endpoint theorem, wrapped at the typed entry: a typed
    environment plus a well-formed context consume DT009T WITHOUT the old
    `EnvWf`. The seven supplies stay explicit, unproven premises. -/
def DT009T_endpoints_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hη : ConvTEtaLeftT E n) (happ : ConvTAppRightT E n)
    (hlam : ConvTLamRightT E n) (hpi : ConvTPiRightT E n)
    (hlet : ConvTLetRightT E n) (hzeta : ConvTZetaRightT E n)
    (hconst : ConvTConstsRightT E n) :
    {a b T : Expr Nat} → ConvT E n Γ a b T →
    Nonempty (HasTyT E n Γ a T) ∧ Nonempty (HasTyT E n Γ b T) :=
  DT009T_endpointsS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
    hΓ hη happ hlam hpi hlet hzeta hconst

/-! ## the end-condition pin: a REAL typed environment consumes head
substitution through the formal entry — no `EnvWf` anywhere at the call site. -/

/-- one axiom member (`Sort 1 : Sort 2` at index 0) — a legal `EnvWfT`
    environment, witness rebuilt locally (GLM-1's `pinAxEnvT` twin). -/
def pinEnvT : ResolvedEnv := extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort (.succ .zero), none⟩

def pinEnvTWf : EnvWfT pinEnvT :=
  EnvWfT.axiom emptyEnv 0 (.sort (.succ .zero)) (.succ (.succ .zero))
    .empty rfl (HasTyT.sort [] (.succ .zero)) (fun _ => rfl) rfl

/-- THE PIN: substituting `Sort 0` for the head assumption `Sort 1` in
    `bvar 0`'s typing, on a real typed environment, through
    `hasTyT_subst0_of_envWfT` ONLY — the old `EnvWf` entry is nowhere in the
    call. -/
def pin_typedEntry_subst0 :
    Nonempty (HasTyT pinEnvT 1 []
      (instantiate0 (Expr.sort .zero) (Expr.bvar 0))
      (instantiate0 (Expr.sort .zero) (Expr.sort (.succ .zero)))) :=
  ⟨hasTyT_subst0_of_envWfT pinEnvTWf
    (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0
      (.sort (.succ .zero)) rfl)
    (HasTyT.sort [] .zero)⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.envClosed_of_groupMembersT
#print axioms Rcic.Declarative.envClosed_of_envWfT
#print axioms Rcic.Declarative.envMembersSubstStable_of_envWfT
#print axioms Rcic.Declarative.envWfT_subst_inst
#print axioms Rcic.Declarative.hasTyT_subst0_of_envWfT
#print axioms Rcic.Declarative.convT_subst0_of_envWfT
#print axioms Rcic.Declarative.DT009T_endpoints_of_envWfT
#print axioms Rcic.Declarative.pin_typedEntry_subst0
