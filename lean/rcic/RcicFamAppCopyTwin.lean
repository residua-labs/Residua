import rcic.RcicAnnRowsSupply
import rcic.RcicClassCAxSpine

/-!
# RcicFamAppCopyTwin — a copy-only twin of `riEnv`: `RI₀` as an EMPTY inductive group, `mk₀` an axiom

`riEnv` (class B: `RI : Sort 0 → Sort 0`, `mk : Π X, RI X`, `rec` AnySort) is not in the copy's
scope: its recursor is in no profile arm (`PropElimStructA` fails, `riPolicy_anySort`). The copy's
admission `EnvWfA.group` takes a family with ANY list of constructors — including the empty list — and
no recursor (`.groupRec` is the separate rule that adds one). So the environment

  `gEnvA = { RI₀ : Sort 0 → Sort 0 (inductive, no constructors) @0 ;  mk₀ : Π X, RI₀ X (AXIOM, arity 0) @2 }`

is admitted by `.group … [] …` then `.axiomM`. It has no recursor and no constructor member, so every
premise of `AnnEnvA` that speaks about recursors or constructors is vacuous (`PropElimStructA`,
`EnvNoFunA`, `EnvNormEraseA`), and `SmallIndexProfileA` is vacuous at a `Prop` family. The landed
supplier `typedRowsWf_of_annEnvA` then gives the three typed chain rows of the erased environment
`gEnv₀ = eraseEnv gEnvA = { riFam @0 ; ⟨axiomM, 0, riCtor.mtype, none⟩ @2 }`, for every universe bound.

`gEnv₀` is not an `EnvWfT` (main's group rule bundles the recursor) — it is a COPY-ONLY environment.
`RcicFamAppPiRow` carries `riEnv`'s derivations into it (`tr`: `mk ↦ mk₀`, `rec.{l} ↦ recT l`) and back
(a renaming: `gEnv₀` has no ι and no δ), which is how `riEnv`'s Π row is read off `gEnv₀`'s.
-/

namespace Rcic.Syn.FamApp.CopyTwin

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Syn
open Rcic.Syn.ClassC

/-! ## §1 the annotated members and environment -/

/-- `RI₀ : Sort 0 → Sort 0`, annotated (domain and codomain sorts `Sort 1`); parameter count `0`. -/
def riFamA : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero), none, 0, none⟩

/-- `mk₀ : Π (X : Sort 0), RI₀ X`, an AXIOM of arity `0`, annotated (domain sort `Sort 1`, codomain
    sort `Sort 0`). -/
def mkAxA : CheckedMemberA :=
  ⟨.axiomM, 0, .pi (.sort .zero) (.succ .zero) (.app (.const 0 []) (.bvar 0)) .zero, none, 0, none⟩

def gFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 0 riFamA
def gEnvA : ResolvedEnvA := extendEnvA gFamEnvA 2 mkAxA

theorem gFamEnvA_members (r : Nat) :
    gFamEnvA.members r = if r = 0 then some riFamA else none := rfl

theorem gEnvA_members (r : Nat) :
    gEnvA.members r = if r = 2 then some mkAxA else if r = 0 then some riFamA else none := rfl

theorem gEnvA_class {r : Nat} {m : CheckedMemberA} (h : gEnvA.members r = some m) :
    (r = 2 ∧ m = mkAxA) ∨ (r = 0 ∧ m = riFamA) := by
  rw [gEnvA_members] at h
  by_cases h2 : r = 2
  · rw [if_pos h2] at h; exact Or.inl ⟨h2, (Option.some.inj h).symm⟩
  · rw [if_neg h2] at h
    by_cases h0 : r = 0
    · rw [if_pos h0] at h; exact Or.inr ⟨h0, (Option.some.inj h).symm⟩
    · rw [if_neg h0] at h; exact Option.noConfusion h

/-- no member of the twin is a recursor. -/
theorem gEnvA_noRec {r : Nat} {m : CheckedMemberA} (h : gEnvA.members r = some m) :
    m.mclass ≠ .recursorM := by
  rcases gEnvA_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact fun h => MemberClass.noConfusion h

/-- no member of the twin is a constructor. -/
theorem gEnvA_noCtor {r : Nat} {m : CheckedMemberA} (h : gEnvA.members r = some m) :
    m.mclass ≠ .constructorM := by
  rcases gEnvA_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact fun h => MemberClass.noConfusion h

/-! ## §2 the two member types, typed on the copy (ι-free derivations, at every interface) -/

/-- `Sort 0 → Sort 0 : Sort (imax 1 1)`, in every context and environment. -/
def riFamTyA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (Γ : LCtxA) :
    HasTyA E I n Γ riFamA.mtypeA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero) (.sort Γ .zero) (.sort _ .zero)

/-- `RI₀ X : Sort 0` under `X : Sort 0`, wherever `RI₀` is member `0`. -/
def riAppTyA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (h0 : E.members 0 = some riFamA)
    (Γ : LCtxA) :
    HasTyA E I n (.assumption (.sort .zero) :: Γ) (.app (.const 0 []) (.bvar 0)) (.sort .zero) :=
  .app _ (.const 0 []) (.bvar 0) (.sort .zero) (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero)
    (.sort _ .zero) (.sort _ .zero)
    (.const _ 0 [] riFamA (.imax (.succ .zero) (.succ .zero)) h0 rfl rfl (riFamTyA _))
    (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))

/-- `Π (X : Sort 0), RI₀ X : Sort (imax 1 0)`, wherever `RI₀` is member `0`. -/
def mkAxTyA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (h0 : E.members 0 = some riFamA)
    (Γ : LCtxA) :
    HasTyA E I n Γ mkAxA.mtypeA (.sort (.imax (.succ .zero) .zero)) :=
  .pi Γ (.sort .zero) (.succ .zero) (.app (.const 0 []) (.bvar 0)) .zero (.sort Γ .zero)
    (riAppTyA h0 Γ)

/-! ## §3 admission: an empty group, then an axiom -/

/-- `RI₀`'s family view: no parameters, one `Sort 0` index, result sort `0`. -/
def riFamViewA : FamViewA riFamA where
  params := []
  indices := [(.sort .zero, .succ .zero)]
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

/-- the empty group `{RI₀}`: `EnvWfA.group` with no constructors. -/
def gFamEnvWfA (I : IotaIfaceA) : EnvWfA I gFamEnvA :=
  .group emptyEnvA 0 riFamA (.imax (.succ .zero) (.succ .zero)) .empty rfl rfl (fun _ => rfl)
    (riFamTyA []) rfl riFamViewA [] rfl

/-- the twin admitted: the empty group, then the axiom `mk₀`. -/
def gEnvWfA (I : IotaIfaceA) : EnvWfA I gEnvA :=
  .axiomM gFamEnvA 2 mkAxA.mtypeA (.imax (.succ .zero) .zero) (gFamEnvWfA I) rfl
    (mkAxTyA rfl []) (fun _ => rfl) rfl

/-! ## §4 the copy's profiles, all vacuous -/

/-- the small-index profile: the only family is a `Prop` family, where the inequality is never asked. -/
theorem gEnvA_small : SmallIndexProfileA gEnvA := by
  intro r m u₀ hm hind hbody v hv ρ x y hx hy hy0
  rcases gEnvA_class hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hind (fun h => MemberClass.noConfusion h)
  · change ExprA.sort .zero = .sort u₀ at hbody
    cases hbody
    change some 0 = some y at hy
    cases hy
    omega

/-- no recursor, so the elimination profile has nothing to constrain. -/
theorem gEnvA_propElim : PropElimStructA gEnvA := by
  intro r rm D f ls fm u₀ hr hc
  exact absurd hc (gEnvA_noRec hr)

/-- no constructor, so no function-recursive field. -/
theorem gEnvA_noFun : EnvNoFunA gEnvA := by
  intro c cm f fm shapes hc hcls
  exact absurd hcls (gEnvA_noCtor hc)

/-- no constructor, so no `normA` to compare. -/
theorem gEnvA_normErase : EnvNormEraseA gEnvA := by
  intro r m hm hmc
  exact absurd hmc (gEnvA_noCtor hm)

/-- THE TWIN IS IN THE COPY'S SCOPE. -/
theorem gAnnEnvA : AnnEnvA gEnvA where
  wf := ⟨gEnvWfA _⟩
  small := gEnvA_small
  propElim := gEnvA_propElim
  noFun := gEnvA_noFun

/-! ## §5 the erased twin and its rows -/

/-- `mk₀` erased: an axiom at `mk`'s stored type. -/
def mkAx : CheckedMember := ⟨.axiomM, 0, riCtor.mtype, none⟩

/-- the erased twin: `riFam` at `0`, `mk₀` at `2`; no member at `1`. -/
def gEnv₀ : ResolvedEnv := extendEnv (extendEnv emptyEnv 0 riFam) 2 mkAx

theorem gEnv₀_members (r : Nat) :
    gEnv₀.members r = if r = 2 then some mkAx else if r = 0 then some riFam else none := rfl

theorem eraseEnv_gEnvA_members (r : Nat) : (eraseEnv gEnvA).members r = gEnv₀.members r := by
  rw [members_eraseEnv, gEnvA_members, gEnv₀_members]
  by_cases h2 : r = 2
  · rw [if_pos h2, if_pos h2]; rfl
  · rw [if_neg h2, if_neg h2]
    by_cases h0 : r = 0
    · rw [if_pos h0, if_pos h0]; rfl
    · rw [if_neg h0, if_neg h0]; rfl

private theorem resolvedEnv_ext {E F : ResolvedEnv} (h : ∀ r, E.members r = F.members r) : E = F := by
  cases E; cases F
  exact congrArg ResolvedEnv.mk (funext h)

theorem eraseEnv_gEnvA : eraseEnv gEnvA = gEnv₀ := resolvedEnv_ext eraseEnv_gEnvA_members

/-- **THE TWIN'S ROWS**, from the copy's supplier, at every universe bound. -/
theorem g0Rows (n : Nat) : TypedRowsWf gEnv₀ n := by
  have h := typedRowsWf_of_annEnvA gAnnEnvA gEnvA_normErase n
  rwa [eraseEnv_gEnvA] at h

end Rcic.Syn.FamApp.CopyTwin

#print axioms Rcic.Syn.FamApp.CopyTwin.gAnnEnvA
#print axioms Rcic.Syn.FamApp.CopyTwin.g0Rows
