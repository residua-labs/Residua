import rcic.RcicAnnSemPrefixRows
import rcic.RcicDTMetaTyped
import rcic.RcicSynObsLevels

/-!
# RcicFamAppRevTwin — the copy-only twin of ANY revealed singleton over an in-scope base, with its rows

`RcicFamAppCopyTwin` built, by hand, the recursor-free twin `gEnv₀ = { RI₀ (inductive, no constructors) @0 ;
mk₀ (axiom at `mk`'s type) @2 }` of the class-B fixture `riEnv`, and read its three typed rows off the copy's
supplier. This module does the same construction once, for the shape the F3 tier's class B1 uses (both B1
fixtures are instances: `RI` over the empty base with `I = Sort 0`, `f = 0`; `Foo` over the `Nat` block with
`I = Nat`, `f = 4`):

  a base `E₀` in the copy's scope (`EnvWfT E₀`, `InScope`), fresh at `f` and `f + 2`;
  a closed index type `I : Sort uI` typed in `E₀` (parameter-free levels);
  the family `F : Π (i : I), Sort 0` at `f`; its constructor `mk : Π (x : I), F x` would sit at `f + 1` and
  the AnySort recursor at `f + 2` (in the ENVIRONMENT OF INTEREST, which this module never mentions).

THE TWIN replaces the group by the family ALONE (an inductive member with NO constructor) and an AXIOM with
the constructor's stored type at `f + 2`:  `twin = E₀ + F @f + ⟨axiomM, mk's type⟩ @(f+2)`. It is admitted by
the copy through the landed bridge, step by step: `envBridgeSem` admits the base (an annotated copy `EA0`
with `eraseEnv EA0 = E₀`, its profiles, and `EnvWfA` at every interface agreeing with its own); the family
alone is `EnvWfA.group … [] …` — exactly the "family-scope" step the bridge itself takes inside
`bridge_group` before it walks the constructors (`smallIndexProfileA_fam`, `propElimStructA_extendFam`,
`envNoFunA_extend`, `EnvNormEraseA.extend`); the axiom is `bridgeStep_axiom`. The supplier
`typedRowsWf_of_annEnvA` then gives **`RevBase.twinRows : TypedRowsWf B.twin n`** for every `n`.

The twin has no recursor, hence no ι of its own; its only recursors are the base's. `RcicFamAppRevTwinMeta`
(next) supplies the six metatheory facts a translation target needs (`TwinMeta`) from the base's. Nothing here
is a statement about the environment of interest; it is the target of the generic translation.
closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.RevTwin

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## §1 the shape -/

/-- `F : Π (i : I), Sort 0`, the revealed singleton's family member. -/
def revFamM (I : Expr Nat) : CheckedMember := ⟨.inductiveM, 0, .pi I (.sort .zero), none⟩

/-- `Π (x : I), F x`, the constructor's stored type (the field revealed bare as the index). -/
def revCtorTy (f : Nat) (I : Expr Nat) : Expr Nat := .pi I (.app (.const f []) (.bvar 0))

/-- the twin's axiom: `mk`'s stored type as an axiom of arity `0`. -/
def revAxM (f : Nat) (I : Expr Nat) : CheckedMember := ⟨.axiomM, 0, revCtorTy f I, none⟩

/-- a base for a revealed singleton: an in-scope `EnvWfT` sitting below `f` (so fresh at `f`, `f + 1`,
    `f + 2`), and a closed index type `I : Sort uI` typed in it at universe arity `0`, with parameter-free
    levels. The freshness facts `hf0`/`hf2` follow from `hlow`; they are kept as fields for the reader. -/
structure RevBase : Type where
  E₀ : ResolvedEnv
  hW₀ : EnvWfT E₀
  hP₀ : hW₀.InScope
  f : Nat
  hf0 : E₀.members f = none
  hf2 : E₀.members (f + 2) = none
  /-- the base sits below the group: every member reference is below `f`. -/
  hlow : ∀ r m, E₀.members r = some m → r < f
  I : Expr Nat
  uI : Level
  hI : HasTyT E₀ 0 [] I (.sort uI)
  hclI : ∀ k, lift k 1 I = I
  hlvlI : exprLevelsBounded 0 I = true
  huI : levelBounded 0 uI = true

namespace RevBase

variable (B : RevBase)

/-- the base with the family alone. -/
def famEnv : ResolvedEnv := extendEnv B.E₀ B.f (revFamM B.I)

/-- the twin with the axiom at a reference `a` (fresh when `f < a`): the family alone, then the axiom. -/
def twinAt (a : Nat) : ResolvedEnv := extendEnv B.famEnv a (revAxM B.f B.I)

/-- THE TWIN: the family alone, then the axiom at `f + 2`. -/
def twin : ResolvedEnv := B.twinAt (B.f + 2)

theorem twinAt_members (a r : Nat) :
    (B.twinAt a).members r = if r = a then some (revAxM B.f B.I)
      else if r = B.f then some (revFamM B.I) else B.E₀.members r := rfl

theorem famEnv_members (r : Nat) :
    B.famEnv.members r = if r = B.f then some (revFamM B.I) else B.E₀.members r := rfl

theorem twin_members (r : Nat) :
    B.twin.members r = if r = B.f + 2 then some (revAxM B.f B.I)
      else if r = B.f then some (revFamM B.I) else B.E₀.members r := rfl

theorem famEnv_ext : ∀ r m, B.E₀.members r = some m → B.famEnv.members r = some m := fun r m h => by
  rw [famEnv_members]
  by_cases hr : r = B.f
  · subst hr; rw [B.hf0] at h; exact Option.noConfusion h
  · rw [if_neg hr]; exact h

theorem famEnv_f2 : B.famEnv.members (B.f + 2) = none := by
  rw [famEnv_members, if_neg (by omega)]; exact B.hf2

/-- every reference above `f` is fresh in the family-alone environment (the base sits below `f`). -/
theorem famEnv_fresh (a : Nat) (ha : B.f < a) : B.famEnv.members a = none := by
  rw [famEnv_members, if_neg (by omega)]
  cases h : B.E₀.members a with
  | none => rfl
  | some m => exact absurd (B.hlow a m h) (by omega)

/-! ## §2 the two closed types, on main -/

theorem revFamTy_closed (k : Nat) : lift k 1 (revFamM B.I).mtype = (revFamM B.I).mtype := by
  show lift k 1 (.pi B.I (.sort .zero)) = .pi B.I (.sort .zero)
  simp only [lift, B.hclI k]

theorem revFamTy_lvl : exprLevelsBounded 0 (revFamM B.I).mtype = true := by
  show exprLevelsBounded 0 (.pi B.I (.sort .zero)) = true
  simp only [exprLevelsBounded, B.hlvlI, levelBounded, Bool.and_self]

theorem revCtorTy_closed (k : Nat) : lift k 1 (revCtorTy B.f B.I) = revCtorTy B.f B.I := by
  have h0 : ¬ (k + 1 ≤ 0) := by omega
  simp only [revCtorTy, lift, B.hclI k, h0, ite_false]

theorem revCtorTy_lvl : exprLevelsBounded 0 (revCtorTy B.f B.I) = true := by
  simp only [revCtorTy, exprLevelsBounded, B.hlvlI, levelsBounded, Bool.and_self, Bool.true_and]

/-- `F : Sort (imax uI 1)` in the family-alone environment (the family's type, weakened from the base). -/
def famTyT : HasTyT B.famEnv 0 [] (revFamM B.I).mtype (.sort (.imax B.uI (.succ .zero))) :=
  .pi [] B.I B.uI (.sort .zero) (.succ .zero) (hasTyTExt (famEnv_ext B) B.hI) (.sort _ .zero)

theorem famEnv_f : B.famEnv.members B.f = some (revFamM B.I) := by
  rw [famEnv_members, if_pos rfl]

/-- `F : Π (i : I), Sort 0` at reference `f`, under the index binder, wherever `F` is member `f`. -/
def famConstTy {E : ResolvedEnv} (hfam : E.members B.f = some (revFamM B.I)) (Γ : LCtx) :
    HasTyT E 0 Γ (.const B.f []) (.pi B.I (.sort .zero)) := by
  have h : HasTyT E 0 Γ (.const B.f []) (instantiateLevels [] (revFamM B.I).mtype) :=
    .const _ B.f [] (revFamM B.I) hfam rfl rfl
  rwa [Ann.instantiateLevels_closed [] _ (revFamTy_lvl B)] at h

/-- `Π (x : I), F x : Sort (imax uI 0)` wherever `F` is member `f` and `I : Sort uI`: ConstructorScope's
    typing of the constructor's stored type, built from the index type's. -/
def ctorTyAt {E : ResolvedEnv} (hfam : E.members B.f = some (revFamM B.I))
    (hI : HasTyT E 0 [] B.I (.sort B.uI)) :
    HasTyT E 0 [] (revCtorTy B.f B.I) (.sort (.imax B.uI .zero)) :=
  .pi [] B.I B.uI (.app (.const B.f []) (.bvar 0)) .zero hI
    (.app _ (.const B.f []) (.bvar 0) B.I (.sort .zero) (famConstTy B hfam _)
      (.bvar _ 0 B.I (by simp only [lookupType, List.get?, B.hclI 0])))

/-- the constructor's stored type, typed in the family-alone environment. -/
def ctorTyT : HasTyT B.famEnv 0 [] (revCtorTy B.f B.I) (.sort (.imax B.uI .zero)) :=
  ctorTyAt B (famEnv_f B) (hasTyTExt (famEnv_ext B) B.hI)

/-! ## §3 THE ROWS OF THE TWIN, from the bridge -/

/-- the vacuous small-index obligation of a `Prop` family: the inequality is asked only where the
    family's sort evaluates positively, and `Sort 0` evaluates to `0`. -/
theorem smallIdx_prop (iA : List (ExprA × Level)) :
    ∀ v ∈ iA.map Prod.snd, ∀ (ρ : Nat → Option Nat) (x y : Nat),
      eval ρ v = some x → eval ρ .zero = some y → 0 < y → x ≤ y := by
  intro v _ ρ x y _ hy hpos
  have h0 : (some 0 : Option Nat) = some y := hy
  cases h0
  exact absurd hpos (Nat.lt_irrefl 0)

/-- **THE TWIN'S ROWS**, at every universe bound and at every fresh reference `a > f` of the axiom: the base
    through `envBridgeSem`, the family alone through the copy's `group` rule with no constructors, the axiom
    through `bridgeStep_axiom`, the rows through the landed supplier. -/
theorem twinRowsAt (a : Nat) (ha : B.f < a) (n : Nat) : TypedRowsWf (B.twinAt a) n := by
  obtain ⟨EA0, hE0, hsm, hpo, hnf, hn, hWJ⟩ :=
    envBridgeSem ctorTyOfViewSemA_holds recTyOfViewsSemA_holds B.hW₀ B.hP₀
  have C0 : AnnEnvA EA0 := ⟨hWJ _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩
  -- the index type, annotated and closed
  have hI' : HasTyT (eraseEnv EA0) 0 [] B.I (.sort B.uI) := by rw [hE0]; exact B.hI
  obtain ⟨IA, ls, hIe, hIlvl, ⟨tI⟩⟩ := annotateClosedType C0 hn hI' B.hlvlI
  rw [Rcic.Syn.instLevel_of_paramFree ls B.uI B.huI] at tI
  -- the family alone, annotated
  let fmA : CheckedMemberA := famMemberA 0 [] [(IA, B.uI)] .zero
  have hfr : EA0.members B.f = none := members_none_of_erase (by rw [hE0]; exact B.hf0)
  obtain ⟨hW0I0⟩ := hWJ _ (IfaceAgreeA.refl _ _)
  have hpreA : PrefixA EA0 (extendEnvA EA0 B.f fmA) := prefixA_extend EA0 B.f fmA hfr
  have hag0 : IfaceAgreeA EA0 (iotaIfaceA EA0) (iotaIfaceA (extendEnvA EA0 B.f fmA)) :=
    ifaceAgreeA_prefix hW0I0 hpreA
  have hTfam : HasTyA EA0 (iotaIfaceA EA0) 0 [] fmA.mtypeA (.sort (.imax B.uI (.succ .zero))) :=
    .pi [] IA B.uI (.sort .zero) (.succ .zero) tI (.sort _ .zero)
  have hfmE : erase fmA.mtypeA = (revFamM B.I).mtype := by
    show erase (.pi IA B.uI (.sort .zero) (.succ .zero)) = .pi B.I (.sort .zero)
    simp only [erase, hIe]
  have hclTA : ∀ k, liftA k 1 fmA.mtypeA = fmA.mtypeA := fun k =>
    liftA_eq_of_erase _ k (by rw [hfmE]; exact revFamTy_closed B k)
  have hlvlA : exprLevelsBoundedA 0 fmA.mtypeA = true := by
    show exprLevelsBoundedA 0 (.pi IA B.uI (.sort .zero) (.succ .zero)) = true
    simp only [exprLevelsBoundedA, hIlvl, B.huI, levelBounded, Bool.and_self]
  let fvA : FamViewA fmA := famViewOfA 0 [] [(IA, B.uI)] .zero (Or.inl (fun _ => rfl))
  have hWfam : ∀ J, IfaceAgreeA (extendEnvA EA0 B.f fmA) (iotaIfaceA (extendEnvA EA0 B.f fmA)) J →
      Nonempty (EnvWfA J (extendEnvA EA0 B.f fmA)) := fun J hJ => by
    have hag : IfaceAgreeA EA0 (iotaIfaceA EA0) J := hag0.trans (IfaceAgreeA.prefix hpreA hJ)
    obtain ⟨hW0J⟩ := hWJ J hag
    exact ⟨.group EA0 B.f fmA _ hW0J rfl rfl hclTA (hasTyIfaceA hag hTfam) hlvlA fvA [] hfr⟩
  obtain ⟨hWfam0⟩ := hWfam _ (IfaceAgreeA.refl _ _)
  have Cfam : AnnEnvA (extendEnvA EA0 B.f fmA) :=
    ⟨⟨hWfam0⟩, smallIndexProfileA_fam (smallIdx_prop _) hsm hfr,
      propElimStructA_extendFam hW0I0 hfr (fun h => MemberClass.noConfusion h) hpo,
      envNoFunA_extend hW0I0 hnf hfr (fun h => MemberClass.noConfusion h)⟩
  have hnfam : EnvNormEraseA (extendEnvA EA0 B.f fmA) := hn.extend (fun h => MemberClass.noConfusion h)
  have hEfam : eraseEnv (extendEnvA EA0 B.f fmA) = B.famEnv := by
    rw [eraseEnv_extend, hE0]
    show extendEnv B.E₀ B.f (eraseMember fmA) = extendEnv B.E₀ B.f (revFamM B.I)
    have hm : eraseMember fmA = revFamM B.I := by
      show (⟨.inductiveM, 0, erase fmA.mtypeA, none⟩ : CheckedMember) = revFamM B.I
      rw [hfmE]; rfl
    rw [hm]
  -- the axiom
  have hfr2 : (eraseEnv (extendEnvA EA0 B.f fmA)).members a = none := by
    rw [hEfam]; exact famEnv_fresh B a ha
  have hA' : HasTyT (eraseEnv (extendEnvA EA0 B.f fmA)) 0 [] (revCtorTy B.f B.I) (.sort (.imax B.uI .zero)) := by
    rw [hEfam]; exact ctorTyT B
  obtain ⟨mA, hmAc, hEtw, hWtw⟩ :=
    bridgeStep_axiom Cfam hnfam hWfam hfr2 hA' (revCtorTy_closed B) (revCtorTy_lvl B)
  have hfrA2 : (extendEnvA EA0 B.f fmA).members a = none := members_none_of_erase hfr2
  obtain ⟨hWtw0⟩ := hWtw _ (IfaceAgreeA.refl _ _)
  have hnotInd : mA.mclass ≠ .inductiveM := fun h => MemberClass.noConfusion (hmAc.symm.trans h)
  have hnotRec : mA.mclass ≠ .recursorM := fun h => MemberClass.noConfusion (hmAc.symm.trans h)
  have hnotCtor : mA.mclass ≠ .constructorM := fun h => MemberClass.noConfusion (hmAc.symm.trans h)
  obtain ⟨hsm', hpo'⟩ := profilesA_extend hWfam0 hfrA2 hnotInd hnotRec Cfam.small Cfam.propElim
  have Ctw : AnnEnvA (extendEnvA (extendEnvA EA0 B.f fmA) a mA) :=
    ⟨⟨hWtw0⟩, hsm', hpo', envNoFunA_extend hWfam0 Cfam.noFun hfrA2 hnotCtor⟩
  have hntw : EnvNormEraseA (extendEnvA (extendEnvA EA0 B.f fmA) a mA) := hnfam.extend hnotCtor
  have h := typedRowsWf_of_annEnvA Ctw hntw n
  rw [hEtw, hEfam] at h
  exact h

/-- the rows of the twin with the axiom at `f + 2`. -/
theorem twinRows (n : Nat) : TypedRowsWf B.twin n := B.twinRowsAt (B.f + 2) (by omega) n

end RevBase

end Rcic.Syn.FamApp.RevTwin

#print axioms Rcic.Syn.FamApp.RevTwin.RevBase.twinRows
