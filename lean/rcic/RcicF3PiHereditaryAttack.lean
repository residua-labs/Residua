import rcic.RcicF3PiHereditaryEnv
import rcic.RcicF3PiNormalizeAttack
/-! Adversarial hereditary-normalization checks and inhabited dependent
product presentations. No universal family producer. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiHereditaryAttack
open Rcic.Declarative PiHereditary
universe u

def badType : Expr Nat :=
  .pi (.bvar 0) (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 3))
def badAssignment : Nat → PSet.{u}
  | 0 => tyv PiErasureAttack.domain
  | 1 => tyv pempty
  | _ => tyv PiErasureAttack.domain
kernel_rfl_theorem badRead :
  piTelescopeFuel emptyEnv 16 badType = some ([.bvar 0], .bvar 3)

/-- Root nonemptiness does not pay hereditary regularity. The beta hidden
under the Pi binder applies an empty-domain lambda to a nonmember. -/
theorem root_ne_not_regular (M : Interp.{u}) (σ : Nat → Nat) :
    (¬ Equiv (den M σ badAssignment badType) pempty) ∧
      ¬ Regular M σ badType badAssignment := by
  constructor
  · exact tyv_ne_pempty _
  · intro hR
    have ha : PiErasureAttack.atom ∈ Ed M (tyv PiErasureAttack.domain) :=
      mem_congr_right (ed_tyv M (Or.inr (fun h =>
        tyv_ne_pempty _ (mem_singleton.mp h).symm))).symm (mem_singleton.mpr Equiv.rfl)
    have hne := (hR.2.2 PiErasureAttack.atom ha).2
    have hx : tyv PiErasureAttack.domain ∈ Ed M (tyv pempty) :=
      mem_of_fapp_lamVal_ne M hne
    exact not_mem_pempty (mem_congr_right (ed_tyv M (Or.inr not_mem_pempty)) hx)
/-- The malformed hidden beta actually changes the element set, despite a
nonempty raw root. The normalized side has an explicit lambda inhabitant. -/
theorem bad_normalization_changes_members (M : Interp.{u}) (σ : Nat → Nat) :
    ∃ x, x ∈ Ed M (den M σ badAssignment (policyPi [.bvar 0] (.bvar 3))) ∧
      ¬ x ∈ Ed M (den M σ badAssignment badType) := by
  have ha : PiErasureAttack.atom ∈ Ed M (tyv PiErasureAttack.domain) :=
    mem_congr_right (ed_tyv M (Or.inr (fun h =>
      tyv_ne_pempty _ (mem_singleton.mp h).symm))).symm (mem_singleton.mpr Equiv.rfl)
  let x := lamVal M (tyv PiErasureAttack.domain) (fun _ => PiErasureAttack.atom)
  refine ⟨x, lam_mem M (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl)
    (fun _ _ => ha), ?_⟩
  intro hx
  have hm := app_mem M (A := tyv PiErasureAttack.domain)
    (B := fun _ => fapp (lamVal M (tyv pempty) (fun z => z)) (tyv PiErasureAttack.domain))
    (fun _ _ _ => Equiv.rfl) hx ha
  have hL : LamProof M (tyv pempty) (fun z => z) := fun _ hz =>
    (not_mem_pempty (mem_congr_right (ed_tyv M (Or.inr not_mem_pempty)) hz)).elim
  have he : Equiv (fapp (lamVal M (tyv pempty) (fun z => z))
      (tyv PiErasureAttack.domain)) pempty := by
    unfold lamVal
    rw [cond_pos hL]
    exact fapp_pempty _
  exact not_mem_pempty (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hm)

def identityEnv (label : Nat) : ResolvedEnv := extendEnv emptyEnv label PiSyntaxAttack.idMember
def identityWfT (label : Nat) : EnvWfT (identityEnv label) :=
  .definition emptyEnv label PiSyntaxAttack.idType PiSyntaxAttack.idBody
    (.imax (.succ PiSyntaxAttack.level) (.succ PiSyntaxAttack.level)) .empty rfl
    (PiSyntaxAttack.idTypeTy _ _ _) (PiSyntaxAttack.idBodyTy _ _ _)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- The body-regularity construction has a real stored definition at EVERY
reference, including labels 1/2. Its table, bound, member soundness and iota
obligations are all paid internally. -/
theorem identity_conditions (P : Premises4) (K : Nat → Nat) (label : Nat) :
    BoundG K (identityWfT label) ∧
      AllSound P (envμ P (identityWfT label)) K (identityEnv label) ∧
      CtorFreeAxFree (identityEnv label) ∧
      ∀ σ, BodiesRegular (mkM P (envμ P (identityWfT label))) σ K (identityEnv label) := by
  have hB : BoundG K (identityWfT label) := by
    simp [identityWfT, BoundG, PiSyntaxAttack.idBodyTy, LOKt, PiSyntaxAttack.level, evalTotal]
  have hEB : EnvBound K (identityWfT label) := hB
  have hC : CtorFreeAxFree (identityEnv label) := by
    intro r m hm
    by_cases hr : r = label
    · subst hr
      rw [show (identityEnv r).members r = some PiSyntaxAttack.idMember from
        members_extend_eq emptyEnv r PiSyntaxAttack.idMember] at hm
      cases hm
      exact ⟨MemberClass.noConfusion, MemberClass.noConfusion⟩
    · rw [show (identityEnv label).members r = none from
        members_extend_ne emptyEnv label PiSyntaxAttack.idMember r hr] at hm
      cases hm
  have hA := allSound_ctorFree P K (identityWfT label) hC hEB _ (faithful_envμ P (identityWfT label)).1
  have hI : ∀ r m, (identityEnv label).members r = some m →
      m.mclass = .recursorM → IotaAt P (envμ P (identityWfT label)) K (identityEnv label) r := by
    intro r m hm hk
    by_cases hr : r = label
    · subst hr
      rw [show (identityEnv r).members r = some PiSyntaxAttack.idMember from
        members_extend_eq emptyEnv r PiSyntaxAttack.idMember] at hm
      cases hm
      cases hk
    · rw [show (identityEnv label).members r = none from
        members_extend_ne emptyEnv label PiSyntaxAttack.idMember r hr] at hm
      cases hm
  exact ⟨hB, hA, hC, fun σ => bodiesRegular_of_bound P _ K (identityWfT label) hB hA hI
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ hm hn => by rw [hm] at hn; cases hn) σ⟩

/-- Elementary reconstruction of the original nested empty-domain fixture's
binder annotations; all codomains read type values, including the empty type. -/
theorem empty_regular (M : Interp.{u}) (σ : Nat → Nat) :
    Regular M σ PiNormalizeAttack.emptyType (PiNormalizeAttack.emptyAssignment M) :=
  ⟨trivial, tyv_ne_pempty _, fun _ _ =>
    ⟨⟨trivial, tyv_ne_pempty _, fun _ _ => ⟨trivial, tyv_ne_pempty _⟩⟩, tyv_ne_pempty _⟩⟩

/-- Full two-way membership on an inhabited erased product with an inner
empty domain, including beta and let presentations. This is a semantic field
fixture; no typing of a fresh inductive group is asserted. -/
theorem empty_presentations_iff (M : Interp.{u}) (σ K : Nat → Nat) :
    (∀ T ∈ [PiNormalizeAttack.emptyType, PiNormalizeAttack.betaEmpty, PiNormalizeAttack.zetaEmpty],
      ∀ x, x ∈ Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ (.bvar 2))
        PiNormalizeAttack.emptyDomains (PiNormalizeAttack.emptyAssignment M)).erasedType M (fun i => i.1)) ↔
        x ∈ Ed M (den M σ (PiNormalizeAttack.emptyAssignment M) T)) ∧
      pempty ∈ Ed M (den M σ (PiNormalizeAttack.emptyAssignment M) PiNormalizeAttack.emptyType) := by
  have hmem := (PiNormalizeAttack.empty_presentations M σ K).1
  have hb : BodiesOK emptyEnv σ K := by intro _ _ _ _ h; cases h
  have hR : BodiesRegular M σ K emptyEnv := by intro _ _ _ _ h; cases h
  have go : ∀ T, T ∈ [PiNormalizeAttack.emptyType, PiNormalizeAttack.betaEmpty,
        PiNormalizeAttack.zetaEmpty] →
      piTelescopeFuel emptyEnv 16 T = some (PiNormalizeAttack.emptyDomains, .bvar 2) →
      InstOK emptyEnv σ K T → Regular M σ T (PiNormalizeAttack.emptyAssignment M) →
      ∀ x, x ∈ Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ (.bvar 2))
        PiNormalizeAttack.emptyDomains (PiNormalizeAttack.emptyAssignment M)).erasedType M (fun i => i.1)) ↔
        x ∈ Ed M (den M σ (PiNormalizeAttack.emptyAssignment M) T) := by
    intro T hT hw hI hreg x
    have hne : ¬ Equiv (den M σ (PiNormalizeAttack.emptyAssignment M) T) pempty := by
      intro h0
      exact not_mem_pempty (mem_congr_right ((ed_congr M h0).trans (ed_pempty M)) (hmem T hT))
    have he := normalizedField_ed M σ K (PiNormalizeAttack.emptySound M σ K)
      hb hR hw hI (PiNormalizeAttack.emptyAssignment M) hne hreg
    exact ⟨mem_congr_right he, mem_congr_right he.symm⟩
  refine ⟨?_, hmem _ (List.mem_cons_self ..)⟩
  intro T hT
  have hT' := hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT'
  rcases hT' with rfl | rfl | rfl
  · exact go _ hT PiNormalizeAttack.emptyRead (by intro _ _ h; cases h) (empty_regular M σ)
  · exact go _ hT PiNormalizeAttack.betaEmptyRead (by intro _ _ h; cases h)
      ⟨⟨trivial, tyv_ne_pempty _, fun _ _ => trivial⟩, empty_regular M σ⟩
  · exact go _ hT PiNormalizeAttack.zetaEmptyRead (by intro _ _ h; cases h)
      ⟨trivial, tyv_ne_pempty _, empty_regular M σ, trivial⟩

/-- A closed, inhabited dependent product, used independently of any
inductive-family table. -/
def closedField : Expr Nat := .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))
def closedDomains : List (Expr Nat) := [.sort .zero, .bvar 0]
def closedFieldTy (E : ResolvedEnv) :
    HasTyT E 0 [] closedField (.sort PiSyntaxAttack.level) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl))
def closedProof : Expr Nat := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))
def closedProofTy (E : ResolvedEnv) : HasTyT E 0 [] closedProof closedField :=
  .lam [] _ _ _ _ (.sort [] .zero)
    (.lam _ _ _ _ _ (.bvar _ 0 _ rfl) (.bvar _ 0 _ rfl))
def closedBeta : Expr Nat := .app PiSyntaxAttack.idBody closedField
def closedDelta (label : Nat) : Expr Nat := .app (.const label []) closedField
def closedZeta : Expr Nat := .letE (.sort PiSyntaxAttack.level) closedField (.bvar 0)
def closedBetaTy (E : ResolvedEnv) :
    HasTyT E 0 [] closedBeta (.sort PiSyntaxAttack.level) :=
  .app [] _ _ _ _ (PiSyntaxAttack.idBodyTy _ _ _) (closedFieldTy E)
def closedDeltaTy (label : Nat) :
    HasTyT (identityEnv label) 0 [] (closedDelta label) (.sort PiSyntaxAttack.level) :=
  .app [] _ _ _ _ (.const [] label [] PiSyntaxAttack.idMember
    (members_extend_eq emptyEnv label _) rfl rfl) (closedFieldTy _)
def closedZetaTy (E : ResolvedEnv) :
    HasTyT E 0 [] closedZeta (.sort PiSyntaxAttack.level) :=
  .letE [] _ _ _ _ _ (.sort [] PiSyntaxAttack.level) (closedFieldTy E) (.bvar _ 0 _ rfl)

/-- Elementary computation of raw/beta/delta/zeta telescopes under a real
stored definition, with no reserved numeric identity. -/
theorem closed_reads (label : Nat) :
    ∀ T ∈ [closedField, closedBeta, closedDelta label, closedZeta],
      piTelescopeFuel (identityEnv label) 16 T = some (closedDomains, .bvar 1) := by
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · simp [closedDelta, piTelescopeFuel, whnfFuel, appsSpine, transparentBody,
      identityEnv, extendEnv, PiSyntaxAttack.idMember, PiSyntaxAttack.idBody,
      PiSyntaxAttack.level, transparent, instantiateLevels, closedField,
      closedDomains, foldApps, instantiate0, instantiate, lift]
  · rfl

/-- Full membership equivalence on a closed inhabited dependent product,
including delta under an actual definition at every numeric reference.
All environment and bound obligations are constructed here. -/
theorem closed_presentations_iff (P : Premises4) (σ K : Nat → Nat)
    (label : Nat) (ρ : Nat → PSet.{4}) :
    let M := mkM P (envμ P (identityWfT label))
    (∀ T ∈ [closedField, closedBeta, closedDelta label, closedZeta],
      ∀ x, x ∈ Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ (.bvar 1))
        closedDomains ρ).erasedType M (fun i => i.1)) ↔ x ∈ Ed M (den M σ ρ T)) ∧
      den M σ ρ closedProof ∈ Ed M (den M σ ρ closedField) := by
  let μ := envμ P (identityWfT label)
  let M := mkM P μ
  obtain ⟨hB, hA, hC, hR⟩ := identity_conditions P K label
  have hE : EnvSound M σ K (identityEnv label) 0 := envSound_of_allSound P hA hC σ 0
  have hb : BodiesOK (identityEnv label) σ K :=
    bodiesOK_of_envWfT K (identityWfT label) hB (fun _ _ h => h)
      (fun _ _ h hn => by rw [h] at hn; cases hn) σ
  have go : ∀ T, T ∈ [closedField, closedBeta, closedDelta label, closedZeta] →
      ∀ (d : HasTyT (identityEnv label) 0 [] T (.sort PiSyntaxAttack.level)),
      LOKt σ 4 K d → ∀ x,
      x ∈ Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ (.bvar 1))
        closedDomains ρ).erasedType M (fun i => i.1)) ↔ x ∈ Ed M (den M σ ρ T) := by
    intro T hT d hd x
    have he := (syntaxCompile_ed M σ (.bvar 1) closedDomains ρ).trans
      (ed_congr M (den_piTelescope_typed4 P μ σ K hE hb (hR σ) d hd
        (closed_reads label T hT) ρ trivial))
    exact ⟨mem_congr_right he, mem_congr_right he.symm⟩
  refine ⟨?_, ?_⟩
  · intro T hT
    have ht := hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact go _ hT (closedFieldTy _) (by
        simp [closedFieldTy, LOKt, PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedBetaTy _) (by
        simp [closedBetaTy, PiSyntaxAttack.idBodyTy, closedFieldTy, LOKt,
          PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedDeltaTy label) (by
        simp [closedDeltaTy, closedFieldTy, LOKt, LevelsOK,
          PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedZetaTy _) (by
        simp [closedZetaTy, closedFieldTy, LOKt, PiSyntaxAttack.level, evalTotal])
  · exact sound_ty (P.good _ rfl) hE (closedProofTy _) (by
      simp [closedProofTy, LOKt, evalTotal]) ρ trivial
end Rcic.F3.PSet.PiHereditaryAttack
