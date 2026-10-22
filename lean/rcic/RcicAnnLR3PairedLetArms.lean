import rcic.RcicAnnLR3PairedArms
import rcic.RcicAnnLR3UnitTranslate
import rcic.RcicAnnLR3NeutralCodes
import rcic.RcicAnnSpineConv

/-!
# Let-substitution paired arms at the unit-model interpretation

Supplies the three let-substitution contracts of `RcicAnnLR3PairedArms`:

* `Ty_letE` — typing of `letE` at the instantiated codomain;
* `Conv_zeta` — the ζ conversion `letE ⟶ instantiate0A`;
* `Conv_letE` — letE congruence.

All three are proved at the **actual** interpretation: the `AnnSemantics`
whose image is `UnitTranslate.denote ν ρ e = denI ρ (translate ν e)`.

## Evaluator laws (paired form)

The unary laws landed in `RcicAnnLR3UnitTranslate` —
`denote_substitution`, `beta_sound`, `zeta_sound` — are repackaged here:

* `denote_instantiate0_cons`: `denote ν ρ (instantiate0A s e)` denotes as `e`
  at the environment extended by `denote ν ρ s` (the `j = 0` corner of
  `denote_substitution`, with `liftA 0 0 s = s` and `insert ρ 0 = cons`).
* `denote_letE_cons`: `denote ν ρ (.letE A v b)` denotes as `b` at the
  environment extended by `denote ν ρ v` (`zeta_sound` then
  `denote_instantiate0_cons`).
* `el_valueEq` / `codeElement_valueEq`: the concrete `NeutralCodes` element
  relations are closed under `ValueEq` in each argument, so semantic
  equations can be moved inside element relations.
* `code_valueEq`: a code can be re-presented at a `ValueEq`-equal value.

`approxI_sortTerm_env` proves that the closed sort code does not depend on
the environment — this is what `AnnSemantics.sort_image` needs from the
actual interpretation, since `universeValue` is defined at `EnvI.bot`.

## Arms

* `ty_letE_supplied`, `conv_zeta_supplied` close their contracts directly.
* `conv_letE_supplied` needs the extended context
  `.letBinding A v :: Γ` to be well-formed for the body induction
  hypothesis. `CtxWfA.letBinding` asks for `HasTyA Γ A (.sort u)` and
  `HasTyA Γ v A` — the LEFT typings of the `ConvA` premises. Those are the
  regularity projections `convA_hasTy_left`, which require the environment
  hypotheses `EnvClosedA E`, `IotaLiftA I`, `IotaRecHeadA E I`,
  `IotaSubstA I`. They are named hypotheses of the supplier, explained
  above; nothing else is assumed.

`closure_claim = 0`.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Rcic.Declarative.Ann.LR3.PairedLetRoute
open Rcic.Declarative
open TypedStatements PairedStatements
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER NeutralCodes

variable (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)

/-! ## §1 The closed sort code ignores the environment -/

/-- `sortTerm k` is a closed constant spine: every `ApproxI` derivation for
it replays verbatim at any other environment. -/
theorem approxI_sortTerm_env (ρ σ : EnvI) (k : Option Nat) {c : CptI}
    (h : ApproxI ρ (sortTerm k) c) : ApproxI σ (sortTerm k) c := by
  rcases approxI_app_inv h with hc | happ | hsp
  · subst hc
    exact .bot _ _
  · obtain ⟨g, s, _, hf, _, _⟩ := happ
    rcases approxI_app_inv hf with hb | ⟨g', s', hg, hf', _, _⟩
      | ⟨r', args', u', hs', hf', _⟩
    · cases hb
    · rcases approxI_const_inv hf' with hb | hb <;> cases hb
    · cases hs'
  · obtain ⟨r, args, u, hc, hf, ha⟩ := hsp
    -- The level payload of the tag head replays at any environment.
    have hlevel : ∀ (i : Option Nat) {τ : EnvI} {x : CptI},
        ApproxI τ (levelTerm i) x → ApproxI σ (levelTerm i) x := by
      intro i τ x hlt
      rcases approxI_const_inv hlt with hb | hb
      · subst hb; exact .bot _ _
      · subst hb; exact .const _ _ _
    rcases approxI_app_inv hf with hb | ⟨g', s', hg, hf', _, _⟩
      | ⟨r', args', u', hs', hf', ha'⟩
    · cases hb
    · rcases approxI_const_inv hf' with hb | hb <;> cases hb
    · -- `hs' : .spine r args = .spine r' (args' ++ [u'])`; the const head
      -- forces `r' = 10`, `args' = []`.
      cases hs'
      rcases approxI_const_inv hf' with hb | hb
      · cases hb
      · cases hb
        -- `hf` is now `ApproxI σ F (.spine 10 [u'])` via the rebuilt spine.
        have hF : ApproxI σ (.app (.const 10 []) (levelTerm (k.map Nat.succ)))
            (.spine 10 ([] ++ [u'])) :=
          .appSpine (.const σ 10 []) (hlevel _ ha')
        rcases approxI_app_inv ha with hb | ⟨g', s', hg, hf', _, _⟩
          | ⟨r', args', u', hs', hf', ha'⟩
        · -- `u = .bot`: the tail is the bottom compact.
          subst hb
          subst hc
          exact .appSpine hF (.bot _ _)
        · rcases approxI_const_inv hf' with hb | hb <;> cases hb
        · cases hs'
          rcases approxI_const_inv hf' with hb | hb
          · cases hb
          · cases hb
            subst hc
            exact .appSpine hF (.appSpine (.const σ 11 []) (hlevel _ ha'))

/-- The denotation of the closed sort code is environment-independent. -/
theorem denI_sortTerm_env (ρ σ : EnvI) (k : Option Nat) :
    ValueEq (denI ρ (sortTerm k)) (denI σ (sortTerm k)) :=
  fun _ => ⟨approxI_sortTerm_env ρ σ k, approxI_sortTerm_env σ ρ k⟩

/-! ## §2 The unit-model semantics and its evaluator laws -/

/-- The attached source image is the actual interpretation. -/
def denoteImage (ν : Valuation) (_Γ : LCtxA) (ρ : EnvI) (e : ExprA) : Value :=
  UnitModel.denote ν ρ e

/-- Sort codes evaluate to the compact universe; the `ρ`-indexed denotation
equals `universeValue` after `denI_sortTerm_env`. -/
theorem denoteImage_sort (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (l : Level) :
    denoteImage ν Γ ρ (.sort l) = universeValue (eval ν l) :=
  valueEq_eq (denI_sortTerm_env ρ EnvI.bot (eval ν l))

/-- The `AnnSemantics` whose image is the unit-model denotation. -/
def denoteSemantics : AnnSemantics :=
  NeutralCodes.annSemantics denoteImage denoteImage_sort

/-- The `j = 0` corner of `denote_substitution`: instantiating `bvar 0` with
`s` denotes as the body under the environment extended by `denote ν ρ s`. -/
theorem denote_instantiate0_cons (ν : Valuation) (ρ : EnvI) (s e : ExprA) :
    ValueEq (UnitModel.denote ν ρ (instantiate0A s e))
      (UnitModel.denote ν (EnvI.cons (UnitModel.denote ν ρ s) ρ) e) := by
  intro c
  have h := UnitModel.denote_substitution ν ρ 0 s e c
  rw [liftA_zero] at h
  rw [EnvI.insert_zero] at h
  have hdrop : EnvI.drop ρ 0 = ρ := rfl
  rw [hdrop] at h
  show UnitModel.denote ν ρ (instantiate0A s e) c ↔ _
  unfold instantiate0A
  exact h

/-- ζ-evaluation and substitution: `letE` denotes as its body under the
extended environment. -/
theorem denote_letE_cons (ν : Valuation) (ρ : EnvI) (A v b : ExprA) :
    ValueEq (UnitModel.denote ν ρ (.letE A v b))
      (UnitModel.denote ν (EnvI.cons (UnitModel.denote ν ρ v) ρ) b) :=
  ValueEq.trans (UnitModel.zeta_sound ν ρ A v b)
    (denote_instantiate0_cons ν ρ v b)

/-! ## §3 ValueEq-respect of the concrete element relations -/

/-- `Neutral` is extensional under `ValueEq`. -/
theorem neutral_valueEq {x x' : Value} (h : ValueEq x x') :
    Neutral x → Neutral x' :=
  fun ⟨r, hr⟩ => ⟨r, (NeutralPER.atomNeutral_extensional r h).mp hr⟩

theorem neutral_extensional : NeutralPER.ExtensionalNeutral Neutral :=
  fun h => Iff.intro (neutral_valueEq h) (neutral_valueEq h.symm)

/-- `ProofMember` is extensional under `ValueEq` whenever its neutral
predicate is. -/
theorem proofMember_valueEq {N : NeutralPER.NeutralPredicate}
    (hN : NeutralPER.ExtensionalNeutral N) (P : Prop) {x x' : Value}
    (h : ValueEq x x') : NeutralPER.ProofMember N P x → NeutralPER.ProofMember N P x' := by
  rintro (⟨hP, hx⟩ | hx)
  · exact Or.inl ⟨hP, h.symm.trans hx⟩
  · exact Or.inr ((hN h).mp hx)

/-- Every descriptor's element relation respects `ValueEq` pointwise. -/
theorem el_valueEq (d : Descriptor) {x x' y y' : Value}
    (hx : ValueEq x x') (hy : ValueEq y y') :
    El d x y → El d x' y' := by
  cases d with
  | neutralType k name =>
      rintro ⟨hx', hy'⟩
      exact ⟨proofMember_valueEq neutral_extensional False hx hx',
        proofMember_valueEq neutral_extensional False hy hy'⟩
  | proof P =>
      rintro ⟨hx', hy'⟩
      exact ⟨proofMember_valueEq neutral_extensional P hx hx',
        proofMember_valueEq neutral_extensional P hy hy'⟩
  | univ k =>
      rintro ⟨d', e', hd', hr', hxd', hye'⟩
      exact ⟨d', e', hd', hr', hx.symm.trans hxd', hy.symm.trans hye'⟩

/-- A code of `V` is equally a code of any `ValueEq`-equal value. -/
theorem code_valueEq {k : Option Nat} {V W : Value} {R : Relation}
    (hW : ValueEq W V) (hc : Code k V R) : Code k W R := by
  obtain ⟨d, hd, hv, hr⟩ := hc
  exact ⟨d, hd, hW.trans hv, hr⟩

/-- Element relations assigned by concrete codes respect `ValueEq` in each
argument — the paired form in which `zeta_sound` and substitution move
inside the element position of a `PairedJudgment`. -/
theorem codeElement_valueEq {k : Option Nat} {V : Value} {R : Relation}
    {x x' y y' : Value} (hc : Code k V R)
    (hx : ValueEq x x') (hy : ValueEq y y') (h : R x y) : R x' y' := by
  obtain ⟨d, _, _, hr⟩ := hc
  exact (hr x' y').mpr (el_valueEq d hx hy ((hr x y).mp h))

/-! ## §4 The let-substitution arms -/

/-- `PairedArms.Ty_letE` at the unit-model interpretation. Every source
premise and induction hypothesis position is retained; `ih_hA` and `ih_hTy`
are unused because the body induction hypothesis already carries the
substituted-type code pair. -/
theorem ty_letE_supplied : PairedArms.Ty_letE denoteSemantics E I n := by
  intro Γ A u w value B body hA hv hTy hb ih_hA ih_hv ih_hTy ih_hb hΓ ν μ ρ σ hν hρ
  obtain ⟨kv, Rv, Sv, hcpv, hrelv⟩ := ih_hv hΓ ν μ ρ σ hν hρ
  have hΓ' : CtxWfA E I n (.letBinding A value :: Γ) := .letBinding hΓ hA hv
  have hρ' : PairedRealises denoteSemantics ν μ (.letBinding A value :: Γ)
      (EnvI.cons (UnitModel.denote ν ρ value) ρ)
      (EnvI.cons (UnitModel.denote μ σ value) σ) :=
    .letBinding hρ hcpv hrelv
      (TypedPER.left_member (denoteSemantics.lawful hcpv.left_code) hrelv)
      (hcpv.to_right (TypedPER.right_member (denoteSemantics.lawful hcpv.left_code) hrelv))
  obtain ⟨kb, Rb, Sb, hcpb, hrelb⟩ := ih_hb hΓ' ν μ
    (EnvI.cons (UnitModel.denote ν ρ value) ρ)
    (EnvI.cons (UnitModel.denote μ σ value) σ) hν hρ'
  exact ⟨kb, Rb, Sb,
    ⟨code_valueEq (denote_instantiate0_cons ν ρ value B) hcpb.left_code,
      code_valueEq (denote_instantiate0_cons μ σ value B) hcpb.right_code,
      hcpb.transport⟩,
    codeElement_valueEq hcpb.left_code
      (denote_letE_cons ν ρ A value body).symm
      (denote_letE_cons μ σ A value body).symm hrelb⟩

/-- `PairedArms.Conv_zeta` at the unit-model interpretation. The reduct
induction hypothesis carries the instantiated images; `zeta_sound` moves
the letE denotation onto it. -/
theorem conv_zeta_supplied : PairedArms.Conv_zeta denoteSemantics E I n := by
  intro Γ A value body B u hA hv hb hred ih_hA ih_hv ih_hb ih_hred hΓ ν μ ρ σ hν hρ
  obtain ⟨kT, RT, ST, hcpT, hrelT⟩ := ih_hred hΓ ν μ ρ σ hν hρ
  exact ⟨kT, RT, ST, hcpT,
    codeElement_valueEq hcpT.left_code
      (UnitModel.zeta_sound ν ρ A value body).symm (ValueEq.refl _) hrelT⟩

/-- `PairedArms.Conv_letE` at the unit-model interpretation.

Named premise — the regularity hypotheses `(hE, hI, hR, hIS)`: the body
induction hypothesis lives in `.letBinding A v :: Γ`, and `CtxWfA` of that
context requires the left typings `HasTyA Γ A (.sort u)` and `HasTyA Γ v A`.
No arm premise stores them (`hb`'s context contains the binding but `ConvA`
does not retain context well-formedness); the only landed supplier is the
regularity projection `convA_hasTy_left`, which requires exactly these four
environment hypotheses. Everything else in the arm is discharged. -/
theorem conv_letE_supplied (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) :
    PairedArms.Conv_letE denoteSemantics E I n := by
  intro Γ A A' v v' b b' B u hA hv hb hrt ih_hA ih_hv ih_hb ih_hrt hΓ ν μ ρ σ hν hρ
  obtain ⟨kv, Rv, Sv, hcpv, hrelv⟩ := ih_hv hΓ ν μ ρ σ hν hρ
  obtain ⟨k2, Rv2, Sv2, hcp2, hrel2⟩ := ih_hv hΓ μ μ σ σ
    (ValuationRel.refl μ) hρ.right_diagonal
  -- `right_value`: `Sv` sees the right-world stored source `v`, while the
  -- extended right environment holds `v'`; the μ-diagonal of `hv` plus
  -- code coherence close the gap.
  have hright : Sv (UnitModel.denote μ σ v') (UnitModel.denote μ σ v) :=
    (denoteSemantics.lawful hcpv.right_code).symm
      ((denoteSemantics.coherent hcp2.right_code hcpv.right_code _ _).mp
        ((hcp2.transport _ _).mp hrel2))
  have hΓ' : CtxWfA E I n (.letBinding A v :: Γ) :=
    .letBinding hΓ (convA_hasTy_left hE hI hR hIS hΓ hA)
      (convA_hasTy_left hE hI hR hIS hΓ hv)
  have hρ' : PairedRealises denoteSemantics ν μ (.letBinding A v :: Γ)
      (EnvI.cons (UnitModel.denote ν ρ v) ρ)
      (EnvI.cons (UnitModel.denote μ σ v') σ) :=
    .letBinding hρ hcpv hrelv
      (TypedPER.left_member (denoteSemantics.lawful hcpv.left_code) hrelv) hright
  obtain ⟨kb, Rb, Sb, hcpb, hrelb⟩ := ih_hb hΓ' ν μ
    (EnvI.cons (UnitModel.denote ν ρ v) ρ)
    (EnvI.cons (UnitModel.denote μ σ v') σ) hν hρ'
  obtain ⟨kT, RT, ST, hcpT, _⟩ := ih_hrt hΓ ν μ ρ σ hν hρ
  refine ⟨kT, RT, ST, hcpT, ?_⟩
  have hcRT : Code kT
      (UnitModel.denote ν (EnvI.cons (UnitModel.denote ν ρ v) ρ) B) RT :=
    code_valueEq (denote_instantiate0_cons ν ρ v B).symm hcpT.left_code
  have hRb : RT (UnitModel.denote ν (EnvI.cons (UnitModel.denote ν ρ v) ρ) b)
      (UnitModel.denote μ (EnvI.cons (UnitModel.denote μ σ v') σ) b') :=
    (denoteSemantics.coherent hcRT hcpb.left_code _ _).mpr hrelb
  exact codeElement_valueEq hcpT.left_code
    (denote_letE_cons ν ρ A v b).symm (denote_letE_cons μ σ A' v' b').symm hRb

end Rcic.Declarative.Ann.LR3.PairedLetRoute
