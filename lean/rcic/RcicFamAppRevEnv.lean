import rcic.RcicFamAppRevShape
import rcic.RcicIARecTel
import rcic.RcicParRedSRTyped

/-!
# RcicFamAppRevEnv — the environment of ANY revealed singleton, its copy-only twin, and the translation of its
derivations into any target

`RevEnv` is the environment of interest of the tier's generic B1 shape: a `RevBase` (an in-scope `EnvWfT` base
`E₀` below `f`, a closed level-free index type `I : Sort uI` typed in it) and an `EnvWfT` environment `E` that is
`E₀` below `f`, has the family `F : Π (i : I), Sort 0` at `f`, the constructor `mk : Π (x : I), F x` at `f + 1`, the
AnySort recursor at `f + 2`, and nothing above. Both B1 fixtures are instances (`riEnv`: `f = 0`, `I = Sort 0`,
`E₀` empty; the `Foo` fixture: `f = 4`, `I = Nat`, `E₀` the `Nat` block).

* `R.shapeE : RevShape R.sig R.E` — the environment of interest is a `RevShape` (so its λ-recursor is typed in it).
* `R.twin₁ := R.twinAt (f + 1)` — the copy-only twin with the axiom at the constructor's OWN reference, its rows
  (`twin₁Rows`, from `RcicFamAppRevTwin`), and `R.shapeT : RevShape R.sig R.twin₁`.
* **the forward translation** `trTyW`/`trConvW`/`trTyConvW`/`trCtxWfW`: every derivation of `R.E` becomes a
  derivation of any `RevTwinTarget R.sig G` that agrees with `R.E` below `f`, at the translated terms. Leaves: base
  members are kept (their stored types and bodies are fixed by `tr`, as their constants are members of `E₀`); the
  family and the constructor are kept; `rec.{[l]}` becomes the λ-recursor typed by `irr` (`recTypedW`); a base ι
  step is the transported witness (`derivedIota_tr`); the revealed singleton's ι step is the cell read in the target
  (`iotaConvW`); δ is a base δ. The fixture's translation (`RcicFamAppTwinGeneric.trTyW`) is the instance.

closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin

set_option maxRecDepth 8192

/-! ## §1 the environment of interest -/

/-- the environment of a revealed singleton: a `RevBase` and an `EnvWfT` environment that is the base below `f`,
    the group at `f`, `f + 1`, `f + 2`, and nothing above. -/
structure RevEnv extends RevBase : Type where
  E : ResolvedEnv
  hW : EnvWfT E
  hbase : ∀ r, r < f → E.members r = E₀.members r
  hEf : E.members f = some (revFamM I)
  hEf1 : E.members (f + 1) = some (revCtorM f I)
  hEf2 : E.members (f + 2) = some (revRecM f I)
  habove : ∀ r, f + 2 < r → E.members r = none

namespace RevEnv

variable (R : RevEnv)

/-- the signature. -/
abbrev sig : RevSig := ⟨R.f, R.I, R.uI, R.hclI, R.hlvlI⟩

theorem base_ext : ∀ r m, R.E₀.members r = some m → R.E.members r = some m := fun r m h => by
  rw [R.hbase r (R.hlow r m h)]; exact h

theorem hIfree : occursConst R.f R.I = false :=
  occursConst_false_of_constsIn R.hf0 R.I (hasTyT_constsIn R.hI)

theorem trI : tr R.f R.I R.I = R.I := tr_id_of_hasTyT R.hf2 R.hI

/-- the four kinds of member of `E`. -/
theorem members_class {r : Nat} {m : CheckedMember} (h : R.E.members r = some m) :
    r < R.f ∨ (r = R.f ∧ m = revFamM R.I) ∨ (r = R.f + 1 ∧ m = revCtorM R.f R.I) ∨
      (r = R.f + 2 ∧ m = revRecM R.f R.I) := by
  by_cases hlt : r < R.f
  · exact Or.inl hlt
  by_cases h0 : r = R.f
  · subst h0; rw [R.hEf] at h; exact Or.inr (Or.inl ⟨rfl, (Option.some.inj h).symm⟩)
  by_cases h1 : r = R.f + 1
  · subst h1; rw [R.hEf1] at h; exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj h).symm⟩))
  by_cases h2 : r = R.f + 2
  · subst h2; rw [R.hEf2] at h; exact Or.inr (Or.inr (Or.inr ⟨rfl, (Option.some.inj h).symm⟩))
  · exfalso
    rw [R.habove r (by omega)] at h
    exact Option.noConfusion h

/-- a recursor member is a base recursor or the revealed singleton's. -/
theorem rec_class {r : Nat} {m : CheckedMember} (h : R.E.members r = some m)
    (hk : m.mclass = .recursorM) : r < R.f ∨ r = R.f + 2 := by
  rcases R.members_class h with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hlt
  · exact absurd hk (fun h => MemberClass.noConfusion h)
  · exact absurd hk (fun h => MemberClass.noConfusion h)
  · exact Or.inr rfl

/-- `tr` fixes the stored type of every base member. -/
theorem tr_base_mtype {r : Nat} {m : CheckedMember} (h : R.E₀.members r = some m) :
    tr R.f R.I m.mtype = m.mtype :=
  tr_id_of_cmc R.hf2 (membersClosed_of_envWfT R.hW₀ r m h)

/-- `tr` fixes every instantiated transparent body of a base member. -/
theorem tr_base_body {r : Nat} {m : CheckedMember} {b : Expr Nat} (ls : List Level)
    (h : R.E₀.members r = some m) (htr : transparent m.mclass = true) (hb : m.body = some b) :
    tr R.f R.I (instantiateLevels ls b) = instantiateLevels ls b :=
  tr_id_of_cmc R.hf2 (bodiesClosed_of_envWfT R.hW₀ r m h b htr hb ls)

theorem tr_revFamTy : tr R.f R.I (revFamM R.I).mtype = (revFamM R.I).mtype := by
  show tr R.f R.I (.pi R.I (.sort .zero)) = .pi R.I (.sort .zero)
  simp [tr, R.trI]

theorem tr_revCtorTy : tr R.f R.I (revCtorTy R.f R.I) = revCtorTy R.f R.I := by
  simp [revCtorTy, tr, R.trI, trC_ne R.f R.I (show R.f ≠ R.f + 2 by omega)]

theorem tr_recTyG (l : Level) : tr R.f R.I (recTyG R.f R.I l) = recTyG R.f R.I l := by
  simp [recTyG, motTy, minTy, tr, R.trI, trC_ne R.f R.I (show R.f ≠ R.f + 2 by omega),
    trC_ne R.f R.I (show R.f + 1 ≠ R.f + 2 by omega)]

/-- `tr` fixes the stored type of EVERY member of `E` (the recursor's type mentions `F` and `mk`, not `rec`). -/
theorem tr_mtype {r : Nat} {m : CheckedMember} (h : R.E.members r = some m) :
    tr R.f R.I m.mtype = m.mtype := by
  rcases R.members_class h with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact R.tr_base_mtype (by rw [← R.hbase r hlt]; exact h)
  · exact R.tr_revFamTy
  · exact R.tr_revCtorTy
  · exact R.tr_recTyG (.param 0)

/-! ## §2 `E` as a shape -/

/-- `I : Sort uI` in `E`, at every level bound and context. -/
def hIE (n : Nat) (Γ : LCtx) : HasTyT R.E n Γ R.I (.sort R.uI) := by
  have h0 : HasTyT R.E 0 [] R.I (.sort R.uI) := hasTyTExt R.base_ext R.hI
  have h1 : HasTyT R.E n [] R.I (.sort R.uI) := hasTyT_levelMono (Nat.zero_le n) h0
  have h2 := hasTyTLiftPrefix (envClosed_of_envWfT R.hW) Γ h1
  rw [List.append_nil, lift_of_closed _ (R.hclI 0)] at h2
  exact h2

/-- the environment of interest is a shape of its own signature. -/
def shapeE : RevShape R.sig R.E where
  hfam := R.hEf
  m₁ := revCtorM R.f R.I
  h1 := R.hEf1
  h1t := rfl
  h1a := rfl
  hI := R.hIE

/-! ## §3 the twin with the axiom at the constructor's reference -/

/-- THE TWIN: the base, the family alone, the axiom `mk` at `f + 1`. -/
def twin₁ : ResolvedEnv := R.toRevBase.twinAt (R.f + 1)

theorem twin₁Rows (n : Nat) : TypedRowsWf R.twin₁ n := R.toRevBase.twinRowsAt (R.f + 1) (by omega) n

theorem twin₁_members (r : Nat) :
    R.twin₁.members r = if r = R.f + 1 then some (revAxM R.f R.I)
      else if r = R.f then some (revFamM R.I) else R.E₀.members r := rfl

theorem twin₁_agree (r : Nat) (hr : r < R.f) : R.twin₁.members r = R.E.members r := by
  rw [twin₁_members, if_neg (by omega), if_neg (by omega), R.hbase r hr]

theorem twin₁_f : R.twin₁.members R.f = some (revFamM R.I) := by
  rw [twin₁_members, if_neg (by omega), if_pos rfl]

theorem twin₁_f1 : R.twin₁.members (R.f + 1) = some (revAxM R.f R.I) := by
  rw [twin₁_members, if_pos rfl]

theorem twin₁_f2 : R.twin₁.members (R.f + 2) = none := by
  rw [twin₁_members, if_neg (by omega), if_neg (by omega)]; exact R.hf2

theorem twin₁_ext : ∀ r m, R.E₀.members r = some m → R.twin₁.members r = some m := fun r m h => by
  have := R.hlow r m h
  rw [twin₁_members, if_neg (by omega), if_neg (by omega)]; exact h

/-- the twin's members, read. -/
theorem twin₁_class {r : Nat} {m : CheckedMember} (h : R.twin₁.members r = some m) :
    (r < R.f ∧ R.E₀.members r = some m) ∨ (r = R.f ∧ m = revFamM R.I) ∨ (r = R.f + 1 ∧ m = revAxM R.f R.I) := by
  rw [twin₁_members] at h
  by_cases h1 : r = R.f + 1
  · rw [if_pos h1] at h; exact Or.inr (Or.inr ⟨h1, (Option.some.inj h).symm⟩)
  · rw [if_neg h1] at h
    by_cases h0 : r = R.f
    · rw [if_pos h0] at h; exact Or.inr (Or.inl ⟨h0, (Option.some.inj h).symm⟩)
    · rw [if_neg h0] at h; exact Or.inl ⟨R.hlow r m h, h⟩

theorem twin₁_closed : EnvClosed R.twin₁ := by
  intro r m hm
  rcases R.twin₁_class hm with ⟨_, h0⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact envClosed_of_envWfT R.hW₀ r m h0
  · exact ⟨R.revFamTy_closed, fun b hb => Option.noConfusion hb⟩
  · exact ⟨R.revCtorTy_closed, fun b hb => Option.noConfusion hb⟩

/-- `I : Sort uI` in the twin, at every level bound and context. -/
def hIT (n : Nat) (Γ : LCtx) : HasTyT R.twin₁ n Γ R.I (.sort R.uI) := by
  have h0 : HasTyT R.twin₁ 0 [] R.I (.sort R.uI) := hasTyTExt R.twin₁_ext R.hI
  have h1 : HasTyT R.twin₁ n [] R.I (.sort R.uI) := hasTyT_levelMono (Nat.zero_le n) h0
  have h2 := hasTyTLiftPrefix R.twin₁_closed Γ h1
  rw [List.append_nil, lift_of_closed _ (R.hclI 0)] at h2
  exact h2

/-- the twin is a shape of the same signature. -/
def shapeT : RevShape R.sig R.twin₁ where
  hfam := R.twin₁_f
  m₁ := revAxM R.f R.I
  h1 := R.twin₁_f1
  h1t := rfl
  h1a := rfl
  hI := R.hIT

/-! ## §4 the translation of derivations, `R.E → G` -/

theorem litExp_eq' {t : Nat} {exp : Expr Nat} (h : LiteralExpansion t exp) : exp = natExpand t := by
  cases h; rfl

section Translate

variable {G : ResolvedEnv} {n : Nat}

mutual
theorem trTyW (R : RevEnv) (W : RevTwinTarget R.sig G) (hagree : ∀ r, r < R.f → G.members r = R.E.members r) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT R.E n Γ e A → CtxWfT G n (trCtx R.f R.I Γ) →
    Nonempty (HasTyT G n (trCtx R.f R.I Γ) (tr R.f R.I e) (tr R.f R.I A))
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ =>
      ⟨.bvar _ i (tr R.f R.I A) (by rw [lookupType_trCtx R.hclI, h]; rfl)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      show Nonempty (HasTyT G n (trCtx R.f R.I Γ) (tr R.f R.I (.const r ls))
        (tr R.f R.I (instantiateLevels ls m.mtype)))
      rw [tr_instantiateLevels R.hlvlI, R.tr_mtype hres]
      rcases R.members_class hres with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨.const _ r ls m (by rw [hagree r hlt]; exact hres) hlen hwf⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨.const _ R.f ls (revFamM R.I) W.hfam hlen hwf⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨W.mkConstTy (trCtx R.f R.I Γ) ls hlen hwf⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        have e : instantiateLevels [l] (revRecM R.f R.I).mtype = recTyG R.f R.I l := W.recTyS_inst l
        rw [tr_rec, e]
        exact ⟨W.recTypedW _ l⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hB'⟩ := trTyW R W hagree hB (.assumption _ (tr R.f R.I A) u hΓ' hA')
      exact ⟨.pi _ (tr R.f R.I A) u (tr R.f R.I B) v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ' => by
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hb'⟩ := trTyW R W hagree hbody (.assumption _ (tr R.f R.I A) u hΓ' hA')
      exact ⟨.lam _ (tr R.f R.I A) u (tr R.f R.I body) (tr R.f R.I B) hA' hb'⟩
  | _, _, _, .app Γ g a A B hf ha, hΓ' => by
      obtain ⟨hf'⟩ := trTyW R W hagree hf hΓ'
      obtain ⟨ha'⟩ := trTyW R W hagree ha hΓ'
      show Nonempty (HasTyT G n (trCtx R.f R.I Γ) (.app (tr R.f R.I g) (tr R.f R.I a))
        (tr R.f R.I (instantiate0 a B)))
      rw [tr_instantiate0 R.hclI]
      exact ⟨.app _ (tr R.f R.I g) (tr R.f R.I a) (tr R.f R.I A) (tr R.f R.I B) hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hv'⟩ := trTyW R W hagree hv hΓ'
      obtain ⟨hb'⟩ := trTyW R W hagree hb (.letBinding _ (tr R.f R.I A) u (tr R.f R.I value) hΓ' hA' hv')
      show Nonempty (HasTyT G n (trCtx R.f R.I Γ)
        (.letE (tr R.f R.I A) (tr R.f R.I value) (tr R.f R.I body)) (tr R.f R.I (instantiate0 value B)))
      rw [tr_instantiate0 R.hclI]
      exact ⟨.letE _ (tr R.f R.I A) u (tr R.f R.I value) (tr R.f R.I B) (tr R.f R.I body) hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ' => by
      obtain ⟨h⟩ := trTyW R W hagree hexp hΓ'
      rw [tr_natExpand] at h
      exact ⟨.lit _ t (tr R.f R.I T) h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ' => by
      obtain ⟨h'⟩ := trTyW R W hagree h hΓ'
      obtain ⟨hc'⟩ := trConvW R W hagree hc hΓ'
      exact ⟨.conv _ (tr R.f R.I e) (tr R.f R.I A) (tr R.f R.I B) u h' hc'⟩

theorem trConvW (R : RevEnv) (W : RevTwinTarget R.sig G) (hagree : ∀ r, r < R.f → G.members r = R.E.members r) :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT R.E n Γ a b A → CtxWfT G n (trCtx R.f R.I Γ) →
    Nonempty (ConvT G n (trCtx R.f R.I Γ) (tr R.f R.I a) (tr R.f R.I b) (tr R.f R.I A))
  | _, _, _, _, .refl Γ a A h, hΓ' => by
      obtain ⟨h'⟩ := trTyW R W hagree h hΓ'
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ' => by
      obtain ⟨h'⟩ := trConvW R W hagree h hΓ'
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConvW R W hagree h1 hΓ'
      obtain ⟨h2'⟩ := trConvW R W hagree h2 hΓ'
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ' => by
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hb'⟩ := trTyW R W hagree hbody (.assumption _ (tr R.f R.I A) u hΓ' hA')
      obtain ⟨ha'⟩ := trTyW R W hagree harg hΓ'
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (.app (.lam (tr R.f R.I A) (tr R.f R.I body)) (tr R.f R.I arg))
        (tr R.f R.I (instantiate0 arg body)) (tr R.f R.I (instantiate0 arg B)))
      rw [tr_instantiate0 R.hclI, tr_instantiate0 R.hclI]
      exact ⟨.beta _ (tr R.f R.I A) (tr R.f R.I body) (tr R.f R.I arg) (tr R.f R.I B) u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hv'⟩ := trTyW R W hagree hv hΓ'
      obtain ⟨hb'⟩ := trTyW R W hagree hb (.letBinding _ (tr R.f R.I A) u (tr R.f R.I value) hΓ' hA' hv')
      show Nonempty (ConvT G n (trCtx R.f R.I Γ)
        (.letE (tr R.f R.I A) (tr R.f R.I value) (tr R.f R.I body))
        (tr R.f R.I (instantiate0 value body)) (tr R.f R.I (instantiate0 value B)))
      rw [tr_instantiate0 R.hclI, tr_instantiate0 R.hclI]
      exact ⟨.zeta _ (tr R.f R.I A) (tr R.f R.I value) (tr R.f R.I body) (tr R.f R.I B) u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ' => by
      obtain ⟨hv'⟩ := trTyW R W hagree hv hΓ'
      exact ⟨.zetaLocal _ i (tr R.f R.I A) (tr R.f R.I v) (by rw [lookupValue_trCtx R.hclI, hval]; rfl)
        (by rw [lookupType_trCtx R.hclI, hty]; rfl) hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb, hΓ' => by
      have hlt : r < R.f := by
        rcases R.members_class hres with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hlt
        all_goals exact Option.noConfusion hbody
      have h0 : R.E₀.members r = some m := by rw [← R.hbase r hlt]; exact hres
      obtain ⟨hb'⟩ := trTyW R W hagree hb hΓ'
      have hbfix := R.tr_base_body ls h0 htr hbody
      have hT : tr R.f R.I (instantiateLevels ls m.mtype) = instantiateLevels ls m.mtype := by
        rw [tr_instantiateLevels R.hlvlI, R.tr_mtype hres]
      rw [hbfix, hT] at hb'
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (tr R.f R.I (.const r ls)) (tr R.f R.I (instantiateLevels ls b))
        (tr R.f R.I (instantiateLevels ls m.mtype)))
      rw [hbfix, hT, tr_const_ne R.f R.I (by omega)]
      exact ⟨.delta _ r ls m b (by rw [hagree r hlt]; exact hres) hbody htr hlen hwf hb'⟩
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, hΓ' => by
      obtain ⟨hl'⟩ := trTyW R W hagree hl hΓ'
      obtain ⟨hr'⟩ := trTyW R W hagree hr hΓ'
      cases h with
      | of w =>
        rcases R.rec_class w.hrec w.hrecK with hlt | h2
        · have hfix : tr R.f R.I w.ctorMember.mtype = w.ctorMember.mtype :=
            R.tr_base_mtype (by rw [← R.hbase _ (witness_refs_lt w hlt).1]; exact w.hctor)
          exact ⟨.iota _ _ _ _ (derivedIota_tr R.hclI R.hlvlI hagree w hlt hfix) hl' hr'⟩
        · obtain ⟨ls, lsC, M, m, X, x, hlen, hL, hR⟩ :=
            revIota_inv R.hEf R.hEf1 R.hEf2 R.hlvlI R.hIfree w h2
          obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
          rw [hL] at hl'
          rw [hL, hR]
          have e1 : tr R.f R.I (foldApps (.const (R.f + 2) [l]) [M, m, X, foldApps (.const (R.f + 1) lsC) [x]]) =
              .app (.app (.app (.app (recTG R.f R.I l) (tr R.f R.I M)) (tr R.f R.I m)) (tr R.f R.I X))
                (.app (.const (R.f + 1) lsC) (tr R.f R.I x)) := by
            simp [tr_foldApps, foldApps, tr, trC_rec, trC_ne R.f R.I (show R.f + 1 ≠ R.f + 2 by omega)]
          rw [e1] at hl' ⊢
          exact W.iotaConvW hΓ' l lsC (tr R.f R.I M) (tr R.f R.I m) (tr R.f R.I X) (tr R.f R.I x) (tr R.f R.I T) hl'
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ' => by
      obtain ⟨h'⟩ := trTyW R W hagree hexp hΓ'
      rw [litExp_eq' h] at h' ⊢
      rw [tr_natExpand] at h' ⊢
      exact ⟨.lit _ t (natExpand t) (tr R.f R.I T) (.of t) h'⟩
  | _, _, _, _, .app Γ g g' a b A B h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConvW R W hagree h1 hΓ'
      obtain ⟨h2'⟩ := trConvW R W hagree h2 hΓ'
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (.app (tr R.f R.I g) (tr R.f R.I a))
        (.app (tr R.f R.I g') (tr R.f R.I b)) (tr R.f R.I (instantiate0 a B)))
      rw [tr_instantiate0 R.hclI]
      exact ⟨.app _ (tr R.f R.I g) (tr R.f R.I g') (tr R.f R.I a) (tr R.f R.I b) (tr R.f R.I A) (tr R.f R.I B) h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ' => by
      obtain ⟨hA'⟩ := trConvW R W hagree hA hΓ'
      obtain ⟨hb'⟩ := trConvW R W hagree hb (.assumption _ (tr R.f R.I A) u hΓ' (W.meta.ends hΓ' hA').1)
      exact ⟨.lam _ (tr R.f R.I A) (tr R.f R.I A') (tr R.f R.I b) (tr R.f R.I b') (tr R.f R.I B) u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trConvW R W hagree hA hΓ'
      obtain ⟨hB'⟩ := trConvW R W hagree hB (.assumption _ (tr R.f R.I A) u hΓ' (W.meta.ends hΓ' hA').1)
      exact ⟨.pi _ (tr R.f R.I A) (tr R.f R.I A') (tr R.f R.I B) (tr R.f R.I B') u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trConvW R W hagree hA hΓ'
      obtain ⟨hv'⟩ := trConvW R W hagree hv hΓ'
      obtain ⟨hb'⟩ := trConvW R W hagree hb (.letBinding _ (tr R.f R.I A) u (tr R.f R.I v) hΓ'
        (W.meta.ends hΓ' hA').1 (W.meta.ends hΓ' hv').1)
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (.letE (tr R.f R.I A) (tr R.f R.I v) (tr R.f R.I b))
        (.letE (tr R.f R.I A') (tr R.f R.I v') (tr R.f R.I b')) (tr R.f R.I (instantiate0 v B)))
      rw [tr_instantiate0 R.hclI]
      exact ⟨.letE _ (tr R.f R.I A) (tr R.f R.I A') (tr R.f R.I v) (tr R.f R.I v') (tr R.f R.I b) (tr R.f R.I b')
        (tr R.f R.I B) u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ => by
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (tr R.f R.I (.const r ls)) (tr R.f R.I (.const r ls'))
        (tr R.f R.I (instantiateLevels ls m.mtype)))
      rw [tr_instantiateLevels R.hlvlI, R.tr_mtype hres]
      rcases R.members_class hres with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [tr_const_ne R.f R.I (by omega), tr_const_ne R.f R.I (by omega)]
        exact ⟨.consts _ r ls ls' m (by rw [hagree r hlt]; exact hres) hlen hwf hwf' h⟩
      · rw [tr_const_ne R.f R.I (by omega), tr_const_ne R.f R.I (by omega)]
        exact ⟨.consts _ R.f ls ls' (revFamM R.I) W.hfam hlen hwf hwf' h⟩
      · rw [tr_const_ne R.f R.I (by omega), tr_const_ne R.f R.I (by omega)]
        have c := ConvT.consts (trCtx R.f R.I Γ) (R.f + 1) ls ls' W.m₁ W.h1 (by rw [W.h1a]; exact hlen) hwf hwf' h
        rw [W.h1t] at c
        exact ⟨c⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        rcases ls' with _ | ⟨l', _ | ⟨l'', t⟩⟩
        · exact h.elim
        · have e : instantiateLevels [l] (revRecM R.f R.I).mtype = recTyG R.f R.I l := W.recTyS_inst l
          rw [tr_rec, tr_rec, e]
          exact ⟨W.recConvW _ l l' h.1⟩
        · exact h.2.elim
  | _, _, _, _, .eta Γ g A B h, hΓ' => by
      obtain ⟨h'⟩ := trTyW R W hagree h hΓ'
      show Nonempty (ConvT G n (trCtx R.f R.I Γ) (.lam (tr R.f R.I A) (.app (tr R.f R.I (lift 0 1 g)) (.bvar 0)))
        (tr R.f R.I g) (.pi (tr R.f R.I A) (tr R.f R.I B)))
      rw [tr_lift R.hclI]
      exact ⟨.eta _ (tr R.f R.I g) (tr R.f R.I A) (tr R.f R.I B) h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ' => by
      obtain ⟨hP'⟩ := trTyW R W hagree hP hΓ'
      obtain ⟨hp'⟩ := trTyW R W hagree hp hΓ'
      obtain ⟨hq'⟩ := trTyW R W hagree hq hΓ'
      exact ⟨.irr _ (tr R.f R.I P) (tr R.f R.I p) (tr R.f R.I q) hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ' => by
      obtain ⟨h'⟩ := trConvW R W hagree h hΓ'
      obtain ⟨hA'⟩ := trConvW R W hagree hA hΓ'
      exact ⟨.tyConv _ (tr R.f R.I a) (tr R.f R.I b) (tr R.f R.I A) (tr R.f R.I A') u h' hA'⟩
end

theorem trTyConvW (R : RevEnv) (W : RevTwinTarget R.sig G) (hagree : ∀ r, r < R.f → G.members r = R.E.members r)
    {Γ : LCtx} {a b : Expr Nat} (h : TyConvT R.E n Γ a b) (hΓ' : CtxWfT G n (trCtx R.f R.I Γ)) :
    Nonempty (TyConvT G n (trCtx R.f R.I Γ) (tr R.f R.I a) (tr R.f R.I b)) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := trConvW R W hagree h hΓ'; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem trCtxWfW (R : RevEnv) (W : RevTwinTarget R.sig G) (hagree : ∀ r, r < R.f → G.members r = R.E.members r)
    {Γ : LCtx} (h : CtxWfT R.E n Γ) : Nonempty (CtxWfT G n (trCtx R.f R.I Γ)) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      exact ⟨.assumption _ (tr R.f R.I A) u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := trTyW R W hagree hA hΓ'
      obtain ⟨hv'⟩ := trTyW R W hagree hv hΓ'
      exact ⟨.letBinding _ (tr R.f R.I A) u (tr R.f R.I v) hΓ' hA' hv'⟩

end Translate

end RevEnv

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.RevEnv.shapeE
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.shapeT
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.twin₁Rows
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.trConvW
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.trCtxWfW
