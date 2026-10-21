import rcic.RcicA2SortSupport
import rcic.RcicDT008Equiv
import rcic.RcicDTRowFields
import rcic.RcicEtaKDecide
import rcic.RcicIotaSRRowsLemmas
import rcic.RcicParRedTConv

/-!
Source-reviewed draft against minustwo/residua
76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. Remains a research draft in scope.

These are constructive supporting lemmas, not a declaration that the full
family row has been compiled or that NativeConvValleys is proved.
The family head argument retains every one of the 18 ParRedT constructors.
The argument-certificate decoder is described separately in nv_family_report.md.
No axiom, sorry, normalization, InScope, or erased-to-native reflection.
closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.NativeFamilyProjection

variable {E : ResolvedEnv} {n : Nat}

def SortRow (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
    TyConvT E n Γ (.sort u) (.sort v) → eqN u v

def PiRow (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- Exact refactor of DT012T_type_uniqueness_of_typedRowsWf:
only the two fields actually consumed by that proof are parameters.
Delegates to the landed `DT012T_type_uniqueness_of_sortRow_piRow`
(`RcicDTRowFields`); `SortRow`/`PiRow` are the same two-field interface. -/
def typeUniq_of_sort_pi (hW : EnvWfT E)
    (hsort : SortRow E n) (hpi : PiRow E n) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    {B : Expr Nat} → HasTyT E n Γ e B → Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW hsort hpi

/-! ## Admission and the non-proof family-head invariant -/

def FamilyArity (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .inductiveM →
    isArity m.mtype = true

theorem familyArity_extend_nonfamily {E : ResolvedEnv} (hE : FamilyArity E)
    (r : Nat) (m : CheckedMember) (hn : m.mclass ≠ .inductiveM) :
    FamilyArity (extendEnv E r m) := by
  intro r' m' hres hcls
  by_cases heq : r' = r
  · subst r'
    simp only [extendEnv, if_pos rfl] at hres
    cases hres
    exact False.elim (hn hcls)
  · simp only [extendEnv, if_neg heq] at hres
    exact hE r' m' hres hcls

theorem familyArity_group {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (g : GroupMembersT S E ms E') :
    FamilyArity E → FamilyArity E' := by
  induction g with
  | nil => exact fun h => h
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro hE
      apply ih
      intro r' m' hres hcls
      by_cases heq : r' = r
      · subst r'
        simp only [extendEnv, if_pos rfl] at hres
        cases hres
        exact harity hcls
      · simp only [extendEnv, if_neg heq] at hres
        exact hE r' m' hres hcls

def familyArity_of_envWfT : {E : ResolvedEnv} → EnvWfT E → FamilyArity E
  | _, .empty => by
      intro r m h
      cases h
  | _, .axiom E r A _ hE .. =>
      familyArity_extend_nonfamily (familyArity_of_envWfT hE)
        r ⟨.axiomM, 0, A, none⟩ (by intro h; cases h)
  | _, .definition E r A v _ hE .. =>
      familyArity_extend_nonfamily (familyArity_of_envWfT hE)
        r ⟨.definitionM, 0, A, some v⟩ (by intro h; cases h)
  | _, .thm E r A p hE .. =>
      familyArity_extend_nonfamily (familyArity_of_envWfT hE)
        r ⟨.theoremM, 0, A, some p⟩ (by intro h; cases h)
  | _, .opaque E r A v _ hE .. =>
      familyArity_extend_nonfamily (familyArity_of_envWfT hE)
        r ⟨.opaqueM, 0, A, some v⟩ (by intro h; cases h)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      familyArity_group hmem (familyArity_of_envWfT hE)

theorem isArity_instantiateLevels (ls : List Level) (T : Expr Nat) :
    isArity (instantiateLevels ls T) = isArity T := by
  induction T <;> simp_all [instantiateLevels, isArity]

theorem arity_not_prop (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) :
    {Γ : LCtx} → CtxWfT E n Γ → {T : Expr Nat} →
    isArity T = true → HasTyT E n Γ T (.sort .zero) → False
  | Γ, hΓ, .sort l, _, hT => by
      have bad := F8A2Support.sort_chain_eq su hW hΓ
        (hasTyTInv_sortT hT rfl)
      have hb := bad (fun _ => none)
      cases he : eval (fun _ => none) l <;> simp [eval, he] at hb
  | Γ, hΓ, .pi A B, hshape, hT => by
      obtain ⟨u, ⟨hA⟩, ⟨hB⟩⟩ :=
        F8A2Support.pi_zero_inv su hW hΓ hT
      exact arity_not_prop hW su (.assumption Γ A u hΓ hA)
        (T := B) hshape hB
  | _, _, .bvar _, h, _ => by cases h
  | _, _, .const _ _, h, _ => by cases h
  | _, _, .app _ _, h, _ => by cases h
  | _, _, .lam _ _, h, _ => by cases h
  | _, _, .letE _ _ _, h, _ => by cases h
  | _, _, .lit _, h, _ => by cases h

/-- Applies to every native prefix, including an unsaturated family constant.
No piRow, uniqueness, saturation, or reduction back-lift occurs here. -/
theorem familyPrefix_not_proof (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hres : E.members r = some m)
    (hcls : m.mclass = .inductiveM) (ls : List Level) (xs : List (Expr Nat)) :
    ¬ F8A2Support.IsProof E n Γ (foldApps (.const r ls) xs) := by
  intro hp
  obtain ⟨P, ⟨hP⟩, ⟨hhead⟩⟩ :=
    F8A2Support.proof_foldApps_head su hW hΓ xs hp
  obtain ⟨m', hres', _, _, c⟩ := hasTyTInv_const hhead rfl
  have hmeq : m' = m := Option.some.inj (hres'.symm.trans hres)
  subst m'
  obtain ⟨hT0⟩ := F8A2Support.sort_transport su hW hΓ c.symmT hP
  apply arity_not_prop hW su hΓ _ hT0
  rw [isArity_instantiateLevels]
  exact familyArity_of_envWfT hW r m hres hcls

structure ProofLeaf (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (p q T : Expr Nat) where
  hT : HasTyT E n Γ T (.sort .zero)
  hp : HasTyT E n Γ p T
  hq : HasTyT E n Γ q T

abbrev Step (Γ : LCtx) (a b T : Expr Nat) :=
  ParRedT (ProofLeaf E n) E n Γ a b T

abbrev Star (Γ : LCtx) (a b T : Expr Nat) :=
  ParRedTStar (ProofLeaf E n) E n Γ a b T

def ProofLeaf.endpoints {Γ : LCtx} {p q T : Expr Nat}
    (h : ProofLeaf E n Γ p q T) :
    HasTyT E n Γ p T × HasTyT E n Γ q T := ⟨h.hp, h.hq⟩

def ProofLeaf.native {Γ : LCtx} {p q T : Expr Nat}
    (h : ProofLeaf E n Γ p q T) : ConvT E n Γ p q T :=
  .irr Γ T p q h.hT h.hp h.hq

theorem family_ne_recursor {r s : Nat} {m q : CheckedMember}
    (hm : E.members r = some m) (hmc : m.mclass = .inductiveM)
    (hq : E.members s = some q) (hqc : q.mclass = .recursorM) : r ≠ s := by
  intro hrs
  subst s
  have hmq : m = q := Option.some.inj (hm.symm.trans hq)
  subst q
  rw [hmc] at hqc
  cases hqc

theorem recursor_head_false {r s : Nat} {m q : CheckedMember}
    (hm : E.members r = some m) (hmc : m.mclass = .inductiveM)
    (hq : E.members s = some q) (hqc : q.mclass = .recursorM)
    {ls ls' : List Level} (h : (Expr.const s ls : Expr Nat) = .const r ls') :
    False :=
  family_ne_recursor hm hmc hq hqc (Expr.const.inj h).1.symm

theorem unionIota_family_source_false {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hmc : m.mclass = .inductiveM) :
    {lhs rhs : Expr Nat} → DerivedIotaU E lhs rhs → {ls : List Level} →
    (appsSpine lhs).1 = .const r ls → False
  | _, _, .ofU w, _, hh =>
      recursor_head_false hm hmc w.hrec w.hrecK
        (by simpa only [iotaLhsOf, recCall, appsSpine_foldApps_const] using hh)
  | _, _, .ofUS w, _, hh =>
      recursor_head_false hm hmc w.hrec w.hrecK
        (by simpa only [iotaLhsOfS, recCall, appsSpine_foldApps_const] using hh)

/-- All 18 current constructors. The only recursive cases with a possible
family source are app's function child and conv; iotaSpine is refuted after
recursing on its original first child. -/
theorem step_family_head (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    (hmc : m.mclass = .inductiveM) :
    {a b T : Expr Nat} → Step (E := E) (n := n) Γ a b T →
    {ls : List Level} → (appsSpine a).1 = .const r ls →
    ∃ ls', (appsSpine b).1 = .const r ls' ∧ eqNList ls ls' ∧
      (appsSpine a).2.length = (appsSpine b).2.length
  | _, _, _, .refl _ _ _ _, ls, hh => ⟨ls, hh, eqNList_refl ls, rfl⟩
  | _, _, _, .sortEq .., _, hh => nomatch hh
  | _, _, _, .consts _ r0 ls0 ls1 _ heq _ _, _, hh => by
      obtain ⟨rfl, rfl⟩ := Expr.const.inj hh
      exact ⟨ls1, rfl, heq, rfl⟩
  | _, _, _, .bvarZeta .., _, hh => nomatch hh
  | _, _, _, .delta _ r0 _ m0 _ _ hres _ htr _ _ _ _, _, hh => by
      have hr : r0 = r := (Expr.const.inj hh).1
      subst r0
      have hmem : m0 = m := Option.some.inj (hres.symm.trans hm)
      subst m0
      simp only [hmc, transparent] at htr
      cases htr
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ _ _, _, hh => by
      obtain ⟨ls', hh', heq, hlen⟩ := step_family_head hW su hΓ hm hmc hf hh
      refine ⟨ls', hh', heq, ?_⟩
      simpa only [appsSpine, List.length_append, List.length_cons,
        List.length_nil] using congrArg (fun k => k + 1) hlen
  | _, _, _, .beta .., _, hh => nomatch hh
  | _, _, _, .lam .., _, hh => nomatch hh
  | _, _, _, .pi .., _, hh => nomatch hh
  | _, _, _, .letE .., _, hh => nomatch hh
  | _, _, _, .zeta .., _, hh => nomatch hh
  | _, _, _, .iotaSpine _ _ _ _ _ hs hi _ _, _, hh => by
      obtain ⟨ls', hh', _, _⟩ := step_family_head hW su hΓ hm hmc hs hh
      exact False.elim (unionIota_family_source_false hm hmc hi hh')
  | _, _, _, .iotaStarK _ w .., _, hh => by
      exact False.elim (recursor_head_false hm hmc w.hrec w.hrecK
        (by simpa only [recCall, appsSpine_foldApps_const] using hh))
  | _, _, _, .iotaStarKEta _ w _ _ _ _ _ _ _ _ happ .., _, hh => by
      exact False.elim (recursor_head_false hm hmc w.hrec w.hrecK
        ((iotaStarKEta_head happ).1.symm.trans hh))
  | _, _, _, .lit .., _, hh => nomatch hh
  | _, _, _, .eta .., _, hh => nomatch hh
  | _, _, _, .peq _ p _ _ hp, ls, hh => by
      have hproof : F8A2Support.IsProof E n Γ
          (foldApps (.const r ls) (appsSpine p).2) := by
        rw [← hh, foldApps_appsSpine]
        exact ⟨_, ⟨hp.hT⟩, ⟨hp.hp⟩⟩
      exact False.elim (familyPrefix_not_proof hW su hΓ hm hmc ls _ hproof)
  | _, _, _, .conv _ _ _ _ _ hs _, _, hh =>
      step_family_head hW su hΓ hm hmc hs hh

theorem star_family_head (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    (hmc : m.mclass = .inductiveM) :
    {a b T : Expr Nat} → Star (E := E) (n := n) Γ a b T →
    {ls : List Level} → (appsSpine a).1 = .const r ls →
    ∃ ls', (appsSpine b).1 = .const r ls' ∧ eqNList ls ls' ∧
      (appsSpine a).2.length = (appsSpine b).2.length
  | _, _, _, .refl _ _ _ _, ls, hh => ⟨ls, hh, eqNList_refl ls, rfl⟩
  | _, _, _, .tail h hs, _, hh => by
      obtain ⟨ls1, hh1, heq1, hlen1⟩ := step_family_head hW su hΓ hm hmc h hh
      obtain ⟨ls2, hh2, heq2, hlen2⟩ := star_family_head hW su hΓ hm hmc hs hh1
      exact ⟨ls2, hh2, F8A2Support.eqNList_trans_local heq1 heq2,
        hlen1.trans hlen2⟩

/-- The head of any natively typed application has a native typing.
This does not infer its canonical telescope and uses no piRow. -/
def typing_foldApps_head :
    (xs : List (Expr Nat)) → {Γ : LCtx} → {f T : Expr Nat} →
    HasTyT E n Γ (foldApps f xs) T → Σ' U : Expr Nat, HasTyT E n Γ f U
  | [], _, _, T, h => ⟨T, h⟩
  | _ :: xs, _, _, _, h => by
      let ⟨_, hfa⟩ := typing_foldApps_head xs h
      let ⟨A, B, hf, _, _⟩ := hasTyTInv_app hfa rfl
      exact ⟨.pi A B, hf⟩

theorem native_level_facts {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) {ls : List Level} {xs : List (Expr Nat)}
    {T : Expr Nat} (h : HasTyT E n Γ (foldApps (.const r ls) xs) T) :
    ls.length = m.arity ∧ levelsBounded n ls = true := by
  let ⟨_, hh⟩ := typing_foldApps_head xs h
  let ⟨m', hm', hlen, hwf, _⟩ := hasTyTInv_const hh rfl
  have heq : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  exact ⟨hlen, hwf⟩

/-! ## Dependent row algebra: the residual is always instantiated by the left -/

/-- The exact residual update used by composition. First change the value in
the LEFT B, then substitute y into the piRow codomain chain. -/
theorem residual_chain (hW : EnvWfT E) (hpi : PiRow E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' x y : Expr Nat} {u : Level}
    (hT : HasTyT E n Γ (.pi A B) (.sort u))
    (d : TyConvT E n Γ (.pi A B) (.pi A' B'))
    (cxy : ConvT E n Γ x y A) :
    Nonempty (TyConvT E n Γ (instantiate0 x B) (instantiate0 y B')) := by
  obtain ⟨_, ⟨dB⟩⟩ := hpi hΓ d
  obtain ⟨uA, vB, hA, hB, _⟩ := hasTyTInv_pi hT rfl
  obtain ⟨⟨hx⟩, ⟨hy⟩⟩ := convT_endpoints hW hΓ cxy
  let cval := convT_inst0_valueSort hA hB hx hy cxy
  let csub := tyConvT_subst0_of_envWfT hW hy dB
  exact ⟨.trans _ _ _ _ (.of _ _ _ vB cval) csub⟩

/-- Different initial telescopes are allowed. Both second-row argument
conversions are reindexed to the first row's current left domain. -/
theorem convArgs_transAcross (hW : EnvWfT E) (hpi : PiRow E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {xs ys : List (Expr Nat)}
    (hxy : ConvArgsT E n Γ T xs ys) :
    ∀ {T' : Expr Nat} {u : Level} {zs : List (Expr Nat)},
      HasTyT E n Γ T (.sort u) →
      TyConvT E n Γ T T' →
      ConvArgsT E n Γ T' ys zs →
      ConvArgsT E n Γ T xs zs := by
  induction hxy with
  | nil T =>
      intro T' u zs hT d hyz
      cases hyz
      exact .nil T
  | cons A B x y xs ys hc hs ih =>
      intro T' u zs hT d hyz
      cases hyz with
      | cons A' B' y z ys zs hcyz hsyz =>
          obtain ⟨cxy⟩ := hc
          obtain ⟨cyz⟩ := hcyz
          obtain ⟨⟨dA⟩, _⟩ := hpi hΓ d
          let cyzA := convT_of_tyConv cyz dA.symmT
          let cxz := ConvT.trans Γ x y z A cxy cyzA
          obtain ⟨dres⟩ := residual_chain hW hpi hΓ hT d cxy
          obtain ⟨uA, vB, hA, hB, _⟩ := hasTyTInv_pi hT rfl
          obtain ⟨⟨hx⟩, _⟩ := convT_endpoints hW hΓ cxy
          have hR : HasTyT E n Γ (instantiate0 x B) (.sort vB) :=
            hasTyT_subst0_of_envWfT hW hB hx
          exact .cons A B x z xs zs ⟨cxz⟩ (ih hR dres hsyz)

/-- The two rows have a shared right argument list. This is the valley
operation. The NEW x-to-y conversion drives the next residual update. -/
theorem convArgs_meetAcross (hW : EnvWfT E) (hpi : PiRow E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {xs zs : List (Expr Nat)}
    (hxz : ConvArgsT E n Γ T xs zs) :
    ∀ {T' : Expr Nat} {u : Level} {ys : List (Expr Nat)},
      HasTyT E n Γ T (.sort u) →
      TyConvT E n Γ T T' →
      ConvArgsT E n Γ T' ys zs →
      ConvArgsT E n Γ T xs ys := by
  induction hxz with
  | nil T =>
      intro T' u ys hT d hyz
      cases hyz
      exact .nil T
  | cons A B x z xs zs hc hs ih =>
      intro T' u ys hT d hyz
      cases hyz with
      | cons A' B' y z ys zs hcyz hsyz =>
          obtain ⟨cxz⟩ := hc
          obtain ⟨cyz⟩ := hcyz
          obtain ⟨⟨dA⟩, _⟩ := hpi hΓ d
          let cyzA := convT_of_tyConv cyz dA.symmT
          let cxy := ConvT.trans Γ x z y A cxz (ConvT.symm Γ y z A cyzA)
          obtain ⟨dres⟩ := residual_chain hW hpi hΓ hT d cxy
          obtain ⟨uA, vB, hA, hB, _⟩ := hasTyTInv_pi hT rfl
          obtain ⟨⟨hx⟩, _⟩ := convT_endpoints hW hΓ cxy
          have hR : HasTyT E n Γ (instantiate0 x B) (.sort vB) :=
            hasTyT_subst0_of_envWfT hW hB hx
          exact .cons A B x y xs ys ⟨cxy⟩ (ih hR dres hsyz)

theorem convArgs_length {Γ : LCtx} {T : Expr Nat}
    {xs ys : List (Expr Nat)} (h : ConvArgsT E n Γ T xs ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons A B x y xs ys h hs ih => exact congrArg Nat.succ ih

/-- Appending the last application argument uses the actual left applyTel
residual. No equality between left and right residual terms is substituted. -/
theorem convArgs_snoc {Γ : LCtx} {T : Expr Nat}
    {xs ys : List (Expr Nat)} (h : ConvArgsT E n Γ T xs ys) :
    ∀ {A B x y : Expr Nat},
      applyTel xs T = some (.pi A B) →
      ConvT E n Γ x y A →
      ConvArgsT E n Γ T (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil T =>
      intro A B x y heval c
      simp only [applyTel] at heval
      cases heval
      exact .cons A B x y [] [] ⟨c⟩ (.nil _)
  | cons A0 B0 x0 y0 xs ys hc hs ih =>
      intro A B x y heval c
      exact .cons A0 B0 x0 y0 (xs ++ [x]) (ys ++ [y]) hc
        (ih heval c)

/-- Native level-instance congruence, independently of family inversion and U.
Both endpoint lists keep their own native length and boundedness receipts. -/
theorem storedLevels_chain (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hres : E.members r = some m) {ls ls' : List Level}
    (hlen : ls.length = m.arity) (_hlen' : ls'.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (heq : eqNList ls ls') :
    Nonempty (TyConvT E n Γ
      (instantiateLevels ls m.mtype) (instantiateLevels ls' m.mtype)) := by
  have hcl := envClosed_of_envWfT hW
  obtain ⟨u, hmT⟩ := envWfT_mtypeSortTyped hW r m hres
  have hc0 : ConvT E n [] (instantiateLevels ls m.mtype)
      (instantiateLevels ls' m.mtype) (.sort (instLevel ls u)) :=
    convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
      heq hwf hwf' hlen hmT
  have hclm : lift 0 1 m.mtype = m.mtype := (hcl r m hres).1 0
  have hcΓ : ConvT E n Γ (instantiateLevels ls m.mtype)
      (instantiateLevels ls' m.mtype) (.sort (instLevel ls u)) := by
    have hw := convTLiftPrefix hcl Γ hc0
    simp only [List.append_nil, lift_instantiateLevels, lift] at hw
    rw [lift_of_closed _ hclm 0 Γ.length] at hw
    exact hw
  exact ⟨.of Γ _ _ (instLevel ls u) hcΓ⟩

/-- Collapse the ORIGINAL TyConvT at its original given left sort.
No piRow or family inversion is used, including in the pure-reflexive case.
Delegates to the landed `F8EtaK.convT_of_tyConvT_sort_of_sortUniq`
(`RcicEtaKDecide`) with `su` eta-expanded to the implicit-binder form. -/
theorem originalTyConv_at_leftSort (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → {u : Level} →
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A B →
    Nonempty (ConvT E n Γ A B (.sort u)) :=
  F8EtaK.convT_of_tyConvT_sort_of_sortUniq hW
    (fun hΓ' h1 h2 => su hW hΓ' h1 h2) hΓ

/-! ## The exact additional certificates sufficient for the family decoder -/


/-- A certificate is required for each argument step exposed while following
the actual function spine. A native conversion of the whole family application
does not replace these proper-child certificates. Every Step constructor
remains in the carrier. This is an explicit stronger output contract, not a
claim that NativeConvValleys already supplies it. -/
def ArgCert :
    {Γ : LCtx} → {a b T : Expr Nat} → Step (E := E) (n := n) Γ a b T → Prop
  | Γ, _, _, _, .app _ _ _ a a' A _ _ _ _ hf _ _ _ _ _ =>
      ArgCert hf ∧ Nonempty (ConvT E n Γ a a' A)
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _ => ArgCert hs
  | _, _, _, _, .conv _ _ _ _ _ hs _ => ArgCert hs
  | _, _, _, _, _ => True

/-- Proposition-valued refactor of all eighteen branches of the pinned
RcicParRedTConv.parRedT_to_convT (lines 127--294). Each recursive certificate
and each uniqueness answer is opened only while proving Nonempty (ConvT ...).
The data-valued upstream API is not called, and no choice converts existence
of uniqueness witnesses into a global data-valued uniqueness supplier.

hIotaS remains an explicit native computation premise for the schema branch.
Neither admission nor endpoint typing is claimed to construct it. -/
theorem parRedT_to_convT_nonempty
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hPEq : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → HasTyT E n Γ' p T × HasTyT E n Γ' q T)
    (hPEqC : ∀ {Γ' : LCtx} {p q T : Expr Nat},
      PEq Γ' p q T → ConvT E n Γ' p q T)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T → HasTyT E n Γ' rhs T →
      ConvT E n Γ' lhs rhs T)
    (hUniq : ∀ {Γ' : LCtx} (_ : CtxWfT E n Γ') {a A B : Expr Nat},
      HasTyT E n Γ' a A → HasTyT E n Γ' a B →
        Nonempty (TyConvT E n Γ' A B)) :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
      Nonempty (ConvT E n Γ a b T)
  | _, _, _, .refl _ _ _ h => ⟨.refl _ _ _ h⟩
  | _, _, _, .sortEq _ _ _ _ h hl _ =>
      ⟨convT_of_tyConv (.sorts _ _ _ h) (hasTyTInv_sortT hl rfl)⟩
  | _, _, _, .consts _ _ _ _ _ h hl hr => by
      obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const hl rfl
      obtain ⟨_, _, _, hwf', _⟩ := hasTyTInv_const hr rfl
      exact ⟨convT_of_tyConv (.consts _ _ _ _ m hres hlen hwf hwf' h) hcv⟩
  | _, _, _, .bvarZeta Γ i A v v' _ h hv hl _ => by
      obtain ⟨A', hlkT, hcv⟩ := hasTyTInv_bvar hl rfl
      have heq : A' = lift 0 (i + 1) A := by
        have h2 := lookupType_getQ_letBinding h
        rw [hlkT] at h2
        injection h2
      subst heq
      have hval : lookupValue Γ i = some (lift 0 (i + 1) v) :=
        lookupValue_getQ_letBinding h
      have hvA : HasTyT E n (Γ.drop (i + 1)) v A :=
        parRedT_hasTy_left hPEq (ctxWfT_drop hΓ (i + 1)) hv
      have hlt : i + 1 ≤ Γ.length := get?_lt_length Γ h
      have hlen : (Γ.take (i + 1)).length = i + 1 := by
        rw [List.length_take]
        exact Nat.min_eq_left hlt
      have hliftv : HasTyT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) A) := by
        have h0 := hasTyTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1)) hvA
        rw [hlen, List.take_append_drop] at h0
        exact h0
      obtain ⟨cv⟩ := parRedT_to_convT_nonempty hW
        (ctxWfT_drop hΓ (i + 1)) hPEq hPEqC hIotaS hUniq hv
      have hliftc : ConvT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) v')
          (lift 0 (i + 1) A) := by
        have h0 := convTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1)) cv
        rw [hlen, List.take_append_drop] at h0
        exact h0
      exact ⟨convT_of_tyConv
        (ConvT.trans Γ (.bvar i) (lift 0 (i + 1) v) (lift 0 (i + 1) v')
          (lift 0 (i + 1) A)
          (ConvT.zetaLocal Γ i _ _ hval hlkT hliftv) hliftc)
        hcv⟩
  | _, _, _, .delta Γ r ls m b _ hres hbody htr hlen hwf hl _ => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hl rfl
      cases hres.symm.trans hres'
      exact ⟨convT_of_tyConv
        (.delta Γ r ls m b hres hbody htr hlen hwf
          (envWfT_bodyTyped hW hres hbody hlen)) hcv⟩
  | _, _, _, .app Γ f f' a a' A B _ _ _ hf hc _ _ ha _ => by
      obtain ⟨cf⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq hf
      obtain ⟨ca⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq ha
      exact ⟨.app Γ f f' a a' A B (convT_of_tyConv cf hc) ca⟩
  | _, _, _, .beta Γ A body body' arg arg' B u v _ hA hB _ hb ha _ => by
      obtain ⟨cb⟩ := parRedT_to_convT_nonempty hW
        (.assumption Γ A u hΓ hA) hPEq hPEqC hIotaS hUniq hb
      obtain ⟨ca⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq ha
      have hbody' := parRedT_hasTy_right hPEq (.assumption Γ A u hΓ hA) hb
      have harg := parRedT_hasTy_left hPEq hΓ ha
      have harg' := parRedT_hasTy_right hPEq hΓ ha
      have capp : ConvT E n Γ (.app (.lam A body) arg) (.app (.lam A body') arg')
          (instantiate0 arg B) :=
        .app Γ _ _ arg arg' A B
          (.lam Γ A A body body' B u (.refl Γ A (.sort u) hA) cb) ca
      have cbeta : ConvT E n Γ (.app (.lam A body') arg')
          (instantiate0 arg' body') (instantiate0 arg' B) :=
        .beta Γ A body' arg' B u hA hbody' harg'
      have cval : ConvT E n Γ (instantiate0 arg' B) (instantiate0 arg B)
          (.sort v) :=
        convT_inst0_valueSort hA hB harg' harg (.symm Γ arg arg' A ca)
      exact ⟨.trans Γ _ _ _ (instantiate0 arg B) capp
        (convT_of_tyConv cbeta (.of _ _ _ v cval))⟩
  | _, _, _, .lam Γ A A' body body' B u _ hc hA _ hb _ => by
      obtain ⟨cb⟩ := parRedT_to_convT_nonempty hW
        (.assumption Γ A u hΓ hA) hPEq hPEqC hIotaS hUniq hb
      exact ⟨.lam Γ A A' body body' B u hc cb⟩
  | _, _, _, .pi Γ A A' B B' u v _ hc _ hcB _ =>
      ⟨.pi Γ A A' B B' u v hc hcB⟩
  | _, _, _, .letE Γ A A' value value' body body' B u _ hc hA hv _ _ hb _ => by
      obtain ⟨cv⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq hv
      obtain ⟨cb⟩ := parRedT_to_convT_nonempty hW
        (.letBinding Γ A u value hΓ hA (parRedT_hasTy_left hPEq hΓ hv))
        hPEq hPEqC hIotaS hUniq hb
      exact ⟨.letE Γ A A' value value' body body' B u hc cv cb⟩
  | _, _, _, .zeta Γ A value value' body body' B u w hA hv hB _ hb _ => by
      obtain ⟨cv⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq hv
      have hvA := parRedT_hasTy_left hPEq hΓ hv
      have hv'A := parRedT_hasTy_right hPEq hΓ hv
      obtain ⟨cb⟩ := parRedT_to_convT_nonempty hW
        (.letBinding Γ A u value hΓ hA hvA) hPEq hPEqC hIotaS hUniq hb
      have hcl := envClosed_of_envWfT hW
      have hB' : HasTyT E n (.letBinding A value' :: Γ) B (.sort w) :=
        hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
          (.symm Γ value value' A cv) hv'A hB
      have hb' : HasTyT E n (.letBinding A value' :: Γ) body' B :=
        hasTyTConvLet hcl (.refl Γ A (.sort u) hA)
          (.symm Γ value value' A cv) hv'A
          (parRedT_hasTy_right hPEq (.letBinding Γ A u value hΓ hA hvA) hb)
      have leg1 : ConvT E n Γ (.letE A value body) (.letE A value' body')
          (instantiate0 value B) :=
        .letE Γ A A value value' body body' B u (.refl Γ A (.sort u) hA) cv cb
      have leg2 : ConvT E n Γ (.letE A value' body') (instantiate0 value' body')
          (instantiate0 value B) :=
        convT_of_tyConv (.zeta Γ A value' body' B u hA hv'A hb')
          (.of _ _ _ w (convT_inst0_valueSortLet hA hv'A hvA hB' hB
            (.symm Γ value value' A cv)))
      exact ⟨.trans Γ _ _ _ _ leg1 leg2⟩
  | _, _, _, .iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs => by
      obtain ⟨cs⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq hstep
      have ci : ConvT E n Γ lhs' rhs T :=
        match derivedIotaU_elim hI with
        | .inl d => .iota Γ lhs' rhs T d hred hrhs
        | .inr t => hIotaS t hred hrhs
      exact ⟨.trans Γ lhs lhs' rhs T cs ci⟩
  | _, _, _, .iotaStarK Γ w major Tm rhs T _ _ _ _ _ hmajor hmk hTm0 hι hlι
        hlhs hrhs => by
      have hlhs' : HasTyT E n Γ
          (.app (foldApps (.const w.recRef w.ls) w.preMajor) major) T := by
        simpa only [recCall, foldApps_snoc] using hlhs
      obtain ⟨A0, B0, hfun, hargM, hcv⟩ := hasTyTInv_app hlhs' rfl
      obtain ⟨cU⟩ := hUniq hΓ hmajor hargM
      have cmaj : ConvT E n Γ major (ctorMajor w) A0 :=
        convT_of_tyConv
          (ConvT.irr Γ Tm major (ctorMajor w) hTm0 hmajor hmk) cU
      have capp : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major)
          (iotaLhsOf w) (instantiate0 major B0) := by
        simp only [recCall, iotaLhsOf, foldApps_snoc]
        exact .app Γ _ _ major (ctorMajor w) A0 B0
          (.refl Γ _ (.pi A0 B0) hfun) cmaj
      have cl : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major)
          (iotaLhsOf w) T := convT_of_tyConv capp hcv
      have ci : ConvT E n Γ (iotaLhsOf w) rhs T :=
        match derivedIotaU_elim hι with
        | .inl d => .iota Γ (iotaLhsOf w) rhs T d hlι hrhs
        | .inr t => hIotaS t hlι hrhs
      exact ⟨.trans Γ _ _ _ T cl ci⟩
  | _, _, _, .iotaStarKEta Γ w f A B Tm rhs u _ _ happ hA hf _ _ _
        hmajor hmk hTm0 hι hlι hlhs hrhs => by
      have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      have hlhs' : HasTyT E n (.assumption A :: Γ)
          (.app (foldApps (.const w.recRef w.ls) w.preMajor) (.bvar 0)) B := by
        simpa only [recCall, foldApps_snoc] using hlhs
      obtain ⟨A0, B0, hfun, hargM, hcv⟩ := hasTyTInv_app hlhs' rfl
      obtain ⟨cU⟩ := hUniq hΓ' hmajor hargM
      have cmaj : ConvT E n (.assumption A :: Γ) (.bvar 0) (ctorMajor w) A0 :=
        convT_of_tyConv
          (ConvT.irr (.assumption A :: Γ) Tm (.bvar 0) (ctorMajor w) hTm0 hmajor hmk) cU
      have capp : ConvT E n (.assumption A :: Γ)
          (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0))
          (iotaLhsOf w) (instantiate0 (.bvar 0) B0) := by
        simp only [recCall, iotaLhsOf, foldApps_snoc]
        exact .app (.assumption A :: Γ) _ _ (.bvar 0) (ctorMajor w) A0 B0
          (.refl (.assumption A :: Γ) _ (.pi A0 B0) hfun) cmaj
      have cl : ConvT E n (.assumption A :: Γ)
          (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0))
          (iotaLhsOf w) B := convT_of_tyConv capp hcv
      have ci : ConvT E n (.assumption A :: Γ) (iotaLhsOf w) rhs B :=
        match derivedIotaU_elim hι with
        | .inl d => .iota (.assumption A :: Γ) (iotaLhsOf w) rhs B d hlι hrhs
        | .inr t => hIotaS t hlι hrhs
      have cbody : ConvT E n (.assumption A :: Γ)
          (.app (lift 0 1 f) (.bvar 0)) rhs B := by
        rw [← happ]
        exact .trans (.assumption A :: Γ) _ _ _ B cl ci
      exact ⟨.trans Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A rhs) (.pi A B)
        (.symm Γ _ _ _ (.eta Γ f A B hf))
        (.lam Γ A A (.app (lift 0 1 f) (.bvar 0)) rhs B u
          (.refl Γ A (.sort u) hA) cbody)⟩
  | _, _, _, .lit Γ t T hexp => ⟨.lit Γ t (natExpand t) T (.of t) hexp⟩
  | _, _, _, .eta Γ f _ A B hf _ => by
      obtain ⟨cf⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq hf
      exact ⟨.trans _ _ _ _ _
        (ConvT.eta Γ f A B (parRedT_hasTy_left hPEq hΓ hf)) cf⟩
  | _, _, _, .peq _ _ _ _ h => ⟨hPEqC h⟩
  | _, _, _, .conv _ _ _ _ _ h hc => by
      obtain ⟨c⟩ := parRedT_to_convT_nonempty hW hΓ hPEq hPEqC hIotaS hUniq h
      exact ⟨convT_of_tyConv c hc⟩

/-- Conditional certificate construction by the proposition-valued back-lift
above. U is constructed from sortRow+piRow at its native Nonempty granularity.
hIotaS remains explicit; it is not supplied by an inverse legacy bridge,
endpoint typing, or mere valley existence. -/
theorem argCert_of_backlift (hW : EnvWfT E)
    (hsort : SortRow E n) (hpi : PiRow E n)
    (hIotaS : ∀ {Γ' : LCtx} {lhs rhs T : Expr Nat},
      DerivedIotaT E lhs rhs → HasTyT E n Γ' lhs T →
      HasTyT E n Γ' rhs T → ConvT E n Γ' lhs rhs T) :
    {Γ : LCtx} → CtxWfT E n Γ → {a b T : Expr Nat} →
    (s : Step (E := E) (n := n) Γ a b T) → ArgCert s
  | Γ, hΓ, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _ => by
      refine ⟨argCert_of_backlift hW hsort hpi hIotaS hΓ hf, ?_⟩
      exact parRedT_to_convT_nonempty hW hΓ ProofLeaf.endpoints ProofLeaf.native hIotaS
        (fun hΓ' _ _ _ ha hb =>
          typeUniq_of_sort_pi hW hsort hpi hΓ' ha hb) ha
  | _, hΓ, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _ =>
      argCert_of_backlift hW hsort hpi hIotaS hΓ hs
  | _, hΓ, _, _, _, .conv _ _ _ _ _ hs _ =>
      argCert_of_backlift hW hsort hpi hIotaS hΓ hs
  | _, _, _, _, _, .refl _ _ _ _ => True.intro
  | _, _, _, _, _, .sortEq _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .consts _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .bvarZeta _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .lit _ _ _ _ => True.intro
  | _, _, _, _, _, .eta _ _ _ _ _ _ _ => True.intro
  | _, _, _, _, _, .peq _ _ _ _ _ => True.intro

inductive CertifiedStar (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Type
  | refl (a T : Expr Nat) (h : HasTyT E n Γ a T) : CertifiedStar Γ a a T
  | tail {a b c T : Expr Nat} (s : Step (E := E) (n := n) Γ a b T)
      (hc : ArgCert s) (rest : CertifiedStar Γ b c T) : CertifiedStar Γ a c T

structure CertifiedValley (Γ : LCtx) (a b T : Expr Nat) where
  centre : Expr Nat
  left : CertifiedStar (E := E) (n := n) Γ a centre T
  right : CertifiedStar (E := E) (n := n) Γ b centre T

def NativeCertifiedConvValleys (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b T : Expr Nat},
    ConvT E n Γ a b T →
      Nonempty (CertifiedValley (E := E) (n := n) Γ a b T)

/-
Remaining mathematical decoder is given constructively in nv_family_report.md:
(1) prefixInv from stored arity, piRow and scoped sort-Pi separation;
(2) certified app projection via original ArgCert and left residual domain;
(3) convArgs_transAcross over stars;
(4) convArgs_meetAcross on the two valley paths;
(5) original TyConvT collapse at its given left sorting.

No claim that these final five interfaces have been compiled is made here.
The draft deliberately does not insert opaque assumptions named after them.
-/

end Rcic.Declarative.NativeFamilyProjection


