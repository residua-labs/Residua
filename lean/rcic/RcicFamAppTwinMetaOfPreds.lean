import rcic.RcicFamAppTwinGeneric
import rcic.RcicDT0709EnvWf
import rcic.RcicDT1011Rows
import rcic.RcicDTRowFields
import rcic.RcicIotaSRRowsLemmas
import rcic.RcicCtxConvT

/-!
# RcicFamAppTwinMetaOfPreds — the six metatheory facts of a translation target from its base predicates

`TwinMeta G` (`RcicFamAppTwinGeneric`) is what the translation into a twin consumes: regularity, conversion
endpoints, chain collapse at a sort, substitution, type uniqueness (DT-012) and spine inversion. An `EnvWfT`
twin supplies them through the landed wrappers (`TwinMeta.ofEnvWfT`). A COPY-ONLY twin — a recursor-free
environment the copy admits but main's group rule does not — has no `EnvWfT` derivation, so here the six
facts are built from the predicate-level cores (`regularT`, `endpoints3`, `convT_subst0S`, `convT_substLetS`,
`convT_of_tyConvT_sortN`, and the `DT012T_type_uniqueness_of_sortRow_piRow` / `spineInvAux` proofs run over
the predicates instead of an `EnvWfT`): `TwinMeta.ofPreds : BasePreds G → TwinMeta G`, where `BasePreds G`
bundles `EnvClosed`, `EnvMembersSubstStable`, `EnvMembersSortTypedT`, `EnvLevelsT`, `IotaLevelsT` and the
three rows. `RcicFamAppPiRow` (the fixture twin `gEnv₀`) and `RcicFamAppRevTwinMeta` (the twin of any
revealed singleton) both instantiate it. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp

open Rcic.Declarative
open Rcic.Syn

/-- the base predicates of an environment together with its three rows: what the six metatheory facts of a
    translation target are built from when the environment is not an `EnvWfT`. -/
structure BasePreds (G : ResolvedEnv) : Type where
  hcl : EnvClosed G
  hss : EnvMembersSubstStable G
  hms : EnvMembersSortTypedT G
  hEL : EnvLevelsT G
  hIL : IotaLevelsT G
  rows : ∀ n, TypedRowsWf G n

namespace BasePreds

variable {G : ResolvedEnv}

/-- the letBinding head-substitution, from closedness and substitution stability. -/
def substLet (P : BasePreds G) (n : Nat) : SubstLetT G n := fun {_Γ A v _e _B} hv hb => by
  have h0 := hasTyT_substLetS P.hcl P.hss A v (j := 0) hb (by simp)
    (by rw [lift_zero, lift_zero]; exact hv)
  rw [lift_zero] at h0
  exact h0

/-- the level-list congruence at a constant (the `constsRightDataT_of_envWfT` proof over the predicates). -/
def constsRight (P : BasePreds G) (n : Nat) : ConstsRightDataT G n :=
  fun {Γ} _hΓ {_ m ls ls'} hres hlen hwf hwf' heq => by
    have hcl := P.hcl
    obtain ⟨u, hmT⟩ := P.hms _ m hres
    have hlen' : ls'.length = m.arity :=
      (eqNList_length ls ls' heq).symm.trans hlen
    have hc0 : ConvT G n [] (instantiateLevels ls' m.mtype)
        (instantiateLevels ls m.mtype) (.sort (instLevel ls' u)) :=
      convT_instantiateLevels P.hEL P.hIL (eqNList_symm heq) hwf' hwf hlen' hmT
    have hclm : lift 0 1 m.mtype = m.mtype := (hcl _ m hres).1 0
    have hcΓ : ConvT G n Γ (instantiateLevels ls' m.mtype)
        (instantiateLevels ls m.mtype) (.sort (instLevel ls' u)) := by
      have hw := convTLiftPrefix hcl Γ hc0
      simp only [List.append_nil, lift_instantiateLevels, lift] at hw
      rw [lift_of_closed _ hclm 0 Γ.length] at hw
      exact hw
    exact .conv Γ _ _ _ (instLevel ls' u) (.const Γ _ ls' m hres hlen' hwf') hcΓ

theorem regular (P : BasePreds G) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT G n Γ) {e T : Expr Nat}
    (h : HasTyT G n Γ e T) : ∃ w : Level, Nonempty (HasTyT G n Γ T (.sort w)) :=
  let ⟨w, hw⟩ := regularT P.hcl P.hss (P.substLet n) P.hms P.hEL P.hIL
    (P.constsRight n) h hΓ
  ⟨w, ⟨hw⟩⟩

def ends (P : BasePreds G) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT G n Γ) {a b T : Expr Nat}
    (c : ConvT G n Γ a b T) :
    HasTyT G n Γ a T ×' HasTyT G n Γ b T ×' (Σ' w, HasTyT G n Γ T (.sort w)) :=
  endpoints3 P.hcl P.hss (P.substLet n) P.hms P.hEL P.hIL
    (P.constsRight n) c hΓ

def subst0 (P : BasePreds G) {n : Nat} {v t : Expr Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT G n (.assumption t :: Γ) a b T) (hv : HasTyT G n Γ v t) :
    ConvT G n Γ (instantiate0 v a) (instantiate0 v b) (instantiate0 v T) :=
  convT_subst0S P.hcl P.hss h hv

def tyConvSubst0 (P : BasePreds G) {n : Nat} {v t : Expr Nat} {Γ : LCtx} (hv : HasTyT G n Γ v t) :
    {A B : Expr Nat} → TyConvT G n (.assumption t :: Γ) A B →
    TyConvT G n Γ (instantiate0 v A) (instantiate0 v B)
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ u c => .of _ _ _ u (subst0 P c hv)
  | _, _, .trans _ _ _ _ c₁ c₂ => .trans _ _ _ _ (tyConvSubst0 P hv c₁) (tyConvSubst0 P hv c₂)

theorem substLet0TyConv (P : BasePreds G) {n : Nat} {t w0 : Expr Nat} {Γ : LCtx} :
    {X Y : Expr Nat} → TyConvT G n (.letBinding t w0 :: Γ) X Y → HasTyT G n Γ w0 t →
    Nonempty (TyConvT G n Γ (instantiate0 w0 X) (instantiate0 w0 Y))
  | _, _, .refl _ _, _ => ⟨.refl _ _⟩
  | _, _, .of _ _ _ _ hc, hv => by
      have hc' := convT_substLetS P.hcl P.hss t w0 (j := 0) hc (by simp)
        (by rw [lift_zero, lift_zero]; exact hv)
      rw [lift_zero] at hc'
      exact ⟨.of _ _ _ _ hc'⟩
  | _, _, .trans _ _ _ _ h₁ h₂, hv =>
      (substLet0TyConv P h₁ hv).elim fun c₁ =>
        (substLet0TyConv P h₂ hv).elim fun c₂ => ⟨.trans _ _ _ _ c₁ c₂⟩

/-- DT-012 from the predicates (the `DT012T_type_uniqueness_of_sortRow_piRow` proof over the rows and the
    substitution cores instead of an `EnvWfT`): two types of one term are chain-convertible. -/
def uniq (P : BasePreds G) {n : Nat} : {Γ : LCtx} → CtxWfT G n Γ → {e A : Expr Nat} → HasTyT G n Γ e A →
    {B : Expr Nat} → HasTyT G n Γ e B → Nonempty (TyConvT G n Γ A B)
  | _, _, _, _, .sort _ l, _, hB => ⟨hasTyTInv_sortT hB rfl⟩
  | _, _, _, _, .bvar _ _ _ h, _, hB => by
      obtain ⟨A', hlk', hcv⟩ := hasTyTInv_bvar hB rfl
      obtain rfl : A' = _ := Option.some.inj (hlk'.symm.trans h)
      exact ⟨hcv⟩
  | _, _, _, _, .const _ _ _ _ hres _ _, _, hB => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hB rfl
      obtain rfl : m' = _ := Option.some.inj (hres'.symm.trans hres)
      exact ⟨hcv⟩
  | Γ, hΓ, _, _, .pi _ A u _ _ hA hB, _, hBt => by
      obtain ⟨u', v', hA', hB', hcv⟩ := hasTyTInv_pi hBt rfl
      obtain ⟨cA⟩ := uniq P hΓ hA hA'
      have hΓA : CtxWfT G n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := uniq P hΓA hB hB'
      exact ⟨.trans _ _ _ _
        (.of _ _ _ _ (ConvT.sorts _ _ _
          (Ann.eqNA_imax ((P.rows n).sortRow hΓ cA) ((P.rows n).sortRow hΓA cB)))) hcv⟩
  | Γ, hΓ, _, _, .lam _ A u _ _ hA hb, _, hBt => by
      obtain ⟨_, B', _, hb', hcv⟩ := hasTyTInv_lam hBt rfl
      have hΓA : CtxWfT G n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := uniq P hΓA hb hb'
      exact ⟨.trans _ _ _ _ (tyConvT_pi_cod hA cB) hcv⟩
  | _, hΓ, _, _, .app _ _ _ _ _ hf ha, _, hBt => by
      obtain ⟨A', B', hf', _, hcv⟩ := hasTyTInv_app hBt rfl
      obtain ⟨cF⟩ := uniq P hΓ hf hf'
      obtain ⟨cB⟩ := ((P.rows n).piRow hΓ cF).2
      have cI := tyConvSubst0 P ha cB
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | Γ, hΓ, _, _, .letE _ A u v _ _ hA hv hb, _, hBt => by
      obtain ⟨_, B', _, _, hb', hcv⟩ := hasTyTInv_letE hBt rfl
      have hΓL : CtxWfT G n (.letBinding A v :: Γ) := .letBinding Γ A u v hΓ hA hv
      obtain ⟨cB⟩ := uniq P hΓL hb hb'
      obtain ⟨cI⟩ := substLet0TyConv P cB hv
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | _, hΓ, _, _, .lit _ _ _ hexp, _, hBt => by
      obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit hBt rfl
      obtain ⟨c⟩ := uniq P hΓ hexp hnat
      exact ⟨.trans _ _ _ _ c hcv⟩
  | _, hΓ, _, _, .conv _ _ _ _ _ h hc, _, hBt => by
      obtain ⟨c⟩ := uniq P hΓ h hBt
      exact ⟨.trans _ _ _ _ (TyConvT.symmT (.of _ _ _ _ hc)) c⟩

/-- a chain between sort-typed types collapses to one conversion at the left type's sort. -/
theorem collapse (P : BasePreds G) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT G n Γ) {a b : Expr Nat} {u : Level}
    (hA : HasTyT G n Γ a (.sort u)) (h : TyConvT G n Γ a b) :
    Nonempty (ConvT G n Γ a b (.sort u)) :=
  convT_of_tyConvT_sortN (fun {_ _ _ _} hΓ' hc => ⟨(ends P hΓ' hc).1⟩)
    (fun {_ _ _ _} hΓ' h1 h2 => uniq P hΓ' h1 h2) hΓ hA h

/-- spine inversion at the Π row (the `spineInvAux` proof over the predicates). -/
def spineInvAux (P : BasePreds G) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT G n Γ) {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : G.members r = some m) {U : Expr Nat} :
    (rxs rds : List (Expr Nat)) → rds.length = rxs.length →
    instantiateLevels ls m.mtype = policyPi rds.reverse U → {T : Expr Nat} →
    HasTyT G n Γ (foldApps (.const r ls) rxs.reverse) T →
    Nonempty ((ls.length = m.arity) ×' (levelsBounded n ls = true) ×'
      (∀ i x d, rxs.reverse[i]? = some x → rds.reverse[i]? = some d →
        HasTyT G n Γ x (instPrefix (rxs.reverse.take i) d)) ×'
      TyConvT G n Γ (instPrefix rxs.reverse U) T)
  | [], [], _, hpi, T, hT => by
      obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const (r := r) (ls := ls) hT rfl
      have hmeq : m = m' := Option.some.inj (hres.symm.trans hres')
      subst hmeq
      simp only [List.reverse_nil, policyPi] at hpi
      rw [hpi] at hcv
      exact ⟨⟨hlen, hwf, fun i x d hx _ => by
        rw [List.reverse_nil, List.getElem?_nil] at hx; exact Option.noConfusion hx,
        by simpa only [instPrefix_nil] using hcv⟩⟩
  | [], _ :: _, hlen, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen; exact Nat.noConfusion hlen
  | _ :: _, [], hlen, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen; exact Nat.noConfusion hlen
  | y :: rys, D :: rds, hlen, hpi, T, hT => by
      have hlen' : rds.length = rys.length := Nat.succ.inj hlen
      rw [List.reverse_cons, foldApps_snoc] at hT
      obtain ⟨A, B, hf, hy, hc⟩ := hasTyTInv_app hT rfl
      have hpi' : instantiateLevels ls m.mtype = policyPi rds.reverse (.pi D U) := by
        rw [hpi, List.reverse_cons, policyPi_append]; rfl
      obtain ⟨hlsl, hwf, hargs, hconv⟩ := spineInvAux P hΓ hres rys rds hlen' hpi' hf
      rw [instPrefix_pi] at hconv
      obtain ⟨⟨cD⟩, ⟨cU⟩⟩ := (P.rows n).piRow hΓ hconv
      have hy' : HasTyT G n Γ y (instPrefix rys.reverse D) :=
        hasTyT_of_tyConv hy (TyConvT.symmT cD)
      have hsub := tyConvSubst0 P hy' cU
      refine ⟨⟨hlsl, hwf, ?_, ?_⟩⟩
      · intro i x d hx hd
        rw [List.reverse_cons] at hx hd ⊢
        by_cases hi : i < rys.reverse.length
        · rw [List.getElem?_append_left hi] at hx
          have hi' : i < rds.reverse.length := by
            rw [List.length_reverse] at hi ⊢; omega
          rw [List.getElem?_append_left hi'] at hd
          rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
          exact hargs i x d hx hd
        · have hge : rys.reverse.length ≤ i := Nat.le_of_not_lt hi
          rw [List.getElem?_append_right hge] at hx
          have hge' : rds.reverse.length ≤ i := by
            rw [List.length_reverse] at hge ⊢; omega
          rw [List.getElem?_append_right hge'] at hd
          have hi0 : i - rys.reverse.length = 0 := by
            cases hlt : i - rys.reverse.length with
            | zero => rfl
            | succ k =>
                rw [hlt, List.getElem?_cons_succ, List.getElem?_nil] at hx
                exact Option.noConfusion hx
          have hi0' : i - rds.reverse.length = 0 := by
            rw [List.length_reverse] at hi0 ⊢; rw [hlen']; exact hi0
          rw [hi0] at hx
          rw [hi0'] at hd
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hd
          subst hx; subst hd
          have hieq : i = rys.reverse.length := by omega
          rw [hieq, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          exact hy'
      · rw [List.reverse_cons, instPrefix_snoc]
        exact .trans _ _ _ _ hsub hc

def spineInv (P : BasePreds G) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT G n Γ) {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : G.members r = some m) {doms : List (Expr Nat)} {U : Expr Nat}
    (hpi : instantiateLevels ls m.mtype = policyPi doms U) (xs : List (Expr Nat))
    (hlen : doms.length = xs.length) {T : Expr Nat}
    (hT : HasTyT G n Γ (foldApps (.const r ls) xs) T) :
    Nonempty ((ls.length = m.arity) ×' (levelsBounded n ls = true) ×'
      (∀ i x d, xs[i]? = some x → doms[i]? = some d →
        HasTyT G n Γ x (instPrefix (xs.take i) d)) ×'
      TyConvT G n Γ (instPrefix xs U) T) := by
  have h := spineInvAux P hΓ hres xs.reverse doms.reverse
    (by simp only [List.length_reverse]; exact hlen)
    (by rw [List.reverse_reverse]; exact hpi)
    (by rw [List.reverse_reverse]; exact hT)
  rw [List.reverse_reverse, List.reverse_reverse] at h
  exact h


/-- **the six facts from the predicates.** -/
def toTwinMeta (P : BasePreds G) : TwinMeta G where
  regular := fun {_n _Γ} hΓ {_e _T} h => regular P hΓ h
  ends := fun {_n _Γ} hΓ {_a _b _T} c => ends P hΓ c
  collapse := fun {_n _Γ} hΓ {_a _b _u} hA h => collapse P hΓ hA h
  subst0 := fun {_n _v _t _Γ _a _b _T} h hv => subst0 P h hv
  uniq := fun {_n _Γ} hΓ {_e _A} h1 {_B} h2 => uniq P hΓ h1 h2
  spineInv := fun {_n _Γ} hΓ {_r _ls _m} hres {_doms _U} hpi xs hlen {_T} hT =>
    spineInv P hΓ hres hpi xs hlen hT

end BasePreds

/-- a translation target's metatheory from its base predicates and rows, without an `EnvWfT`. -/
def TwinMeta.ofPreds {G : ResolvedEnv} (P : BasePreds G) : TwinMeta G := P.toTwinMeta

/-! ## two generic readers shared by the Π-row assemblies (the fixture's and the generic one) -/

/-- a chain moved along a context conversion (pointwise `convT_ctx`). -/
def tyConvT_ctx₀ {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Γ Γ' : LCtx}
    (hcc : CtxConvT E n Γ Γ') : {A B : Expr Nat} → TyConvT E n Γ A B → TyConvT E n Γ' A B
  | _, _, .refl _ A => .refl Γ' A
  | _, _, .of _ A B u hc => .of Γ' A B u (convT_ctx hcl hcc hc)
  | _, _, .trans _ A B C h1 h2 => .trans Γ' A B C (tyConvT_ctx₀ hcl hcc h1) (tyConvT_ctx₀ hcl hcc h2)

/-- the components of a Π are sort-typed in a well-formed environment whenever a non-trivial chain starts
    at it. -/
theorem piCompsTyped {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B X : Expr Nat} (h : TyConvT E n Γ (.pi A B) X) (hne : (Expr.pi A B : Expr Nat) ≠ X) :
    ∃ u v, Nonempty (HasTyT E n Γ A (.sort u)) ∧
      Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort v)) := by
  rcases TyConvT.firstOf h with he | ⟨C, w, ⟨hstep⟩, _⟩
  · exact absurd he hne
  · have hty := (NativeValleys.convEnds hW hΓ hstep).1
    obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hty rfl
    exact ⟨u, v, ⟨hA⟩, ⟨hB⟩⟩

end Rcic.Syn.FamApp

#print axioms Rcic.Syn.FamApp.TwinMeta.ofPreds
