import rcic.RcicEtakMovingMinorPeak
import rcic.RcicEtakMovingMinorUnion
import rcic.RcicEtaKHeadInvariant
import rcic.RcicEtaKDecide
import rcic.RcicA2SortSupport

/-!
Exact-source all18 successor control for the moving-minor Eq peak.
Pin: 76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. No sorry/axiom.
The conclusions retain explicit proof-escape alternatives. No global
confluence, native normalization, InScope, type uniqueness, or sort
uniqueness is used by the successor controls themselves.
closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.NativeMovingMinor76

open F8EtaK (Const65SpineAt HasConst65ProofRoot)

/-- A native inclusion of the proof-only leaf into the existing native
heterogeneous proof relation, at unchanged context/endpoints/index. -/
def leafMap {Gamma : LCtx} {p q T : Expr Nat}
    (h : ProofLeaf eqEnvT 2 Gamma p q T) : PEqLeafT eqEnvT 2 Gamma p q T :=
  ⟨.proof Gamma p q T T h.hT h.hT h.hp h.hq, h.hp, h.hq⟩

def mapStep : {Gamma : LCtx} → {a b T : Expr Nat} → Step Gamma a b T →
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 Gamma a b T
  | _, _, _, _, .refl Gamma a T h => .refl Gamma a T h
  | _, _, _, _, .sortEq Gamma l k T h hl hr => .sortEq Gamma l k T h hl hr
  | _, _, _, _, .consts Gamma r ls ms T h hl hr => .consts Gamma r ls ms T h hl hr
  | _, _, _, _, .bvarZeta Gamma i A v v' T h hv hl hr =>
      .bvarZeta Gamma i A v v' T h (mapStep hv) hl hr
  | _, _, _, _, .delta Gamma r ls m b T h hb ht hn hw hl hr =>
      .delta Gamma r ls m b T h hb ht hn hw hl hr
  | _, _, _, _, .app Gamma f f' a a' A B T v w hf hc hB hTy ha hr =>
      .app Gamma f f' a a' A B T v w (mapStep hf) hc hB hTy (mapStep ha) hr
  | _, _, _, _, .beta Gamma A b b' a a' B u v w hA hB hTy hb ha hr =>
      .beta Gamma A b b' a a' B u v w hA hB hTy (mapStep hb) (mapStep ha) hr
  | _, _, _, _, .lam Gamma A A' b b' B u v hc hA hB hb hr =>
      .lam Gamma A A' b b' B u v hc hA hB (mapStep hb) hr
  | _, _, _, _, .pi Gamma A A' B B' u v hA hc hB hcB hr =>
      .pi Gamma A A' B B' u v hA hc hB hcB hr
  | _, _, _, _, .letE Gamma A A' v v' b b' B u w hc hA hv hB hTy hb hr =>
      .letE Gamma A A' v v' b b' B u w hc hA (mapStep hv) hB hTy (mapStep hb) hr
  | _, _, _, _, .zeta Gamma A v v' b b' B u w hA hv hB hTy hb hr =>
      .zeta Gamma A v v' b b' B u w hA (mapStep hv) hB hTy (mapStep hb) hr
  | _, _, _, _, .iotaSpine Gamma a b c T h hi hb hc =>
      .iotaSpine Gamma a b c T (mapStep h) hi hb hc
  | _, _, _, _, .iotaStarK Gamma w major P rhs T rl afs
      hrl hsel hfam hm hc hP hi hli hl hr =>
      .iotaStarK Gamma w major P rhs T rl afs hrl hsel hfam hm hc hP hi hli hl hr
  | _, _, _, _, .iotaStarKEta Gamma w f A B P rhs u rl afs
      happ hA hf hrl hsel hfam hm hc hP hi hli hl hr =>
      .iotaStarKEta Gamma w f A B P rhs u rl afs
        happ hA hf hrl hsel hfam hm hc hP hi hli hl hr
  | _, _, _, _, .lit Gamma t T h => .lit Gamma t T h
  | _, _, _, _, .eta Gamma f f' A B hf hl => .eta Gamma f f' A B (mapStep hf) hl
  | _, _, _, _, .peq Gamma p q T h => .peq Gamma p q T (leafMap h)
  | _, _, _, _, .conv Gamma a b T U h hc => .conv Gamma a b T U (mapStep h) hc

def LeftClass (e : Expr Nat) : Prop :=
  Const65SpineAt [two] 5 e ∨ ∃ A, e = .lam A movingMinor

def RecProofEscape (Gamma : LCtx) : Prop :=
  HasConst65ProofRoot eqEnvT 2 Gamma [two] 5

theorem leftClass_initial : LeftClass leftEnd :=
  .inl ⟨[two], [.sort .zero, propParam, motive, movingMinor, propParam],
    rfl, rfl, eqNList_refl _⟩

/-- Every witness for an eta-K step whose source is this EXACT F(v)
returns the unchanged, still-beta-headed v. Arbitrary hI : DerivedIotaU
is reduced by the all-witness union theorem, not assumed canonical. -/
theorem etaK_rhs_fixed {w : IotaWitness eqEnvT} {f rhs : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (heq : f = leftEnd) (hi : DerivedIotaU eqEnvT (iotaLhsOf w) rhs) :
    rhs = movingMinor := by
  have hd := iotaStarKEta_head happ
  rw [heq] at hd
  have hh : Expr.const 65 [two] = Expr.const w.recRef w.ls := hd.1
  have hr : w.recRef = 65 := (Expr.const.inj hh).1.symm
  have hls : w.ls = [two] := (Expr.const.inj hh).2.symm
  have hp : w.preMajor =
      [.sort .zero, propParam, motive, movingMinor, propParam] := hd.2.1.symm
  apply NativeMovingMinorUnion76.unionRhs hi [two]
    (.sort .zero) propParam motive movingMinor propParam (ctorMajor w)
  simp only [iotaLhsOf, hr, hls, hp]

/-- Full 18-constructor source control. The only recursive calls with
source F(v) are on original conv.h and iotaSpine.hstep children.
The app function child has four arguments, so the landed all18 <5
theorem applies; there is no NoEtaKStep restriction anywhere. -/
theorem leftStepControl {Gamma : LCtx} :
    {a b T : Expr Nat} → Step Gamma a b T → a = leftEnd →
    LeftClass b ∨ RecProofEscape Gamma
  | _, _, _, .refl _ _ _ _, heq => by
      rw [heq]
      exact .inl leftClass_initial
  | _, _, _, .app _ f f' a a' _ _ _ _ _ hf _ _ _ _ha _, heq => by
      have hparts : f = foldApps (.const 65 [two])
          [.sort .zero, propParam, motive, movingMinor] := (Expr.app.inj heq).1
      rcases F8EtaK.parRedT_const65_spine_lt5 (mapStep hf) hparts rfl
        (by decide) (eqNList_refl [two]) with hsp | hpr
      · obtain ⟨ls, xs, he, hl, hls⟩ := hsp
        refine .inl (.inl ⟨ls, xs ++ [a'], ?_, ?_, hls⟩)
        · rw [he, foldApps_snoc]
        · simp only [List.length_append, List.length_singleton, hl]
          rfl
      · exact .inr (F8EtaK.hasConst65ProofRoot_mono (by decide) hpr)
  | _, _, _, .iotaSpine _ _ _ _ _ h hi _ _, heq => by
      rcases leftStepControl h heq with hcl | hpr
      · rcases hcl with hsp | hlam
        · obtain ⟨ls, xs, he, hl, _⟩ := hsp
          exact False.elim (F8EtaK.short_rec65_not_derivedIotaU
            (by omega) hi he)
        · obtain ⟨A, he⟩ := hlam
          exact False.elim (F8EtaK.derivedIotaU_lam_source_false hi he)
      · exact .inr hpr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      False.elim (F8EtaK.short_rec65_not_K_source
        (ls := [two])
        (xs := [.sort .zero, propParam, motive, movingMinor, propParam])
        (by decide) w major heq)
  | _, _, _, .iotaStarKEta _ w f A B P rhs u rl afs
      happ _ _ _ _ _ _ _ _ hi _ _ _, heq =>
      .inl (.inr ⟨A, congrArg (Expr.lam A) (etaK_rhs_fixed happ heq hi)⟩)
  | _, _, _, .peq _ _ _ T h, heq => by
      rw [heq] at h
      exact .inr ⟨[two],
        [.sort .zero, propParam, motive, movingMinor, propParam], T,
        Nat.le_refl _, eqNList_refl _, ⟨h.hT⟩, ⟨h.hp⟩⟩
  | _, _, _, .conv _ _ _ _ _ h _, heq => leftStepControl h heq
  | _, _, _, .sortEq .., heq => nomatch heq
  | _, _, _, .consts .., heq => nomatch heq
  | _, _, _, .bvarZeta .., heq => nomatch heq
  | _, _, _, .delta .., heq => nomatch heq
  | _, _, _, .beta .., heq => nomatch heq
  | _, _, _, .lam .., heq => nomatch heq
  | _, _, _, .pi .., heq => nomatch heq
  | _, _, _, .letE .., heq => nomatch heq
  | _, _, _, .zeta .., heq => nomatch heq
  | _, _, _, .lit .., heq => nomatch heq
  | _, _, _, .eta .., heq => nomatch heq

def ProofRoot (Gamma : LCtx) (e : Expr Nat) : Prop :=
  ∃ P, Nonempty (HasTyT eqEnvT 2 Gamma P (.sort .zero)) ∧
    Nonempty (HasTyT eqEnvT 2 Gamma e P)

def SortLamClass (e : Expr Nat) : Prop :=
  ∃ A u, e = .lam A (.sort u) ∧ eqN u .zero

/-- The second disjunct carries the actual binder-sorting receipt,
so a later independent SU theorem can construct its precise CtxWfT. -/
def SortLamProofEscape (Gamma : LCtx) : Prop :=
  (∃ A u, ProofRoot Gamma (.lam A (.sort u))) ∨
  (∃ A u v, Nonempty (HasTyT eqEnvT 2 Gamma A (.sort v)) ∧
    ProofRoot (.assumption A :: Gamma) (.sort u))

theorem iotaU_not_sort {lhs rhs : Expr Nat} {u : Level}
    (hi : DerivedIotaU eqEnvT lhs rhs) (heq : lhs = .sort u) : False := by
  cases hi with
  | ofU w =>
      rw [iotaLhsOf, recCall, foldApps_snoc] at heq
      cases heq
  | ofUS w =>
      rw [iotaLhsOfS, recCall, foldApps_snoc] at heq
      cases heq

theorem sortStepControl {Gamma : LCtx} :
    {a b T : Expr Nat} → Step Gamma a b T → ∀ (u : Level), a = .sort u →
    (∃ v, b = .sort v ∧ eqN u v) ∨ ProofRoot Gamma (.sort u)
  | _, _, _, .refl _ _ _ _, u, heq => .inl ⟨u, heq, eqN_refl u⟩
  | _, _, _, .sortEq _ _ v _ h _ _, u, heq => by
      cases heq
      exact .inl ⟨v, rfl, h⟩
  | _, _, _, .iotaSpine _ _ _ _ _ h hi _ _, u, heq => by
      rcases sortStepControl h u heq with ⟨v, hb, _⟩ | hpr
      · exact False.elim (iotaU_not_sort hi hb)
      · exact .inr hpr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, heq => by
      rw [recCall, foldApps_snoc] at heq
      cases heq
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _, _, heq => by
      have hh := (iotaStarKEta_head happ).1
      rw [heq] at hh
      exact nomatch hh
  | _, _, _, .peq _ _ _ T h, _, heq => by
      rw [heq] at h
      exact .inr ⟨T, ⟨h.hT⟩, ⟨h.hp⟩⟩
  | _, _, _, .conv _ _ _ _ _ h _, u, heq => sortStepControl h u heq
  | _, _, _, .consts .., _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app .., _, heq => nomatch heq
  | _, _, _, .beta .., _, heq => nomatch heq
  | _, _, _, .lam .., _, heq => nomatch heq
  | _, _, _, .pi .., _, heq => nomatch heq
  | _, _, _, .letE .., _, heq => nomatch heq
  | _, _, _, .zeta .., _, heq => nomatch heq
  | _, _, _, .lit .., _, heq => nomatch heq
  | _, _, _, .eta .., _, heq => nomatch heq

theorem lamSortStepControl {Gamma : LCtx} :
    {a b T : Expr Nat} → Step Gamma a b T →
    ∀ (A : Expr Nat) (u : Level), a = .lam A (.sort u) →
    (∃ A' v, b = .lam A' (.sort v) ∧ eqN u v) ∨ SortLamProofEscape Gamma
  | _, _, _, .refl _ _ _ _, A, u, heq => .inl ⟨A, u, heq, eqN_refl u⟩
  | _, _, _, .lam _ A0 A' body body' B v w _ hA _ hb _, A, u, heq => by
      have hdom := (Expr.lam.inj heq).1
      have hbody := (Expr.lam.inj heq).2
      subst A0
      rcases sortStepControl hb u hbody with ⟨u', he, hu⟩ | hpr
      · exact .inl ⟨A', u', congrArg (Expr.lam A') he, hu⟩
      · exact .inr (.inr ⟨A, u, v, ⟨hA⟩, hpr⟩)
  | _, _, _, .eta _ _ _ _ _ _ _, _, _, heq => by
      have hbody := (Expr.lam.inj heq).2
      cases hbody
  | _, _, _, .iotaSpine _ _ _ _ _ h hi _ _, A, u, heq => by
      rcases lamSortStepControl h A u heq with ⟨A', v, hb, _⟩ | hpr
      · exact False.elim (F8EtaK.derivedIotaU_lam_source_false hi hb)
      · exact .inr hpr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq =>
      False.elim (F8EtaK.foldApps_const_ne_lam_any
        (xs := w.preMajor ++ [major]) heq)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => by
      have hh := (iotaStarKEta_head happ).1
      rw [heq] at hh
      exact nomatch hh
  | _, _, _, .peq _ _ _ T h, A, u, heq => by
      rw [heq] at h
      exact .inr (.inl ⟨A, u, T, ⟨h.hT⟩, ⟨h.hp⟩⟩)
  | _, _, _, .conv _ _ _ _ _ h _, A, u, heq => lamSortStepControl h A u heq
  | _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, .pi .., _, _, heq => nomatch heq
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, .lit .., _, _, heq => nomatch heq

theorem sortLamStarControl {Gamma : LCtx} :
    {a b T : Expr Nat} → Star Gamma a b T → SortLamClass a →
    SortLamClass b ∨ SortLamProofEscape Gamma
  | _, _, _, .refl _ _ _ _, h => .inl h
  | _, _, _, .tail h hs, ⟨A, u, he, hu⟩ => by
      rcases lamSortStepControl h A u he with ⟨A', v, hb, huv⟩ | hpr
      · exact sortLamStarControl hs
          ⟨A', v, hb, eqN_trans (eqN_symm huv) hu⟩
      · exact .inr hpr

theorem leftClass_not_sortLam {e : Expr Nat}
    (hL : LeftClass e) (hR : SortLamClass e) : False := by
  obtain ⟨A, u, he, _⟩ := hR
  rcases hL with ⟨ls, xs, hs, _, _⟩ | ⟨B, hb⟩
  · rw [hs] at he
    exact F8EtaK.foldApps_const_ne_lam_any he
  · have hbody := (Expr.lam.inj (hb.symm.trans he)).2
    cases hbody

/-- UNCONDITIONAL precise escape theorem. It also covers the reversed
asymmetric tile: rightEnd takes arbitrary many steps, leftEnd at most one.
The theorem asserts an explicit typing escape, not its impossibility. -/
theorem optionalAgainstStar_implies_escape {Gamma : LCtx} {j T : Expr Nat}
    (hL : leftEnd = j ∨ Nonempty (Step Gamma leftEnd j T))
    (hR : Star Gamma rightEnd j T) :
    RecProofEscape Gamma ∨ SortLamProofEscape Gamma := by
  have hLc : LeftClass j ∨ RecProofEscape Gamma := by
    rcases hL with he | hsn
    · rw [← he]
      exact .inl leftClass_initial
    · exact hsn.elim fun hs => leftStepControl hs rfl
  have hRc : SortLamClass j ∨ SortLamProofEscape Gamma :=
    sortLamStarControl hR ⟨domain, .zero, rfl, eqN_refl .zero⟩
  rcases hLc with hcL | hprL
  · rcases hRc with hcR | hprR
    · exact False.elim (leftClass_not_sortLam hcL hcR)
    · exact .inr hprR
  · exact .inl hprL

/-! Discharge of the explicit escapes under independent native SU.
No theorem here constructs that SU from actualEnvWf. -/

theorem sort_not_proof (su : F8A2Support.SortUnique eqEnvT 2)
    {Gamma : LCtx} (hGamma : CtxWfT eqEnvT 2 Gamma) (u : Level) :
    ¬ ProofRoot Gamma (.sort u) := by
  rintro ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  have c := hasTyTInv_sortT hp rfl
  obtain ⟨h0⟩ := F8A2Support.sort_transport su actualEnvWf hGamma c.symmT hP
  have bad := su actualEnvWf hGamma (.sort Gamma (.succ u)) h0
    (fun _ => some 0)
  cases he : eval (fun _ => some 0) u <;>
    simp [eval, he, Option.map] at bad

theorem sortLam_no_escape (su : F8A2Support.SortUnique eqEnvT 2)
    {Gamma : LCtx} (hGamma : CtxWfT eqEnvT 2 Gamma) :
    ¬ SortLamProofEscape Gamma := by
  rintro (⟨A, u, P, ⟨hP⟩, ⟨hp⟩⟩ | ⟨A, u, v, ⟨hA⟩, hpr⟩)
  · obtain ⟨v, B, hA, hb, c⟩ := hasTyTInv_lam hp rfl
    obtain ⟨hpi0⟩ := F8A2Support.sort_transport su actualEnvWf hGamma c.symmT hP
    obtain ⟨_, _, ⟨hB0⟩⟩ := F8A2Support.pi_zero_inv su actualEnvWf hGamma hpi0
    exact sort_not_proof su (.assumption Gamma A v hGamma hA) u
      ⟨B, ⟨hB0⟩, ⟨hb⟩⟩
  · exact sort_not_proof su (.assumption Gamma A v hGamma hA) u hpr

theorem eqRecSort_two {ls : List Level} (hls : eqNList ls [two]) :
    eval (fun _ => some 0) (instLevel ls F8EtaK.eqRecSort) = some 3 := by
  cases ls with
  | nil => cases hls
  | cons u rest =>
      cases rest with
      | cons _ _ => cases hls.2
      | nil =>
          have hu : eval (fun _ => some 0) u = some 2 := hls.1 (fun _ => some 0)
          simp [instLevel, lvlSubst, levelParamSubst, F8EtaK.eqRecSort,
            eval, hu, Option.bind, Option.map] <;> rfl

theorem rec_no_escape (su : F8A2Support.SortUnique eqEnvT 2)
    {Gamma : LCtx} (hGamma : CtxWfT eqEnvT 2 Gamma) :
    ¬ RecProofEscape Gamma := by
  rintro ⟨ls, xs, P, _, hls, ⟨hP⟩, ⟨hp⟩⟩
  have hhead := F8A2Support.proof_foldApps_head su actualEnvWf hGamma xs
    (show F8A2Support.IsProof eqEnvT 2 Gamma
      (foldApps (.const 65 ls) xs) from ⟨P, ⟨hP⟩, ⟨hp⟩⟩)
  obtain ⟨Q, ⟨hQ⟩, ⟨hc⟩⟩ := hhead
  obtain ⟨m, hres, hlen, hwf, c⟩ := hasTyTInv_const hc rfl
  have hm : m = eqRecT := (Option.some.inj hres).symm
  subst m
  let hcl := envClosed_of_envWfT actualEnvWf
  have hclosed := (hcl 65 eqRecT rfl).1
  have hi := hasTyT_instLevels (envWfT_levels actualEnvWf)
    (iotaLevelsT_of_envWfT actualEnvWf) hwf hlen F8EtaK.eqRecMtypeTy
  have hstored := hasTyTLiftPrefix hcl Gamma hi
  rw [lift_instantiateLevels, lift_of_closed _ (hclosed 0)] at hstored
  simp only [List.append_nil, instLvlsCtx, List.map_nil,
    instantiateLevels, lift] at hstored
  obtain ⟨hzero⟩ := F8A2Support.sort_transport su actualEnvWf hGamma c.symmT hQ
  have heq := su actualEnvWf hGamma hstored hzero (fun _ => some 0)
  have h3 := eqRecSort_two hls
  have bad : (some 3 : Option Nat) = some 0 := h3.symm.trans heq
  cases bad

/-- Conditional negative for the all18 native Step carrier. SU is explicit.
This is NOT an unconditional countermodel from EnvWfT alone. -/
theorem no_optional_against_star_of_SU
    (su : F8A2Support.SortUnique eqEnvT 2) {j : Expr Nat}
    (hL : leftEnd = j ∨ Nonempty (Step [] leftEnd j commonType))
    (hR : Star [] rightEnd j commonType) : False := by
  rcases optionalAgainstStar_implies_escape hL hR with hr | hs
  · exact rec_no_escape su actualCtxWf hr
  · exact sortLam_no_escape su actualCtxWf hs

theorem no_zero_or_one_common_of_SU
    (su : F8A2Support.SortUnique eqEnvT 2) :
    ¬ ∃ j, (leftEnd = j ∨ Nonempty (Step [] leftEnd j commonType)) ∧
      (rightEnd = j ∨ Nonempty (Step [] rightEnd j commonType)) := by
  rintro ⟨j, hL, hR⟩
  rcases hR with he | hne
  · subst he
    exact no_optional_against_star_of_SU su hL
      (.refl [] rightEnd commonType (rightTy []))
  · exact hne.elim fun h =>
      no_optional_against_star_of_SU su hL
        (.tail h (.refl [] j commonType
          (parRedT_hasTy_right NativeHereditaryPaths76.leafTy
            actualCtxWf h)))

end Rcic.Declarative.NativeMovingMinor76
