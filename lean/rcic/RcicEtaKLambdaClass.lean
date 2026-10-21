import rcic.RcicEtaKDescendants
namespace Rcic.Declarative.F8EtaK.A2
set_option maxRecDepth 8192

def LamClass (e : Expr Nat) : Prop := ∃ A, e = .lam A (.bvar 1)
section LambdaClass
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {R : Prop}
variable (emitLam : ∀ {A P}, HasTyT E n Γ P (.sort .zero) →
  HasTyT E n Γ (.lam A (.bvar 1)) P → R)
variable (emitMinor : ∀ {A P}, CtxWfT E n (.assumption A :: Γ) → HasTyT E n (.assumption A :: Γ) P (.sort .zero) →
  HasTyT E n (.assumption A :: Γ) (.bvar 1) P → R)
include emitLam emitMinor in
theorem raw_lam_or (hΓ : CtxWfT E n Γ) : {a b T : Expr Nat} → PEqT E n Γ a b →
    HasTyT E n Γ a T → (A : Expr Nat) → a = .lam A (.bvar 1) → LamClass b ∨ R
  | _, _, _, .lam _ A0 A' _ _ _ hb, ht, A, he => by
      obtain ⟨u, B, hA, hbody, hidx⟩ := hasTyTInv_lam ht rfl
      have hΓA := CtxWfT.assumption Γ A0 u hΓ hA
      cases he
      rcases raw_var_or (R := R) (emitMinor hΓA) hb rfl with hb' | hr
      · exact .inl ⟨A', congrArg (Expr.lam A') hb'⟩
      · exact .inr hr
  | _, _, _, .proof _ _ _ _ _ hP _ hp _, _, A, he => by
      cases he
      exact .inr (emitLam hP hp)
  | _, _, _, .bvar .., _, _, he => nomatch he
  | _, _, _, .sort .., _, _, he => nomatch he
  | _, _, _, .const .., _, _, he => nomatch he
  | _, _, _, .app .., _, _, he => nomatch he
  | _, _, _, .pi .., _, _, he => nomatch he
  | _, _, _, .letE .., _, _, he => nomatch he
  | _, _, _, .lit .., _, _, he => nomatch he

include emitLam emitMinor in
theorem par_lam_or (hΓ : CtxWfT E n Γ) (hz : ∀ A v, Γ.get? 0 ≠ some (.letBinding A v)) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T →
    (A : Expr Nat) → a = .lam A (.bvar 1) → LamClass b ∨ R
  | _, _, _, .refl _ _ _ _, A, he => .inl ⟨A, he⟩
  | _, _, _, .lam _ A0 A' _ _ _ u _ _ hA _ hb _, A, he => by
      have hz' : ∀ B v, (LocalDecl.assumption A0 :: Γ).get? 1 ≠ some (.letBinding B v) := hz
      cases he
      rcases par_var_or hz' (emitMinor (.assumption Γ A0 u hΓ hA)) hb rfl with hb' | hr
      · exact .inl ⟨A', congrArg (Expr.lam A') hb'⟩
      · exact .inr hr
  | _, _, _, .iotaSpine _ _ _ _ _ hs hi _ _, A, he => by
      rcases par_lam_or hΓ hz hs A he with hc | hr
      · rcases hc with ⟨A', he'⟩
        exact False.elim (iota_not_lam hi he')
      · exact .inr hr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, he =>
      False.elim (const_spine_not_lam (xs := w.preMajor ++ [major]) he)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, he => by
      obtain ⟨_, _, happ0⟩ := iotaStarKEta_appParts happ
      nomatch he.symm.trans happ0
  | _, _, _, .peq _ _ _ _ leaf, A, he => raw_lam_or emitLam emitMinor hΓ leaf.1 leaf.2.1 A he
  | _, _, _, .conv _ _ _ _ _ h _, A, he => par_lam_or hΓ hz h A he
  | _, _, _, .sortEq .., _, he => nomatch he
  | _, _, _, .consts .., _, he => nomatch he
  | _, _, _, .bvarZeta .., _, he => nomatch he
  | _, _, _, .delta .., _, he => nomatch he
  | _, _, _, .app .., _, he => nomatch he
  | _, _, _, .beta .., _, he => nomatch he
  | _, _, _, .pi .., _, he => nomatch he
  | _, _, _, .letE .., _, he => nomatch he
  | _, _, _, .zeta .., _, he => nomatch he
  | _, _, _, .lit .., _, he => nomatch he
  | _, _, _, .eta .., _, he => nomatch he
end LambdaClass
end Rcic.Declarative.F8EtaK.A2
