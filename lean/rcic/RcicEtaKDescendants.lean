import rcic.RcicEtaKHeadInvariant

/-! A2: exact arity and descendant-class analysis for the original positive Eq
peak. No original reduction constructor changes. closure_claim = 0. -/
namespace Rcic.Declarative.F8EtaK.A2
set_option maxRecDepth 8192
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

theorem witness_arity (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  rw [w.hpre]
  exact hn

theorem witnessS_arity (w : IotaWitnessS eqEnvT) (hr : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  rw [w.hpre]
  exact hn

theorem const_spine_not_lam {r : Nat} {ls : List Level} {xs : List (Expr Nat)}
    {A b : Expr Nat} (h : foldApps (.const r ls) xs = .lam A b) : False := by
  have hh := congrArg (fun e => (appsSpine e).1) h
  change (appsSpine (foldApps (.const r ls) xs)).1 = Expr.lam A b at hh
  rw [appsSpine_foldApps_const] at hh
  cases hh

theorem iota_not_var {lhs rhs : Expr Nat} (h : DerivedIotaU E lhs rhs)
    {i : Nat} (he : lhs = .bvar i) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_bvar (.const w.recRef w.ls) (ctorMajor w) w.preMajor he
  | ofUS w =>
      exact foldApps_snoc_ne_bvar (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) w.preMajor he

theorem iota_not_lam {lhs rhs A b : Expr Nat} (h : DerivedIotaU E lhs rhs)
    (he : lhs = .lam A b) : False := by
  cases h with
  | ofU w => exact const_spine_not_lam (xs := w.preMajor ++ [ctorMajor w]) he
  | ofUS w =>
      exact const_spine_not_lam
        (xs := w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]) he

theorem call_not_short (w : IotaWitness eqEnvT) (major : Expr Nat)
    {ls : List Level} {xs : List (Expr Nat)} (hn : xs.length < 6)
    (he : recCall (.const w.recRef w.ls) w.preMajor major =
      foldApps (.const 65 ls) xs) : False := by
  have hs := congrArg appsSpine he
  change appsSpine (foldApps (.const w.recRef w.ls) (w.preMajor ++ [major])) = _ at hs
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  have hh := congrArg Prod.fst hs
  have hx := congrArg Prod.snd hs
  have hr : w.recRef = 65 := by
    have hh' : Expr.const w.recRef w.ls = .const 65 ls := hh
    injection hh'
  have ha := witness_arity w hr
  have hl := congrArg List.length hx
  simp only [List.length_append, List.length_singleton] at hl
  omega

theorem iota_not_short {lhs rhs : Expr Nat} (h : DerivedIotaU eqEnvT lhs rhs)
    {ls : List Level} {xs : List (Expr Nat)} (hn : xs.length < 6)
    (he : lhs = foldApps (.const 65 ls) xs) : False := by
  cases h with
  | ofU w => exact call_not_short w (ctorMajor w) hn he
  | ofUS w =>
    have hs := congrArg appsSpine he
    change appsSpine (foldApps (.const w.recRef w.ls)
      (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)])) = _ at hs
    rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
    have hh := congrArg Prod.fst hs
    have hx := congrArg Prod.snd hs
    have hr : w.recRef = 65 := by
      have hh' : Expr.const w.recRef w.ls = .const 65 ls := hh
      injection hh'
    have ha := witnessS_arity w hr
    have hl := congrArg List.length hx
    simp only [List.length_append, List.length_singleton] at hl
    omega

end Rcic.Declarative.F8EtaK.A2

namespace Rcic.Declarative.F8EtaK.A2
section VariableClass
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {R : Prop} {i : Nat}

theorem raw_var_or
    (emit : ∀ {P}, HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ (.bvar i) P → R) :
    {a b : Expr Nat} → PEqT E n Γ a b → a = .bvar i → b = .bvar i ∨ R
  | _, _, .bvar _ _, he => .inl he
  | _, _, .proof _ _ _ _ _ hP _ hp _, he => by
      cases he
      exact .inr (emit hP hp)
  | _, _, .sort .., he => nomatch he
  | _, _, .const .., he => nomatch he
  | _, _, .app .., he => nomatch he
  | _, _, .lam .., he => nomatch he
  | _, _, .pi .., he => nomatch he
  | _, _, .letE .., he => nomatch he
  | _, _, .lit .., he => nomatch he

theorem par_var_or
    (hz : ∀ A v, Γ.get? i ≠ some (.letBinding A v))
    (emit : ∀ {P}, HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ (.bvar i) P → R) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T →
    a = .bvar i → b = .bvar i ∨ R
  | _, _, _, .refl _ _ _ _, he => .inl he
  | _, _, _, .bvarZeta _ _ _ _ _ _ h _ _ _, he => by
      cases he
      exact False.elim (hz _ _ h)
  | _, _, _, .iotaSpine _ _ _ _ _ hs hi _ _, he => by
      rcases par_var_or hz emit hs he with hf | hr
      · exact False.elim (iota_not_var hi hf)
      · exact .inr hr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, he =>
      False.elim (foldApps_snoc_ne_bvar (.const w.recRef w.ls) major w.preMajor he)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., he => by
      obtain ⟨_, _, happ0⟩ := iotaStarKEta_appParts happ
      nomatch he.symm.trans happ0
  | _, _, _, .peq _ _ _ _ leaf, he => raw_var_or emit leaf.1 he
  | _, _, _, .conv _ _ _ _ _ h _, he => par_var_or hz emit h he
  | _, _, _, .sortEq .., he => nomatch he
  | _, _, _, .consts .., he => nomatch he
  | _, _, _, .delta .., he => nomatch he
  | _, _, _, .app .., he => nomatch he
  | _, _, _, .beta .., he => nomatch he
  | _, _, _, .lam .., he => nomatch he
  | _, _, _, .pi .., he => nomatch he
  | _, _, _, .letE .., he => nomatch he
  | _, _, _, .zeta .., he => nomatch he
  | _, _, _, .lit .., he => nomatch he
  | _, _, _, .eta .., he => nomatch he
end VariableClass
end Rcic.Declarative.F8EtaK.A2

namespace Rcic.Declarative.F8EtaK.A2

def AllVars (xs : List (Expr Nat)) : Prop := ∀ x ∈ xs, ∃ i, x = .bvar i
def GoodLs (ls : List Level) : Prop := eqNList ls [.succ .zero]
def RecClass (xs : List (Expr Nat)) (e : Expr Nat) : Prop :=
  ∃ ls, e = foldApps (.const 65 ls) xs ∧ GoodLs ls

section RecClass
variable {n : Nat} {Γ : LCtx} {R : Prop}
variable (emitVar : ∀ {i P}, HasTyT eqEnvT n Γ P (.sort .zero) →
  HasTyT eqEnvT n Γ (.bvar i) P → R)
variable (emitRec : ∀ {ls xs P}, GoodLs ls → xs.length < 6 → AllVars xs →
  HasTyT eqEnvT n Γ P (.sort .zero) →
  HasTyT eqEnvT n Γ (foldApps (.const 65 ls) xs) P → R)

include emitVar emitRec in
theorem raw_rec_or : {a b : Expr Nat} → PEqT eqEnvT n Γ a b →
    (ls : List Level) → (xs : List (Expr Nat)) →
    a = foldApps (.const 65 ls) xs → GoodLs ls → xs.length < 6 → AllVars xs →
    RecClass xs b ∨ R
  | _, _, .const _ r ls0 ls1 hc, ls, xs, he, hls, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh : Expr.const r ls0 = .const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      cases hx
      cases hh
      exact .inl ⟨ls1, rfl, eqNList_trans (eqNList_symm hc) hls⟩
  | _, _, .app _ f f' a a' hf ha, ls, xs, he, hls, hn, hv => by
      have hs := congrArg appsSpine he
      change ((appsSpine f).1, (appsSpine f).2 ++ [a]) = _ at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : (appsSpine f).1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : (appsSpine f).2 ++ [a] = xs := congrArg Prod.snd hs
      have hfshape : f = foldApps (.const 65 ls) (appsSpine f).2 := by
        rw [← hh]
        exact (foldApps_appsSpine f).symm
      have hlen : (appsSpine f).2.length < 6 := by
        have hl := congrArg List.length hx
        simp only [List.length_append, List.length_singleton] at hl
        omega
      have hvars : AllVars (appsSpine f).2 :=
        fun x hm => hv x (hx ▸ List.mem_append.mpr (.inl hm))
      rcases raw_rec_or hf ls (appsSpine f).2 hfshape hls hlen hvars with hfc | hr
      · obtain ⟨i, hi⟩ := hv a (hx ▸ List.mem_append.mpr (.inr (.head _)))
        rcases raw_var_or (R := R) emitVar ha hi with hac | hr
        · rcases hfc with ⟨ls', hf', hls'⟩
          refine .inl ⟨ls', ?_, hls'⟩
          rw [hf', hac, ← hi, ← hx, foldApps_snoc]
        · exact .inr hr
      · exact .inr hr
  | _, _, .proof _ _ _ _ _ hP _ hp _, ls, xs, he, hls, hn, hv =>
      .inr (emitRec hls hn hv hP (he ▸ hp))
  | _, _, .bvar .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, .sort .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, .lam .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, .pi .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, .letE .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, .lit .., _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
end RecClass
end Rcic.Declarative.F8EtaK.A2

namespace Rcic.Declarative.F8EtaK.A2
section TypedRecClass
variable {n : Nat} {Γ : LCtx} {R : Prop}
variable (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
variable (emitVar : ∀ {i P}, HasTyT eqEnvT n Γ P (.sort .zero) →
  HasTyT eqEnvT n Γ (.bvar i) P → R)
variable (emitRec : ∀ {ls xs P}, GoodLs ls → xs.length < 6 → AllVars xs →
  HasTyT eqEnvT n Γ P (.sort .zero) →
  HasTyT eqEnvT n Γ (foldApps (.const 65 ls) xs) P → R)

include hz emitVar emitRec in
theorem par_rec_or : {a b T : Expr Nat} →
    (h : ParRedT (PEqLeafT eqEnvT n) eqEnvT n Γ a b T) →
    NoEtaKStep h →
    (ls : List Level) → (xs : List (Expr Nat)) →
    a = foldApps (.const 65 ls) xs → GoodLs ls → xs.length < 6 → AllVars xs →
    RecClass xs b ∨ R
  | _, _, _, .refl _ _ _ _, _, ls, xs, he, hls, _, _ => .inl ⟨ls, he, hls⟩
  | _, _, _, .consts _ r ls0 ls1 _ hc _ _, _, ls, xs, he, hls, hn, hv =>
      raw_rec_or emitVar emitRec (.const _ r ls0 ls1 hc) ls xs he hls hn hv
  | _, _, _, .app _ f f' a a' _ _ _ _ _ hf _ _ _ ha _, hno, ls, xs, he, hls, hn, hv => by
      have hs := congrArg appsSpine he
      change ((appsSpine f).1, (appsSpine f).2 ++ [a]) = _ at hs
      rw [appsSpine_foldApps_const] at hs
      have hh : (appsSpine f).1 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : (appsSpine f).2 ++ [a] = xs := congrArg Prod.snd hs
      have hfshape : f = foldApps (.const 65 ls) (appsSpine f).2 := by
        rw [← hh]
        exact (foldApps_appsSpine f).symm
      have hlen : (appsSpine f).2.length < 6 := by
        have hl := congrArg List.length hx
        simp only [List.length_append, List.length_singleton] at hl
        omega
      have hvars : AllVars (appsSpine f).2 :=
        fun x hm => hv x (hx ▸ List.mem_append.mpr (.inl hm))
      rcases par_rec_or hf hno.1 ls (appsSpine f).2 hfshape hls hlen hvars with hfc | hr
      · obtain ⟨i, hi⟩ := hv a (hx ▸ List.mem_append.mpr (.inr (.head _)))
        rcases par_var_or (R := R) (hz i) emitVar ha hi with hac | hr
        · rcases hfc with ⟨ls', hf', hls'⟩
          refine .inl ⟨ls', ?_, hls'⟩
          rw [hf', hac, ← hi, ← hx, foldApps_snoc]
        · exact .inr hr
      · exact .inr hr
  | _, _, _, .delta _ r ls0 m b _ hres hbody _ _ _ _ _, _, ls, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh : Expr.const r ls0 = .const 65 ls := congrArg Prod.fst hs
      have hr : r = 65 := by injection hh
      subst r
      have hm : m = eqRecT := (Option.some.inj hres).symm
      subst m
      cases hbody
  | _, _, _, .iotaSpine _ _ _ _ _ h hi _ _, hno, ls, xs, he, hls, hn, hv => by
      rcases par_rec_or h hno ls xs he hls hn hv with hfc | hr
      · rcases hfc with ⟨ls', hf', _⟩
        exact False.elim (iota_not_short hi hn hf')
      · exact .inr hr
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, ls, xs, he, _, hn, _ =>
      False.elim (call_not_short w major hn he)
  | _, _, _, .iotaStarKEta .., hno, _, _, _, _, _, _ =>
      nomatch hno
  | _, _, _, .peq _ _ _ _ leaf, _, ls, xs, he, hls, hn, hv =>
      raw_rec_or emitVar emitRec leaf.1 ls xs he hls hn hv
  | _, _, _, .conv _ _ _ _ _ h _, hno, ls, xs, he, hls, hn, hv =>
      par_rec_or h hno ls xs he hls hn hv
  | _, _, _, .sortEq .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .bvarZeta .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .beta .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .lam .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .pi .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .letE .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .zeta .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .lit .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
  | _, _, _, .eta .., _, _, _, he, _, _, _ => by
      have hs := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      cases hh
end TypedRecClass
end Rcic.Declarative.F8EtaK.A2
