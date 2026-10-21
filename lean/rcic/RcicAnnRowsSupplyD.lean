import rcic.RcicTypedRowsWfD
import rcic.RcicAnnAnnotateD
import rcic.RcicAnnIotaSR
import rcic.RcicAnnRowsSupply

/-!
# R-NoDeltaRec-4d-vi — the rows at the D-judgment, and the `TypedRowsWfD` supplier

`RcicAnnTypedRows`'s three rows and `RcicAnnRowsSupply`'s chain adapter + supplier, stated
at the D-judgment (`ConvTD`/`TyConvTD`/`CtxWfTD`/`HasTyTD`/`ConvArgsTD` over `EA`, with ι
`DerivedIotaN`). Every proof is the legacy one with `annConvTD`/`annCtxWfTD`/`annHasTyTD`
for the annotation and `tyConvTD_of_tyConvA`/`convArgsTD_of_convArgsA`/`hasTyTD_of_hasTyA`/
`convTD_of_convA` for the transports — each taking `IotaErasesAN`, proved from `EnvWfA`
alone by `iotaErasesAN_of_envWfA`. **`EnvNormEraseA` does not occur**: the only ι read the
adapter and the rows make is annotation's, and `annConvTD`'s ι arm consumes
`iotaFnA_of_derivedIotaN`, which needs `EnvWfA` only.

`famAppConvInjTD_any` is the `piConvInjT'`-analogue family row; `piConvInjTD`/`piConvInjTD'`
is the row itself. `sortConvCharTD`/`piConvInjTD`/`famAppConvInjTD_any` carry `IotaSRA` as
the single named hypothesis, `annConvT`'s own; the `'` variants discharge it by `iotaSRA`.

(1) the erasure transports at `IotaErasesAN`;
(2) the chain adapter at `TyConvTD`;
(3) the three rows + `'` variants;
(4) `typedRowsWfD_of_annEnvA`, the supplier.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

variable {E : ResolvedEnvA} {n : Nat}

/-! ## (1) the erasure transports -/

/-- the D-erasure's ι premise from the admission alone — `C.hNS hn`'s D-twin, no
    `EnvNormEraseA`: `IotaErasesAN` is `iotaCorrN_of_envWfA`'s erasure half. -/
theorem iotaErasesAN_of_annEnvA (C : AnnEnvA E) : IotaErasesAN E :=
  C.wf.elim fun hW => iotaErasesAN_of_envWfA hW C.noFun

/-- a copy typing erases to a `HasTyTD` under `AnnEnvA` alone. -/
theorem hasTyTD_of_hasTyA_of_annEnvA (C : AnnEnvA E) {Γ : LCtxA} {e T : ExprA}
    (h : HasTyA E (iotaIfaceA E) n Γ e T) :
    Nonempty (HasTyTD E n (eraseCtx Γ) (erase e) (erase T)) :=
  hasTyTD_of_hasTyA (iotaErasesAN_of_annEnvA C) h

/-- a copy conversion erases to a `ConvTD` under `AnnEnvA` alone. -/
theorem convTD_of_convA_of_annEnvA (C : AnnEnvA E) {Γ : LCtxA} {a b T : ExprA}
    (h : ConvA E (iotaIfaceA E) n Γ a b T) :
    Nonempty (ConvTD E n (eraseCtx Γ) (erase a) (erase b) (erase T)) :=
  convTD_of_convA (iotaErasesAN_of_annEnvA C) h

/-- a copy type-conversion erases to a `TyConvTD` under `AnnEnvA` alone. -/
theorem tyConvTD_of_tyConvA_of_annEnvA (C : AnnEnvA E) {Γ : LCtxA} {A B : ExprA}
    (h : TyConvA E (iotaIfaceA E) n Γ A B) :
    Nonempty (TyConvTD E n (eraseCtx Γ) (erase A) (erase B)) :=
  tyConvTD_of_tyConvA (iotaErasesAN_of_annEnvA C) h

/-- pointwise copy conversions erase to `ConvArgsTD` under `AnnEnvA` alone. -/
theorem convArgsTD_of_convArgsA_of_annEnvA (C : AnnEnvA E) {Γ : LCtxA} {T : ExprA}
    {xs xs' : List ExprA} (h : ConvArgsA E (iotaIfaceA E) n Γ T xs xs') :
    ConvArgsTD E n (eraseCtx Γ) (erase T) (xs.map erase) (xs'.map erase) :=
  convArgsTD_of_convArgsA (iotaErasesAN_of_annEnvA C) h

/-! ## (2) the chain adapter at `TyConvTD` -/

/-- The typing the adapter needs: a `ConvTD` at a sort gives its left end's typing at that
    sort — `hasTyT_sort_of_convT`'s twin, no `EnvNormEraseA`. -/
theorem hasTyTD_sort_of_convTD (C : AnnEnvA E) {Γ : LCtx} (hΓ : CtxWfTD E n Γ)
    {a b : Expr Nat} {u : Level} (h : ConvTD E n Γ a b (.sort u)) :
    Nonempty (HasTyTD E n Γ a (.sort u)) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD' C hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvTD' C h hΓA hctx
  have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨t'⟩ := hasTyTD_of_hasTyA_of_annEnvA C tA
  rw [ha, hT, hctx] at t'
  exact ⟨t'⟩

/-- The typing the adapter needs for `trans`: the right end at the same sort. -/
theorem hasTyTD_sortRight_of_convTD (C : AnnEnvA E) {Γ : LCtx} (hΓ : CtxWfTD E n Γ)
    {a b : Expr Nat} {u : Level} (h : ConvTD E n Γ a b (.sort u)) :
    Nonempty (HasTyTD E n Γ b (.sort u)) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD' C hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvTD' C h hΓA hctx
  have tB := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨t'⟩ := hasTyTD_of_hasTyA_of_annEnvA C tB
  rw [hb, hT, hctx] at t'
  exact ⟨t'⟩

/-- THE CHAIN ADAPTER at the D-judgment: with the left end typed at a sort, a `TyConvTD`
    chain to any right end is one `ConvTD` at that sort — `convT_of_tyConvT_sort`'s twin,
    no `EnvNormEraseA`. -/
theorem convTD_of_tyConvTD_sort (C : AnnEnvA E) {Γ : LCtx} (hΓ : CtxWfTD E n Γ)
    {a b : Expr Nat} {u : Level} (hA : HasTyTD E n Γ a (.sort u))
    (h : TyConvTD E n Γ a b) :
    Nonempty (ConvTD E n Γ a b (.sort u)) := by
  induction h with
  | refl => exact ⟨ConvTD.refl _ _ _ hA⟩
  | of _ _ u h =>
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD' C hΓ
      obtain ⟨aA, bA, TA, ha, hb, hTv, ⟨c⟩⟩ := annConvTD' C h hΓA hctx
      obtain ⟨aA2, TA2, ha2, hTu, ⟨t2⟩⟩ := annHasTyTD' C hA hΓA hctx
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
      obtain ⟨t⟩ := annTyA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
        (ha.trans ha2.symm) tA t2
      obtain ⟨hc⟩ := convTD_of_convA_of_annEnvA C (convA_of_tyConvA c t)
      rw [ha, hb, hTu, hctx] at hc
      exact ⟨hc⟩
  | trans _ _ _ h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1 hA
      obtain ⟨hmid⟩ := hasTyTD_sortRight_of_convTD C hΓ c1
      obtain ⟨c2⟩ := ih2 hmid
      exact ⟨ConvTD.trans _ _ _ _ _ c1 c2⟩

/-! ## (3) the rows at the D-judgment -/

/-- ROW 1 at the D-judgment: convertible sorts are `=ₙ`. `sortConvCharT`'s twin — the named
    hypothesis is `IotaSRA`, `annConvT`'s own; no `EnvNormEraseA`. -/
theorem sortConvCharTD (C : AnnEnvA E) (hSR : IotaSRA E n) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {l₁ l₂ : Level} {T : Expr Nat}
    (h : ConvTD E n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
  obtain ⟨aA, bA, TA, ha, hb, _, ⟨c⟩⟩ := annConvTD C hSR h hΓA hctx
  obtain rfl := erase_eq_sort ha
  obtain rfl := erase_eq_sort hb
  obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
    (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c) (.sort ΓA l₁)
  obtain ⟨hW⟩ := C.wf
  exact sortConvCharA_rec hW posValA_one C.small C.propElim hΓA (convA_of_tyConvA c t)

/-- ROW 2 at the D-judgment: convertible pis have type-convertible domains and, under the
    left domain, type-convertible codomains — `piConvInjT`'s twin, `piConvInjT'`'s analogue
    WITHOUT the `EnvNormEraseA` premise. -/
theorem piConvInjTD (C : AnnEnvA E) (hSR : IotaSRA E n) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {A B A' B' T : Expr Nat}
    (h : ConvTD E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvTD E n Γ A A') ∧
      Nonempty (TyConvTD E n (.assumption A :: Γ) B B') := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
  obtain ⟨aA, bA, TA, ha, hb, _, ⟨c⟩⟩ := annConvTD C hSR h hΓA hctx
  obtain ⟨AA, u, BA, v, rfl, hAe, hBe⟩ := erase_eq_pi ha
  obtain ⟨AA', u', BA', v', rfl, hA'e, hB'e⟩ := erase_eq_pi hb
  have t1 := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts t1
  obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA t1
    (.pi ΓA AA u BA v hAu hBv)
  obtain ⟨hW⟩ := C.wf
  obtain ⟨_, _, ⟨tA⟩, ⟨tB⟩⟩ :=
    piConvInjA_rec hW posValA_one C.small C.propElim hΓA (convA_of_tyConvA c t)
  have hNS := iotaErasesAN_of_annEnvA C
  obtain ⟨tA'⟩ := tyConvTD_of_tyConvA hNS tA
  obtain ⟨tB'⟩ := tyConvTD_of_tyConvA hNS tB
  subst hAe hA'e hBe hB'e hctx
  exact ⟨⟨tA'⟩, ⟨tB'⟩⟩

/-- ROW 3 at the D-judgment, at a Type-level family — `famAppConvInjT`'s twin. -/
theorem famAppConvInjTD (C : AnnEnvA E) (hSR : IotaSRA E n) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (hz : isZero (instLevel ls u₀) = false)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvTD C hSR h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_rec hW posValA_one C.small C.propElim hΓA hm hind hsh hz c
  have hT' := convArgsTD_of_convArgsA_of_annEnvA C hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

/-- ROW 3 at the D-judgment, at a `Prop`-level conversion — `famAppConvInjT_prop`'s twin. -/
theorem famAppConvInjTD_prop (C : AnnEnvA E) (hSR : IotaSRA E n) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hw : isZero w = true)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvTD C hSR h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_prop_rec hW posValA_one C.small C.propElim hΓA hm hind hw c
  have hT' := convArgsTD_of_convArgsA_of_annEnvA C hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

/-- ROW 3 at the D-judgment, at either level: neither `hz` nor `hw` is assumed —
    `famAppConvInjT_any`'s twin, no `EnvNormEraseA`. -/
theorem famAppConvInjTD_any (C : AnnEnvA E) (hSR : IotaSRA E n) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvTD C hSR h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_any_rec hW posValA_one C.small C.propElim hΓA hm hind hsh c
  have hT' := convArgsTD_of_convArgsA_of_annEnvA C hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

/-- ROW 1 at the D-judgment, `IotaSRA` discharged — `sortConvCharT'`'s twin. -/
theorem sortConvCharTD' (C : AnnEnvA E) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {l₁ l₂ : Level} {T : Expr Nat}
    (h : ConvTD E n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ :=
  sortConvCharTD C (iotaSRA C) hΓ h

/-- ROW 2 at the D-judgment, `IotaSRA` discharged — `piConvInjT'`'s analogue WITHOUT
    `EnvNormEraseA` (the brief's item 3). -/
theorem piConvInjTD' (C : AnnEnvA E) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {A B A' B' T : Expr Nat}
    (h : ConvTD E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvTD E n Γ A A') ∧
      Nonempty (TyConvTD E n (.assumption A :: Γ) B B') :=
  piConvInjTD C (iotaSRA C) hΓ h

/-- ROW 3 at the D-judgment at a Type-level family, `IotaSRA` discharged —
    `famAppConvInjT'`'s twin. -/
theorem famAppConvInjTD' (C : AnnEnvA E) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (hz : isZero (instLevel ls u₀) = false)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjTD C (iotaSRA C) hΓ hm hind hsh hz h

/-- ROW 3 at the D-judgment at a `Prop`-level conversion, `IotaSRA` discharged —
    `famAppConvInjT_prop'`'s twin. -/
theorem famAppConvInjTD_prop' (C : AnnEnvA E) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hw : isZero w = true)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjTD_prop C (iotaSRA C) hΓ hm hind hw h

/-- ROW 3 at the D-judgment at either level, `IotaSRA` discharged —
    `famAppConvInjT_any'`'s twin, no `EnvNormEraseA`. -/
theorem famAppConvInjTD_any' (C : AnnEnvA E) {Γ : LCtx}
    (hΓ : CtxWfTD E n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvTD E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsTD E n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjTD_any C (iotaSRA C) hΓ hm hind hsh h

/-! ## (4) the supplier -/

/-- THE SUPPLIER at the D-judgment: every environment the copy admits bears the three chain
    rows on `TyConvTD`. `typedRowsWf_of_annEnvA`'s twin — `AnnEnvA` alone, no
    `EnvNormEraseA`: the only premise the legacy supplier consumed it for was the
    ι-correspondence `C.hNS`, and the D-judgment's ι correspondence is unconditional. -/
theorem typedRowsWfD_of_annEnvA (C : AnnEnvA E) (n : Nat) : TypedRowsWfD E n where
  sortRow := fun {_} hΓ {_ _} h => by
    obtain ⟨c⟩ := convTD_of_tyConvTD_sort C hΓ (HasTyTD.sort _ _) h
    exact sortConvCharTD' C hΓ c
  piRow := fun {_} hΓ {_ _ _ _} h => by
    rcases TyConvTD.firstOf h with he | ⟨X, u, ⟨hstep⟩, _⟩
    · rcases Expr.pi.inj he with ⟨rfl, rfl⟩
      exact ⟨⟨TyConvTD.refl _ _⟩, ⟨TyConvTD.refl _ _⟩⟩
    · obtain ⟨hty⟩ := hasTyTD_sort_of_convTD C hΓ hstep
      obtain ⟨c⟩ := convTD_of_tyConvTD_sort C hΓ hty h
      exact piConvInjTD' C hΓ c
  famAppRow := fun {_} hΓ {r m ls ls' xs xs' w} hm hind hty h => by
      obtain ⟨hW⟩ := C.wf
      obtain ⟨u₀, hsh⟩ := envWfA_famArity hW r m hm hind
      obtain ⟨c⟩ := convTD_of_tyConvTD_sort C hΓ hty h
      exact famAppConvInjTD_any' C hΓ hm hind hsh c

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.iotaErasesAN_of_annEnvA
#print axioms Rcic.Declarative.Ann.hasTyTD_sort_of_convTD
#print axioms Rcic.Declarative.Ann.convTD_of_tyConvTD_sort
#print axioms Rcic.Declarative.Ann.sortConvCharTD
#print axioms Rcic.Declarative.Ann.piConvInjTD
#print axioms Rcic.Declarative.Ann.famAppConvInjTD
#print axioms Rcic.Declarative.Ann.famAppConvInjTD_prop
#print axioms Rcic.Declarative.Ann.famAppConvInjTD_any
#print axioms Rcic.Declarative.Ann.sortConvCharTD'
#print axioms Rcic.Declarative.Ann.piConvInjTD'
#print axioms Rcic.Declarative.Ann.famAppConvInjTD_any'
#print axioms Rcic.Declarative.Ann.typedRowsWfD_of_annEnvA
