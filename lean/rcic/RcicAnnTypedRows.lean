import rcic.RcicAnnAnnotate
import rcic.RcicAnnFamAppAny

/-!
# M3-d — the three rows on the typed judgment

`main`'s rows (`RcicInvertFamily`: `SortConvChar`, `PiConvInj`, `FamAppConvInj`, bundled in
`RcicRowsT.RowsT`) are stated on the untyped `Conv`, which is total (R-ConvCollapse), so two of them
are refuted there and the third is degenerate. This module states them on R-CIC's typed judgment
(`RcicTypedJ`: `HasTyT` / `ConvT`), the judgment the landing makes `main`'s root, and proves them
over every environment the copy admits under the profile (`AnnEnvA`).

Each row has the same proof. Annotate the conversion and its context (`annConvT`, `annCtxWfT`).
Retype the annotated conversion at the subject's own sort by type uniqueness (`hasTyA_uniq`). Apply
the copy's row at the concrete ι (`*_rec`), then erase its conclusion back (`tyConvT_of_tyConvA`,
`convArgsT_of_convArgsA`).

The rows are stated in existence form (M3-b-0 O5). Here they carry one hypothesis beyond the copy's
own rows: ι subject reduction (`IotaSRA`), the annotation's one premise (`RcicAnnAnnotate`).
`RcicAnnIotaSR` proves it and restates the rows without it (`sortConvCharT'`, `piConvInjT'`,
`famAppConvInjT'`, `famAppConvInjT_prop'`, `famAppConvInjT_any'`). Row 3 at either level
(`famAppConvInjT_any`) assumes neither `hz` nor `hw`, by `RcicAnnFamAppAny`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Rows
variable {E : ResolvedEnvA} {n : Nat}

/-! ## (1) erasure inverted at a family application; pointwise conversions erased -/

theorem erase_eq_foldApps_const {e : ExprA} {r : Nat} {ls : List Level} {xs : List (Expr Nat)}
    (h : erase e = foldApps (.const r ls) xs) :
    ∃ xsA, e = foldAppsA (.const r ls) xsA ∧ xsA.map erase = xs := by
  have hs : appsSpine (erase e) = (.const r ls, xs) := by rw [h, appsSpine_foldApps]; rfl
  obtain ⟨xsA, hsp, hmap⟩ := appsSpineA_of_erase_const hs
  refine ⟨xsA, ?_, hmap⟩
  have := foldAppsA_appsSpineA e
  rw [hsp] at this
  exact this.symm

/-- pointwise conversions along a telescope erase to the typed judgment's. -/
theorem convArgsT_of_convArgsA {J : IotaIfaceA} (hW : EnvWfA J E) (hNS : IotaErasesA E) {Γ : LCtxA} :
    {T : ExprA} → {xs xs' : List ExprA} → ConvArgsA E (iotaIfaceA E) n Γ T xs xs' →
      ConvArgsT (eraseEnv E) n (eraseCtx Γ) (erase T) (xs.map erase) (xs'.map erase)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A _ B _ f f' _ _ ⟨h⟩ hs => by
      have ih := convArgsT_of_convArgsA hW hNS hs
      rw [erase_instantiate0A] at ih
      exact .cons (erase A) (erase B) (erase f) (erase f') _ _ (convT_of_convA hW hNS h) ih

/-! ## (2) the rows -/

/-- ROW 1 ON THE TYPED JUDGMENT: convertible sorts are `=ₙ`. -/
theorem sortConvCharT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {l₁ l₂ : Level} {T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, _, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain rfl := erase_eq_sort ha
  obtain rfl := erase_eq_sort hb
  obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
    (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c) (.sort ΓA l₁)
  obtain ⟨hW⟩ := C.wf
  exact sortConvCharA_rec hW posValA_one C.small C.propElim hΓA (convA_of_tyConvA c t)

/-- ROW 2 ON THE TYPED JUDGMENT: convertible pis have type-convertible domains and, under the left
    domain, type-convertible codomains. -/
theorem piConvInjT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {A B A' B' T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT (eraseEnv E) n Γ A A') ∧
      Nonempty (TyConvT (eraseEnv E) n (.assumption A :: Γ) B B') := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, _, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain ⟨AA, u, BA, v, rfl, hAe, hBe⟩ := erase_eq_pi ha
  obtain ⟨AA', u', BA', v', rfl, hA'e, hB'e⟩ := erase_eq_pi hb
  have t1 := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts t1
  obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA t1
    (.pi ΓA AA u BA v hAu hBv)
  obtain ⟨hW⟩ := C.wf
  obtain ⟨_, _, ⟨tA⟩, ⟨tB⟩⟩ :=
    piConvInjA_rec hW posValA_one C.small C.propElim hΓA (convA_of_tyConvA c t)
  obtain ⟨tA'⟩ := tyConvT_of_tyConvA hW (C.hNS hn) tA
  obtain ⟨tB'⟩ := tyConvT_of_tyConvA hW (C.hNS hn) tB
  subst hAe hA'e hBe hB'e hctx
  exact ⟨⟨tA'⟩, ⟨tB'⟩⟩

/-- ROW 3 ON THE TYPED JUDGMENT, at a Type-level family: convertible applications of one family have
    `=ₙ` levels and pointwise convertible arguments along the family's telescope. -/
theorem famAppConvInjT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (hz : isZero (instLevel ls u₀) = false)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_rec hW posValA_one C.small C.propElim hΓA hm hind hsh hz c
  have hT' := convArgsT_of_convArgsA hW (C.hNS hn) hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

/-- ROW 3 ON THE TYPED JUDGMENT, at a `Prop`-level conversion. -/
theorem famAppConvInjT_prop (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hw : isZero w = true)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_prop_rec hW posValA_one C.small C.propElim hΓA hm hind hw c
  have hT' := convArgsT_of_convArgsA hW (C.hNS hn) hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

/-- ROW 3 ON THE TYPED JUDGMENT, at either level: neither the family's sort (`hz`) nor the conversion's
    (`hw`) is assumed (`famAppConvInjA_any_rec`, M2-g′ (e)). -/
theorem famAppConvInjT_any (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat} {m : CheckedMemberA} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {u₀ w : Level} (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain rfl := erase_eq_sort hT
  obtain ⟨xsA, rfl, rfl⟩ := erase_eq_foldApps_const ha
  obtain ⟨xsA', rfl, rfl⟩ := erase_eq_foldApps_const hb
  obtain ⟨hW⟩ := C.wf
  obtain ⟨hl, hlen, hargs⟩ :=
    famAppConvInjA_any_rec hW posValA_one C.small C.propElim hΓA hm hind hsh c
  have hT' := convArgsT_of_convArgsA hW (C.hNS hn) hargs
  rw [erase_instantiateLevelsA, hctx] at hT'
  exact ⟨hl, by rw [List.length_map, List.length_map, hlen], hT'⟩

end Rows

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.convArgsT_of_convArgsA
#print axioms Rcic.Declarative.Ann.sortConvCharT
#print axioms Rcic.Declarative.Ann.piConvInjT
#print axioms Rcic.Declarative.Ann.famAppConvInjT
#print axioms Rcic.Declarative.Ann.famAppConvInjT_prop
#print axioms Rcic.Declarative.Ann.famAppConvInjT_any
