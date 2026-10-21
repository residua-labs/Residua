import rcic.RcicTypedGroupPins
import rcic.RcicDTMetaTypedScope
import rcic.RcicIota
import rcic.RcicInvert

/-!
# DT typed counterparts, segment 4 — DT-015 / DT-020

O2S-pattern typed counterparts (erratum E-O2SCounterparts) for the last two
02 §14 rows of this lane, over the typed root (`HasTyT`/`ConvT`/`Step`,
shared by both judgments), BESIDE the legacy theorems — no legacy
statement touched — with consumption pins at `natEnvU` / `listEnvUT`.

- DT-015 — theorem/opaque rigidity. The legacy theorem concluded
  `Nonempty (DerivedIota …)` — vacuous content, because a const-headed
  step can only be δ (which requires `transparent = true`, refused by
  rigidity) or ι (a `DerivedIota` at a bare const, impossible outright,
  `derivedIota_const_false`). Stated here at the strength the row names:
  a rigid member's constant takes NO step; the legacy-shape corollary is
  the one-liner `DT015T_rigidity_derivedIota`.
- DT-020 — R-CIC-0λ embeds into R-CIC-0ι, cc's option (b): the profile
  `NoIotaTy`/`NoIotaConvT` walks a derivation and refutes exactly the
  `ConvT.iota` arm — the whole 0λ/0ι difference — definitionally. The
  counterpart `DT020T_lambda_embeds_into_iota` is the half with content:
  on an environment where `DerivedIota` is uninhabited, EVERY typed
  derivation is iota-free, proved by mutual induction
  (`noIotaTy_of_noDerivedIota` / `noIotaConvT_of_noDerivedIota`) — the
  iota arm alone is discharged by the premise. Consumed at `emptyEnv`
  (a real ι-free env) and pinned by the refusal teeth
  `noIotaConvT_iota_refused` / `noIotaTy_conv_iota_refused`.

`dtTypedCensus` lives in `RcicDTMetaTypedLiftSubst` (seg 1); this file adds
the final two counterparts it names.
-/

namespace Rcic.Declarative

/-- DT-015 typed, the row's actual strength: a rigid member's constant
    takes NO one-step reduction. `stepConstInv` splits a const-head step
    into δ (transparent — contradicted by rigidity) and ι (a `DerivedIota`
    at a bare const — impossible). `Step` is the reduction interface the
    typed root's subject reduction reads. -/
theorem DT015T_rigidity {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hrigid : transparent m.mclass = false)
    {e' : Expr Nat} (hstep : Step E n Γ (.const r ls) e') : False := by
  cases stepConstInv hstep rfl with
  | inl delta =>
      let ⟨m', _b0, hres', _hbody', htr', _hbeq⟩ := delta
      rw [hres] at hres'; cases hres'
      rw [hrigid] at htr'; exact absurd htr' (by simp)
  | inr hι => exact derivedIota_const_false hι

/-- the legacy-shape corollary: under rigidity any step would land on a
    derived iota — unreachable, since there are no steps. -/
theorem DT015T_rigidity_derivedIota {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hrigid : transparent m.mclass = false)
    {e' : Expr Nat} (hstep : Step E n Γ (.const r ls) e') :
    Nonempty (DerivedIota E (.const r ls) e') :=
  (DT015T_rigidity hres hrigid hstep).elim

/-! ## the iota-free profile (DT-020's non-vacuous `UsesNoIotaT`) -/

mutual

/-- the iota-free profile, typing side: a `HasTyT` derivation carries no
    `ConvT.iota` node anywhere — through `conv` wrappers and every field
    derivation. -/
def NoIotaTy {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, .sort _ _ => True
  | _, _, _, .bvar _ _ _ _ => True
  | _, _, _, .const _ _ _ _ _ _ _ => True
  | _, _, _, .pi _ _ _ _ _ hA hB => NoIotaTy hA ∧ NoIotaTy hB
  | _, _, _, .lam _ _ _ _ _ hA hbody => NoIotaTy hA ∧ NoIotaTy hbody
  | _, _, _, .app _ _ _ _ _ hf ha => NoIotaTy hf ∧ NoIotaTy ha
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      NoIotaTy hA ∧ NoIotaTy hv ∧ NoIotaTy hb
  | _, _, _, .lit _ _ _ hexp => NoIotaTy hexp
  | _, _, _, .conv _ _ _ _ _ h hc => NoIotaTy h ∧ NoIotaConvT hc

/-- the conversion side: every arm recurses over its field derivations
    except `.iota`, which is refuted — that arm is the whole 0λ/0ι
    difference. -/
def NoIotaConvT {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Prop
  | _, _, _, _, .refl _ _ _ h => NoIotaTy h
  | _, _, _, _, .symm _ _ _ _ h => NoIotaConvT h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => NoIotaConvT h1 ∧ NoIotaConvT h2
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg =>
      NoIotaTy hA ∧ NoIotaTy hbody ∧ NoIotaTy harg
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb =>
      NoIotaTy hA ∧ NoIotaTy hv ∧ NoIotaTy hb
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => NoIotaTy hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => NoIotaTy hb
  | _, _, _, _, .iota _ _ _ _ _ _ _ => False
  | _, _, _, _, .lit _ _ _ _ _ hexp => NoIotaTy hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => NoIotaConvT h1 ∧ NoIotaConvT h2
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => NoIotaConvT hA ∧ NoIotaConvT hb
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => NoIotaConvT hA ∧ NoIotaConvT hB
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      NoIotaConvT hA ∧ NoIotaConvT hv ∧ NoIotaConvT hb
  | _, _, _, _, .sorts _ _ _ _ => True
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => True
  | _, _, _, _, .eta _ _ _ _ h => NoIotaTy h
  | _, _, _, _, .irr _ _ _ _ hP hp hq =>
      NoIotaTy hP ∧ NoIotaTy hp ∧ NoIotaTy hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => NoIotaConvT h ∧ NoIotaConvT hA

end

mutual

/-- the option-(b) half of DT-020, typing side: on an environment where
    `DerivedIota` is uninhabited, EVERY typed derivation is iota-free —
    the `conv` arm hands its conversion field to the `ConvT` twin. By
    mutual induction over the derivation. -/
theorem noIotaTy_of_noDerivedIota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) :
    {n : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    (h : HasTyT E n Γ e A) → NoIotaTy h
  | _, _, _, _, .sort _ _ => trivial
  | _, _, _, _, .bvar _ _ _ _ => trivial
  | _, _, _, _, .const _ _ _ _ _ _ _ => trivial
  | _, _, _, _, .pi _ _ _ _ _ hA hB =>
      ⟨noIotaTy_of_noDerivedIota hno hA, noIotaTy_of_noDerivedIota hno hB⟩
  | _, _, _, _, .lam _ _ _ _ _ hA hbody =>
      ⟨noIotaTy_of_noDerivedIota hno hA, noIotaTy_of_noDerivedIota hno hbody⟩
  | _, _, _, _, .app _ _ _ _ _ hf ha =>
      ⟨noIotaTy_of_noDerivedIota hno hf, noIotaTy_of_noDerivedIota hno ha⟩
  | _, _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      ⟨noIotaTy_of_noDerivedIota hno hA, noIotaTy_of_noDerivedIota hno hv,
       noIotaTy_of_noDerivedIota hno hb⟩
  | _, _, _, _, .lit _ _ _ hexp => noIotaTy_of_noDerivedIota hno hexp
  | _, _, _, _, .conv _ _ _ _ _ h hc =>
      ⟨noIotaTy_of_noDerivedIota hno h, noIotaConvT_of_noDerivedIota hno hc⟩

/-- the conversion twin: every arm recurses over its field derivations;
    `ConvT.iota` alone is discharged by the no-`DerivedIota` premise. -/
theorem noIotaConvT_of_noDerivedIota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) :
    {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    (h : ConvT E n Γ a b T) → NoIotaConvT h
  | _, _, _, _, _, .refl _ _ _ h => noIotaTy_of_noDerivedIota hno h
  | _, _, _, _, _, .symm _ _ _ _ h => noIotaConvT_of_noDerivedIota hno h
  | _, _, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      ⟨noIotaConvT_of_noDerivedIota hno h1,
       noIotaConvT_of_noDerivedIota hno h2⟩
  | _, _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg =>
      ⟨noIotaTy_of_noDerivedIota hno hA, noIotaTy_of_noDerivedIota hno hbody,
       noIotaTy_of_noDerivedIota hno harg⟩
  | _, _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb =>
      ⟨noIotaTy_of_noDerivedIota hno hA, noIotaTy_of_noDerivedIota hno hv,
       noIotaTy_of_noDerivedIota hno hb⟩
  | _, _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => noIotaTy_of_noDerivedIota hno hv
  | _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => noIotaTy_of_noDerivedIota hno hb
  | _, _, _, _, _, .iota _ _ _ _ hd _ _ => (hno _ _ hd).elim
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => noIotaTy_of_noDerivedIota hno hexp
  | _, _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 =>
      ⟨noIotaConvT_of_noDerivedIota hno h1,
       noIotaConvT_of_noDerivedIota hno h2⟩
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ hA hb =>
      ⟨noIotaConvT_of_noDerivedIota hno hA, noIotaConvT_of_noDerivedIota hno hb⟩
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB =>
      ⟨noIotaConvT_of_noDerivedIota hno hA, noIotaConvT_of_noDerivedIota hno hB⟩
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      ⟨noIotaConvT_of_noDerivedIota hno hA, noIotaConvT_of_noDerivedIota hno hv,
       noIotaConvT_of_noDerivedIota hno hb⟩
  | _, _, _, _, _, .sorts _ _ _ _ => trivial
  | _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => trivial
  | _, _, _, _, _, .eta _ _ _ _ h => noIotaTy_of_noDerivedIota hno h
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq =>
      ⟨noIotaTy_of_noDerivedIota hno hP, noIotaTy_of_noDerivedIota hno hp,
       noIotaTy_of_noDerivedIota hno hq⟩
  | _, _, _, _, _, .tyConv _ _ _ _ _ _ h hA =>
      ⟨noIotaConvT_of_noDerivedIota hno h, noIotaConvT_of_noDerivedIota hno hA⟩

end

/-- DT-020 typed, the non-vacuous half (cc's option b): on an environment
    where `DerivedIota` is uninhabited — the R-CIC-0λ environments — every
    typed derivation already satisfies the iota-free profile, so its image
    under the identity embedding is a 0ι derivation with the profile
    attached. The premise is a satisfiable hypothesis (`emptyEnv` proves
    it, `pin_DT020T_noIotaEnv`), not a hollow restatement: the profile
    conclusion is computed by the mutual induction above, not assumed.

    OPEN DEBT (census B, DT-020): `(hno : ∀ lhs rhs, DerivedIota E lhs rhs
    → False)` stays a presented `∀`-premise — it is a REAL debt, not the
    row's own input. `E.members : Nat → Option CheckedMember` has an
    undecidable domain, so iota-freeness cannot be kernel-checked on an
    arbitrary `E`; and the premise is necessary — `pin_DT020T_hno_necessary`
    inhabits `DerivedIota natEnvU` outright (`wSuccU`). The discharged
    forms live as separate sealed decls: `noDerivedIota_of_noRecursor` /
    `DT020T_lambda_embeds_into_iota_of_noRecursor` (member-shape route,
    consumed at `pinFamEnv` by `pin_DT020T_noIotaFamEnv`) and
    `DT020T_noRecursorTable` / `noDerivedIota_foldEnv_of_noRecursors`
    (the checked finite-table route — the row's premises:none content on
    decidable inputs). Restating THIS anchor on `foldEnv tbl` is not
    available in-module: `RcicForall8NoRecursor` imports this file, so the
    table machinery cannot be pulled up without an import cycle. -/
theorem DT020T_lambda_embeds_into_iota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTyT E n Γ e A) : NoIotaTy h :=
  noIotaTy_of_noDerivedIota hno h

/-- the profile's tooth: nothing rooted at `ConvT.iota` is iota-free —
    the predicate refutes exactly the rule 0λ lacks, definitionally. -/
theorem noIotaConvT_iota_refused {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} (hd : DerivedIota E lhs rhs)
    (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T) :
    ¬ NoIotaConvT (ConvT.iota _ _ _ _ hd hl hr) := fun h => h

/-- the same refusal one level up: a `conv` wrapper around an iota
    conversion is not iota-free either — the profile walks through. -/
theorem noIotaTy_conv_iota_refused {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level} (h : HasTyT E n Γ e A)
    (hd : DerivedIota E A B) (hlhs : HasTyT E n Γ A (.sort u))
    (hrhs : HasTyT E n Γ B (.sort u)) :
    ¬ NoIotaTy (HasTyT.conv _ _ _ _ _ h
      (ConvT.iota _ _ _ _ hd hlhs hrhs)) :=
  fun ⟨_, hF⟩ => hF

/-! ## consumption pins at real fixtures -/

/-- PIN (DT-015T): at `natEnvU` the recursor (`natRecMemberU`, ref 3 —
    `.recursorM`, rigid) takes no step from the const head. -/
theorem pin_DT015T_natU {n : Nat} {Γ : LCtx} {e' : Expr Nat}
    (hstep : Step natEnvU n Γ (.const 3 [.imax (.param 0) .zero]) e') :
    False := DT015T_rigidity (r := 3) (m := natRecMemberU) rfl rfl hstep

/-- PIN (DT-020T, positive): the zeta conversion on `listEnvUT` is
    iota-free — its profile holds, and the embedding consumes the let's
    typing through it. -/
theorem pin_DT020T_zeta_iotaFree {n : Nat} :
    NoIotaConvT (pinZetaConvT listEnvUT n) := by
  simp [NoIotaConvT, NoIotaTy, pinZetaConvT]

/-- `emptyEnv` inhabits no `DerivedIota`: the sole constructor's witness
    carries a recursor membership, and `emptyEnv.members` is `none`
    everywhere — the lookup contradicts it outright. -/
theorem noDerivedIota_emptyEnv (lhs rhs : Expr Nat) :
    DerivedIota emptyEnv lhs rhs → False := fun ⟨w⟩ => Option.noConfusion w.hrec

/-- PIN (DT-020T, option-b consumed): on `emptyEnv` — a real ι-free
    environment — the counterpart hands `Sort 0`'s typing its computed
    iota-free profile. -/
theorem pin_DT020T_noIotaEnv {n : Nat} :
    NoIotaTy (pinSortT emptyEnv n) :=
  DT020T_lambda_embeds_into_iota noDerivedIota_emptyEnv (pinSortT emptyEnv n)

/-- PIN (DT-020T, tooth at the fixture): on `natEnvU` — whose recursor
    genuinely inhabits `DerivedIota` — an iota conversion is refused the
    profile. -/
theorem pin_DT020T_iota_refused {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} (hd : DerivedIota natEnvU lhs rhs)
    (hl : HasTyT natEnvU n Γ lhs T) (hr : HasTyT natEnvU n Γ rhs T) :
    ¬ NoIotaConvT (ConvT.iota _ _ _ _ hd hl hr) :=
  noIotaConvT_iota_refused hd hl hr

/-! ## DT-020 census B — `hno` discharged from the member shape, shown necessary

The row's open leg is `hno : ∀ lhs rhs, DerivedIota E lhs rhs → False`,
the presented `∀`-premise of `DT020T_lambda_embeds_into_iota`. It is
environment-dependent — the two legs:

- DISCHARGE: a recursor-free member table admits no ι witness — every
  `IotaWitness` requires `members recRef = some recMember` with
  `hrecK : recMember.mclass = .recursorM`. `emptyEnv` was the vacuous
  instance; `pinFamEnv` (one `.inductiveM` member) is a non-vacuous one.
- NECESSITY: where a recursor IS admitted the premise is genuinely false
  — `wSuccU` inhabits `DerivedIota natEnvU` — so `hno` cannot be dropped
  for arbitrary `E`; it is a per-environment condition paid at
  recursor-free tables. -/

/-- `hno` discharged: no `.recursorM` member ⇒ no `DerivedIota` — the
    witness's `hrec`/`hrecK` pair would have to name a recursor member
    the table does not contain. The env-level generalization of
    `noDerivedIota_foldEnv_of_noRecursors` (which supplies the same
    argument for checked finite `foldEnv` tables). -/
theorem noDerivedIota_of_noRecursor {E : ResolvedEnv}
    (hnorec : ∀ r m, E.members r = some m → m.mclass ≠ .recursorM) :
    ∀ lhs rhs, DerivedIota E lhs rhs → False := by
  rintro lhs rhs ⟨w⟩
  exact hnorec w.recRef w.recMember w.hrec w.hrecK

/-- the discharged form of `DT020T_lambda_embeds_into_iota`: a
    recursor-free member table pays `hno` from its own shape. -/
theorem DT020T_lambda_embeds_into_iota_of_noRecursor {E : ResolvedEnv}
    (hnorec : ∀ r m, E.members r = some m → m.mclass ≠ .recursorM)
    {n : Nat} {Γ : LCtx} {e A : Expr Nat} (h : HasTyT E n Γ e A) :
    NoIotaTy h :=
  DT020T_lambda_embeds_into_iota (noDerivedIota_of_noRecursor hnorec) h

/-- `pinFamEnv`'s member table is recursor-free — decidable data about
    the admitted environment, not a hypothesis. -/
theorem pinFamEnv_noRecursor : ∀ r m, pinFamEnv.members r = some m →
    m.mclass ≠ .recursorM := by
  intro r m hm
  by_cases h0 : r = 0
  · subst h0
    simp only [pinFamEnv, extendEnv, ↓reduceIte] at hm
    obtain rfl := Option.some.inj hm
    decide
  · unfold pinFamEnv at hm
    rw [members_extend_ne _ _ _ _ h0] at hm
    simp [emptyEnv] at hm

/-- PIN (DT-020T): `pinFamEnv` — a real admitted inductive family, no
    recursor — is ι-free by member-table shape: `hno` derived, never
    presented. -/
theorem pin_DT020T_noIotaFamEnv {n : Nat} :
    NoIotaTy (pinSortT pinFamEnv n) :=
  DT020T_lambda_embeds_into_iota_of_noRecursor pinFamEnv_noRecursor
    (pinSortT pinFamEnv n)

/-- NECESSITY (DT-020T): `hno` cannot hold for arbitrary `E` — at
    `natEnvU`, `wSuccU` inhabits `DerivedIota` outright. The premise is
    genuinely load-bearing: the iota-free profile is provable exactly at
    environments whose member table keeps recursors out. -/
theorem pin_DT020T_hno_necessary :
    Nonempty (DerivedIota natEnvU (iotaLhsOf wSuccU) (iotaRhsOf wSuccU)) ∧
    ¬ (∀ lhs rhs, DerivedIota natEnvU lhs rhs → False) :=
  ⟨⟨.of wSuccU⟩, fun h => h _ _ (.of wSuccU)⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.DT015T_rigidity
#print axioms Rcic.Declarative.DT015T_rigidity_derivedIota
#print axioms Rcic.Declarative.DT020T_lambda_embeds_into_iota
#print axioms Rcic.Declarative.noIotaConvT_iota_refused
#print axioms Rcic.Declarative.noIotaTy_conv_iota_refused
#print axioms Rcic.Declarative.pin_DT015T_natU
#print axioms Rcic.Declarative.pin_DT020T_zeta_iotaFree
#print axioms Rcic.Declarative.noIotaTy_of_noDerivedIota
#print axioms Rcic.Declarative.noIotaConvT_of_noDerivedIota
#print axioms Rcic.Declarative.noDerivedIota_emptyEnv
#print axioms Rcic.Declarative.pin_DT020T_noIotaEnv
#print axioms Rcic.Declarative.pin_DT020T_iota_refused
#print axioms Rcic.Declarative.noDerivedIota_of_noRecursor
#print axioms Rcic.Declarative.DT020T_lambda_embeds_into_iota_of_noRecursor
#print axioms Rcic.Declarative.pinFamEnv_noRecursor
#print axioms Rcic.Declarative.pin_DT020T_noIotaFamEnv
#print axioms Rcic.Declarative.pin_DT020T_hno_necessary
