import rcic.RcicSynAppBvarPBit
import rcic.RcicSynStepCore4
import rcic.RcicSynClosedEslam
import rcic.RcicSynNatSuccIota

/-!
# sortRow staged PBits — the total regularity-bit coherence theorem

`research/rcic/sortrow/PBIT_STAGED_PORTS_CENSUS.md` (glm-pbits lane).
`closure_claim = 0`.

## The uniform discharge (one mechanism, no per-site rules)

Every staged `PBit` port the census leaves open is `PBit σ ρ D D.reg.2`
(the regularity bit, schema S1) possibly composed with a same-subject
`BitCoh` (schema S1∘S2) through `pbit_of_reg_and_bitCoh`. This module proves
the ONE coherence theorem that answers all of them, in the **landed form**
(`Below Aw tbl (tyPairMeas Aw D DT)`, exactly as `RcicSynSortPBit` /
`RcicSynAppBvarPBit` state theirs):

* `PBitRegResid` — the named residual scheme, per head. Zero residual at
  `sort`/`pi`/`const`/`lit`/`conv`/`lam`/`letE`; the design-point-B bvar
  spine ports at `bvar`; the cross-subject function/codomain bit at `app`;
  the inner regularity bit at the six transports (shifted display/context —
  the context-shift `DispFor` is reader data, exactly as the landed
  `pbit_*_of_inner` family states).
* `pbit_reg_of_below` — the total theorem: for ANY `D : TyP` and any
  sort-typing `DT` of its type, `LevelHom σ`, the display fit, the residual,
  and `Below Aw tbl (tyPairMeas Aw D DT)` give `PBit σ ρ D D.reg.2`. `D` sits
  AT the bound, so `Below.pb` is only callable on strict children of `D`
  (via the landed per-head descent lemmas `lexDM_lam_body_pair`,
  `lexDM_app_fun_reg_pair`, `lexDM_esub_val_pair`, …); the conclusion is not
  a projection of any single `Below` field. Heads with landed
  `*_reg_of_below` lemmas delegate to them (composition, never copy).
* `bitEq_of_below_lex` — the same-subject bare-bit answer (schema S2 with
  subject identity) in the `sortCoh_of_below_lex` shape: any
  `levelIsZero (σ u₁) = levelIsZero (σ u₂)` between two sort-typings of one
  expression follows from `Below.bitCoh` at any bound strictly above the
  pair.

## The `*_closed` applications (fixpoint-arm bounds, landed form)

Each port is stated at its own pair measure, so every `Below.pb` call inside
the proof runs on that endpoint's strict children only:

* `pb_app_pbit_of_below` — the `PbHead.app` port `PBit σ ρ (TyP.app …) hT`
  (`RcicSynStepPbCase.lean:108`): the residual case split at `DT := hT`.
* `app_ports_pbits_closed` — all four `AppPorts` PBits (`pbFunL/pbFunR/
  pbArgL/pbArgR`, `RcicSynStepFields5.lean:334–341`). The `L` ports are the
  residual case split at their own reg pair; the `R` ports compose the reg
  bit with the named same-subject `BitCoh` (the census S2 residue; inhabited
  at every common-level endpoint pair, `bitCoh_rfl`). The two `TagCoh`s stay
  open (cross-type, census §1.1).
* `beta_star_pbits_closed` — the `es_beta` `star`-verdict residual
  `PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2`
  (`RcicSynStepFieldsEsBeta.lean:126`); `dr`'s subject is the computed
  `instantiate0 arg body`, so the cohesion is the named premise.
* `lam_star_pbits_closed` — the `es_lam` `star`-verdict residual
  (`RcicSynStepFieldsEsLam.lean:178–181`); here `dr`'s subject is the
  constructor-headed `.lam A' b'`, so the cohesion is DERIVED from the one
  `Below` at `(dr, dl.reg.2)` via the landed
  `pbit_of_below_not_isSortHead` bridge and `isSortHead_false_of_lam_subject`.
* `appBit_of_readPi_of_below` — the `app` bare bit on the entire
  `readPi`-readable fragment (`readPi_sort_level_eq_of_isSortOrPiHead` +
  `imax_bit` + the landed `bitCoh_app_instEnd_of_below`): the residual is the
  non-read half, named exactly, not claimed where it fails.

## Non-vacuity witnesses and the measured `Below` boundary

* `below_pair_sorts` — `Below` is INHABITED at the pair measure of a
  weight-1 sort against its reg typing: nothing measurable is below
  `([1],1] ++ [1], 2)` (every conversion carries an atom `≥ 2`,
  `CvP.atoms_ge_two`; every two-derivation pair has `≥ 2` positive atoms),
  so all six fields hold vacuously at ANY table. This is the pair analogue
  of the landed `below_pinSortP` (Q9.3).
* `pbitRegBelowSortW` / `pbitRegBelowSortW_natSucc` — the FULL hypothesis
  telescope of `pbit_reg_of_below` (LevelHom, DispFor, residual, `Below`)
  holds at a concrete weight-1 sort; the second def pins it to
  `natSuccTable` (`RcicSynNatSuccIota.lean`).
* `lam_star_resid_eslamfix` — the `lam_star` residual telescope at the
  canonical bare-lam fixture (`EslamFix.dl_can`, both endpoints).
* `pbitRegResidBvarZero`, `pbitRegResidEwkSort`, `bitCoh_rfl` — the named
  residuals and the cohesion premise type are each inhabited.

**The measured boundary** (census §"the measured Below boundary"): at any
bound with an atom `≥ 3` — every `app`/`beta`/`lam`-subject pair measure —
the `Below` hypothesis dominates arbitrary `bvar` pairs, whose `PBit` needs
spine data beyond `DispFor` (design point B, `pb_bvar_bitCoh` / #7615), so
full-telescope witnesses for the `*_closed` forms do not close here; the
`Below` side is the load-bearing open hypothesis, exactly as for the landed
`pbit_*_of_below` family. The theorems below share that family's hypothesis
class — no stronger — and their conclusions are not field projections.

## Positioning (the complementary landed lanes)

The forest-path route (`occ_pb` + `StepIH`) is already landed on the
`RegSubAt` sub-domain: `RcicSynClosedEsapp.es_issued_occ_pb` closes the four
`AppPorts` PBits there, naming `sort`/`pi`/`lam`/`lit`/transport-headed
endpoints as its residue; `RcicSynClosedEslam.LamStarResid` keeps the
single-star pair as a `PSum` whose premise leg is kernel-checked unreachable
by receipts at a bare `TyP.lam`. This module's weight-based route reads no
forest, so it closes exactly those residue classes — every head except
`bvar`/`app`/transports is zero-residual.

The genuinely open remainders (cross-type tags, reader-dropped domain sort
receipts, `ClConstPorts.hbit` aliases, `BvarGate` data, the CL/gate ports)
are named in the census and unchanged here. Axioms ⊆ {propext, Quot.sound}.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the residual scheme -/

/-- The per-head named residuals of the total regularity-bit theorem.
    `PUnit` at the seven zero-residual heads; at `bvar` the design-point-B
    spine ports; at `app` the cross-subject function/codomain bit; at the
    six transports the inner regularity bit at its shifted display/context. -/
def PBitRegResid (σ : Level → Level) (ρ : List Disp) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Type
  | _, _, _, _, _, .sort .. => PUnit
  | _, _, _, _, _, .bvar _ _ _ _ _ _ hlook hA => PbBvarSpinePorts hlook hA σ ρ
  | _, _, _, _, _, .const .. => PUnit
  | _, _, _, _, _, .pi .. => PUnit
  | _, _, _, _, _, .lam .. => PUnit
  | _, _, _, _, _, .app _ _ _ _ _ _ _ w hf _ _ =>
      PLift (levelIsZero (σ hf.reg.1) = levelIsZero (σ w))
  | _, _, _, _, _, .letE .. => PUnit
  | _, _, _, _, _, .lit .. => PUnit
  | _, _, _, _, _, .conv .. => PUnit
  | _, _, _, _, _, .wk _ _ _ _ _ d c D₀ => PLift (PBit σ (removeAt ρ c) D₀ D₀.reg.2)
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D₀ _ _ _ =>
      PLift (PBit σ
        (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) D₀ D₀.reg.2)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D₀ _ hv _ =>
      PLift (PBit σ
        (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ) D₀ D₀.reg.2)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D₀ =>
      PLift (PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2)
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀ => PLift (PBit σ ρ D₀ D₀.reg.2)
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _ => PLift (PBit σ ρ D₀ D₀.reg.2)

/-! ## §2 subject-head facts -/

/-- A derivation whose head leaf is `.sort` types a `.sort` subject:
    transports preserve the subject, so `isSortHead = true` pins the
    subject expr to a literal sort. -/
theorem expr_sort_of_isSortHead :
    ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
      (D : TyP E n Γ e T), D.isSortHead = true →
    ∃ l : Level, e = Expr.sort l
  | _, _, _, _, _, .sort _ _ _ l _ _, _ => ⟨l, rfl⟩
  | _, _, _, _, _, .pi .., h => Bool.noConfusion h
  | _, _, _, _, _, .bvar .., h => Bool.noConfusion h
  | _, _, _, _, _, .const .., h => Bool.noConfusion h
  | _, _, _, _, _, .lam .., h => Bool.noConfusion h
  | _, _, _, _, _, .app .., h => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, h =>
      match expr_sort_of_isSortHead D₀ h with
      | ⟨l, hl⟩ => ⟨l, by rw [hl]; rfl⟩
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h =>
      match expr_sort_of_isSortHead D₀ h with
      | ⟨l, hl⟩ => ⟨l, by rw [hl]; rfl⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h =>
      match expr_sort_of_isSortHead D₀ h with
      | ⟨l, hl⟩ => ⟨l, by rw [hl]; rfl⟩
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D₀, h =>
      match expr_sort_of_isSortHead D₀ h with
      | ⟨l, hl⟩ => ⟨instLevel ls l, by rw [hl]; rfl⟩
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, h => expr_sort_of_isSortHead D₀ h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, h => expr_sort_of_isSortHead D₀ h

/-- No derivation of a literal `.app f a` subject has a `.sort` head leaf. -/
theorem isSortHead_false_of_app_subject {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {T : Expr Nat} (D : TyP E n Γ (.app f a) T) :
    D.isSortHead = false := by
  cases hD : D.isSortHead with
  | false => rfl
  | true =>
      obtain ⟨l, hl⟩ := expr_sort_of_isSortHead D hD
      exact Expr.noConfusion hl

/-- No derivation of a literal `.lam A b` subject has a `.sort` head leaf. -/
theorem isSortHead_false_of_lam_subject {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b : Expr Nat} {T : Expr Nat} (D : TyP E n Γ (.lam A b) T) :
    D.isSortHead = false := by
  cases hD : D.isSortHead with
  | false => rfl
  | true =>
      obtain ⟨l, hl⟩ := expr_sort_of_isSortHead D hD
      exact Expr.noConfusion hl

/-! ## §3 the inhabited pair bound -/

/-- (private) the `1 + p + q` non-transport weight is `≥ 2`. -/
private theorem wt_pos_omega2 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e₁ T₁ e₂ T₂ : Expr Nat} (p : TyP E n Γ e₁ T₁) (q : TyP E n Γ e₂ T₂) :
    2 ≤ 1 + p.wt Aw + q.wt Aw := by
  have _ := TyP.wt_pos Aw p
  have _ := TyP.wt_pos Aw q
  omega

/-- (private) the `1 + p + q + r` non-transport weight is `≥ 2`. -/
private theorem wt_pos_omega3 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ : Expr Nat} (p : TyP E n Γ e₁ T₁) (q : TyP E n Γ e₂ T₂)
    (r : TyP E n Γ e₃ T₃) : 2 ≤ 1 + p.wt Aw + q.wt Aw + r.wt Aw := by
  have _ := TyP.wt_pos Aw p
  have _ := TyP.wt_pos Aw q
  have _ := TyP.wt_pos Aw r
  omega

/-- (private) the `1 + p + q + r + s` non-transport weight is `≥ 2`. -/
private theorem wt_pos_omega4 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ e₄ T₄ : Expr Nat} (p : TyP E n Γ e₁ T₁) (q : TyP E n Γ e₂ T₂)
    (r : TyP E n Γ e₃ T₃) (s : TyP E n Γ e₄ T₄) :
    2 ≤ 1 + p.wt Aw + q.wt Aw + r.wt Aw + s.wt Aw := by
  have _ := TyP.wt_pos Aw p
  have _ := TyP.wt_pos Aw q
  have _ := TyP.wt_pos Aw r
  have _ := TyP.wt_pos Aw s
  omega

/-- (private) a non-transport's atoms are `[wt]`, so a weight `≥ 2` is an
    atom `≥ 2`. -/
private theorem atoms_ge_two_of_wt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {h : CvP E n Γ a b T} (Aw : Nat → Nat)
    (ht : h.isTransport = false) (hw : 2 ≤ h.wt Aw) :
    ∃ x ∈ h.atoms Aw, 2 ≤ x := by
  rw [CvP.atoms_rule Aw h ht]
  exact ⟨h.wt Aw, List.mem_singleton.mpr rfl, hw⟩

/-- Every conversion's atom multiset carries an atom `≥ 2`: a non-transport
    is its own rule weight `1 + premises ≥ 2`, and every transport flattens
    into a part that already carries one. -/
theorem CvP.atoms_ge_two (Aw : Nat → Nat) :
    ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T), ∃ x ∈ h.atoms Aw, 2 ≤ x
  | _, _, _, _, _, _, .refl _ _ _ _ _ hd dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega3 Aw hd dl dr)
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ hd dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw hd
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw h1
      have _ := CvP.wt_pos Aw h2
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ hA hb harg dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := TyP.wt_pos Aw hA
      have _ := TyP.wt_pos Aw hb
      have _ := TyP.wt_pos Aw harg
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ hA hv hb dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := TyP.wt_pos Aw hA
      have _ := TyP.wt_pos Aw hv
      have _ := TyP.wt_pos Aw hb
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ hv dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega3 Aw hv dl dr)
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ hb dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega3 Aw hb dl dr)
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ hl hr dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega4 Aw hl hr dl dr)
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ hexp dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega3 Aw hexp dl dr)
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw h1
      have _ := CvP.wt_pos Aw h2
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hA hb dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw hA
      have _ := CvP.wt_pos Aw hb
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hA hB dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw hA
      have _ := CvP.wt_pos Aw hB
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw hA
      have _ := CvP.wt_pos Aw hv
      have _ := CvP.wt_pos Aw hb
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega2 Aw dl dr)
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega2 Aw dl dr)
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ hd dl dr =>
      atoms_ge_two_of_wt Aw rfl (wt_pos_omega3 Aw hd dl dr)
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ hP hp hq dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := TyP.wt_pos Aw hP
      have _ := TyP.wt_pos Aw hp
      have _ := TyP.wt_pos Aw hq
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ hd hA dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := CvP.wt_pos Aw hd
      have _ := CvP.wt_pos Aw hA
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ hB hA hab dl dr => by
      refine atoms_ge_two_of_wt Aw rfl ?_
      simp only [CvP.wt]
      have _ := TyP.wt_pos Aw hB
      have _ := TyP.wt_pos Aw hA
      have _ := CvP.wt_pos Aw hab
      have _ := TyP.wt_pos Aw dl
      have _ := TyP.wt_pos Aw dr
      omega
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ hcv => CvP.atoms_ge_two Aw hcv
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ hcv _ hv hvT => by
      obtain ⟨x, hx, hx2⟩ := CvP.atoms_ge_two Aw hcv
      refine ⟨x, ?_, hx2⟩
      simp only [CvP.atoms]
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl hx)))
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ hcv => CvP.atoms_ge_two Aw hcv
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ hcv => CvP.atoms_ge_two Aw hcv
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ hcv _ => by
      obtain ⟨x, hx, hx2⟩ := CvP.atoms_ge_two Aw hcv
      refine ⟨x, ?_, hx2⟩
      simp only [CvP.atoms]
      exact List.mem_append.mpr (Or.inl hx)


/-- No positive multiset with an atom `≥ 2`, nor any positive multiset of
    two or more atoms, steps `DMStep`-below `[1, 1]`: the removed `X` lives
    in `[1, 1]` so `Y` would need an atom `< 1`. -/
theorem not_dmStep_two_ones {M : List Nat} (hpos : ∀ y ∈ M, 1 ≤ y)
    (hbig : 2 ≤ M.length ∨ ∃ x ∈ M, 2 ≤ x) : ¬ DMStep M [1, 1] := by
  rintro ⟨X, Y, Z, hXne, hMX, hYZ, hlt⟩
  have hXZ1 : ∀ w ∈ X ++ Z, w = 1 := by
    intro w hw
    have hw1 : w ∈ [1, 1] := hMX.mem_iff.mpr hw
    rcases List.mem_cons.mp hw1 with rfl | h2
    · rfl
    · exact List.mem_singleton.mp h2
  have hYnil : Y = [] := by
    cases Y with
    | nil => rfl
    | cons y Y' =>
        exfalso
        obtain ⟨x, hxX, hyx⟩ := hlt y (List.mem_cons_self y Y')
        have hx1 : x = 1 := hXZ1 x (List.mem_append_left _ hxX)
        have hym : y ∈ M :=
          hYZ.mem_iff.mpr (List.mem_append_left _ (List.mem_cons_self y Y'))
        have := hpos y hym
        omega
  have hLXZ : X.length + Z.length = 2 := by
    have := hMX.length_eq
    simpa [List.length_append] using this.symm
  rcases hbig with hlen | hbigx
  · rw [hYnil, List.nil_append] at hYZ
    have hML : M.length = Z.length := hYZ.length_eq
    have hX0 : X.length = 0 := by omega
    exact hXne (List.eq_nil_of_length_eq_zero hX0)
  · obtain ⟨x, hxM, hx2⟩ := hbigx
    have hxYZ : x ∈ Y ++ Z := hYZ.mem_iff.mp hxM
    rcases List.mem_append.mp hxYZ with hxy | hxZ
    · obtain ⟨x', hx'X, hxx'⟩ := hlt x hxy
      have hx'1 : x' = 1 := hXZ1 x' (List.mem_append_left _ hx'X)
      omega
    · have hx1 : x = 1 := hXZ1 x (List.mem_append_right _ hxZ)
      omega

/-- Nothing measurable is `LexDM`-below `([1, 1], 2)` unless it is a
    positive multiset with an atom `≥ 2`, or of two or more atoms, at
    weight `≥ 2` — each impossible at that bound. -/
theorem not_lex_two_ones {M : List Nat} {w : Nat} (hpos : ∀ y ∈ M, 1 ≤ y)
    (hbig : 2 ≤ M.length ∨ ∃ x ∈ M, 2 ≤ x) (hw : 2 ≤ w) :
    ¬ Prod.Lex DMStep (fun x y : Nat => x < y) (M, w) ([1, 1], 2) := by
  intro hlt
  cases hlt with
  | left _ _ hdm => exact not_dmStep_two_ones hpos hbig hdm
  | right _ hltw => omega

/-- (private) both atoms of a derivation pair are positive. -/
private theorem atoms_pair_pos (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e₁ T₁) (D₂ : TyP E n Γ e₂ T₂) :
    ∀ y ∈ D₁.atoms Aw ++ D₂.atoms Aw, 1 ≤ y := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_pos_ty Aw D₁ y hy
  · exact atoms_pos_ty Aw D₂ y hy

/-- (private) a derivation pair has at least two atoms. -/
private theorem atoms_pair_len (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e₁ T₁) (D₂ : TyP E n Γ e₂ T₂) :
    2 ≤ (D₁.atoms Aw ++ D₂.atoms Aw).length := by
  have h1 : 0 < (D₁.atoms Aw).length :=
    List.length_pos.mpr (TyP.atoms_ne_nil Aw D₁)
  have h2 : 0 < (D₂.atoms Aw).length :=
    List.length_pos.mpr (TyP.atoms_ne_nil Aw D₂)
  rw [List.length_append]
  omega

/-- The pair analogue of the landed `below_pinSortP` (Q9.3): at the pair
    measure of a weight-1 sort against its own regular typing —
    `([1] ++ [1], 2)` — nothing measurable is below, so `Below` holds at
    EVERY `Aw` and table. This is the inhabited end of the `Below`
    hypothesis for pair-measure statements. -/
def below_pair_sorts (Aw : Nat → Nat) (tbl : List CRule) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {l k : Level} (h : eqN k (.succ l)) :
    Below Aw tbl (tyPairMeas Aw (TyP.sort E n Γ l k h) (TyP.sort E n Γ l k h).reg.2) where
  es hcv _ _ _ hlt := by
    obtain ⟨x, hx, hx2⟩ := CvP.atoms_ge_two Aw hcv
    have hw : 2 ≤ hcv.wt Aw := Nat.le_trans hx2 (CvP.atoms_le Aw hcv x hx)
    exact (not_lex_two_ones (atoms_pos_cv Aw hcv) (Or.inr ⟨x, hx, hx2⟩) hw hlt).elim
  cl D₁ D₂ _ _ _ hlt := by
    have hw : 2 ≤ D₁.wt Aw + D₂.wt Aw := by
      have _ := TyP.wt_pos Aw D₁
      have _ := TyP.wt_pos Aw D₂
      omega
    exact (not_lex_two_ones (atoms_pair_pos Aw D₁ D₂) (Or.inl (atoms_pair_len Aw D₁ D₂))
      hw hlt).elim
  eut D₁ D₂ _ _ _ hlt := by
    have hw : 2 ≤ D₁.wt Aw + D₂.wt Aw := by
      have _ := TyP.wt_pos Aw D₁
      have _ := TyP.wt_pos Aw D₂
      omega
    exact (not_lex_two_ones (atoms_pair_pos Aw D₁ D₂) (Or.inl (atoms_pair_len Aw D₁ D₂))
      hw hlt).elim
  cts hcv DX hlt := by
    have hpos : ∀ y ∈ hcv.atoms Aw ++ DX.atoms Aw, 1 ≤ y := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact atoms_pos_cv Aw hcv y hy
      · exact atoms_pos_ty Aw DX y hy
    have hlen : 2 ≤ (hcv.atoms Aw ++ DX.atoms Aw).length := by
      have h1 : 0 < (hcv.atoms Aw).length :=
        List.length_pos.mpr (CvP.atoms_ne_nil Aw hcv)
      have h2 : 0 < (DX.atoms Aw).length :=
        List.length_pos.mpr (TyP.atoms_ne_nil Aw DX)
      rw [List.length_append]
      omega
    have hw : 2 ≤ hcv.wt Aw + DX.wt Aw := by
      have _ := CvP.wt_pos Aw hcv
      have _ := TyP.wt_pos Aw DX
      omega
    exact (not_lex_two_ones hpos (Or.inl hlen) hw hlt).elim
  pb D DT _ _ _ hlt := by
    have hw : 2 ≤ D.wt Aw + DT.wt Aw := by
      have _ := TyP.wt_pos Aw D
      have _ := TyP.wt_pos Aw DT
      omega
    exact (not_lex_two_ones (atoms_pair_pos Aw D DT) (Or.inl (atoms_pair_len Aw D DT))
      hw hlt).elim
  bitCoh D₁ D₂ _ _ _ hlt := by
    have hw : 2 ≤ D₁.wt Aw + D₂.wt Aw := by
      have _ := TyP.wt_pos Aw D₁
      have _ := TyP.wt_pos Aw D₂
      omega
    exact (not_lex_two_ones (atoms_pair_pos Aw D₁ D₂) (Or.inl (atoms_pair_len Aw D₁ D₂))
      hw hlt).elim

/-! ## §4 the total regularity-bit theorem (landed form) -/

/-- `PBit σ ρ D D.reg.2` for ANY derivation `D`, from `LevelHom σ`, the
    display fit, the per-head residual, and `Below Aw tbl (tyPairMeas Aw D DT)`
    — the landed form: `D` sits AT the bound, so `Below.pb` answers only the
    strict children (each head via its landed descent lemma; the heads with
    landed `*_reg_of_below` lemmas delegate to them). One mechanism for
    every staged S1/S1∘S2 bit. -/
theorem pbit_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {σ : Level → Level} (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) {s : Level} (DT : TyP E n Γ T (.sort s))
    {ρ : List Disp} (hρ : DispFor σ E n Γ ρ)
    (r : PBitRegResid σ ρ D)
    (Bel : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D D.reg.2 := by
  cases D with
  | sort E n Γ l k h =>
      exact pbit_reg_of_isSortOrPiHead (D := TyP.sort E n Γ l k h) rfl hσ.levelSub ρ
  | bvar E n Γ i A u hlook hA =>
      have r' : PbBvarSpinePorts hlook hA σ ρ := r
      exact pbit_bvar_spine r'.dispC r'.sortAt r'.spineLet rfl
  | const E n Γ r ls ls₀ m u hres hlen hwf hls hT =>
      exact pbit_const_reg σ ρ hres hlen hwf hls hT
  | pi E n Γ A u B v hA hB =>
      exact pbit_reg_of_isSortOrPiHead (D := TyP.pi E n Γ A u B v hA hB) rfl hσ.levelSub ρ
  | lam E n Γ A u body B v hA hbody hB =>
      exact pbit_lam_reg_of_below Aw tbl hA hbody hB DT hσ ρ hρ Bel
  | app E n Γ f a A B w hf ha hT =>
      have r' : PLift (levelIsZero (σ hf.reg.1) = levelIsZero (σ w)) := r
      exact pbit_app_of_fun σ ρ hf ha hT hf.reg.2 hT
        (Bel.pb hf hf.reg.2 σ ρ hρ (lexDM_app_fun_reg_pair Aw hf ha hT DT))
        r'.down
  | letE E n Γ A u value B body w hA hv hb hT =>
      exact pbit_letE_reg_of_below Aw tbl hA hv hb hT DT σ ρ hρ Bel
  | lit E n Γ t T hexp =>
      exact pbit_lit_reg_of_below Aw tbl hexp DT σ ρ hρ Bel
  | conv E n Γ e A B u h hc =>
      exact pbit_conv_reg_of_below Aw tbl h hc DT σ ρ hρ Bel
  | wk E n Γ e A d c D₀ =>
      have r' : PLift (PBit σ (removeAt ρ c) D₀ D₀.reg.2) := r
      exact pbit_wk_reg_of_inner σ ρ D₀ r'.down
  | esub E n Γ e A t v j u D₀ hget hv hvT =>
      have r' : PLift (PBit σ
        (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) D₀ D₀.reg.2) := r
      cases hu : levelIsZero (σ u) with
      | true =>
          exact pbit_esub_drop_reg_of_inner σ ρ D₀ hget hv hvT hu
            (by simpa [hu, binderDisp_drop] using r'.down)
      | false =>
          exact pbit_esub_keep_of_inner σ ρ D₀ hget hv hvT D₀.reg.2 _ hu
            (Bel.pb hv hvT σ ρ hρ (lexDM_esub_val_pair Aw D₀ hget hv hvT DT))
            (by simpa [hu, binderDisp_keep] using r'.down) rfl
  | lsub E n Γ e A t v j u D₀ hget hv hvT =>
      have r' : PLift (PBit σ
        (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ) D₀ D₀.reg.2) := r
      exact pbit_lsub_reg_of_inner σ ρ D₀ hget hv hvT r'.down
  | linst E a n Γ e A ls hls hlen D₀ =>
      have r' : PLift (PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2) := r
      exact pbit_linst_reg_of_inner σ ρ hls hlen D₀ r'.down
  | ewk E₀ E n Γ e A hext D₀ =>
      have r' : PLift (PBit σ ρ D₀ D₀.reg.2) := r
      exact (pbit_ewk_reg_iff σ ρ hext D₀).mpr r'.down
  | cctx E n Γ e T A A' u D₀ hA =>
      have r' : PLift (PBit σ ρ D₀ D₀.reg.2) := r
      exact (pbit_cctx_reg_iff σ ρ D₀ hA).mpr r'.down

/-! ## §5 the S2 same-subject bit equation (landed form) -/

/-- Schema S2 with subject identity, in the `sortCoh_of_below_lex` shape:
    any bare bit equation between two sort-typings of ONE expression follows
    from `Below.bitCoh` at any bound strictly above the pair. -/
theorem bitEq_of_below_lex (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n Γ T (.sort u₁)) (D₂ : TyP E n Γ T (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D₁ D₂) bound)
    (Bel : Below Aw tbl bound) :
    levelIsZero (σ u₁) = levelIsZero (σ u₂) :=
  Bel.bitCoh D₁ D₂ σ ρ hρ hlex

/-! ## §6 the `*_closed` applications (each port at its own pair bound) -/

/-- The `PbHead.app` port (`RcicSynStepPbCase.lean:108`): `PBit σ ρ (TyP.app …) hT`
    is the app-head regularity bit — the residual case split at `DT := hT`,
    `Below.pb` called only on the app node's strict children. -/
theorem pb_app_pbit_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    (r : PBitRegResid σ ρ (TyP.app E n Γ f a A B w hf ha hT))
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) hT)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) hT :=
  pbit_reg_of_below Aw tbl hσ _ hT hρ r Bel

/-- The `es_app` `AppPorts` PBits (`pbFunL/pbFunR/pbArgL/pbArgR`,
    `RcicSynStepFields5.lean:334–341`), each port in the landed single-pair
    form: the `L` ports by the residual case split at their own reg pair,
    the `R` ports by composing that reg bit with the named same-subject
    `BitCoh` (census S2; inhabited at every common-level endpoint pair).
    The two `TagCoh`s stay open (cross-type, census §1.1). -/
theorem app_ports_pbits_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    (r1 : PBitRegResid σ ρ h1.dl) (r1' : PBitRegResid σ ρ h1.dr)
    (r2 : PBitRegResid σ ρ h2.dl) (r2' : PBitRegResid σ ρ h2.dr)
    (hcoh1 : BitCoh σ h1.dr.reg.2 h1.dl.reg.2)
    (hcoh2 : BitCoh σ h2.dr.reg.2 h2.dl.reg.2)
    (Bel_dl1 : Below Aw tbl (tyPairMeas Aw h1.dl h1.dl.reg.2))
    (Bel_dr1 : Below Aw tbl (tyPairMeas Aw h1.dr h1.dr.reg.2))
    (Bel_dl2 : Below Aw tbl (tyPairMeas Aw h2.dl h2.dl.reg.2))
    (Bel_dr2 : Below Aw tbl (tyPairMeas Aw h2.dr h2.dr.reg.2)) :
    PBit σ ρ h1.dl h1.dl.reg.2 ∧ PBit σ ρ h1.dr h1.dl.reg.2 ∧
      PBit σ ρ h2.dl h2.dl.reg.2 ∧ PBit σ ρ h2.dr h2.dl.reg.2 :=
  ⟨pbit_reg_of_below Aw tbl hσ h1.dl h1.dl.reg.2 hρ r1 Bel_dl1,
    pbit_of_reg_and_bitCoh h1.dr h1.dl.reg.2
      (pbit_reg_of_below Aw tbl hσ h1.dr h1.dr.reg.2 hρ r1' Bel_dr1) hcoh1,
    pbit_reg_of_below Aw tbl hσ h2.dl h2.dl.reg.2 hρ r2 Bel_dl2,
    pbit_of_reg_and_bitCoh h2.dr h2.dl.reg.2
      (pbit_reg_of_below Aw tbl hσ h2.dr h2.dr.reg.2 hρ r2' Bel_dr2) hcoh2⟩

/-- The `es_beta` `star`-verdict residual (`RcicSynStepFieldsEsBeta.lean:126`):
    `PB[dl, dl.reg.2] ∧ PB[dr, dl.reg.2]` — the left half is the residual
    case split at `dl`'s own reg pair; the right half composes `dr`'s reg bit
    with the named same-subject `BitCoh` (`dr`'s subject is the computed
    `instantiate0 arg body`, so the cohesion cannot be derived from the pair
    bound; `bitCoh_rfl` inhabits the premise type). -/
theorem beta_star_pbits_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ) (rdl : PBitRegResid σ ρ dl) (rdr : PBitRegResid σ ρ dr)
    (hcoh : BitCoh σ dr.reg.2 dl.reg.2)
    (Bel_dl : Below Aw tbl (tyPairMeas Aw dl dl.reg.2))
    (Bel_dr : Below Aw tbl (tyPairMeas Aw dr dr.reg.2)) :
    PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2 :=
  ⟨pbit_reg_of_below Aw tbl hσ dl dl.reg.2 hρ rdl Bel_dl,
    pbit_of_reg_and_bitCoh dr dl.reg.2
      (pbit_reg_of_below Aw tbl hσ dr dr.reg.2 hρ rdr Bel_dr) hcoh⟩

/-- The `es_lam` `star`-verdict residual (`RcicSynStepFieldsEsLam.lean:178–181`):
    `PB[dl, dl.reg.2] ∧ PB[dr, dl.reg.2]`. Here `dr`'s subject is the
    constructor-headed `.lam A' b'`, so `isSortHead = false` holds
    (`isSortHead_false_of_lam_subject`) and the R port is DERIVED from the
    single `Below` at `(dr, dl.reg.2)` via the landed
    `pbit_of_below_not_isSortHead` bridge — no cohesion premise. -/
theorem lam_star_pbits_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ) (rdl : PBitRegResid σ ρ dl) (rdr : PBitRegResid σ ρ dr)
    (Bel_dl : Below Aw tbl (tyPairMeas Aw dl dl.reg.2))
    (Bel_dr : Below Aw tbl (tyPairMeas Aw dr dl.reg.2)) :
    PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2 :=
  ⟨pbit_reg_of_below Aw tbl hσ dl dl.reg.2 hρ rdl Bel_dl,
    pbit_of_below_not_isSortHead Aw tbl dr (isSortHead_false_of_lam_subject dr)
      dl.reg.2 σ ρ hρ (pbit_reg_of_below Aw tbl hσ dr dl.reg.2 hρ rdr Bel_dr) Bel_dr⟩

/-- The `app` bare bit on the entire `readPi`-readable fragment, in the
    landed form: `readPi_sort_level_eq_of_isSortOrPiHead` identifies
    `hf.reg.1` with `.imax g.u g.v`, `imax_bit` drops `g.u`, and the
    `instEnd`/`hT` `BitCoh` is the landed `bitCoh_app_instEnd_of_below` from
    the one `Below` at `(TyP.app …, hT)` — children only. The residual is
    exactly the non-read half — named, not claimed where no read exists. -/
theorem appBit_of_readPi_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (hsp : hf.reg.2.isSortOrPiHead = true)
    {g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B}
    (hr : readPi (envExt_refl E) Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw)
      hf.reg.2 rfl (app_fun_reg_atom_src Aw hf ha hT) = .yes g)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) hT)) :
    levelIsZero (σ hf.reg.1) = levelIsZero (σ w) := by
  have hs := readPi_sort_level_eq_of_isSortOrPiHead (envExt_refl E) Aw
    ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) hf.reg.2 hsp
    (app_fun_reg_atom_src Aw hf ha hT) hr
  have hcoh := bitCoh_app_instEnd_of_below Aw tbl hf ha hT g hT σ ρ hρ Bel
  rw [hs, hσ.imax_bit g.u g.v, hcoh]

/-! ## §7 non-vacuity witnesses -/

/-- The bvar spine residual is inhabited at the `i = 0` assumption fixture:
    the spine is the entry's own `CtxP.assumption`, the entry sort is `rfl`,
    and the spine-let obligation is `trivial` (entry `0` is `.assumption`). -/
def pbitRegResidBvarZero {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp} {A : Expr Nat} {u : Level}
    {hlook : lookupType (.assumption A :: Γ₀) 0 = some (lift 0 1 A)}
    {hA : TyP E n (.assumption A :: Γ₀) (lift 0 1 A) (.sort u)}
    (hC₀ : DispForC σ C₀ ρ₀) (hA₀ : TyP E n Γ₀ A (.sort u)) :
    PBitRegResid σ (binderDisp (levelIsZero (σ u)) :: ρ₀)
      (TyP.bvar E n (.assumption A :: Γ₀) 0 (lift 0 1 A) u hlook hA) :=
  ⟨CtxP.assumption E n Γ₀ A u C₀ hA₀,
    DispForC.assumption hA₀ hC₀, rfl, trivial⟩

/-- A transport residual is inhabited whenever the inner derivation is
    `sort`-headed (its regularity bit is unconditional, `pbit_sort_reg`). -/
def pbitRegResidEwkSort {σ : Level → Level} (hσ : LevelSub σ)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k : Level} {h : eqN k (.succ l)}
    (hext : EnvExt E₀ E) (ρ : List Disp) :
    PBitRegResid σ ρ
      (TyP.ewk E₀ E n Γ (.sort l) (.sort k) hext
        (TyP.sort E₀ n Γ l k h)) :=
  PLift.up (pbit_sort_reg hσ ρ h)

/-- The `beta_star` cohesion premise type is inhabited at every endpoint
    pair with a common reg level — in particular at `dr = dl` (`rfl`). -/
theorem bitCoh_rfl (σ : Level → Level) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u)) :
    BitCoh σ D D :=
  rfl

/-- Full-telescope witness for `pbit_reg_of_below`: at a weight-1 sort the
    residual is `PUnit`, the display fit is `[]` at `id`, and
    `below_pair_sorts` inhabits the `Below` side — EVERY hypothesis of the
    theorem holds at this instance, at every `Aw` and table. -/
def pbitRegBelowSortW {E : ResolvedEnv} {n : Nat} {l k : Level}
    (h : eqN k (.succ l)) (Aw : Nat → Nat) (tbl : List CRule) :
    PBit id [] (TyP.sort E n [] l k h) (TyP.sort E n [] l k h).reg.2 :=
  pbit_reg_of_below Aw tbl levelHom_id (TyP.sort E n [] l k h)
    (TyP.sort E n [] l k h).reg.2 (DispFor.nil levelSub_id) ⟨⟩
    (below_pair_sorts Aw tbl h)

/-- The same witness pinned to `natSuccTable` (`RcicSynNatSuccIota.lean`),
    cc's requested table: the whole telescope holds there. -/
theorem pbitRegBelowSortW_natSucc :
    PBit id [] (TyP.sort natEnvU 1 [] .zero (.succ .zero) (eqN_refl _))
      (TyP.sort natEnvU 1 [] .zero (.succ .zero) (eqN_refl _)).reg.2 :=
  pbitRegBelowSortW (eqN_refl _) AwNat natSuccTable

/-- The `lam_star` residual telescope is inhabited at the canonical bare-lam
    fixture (`EslamFix.dl_can`, both endpoints): the residuals are `PUnit`
    at the `.lam` head, and the R-port cohesion needs no premise. The two
    `Below` bounds remain the load-bearing open hypotheses there (the
    measured `Below` boundary, module header). -/
def lam_star_resid_eslamfix :
    PProd (PBitRegResid id [] EslamFix.dl_can) (PBitRegResid id [] EslamFix.dl_can) :=
  ⟨⟨⟩, ⟨⟩⟩

end Rcic.Syn

#print axioms Rcic.Syn.expr_sort_of_isSortHead
#print axioms Rcic.Syn.isSortHead_false_of_app_subject
#print axioms Rcic.Syn.isSortHead_false_of_lam_subject
#print axioms Rcic.Syn.CvP.atoms_ge_two
#print axioms Rcic.Syn.not_dmStep_two_ones
#print axioms Rcic.Syn.not_lex_two_ones
#print axioms Rcic.Syn.below_pair_sorts
#print axioms Rcic.Syn.pbit_reg_of_below
#print axioms Rcic.Syn.bitEq_of_below_lex
#print axioms Rcic.Syn.app_ports_pbits_closed
#print axioms Rcic.Syn.beta_star_pbits_closed
#print axioms Rcic.Syn.lam_star_pbits_closed
#print axioms Rcic.Syn.pb_app_pbit_of_below
#print axioms Rcic.Syn.appBit_of_readPi_of_below
#print axioms Rcic.Syn.pbitRegResidBvarZero
#print axioms Rcic.Syn.pbitRegResidEwkSort
#print axioms Rcic.Syn.bitCoh_rfl
#print axioms Rcic.Syn.pbitRegBelowSortW
#print axioms Rcic.Syn.pbitRegBelowSortW_natSucc
#print axioms Rcic.Syn.lam_star_resid_eslamfix
