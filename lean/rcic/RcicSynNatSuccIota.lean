import rcic.RcicSynBelow
import rcic.RcicSynES
import rcic.RcicSynPack
import rcic.RcicSynEnrich
import rcic.RcicDTMetaTypedSR

/-!
# S17 — the Nat-successor retained-result ι instance (`wSuccU1`)

`research/rcic/sortrow/S17_NAT_SUCCESSOR_ES.md` (PR #7389). The fixture is
`natEnvU` (universe arity 1) with `wSuccU1 = { wSuccU with ls := [.succ .zero] }`:
`N.rec.{1} P mz ms (succ zero)` where `P = λ n:N. N`, `mz = zero`,
`ms = λ n:N. λ ih:N. zero`, and the one `directRec` field keeps a real
`R(zero)` in the RHS.

* `prefixTy`/`recAtN`/`rawMinorTy` are rebuilt from `pinIota*` producers
  (§2) — never `pin_iotaPreserveT`/`InScope`.
* `hL`/`hR` are `enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil`-enriched and
  `H := CvP.iota … (DerivedIota.of wSuccU1) hL hR hL hR` (§3);
  `Nι := H.wt AwNat` with `AwNat` the enriched admission weight.
* `natSuccRule`/`natSuccTable` are the §6 singleton with `TableWF`.
* §7: the `CRoot.ctor` match plus exactly four β steps reach
  `ER = msε Z (recε Pε Z msε Z)`, kernel-pinned equal to `hR.eps id []`;
  `natSucc_iota_erasure : ES natSuccTable id [] H`.
* §5's request list stores the real derivations; every stored weight is
  `< Nι`; the K1 pair is `BitCoh id qrecZero.reg.2 cβ.dr` and
  `BitCoh id cβ.dl d₀.reg.2`; the exactness mutant `msε Z Z` is rejected
  by the exact-`ER` check, not by normal values.

`closure_claim = 0`; T7 declaration correspondence stays the open wall.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §2 the producers (no `pin_iotaPreserveT`, no `InScope`) -/

/-- `R a` — `rec P mz ms a` as a raw `Expr Nat`, at `ls = [.succ .zero]`. -/
def recAppS17 (a : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ) natMinorS) a

/-- `prefixTy`: the `h0–h3` spine of `pinIotaLhsTy` extracted to a
    straight-line producer — `rec P mz ms : Π n:N. P n` at `[]`. -/
noncomputable def prefixTy :
    HasTyT natEnvU 1 [] (.app (.app (.app (.const 3 [.succ .zero])
      natMotive) natMinorZ) natMinorS)
      (.pi (.const 0 []) (.app natMotive (.bvar 0))) :=
  have h0 : HasTyT natEnvU 1 [] (.const 3 [.succ .zero]) _ :=
    HasTyT.const [] 3 [.succ .zero] natRecMemberU rfl rfl rfl
  have h1 : HasTyT natEnvU 1 [] (.app (.const 3 [.succ .zero]) natMotive)
      (.pi (.app natMotive (.const 1 []))
        (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
            (.app natMotive (.app (.const 2 []) (.bvar 1)))))
          (.pi (.const 0 []) (.app natMotive (.bvar 0))))) :=
    HasTyT.app [] _ _ _ _ h0 pinIotaMotiveTy
  have h2 : HasTyT natEnvU 1 []
      (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
      (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
          (.app natMotive (.app (.const 2 []) (.bvar 1)))))
        (.pi (.const 0 []) (.app natMotive (.bvar 0)))) :=
    HasTyT.app [] _ _ _ _ h1 pinIotaMinorZTy
  HasTyT.app [] _ _ _ _ h2 pinIotaMinorSTy

/-- `recAtN a ha` — `R a : N`, by `prefixTy` applied to `ha : a : N` and the
    original β conversion `P a ≡ N` (`pinIotaMotiveApp`). -/
noncomputable def recAtN (a : Expr Nat)
    (ha : HasTyT natEnvU 1 [] a (.const 0 [])) :
    HasTyT natEnvU 1 [] (recAppS17 a) (.const 0 []) :=
  HasTyT.conv _ _ (.app natMotive a) (.const 0 []) (.succ .zero)
    (HasTyT.app [] _ _ _ _ prefixTy ha) (pinIotaMotiveApp [] a ha)

/-- `rawMinorTy`: `ms : Π n:N. Π ih:N. N` — the rhs's own minor typing,
    two λs over `N : sort 1` and `zero : N`; no β ride, unlike
    `pinIotaMinorSTy` (which lands the declared `Π ih : P n` domain). -/
noncomputable def rawMinorTy :
    HasTyT natEnvU 1 [] natMinorS
      (.pi (.const 0 []) (.pi (.const 0 []) (.const 0 []))) :=
  have hN1 : CtxWfT natEnvU 1 [.assumption (.const 0 [])] :=
    .assumption [] _ _ .nil pinIotaFamTy
  HasTyT.lam [] (.const 0 []) (.succ .zero) (.lam (.const 0 []) (.const 1 []))
    (.pi (.const 0 []) (.const 0 [])) pinIotaFamTy
    (HasTyT.lam _ (.const 0 []) (.succ .zero)
      (.const 1 []) (.const 0 [])
      (pinIotaNSortTy _ hN1)
      (HasTyT.const _ 1 [] natZeroMember rfl rfl rfl))

/-! ## §3 `hLᵀ`, `hRᵀ`, the enriched `hL`/`hR`, `H`, `Nι` -/

/-- `hLᵀ`: `R (succ zero) : N` — the original lhs typing, un-enriched;
    the term ascription is `iotaLhsOf wSuccU1` itself. -/
noncomputable def hLT : HasTyT natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 []) :=
  recAtN _ pinIotaMajorTy

/-- `hRᵀ`: `ms zero (R zero) : N` — the original rhs typing, built
    independently (no `iotaPreserveT`/`InScope`). Its term is exactly
    `iotaRhsOf wSuccU1` (`foldApps natMinorS (rhsArgs …)`), checked by the
    type ascription. -/
noncomputable def hRT : HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 []) :=
  HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _ rawMinorTy pinIotaZeroTy)
    (recAtN _ pinIotaZeroTy)

/-- The enriched lhs typing (one of `H`'s four occurrences). -/
noncomputable def hL : TyP natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil hLT

/-- The enriched rhs typing. -/
noncomputable def hR : TyP natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil hRT

/-- `H`: the stored ι node. `hlhs`/`hrhs`/`dl`/`dr` keep the constructor's
    four original occurrences — equal in value, never de-duplicated. -/
noncomputable def H :
    CvP natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) :=
  CvP.iota natEnvU 1 [] _ _ _ (DerivedIota.of wSuccU1) hL hR hL hR

/-- the real admission weight of `enrichEnvWfT natEnvUWfT`. -/
noncomputable def AwNat : Nat → Nat := (enrichEnvWfT natEnvUWfT).admW

/-- `Nι := H.wt Aw` — the only caller budget. -/
noncomputable def Nι : Nat := H.wt AwNat

/-- §4's shape: `Nι = 1 + 2 * hL.wt + 2 * hR.wt` (four real occurrences). -/
theorem Nι_eq : Nι = 1 + 2 * hL.wt AwNat + 2 * hR.wt AwNat := by
  have hw : H.wt AwNat =
      1 + hL.wt AwNat + hR.wt AwNat + hL.wt AwNat + hR.wt AwNat := rfl
  rw [Nι, hw]; omega

/-! ## §6 the singleton successor-rule table -/

/-- `Pε`, `Zε`, `msε`, `majorε` — the §5.4 erasures of the real arguments
    (`P = λ n:N. N`, `mz = zero`, `ms = λn.λih. zero`, `succ zero`). -/
def Pε : ETm := .lam (.const 0 [])
def Zε : ETm := .const 1 []
def msε : ETm := .lam (.lam (.const 1 []))
def majorε : ETm := .app (.const 2 []) (.const 1 [])

/-- `recε f z s n` — the erased recursor spine `const 3 [succ zero]` applied. -/
def recε (f z s n : ETm) : ETm :=
  ETm.appN (.const 3 [.succ .zero]) [f, z, s, n]

/-- §6 `natSuccRule` — verbatim from the spec; innermost argument order
    `[P, mz, ms, field]` is de Bruijn `[3, 2, 1, 0]`. -/
def natSuccRule : CRule where
  head := 3
  nargs := fun _ => 3
  major := some (2, fun _ => 1)
  rhs := fun ls _ =>
    .lam (.lam (.lam (.lam
      (.app (.app (.bvar 1) (.bvar 0))
        (ETm.appN (.const 3 ls) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))))

def natSuccTable : List CRule := [natSuccRule]

/-- `TableWF` for the singleton, mirroring `loopTable_wf`: rhs congruence,
    closedness under four λs, no rule for the constructor head `2`,
    singleton disjointness, empty bare premises. -/
theorem natSuccTable_wf : TableWF natSuccTable where
  congr :=
    { rhs := by
        intro ρ hρ ls₁ ls₂ ms₁ ms₂ hls _
        simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
        exact .lam (.lam (.lam (.lam
          (.app (.app (.bvar _) (.bvar _))
            (lvlEq_appN (.const _ hls)
              (.cons (.bvar _) (.cons (.bvar _)
                (.cons (.bvar _) (.cons (.bvar _) .nil)))))))))
      nargs := by
        intro ρ hρ _ _ _
        simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
        cases hm; exact fun _ => rfl }
  closed := by
    intro ρ hρ ls ms
    simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
    simp only [natSuccRule, ETm.appN, ETm.ClosedAt]
    exact ⟨⟨by decide, by decide⟩,
      ⟨⟨⟨⟨trivial, by decide⟩, by decide⟩, by decide⟩, by decide⟩⟩
  rigid := by
    intro ρ hρ d m hm σ hσ
    simp only [natSuccTable, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    cases hm; decide
  bare_unique := by
    intro ρ hρ hm σ hσ _
    simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
    simp only [natSuccRule] at hm; exact Option.noConfusion hm
  ctor_disjoint := by
    intro ρ hρ σ hσ _ d e m n hm hn
    simp only [natSuccTable, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    exact ⟨rfl, fun _ => rfl⟩
  bare_nullary := by
    intro ρ hρ hm ls
    simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
    simp only [natSuccRule] at hm; exact Option.noConfusion hm

/-! ## §7 the match, the four β steps, and the exact-`ER` pins -/

/-- `EL` — `hL`'s erasure: `recε Pε Zε msε majorε`. -/
def EL : ETm := recε Pε Zε msε majorε

/-- `ER` — the kept-result rhs: `msε Zε (recε Pε Zε msε Zε)`. -/
def ER : ETm := .app (.app msε Zε) (recε Pε Zε msε Zε)

/-- the 4-λ template body at `ls = [.succ .zero]`: `ms n (rec P mz ms n)`. -/
def s17Body : ETm :=
  .app (.app (.bvar 1) (.bvar 0))
    (ETm.appN (.const 3 [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])

/-- PIN: `natSuccRule`'s template at the concrete level list. -/
theorem natSuccRule_rhs_eq :
    natSuccRule.rhs [.succ .zero] [] = .lam (.lam (.lam (.lam s17Body))) := rfl

/-- PIN: the match root — `EL → appN template [Pε, Zε, msε, Zε]`. -/
theorem natSucc_croot :
    CRoot natSuccTable EL (ETm.appN (natSuccRule.rhs [.succ .zero] [])
      [Pε, Zε, msε, Zε]) :=
  CRoot.ctor (List.mem_singleton_self _) rfl [.succ .zero] [] [Pε, Zε, msε] [Zε] rfl rfl

/-- the β residuals at each peeled λ (kernel-evaluated `inst` chains). -/
def s17M1 : ETm := .lam (.lam (ETm.inst 3 Pε s17Body))
def s17M2 : ETm := .lam (ETm.inst 2 Zε (ETm.inst 3 Pε s17Body))
def s17M3 : ETm := ETm.inst 1 msε (ETm.inst 2 Zε (ETm.inst 3 Pε s17Body))

/-- PIN: `inst 0 Pε (λλλ body) = λ s17M1`. -/
theorem s17_beta1_tgt :
    ETm.inst 0 Pε (.lam (.lam (.lam s17Body))) = .lam s17M1 := rfl

/-- PIN: `inst 0 Zε s17M1 = λ s17M2`. -/
theorem s17_beta2_tgt :
    ETm.inst 0 Zε s17M1 = .lam s17M2 := rfl

/-- PIN: `inst 0 msε s17M2 = λ s17M3`. -/
theorem s17_beta3_tgt :
    ETm.inst 0 msε s17M2 = .lam s17M3 := rfl

/-- PIN: the four-step chain lands on `ER` exactly — kernel index arithmetic,
    not a normal-value check. -/
theorem s17_beta4_tgt :
    ETm.inst 0 Zε s17M3 = ER := rfl

/-- the four β steps as `RStep`s, lifted through the outer applications. -/
def s17Step1 :
    RStep natSuccTable
      (ETm.appN (natSuccRule.rhs [.succ .zero] []) [Pε, Zε, msε, Zε])
      (ETm.appN (.lam s17M1) [Zε, msε, Zε]) :=
  .appL Zε (.appL msε (.appL Zε
    (.beta (.lam (.lam (.lam s17Body))) Pε)))

def s17Step2 :
    RStep natSuccTable
      (ETm.appN (.lam s17M1) [Zε, msε, Zε])
      (ETm.appN (.lam s17M2) [msε, Zε]) :=
  .appL Zε (.appL msε (.beta s17M1 Zε))

def s17Step3 :
    RStep natSuccTable
      (ETm.appN (.lam s17M2) [msε, Zε])
      (ETm.appN (.lam s17M3) [Zε]) :=
  .appL Zε (.beta s17M2 msε)

def s17Step4 :
    RStep natSuccTable
      (ETm.appN (.lam s17M3) [Zε]) ER := by
  unfold ETm.appN
  exact .beta s17M3 Zε

/-- PIN: `hL.eps id []` is exactly `EL` — the real enriched typing's own
    erasure (level-gated consts stay consts; `ls.map id = ls`). -/
theorem hL_eps_el : hL.eps id [] = EL := rfl

/-- PIN: `hR.eps id []` is exactly `ER`. -/
theorem hR_eps_er : hR.eps id [] = ER := rfl

/-- §7's target: `ES natSuccTable id [] H` — the retained-result ι
    discharged by its real match plus exactly four β steps. The recursive
    call is NOT reduced and the result is NOT normalized to `zero`. -/
theorem natSucc_iota_erasure : ES natSuccTable id [] H := by
  show ConvMod (EStep natSuccTable) LvlEq (hL.eps id []) (hR.eps id [])
  rw [hL_eps_el, hR_eps_er]
  exact (ConvMod.fwd (.inl (.cr natSucc_croot))).trans
    ((ConvMod.fwd (.inl s17Step1)).trans
      ((ConvMod.fwd (.inl s17Step2)).trans
        ((ConvMod.fwd (.inl s17Step3)).trans (ConvMod.fwd (.inl s17Step4)))))

/-! ## §5 the request list — real fields, each bounded by `Nι` -/

/-- The argument typings inside `hL`/`hR`, as the same enrichments of the
    original producers (enrichment passes the same `CtxP` to app children,
    so each is literally `H`'s own subderivation). -/
noncomputable def qP : TyP natEnvU 1 [] natMotive
    (.pi (.const 0 []) (.sort (.succ .zero))) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaMotiveTy
noncomputable def qmz : TyP natEnvU 1 [] natMinorZ (.app natMotive (.const 1 [])) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaMinorZTy
noncomputable def qms : TyP natEnvU 1 [] natMinorS
    (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
      (.app natMotive (.app (.const 2 []) (.bvar 1))))) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaMinorSTy
noncomputable def qmajor : TyP natEnvU 1 [] (foldApps (.const 2 []) [natField])
    (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaMajorTy
/-- `qfield` — the major's own argument typing (`zero : N` inside
    `succ zero`). -/
noncomputable def qfield : TyP natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaZeroTy
/-- `qrecZero` — `hR`'s second real argument: `recAtN zero pinIotaZeroTy`
    enriched, i.e. `TyP.conv d₀ cβ`. -/
noncomputable def qrecZero : TyP natEnvU 1 [] (recAppS17 (.const 1 [])) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil (recAtN _ pinIotaZeroTy)

/-- §5.2's `d₀` — `R zero : P zero`, the conv's child typing. -/
noncomputable def d₀ : TyP natEnvU 1 [] (recAppS17 (.const 1 []))
    (.app natMotive (.const 1 [])) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil
    (HasTyT.app [] _ _ _ _ prefixTy pinIotaZeroTy)

/-- §5.2's `cβ` — the original β conversion `P zero ≡ N` enriched. -/
noncomputable def cβ : CvP natEnvU 1 [] (.app natMotive (.const 1 []))
    (.const 0 []) (.sort (.succ .zero)) :=
  enrichConvT_of_envWfT natEnvUWfT CtxWfT.nil
    (pinIotaMotiveApp [] (.const 1 []) pinIotaZeroTy)

/-- PIN: `qrecZero`'s regularity is definitionally `cβ.dr` — the K1 slot
    correspondence is direct, no new chain. -/
theorem qrecZero_reg_eq : qrecZero.reg.2 = cβ.dr := rfl

/-- §5 request kinds: pair-below `PB[a,b]`, the K1 bit `BIT[a,b]` on two
    sort typings of one type, and an outer `CL[a,b]`. -/
inductive S17Request : Type where
  | pb {e₁ T₁ e₂ T₂ : Expr Nat}
      (a : TyP natEnvU 1 [] e₁ T₁) (b : TyP natEnvU 1 [] e₂ T₂)
  | bit {T : Expr Nat} {u v : Level}
      (a : TyP natEnvU 1 [] T (.sort u)) (b : TyP natEnvU 1 [] T (.sort v))
  | cl {e T₁ T₂ : Expr Nat}
      (a : TyP natEnvU 1 [] e T₁) (b : TyP natEnvU 1 [] e T₂)

/-- the derivations each request stores. -/
def S17Request.derivations : S17Request → List (Σ e T, TyP natEnvU 1 [] e T)
  | .pb a b | .cl a b => [⟨_, _, a⟩, ⟨_, _, b⟩]
  | .bit a b => [⟨_, _, a⟩, ⟨_, _, b⟩]

/-- §5's freezable request table: six slot PBs, the K1 BIT pair, and the
    four outer requests of the current ES. -/
noncomputable def s17Requests : List S17Request :=
  [ .pb qP qP.reg.2, .pb qmz qmz.reg.2, .pb qms qms.reg.2,
    .pb qmajor qmajor.reg.2, .pb qfield qfield.reg.2,
    .pb qrecZero qrecZero.reg.2,
    .bit qrecZero.reg.2 cβ.dr, .bit cβ.dl d₀.reg.2,
    .pb hL hL.reg.2, .pb hR hL.reg.2, .cl H.dl hL, .cl hR H.dr ]

/-- every stored derivation's weight is strictly below `Nι` — the §5 bound
    (`dmStep_pair_below` pays each `PB`; BIT/CL entries carry the same
    bound), kernel-computed on the real derivations. -/
theorem s17_requests_below :
    ∀ r ∈ s17Requests, ∀ D ∈ r.derivations, D.2.2.wt AwNat < Nι := by
  decide

/-- §4's six bit-false discharges, one per real slot — kernel-evaluated
    `levelIsZero` on the real regularity level at `σ = id`. -/
theorem bit_qP : levelIsZero (id qP.reg.1) = false := by decide
theorem bit_qmz : levelIsZero (id qmz.reg.1) = false := by decide
theorem bit_qms : levelIsZero (id qms.reg.1) = false := by decide
theorem bit_qmajor : levelIsZero (id qmajor.reg.1) = false := by decide
theorem bit_qfield : levelIsZero (id qfield.reg.1) = false := by decide
theorem bit_qrecZero : levelIsZero (id qrecZero.reg.1) = false := by decide

/-- §5.1's `qa.reg.2.wt ≤ qa.wt` side of each PB payment. -/
theorem reg_le_qP : qP.reg.2.wt AwNat ≤ qP.wt AwNat := by decide
theorem reg_le_qmz : qmz.reg.2.wt AwNat ≤ qmz.wt AwNat := by decide
theorem reg_le_qms : qms.reg.2.wt AwNat ≤ qms.wt AwNat := by decide
theorem reg_le_qmajor : qmajor.reg.2.wt AwNat ≤ qmajor.wt AwNat := by decide
theorem reg_le_qfield : qfield.reg.2.wt AwNat ≤ qfield.wt AwNat := by decide
theorem reg_le_qrecZero : qrecZero.reg.2.wt AwNat ≤ qrecZero.wt AwNat := by decide

/-- the §5.1 payment lemma's shape, discharged for each stored pair: both
    sides strictly below `Nι`, hence `dmStep_pair_below` against `H`. -/
theorem pb_qP_below : qP.wt AwNat < Nι ∧ qP.reg.2.wt AwNat < Nι := by decide
theorem pb_qrecZero_below : qrecZero.wt AwNat < Nι ∧ qrecZero.reg.2.wt AwNat < Nι := by decide

/-- the two K1 bit correspondences, discharged as `BitCoh id`. -/
theorem k1_pair_1 : BitCoh id qrecZero.reg.2 cβ.dr := rfl
theorem k1_pair_2 : BitCoh id cβ.dl d₀.reg.2 := rfl

/-- the two outer CLs hold reflexively on `H`'s chosen fields. -/
theorem cl_outer_left : CL natSuccTable id [] H.dl hL := ConvMod.refl _
theorem cl_outer_right : CL natSuccTable id [] hR H.dr := ConvMod.refl _

/-! ## the exactness mutant -/

/-- the mutant the exactness check must reject: `msε Zε Zε` — the "wrong"
    template that discards the recursive result. Its normal value agrees
    with `msε`'s (`Zε`), but it is NOT `ER`. -/
def msMutant : ETm := .app (.app msε Zε) Zε

theorem mutant_rejected : msMutant ≠ ER := by decide

/-- the mutant β-collapses to `Zε` — the exactness check, not the value
    check, is what rejects it. -/
theorem mutant_value_agrees :
    ETm.inst 0 Zε (ETm.inst 1 Zε (.const 1 [])) = Zε := rfl

/-! ## §4 declaration-domain views (Q221): the recursor's own admission
    telescope, lazily instantiated

`natRecTypeUTyT` is this recursor's OWN admission: it types the telescope
`natRecTypeU = Π (P : Π n:N. Sort u). Π (mz : P zero). Π (ms : Π n:N.
Π ih:P n. P (succ n)). Π (t : N). P t` inside `natEnvPrefix` at one level
parameter.  Each §4 domain view takes the real domain field of that same
telescope, transports it forward along the fresh recursor member's
`EnvExt` (`hasTyTExt`), enriches it under the same `natEnvUWfT`/`AwNat`,
level-instantiates it at `σ = [.succ .zero]` (`TyP.linst` — adds no
atoms), and lazily substitutes the preceding real arguments at
descending index (`TyP.esub`: each `hv` is `H`'s own argument
derivation, each `hvT` that argument's `TyP.reg.2`; the `wk` lifts that
place them in the remaining context add no atoms either).  The domain
expressions are the telescope's own fields (`natRecTele_eq`), so each
view's atoms are the admission-domain atoms plus finite repetitions of
the preceding real argument/reg atoms — every one `< Nι`
(`s17_decl_budget`).  No `spineInvAux`, no `hrows.piRow hconv`; general
T7 stays the open wall. -/

/-- the telescope's field decomposition — the §4 domains are literally
    `natRecTypeU`'s binder fields; `natMajorTy` is its `Π t:N. P t` tail. -/
theorem natRecTele_eq : natRecTypeU =
    .pi natMotTyU (.pi natMzDom (.pi natMsTy natMajorTy)) := rfl

/-- `natEnvPrefix → natEnvU`: the fresh recursor member's forward
    extension — the `hasTyTExt` premise. -/
theorem natPrefToU : EnvExt natEnvPrefix natEnvU :=
  envExt_extendEnv natRecMemberU rfl

/-- the instantiated motive domain `Π n:N. Sort 1` at `σ`. -/
abbrev pDomS17 : Expr Nat := .pi (.const 0 []) (.sort (.succ .zero))

/-- `P zero` — the instantiated mz domain (and the retained `R zero`
    domain): `natMotive` applied to `zero`. -/
abbrev pmzDomS17 : Expr Nat := .app natMotive (.const 1 [])

/-- the ms domain after `P := natMotive` — `mz` stays a dead binder. -/
abbrev msDomS17 : Expr Nat :=
  .pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
    (.app natMotive (.app (.const 2 []) (.bvar 1))))

/-- d0 — the motive's domain `Π n:N. Sort (param 0)`, `natRecTypeUTyT`'s
    first `.pi` child verbatim (`natConstTyT` for `N`, `.sort` for the
    codomain — the same two leaves the admission is built from). -/
noncomputable def s17Dom0T :
    HasTyT natEnvPrefix 1 [] natMotTyU
      (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
  .pi _ _ _ _ _ (natConstTyT rfl) (.sort _ (.param 0))

/-- d1 — the mz domain `P zero`, `natMotAppTyT` at `P`'s entry, verbatim
    the telescope's second domain field. -/
noncomputable def s17Dom1T :
    HasTyT natEnvPrefix 1 [.assumption natMotTyU] natMzDom (.sort (.param 0)) :=
  natMotAppTyT 0 (.const 1 []) rfl (.const _ 1 [] natZeroMember rfl rfl rfl)

/-- d2 — the ms domain `Π n:N. Π ih:P n. P (succ n)` — `natMsTyT` itself. -/
noncomputable def s17Dom2T :
    HasTyT natEnvPrefix 1 [.assumption natMzDom, .assumption natMotTyU]
      natMsTy (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  natMsTyT

/-- d3 — the major's domain `N`, the `natConstTyT` leaf `natMajorTyT`
    uses for its domain field. -/
noncomputable def s17Dom3T :
    HasTyT natEnvPrefix 1
      [.assumption natMsTy, .assumption natMzDom, .assumption natMotTyU]
      (.const 0 []) (.sort (.succ .zero)) :=
  natConstTyT rfl

/-- the result field — `P t : Sort u` inside `natMajorTyT`, verbatim its
    `natMotAppTyT` child (`bvar 3 = P`, `bvar 0 = t`). -/
noncomputable def s17BodyT :
    HasTyT natEnvPrefix 1
      [.assumption (.const 0 []), .assumption natMsTy,
       .assumption natMzDom, .assumption natMotTyU]
      (.app (.bvar 3) (.bvar 0)) (.sort (.param 0)) :=
  natMotAppTyT 3 (.bvar 0) rfl (.bvar _ 0 _ rfl)

/-- the domain fields transported to `natEnvU` along `natPrefToU`. -/
noncomputable def s17Dom0U : HasTyT natEnvU 1 [] natMotTyU
    (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
  hasTyTExt natPrefToU s17Dom0T
noncomputable def s17Dom1U :
    HasTyT natEnvU 1 [.assumption natMotTyU] natMzDom (.sort (.param 0)) :=
  hasTyTExt natPrefToU s17Dom1T
noncomputable def s17Dom2U :
    HasTyT natEnvU 1 [.assumption natMzDom, .assumption natMotTyU] natMsTy
      (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  hasTyTExt natPrefToU s17Dom2T
noncomputable def s17Dom3U :
    HasTyT natEnvU 1
      [.assumption natMsTy, .assumption natMzDom, .assumption natMotTyU]
      (.const 0 []) (.sort (.succ .zero)) :=
  hasTyTExt natPrefToU s17Dom3T
noncomputable def s17BodyU :
    HasTyT natEnvU 1
      [.assumption (.const 0 []), .assumption natMsTy,
       .assumption natMzDom, .assumption natMotTyU]
      (.app (.bvar 3) (.bvar 0)) (.sort (.param 0)) :=
  hasTyTExt natPrefToU s17BodyT

/-- the telescope contexts as `CtxWfT`s — the `esub` domains live in
    them. -/
noncomputable def s17CtxP : CtxWfT natEnvU 1 [.assumption natMotTyU] :=
  .assumption _ _ _ .nil s17Dom0U
noncomputable def s17CtxMz :
    CtxWfT natEnvU 1 [.assumption natMzDom, .assumption natMotTyU] :=
  .assumption _ _ _ s17CtxP s17Dom1U
noncomputable def s17CtxMs :
    CtxWfT natEnvU 1
      [.assumption natMsTy, .assumption natMzDom, .assumption natMotTyU] :=
  .assumption _ _ _ s17CtxMz s17Dom2U
noncomputable def s17CtxBody :
    CtxWfT natEnvU 1
      [.assumption (.const 0 []), .assumption natMsTy,
       .assumption natMzDom, .assumption natMotTyU] :=
  .assumption _ _ _ s17CtxMs s17Dom3U

/-- §4 slot 0 — `P`'s declaration domain `Π n:N. Sort 1`: the telescope's
    `natMotTyU` field enriched and instantiated at `σ`. -/
noncomputable def domViewP : TyP natEnvU 1 [] pDomS17
    (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .linst natEnvU 1 1 _ _ _ [.succ .zero] rfl rfl
    (enrichHasTyT_of_envWfT natEnvUWfT .nil s17Dom0U)

/-- §4 slot 1 — `mz`'s declaration domain `P zero`: `natMzDom` after
    `P := natMotive`, paid by `qP` and `qP.reg.2`. -/
noncomputable def domViewMz : TyP natEnvU 1 [] pmzDomS17 (.sort (.succ .zero)) :=
  .esub natEnvU 1 _ _ _ pDomS17 natMotive 0 _
    (.linst natEnvU 1 1 _ _ _ [.succ .zero] rfl rfl
      (enrichHasTyT_of_envWfT natEnvUWfT s17CtxP s17Dom1U))
    rfl qP qP.reg.2

/-- §4 slot 2 — `ms`'s declaration domain `Π n:N. Π ih:P n. P (succ n)`:
    `natMsTy` after `P := natMotive` then `mz := natMinorZ` (a dead
    binder). -/
noncomputable def domViewMs : TyP natEnvU 1 [] msDomS17
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .esub natEnvU 1 _ _ _ pmzDomS17 natMinorZ 0 _
    (.esub natEnvU 1 _ _ _ pDomS17 natMotive 1 _
      (.linst natEnvU 1 1 _ _ _ [.succ .zero] rfl rfl
        (enrichHasTyT_of_envWfT natEnvUWfT s17CtxMz s17Dom2U))
      rfl
      (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP)
      (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP.reg.2))
    rfl qmz qmz.reg.2

/-- §4 slot 3 — the major's declaration domain `N`: the `natMajorTy`
    domain field after `P := natMotive`, `mz := natMinorZ`,
    `ms := natMinorS`. -/
noncomputable def domViewMajor : TyP natEnvU 1 [] (.const 0 []) (.sort (.succ .zero)) :=
  .esub natEnvU 1 _ _ _ msDomS17 natMinorS 0 _
    (.esub natEnvU 1 _ _ _ pmzDomS17 natMinorZ 1 _
      (.esub natEnvU 1 _ _ _ pDomS17 natMotive 2 _
        (.linst natEnvU 1 1 _ _ _ [.succ .zero] rfl rfl
          (enrichHasTyT_of_envWfT natEnvUWfT s17CtxMs s17Dom3U))
        rfl
        (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0
          (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP))
        (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0
          (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP.reg.2)))
      rfl
      (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0 qmz)
      (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0 qmz.reg.2))
    rfl qms qms.reg.2

/-- §4's field row — the directRec field's declaration domain `N`:
    `succ`'s own `natConstTyT` leaf (the same producer the group
    admission uses for `succ : Π _:N. N`); no preceding arguments. -/
noncomputable def domViewField : TyP natEnvU 1 [] (.const 0 [])
    (.sort (.succ .zero)) :=
  enrichHasTyT_of_envWfT natEnvUWfT .nil (natConstTyT rfl)

/-- §4's directRec row — `R(zero)`'s declaration domain `P zero`: the
    telescope's result field `P t` lazily instantiated at the real
    preceding arguments with `t := zero` (`qfield`); the result's own
    natural typing `qrecZero` goes to `N` by the original β (`cβ`,
    `k1_pair`). -/
noncomputable def domViewRetained : TyP natEnvU 1 [] pmzDomS17 (.sort (.succ .zero)) :=
  .esub natEnvU 1 _ _ _ (.const 0 []) (.const 1 []) 0 _
    (.esub natEnvU 1 _ _ _ msDomS17 natMinorS 1 _
      (.esub natEnvU 1 _ _ _ pmzDomS17 natMinorZ 2 _
        (.esub natEnvU 1 _ _ _ pDomS17 natMotive 3 _
          (.linst natEnvU 1 1 _ _ _ [.succ .zero] rfl rfl
            (enrichHasTyT_of_envWfT natEnvUWfT s17CtxBody s17BodyU))
          rfl
          (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0
            (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0
              (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP)))
          (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0
            (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0
              (.wk natEnvU 1 _ _ _ (.assumption pmzDomS17) 0 qP.reg.2))))
        rfl
        (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0
          (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0 qmz))
        (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0
          (.wk natEnvU 1 _ _ _ (.assumption msDomS17) 0 qmz.reg.2)))
      rfl
      (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0 qms)
      (.wk natEnvU 1 _ _ _ (.assumption (.const 0 [])) 0 qms.reg.2))
    rfl qfield qfield.reg.2

/-- the recursor const's own admission atom is paid through `AwNat 3` —
    strictly below `Nι`. -/
theorem s17_aw3_below : AwNat 3 < Nι := by decide

/-- every atom stored in each §4 view is strictly below `Nι` —
    kernel-computed on the real derivations. -/
theorem domViewP_atoms : ∀ a ∈ domViewP.atoms AwNat, a < Nι := by decide
theorem domViewMz_atoms : ∀ a ∈ domViewMz.atoms AwNat, a < Nι := by decide
theorem domViewMs_atoms : ∀ a ∈ domViewMs.atoms AwNat, a < Nι := by decide
theorem domViewMajor_atoms : ∀ a ∈ domViewMajor.atoms AwNat, a < Nι := by decide
theorem domViewField_atoms : ∀ a ∈ domViewField.atoms AwNat, a < Nι := by decide
theorem domViewRetained_atoms : ∀ a ∈ domViewRetained.atoms AwNat, a < Nι := by decide

/-- §4's six declaration-domain views, as stored `TyP`s. -/
noncomputable def s17DeclViews :
    List (Σ e T, TyP natEnvU 1 [] e T) :=
  [⟨_, _, domViewP⟩, ⟨_, _, domViewMz⟩, ⟨_, _, domViewMs⟩,
   ⟨_, _, domViewMajor⟩, ⟨_, _, domViewField⟩, ⟨_, _, domViewRetained⟩]

/-- §4's fixed declaration-domain budget: every atom of every
    lazy-instantiated view is strictly below `Nι`. -/
theorem s17_decl_budget :
    ∀ v ∈ s17DeclViews, ∀ a ∈ v.2.2.atoms AwNat, a < Nι := by decide

#print axioms Rcic.Syn.natRecTele_eq
#print axioms Rcic.Syn.domViewP
#print axioms Rcic.Syn.domViewMz
#print axioms Rcic.Syn.domViewMs
#print axioms Rcic.Syn.domViewMajor
#print axioms Rcic.Syn.domViewField
#print axioms Rcic.Syn.domViewRetained
#print axioms Rcic.Syn.domViewP_atoms
#print axioms Rcic.Syn.domViewMz_atoms
#print axioms Rcic.Syn.domViewMs_atoms
#print axioms Rcic.Syn.domViewMajor_atoms
#print axioms Rcic.Syn.domViewField_atoms
#print axioms Rcic.Syn.domViewRetained_atoms
#print axioms Rcic.Syn.s17_decl_budget
#print axioms Rcic.Syn.s17_aw3_below
#print axioms Rcic.Syn.prefixTy
#print axioms Rcic.Syn.recAtN
#print axioms Rcic.Syn.rawMinorTy
#print axioms Rcic.Syn.hL
#print axioms Rcic.Syn.hR
#print axioms Rcic.Syn.H
#print axioms Rcic.Syn.natSuccTable_wf
#print axioms Rcic.Syn.natSucc_croot
#print axioms Rcic.Syn.s17_beta4_tgt
#print axioms Rcic.Syn.hL_eps_el
#print axioms Rcic.Syn.hR_eps_er
#print axioms Rcic.Syn.natSucc_iota_erasure
#print axioms Rcic.Syn.s17_requests_below
#print axioms Rcic.Syn.k1_pair_1
#print axioms Rcic.Syn.k1_pair_2
#print axioms Rcic.Syn.mutant_rejected
