import rcic.RcicNativePiModelIrr
import rcic.RcicHostPropTransfer
import rcic.RcicAnnAlg

/-!
# RcicNativePiModelK — K and η-K in the ideal model, on top of the proof-irrelevance layer

Continues `RcicNativePiModelIrr` (#7633) over devin-fcd's ideal model (#7628) and answers the
type-level part of the irr interface #7631 asked for.  `closure_claim = 0`.

* **Type level (#7631 item 1).**  `irrLink_false`: under zero-sort coherence a proposition never
  converts to a sort, so `ConvT.irr` is never a type-level link of the logical relation.
* **K = irr on the major, then ι** (`pEqI_K`): the native K step `rec M m h ↝ m` (for `h` a proof
  of a K-eligible proposition) is projected-sound as the composite of `irr` at the proposition
  (`pEqI_irr`), stability of the eliminator in its major (`MajorStable`) and ι at the canonical
  proof (`IotaSoundAt`).
* **η-K = η, irr under λ, ι — REDUCED, not claimed sound** (`pEqI_etaK_of_eta_dom_iota`): of the
  native certificate `f ≡ λp. f p ≡ λp. f r ≡ λp. x` (#7609), the irr-under-λ link is DERIVED from
  #7633's stability under application at every finite demand (`lamIrrAt_of_domTyped`, given the
  dom condition), the ι link from the ι clause by λ-congruence (`lamIotaAt_of_iotaClause`).  What
  stays open is exactly η (`EtaSoundAt`, refuted at `⊥` below) and the ι clause
  (`IotaClauseUnder`, O3).
* **(O4) η is not sound for fcd7's model, even projected, at the degenerate environment**
  (`eta_unsound_bot`): at `f : Sort 0 → Sort 0` the η-expansion denotes the compact
  `lam [([], ⊥)]`, typed at the non-proposition code `pi ⊥ [([], sort)]` of the type, which the
  variable `f` (`{⊥}` at `⊥`) does not denote; the native `ConvT.eta` derivation exists
  (`etaCtx_conv`).  So the η case of `FundamentalLRI` — and with it η-K — needs the paper's
  information order (coalescing `λ(⊥) = ⊥`, downward-closed ideals), which fcd7's set-of-compacts
  model does not have.  ι needs recursor semantics (O3 of #7633).  Hence K and η-K are reduced to
  exactly these named model obligations; nothing here asserts them.

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelKAudit

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit

/-! ### type level: `irr` is never a type-level link (#7631 item 1) -/

/-- Under zero-sort coherence a proposition never converts to a sort; so a `ConvT.irr` at a
    proposition `P` is never a link of `TyConvT`. -/
theorem irrLink_false {E : ResolvedEnv} {n : Nat}
    (zsc : Rcic.Declarative.HostProp.ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P p q : Expr Nat} {u : Level}
    (_hc : ConvT E n Γ p q P) (hP : HasTyT E n Γ P (.sort .zero))
    (hT : TyConvT E n Γ P (.sort u)) : False := by
  obtain ⟨hs⟩ := Rcic.Declarative.HostProp.sort_transport0 zsc hW hΓ hT hP
  exact Rcic.Declarative.Ann.not_eqN_succ_zero u (zsc hW hΓ (HasTyT.sort Γ u) hs)

/-! ### K = irr on the major, then ι -/

/-- The eliminator `R` (recursor applied to motive and minor) is stable in its major at `P`. -/
def MajorStable (E : ResolvedEnv) (ρ : EnvI) (P T R : Expr Nat) : Prop :=
  ∀ x y, PEqI E ρ P x y → PEqI E ρ T (.app R x) (.app R y)

/-- ι at the canonical proof `c` returns the minor `m`. -/
def IotaSoundAt (E : ResolvedEnv) (ρ : EnvI) (T R c m : Expr Nat) : Prop :=
  PEqI E ρ T (.app R c) m

/-- **K**: for any proof `h` of the proposition `P`, `R h ≡ m`. -/
theorem pEqI_K {E : ResolvedEnv} {ρ : EnvI} {P T R c m : Expr Nat}
    (hP : IsPropIdealI E (denI ρ P)) (hs : MajorStable E ρ P T R) (hι : IotaSoundAt E ρ T R c m)
    (h : Expr Nat) : PEqI E ρ T (.app R h) m :=
  pEqI_k_of_irr_iota hP hs hι

/-- K with stability from the dom condition (`pEqI_app_stable`): only ι remains. -/
theorem pEqI_K_of_domTyped {E : ResolvedEnv} {ρ : EnvI} {P T R c m : Expr Nat}
    (hP : IsPropIdealI E (denI ρ P)) (hdom : DomTyped E (denI ρ P) (denI ρ R))
    (hns : NoSpine (denI ρ R)) (hι : IotaSoundAt E ρ T R c m) (h : Expr Nat) :
    PEqI E ρ T (.app R h) m :=
  pEqI_k_of_iota hP hdom hns hι

/-! ### η-K = η, irr under λ, ι -/

/-- η at `f`: the η-expansion is projected-equal to `f` at the Π-type `Π A B`. -/
def EtaSoundAt (E : ResolvedEnv) (ρ : EnvI) (A B f : Expr Nat) : Prop :=
  PEqI E ρ (.pi A B) (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- irr under the binder: replacing the bound proof by the canonical proof `r` in the body. -/
def LamIrrAt (E : ResolvedEnv) (ρ : EnvI) (A B f r : Expr Nat) : Prop :=
  PEqI E ρ (.pi A B) (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A (.app (lift 0 1 f) (lift 0 1 r)))

/-- ι under the binder: the body at the canonical proof computes to `x`. -/
def LamIotaAt (E : ResolvedEnv) (ρ : EnvI) (A B f r x : Expr Nat) : Prop :=
  PEqI E ρ (.pi A B) (.lam A (.app (lift 0 1 f) (lift 0 1 r))) (.lam A (lift 0 1 x))

/-- λ-congruence of untyped semantic equality: equal bodies at every finite demand. -/
theorem semEqI_lam_congrK {ρ : EnvI} {A A' b b' : Expr Nat}
    (hb : ∀ us, SemEqI (EnvI.cons (demand us) ρ) b b') : SemEqI ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | lam hf => exact .lam (fun s hs => (hb s.1 s.2).mp (hf s hs))
  · intro h
    cases h with
    | bot => exact .bot _ _
    | lam hf => exact .lam (fun s hs => (hb s.1 s.2).mpr (hf s hs))

/-- **`LamIrrAt` DERIVED** from #7633's stability under application (`semEqI_app_stable`),
    applied under the binder at every finite demand: if the (lifted) domain is a proposition
    ideal and `⟦lift f⟧` satisfies the dom condition and has no spines there, the body does not
    see which proof it is given, so replacing the bound proof by `r` is sound. -/
theorem lamIrrAt_of_domTyped {E : ResolvedEnv} {ρ : EnvI} {A B f r : Expr Nat}
    (hA : ∀ us, IsPropIdealI E (denI (EnvI.cons (demand us) ρ) (lift 0 1 A)))
    (hdom : ∀ us, DomTyped E (denI (EnvI.cons (demand us) ρ) (lift 0 1 A))
      (denI (EnvI.cons (demand us) ρ) (lift 0 1 f)))
    (hns : ∀ us, NoSpine (denI (EnvI.cons (demand us) ρ) (lift 0 1 f))) :
    LamIrrAt E ρ A B f r :=
  pEqI_of_semEqI (semEqI_lam_congrK (fun us =>
    semEqI_app_stable (hA us) (hdom us) (hns us) (.bvar 0) (lift 0 1 r)))

/-- **The ι clause under the binder — the OPEN remainder** (O3: recursors are opaque spines in
    `ApproxI`; the δ/ι semantics is `agy-pimodel`'s): at every finite demand, the eliminator at
    the canonical proof and its contractum have the same approximations. -/
def IotaClauseUnder (ρ : EnvI) (f r x : Expr Nat) : Prop :=
  ∀ us, SemEqI (EnvI.cons (demand us) ρ) (.app (lift 0 1 f) (lift 0 1 r)) (lift 0 1 x)

/-- `LamIotaAt` from the ι clause, by λ-congruence. -/
theorem lamIotaAt_of_iotaClause {E : ResolvedEnv} {ρ : EnvI} {A B f r x : Expr Nat}
    (h : IotaClauseUnder ρ f r x) : LamIotaAt E ρ A B f r x :=
  pEqI_of_semEqI (semEqI_lam_congrK h)

/-- **η-K reduced** (no soundness claim): `f ≡ λp. x` at `Π A B` follows from η (`EtaSoundAt`, an
    open remainder, REFUTED at `⊥` for fcd7's model by `eta_unsound_bot`), the dom condition under
    the binder (#7633 O2; irr then follows by `lamIrrAt_of_domTyped`), and the ι clause
    (`IotaClauseUnder`, open remainder O3). -/
theorem pEqI_etaK_of_eta_dom_iota {E : ResolvedEnv} {ρ : EnvI} {A B f r x : Expr Nat}
    (hη : EtaSoundAt E ρ A B f)
    (hA : ∀ us, IsPropIdealI E (denI (EnvI.cons (demand us) ρ) (lift 0 1 A)))
    (hdom : ∀ us, DomTyped E (denI (EnvI.cons (demand us) ρ) (lift 0 1 A))
      (denI (EnvI.cons (demand us) ρ) (lift 0 1 f)))
    (hns : ∀ us, NoSpine (denI (EnvI.cons (demand us) ρ) (lift 0 1 f)))
    (hι : IotaClauseUnder ρ f r x) :
    PEqI E ρ (.pi A B) f (.lam A (lift 0 1 x)) :=
  hη.symm.trans ((lamIrrAt_of_domTyped (B := B) (r := r) hA hdom hns).trans
    (lamIotaAt_of_iotaClause hι))

/-! ### (O4) η is not sound for fcd7's model at the degenerate environment -/

/-- The context `f : Sort 0 → Sort 0`. -/
def etaCtx : LCtx := [.assumption (.pi (.sort .zero) (.sort .zero))]

/-- The native η instance at `etaCtx`. -/
def etaCtx_conv (E : ResolvedEnv) (n : Nat) :
    ConvT E n etaCtx (.lam (.sort .zero) (.app (lift 0 1 (.bvar 0)) (.bvar 0))) (.bvar 0)
      (.pi (.sort .zero) (.sort .zero)) :=
  ConvT.eta etaCtx (.bvar 0) (.sort .zero) (.sort .zero) (HasTyT.bvar etaCtx 0 _ rfl)

/-- The code `pi ⊥ [([], sort)]` is not a proposition code. -/
theorem not_isPropC_pi_sortCod (E : ResolvedEnv) : ¬ IsPropC E (.pi .bot [([], .sort)]) := by
  intro h
  cases h with
  | pi hf =>
      have := hf ([], .sort) (List.mem_singleton.mpr rfl)
      cases this

/-- **(O4)**: η is not projected-sound at `EnvI.bot`. -/
theorem eta_unsound_bot (E : ResolvedEnv) :
    ¬ EtaSoundAt E EnvI.bot (.sort .zero) (.sort .zero) (.bvar 0) := by
  intro h
  have hcode : denI EnvI.bot (.pi (.sort .zero) (.sort .zero)) (.pi .bot [([], .sort)]) :=
    .pi (.bot _ _) (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact .sort _ _)
  have hty : CTy E (.lam [([], .bot)]) (.pi .bot [([], .sort)]) :=
    .lam (not_isPropC_pi_sortCod E)
      (fun s hs u hu => by
        simp only [List.mem_singleton] at hs; subst hs; exact nomatch hu)
      (fun s hs _ _ _ => by
        simp only [List.mem_singleton] at hs; subst hs; exact .bot _)
  have hl : denI EnvI.bot (.lam (.sort .zero) (.app (lift 0 1 (.bvar 0)) (.bvar 0)))
      (.lam [([], .bot)]) :=
    .lam (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact .bot _ _)
  obtain ⟨hr, _⟩ := (h (.lam [([], .bot)])).mp ⟨hl, _, hcode, hty⟩
  rcases approxI_bvar_iff.mp hr with h0 | h0
  · exact nomatch h0
  · exact nomatch (h0 : CptI.lam [([], .bot)] = .bot)

#print axioms irrLink_false
#print axioms MajorStable
#print axioms IotaSoundAt
#print axioms pEqI_K
#print axioms pEqI_K_of_domTyped
#print axioms EtaSoundAt
#print axioms LamIrrAt
#print axioms LamIotaAt
#print axioms semEqI_lam_congrK
#print axioms lamIrrAt_of_domTyped
#print axioms IotaClauseUnder
#print axioms lamIotaAt_of_iotaClause
#print axioms pEqI_etaK_of_eta_dom_iota
#print axioms etaCtx
#print axioms etaCtx_conv
#print axioms not_isPropC_pi_sortCod
#print axioms eta_unsound_bot

end Rcic.Declarative.NativeValleys.PiModelKAudit
