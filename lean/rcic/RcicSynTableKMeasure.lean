import rcic.RcicSynTableK
import rcic.RcicSynTableOfIFull
import rcic.RcicPinEqIotaStarK
import rcic.RcicPinLoopEraseWf
import rcic.RcicPinLoopT
import rcic.RcicKGateNoGo
import rcic.RcicSynBelowScoped
import rcic.RcicSynES
import rcic.RcicSynP2Iota

/-!
# Measuring `AllBelowScoped.es` at the post-`irr` iota cell — the K table
# closes it, the iota table does not

The `iotaStarK` cell `eqIotaK : rec α a M m a (refl α a) ⇒ m` is a
`ConvT.iota` at `eqJoinCtx`. Under the canonical disposition of the
*enriched* context (`eqScope.can id`), `TyP.eps` erases the proof major
`refl α a` to `★` — `const 64`'s telescope ends in literal `Sort 0`, so the
`const` clause of `eps` returns `★` and the `app` clause drops it — and the
erased redex is the retained pre-major spine

    appN (const 65 [param 0]) [bvar 3, bvar 2, bvar 1, bvar 0, bvar 2]

`tableOfI`'s only rule at head 65 is constructor-major and cannot fire on
this spine: its lhs is `EStep`-normal and `bvar 0` is `EStep`-normal, so by
the landed confluence architecture any `ES` would collapse to
`LvlEq lhs rhs`, which the shape mismatch refutes — `¬ES (tableOfI …)`.

`tableOfK`'s nullary bare rule at 65 fires at the spine's head subterm; the
emitted `lamN 5 (bvar 1)` then β-reduces under the five arguments to
`bvar 0 = dr.eps` — `+ES (tableOfK …)`.

So `AllBelowScoped.es` at this scope/cell is *true* for `tableOfK` and
*false* for `tableOfI`: the K table is the additive repair, and the
critical-pair analysis of `RcicSynTableK` §7 records why the gate had to
stay a *replacement* of the ctor-major rule rather than an append.

The Loop fixture's K emission is pinned as a consistency check: the rule
`iotaKRuleOf` emits at the Loop group is definitionally the `loopRule`
shape `λ². m (rec M m)` (at head 62).

`closure_claim = 0`: measurements on the landed fixtures, no new admission.
-/

namespace Rcic.Syn

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Declarative.EqPin

/-! ## §1 the scope, the cell, and the erased endpoints -/

/-- `eqJoinCtx`'s `CtxWfT`, assembled from the kg legs: `α : Sort 1` at
`[]`, `a : α` at `[α]`, `M` at `[a, α]`, `m` at `[M, a, α]`, `p : Eq α a a`
at `[m, M, a, α]`. -/
def eqJoinCtxWf : CtxWfT eqEnvT 1 eqJoinCtx :=
  .assumption _ eqPTy _
    (.assumption _ eqMinorT _
      (.assumption _ eqMotT _
        (.assumption _ (.bvar 0) _
          (.assumption [] _ _ .nil (.sort [] _))
          Rcic.kgATy)
        Rcic.kgMotTy)
      Rcic.kgMinorTy)
    Rcic.kgPTyTy

/-- the admitted Eq scope: env `eqEnvT`, context `eqJoinCtx`, the identity
extension. -/
def eqScope : ScopedCtx eqEnvT eqEnvT 1 eqJoinCtx :=
  ⟨pinEqGroupWfT, envExt_refl _, eqJoinCtxWf⟩

/-- the enriched post-`irr` iota cell `rec α a M m a (refl α a) ⇒ m`. -/
noncomputable def eqH : CvP eqEnvT 1 eqJoinCtx (.app eqRecFive eqReflApp)
    (.bvar 1) eqEqLhs :=
  enrichConvT_of_envWfT pinEqGroupWfT eqJoinCtxWf eqIotaK

/-- the erased pre-major spine's argument list: `α a M m a` all survive
(`α`'s sort is `1`, `m`'s sort is `param 0` — only `p` drops). -/
def eqKSpine : List ETm := [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2]

/-- the erased redex: `rec α a M m a` with the `★` major already dropped. -/
def eqKLhs : ETm := .appN (.const 65 [.param 0]) eqKSpine

/-- PIN: `dl.eps` of the enriched `eqIotaK` is exactly the retained
pre-major spine — the `★`-major rule fires on the actual erased image. -/
theorem eqK_dl_eps : eqH.dl.eps id (eqScope.can id) = eqKLhs := by
  with_unfolding_all rfl

/-- PIN: `dr.eps` is `bvar 0` (the erased `m`). -/
theorem eqK_dr_eps : eqH.dr.eps id (eqScope.can id) = .bvar 0 := by
  with_unfolding_all rfl

/-! ## §2 the K rule at the Eq group and the positive `ES` -/

/-- `iotaKGate` fires on the Eq group: singleton `Prop` family, large
elimination, the unique ctor `refl` has two params and no fields. -/
theorem eqKGate_true : iotaKGate 63 eqFamT eqReflT eqRecT = true := by
  decide

/-- the K rule emitted for the Eq group, at the actual emitted arity. -/
theorem eqKRule_emit :
    iotaKRuleOf 63 eqFamT [(64, eqReflT)] 65 eqRecT =
      some (iotaKRule 65 5 2 1 0) := by
  show (if iotaKGate 63 eqFamT eqReflT eqRecT = true then
      some (iotaKRule 65 (iotaKNargs eqFamT eqRecT) (iotaKNparams eqFamT eqRecT)
        (iotaNindices eqRecT) (iotaKNfields eqFamT eqReflT eqRecT)) else none) =
    some (iotaKRule 65 5 2 1 0)
  rw [if_pos eqKGate_true]
  have h1 : iotaKNargs eqFamT eqRecT = 5 := rfl
  have h2 : iotaKNparams eqFamT eqRecT = 2 := rfl
  have h3 : iotaNindices eqRecT = 1 := rfl
  have h4 : iotaKNfields eqFamT eqReflT eqRecT = 0 := rfl
  rw [h1, h2, h3, h4]

/-- the emitted K rule is a member of `tableOfK pinEqGroupWfT`. -/
theorem eqKRule_mem : iotaKRule 65 5 2 1 0 ∈ tableOfK pinEqGroupWfT := by
  obtain ⟨tl, htl⟩ : ∃ tl, tableOfK pinEqGroupWfT =
      iotaRulesKOf 63 eqFamT [(64, eqReflT)] 65 eqRecT ++ tl :=
    ⟨_, by with_unfolding_all rfl⟩
  rw [htl]
  apply List.mem_append_left
  unfold iotaRulesKOf
  rw [eqKRule_emit]
  exact List.mem_singleton.mpr rfl

/-- the erased-step chain: bare K rule at the spine head, then five β. -/
theorem eqK_chain : RStar (RStep (tableOfK pinEqGroupWfT)) eqKLhs (.bvar 0) :=
  .step (rStep_appN_head
      (.cr (.bare eqKRule_mem rfl [.param 0] [] rfl)) eqKSpine)
    (.step (rStep_appN_head
        (.beta (lamN 4 (.bvar 1)) (.bvar 3)) [.bvar 2, .bvar 1, .bvar 0, .bvar 2])
      (.step (rStep_appN_head
          (.beta (lamN 3 (.bvar 1)) (.bvar 2)) [.bvar 1, .bvar 0, .bvar 2])
        (.step (rStep_appN_head
            (.beta (lamN 2 (.bvar 1)) (.bvar 1)) [.bvar 0, .bvar 2])
          (.step (rStep_appN_head
              (.beta (lamN 1 (.bvar 1)) (.bvar 0)) [.bvar 2])
            (.step (.beta (.bvar 1) (.bvar 2)) (.refl _))))))

/-- **positive half.** `AllBelowScoped.es`'s `ES` obligation at this cell
holds under `tableOfK`. -/
theorem eqK_es : ES (tableOfK pinEqGroupWfT) id (eqScope.can id) eqH := by
  unfold ES
  rw [eqK_dl_eps, eqK_dr_eps]
  exact convMod_of_rstar_estep eqK_chain

/-! ## §3 the `tableOfI` refutation -/

/-- every `tableOfI` rule at head 65 is constructor-major: `head_major`
returns either a `.definitionM` δ rule or a `.recursorM` iota rule, and
member 65 is `eqRecT`, a recursor — so the rule is the ctor-major one. -/
theorem tableOfI_eq65_major {ρ : CRule} (hρ : ρ ∈ tableOfI pinEqGroupWfT)
    (hh : ρ.head = 65) : ∃ d m, ρ.major = some (d, m) := by
  rcases tableOfI_head_major pinEqGroupWfT ρ hρ with ⟨m, hm, hmc, _⟩ |
    ⟨_, hm, _, d, k, _, hmaj, _, _⟩
  · rw [hh] at hm
    have hmem : eqEnvT.members 65 = some eqRecT := rfl
    rw [hmem] at hm
    cases hm
    exact absurd hmc (by decide)
  · exact ⟨d, k, hmaj⟩

/-- `const 65 ls` is `EStep`-normal on `tableOfI`: `bare` needs a
`major = none` rule at 65 (none exists), `ctor` needs at least one
argument, and every congruence/shape constructor is dead. -/
theorem eqTableOfI_const65_normal {ls : List Level} {z : ETm}
    (h : EStep (tableOfI pinEqGroupWfT) (.const 65 ls) z) : False := by
  have hsh : ∀ (n : Nat) (l : List Level),
      ETm.spineHead (.const n l) = .const n l := fun _ _ => rfl
  have hsa : ∀ (n : Nat) (l : List Level),
      ETm.spineArgs (.const n l) = [] := fun _ _ => rfl
  rcases h with h | h
  · generalize hs : (ETm.const 65 ls : ETm) = s at h
    cases h with
    | cr hc =>
        cases hc with
        | bare hρ hm ls' args hn =>
            have hsp := congrArg ETm.spineHead hs
            rw [ETm.spineHead_appN] at hsp
            simp only [hsh] at hsp
            injection hsp with h65 _
            obtain ⟨_, _, hmaj⟩ := tableOfI_eq65_major hρ h65.symm
            exact absurd (hmaj.symm.trans hm) (by simp)
        | ctor hρ hm ls' ls'' args bs hn hb =>
            have hsp := congrArg ETm.spineArgs hs
            rw [ETm.spineArgs_appN] at hsp
            simp only [hsa] at hsp
            rw [List.nil_append] at hsp
            exact absurd (List.append_eq_nil.mp hsp.symm).2
              (List.cons_ne_nil _ _)
    | _ => cases hs
  · generalize hs : (ETm.const 65 ls : ETm) = s at h
    cases h <;> cases hs

/-- `EStep`-normality of an `app f x` where `f` is `EStep`-normal with head
`const 65 [param 0]` and `x` is a `bvar`. -/
theorem eqTableOfI_app_normal {f x : ETm}
    (hfh : ETm.spineHead f = .const 65 [.param 0])
    (hfn : ∀ z, ¬ EStep (tableOfI pinEqGroupWfT) f z)
    (hxi : ∃ i, x = .bvar i) {z : ETm}
    (h : EStep (tableOfI pinEqGroupWfT) (.app f x) z) : False := by
  have hsh : ∀ (n : Nat) (l : List Level),
      ETm.spineHead (.const n l) = .const n l := fun _ _ => rfl
  have hsa : ∀ (n : Nat) (l : List Level),
      ETm.spineArgs (.const n l) = [] := fun _ _ => rfl
  have hsb : ∀ i : Nat, ETm.spineHead (.bvar i) = .bvar i := fun _ => rfl
  rcases h with h | h
  · generalize hs : (ETm.app f x : ETm) = s at h
    cases h with
    | beta M N =>
        cases hs
        cases hfh
    | cr hc =>
        cases hc with
        | bare hρ hm ls' args hn =>
            have hsp := congrArg ETm.spineHead hs
            have h₁ : ETm.spineHead (.app f x) = ETm.spineHead f := rfl
            rw [ETm.spineHead_appN, h₁, hfh] at hsp
            simp only [hsh] at hsp
            injection hsp with h65 _
            obtain ⟨_, _, hmaj⟩ := tableOfI_eq65_major hρ h65.symm
            exact absurd (hmaj.symm.trans hm) (by simp)
        | ctor hρ hm ls' ls'' args bs hn hb =>
            have hsp := congrArg ETm.spineArgs hs
            have h₁ : ETm.spineArgs (.app f x) = ETm.spineArgs f ++ [x] := rfl
            rw [ETm.spineArgs_appN, h₁] at hsp
            simp only [hsa] at hsp
            rw [List.nil_append] at hsp
            have hg := congrArg List.getLast? hsp
            have key : ∀ (ys : List ETm) (a : ETm),
                (ys ++ [a]).getLast? = some a := by
              intro ys a
              induction ys with
              | nil => rfl
              | cons y ys ih =>
                  cases ys with
                  | nil => rfl
                  | cons z zs => exact ih
            rw [key, key] at hg
            have hk : x = _ := Option.some.inj hg
            obtain ⟨i, rfl⟩ := hxi
            have hsp := congrArg ETm.spineHead hk
            rw [ETm.spineHead_appN, hsb, hsh] at hsp
            exact ETm.noConfusion hsp
    | appL a' h'' =>
        cases hs
        exact hfn _ (.inl h'')
    | appR f' h'' =>
        cases hs
        obtain ⟨i, rfl⟩ := hxi
        exact rStep_bvar_normal _ _ _ h''
    | _ => cases hs
  · generalize hs : (ETm.app f x : ETm) = s at h
    cases h with
    | appL a' h'' =>
        cases hs
        exact hfn _ (.inr h'')
    | appR f' h'' =>
        cases hs
        obtain ⟨i, rfl⟩ := hxi
        exact etaStep_bvar_normal _ _ h''
    | _ => cases hs

/-- `EStep`-normality of a `const 65 [param 0]`-headed spine over
`bvar` arguments, on `tableOfI`. -/
theorem eqTableOfI_appN_normal : ∀ {f : ETm} {xs : List ETm},
    ETm.spineHead f = .const 65 [.param 0] →
    (∀ z, ¬ EStep (tableOfI pinEqGroupWfT) f z) →
    (∀ y ∈ xs, ∃ i, y = .bvar i) → ∀ z,
    ¬ EStep (tableOfI pinEqGroupWfT) (f.appN xs) z := by
  intro f xs
  induction xs generalizing f with
  | nil => intro hfh hfn _ z h; exact hfn z h
  | cons x xs ih =>
      intro hfh hfn hx z h
      refine ih (f := .app f x) hfh ?_
        (fun y hy => hx y (List.mem_cons_of_mem _ hy)) z h
      intro z' h'
      exact eqTableOfI_app_normal hfh hfn (hx x (List.mem_cons_self _ _)) h'

/-- the erased `eqIotaK` lhs is `EStep`-normal on `tableOfI`. -/
theorem eqTableOfI_lhs_normal (z : ETm)
    (h : EStep (tableOfI pinEqGroupWfT) eqKLhs z) : False :=
  eqTableOfI_appN_normal (f := .const 65 [.param 0]) rfl
    (fun z' h' => eqTableOfI_const65_normal h')
    (by
      intro x hx
      simp only [eqKSpine, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩)
    z h

/-- **negative half.** `AllBelowScoped.es`'s `ES` obligation at this cell
fails under `tableOfI`: both erased endpoints are `EStep`-normal and
`LvlEq`-distinct, so confluence leaves no join. -/
theorem eq_not_es_tableOfI :
    ¬ ES (tableOfI pinEqGroupWfT) id (eqScope.can id) eqH := by
  intro h
  unfold ES at h
  rw [eqK_dl_eps, eqK_dr_eps] at h
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence
      (eStep_strongSim (tableWF_tableOfI_full pinEqGroupWfT).congr)
      (confluent_eStep_wf (tableWF_tableOfI_full pinEqGroupWfT)) h
  obtain rfl := rstar_of_normal eqTableOfI_lhs_normal hc
  obtain rfl := rstar_of_normal (fun z hz => eStep_bvar_normal _ 0 z hz) hd
  have hsymm := lvlEq_equivalence.symm hq
  have heq := lvlEq_bvar_inv hsymm
  have hlit : eqKLhs = .app (.app (.app (.app (.app (.const 65 [.param 0])
      (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2) := rfl
  rw [hlit] at heq
  exact ETm.noConfusion heq

/-! ## §4 the demand and the Loop consistency pin -/

/-- the enriched `eqIotaK` satisfies the assumption-prefix gate — every
stored `TyP` is a native `enrichHasTyT_of_envWfT` image. -/
theorem eqH_assumpPref : eqH.AssumpPref :=
  ⟨NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      pinEqGroupWfT eqJoinCtxWf _,
    NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      pinEqGroupWfT eqJoinCtxWf _,
    NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      pinEqGroupWfT eqJoinCtxWf _,
    NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      pinEqGroupWfT eqJoinCtxWf _⟩

/-- the cell is a demanded public `es` root at the admitted Eq scope. -/
theorem eqK_demand : Demand (.es eqH eqScope id (eqScope.can id)) :=
  .rootEs eqH eqH_assumpPref eqScope id levelHom_id

/-- `iotaKGate` fires on the Loop group too: `Loop`'s telescope ends in
`Sort 0`, the recursor is large-eliminating, `mk`'s single field is a
recursive family app with no indices — and `nindices = 0` makes the erased
recursive call safe. -/
theorem loopKGate_true :
    iotaKGate 60 pinLoopFamT pinLoopMkT pinLoopRecT = true := by
  decide

/-- the Loop K emission: `nargs = 2`, `nparams = 0`, `nindices = 0`,
`nfields = 1` — the emitted rule is `λ². bvar 0 (const 62 ls (bvar 1)
(bvar 0))`, i.e. `loopRule`'s `λ M m. m (rec M m)` at head 62. -/
theorem loopKRule_emit :
    iotaKRuleOf 60 pinLoopFamT [(61, pinLoopMkT)] 62 pinLoopRecT =
      some (iotaKRule 62 2 0 0 1) := by
  show (if iotaKGate 60 pinLoopFamT pinLoopMkT pinLoopRecT = true then
      some (iotaKRule 62 (iotaKNargs pinLoopFamT pinLoopRecT)
        (iotaKNparams pinLoopFamT pinLoopRecT) (iotaNindices pinLoopRecT)
        (iotaKNfields pinLoopFamT pinLoopMkT pinLoopRecT)) else none) =
    some (iotaKRule 62 2 0 0 1)
  rw [if_pos loopKGate_true]
  have h1 : iotaKNargs pinLoopFamT pinLoopRecT = 2 := rfl
  have h2 : iotaKNparams pinLoopFamT pinLoopRecT = 0 := rfl
  have h3 : iotaNindices pinLoopRecT = 0 := rfl
  have h4 : iotaKNfields pinLoopFamT pinLoopMkT pinLoopRecT = 1 := rfl
  rw [h1, h2, h3, h4]

/-- PIN: the emitted Loop rule's rhs is literally `loopRule`'s rhs shape
(`λ². m (rec M m)`) — the additive K table reproduces the hand-pinned
rule through the general gate. -/
theorem loopKRule_rhs : (iotaKRule 62 2 0 0 1).rhs [.succ .zero] [] =
    .lam (.lam (.app (.bvar 0)
      (.app (.app (.const 62 [.succ .zero]) (.bvar 1)) (.bvar 0)))) := rfl

end Rcic.Syn
