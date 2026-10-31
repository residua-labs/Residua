import rcic.RcicAnnIotaSR
import rcic.RcicTypedEnv
import rcic.RcicUntypedConvCollapse

/-!
# M3-e-1 — the environment bridge, without inductive groups

The rows hold on the typed judgment over `eraseEnv E` for every annotated environment `E` the copy
admits (`AnnEnvA`, M3-c/M3-d). This module starts the bridge from R-CIC's typed environment judgment
(`EnvWfT`, `RcicTypedEnv`). Every environment it admits with no inductive group is the erasure of one
the copy admits (`annEnvA_of_envWfT`), so the rows hold over it (`sortConvCharT_envT`,
`piConvInjT_envT`).

* ι INTERFACES (§1–§2). `EnvWfA I` fixes one ι interface for a whole derivation, so an extension step
  needs the prefix's typings at the extension's ι. The ι rule is the only rule that reads the interface,
  at a typed redex, and the head step reads it only at applications. So derivations move between
  interfaces that agree on the environment's terms (`hasTyIfaceA`). The concrete ι reads only members
  that the redex and its recursor's type name, so it agrees between an admitted environment and any
  extension (`iotaFnA_prefix`).
* LEVELS (§3). A bodyless axiom retains its declared universe parameters; bodyful singleton members
  have arity `0`. Annotation may introduce additional binder-level parameters. The closing list
  `closeLs` preserves the declared prefix and instantiates only additional parameters to `zero`,
  leaving the erasure of the stored member type unchanged.
* THE BRIDGE (§5), by induction on `EnvWfT`, at every interface that agrees with the annotation's own.
  Each singleton is annotated by M3-c's annotation in the copy built so far, its levels are closed, and
  its typings are moved to the extension's interface. A group cannot occur.
* WHY NOT `EnvWf` (§6). `main`'s untyped `EnvWf` admits `def bad : Prop := Type` (`envWf_badDef`), and no
  admitted annotation erases to it (`badDef_not_admitted`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) ι interfaces that agree on an environment's terms -/

section Iface
variable {E : ResolvedEnvA} {n : Nat}

/-- two ι interfaces AGREE ON `E` when their functions agree on every term naming only members of
    `E`. The ι rule is the only rule that reads the interface, and it reads it at a typed redex,
    whose constants are members (`hasTyA_constsIn`). -/
def IfaceAgreeA (E : ResolvedEnvA) (I J : IotaIfaceA) : Prop :=
  ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e

theorem IfaceAgreeA.refl (E : ResolvedEnvA) (I : IotaIfaceA) : IfaceAgreeA E I I := fun _ _ => rfl

theorem IfaceAgreeA.symm {I J : IotaIfaceA} (h : IfaceAgreeA E I J) : IfaceAgreeA E J I :=
  fun e he => (h e he).symm

theorem IfaceAgreeA.trans {I J K : IotaIfaceA} (h₁ : IfaceAgreeA E I J) (h₂ : IfaceAgreeA E J K) :
    IfaceAgreeA E I K := fun e he => (h₁ e he).trans (h₂ e he)

/-- agreement on an environment restricts to a sub-environment. -/
theorem IfaceAgreeA.prefix {E₀ : ResolvedEnvA} (hpre : PrefixA E₀ E) {I J : IotaIfaceA}
    (h : IfaceAgreeA E I J) : IfaceAgreeA E₀ I J :=
  fun e he => h e (constsInA_mono (fun r ⟨m, hm⟩ => ⟨m, hpre r m hm⟩) e he)

theorem hStepFnA_app_congr_fn (I J : IotaFnA) (Γ : LCtxA) {f : ExprA} (x : ExprA)
    (hnl : ∀ A u b, f ≠ .lam A u b) (h : hStepFnA E I Γ f = hStepFnA E J Γ f)
    (hfx : I (.app f x) = J (.app f x)) (hx : hStepFnA E I Γ x = hStepFnA E J Γ x) :
    hStepFnA E I Γ (.app f x) = hStepFnA E J Γ (.app f x) := by
  rw [hStepFnA_app_nonlam E I Γ x hnl, hStepFnA_app_nonlam E J Γ x hnl, h, hfx, hx]

/-- the head step reads its ι function only at applications, so two functions that agree on `E`'s
    terms give one head step on them. -/
theorem hStepFnA_iface {I J : IotaFnA} (hag : ∀ e, ConstsInA (domA E) e → I e = J e) (Γ : LCtxA) :
    (e : ExprA) → ConstsInA (domA E) e → hStepFnA E I Γ e = hStepFnA E J Γ e
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .const _ _, _ => rfl
  | .app (.lam _ _ _) _, _ => rfl
  | .app (.bvar i) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.bvar i) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.sort l) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.sort l) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.const r ls) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.const r ls) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.app g y) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.app g y) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.pi a u b v) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.pi a u b v) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.letE a w b) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.letE a w b) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)
  | .app (.lit t) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface hag Γ (.lit t) h.1) (hag _ h) (hStepFnA_iface hag Γ x h.2)

theorem iotaRel_iface {I J : IotaIfaceA} (hag : IfaceAgreeA E I J) {Γ : LCtxA} {e e' : ExprA}
    (hc : ConstsInA (domA E) e) (h : I.rel E Γ e e') : J.rel E Γ e e' :=
  ⟨(hag e hc) ▸ h.1, by rw [← hStepFnA_iface (I := I.fn) (J := J.fn) hag Γ e hc]; exact h.2⟩

/-- `hStepFnA_iface` with the constants-domain factored out: the head step's ι reads are at
    subterms of `e`, so agreement on `e`'s constants suffices whatever the environment's domain
    is (R-NoDeltaRec-4d-ii — the extended environment's interface differs on the new constant,
    which `E`-dom terms never name). -/
theorem hStepFnA_iface_dom {I J : IotaFnA} (D : Nat → Prop) {E : ResolvedEnvA}
    (hag : ∀ e, ConstsInA D e → I e = J e) (Γ : LCtxA) :
    (e : ExprA) → ConstsInA D e → hStepFnA E I Γ e = hStepFnA E J Γ e
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .const _ _, _ => rfl
  | .app (.lam _ _ _) _, _ => rfl
  | .app (.bvar i) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.bvar i) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.sort l) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.sort l) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.const r ls) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.const r ls) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.app g y) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.app g y) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.pi a u b v) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.pi a u b v) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.letE a w b) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.letE a w b) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)
  | .app (.lit t) x, h =>
      hStepFnA_app_congr_fn I J Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_iface_dom D hag Γ (.lit t) h.1) (hag _ h) (hStepFnA_iface_dom D hag Γ x h.2)

/-- `iotaRel_iface` with the domain factored out (R-NoDeltaRec-4d-ii): a rel-step on a term
    whose constants lie in `D` transports when the interfaces agree there. -/
theorem iotaRel_iface_dom {I J : IotaIfaceA} (D : Nat → Prop) {E : ResolvedEnvA}
    (hag : ∀ e, ConstsInA D e → I.fn e = J.fn e) {Γ : LCtxA} {e e' : ExprA}
    (hc : ConstsInA D e) (h : I.rel E Γ e e') : J.rel E Γ e e' :=
  ⟨(hag e hc) ▸ h.1, by rw [← hStepFnA_iface_dom D hag Γ e hc]; exact h.2⟩

variable {I J : IotaIfaceA}

mutual

/-- derivations move between two interfaces that agree on the environment's terms. -/
def hasTyIfaceA (hag : IfaceAgreeA E I J) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → HasTyA E J n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A u h hA => .bvar Γ i A u h (hasTyIfaceA hag hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      .const Γ r ls m u hres hlen hwf (hasTyIfaceA hag hT)
  | _, _, _, .pi Γ A u B v hA hB => .pi Γ A u B v (hasTyIfaceA hag hA) (hasTyIfaceA hag hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam Γ A u body B v (hasTyIfaceA hag hA) (hasTyIfaceA hag hB) (hasTyIfaceA hag hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      .app Γ f a A B u v w (hasTyIfaceA hag hB) (hasTyIfaceA hag hTy) (hasTyIfaceA hag hf)
        (hasTyIfaceA hag ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      .letE Γ A u w value B body (hasTyIfaceA hag hA) (hasTyIfaceA hag hv) (hasTyIfaceA hag hTy)
        (hasTyIfaceA hag hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyIfaceA hag hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv Γ e A B l u (hasTyIfaceA hag h) (hasTyIfaceA hag hAl) hlu (hasTyIfaceA hag hB)
        (convIfaceA hag hc)

def convIfaceA (hag : IfaceAgreeA E I J) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A → ConvA E J n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (hasTyIfaceA hag h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (convIfaceA hag h)
  | _, _, _, _, .trans Γ a b c A h1 h2 => .trans Γ a b c A (convIfaceA hag h1) (convIfaceA hag h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (hasTyIfaceA hag hA) (hasTyIfaceA hag hbody) (hasTyIfaceA hag harg)
        (hasTyIfaceA hag hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (hasTyIfaceA hag hA) (hasTyIfaceA hag hv) (hasTyIfaceA hag hb)
        (hasTyIfaceA hag hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv => .zetaLocal Γ i A v hval hty (hasTyIfaceA hag hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b hres hbody htr hlen hwf (hasTyIfaceA hag hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T (iotaRel_iface hag (hasTyA_constsIn hlhs) h) (hasTyIfaceA hag hlhs)
        (hasTyIfaceA hag hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota Γ f a rhs e T hrec hs ((hag _ (hasTyA_constsIn hlhs)).symm.trans h)
        (hasTyIfaceA hag hlhs) (hasTyIfaceA hag hrhs) (convIfaceA hag hcv)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyIfaceA hag hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      .app Γ f g a b A B u v (convIfaceA hag h1) (convIfaceA hag h2) (hasTyIfaceA hag hB)
        (hasTyIfaceA hag hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      .lam Γ A A' b b' B u u' v hu (convIfaceA hag hA) (convIfaceA hag hb) (hasTyIfaceA hag hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi Γ A A' B B' u u' v v' hu hv (convIfaceA hag hA) (convIfaceA hag hB)
        (hasTyIfaceA hag hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      .letE Γ A A' v v' b b' B u (convIfaceA hag hA) (convIfaceA hag hv) (convIfaceA hag hb)
        (hasTyIfaceA hag hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      .consts Γ r ls ls' m hres hlen hwf hwf' h (hasTyIfaceA hag hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt => .eta Γ f A B u v (hasTyIfaceA hag h) (hasTyIfaceA hag hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyIfaceA hag hP) (hasTyIfaceA hag hp) (hasTyIfaceA hag hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv Γ a b A A' l l' u (convIfaceA hag h) (hasTyIfaceA hag hAl) hlu (hasTyIfaceA hag hA'l)
        hl'u (convIfaceA hag hA)

end

/-- a declarative ι step transports through an environment extension and an interface
    strengthening together, when the redex's constants are all in the base environment: the fn
    read agrees by `hag`, the head step by `hStepFnA_prefix` then `hStepFnA_iface_dom`
    (R-NoDeltaRec-4d-ii). -/
theorem iotaRel_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) {Γ : LCtxA} {e e' : ExprA}
    (hc : ConstsInA (domA E) e) (h : I.rel E Γ e e') : J.rel E' Γ e e' :=
  ⟨hag e hc ▸ h.1, by
    rw [← hStepFnA_iface_dom (domA E) hag Γ e hc, ← hStepFnA_prefix hpre I.fn Γ e hc]
    exact h.2⟩

mutual

/-- typing derivations at `E` transport to a prefix extension `E' ⊇ E` AND a strengthened
    interface, when the interfaces agree on `E`'s terms (R-NoDeltaRec-4d-ii): every embedded
    term of an `E`-derivation is `E`-dom by `hasTyA_constsIn`, so the `iota`/`structIota` arms'
    interface reads are covered by the pointwise premise. -/
def hasTyA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → HasTyA E' J n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A u h hA => .bvar Γ i A u h (hasTyA_env_iface hpre hag hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      .const Γ r ls m u (hpre r m hres) hlen hwf (hasTyA_env_iface hpre hag hT)
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A u B v (hasTyA_env_iface hpre hag hA) (hasTyA_env_iface hpre hag hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam Γ A u body B v (hasTyA_env_iface hpre hag hA) (hasTyA_env_iface hpre hag hB)
        (hasTyA_env_iface hpre hag hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      .app Γ f a A B u v w (hasTyA_env_iface hpre hag hB) (hasTyA_env_iface hpre hag hTy)
        (hasTyA_env_iface hpre hag hf) (hasTyA_env_iface hpre hag ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      .letE Γ A u w value B body (hasTyA_env_iface hpre hag hA) (hasTyA_env_iface hpre hag hv)
        (hasTyA_env_iface hpre hag hTy) (hasTyA_env_iface hpre hag hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyA_env_iface hpre hag hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv Γ e A B l u (hasTyA_env_iface hpre hag h) (hasTyA_env_iface hpre hag hAl) hlu
        (hasTyA_env_iface hpre hag hB) (convA_env_iface hpre hag hc)

def convA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A → ConvA E' J n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (hasTyA_env_iface hpre hag h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (convA_env_iface hpre hag h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      .trans Γ a b c A (convA_env_iface hpre hag h1) (convA_env_iface hpre hag h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (hasTyA_env_iface hpre hag hA) (hasTyA_env_iface hpre hag hbody)
        (hasTyA_env_iface hpre hag harg) (hasTyA_env_iface hpre hag hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (hasTyA_env_iface hpre hag hA) (hasTyA_env_iface hpre hag hv)
        (hasTyA_env_iface hpre hag hb) (hasTyA_env_iface hpre hag hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (hasTyA_env_iface hpre hag hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b (hpre r m hres) hbody htr hlen hwf (hasTyA_env_iface hpre hag hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T (iotaRel_env_iface hpre hag (hasTyA_constsIn hlhs) h)
        (hasTyA_env_iface hpre hag hlhs) (hasTyA_env_iface hpre hag hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota Γ f a rhs e T
        (by rw [← recAtMajorA_prefix hpre (hasTyA_constsIn hlhs).1]; exact hrec)
        (by rw [← structArmA_prefix hpre (hasTyA_constsIn hlhs).1 a]; exact hs)
        ((hag _ (hasTyA_constsIn hlhs)).symm.trans h)
        (hasTyA_env_iface hpre hag hlhs) (hasTyA_env_iface hpre hag hrhs)
        (convA_env_iface hpre hag hcv)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyA_env_iface hpre hag hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      .app Γ f g a b A B u v (convA_env_iface hpre hag h1) (convA_env_iface hpre hag h2)
        (hasTyA_env_iface hpre hag hB) (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      .lam Γ A A' b b' B u u' v hu (convA_env_iface hpre hag hA) (convA_env_iface hpre hag hb)
        (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi Γ A A' B B' u u' v v' hu hv (convA_env_iface hpre hag hA)
        (convA_env_iface hpre hag hB) (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      .letE Γ A A' v v' b b' B u (convA_env_iface hpre hag hA) (convA_env_iface hpre hag hv)
        (convA_env_iface hpre hag hb) (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      .consts Γ r ls ls' m (hpre r m hres) hlen hwf hwf' h (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt =>
      .eta Γ f A B u v (hasTyA_env_iface hpre hag h) (hasTyA_env_iface hpre hag hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyA_env_iface hpre hag hP) (hasTyA_env_iface hpre hag hp)
        (hasTyA_env_iface hpre hag hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv Γ a b A A' l l' u (convA_env_iface hpre hag h) (hasTyA_env_iface hpre hag hAl) hlu
        (hasTyA_env_iface hpre hag hA'l) hl'u (convA_env_iface hpre hag hA)

end

end Iface

/-! ## (2) the concrete ι reads only what an admitted environment already has -/

section IotaPrefix

theorem constsInA_piDomsA {P : Nat → Prop} :
    (e : ExprA) → ConstsInA P e → ∀ d ∈ piDomsA e, ConstsInA P d
  | .pi a _ b _, ⟨ha, hb⟩, d, hd => by
      simp only [piDomsA, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact ha
      · exact constsInA_piDomsA b hb d hd
  | .bvar _, _, _, hd => by simp [piDomsA] at hd
  | .sort _, _, _, hd => by simp [piDomsA] at hd
  | .const _ _, _, _, hd => by simp [piDomsA] at hd
  | .app _ _, _, _, hd => by simp [piDomsA] at hd
  | .lam _ _ _, _, _, hd => by simp [piDomsA] at hd
  | .letE _ _ _, _, _, hd => by simp [piDomsA] at hd
  | .lit _, _, _, hd => by simp [piDomsA] at hd

theorem constsInA_foldAppsA_inv {P : Nat → Prop} :
    (h : ExprA) → (xs : List ExprA) → ConstsInA P (foldAppsA h xs) →
      ConstsInA P h ∧ ∀ x ∈ xs, ConstsInA P x
  | _, [], hh => ⟨hh, fun _ hx => by cases hx⟩
  | h, x :: xs, hh => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := constsInA_foldAppsA_inv (.app h x) xs hh
      exact ⟨h1, fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact h3 y hy⟩

theorem constsInA_spine_args {P : Nat → Prop} (e : ExprA) (h : ConstsInA P e) :
    ∀ x ∈ (appsSpineA e).2, ConstsInA P x := by
  have := foldAppsA_appsSpineA e
  rw [← this] at h
  exact (constsInA_foldAppsA_inv _ _ h).2

variable {I : IotaIfaceA} {E E' : ResolvedEnvA}

/-- the group lookup of the concrete ι agrees in an admitted environment and any extension, at a
    recursor and a constructor of the environment: the family it reads is named by the recursor's
    stored type, typed in the environment. -/
theorem iotaGroupA_prefix (hW : EnvWfA I E) (hpre : PrefixA E E') {recRef ctorRef : Nat}
    (hr : domA E recRef) (hc : domA E ctorRef) :
    iotaGroupA E' recRef ctorRef = iotaGroupA E recRef ctorRef := by
  obtain ⟨recM, hrm⟩ := hr
  obtain ⟨ctorM, hcm⟩ := hc
  have hfam : ∀ D ∈ piDomsA recM.mtypeA, ∀ f ls, (appsSpineA D).1 = .const f ls →
      E'.members f = E.members f := by
    intro D hD f ls hh
    obtain ⟨_, ⟨hT⟩⟩ := envWfA_memberTy hW recRef recM hrm
    obtain ⟨fm, hfm⟩ := constsInA_head D (constsInA_piDomsA _ (hasTyA_constsIn hT) D hD) f ls hh
    rw [hpre f fm hfm, hfm]
  unfold iotaGroupA
  rw [hpre _ _ hrm, hrm, hpre _ _ hcm, hcm]
  simp only
  split
  · cases hl : (piDomsA recM.mtypeA).getLast? with
    | none => rfl
    | some D =>
        simp only
        cases hh : (appsSpineA D).1 with
        | const f ls =>
            simp only
            rw [hfam D (List.mem_of_getLast?_eq_some hl) f ls hh]
        | _ => rfl
  · rfl

/-- the concrete ι of an admitted environment and of any extension agree on its terms. -/
theorem iotaFnA_prefix (hW : EnvWfA I E) (hpre : PrefixA E E') {e : ExprA}
    (hc : ConstsInA (domA E) e) : iotaFnA E' e = iotaFnA E e := by
  unfold iotaFnA
  cases hs : recSpineA e with
  | none => rfl
  | some s =>
      simp only [Option.bind]
      cases hm : spineHeadRefA s.major with
      | none => rfl
      | some c =>
          simp only
          have hsp := recSpineA_some hs
          have hr : domA E s.recRef := constsInA_head e hc s.recRef s.ls (by rw [hsp])
          have hmaj : ConstsInA (domA E) s.major :=
            constsInA_spine_args e hc s.major (by rw [hsp]; simp)
          obtain ⟨ls, hls⟩ := spineHeadRefA_some hm
          have hc' : domA E c := constsInA_head s.major hmaj c ls hls
          rw [iotaGroupA_prefix hW hpre hr hc']

/-- so the interfaces of an admitted environment and of any extension agree on its terms. -/
theorem ifaceAgreeA_prefix (hW : EnvWfA I E) (hpre : PrefixA E E') :
    IfaceAgreeA E (iotaIfaceA E) (iotaIfaceA E') :=
  fun _ hc => (iotaFnA_prefix hW hpre hc).symm

end IotaPrefix

/-! ## (3) closing a typing's levels -/

section Levels

theorem levelBounded_mono {a b : Nat} (hab : a ≤ b) : (l : Level) → levelBounded a l = true →
    levelBounded b l = true
  | .zero, _ => rfl
  | .succ l, h => levelBounded_mono hab l h
  | .max x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_mono hab x h.1, levelBounded_mono hab y h.2⟩
  | .imax x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_mono hab x h.1, levelBounded_mono hab y h.2⟩
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h ⊢
      omega

theorem levelsBounded_mono {a b : Nat} (hab : a ≤ b) : (ls : List Level) → levelsBounded a ls = true →
    levelsBounded b ls = true
  | [], _ => rfl
  | l :: ls, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_mono hab l h.1, levelsBounded_mono hab ls h.2⟩

/-- an upper bound on a level's parameters. -/
def lvlBound : Level → Nat
  | .zero => 0
  | .succ l => lvlBound l
  | .max a b => max (lvlBound a) (lvlBound b)
  | .imax a b => max (lvlBound a) (lvlBound b)
  | .param i => i + 1

theorem levelBounded_lvlBound : (l : Level) → levelBounded (lvlBound l) l = true
  | .zero => rfl
  | .succ l => levelBounded_lvlBound l
  | .max a b => by
      simp only [levelBounded, lvlBound, Bool.and_eq_true]
      exact ⟨levelBounded_mono (Nat.le_max_left _ _) a (levelBounded_lvlBound a),
        levelBounded_mono (Nat.le_max_right _ _) b (levelBounded_lvlBound b)⟩
  | .imax a b => by
      simp only [levelBounded, lvlBound, Bool.and_eq_true]
      exact ⟨levelBounded_mono (Nat.le_max_left _ _) a (levelBounded_lvlBound a),
        levelBounded_mono (Nat.le_max_right _ _) b (levelBounded_lvlBound b)⟩
  | .param i => by simp [levelBounded, lvlBound]

def lvlsBound : List Level → Nat
  | [] => 0
  | l :: ls => max (lvlBound l) (lvlsBound ls)

theorem levelsBounded_lvlsBound : (ls : List Level) → levelsBounded (lvlsBound ls) ls = true
  | [] => rfl
  | l :: ls => by
      simp only [levelsBounded, lvlsBound, Bool.and_eq_true]
      exact ⟨levelBounded_mono (Nat.le_max_left _ _) l (levelBounded_lvlBound l),
        levelsBounded_mono (Nat.le_max_right _ _) ls (levelsBounded_lvlsBound ls)⟩

theorem exprLevelsBoundedA_mono {a b : Nat} (hab : a ≤ b) : (e : ExprA) → exprLevelsBoundedA a e = true →
    exprLevelsBoundedA b e = true
  | .bvar _, _ => rfl
  | .sort l, h => levelBounded_mono hab l h
  | .const _ ms, h => levelsBounded_mono hab ms h
  | .app f x, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h ⊢
      exact ⟨exprLevelsBoundedA_mono hab f h.1, exprLevelsBoundedA_mono hab x h.2⟩
  | .lam a' u b', h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_mono hab a' h.1.1, levelBounded_mono hab u h.1.2⟩,
        exprLevelsBoundedA_mono hab b' h.2⟩
  | .pi a' u b' v, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨exprLevelsBoundedA_mono hab a' h.1.1.1, levelBounded_mono hab u h.1.1.2⟩,
        exprLevelsBoundedA_mono hab b' h.1.2⟩, levelBounded_mono hab v h.2⟩
  | .letE a' w b', h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_mono hab a' h.1.1, exprLevelsBoundedA_mono hab w h.1.2⟩,
        exprLevelsBoundedA_mono hab b' h.2⟩
  | .lit _, _ => rfl

/-- an upper bound on an annotated term's level parameters, annotations included. -/
def lvlBoundA : ExprA → Nat
  | .bvar _ => 0
  | .sort l => lvlBound l
  | .const _ ms => lvlsBound ms
  | .app f x => max (lvlBoundA f) (lvlBoundA x)
  | .lam a u b => max (lvlBoundA a) (max (lvlBound u) (lvlBoundA b))
  | .pi a u b v => max (lvlBoundA a) (max (lvlBound u) (max (lvlBoundA b) (lvlBound v)))
  | .letE a w b => max (lvlBoundA a) (max (lvlBoundA w) (lvlBoundA b))
  | .lit _ => 0

theorem exprLevelsBoundedA_lvlBoundA : (e : ExprA) → exprLevelsBoundedA (lvlBoundA e) e = true
  | .bvar _ => rfl
  | .sort l => levelBounded_lvlBound l
  | .const _ ms => levelsBounded_lvlsBound ms
  | .app f x => by
      simp only [exprLevelsBoundedA, lvlBoundA, Bool.and_eq_true]
      exact ⟨exprLevelsBoundedA_mono (Nat.le_max_left _ _) f (exprLevelsBoundedA_lvlBoundA f),
        exprLevelsBoundedA_mono (Nat.le_max_right _ _) x (exprLevelsBoundedA_lvlBoundA x)⟩
  | .lam a u b => by
      simp only [exprLevelsBoundedA, lvlBoundA, Bool.and_eq_true]
      refine ⟨⟨exprLevelsBoundedA_mono (Nat.le_max_left _ _) a (exprLevelsBoundedA_lvlBoundA a),
        levelBounded_mono ?_ u (levelBounded_lvlBound u)⟩,
        exprLevelsBoundedA_mono ?_ b (exprLevelsBoundedA_lvlBoundA b)⟩ <;> omega
  | .pi a u b v => by
      simp only [exprLevelsBoundedA, lvlBoundA, Bool.and_eq_true]
      refine ⟨⟨⟨exprLevelsBoundedA_mono (Nat.le_max_left _ _) a (exprLevelsBoundedA_lvlBoundA a),
        levelBounded_mono ?_ u (levelBounded_lvlBound u)⟩,
        exprLevelsBoundedA_mono ?_ b (exprLevelsBoundedA_lvlBoundA b)⟩,
        levelBounded_mono ?_ v (levelBounded_lvlBound v)⟩ <;> omega
  | .letE a w b => by
      simp only [exprLevelsBoundedA, lvlBoundA, Bool.and_eq_true]
      refine ⟨⟨exprLevelsBoundedA_mono (Nat.le_max_left _ _) a (exprLevelsBoundedA_lvlBoundA a),
        exprLevelsBoundedA_mono ?_ w (exprLevelsBoundedA_lvlBoundA w)⟩,
        exprLevelsBoundedA_mono ?_ b (exprLevelsBoundedA_lvlBoundA b)⟩ <;> omega
  | .lit _ => rfl

/-- every parameter below `M`, set to `zero`, leaves no parameter. -/
theorem levelBounded_inst_zeros {M : Nat} : (l : Level) → levelBounded M l = true →
    levelBounded 0 (instLevel (List.replicate M .zero) l) = true
  | .zero, _ => rfl
  | .succ l, h => levelBounded_inst_zeros l h
  | .max a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (levelBounded 0 (instLevel _ a) && levelBounded 0 (instLevel _ b)) = true
      simp only [Bool.and_eq_true]
      exact ⟨levelBounded_inst_zeros a h.1, levelBounded_inst_zeros b h.2⟩
  | .imax a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (levelBounded 0 (instLevel _ a) && levelBounded 0 (instLevel _ b)) = true
      simp only [Bool.and_eq_true]
      exact ⟨levelBounded_inst_zeros a h.1, levelBounded_inst_zeros b h.2⟩
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h
      show levelBounded 0 ((List.replicate M Level.zero)[i]?.getD (.param i)) = true
      rw [List.getElem?_replicate, if_pos h]
      rfl

theorem levelsBounded_inst_zeros {M : Nat} : (ls : List Level) → levelsBounded M ls = true →
    levelsBounded 0 (ls.map (instLevel (List.replicate M .zero))) = true
  | [], _ => rfl
  | l :: ls, h => by
      simp only [levelsBounded, Bool.and_eq_true, List.map] at h ⊢
      exact ⟨levelBounded_inst_zeros l h.1, levelsBounded_inst_zeros ls h.2⟩

theorem exprLevelsBoundedA_inst_zeros {M : Nat} : (e : ExprA) → exprLevelsBoundedA M e = true →
    exprLevelsBoundedA 0 (instantiateLevelsA (List.replicate M .zero) e) = true
  | .bvar _, _ => rfl
  | .sort l, h => levelBounded_inst_zeros l h
  | .const _ ms, h => levelsBounded_inst_zeros ms h
  | .app f x, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨exprLevelsBoundedA_inst_zeros f h.1, exprLevelsBoundedA_inst_zeros x h.2⟩
  | .lam a u b, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_inst_zeros a h.1.1, levelBounded_inst_zeros u h.1.2⟩,
        exprLevelsBoundedA_inst_zeros b h.2⟩
  | .pi a u b v, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨exprLevelsBoundedA_inst_zeros a h.1.1.1, levelBounded_inst_zeros u h.1.1.2⟩,
        exprLevelsBoundedA_inst_zeros b h.1.2⟩, levelBounded_inst_zeros v h.2⟩
  | .letE a w b, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_inst_zeros a h.1.1, exprLevelsBoundedA_inst_zeros w h.1.2⟩,
        exprLevelsBoundedA_inst_zeros b h.2⟩
  | .lit _, _ => rfl

theorem levelsBounded_zeros (M : Nat) : levelsBounded 0 (List.replicate M Level.zero) = true := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [List.replicate, levelsBounded, ih]; rfl

variable {E : ResolvedEnvA} {I : IotaIfaceA}

mutual

/-- derivations weaken along the level context: only `const`, `δ` and `consts` read it, as a bound. -/
def hasTyA_lvlWk {a b : Nat} (hab : a ≤ b) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I a Γ e A → HasTyA E I b Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A u h hA => .bvar Γ i A u h (hasTyA_lvlWk hab hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      .const Γ r ls m u hres hlen (levelsBounded_mono hab ls hwf) (hasTyA_lvlWk hab hT)
  | _, _, _, .pi Γ A u B v hA hB => .pi Γ A u B v (hasTyA_lvlWk hab hA) (hasTyA_lvlWk hab hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam Γ A u body B v (hasTyA_lvlWk hab hA) (hasTyA_lvlWk hab hB) (hasTyA_lvlWk hab hbody)
  | _, _, _, .app Γ f x A B u v w hB hTy hf ha =>
      .app Γ f x A B u v w (hasTyA_lvlWk hab hB) (hasTyA_lvlWk hab hTy) (hasTyA_lvlWk hab hf)
        (hasTyA_lvlWk hab ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      .letE Γ A u w value B body (hasTyA_lvlWk hab hA) (hasTyA_lvlWk hab hv) (hasTyA_lvlWk hab hTy)
        (hasTyA_lvlWk hab hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyA_lvlWk hab hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv Γ e A B l u (hasTyA_lvlWk hab h) (hasTyA_lvlWk hab hAl) hlu (hasTyA_lvlWk hab hB)
        (convA_lvlWk hab hc)

def convA_lvlWk {a b : Nat} (hab : a ≤ b) :
    {Γ : LCtxA} → {x y A : ExprA} → ConvA E I a Γ x y A → ConvA E I b Γ x y A
  | _, _, _, _, .refl Γ x A h => .refl Γ x A (hasTyA_lvlWk hab h)
  | _, _, _, _, .symm Γ x y A h => .symm Γ x y A (convA_lvlWk hab h)
  | _, _, _, _, .trans Γ x y z A h1 h2 => .trans Γ x y z A (convA_lvlWk hab h1) (convA_lvlWk hab h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (hasTyA_lvlWk hab hA) (hasTyA_lvlWk hab hbody) (hasTyA_lvlWk hab harg)
        (hasTyA_lvlWk hab hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (hasTyA_lvlWk hab hA) (hasTyA_lvlWk hab hv) (hasTyA_lvlWk hab hb)
        (hasTyA_lvlWk hab hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv => .zetaLocal Γ i A v hval hty (hasTyA_lvlWk hab hv)
  | _, _, _, _, .delta Γ r ls m b' hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b' hres hbody htr hlen (levelsBounded_mono hab ls hwf) (hasTyA_lvlWk hab hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T h (hasTyA_lvlWk hab hlhs) (hasTyA_lvlWk hab hrhs)
  | _, _, _, _, .structIota Γ f x rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota Γ f x rhs e T hrec hs h (hasTyA_lvlWk hab hlhs) (hasTyA_lvlWk hab hrhs)
        (convA_lvlWk hab hcv)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyA_lvlWk hab hexp)
  | _, _, _, _, .app Γ f g x y A B u v h1 h2 hB hrt =>
      .app Γ f g x y A B u v (convA_lvlWk hab h1) (convA_lvlWk hab h2) (hasTyA_lvlWk hab hB)
        (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .lam Γ A A' b₁ b₂ B u u' v hu hA hb hrt =>
      .lam Γ A A' b₁ b₂ B u u' v hu (convA_lvlWk hab hA) (convA_lvlWk hab hb) (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi Γ A A' B B' u u' v v' hu hv (convA_lvlWk hab hA) (convA_lvlWk hab hB)
        (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .letE Γ A A' v v' b₁ b₂ B u hA hv hb hrt =>
      .letE Γ A A' v v' b₁ b₂ B u (convA_lvlWk hab hA) (convA_lvlWk hab hv) (convA_lvlWk hab hb)
        (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      .consts Γ r ls ls' m hres hlen (levelsBounded_mono hab ls hwf) (levelsBounded_mono hab ls' hwf') h
        (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt => .eta Γ f A B u v (hasTyA_lvlWk hab h) (hasTyA_lvlWk hab hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyA_lvlWk hab hP) (hasTyA_lvlWk hab hp) (hasTyA_lvlWk hab hq)
  | _, _, _, _, .tyConv Γ x y A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv Γ x y A A' l l' u (convA_lvlWk hab h) (hasTyA_lvlWk hab hAl) hlu (hasTyA_lvlWk hab hA'l)
        hl'u (convA_lvlWk hab hA)

end

/-- CLOSING A TYPING'S LEVELS. A closed typing at level context `0` re-annotates with every level
    parameter below `M` set to `zero`. When `M` bounds the term and the type, the result names no
    level parameter at all; the erasure changes only where the erasure names one. -/
def closeLevelsA (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (M : Nat) {e A : ExprA}
    (h : HasTyA E I 0 [] e A) :
    HasTyA E I 0 [] (instantiateLevelsA (List.replicate M .zero) e)
      (instantiateLevelsA (List.replicate M .zero) A) :=
  hasTyA_instLevels hEL hIL (levelsBounded_zeros M) (List.length_replicate _ _)
    (hasTyA_lvlWk (Nat.zero_le M) h)


theorem levelsBounded_canonA (a : Nat) : levelsBounded a (canonLevelsA a) = true := by
  have : ∀ (xs : List Nat), (∀ i ∈ xs, i < a) → levelsBounded a (xs.map Level.param) = true := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons i xs ih =>
        intro h
        simp only [List.map_cons, levelsBounded, Bool.and_eq_true]
        exact ⟨by simp [levelBounded, h i (List.mem_cons_self _ _)],
          ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩
  exact this _ (fun i hi => List.mem_range.mp hi)

/-- the canonical list is the identity on every level. -/
theorem instLevel_canonA (a : Nat) : (l : Level) → instLevel (canonLevelsA a) l = l
  | .zero => rfl
  | .succ l => congrArg Level.succ (instLevel_canonA a l)
  | .max x y => by
      show Level.max (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_canonA a x, instLevel_canonA a y]
  | .imax x y => by
      show Level.imax (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_canonA a x, instLevel_canonA a y]
  | .param i => by
      rw [instLevel_param]
      by_cases h : i < a
      · simp [canonLevelsA, h]
      · have : (canonLevelsA a)[i]? = none := by
          simp only [canonLevelsA, List.getElem?_map, List.getElem?_range]
          simp [h, Nat.le_of_not_lt h]
        rw [this]; rfl

theorem instantiateLevels_canonA (a : Nat) : (e : Expr Nat) → instantiateLevels (canonLevelsA a) e = e
  | .bvar _ => rfl
  | .sort l => by simp only [instantiateLevels, instLevel_canonA]
  | .const r ms => by
      simp only [instantiateLevels]
      congr 1
      conv => rhs; rw [← List.map_id ms]
      exact List.map_congr_left (fun l _ => instLevel_canonA a l)
  | .app f x => by simp only [instantiateLevels, instantiateLevels_canonA a f, instantiateLevels_canonA a x]
  | .lam x b => by simp only [instantiateLevels, instantiateLevels_canonA a x, instantiateLevels_canonA a b]
  | .pi x b => by simp only [instantiateLevels, instantiateLevels_canonA a x, instantiateLevels_canonA a b]
  | .letE x v b => by
      simp only [instantiateLevels, instantiateLevels_canonA a x, instantiateLevels_canonA a v,
        instantiateLevels_canonA a b]
  | .lit _ => rfl

theorem levelsBounded_append (k : Nat) : (xs ys : List Level) →
    levelsBounded k (xs ++ ys) = (levelsBounded k xs && levelsBounded k ys)
  | [], _ => by simp [levelsBounded]
  | x :: xs, ys => by
      show (levelBounded k x && levelsBounded k (xs ++ ys)) = _
      rw [levelsBounded_append k xs ys]
      simp only [levelsBounded, Bool.and_assoc]

theorem levelsBounded_replicate_zero (k M : Nat) : levelsBounded k (List.replicate M Level.zero) = true := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [List.replicate, levelsBounded, ih]; rfl

/-- the closing level list at arity `a`: the family's parameters stay, the next `M` go to `zero`. -/
def closeLs (a M : Nat) : List Level := canonLevelsA a ++ List.replicate M .zero

theorem closeLs_length (a M : Nat) : (closeLs a M).length = a + M := by
  simp [closeLs, canonLevelsA]

theorem closeLs_get_lt {a M i : Nat} (h : i < a) : (closeLs a M)[i]? = some (.param i) := by
  have hl : i < (canonLevelsA a).length := by simp [canonLevelsA]; exact h
  rw [closeLs, List.getElem?_append_left hl]
  simp [canonLevelsA, h]

theorem closeLs_get_ge {a M i : Nat} (h1 : a ≤ i) (h2 : i < a + M) :
    (closeLs a M)[i]? = some .zero := by
  have hl : (canonLevelsA a).length ≤ i := by simp [canonLevelsA]; exact h1
  rw [closeLs, List.getElem?_append_right hl, List.getElem?_replicate]
  simp only [canonLevelsA, List.length_map, List.length_range]
  rw [if_pos (by omega)]

theorem levelBounded_inst_closeLs {a M : Nat} : (l : Level) → levelBounded (a + M) l = true →
    levelBounded a (instLevel (closeLs a M) l) = true
  | .zero, _ => rfl
  | .succ l, h => levelBounded_inst_closeLs l h
  | .max x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (levelBounded a (instLevel _ x) && levelBounded a (instLevel _ y)) = true
      simp only [Bool.and_eq_true]
      exact ⟨levelBounded_inst_closeLs x h.1, levelBounded_inst_closeLs y h.2⟩
  | .imax x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (levelBounded a (instLevel _ x) && levelBounded a (instLevel _ y)) = true
      simp only [Bool.and_eq_true]
      exact ⟨levelBounded_inst_closeLs x h.1, levelBounded_inst_closeLs y h.2⟩
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h
      rw [instLevel_param]
      by_cases hi : i < a
      · rw [closeLs_get_lt hi]; simp [levelBounded, hi]
      · rw [closeLs_get_ge (by omega) h]; rfl

theorem levelsBounded_inst_closeLs {a M : Nat} : (ls : List Level) → levelsBounded (a + M) ls = true →
    levelsBounded a (ls.map (instLevel (closeLs a M))) = true
  | [], _ => rfl
  | l :: ls, h => by
      simp only [levelsBounded, Bool.and_eq_true, List.map] at h ⊢
      exact ⟨levelBounded_inst_closeLs l h.1, levelsBounded_inst_closeLs ls h.2⟩

theorem exprLevelsBoundedA_inst_closeLs {a M : Nat} : (e : ExprA) → exprLevelsBoundedA (a + M) e = true →
    exprLevelsBoundedA a (instantiateLevelsA (closeLs a M) e) = true
  | .bvar _, _ => rfl
  | .sort l, h => levelBounded_inst_closeLs l h
  | .const _ ms, h => levelsBounded_inst_closeLs ms h
  | .app f x, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨exprLevelsBoundedA_inst_closeLs f h.1, exprLevelsBoundedA_inst_closeLs x h.2⟩
  | .lam x u b, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_inst_closeLs x h.1.1, levelBounded_inst_closeLs u h.1.2⟩,
        exprLevelsBoundedA_inst_closeLs b h.2⟩
  | .pi x u b v, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨exprLevelsBoundedA_inst_closeLs x h.1.1.1, levelBounded_inst_closeLs u h.1.1.2⟩,
        exprLevelsBoundedA_inst_closeLs b h.1.2⟩, levelBounded_inst_closeLs v h.2⟩
  | .letE x w b, h => by
      simp only [exprLevelsBoundedA, instantiateLevelsA, Bool.and_eq_true] at h ⊢
      exact ⟨⟨exprLevelsBoundedA_inst_closeLs x h.1.1, exprLevelsBoundedA_inst_closeLs w h.1.2⟩,
        exprLevelsBoundedA_inst_closeLs b h.2⟩
  | .lit _, _ => rfl

theorem levelsBounded_closeLs (a M : Nat) : levelsBounded a (closeLs a M) = true := by
  rw [closeLs, levelsBounded_append, levelsBounded_canonA, levelsBounded_replicate_zero]; rfl

/-- the family's own parameters are fixed by the closing list. -/
theorem instLevel_closeLs_of_bounded {a M : Nat} : (l : Level) → levelBounded a l = true →
    instLevel (closeLs a M) l = l
  | .zero, _ => rfl
  | .succ l, h => congrArg Level.succ (instLevel_closeLs_of_bounded l h)
  | .max x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show Level.max (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_closeLs_of_bounded x h.1, instLevel_closeLs_of_bounded y h.2]
  | .imax x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show Level.imax (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_closeLs_of_bounded x h.1, instLevel_closeLs_of_bounded y h.2]
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h
      rw [instLevel_param, closeLs_get_lt h]; rfl

/-- on `main`'s syntax, a term within the family's arity is fixed by the closing list. -/
theorem instantiateLevels_closeLs {a M : Nat} (e : Expr Nat) (h : exprLevelsBounded a e = true) :
    instantiateLevels (closeLs a M) e = e := by
  rw [instantiateLevels_take a _ e h]
  have ht : (closeLs a M).take a = canonLevelsA a := by
    rw [closeLs, List.take_left' (by simp [canonLevelsA])]
  rw [ht]
  exact instantiateLevels_canonA a e

variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- a typing closed: the level context weakened to `a + M`, instantiated at the closing list. -/
def closeTyA (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) {Γ : LCtxA} {e A : ExprA}
    (h : HasTyA E I a Γ e A) :
    HasTyA E I a (instCtxA (closeLs a M) Γ) (instantiateLevelsA (closeLs a M) e)
      (instantiateLevelsA (closeLs a M) A) :=
  hasTyA_instLevels hEL hIL (levelsBounded_closeLs a M) (closeLs_length a M)
    (hasTyA_lvlWk (Nat.le_add_right a M) h)

def closeConvA (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) {Γ : LCtxA} {x y A : ExprA}
    (h : ConvA E I a Γ x y A) :
    ConvA E I a (instCtxA (closeLs a M) Γ) (instantiateLevelsA (closeLs a M) x)
      (instantiateLevelsA (closeLs a M) y) (instantiateLevelsA (closeLs a M) A) :=
  convA_instLevels hEL hIL (levelsBounded_closeLs a M) (closeLs_length a M)
    (convA_lvlWk (Nat.le_add_right a M) h)


end Levels

/-! ## (4) erasure facts the bridge reads -/

section EraseFacts

/-- closedness reads through erasure: lifting changes no annotation. -/
theorem liftA_eq_of_erase : (e : ExprA) → (c : Nat) → lift c 1 (erase e) = erase e → liftA c 1 e = e
  | .bvar i, c, h => by
      simp only [erase, lift] at h
      simp only [liftA]
      split <;> split at h <;> first | rfl | (injection h with h; omega)
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app f x, c, h => by
      simp only [erase, lift] at h
      injection h with h1 h2
      simp only [liftA, liftA_eq_of_erase f c h1, liftA_eq_of_erase x c h2]
  | .lam a u b, c, h => by
      simp only [erase, lift] at h
      injection h with h1 h2
      simp only [liftA, liftA_eq_of_erase a c h1, liftA_eq_of_erase b (c + 1) h2]
  | .pi a u b v, c, h => by
      simp only [erase, lift] at h
      injection h with h1 h2
      simp only [liftA, liftA_eq_of_erase a c h1, liftA_eq_of_erase b (c + 1) h2]
  | .letE a w b, c, h => by
      simp only [erase, lift] at h
      injection h with h1 h2 h3
      simp only [liftA, liftA_eq_of_erase a c h1, liftA_eq_of_erase w c h2, liftA_eq_of_erase b (c + 1) h3]
  | .lit _, _, _ => rfl

theorem instantiateLevels_closed (ls : List Level) (e : Expr Nat) (h : exprLevelsBounded 0 e = true) :
    instantiateLevels ls e = e := by
  rw [instantiateLevels_take 0 ls e h, List.take_zero, instantiateLevels_nil]

theorem eraseEnv_extend (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA) :
    eraseEnv (extendEnvA E r m) = extendEnv (eraseEnv E) r (eraseMember m) := by
  show ResolvedEnv.mk _ = ResolvedEnv.mk _
  congr 1
  funext r'
  exact members_eraseEnv_extend E r m r'

theorem eraseEnv_empty : eraseEnv emptyEnvA = emptyEnv := rfl

theorem members_none_of_erase {E : ResolvedEnvA} {r : Nat} (h : (eraseEnv E).members r = none) :
    E.members r = none := by
  rw [members_eraseEnv] at h
  cases hm : E.members r with
  | none => rfl
  | some m => rw [hm] at h; exact Option.noConfusion h

end EraseFacts

/-! ## (5) THE ENVIRONMENT BRIDGE, without inductive groups -/

section Bridge

/-- an annotated environment with no inductive group. -/
def NoGroupEnvA (E : ResolvedEnvA) : Prop := NoGroupEnv (eraseEnv E)

theorem noGroupEnvA_members {E : ResolvedEnvA} (h : NoGroupEnvA E) {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) :
    m.mclass ≠ .inductiveM ∧ m.mclass ≠ .constructorM ∧ m.mclass ≠ .recursorM :=
  h r (eraseMember m) (by rw [members_eraseEnv, hm]; rfl)

theorem smallIndexProfileA_of_noGroup {E : ResolvedEnvA} (h : NoGroupEnvA E) : SmallIndexProfileA E :=
  fun _ _ _ hm hcls => absurd hcls (noGroupEnvA_members h hm).1

theorem envNoFunA_of_noGroup {E : ResolvedEnvA} (h : NoGroupEnvA E) : EnvNoFunA E :=
  fun _ _ _ _ _ hm hcls _ _ _ _ _ _ => absurd hcls (noGroupEnvA_members h hm).2.1

/-- a group-free environment is `EnvNormEraseA`-clean vacuously: it has no constructor member to
    constrain. -/
theorem envNormEraseA_of_noGroup {E : ResolvedEnvA} (h : NoGroupEnvA E) : EnvNormEraseA E :=
  fun _ _ hm hcls _ _ => absurd hcls (noGroupEnvA_members h hm).2.1

theorem propElimOnlyA_of_noGroup {E : ResolvedEnvA} (h : NoGroupEnvA E) : PropElimOnlyA E :=
  fun _ _ _ _ _ _ _ hm hcls => absurd hcls (noGroupEnvA_members h hm).2.2

/-- R-NoFunRec-1 B2: at a no-group environment the typed-root ι correspondence
    needs no certificate — there are no recursors, so `DerivedIotaT` evidence
    cannot exist (`ann`) and the copy's ι never fires (`eraseT`). -/
theorem iotaCorrTA_of_noGroupEnvA {E : ResolvedEnvA} (hno : NoGroupEnvA E) : IotaCorrTA E where
  ann := fun _ _ hd => by
    obtain ⟨w, -, -⟩ := derivedIotaT_unpack hd
    exact ((hno _ _ w.hrec).2.2 w.hrecK).elim
  eraseT := fun _ _ hstep => by
    obtain ⟨_, _, g, _, _, hg, _⟩ := iotaFnA_some hstep
    obtain ⟨hrec, hrecK, _⟩ := iotaGroupA_some hg
    exact ((noGroupEnvA_members hno hrec).2.2 hrecK).elim

theorem noGroupEnv_of_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) (h : NoGroupEnv (extendEnv E r m)) : NoGroupEnv E := by
  intro r' m' hm'
  apply h r' m'
  show (if r' = r then some m else E.members r') = some m'
  rw [if_neg (fun hr => by subst hr; rw [hfresh] at hm'; exact Option.noConfusion hm')]
  exact hm'

/-- a group's members persist to its end: each later reference is fresh. -/
theorem groupMembersT_prefix {S : ResolvedEnv} :
    {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E ms E' → ∀ r m, E.members r = some m → E'.members r = some m
  | _, _, _, .nil _ => fun _ _ h => h
  | _, _, _, .cons E r₀ m₀ _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest => fun r m h => by
      apply groupMembersT_prefix hrest r m
      show (if r = r₀ then some m₀ else E.members r) = some m
      rw [if_neg (fun hr => by subst hr; rw [hfresh] at h; exact Option.noConfusion h)]
      exact h

theorem groupMembersT_mem {S : ResolvedEnv} :
    {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E ms E' → ∀ p ∈ ms, E'.members p.1 = some p.2
  | _, _, _, .nil _ => fun _ hp => by cases hp
  | _, _, _, .cons E r₀ m₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest => fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact groupMembersT_prefix hrest r₀ m₀ (by show (if r₀ = r₀ then some m₀ else _) = _; rw [if_pos rfl])
      · exact groupMembersT_mem hrest p hp

/-- the bridge's environment entry: an annotation admitted at every interface that agrees with its own
    on its terms, with no inductive group, is an environment the copy admits. -/
theorem annEnvA_of_bridged {EA : ResolvedEnvA} (hno : NoGroupEnvA EA)
    (hW : ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)) : AnnEnvA EA :=
  ⟨hW _ (IfaceAgreeA.refl _ _), smallIndexProfileA_of_noGroup hno,
    propElimStructA_of_propElimOnlyA (propElimOnlyA_of_noGroup hno), envNoFunA_of_noGroup hno⟩

variable {E : ResolvedEnvA}

/-- A locally closed type annotates at its own universe arity. The existing
    prefix-preserving closing list fixes its declared parameters and closes only
    the additional levels introduced by annotations. -/
theorem annotateClosedType (C : AnnEnvA E) (hn : EnvNormEraseA E) {arity : Nat}
    {A : Expr Nat} {u : Level}
    (hA : HasTyT (eraseEnv E) arity [] A (.sort u)) (hlvl : exprLevelsBounded arity A = true) :
    ∃ (AA : ExprA) (ls : List Level), erase AA = A ∧ exprLevelsBoundedA arity AA = true ∧
      Nonempty (HasTyA E (iotaIfaceA E) arity [] AA (.sort (instLevel ls u))) := by
  obtain ⟨AA, TA, hAe, hTe, ⟨t⟩⟩ := annHasTyT' C hn hA CtxWfA.nil rfl
  obtain rfl := erase_eq_sort hTe
  refine ⟨instantiateLevelsA (closeLs arity (lvlBoundA AA)) AA,
    closeLs arity (lvlBoundA AA), ?_, ?_, ⟨closeTyA C.hEL C.hIL arity _ t⟩⟩
  · rw [erase_instantiateLevelsA, hAe, instantiateLevels_closeLs _ hlvl]
  · exact exprLevelsBoundedA_inst_closeLs AA
      (exprLevelsBoundedA_mono (Nat.le_add_left (lvlBoundA AA) arity) AA
        (exprLevelsBoundedA_lvlBoundA AA))

/-- a closed value of a closed type annotates, at one closing of levels, with the type. -/
theorem annotateClosedValue (C : AnnEnvA E) (hn : EnvNormEraseA E) {A v : Expr Nat} {u : Level}
    (hA : HasTyT (eraseEnv E) 0 [] A (.sort u)) (hv : HasTyT (eraseEnv E) 0 [] v A)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
    ∃ (AA vA : ExprA) (ls : List Level), erase AA = A ∧ erase vA = v ∧
      exprLevelsBoundedA 0 AA = true ∧ exprLevelsBoundedA 0 vA = true ∧
      Nonempty (HasTyA E (iotaIfaceA E) 0 [] AA (.sort (instLevel ls u))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) 0 [] vA AA) := by
  obtain ⟨AA, TA, hAe, hTe, ⟨t⟩⟩ := annHasTyT' C hn hA CtxWfA.nil rfl
  obtain rfl := erase_eq_sort hTe
  obtain ⟨vA, TV, hve, hTVe, ⟨tv⟩⟩ := annHasTyT' C hn hv CtxWfA.nil rfl
  obtain ⟨tv'⟩ := hasTyA_reannot C CtxWfA.nil tv (hTVe.trans hAe.symm) t
  let M := max (lvlBoundA AA) (lvlBoundA vA)
  refine ⟨instantiateLevelsA (List.replicate M .zero) AA, instantiateLevelsA (List.replicate M .zero) vA,
    List.replicate M .zero, ?_, ?_, ?_, ?_, ⟨closeLevelsA C.hEL C.hIL _ t⟩, ⟨closeLevelsA C.hEL C.hIL _ tv'⟩⟩
  · rw [erase_instantiateLevelsA, hAe, instantiateLevels_closed _ _ hlvlA]
  · rw [erase_instantiateLevelsA, hve, instantiateLevels_closed _ _ hlvlv]
  · exact exprLevelsBoundedA_inst_zeros AA
      (exprLevelsBoundedA_mono (Nat.le_max_left _ _) AA (exprLevelsBoundedA_lvlBoundA AA))
  · exact exprLevelsBoundedA_inst_zeros vA
      (exprLevelsBoundedA_mono (Nat.le_max_right _ _) vA (exprLevelsBoundedA_lvlBoundA vA))

/-- the agreement a singleton step needs: the prefix's own interface and any interface that agrees
    with the extension's on its terms agree on the prefix's terms. -/
theorem ifaceAgree_step {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA) {r : Nat}
    {m : CheckedMemberA} (hfr : EA.members r = none) {J : IotaIfaceA}
    (hJ : IfaceAgreeA (extendEnvA EA r m) (iotaIfaceA (extendEnvA EA r m)) J) :
    IfaceAgreeA EA (iotaIfaceA EA) J :=
  (ifaceAgreeA_prefix hW (prefixA_extend EA r m hfr)).trans (hJ.prefix (prefixA_extend EA r m hfr))

/-- the bridge's singleton steps: an extension by an axiom, definition, theorem or opaque member whose
    parts are typed in the erasure of an admitted base is the erasure of an extension the copy admits,
    at every interface that agrees with the extension's own on its terms. -/
theorem bridgeStep_axiom {EA : ResolvedEnvA} (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)) {r : Nat} {A : Expr Nat}
    {arity : Nat} {u : Level} (hfresh : (eraseEnv EA).members r = none) (hA : HasTyT (eraseEnv EA) arity [] A (.sort u))
    (hcl : ∀ k, lift k 1 A = A) (hlvl : exprLevelsBounded arity A = true) :
    ∃ mA : CheckedMemberA, mA.mclass = .axiomM ∧
      eraseEnv (extendEnvA EA r mA) = extendEnv (eraseEnv EA) r ⟨.axiomM, arity, A, none⟩ ∧
      ∀ J, IfaceAgreeA (extendEnvA EA r mA) (iotaIfaceA (extendEnvA EA r mA)) J →
        Nonempty (EnvWfA J (extendEnvA EA r mA)) := by
  obtain ⟨AA, ls, hAe, hlvlA, ⟨tA⟩⟩ := annotateClosedType C hn hA hlvl
  have hcl' : ∀ k, liftA k 1 AA = AA := fun k => liftA_eq_of_erase AA k (by rw [hAe]; exact hcl k)
  have hfr := members_none_of_erase hfresh
  refine ⟨⟨.axiomM, arity, AA, none, 0, none⟩, rfl, ?_, fun J hJ => ?_⟩
  · rw [eraseEnv_extend, eraseMember]; simp only [hAe, Option.map_none']
  · obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
    have hag := ifaceAgree_step hW0 hfr hJ
    obtain ⟨hWJ⟩ := hW J hag
    exact ⟨.axiomM EA r AA _ hWJ hfr (hasTyIfaceA hag tA) hcl' hlvlA⟩

theorem bridgeStep_definition {EA : ResolvedEnvA} (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)) {r : Nat} {A v : Expr Nat}
    {u : Level} (hfresh : (eraseEnv EA).members r = none) (hA : HasTyT (eraseEnv EA) 0 [] A (.sort u))
    (hv : HasTyT (eraseEnv EA) 0 [] v A) (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
    ∃ mA : CheckedMemberA, mA.mclass = .definitionM ∧
      eraseEnv (extendEnvA EA r mA) = extendEnv (eraseEnv EA) r ⟨.definitionM, 0, A, some v⟩ ∧
      ∀ J, IfaceAgreeA (extendEnvA EA r mA) (iotaIfaceA (extendEnvA EA r mA)) J →
        Nonempty (EnvWfA J (extendEnvA EA r mA)) := by
  obtain ⟨AA, vA, ls, hAe, hve, hlA, hlv, ⟨tA⟩, ⟨tv⟩⟩ := annotateClosedValue C hn hA hv hlvlA hlvlv
  have hclA' : ∀ k, liftA k 1 AA = AA := fun k => liftA_eq_of_erase AA k (by rw [hAe]; exact hclA k)
  have hclv' : ∀ k, liftA k 1 vA = vA := fun k => liftA_eq_of_erase vA k (by rw [hve]; exact hclv k)
  have hfr := members_none_of_erase hfresh
  refine ⟨⟨.definitionM, 0, AA, some vA, 0, none⟩, rfl, ?_, fun J hJ => ?_⟩
  · rw [eraseEnv_extend, eraseMember]; simp only [hAe, hve, Option.map_some']
  · obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
    have hag := ifaceAgree_step hW0 hfr hJ
    obtain ⟨hWJ⟩ := hW J hag
    exact ⟨.definitionM EA r AA vA _ hWJ hfr (hasTyIfaceA hag tA) (hasTyIfaceA hag tv) hclA' hclv' hlA hlv⟩

theorem bridgeStep_thm {EA : ResolvedEnvA} (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)) {r : Nat} {A p : Expr Nat}
    (hfresh : (eraseEnv EA).members r = none) (hA : HasTyT (eraseEnv EA) 0 [] A (.sort .zero))
    (hp : HasTyT (eraseEnv EA) 0 [] p A) (hclA : ∀ k, lift k 1 A = A) (hclp : ∀ k, lift k 1 p = p)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlp : exprLevelsBounded 0 p = true) :
    ∃ mA : CheckedMemberA, mA.mclass = .theoremM ∧
      eraseEnv (extendEnvA EA r mA) = extendEnv (eraseEnv EA) r ⟨.theoremM, 0, A, some p⟩ ∧
      ∀ J, IfaceAgreeA (extendEnvA EA r mA) (iotaIfaceA (extendEnvA EA r mA)) J →
        Nonempty (EnvWfA J (extendEnvA EA r mA)) := by
  obtain ⟨AA, pA, ls, hAe, hpe, hlA, hlp, ⟨tA⟩, ⟨tp⟩⟩ := annotateClosedValue C hn hA hp hlvlA hlvlp
  have hclA' : ∀ k, liftA k 1 AA = AA := fun k => liftA_eq_of_erase AA k (by rw [hAe]; exact hclA k)
  have hclp' : ∀ k, liftA k 1 pA = pA := fun k => liftA_eq_of_erase pA k (by rw [hpe]; exact hclp k)
  have hfr := members_none_of_erase hfresh
  refine ⟨⟨.theoremM, 0, AA, some pA, 0, none⟩, rfl, ?_, fun J hJ => ?_⟩
  · rw [eraseEnv_extend, eraseMember]; simp only [hAe, hpe, Option.map_some']
  · obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
    have hag := ifaceAgree_step hW0 hfr hJ
    obtain ⟨hWJ⟩ := hW J hag
    exact ⟨.theoremM EA r AA pA hWJ hfr (hasTyIfaceA hag tA) (hasTyIfaceA hag tp) hclA' hclp' hlA hlp⟩

theorem bridgeStep_opaque {EA : ResolvedEnvA} (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)) {r : Nat} {A v : Expr Nat}
    {u : Level} (hfresh : (eraseEnv EA).members r = none) (hA : HasTyT (eraseEnv EA) 0 [] A (.sort u))
    (hv : HasTyT (eraseEnv EA) 0 [] v A) (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
    ∃ mA : CheckedMemberA, mA.mclass = .opaqueM ∧
      eraseEnv (extendEnvA EA r mA) = extendEnv (eraseEnv EA) r ⟨.opaqueM, 0, A, some v⟩ ∧
      ∀ J, IfaceAgreeA (extendEnvA EA r mA) (iotaIfaceA (extendEnvA EA r mA)) J →
        Nonempty (EnvWfA J (extendEnvA EA r mA)) := by
  obtain ⟨AA, vA, ls, hAe, hve, hlA, hlv, ⟨tA⟩, ⟨tv⟩⟩ := annotateClosedValue C hn hA hv hlvlA hlvlv
  have hclA' : ∀ k, liftA k 1 AA = AA := fun k => liftA_eq_of_erase AA k (by rw [hAe]; exact hclA k)
  have hclv' : ∀ k, liftA k 1 vA = vA := fun k => liftA_eq_of_erase vA k (by rw [hve]; exact hclv k)
  have hfr := members_none_of_erase hfresh
  refine ⟨⟨.opaqueM, 0, AA, some vA, 0, none⟩, rfl, ?_, fun J hJ => ?_⟩
  · rw [eraseEnv_extend, eraseMember]; simp only [hAe, hve, Option.map_some']
  · obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
    have hag := ifaceAgree_step hW0 hfr hJ
    obtain ⟨hWJ⟩ := hW J hag
    exact ⟨.opaqueM EA r AA vA _ hWJ hfr (hasTyIfaceA hag tA) (hasTyIfaceA hag tv) hclA' hclv' hlA hlv⟩

/-- THE ENVIRONMENT BRIDGE, without inductive groups: every environment of R-CIC's typed environment
    judgment with no inductive group is the erasure of an environment the copy admits, at every
    interface that agrees with that environment's own on its terms. -/
theorem envBridge_noGroup : {E : ResolvedEnv} → EnvWfT E → NoGroupEnv E →
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ NoGroupEnvA EA ∧
      ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)
  | _, .empty, _ => ⟨emptyEnvA, rfl, fun _ _ hm => Option.noConfusion hm, fun _ _ => ⟨.empty⟩⟩
  | _, .axiom E r A u hE hfresh hA hcl hlvl, hno => by
      obtain ⟨EA, rfl, hnoA, hW⟩ := envBridge_noGroup hE (noGroupEnv_of_extend hfresh hno)
      obtain ⟨_, _, hEnv, hW'⟩ := bridgeStep_axiom (annEnvA_of_bridged hnoA hW) (envNormEraseA_of_noGroup hnoA) hW hfresh hA hcl hlvl
      exact ⟨_, hEnv, by unfold NoGroupEnvA; rw [hEnv]; exact hno, hW'⟩
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hno => by
      obtain ⟨EA, rfl, hnoA, hW⟩ := envBridge_noGroup hE (noGroupEnv_of_extend hfresh hno)
      obtain ⟨_, _, hEnv, hW'⟩ :=
        bridgeStep_definition (annEnvA_of_bridged hnoA hW) (envNormEraseA_of_noGroup hnoA) hW hfresh hA hv hclA hclv hlvlA hlvlv
      exact ⟨_, hEnv, by unfold NoGroupEnvA; rw [hEnv]; exact hno, hW'⟩
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hno => by
      obtain ⟨EA, rfl, hnoA, hW⟩ := envBridge_noGroup hE (noGroupEnv_of_extend hfresh hno)
      obtain ⟨_, _, hEnv, hW'⟩ :=
        bridgeStep_thm (annEnvA_of_bridged hnoA hW) (envNormEraseA_of_noGroup hnoA) hW hfresh hA hp hclA hclp hlvlA hlvlp
      exact ⟨_, hEnv, by unfold NoGroupEnvA; rw [hEnv]; exact hno, hW'⟩
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hno => by
      obtain ⟨EA, rfl, hnoA, hW⟩ := envBridge_noGroup hE (noGroupEnv_of_extend hfresh hno)
      obtain ⟨_, _, hEnv, hW'⟩ :=
        bridgeStep_opaque (annEnvA_of_bridged hnoA hW) (envNormEraseA_of_noGroup hnoA) hW hfresh hA hv hclA hclv hlvlA hlvlv
      exact ⟨_, hEnv, by unfold NoGroupEnvA; rw [hEnv]; exact hno, hW'⟩
  | _, .group _ f fm _ _ _ _ _ hfam _ _ hmem, hno =>
      absurd hfam (hno f fm (groupMembersT_mem hmem (f, fm) (List.mem_cons_self _ _))).1

/-- every environment of the typed environment judgment with no inductive group is the erasure of one
    the copy admits. -/
theorem annEnvA_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) (hno : NoGroupEnv E) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ AnnEnvA EA ∧ EnvNormEraseA EA := by
  obtain ⟨EA, hE, hnoA, hWA⟩ := envBridge_noGroup hW hno
  exact ⟨EA, hE, annEnvA_of_bridged hnoA hWA, envNormEraseA_of_noGroup hnoA⟩

/-- ROW 1 OVER THE TYPED ENVIRONMENT JUDGMENT, without inductive groups. -/
theorem sortConvCharT_envT {E : ResolvedEnv} (hW : EnvWfT E) (hno : NoGroupEnv E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level} {T : Expr Nat} (h : ConvT E n Γ (.sort l₁) (.sort l₂) T) :
    eqN l₁ l₂ := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT hW hno
  exact sortConvCharT' C hn hΓ h

/-- ROW 2 OVER THE TYPED ENVIRONMENT JUDGMENT, without inductive groups. -/
theorem piConvInjT_envT {E : ResolvedEnv} (hW : EnvWfT E) (hno : NoGroupEnv E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A B A' B' T : Expr Nat} (h : ConvT E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT hW hno
  exact piConvInjT' C hn hΓ h

end Bridge

/-! ## (6) the untyped `EnvWf` admits an environment no admitted annotation erases to -/

section BadDef

/-- `def bad : Prop := Type`, in the empty environment. -/
def badDefEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.definitionM, 0, .sort .zero, some (.sort (.succ .zero))⟩

/-- `main`'s untyped `EnvWf` admits it at every level count: the value `Type` is retyped at `Prop` by the
    total conversion (`UntypedConvCollapse.retypeAny`). -/
def envWf_badDef (n : Nat) : EnvWf badDefEnv n :=
  .definition emptyEnv 0 (.sort .zero) (.sort (.succ .zero)) (.succ .zero) (.empty n) rfl
    (.sort [] .zero) (UntypedConvCollapse.retypeAny (.sort [] (.succ .zero)) (.sort .zero))
    (fun _ => rfl) (fun _ => rfl)

/-- and it is the erasure of no environment the copy admits: there `Type : Prop` would make `Prop` and
    `Type 1` convertible sorts, which row 1 refutes. -/
theorem badDef_not_admitted : ¬ ∃ EA : ResolvedEnvA, eraseEnv EA = badDefEnv ∧ AnnEnvA EA := by
  rintro ⟨EA, hE, C⟩
  obtain ⟨hW⟩ := C.wf
  have h0 : (eraseEnv EA).members 0 =
      some ⟨.definitionM, 0, .sort .zero, some (.sort (.succ .zero))⟩ := by rw [hE]; rfl
  rw [members_eraseEnv] at h0
  cases hm : EA.members 0 with
  | none => rw [hm] at h0; exact Option.noConfusion h0
  | some mA =>
      rw [hm] at h0
      injection h0 with h0
      have hT : erase mA.mtypeA = .sort .zero := congrArg CheckedMember.mtype h0
      have hb : mA.bodyA.map erase = some (.sort (.succ .zero)) := congrArg CheckedMember.body h0
      have har : mA.arity = 0 := congrArg CheckedMember.arity h0
      have hTA := erase_eq_sort hT
      cases hbA : mA.bodyA with
      | none => rw [hbA] at hb; exact Option.noConfusion hb
      | some b =>
          rw [hbA] at hb
          injection hb with hb
          obtain rfl := erase_eq_sort hb
          obtain ⟨t⟩ := envWfA_memberBody hW 0 mA _ hm hbA
          rw [har, hTA] at t
          obtain ⟨tc⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS 0) posValA_one .nil t
            (.sort [] (.succ .zero))
          have c := tyConvA_collapse C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS 0) posValA_one .nil tc
            (.sort [] .zero)
          have h2 := sortConvCharA_rec hW posValA_one C.small C.propElim .nil c (fun _ => none)
          simp [eval] at h2

end BadDef

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.hasTyIfaceA
#print axioms Rcic.Declarative.Ann.iotaFnA_prefix
#print axioms Rcic.Declarative.Ann.closeLevelsA
#print axioms Rcic.Declarative.Ann.liftA_eq_of_erase
#print axioms Rcic.Declarative.Ann.envBridge_noGroup
#print axioms Rcic.Declarative.Ann.annEnvA_of_envWfT
#print axioms Rcic.Declarative.Ann.sortConvCharT_envT
#print axioms Rcic.Declarative.Ann.piConvInjT_envT
#print axioms Rcic.Declarative.Ann.envWf_badDef
#print axioms Rcic.Declarative.Ann.badDef_not_admitted
