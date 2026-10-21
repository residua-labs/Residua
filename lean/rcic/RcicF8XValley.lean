import rcic.RcicF8XFlat
import rcic.RcicF8EvInvT
import rcic.RcicF8CtxConvVar

/-!
# `RcicF8XValley` — the X tile's Stratum B worker, in a well-formed context (S3b)

S0 §5 (#7026), `S3_X_VALLEY_DESIGN.md`, cc's ruling of 2026-10-14 on #7035 (the Γ-unconditional
`JProc` has no supplier — `JTileS0.no_jproc_supplier` — H-J is `JProcWf`, Stratum B delivers the
additive sibling `XProcWf`), and the independent audit of 2026-10-14 on #7063/#7070: a GLOBAL
supplier field `J : ∀ R, JProcWf R` is itself uninhabited on this carrier (a childless `sorts`
literal cannot have a leaf-free endpoint typing), so every theorem quantified over such a bundle
was vacuous. The suppliers here are therefore **partial**: each may decline a request (`Option`),
its contract holds on its answers, a total supplier is a partial one (`…ofTotal`, so the sealed
contracts transfer), and the worker returns `Option` — a declined call is an explicit refusal.
`Suppliers.declining hsep` (the landed `ctxConvVar` as K, every J/D/U/S request declined)
inhabits `Suppliers E n` given `SepAll E n`, the one named Prop hypothesis S1 already carries;
the Stratum-A route consults no supplier, so it answers under it (S4, `xTile?_isSome_of_piSpined`).

The worker runs on the flattened, segmented input (S3a): a segment is one Π-spined link
(Stratum A, S1's `xStructTc`, unconditional) or a `bPrefix` — `ofCv` links whose lazy
conversion has no `esub` and weakens only at cutoff 0 — read by the valley route:

* `lit h`      → `J R hΓ h hsub` (the only J call; at the segment's own context, where
                 `hΓ` is the caller's);
* `refl D`     → the trivial valley `⟨a, refl D, refl D, D, D⟩`;
* `symm`       → `Valley.symm`;  `tyConv u' c cA` → `Valley.conv (ofCv u' cA)` (the index
                 chain is used whole; no J call inside it);
* `trans`      → the D-join of the two valleys at the shared middle (`EvParStar.trans`);
* `wk d 0 c`   → the valley of `c` at the tail context — `CtxWfT (d :: Γ₀)` inverts to
                 `CtxWfT Γ₀` (`ctxWfT_tail`) — then `Valley.wk`;
* consecutive links of a prefix: U aligns the two indices at the middle (`Valley.conv` by
  `symm (U ty₂ ty₁)`), then the D-join.

The prefix valley `W : Valley R Γ (.pi A B) (.pi A' B') T` is READ through `S`
(H-STRUCTPI, SP-1's `StructPiPayload`): every step of `W.left` out of a Π is a structural
step with components `hc : EvCv A A' (.sort u)`, `hcB : EvCv (A :: Γ) B B' (.sort v)`; the
components compose by `trans`, the codomains move along the domain chain by `K`
(`EvTc.wk` for `wk` steps, nothing for `conv` steps — the components ignore the index);
the two legs meet at `W.N` and the right leg is reversed.

**Where `CtxWfT` of each recursive context comes from (cc §3).** Every J call of this
module is at the caller's `Γ` (`hΓ`) or at the tail of a cutoff-0 weakening (`ctxWfT_tail`).
U, D, S, K and `xStructTc` take no context premise. The valley route never recurses into a
binder context; the consumer's binder context is supplied in S3c (`RcicF8XBinderWf`).

**Named walls (admissibility is the Bool `xAdm`; `false` is reported, never papered over):**
W-X-SUBST (a `subst0`/`substLet` link or an `esub` node in a Stratum-B position, S0 §5.6),
W-X-WK (a weakening at cutoff `k > 0` there: J needs `CtxWfT` of the un-weakened context, a
strengthening the tree lacks), and the sealed unconditional `XProc`'s Stratum-B part: no
supplier on this route (not proven false). A declined supplier request is the fourth, dynamic,
refusal (`none`), named by the call that declined.

Multiplicity (cc Q6): a re-wrapped link repeats shared leaves once per component; the
contract is `SubEq` membership, as sealed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### kit -/

theorem subEq_trans {x y z : Jd E n} (hxy : SubEq x y) (hyz : SubEq y z) : SubEq x z := by
  cases hyz with
  | inl heq => subst heq; exact hxy
  | inr hs => exact .inr (subEq_trans_subOf hxy hs)

/-- `ℓ` is `SubEq` some element of `L`: the bound shape of every sealed contract. -/
abbrev Below (ℓ : Jd E n) (L : List (Jd E n)) : Prop := ∃ ℓ' ∈ L, SubEq ℓ ℓ'

theorem below_of_mem {ℓ : Jd E n} {L : List (Jd E n)} (h : ℓ ∈ L) : Below ℓ L :=
  ⟨ℓ, h, .inl rfl⟩

theorem below_left {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Below ℓ L) : Below ℓ (L ++ L') := by
  obtain ⟨ℓ', hm, hs⟩ := h
  exact ⟨ℓ', List.mem_append.mpr (.inl hm), hs⟩

theorem below_right {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Below ℓ L') : Below ℓ (L ++ L') := by
  obtain ⟨ℓ', hm, hs⟩ := h
  exact ⟨ℓ', List.mem_append.mpr (.inr hm), hs⟩

theorem below_trans {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Below ℓ L)
    (hL : ∀ x ∈ L, Below x L') : Below ℓ L' := by
  obtain ⟨ℓ', hm, hs⟩ := h
  obtain ⟨ℓ'', hm', hs'⟩ := hL ℓ' hm
  exact ⟨ℓ'', hm', subEq_trans hs hs'⟩

theorem below_append_elim {ℓ : Jd E n} {L L' : List (Jd E n)} (h : Below ℓ (L ++ L')) :
    Below ℓ L ∨ Below ℓ L' := by
  obtain ⟨ℓ', hm, hs⟩ := h
  rcases List.mem_append.mp hm with hm | hm
  · exact .inl ⟨ℓ', hm, hs⟩
  · exact .inr ⟨ℓ', hm, hs⟩

/-- `isPi` is lift-invariant. -/
theorem isPi_lift (k m : Nat) : (e : Expr Nat) → isPi (lift k m e) = isPi e
  | .bvar _ => by simp only [lift]; split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the tail of a well-formed context is well-formed (the cutoff-0 weakening case). -/
def ctxWfT_tail : {d : LocalDecl} → {Γ : LCtx} → CtxWfT E n (d :: Γ) → CtxWfT E n Γ
  | _, _, .assumption _ _ _ hΓ _ => hΓ
  | _, _, .letBinding _ _ _ _ hΓ _ _ => hΓ

variable {Γ : LCtx}

theorem Valley.below_left {M₁ M₂ T : Expr Nat} (V : Valley R Γ M₁ M₂ T) {ℓ : Jd E n}
    (h : ℓ ∈ V.left.leaves) : ℓ ∈ V.leaves := by
  simp only [Valley.leaves, List.mem_append]; exact .inl (.inl (.inl h))

theorem Valley.below_right {M₁ M₂ T : Expr Nat} (V : Valley R Γ M₁ M₂ T) {ℓ : Jd E n}
    (h : ℓ ∈ V.right.leaves) : ℓ ∈ V.leaves := by
  simp only [Valley.leaves, List.mem_append]; exact .inl (.inl (.inr h))

theorem Valley.below_ty₁ {M₁ M₂ T : Expr Nat} (V : Valley R Γ M₁ M₂ T) {ℓ : Jd E n}
    (h : ℓ ∈ V.ty₁.leaves) : ℓ ∈ V.leaves := by
  simp only [Valley.leaves, List.mem_append]; exact .inl (.inr h)

theorem Valley.below_ty₂ {M₁ M₂ T : Expr Nat} (V : Valley R Γ M₁ M₂ T) {ℓ : Jd E n}
    (h : ℓ ∈ V.ty₂.leaves) : ℓ ∈ V.leaves := by
  simp only [Valley.leaves, List.mem_append]; exact .inr h

theorem XOut.below_fst {A₁ B₁ A₂ B₂ : Expr Nat} {o : XOut R Γ A₁ B₁ A₂ B₂} {L : List (Jd E n)}
    (bd : ∀ ℓ ∈ XOut.leaves o, Below ℓ L) {ℓ : Jd E n} (h : ℓ ∈ o.1.leaves) : Below ℓ L :=
  bd ℓ (List.mem_append.mpr (.inl h))

theorem XOut.below_snd {A₁ B₁ A₂ B₂ : Expr Nat} {o : XOut R Γ A₁ B₁ A₂ B₂} {L : List (Jd E n)}
    (bd : ∀ ℓ ∈ XOut.leaves o, Below ℓ L) {ℓ : Jd E n} (h : ℓ ∈ o.2.leaves) : Below ℓ L :=
  bd ℓ (List.mem_append.mpr (.inr h))

/-! ### H-STRUCTPI: reading a step out of a Π (SP-1's payload, reused) -/

/-- H-STRUCTPI: a provenance step out of a Π-shaped term is a Π-structural step, read as
    SP-1's payload (X uses `hc` and `hcB`). -/
abbrev StructPiProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B q T : Expr Nat}, EvPar R Γ (.pi A B) q T →
    Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T

/-- H-STRUCTPI's leaf contract: the two components cite only sub-derivations of the step. -/
def StructPiContract (S : ∀ R : List (Jd E n), StructPiProc R) : Prop :=
  ∀ R {Γ : LCtx} {A B q T : Expr Nat} (s : EvPar R Γ (.pi A B) q T),
    ∀ ℓ ∈ (S R s).2.2.2.hc.leaves ++ (S R s).2.2.2.hcB.leaves, ∃ ℓ' ∈ s.leaves, SubEq ℓ ℓ'

/-- non-vacuity of the shape: SP-1's own step is read by its payload. -/
def structPiSelf {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T) :
    Σ' (A₁ B₁ : Expr Nat), (Expr.pi A' B' : Expr Nat) = .pi A₁ B₁ ×'
      StructPiPayload R Γ A B A₁ B₁ T :=
  ⟨A', B', rfl, p⟩

theorem structPiSelf_contract {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T) :
    ∀ ℓ ∈ (structPiSelf p).2.2.2.hc.leaves ++ (structPiSelf p).2.2.2.hcB.leaves,
      ∃ ℓ' ∈ (EvPar.structPi p).leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  refine ⟨ℓ, ?_, .inl rfl⟩
  simp only [structPiSelf, EvPar.leaves, StructPiPayload.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with hℓ | hℓ
  · exact .inl (.inl (.inl (.inl (.inr hℓ))))
  · exact .inl (.inl (.inr hℓ))

/-! ### the suppliers at the module boundary — partial -/

/-- H-J, partial: a join for a bare `ConvT` literal certified into `R`, in a well-formed
    context, or a refusal. -/
abbrev JProcWfP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {M₁ M₂ T : Expr Nat}, CtxWfT E n Γ → (h : ConvT E n Γ M₁ M₂ T) →
    (∃ r ∈ R, SubEq (.cv h) r) → Option (Valley R Γ M₁ M₂ T)

/-- H-J's strict leaf contract on answers. -/
def JContractWfP (J : ∀ R : List (Jd E n), JProcWfP R) : Prop :=
  ∀ R {Γ : LCtx} {M₁ M₂ T : Expr Nat} (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ M₁ M₂ T)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) (V : Valley R Γ M₁ M₂ T),
    J R hΓ h hsub = some V → ∀ ℓ ∈ V.leaves, SubOf ℓ (.cv h)

/-- H-D, partial. -/
abbrev DProcP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, EvParStar R Γ a b T → EvParStar R Γ a c T →
    Option (Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T)

def DContractP (D : ∀ R : List (Jd E n), DProcP R) : Prop :=
  ∀ R {Γ : LCtx} {a b c T : Expr Nat} (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T)
    (r : Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T),
    D R h₁ h₂ = some r → ∀ ℓ ∈ r.2.1.leaves ++ r.2.2.leaves, ∃ ℓ' ∈ h₁.leaves ++ h₂.leaves, SubEq ℓ ℓ'

/-- U, partial. -/
abbrev UProcP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a A B : Expr Nat}, EvTy R Γ a A → EvTy R Γ a B → Option (EvTc R Γ A B)

def UContractP (U : ∀ R : List (Jd E n), UProcP R) : Prop :=
  ∀ R {Γ : LCtx} {a A B : Expr Nat} (l : EvTy R Γ a A) (r : EvTy R Γ a B) (u : EvTc R Γ A B),
    U R l r = some u → ∀ ℓ ∈ u.leaves, ∃ ℓ' ∈ l.leaves ++ r.leaves, SubEq ℓ ℓ'

/-- H-STRUCTPI, partial. -/
abbrev StructPiProcP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B q T : Expr Nat}, EvPar R Γ (.pi A B) q T →
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T)

def StructPiContractP (S : ∀ R : List (Jd E n), StructPiProcP R) : Prop :=
  ∀ R {Γ : LCtx} {A B q T : Expr Nat} (s : EvPar R Γ (.pi A B) q T)
    (r : Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T),
    S R s = some r → ∀ ℓ ∈ r.2.2.2.hc.leaves ++ r.2.2.2.hcB.leaves, ∃ ℓ' ∈ s.leaves, SubEq ℓ ℓ'

/-! total suppliers are partial ones: the sealed contracts transfer. -/

def JProcWfP.ofTotal (J : ∀ R : List (Jd E n), JProcWf R) : ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hsub => some (J R hΓ h hsub)

theorem JContractWfP.ofTotal {J : ∀ R : List (Jd E n), JProcWf R} (hJ : JContractWf J) :
    JContractWfP (JProcWfP.ofTotal J) := by
  intro R Γ M₁ M₂ T hΓ h hsub V hV
  simp only [JProcWfP.ofTotal, Option.some.injEq] at hV
  subst hV
  exact hJ R hΓ h hsub

def DProcP.ofTotal (D : ∀ R : List (Jd E n), DProc R) : ∀ R : List (Jd E n), DProcP R :=
  fun R {_ _ _ _ _} h₁ h₂ => some (D R h₁ h₂)

theorem DContractP.ofTotal {D : ∀ R : List (Jd E n), DProc R} (hD : DContract D) :
    DContractP (DProcP.ofTotal D) := by
  intro R Γ a b c T h₁ h₂ r hr
  simp only [DProcP.ofTotal, Option.some.injEq] at hr
  subst hr
  exact hD R h₁ h₂

def UProcP.ofTotal (U : ∀ R : List (Jd E n), UProc R) : ∀ R : List (Jd E n), UProcP R :=
  fun R {_ _ _ _} l r => some (U R l r)

theorem UContractP.ofTotal {U : ∀ R : List (Jd E n), UProc R} (hU : UContract U) :
    UContractP (UProcP.ofTotal U) := by
  intro R Γ a A B l r u hu
  simp only [UProcP.ofTotal, Option.some.injEq] at hu
  subst hu
  exact hU R l r

def StructPiProcP.ofTotal (S : ∀ R : List (Jd E n), StructPiProc R) :
    ∀ R : List (Jd E n), StructPiProcP R :=
  fun R {_ _ _ _ _} s => some (S R s)

theorem StructPiContractP.ofTotal {S : ∀ R : List (Jd E n), StructPiProc R}
    (hS : StructPiContract S) : StructPiContractP (StructPiProcP.ofTotal S) := by
  intro R Γ A B q T s r hr
  simp only [StructPiProcP.ofTotal, Option.some.injEq] at hr
  subst hr
  exact hS R s

/-- the landed and named hypotheses X's Stratum B calls, partial; `K` is total (the landed
    `ctxConvVar` inhabits it). -/
structure Suppliers (E : ResolvedEnv) (n : Nat) where
  K : ∀ R : List (Jd E n), CtxConvProc R
  hK : CtxConvContract K
  hsep : SepAll E n
  J : ∀ R : List (Jd E n), JProcWfP R
  hJ : JContractWfP J
  D : ∀ R : List (Jd E n), DProcP R
  hD : DContractP D
  U : ∀ R : List (Jd E n), UProcP R
  hU : UContractP U
  S : ∀ R : List (Jd E n), StructPiProcP R
  hS : StructPiContractP S

/-- Operational callbacks used by the strict valley helpers. -/
structure ValleyOps (E : ResolvedEnv) (n : Nat) where
  K : ∀ R : List (Jd E n), CtxConvProc R
  hK : CtxConvContract K
  D : ∀ R : List (Jd E n), DProcP R
  hD : DContractP D
  U : ∀ R : List (Jd E n), UProcP R
  hU : UContractP U
  S : ∀ R : List (Jd E n), StructPiProcP R
  hS : StructPiContractP S


def Suppliers.toValleyOps (X : Suppliers E n) : ValleyOps E n where
  K := X.K
  hK := X.hK
  D := X.D
  hD := X.hD
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-- the suppliers that decline every J/D/U/S request, with the landed `ctxConvVar` as K: the
    bundle is inhabited given `SepAll E n` (S1's named hypothesis), so nothing below is vacuous. -/
def Suppliers.declining (hsep : SepAll E n) : Suppliers E n where
  K := fun _ {_ _ _ _ _} cA e => ctxConvVar cA e
  hK := fun _ {_ _ _ _ _} cA e => ctxConvVar_contract cA e
  hsep := hsep
  J := fun _ {_ _ _ _} _ _ _ => none
  hJ := fun _ {_ _ _ _} _ _ _ _ h => nomatch h
  D := fun _ {_ _ _ _ _} _ _ => none
  hD := fun _ {_ _ _ _ _} _ _ _ h => nomatch h
  U := fun _ {_ _ _ _} _ _ => none
  hU := fun _ {_ _ _ _} _ _ _ h => nomatch h
  S := fun _ {_ _ _ _ _} _ => none
  hS := fun _ {_ _ _ _ _} _ _ h => nomatch h

/-- a leaf-bounded valley. -/
abbrev BValley (R : List (Jd E n)) (Γ : LCtx) (M₁ M₂ T : Expr Nat) (L : List (Jd E n)) : Type :=
  Σ' V : Valley R Γ M₁ M₂ T, ∀ ℓ ∈ V.leaves, Below ℓ L

/-! ### joining valleys -/

/-- two valleys at a common index, joined by D at the shared endpoint (S0 §5.1 step 3), or a
    refusal. -/
def joinValley (X : Suppliers E n) {a b c T : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (V₁ : BValley R Γ a b T L₁) (V₂ : BValley R Γ b c T L₂) :
    Option (BValley R Γ a c T (L₁ ++ L₂)) :=
  match hd : X.D R V₁.1.right V₂.1.left with
  | none => none
  | some d => some ⟨⟨d.1, .trans V₁.1.left d.2.1, .trans V₂.1.right d.2.2, V₁.1.ty₁, V₂.1.ty₂⟩,
      fun ℓ hℓ => by
        have hlegs : ∀ x ∈ d.2.1.leaves ++ d.2.2.leaves, Below x (L₁ ++ L₂) := fun x hx =>
          below_trans (X.hD R V₁.1.right V₂.1.left d hd x hx) (fun y hy => by
            rcases List.mem_append.mp hy with hy | hy
            · exact below_left (V₁.2 y (V₁.1.below_right hy))
            · exact below_right (V₂.2 y (V₂.1.below_left hy)))
        simp only [Valley.leaves, EvParStar.leaves, List.mem_append] at hℓ
        rcases hℓ with (((hℓ | hℓ) | (hℓ | hℓ)) | hℓ) | hℓ
        · exact below_left (V₁.2 ℓ (V₁.1.below_left hℓ))
        · exact hlegs ℓ (List.mem_append.mpr (.inl hℓ))
        · exact below_right (V₂.2 ℓ (V₂.1.below_right hℓ))
        · exact hlegs ℓ (List.mem_append.mpr (.inr hℓ))
        · exact below_left (V₁.2 ℓ (V₁.1.below_ty₁ hℓ))
        · exact below_right (V₂.2 ℓ (V₂.1.below_ty₂ hℓ))⟩

/-- two valleys at different indices: U aligns the second to the first at the shared
    endpoint (S0 §5.1 step 2), then the D-join; or a refusal. -/
def alignJoin (X : Suppliers E n) {a b c T₁ T₂ : Expr Nat} {L₁ L₂ : List (Jd E n)}
    (V₁ : BValley R Γ a b T₁ L₁) (V₂ : BValley R Γ b c T₂ L₂) :
    Option (BValley R Γ a c T₁ (L₁ ++ L₂)) :=
  match hu : X.U R V₁.1.ty₂ V₂.1.ty₁ with
  | none => none
  | some u =>
      let V₂' : BValley R Γ b c T₁ (L₁ ++ L₂) := ⟨V₂.1.conv (.symm u), fun ℓ hℓ => by
        rcases List.mem_append.mp (V₂.1.conv_leaves (.symm u) ℓ hℓ) with hℓ | hℓ
        · exact below_right (V₂.2 ℓ hℓ)
        · have hℓ' : ℓ ∈ u.leaves := by simpa only [EvTc.leaves] using hℓ
          exact below_trans (X.hU R V₁.1.ty₂ V₂.1.ty₁ u hu ℓ hℓ') (fun y hy => by
            rcases List.mem_append.mp hy with hy | hy
            · exact below_left (V₁.2 y (V₁.1.below_ty₂ hy))
            · exact below_right (V₂.2 y (V₂.1.below_ty₁ hy)))⟩
      (joinValley X V₁ V₂').map (fun r => ⟨r.1, fun ℓ hℓ => by
        rcases below_append_elim (r.2 ℓ hℓ) with h | h
        · exact below_left h
        · exact h⟩)

/-! ### the valley of a link -/

/-- the valley of a lazy conversion with no `esub` and cutoff-0 weakenings only, in a
    well-formed context: J on the literal, `Valley` operations on the rest; or a refusal. -/
def valleyCv (X : Suppliers E n) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    CtxWfT E n Γ → bCv c = true → Option (BValley R Γ a b T c.leaves)
  | _, _, _, _, .lit h hsub, hΓ, _ =>
      match hJ : X.J R hΓ h hsub with
      | none => none
      | some V => some ⟨V, fun ℓ hℓ =>
          ⟨.cv h, by simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil, or_false],
            .inr (X.hJ R hΓ h hsub V hJ ℓ hℓ)⟩⟩
  | _, _, _, _, .refl Dt, _, _ =>
      some ⟨⟨_, .refl Dt, .refl Dt, Dt, Dt⟩, fun ℓ hℓ => by
        simp only [Valley.leaves, EvParStar.leaves, List.mem_append, or_self] at hℓ
        simp only [EvCv.leaves]
        exact below_of_mem hℓ⟩
  | _, _, _, _, .symm c, hΓ, h =>
      (valleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.symm, fun ℓ hℓ => by simpa only [EvCv.leaves] using r.2 ℓ (r.1.symm_leaves ℓ hℓ)⟩)
  | _, _, _, _, .trans c₁ c₂, hΓ, h =>
      have h' : bCv c₁ = true ∧ bCv c₂ = true := by
        simpa only [bCv, Bool.and_eq_true] using h
      match valleyCv X c₁ hΓ h'.1, valleyCv X c₂ hΓ h'.2 with
      | some r₁, some r₂ =>
          (joinValley X r₁ r₂).map (fun r =>
            ⟨r.1, fun ℓ hℓ => by simpa only [EvCv.leaves] using r.2 ℓ hℓ⟩)
      | _, _ => none
  | _, _, _, _, .tyConv u' c cA, hΓ, h =>
      (valleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.conv (.ofCv u' cA), fun ℓ hℓ => by
          simp only [EvCv.leaves]
          rcases List.mem_append.mp (r.1.conv_leaves (.ofCv u' cA) ℓ hℓ) with hℓ | hℓ
          · exact below_left (r.2 ℓ hℓ)
          · exact below_right (below_of_mem (by simpa only [EvTc.leaves] using hℓ))⟩)
  | _, _, _, _, .rety c cA, hΓ, h =>
      (valleyCv X c hΓ (by simpa only [bCv] using h)).map (fun r =>
        ⟨r.1.conv cA, fun ℓ hℓ => by
          simp only [EvCv.leaves]
          rcases List.mem_append.mp (r.1.conv_leaves cA ℓ hℓ) with hℓ | hℓ
          · exact below_left (r.2 ℓ hℓ)
          · exact below_right (below_of_mem hℓ)⟩)
  | _, _, _, _, @EvCv.wk _ _ _ Γ₀ a₀ b₀ T₀ d k c, hΓ, h => by
      cases k with
      | zero =>
          exact (valleyCv X c (ctxWfT_tail hΓ) (by simpa only [bCv] using h)).map (fun r =>
            ⟨r.1.wk d 0, fun ℓ hℓ => by
              rw [Valley.wk_leaves] at hℓ
              simpa only [EvCv.leaves] using r.2 ℓ hℓ⟩)
      | succ k => exact nomatch h
  | _, _, _, _, .esub .., _, h => nomatch h
  | _, _, _, _, .subst0 .., _, h => nomatch h
  | _, _, _, _, .substLet .., _, h => nomatch h
  | _, _, _, _, .sorts .., _, h => nomatch h
  | _, _, _, _, .consts .., _, h => nomatch h

/-- the valley of a `bLink`, with its index; or a refusal. -/
def linkValley (X : Suppliers E n) : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    CtxWfT E n Γ → bLink l = true → Option (Σ' T : Expr Nat, BValley R Γ A B T l.leaves)
  | _, _, _, .ofCv u c, hΓ, hb =>
      (valleyCv X c hΓ (by simpa only [bLink] using hb)).map (fun r =>
        ⟨.sort u, r.1, fun ℓ hℓ => by simpa only [EvTc.leaves] using r.2 ℓ hℓ⟩)
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k l, hΓ, hb => by
      cases k with
      | zero =>
          exact (linkValley X l (ctxWfT_tail hΓ) (by simpa only [bLink] using hb)).map (fun r =>
            ⟨lift 0 1 r.1, r.2.1.wk d 0, fun ℓ hℓ => by
              rw [Valley.wk_leaves] at hℓ
              simpa only [EvTc.leaves] using r.2.2 ℓ hℓ⟩)
      | succ k => exact nomatch hb
  | _, _, _, .piCod .., _, hb => nomatch hb
  | _, _, _, .subst0 .., _, hb => nomatch hb
  | _, _, _, .substLet .., _, hb => nomatch hb
  | _, _, _, .lit .., _, hb => nomatch hb
  | _, _, _, .refl .., _, hb => nomatch hb
  | _, _, _, .symm .., _, hb => nomatch hb
  | _, _, _, .trans .., _, hb => nomatch hb

/-- the valley of a nonempty `bPrefix`: link valleys, U-aligned and D-joined left to right; or
    a refusal. -/
def prefixValley (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P M B : Expr Nat} →
    (l : EvTc R Γ P M) → bLink l = true → (rest : Flat R Γ M B) → rest.bPrefix = true →
    Option (Σ' T : Expr Nat, BValley R Γ P B T (l.leaves ++ rest.leaves))
  | _, _, _, l, hb, .nil _, _ =>
      (linkValley X l hΓ hb).map (fun r => ⟨r.1, r.2.1, fun ℓ hℓ => below_left (r.2.2 ℓ hℓ)⟩)
  | _, _, _, l, hb, .cons l' hl' rest', hb' =>
      have h' : bLink l' = true ∧ rest'.bPrefix = true := by
        simpa only [Flat.bPrefix, Bool.and_eq_true] using hb'
      match linkValley X l hΓ hb, prefixValley X hΓ l' h'.1 rest' h'.2 with
      | some r₁, some r₂ =>
          (alignJoin X r₁.2 r₂.2).map (fun r =>
            ⟨r₁.1, r.1, fun ℓ hℓ => by simpa only [Flat.leaves] using r.2 ℓ hℓ⟩)
      | _, _ => none

/-! ### reading a valley at Π endpoints (S0 §5.3) -/

/-- walk a provenance star out of a Π-shaped term: every step through `S`, the components
    composed by `trans` and `K`; the index is irrelevant, `wk` is pushed onto the components,
    a lazy `subst0`/`substLet` (W-X-SUBST S0 §5) is pushed onto the components as the lazy
    `EvTc.subst0`/`substLet` links (the codomain's one binder deeper) when the source was a Π;
    or a refusal (S declined a step; or the substituted VARIABLE was the Π — named
    `[x_read_subst_var]`: no component walk exists for a star that starts at the hole). -/
def readStar (X : Suppliers E n) : {Γ : LCtx} → {p q T : Expr Nat} → (hs : EvParStar R Γ p q T) →
    ∀ {A B : Expr Nat}, p = .pi A B →
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×'
      Σ' o : XOut R Γ A B A' B', ∀ ℓ ∈ XOut.leaves o, Below ℓ hs.leaves)
  | _, _, _, _, @EvParStar.refl _ _ _ Γ a T h, A, B, hp => by
      subst hp
      exact some ⟨A, B, rfl, (.refl Γ A, .refl _ B), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ⟩
  | _, _, _, _, @EvParStar.tail _ _ _ Γ a b c T h hs, A, B, hp => by
      let h' : EvPar R Γ (.pi A B) b T := hp ▸ h
      rcases hS : X.S R h' with _ | ⟨A₁, B₁, hb, pay⟩
      · exact none
      · rcases readStar X hs hb with _ | ⟨A', B', hq, o₂, bd₂⟩
        · exact none
        · have hpay : ∀ ℓ ∈ pay.hc.leaves ++ pay.hcB.leaves, Below ℓ h.leaves := by
            have := X.hS R h' _ hS
            subst hp
            exact this
          refine some ⟨A', B', hq, (.trans (.ofCv pay.u pay.hc) o₂.1,
            .trans (.ofCv pay.v pay.hcB) (X.K R (.ofCv pay.u pay.hc) o₂.2)), fun ℓ hℓ => ?_⟩
          simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
          simp only [EvParStar.leaves]
          rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
          · exact below_left (hpay ℓ (List.mem_append.mpr (.inl hℓ)))
          · exact below_right (XOut.below_fst bd₂ hℓ)
          · exact below_left (hpay ℓ (List.mem_append.mpr (.inr hℓ)))
          · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
            · exact below_left (hpay ℓ (List.mem_append.mpr (.inl (by simpa only [EvTc.leaves] using hℓ))))
            · exact below_right (XOut.below_snd bd₂ hℓ)
  | _, _, _, _, @EvParStar.conv _ _ _ Γ a b T T' hs c, A, B, hp => by
      rcases readStar X hs hp with _ | ⟨A', B', hq, o, bd⟩
      · exact none
      · exact some ⟨A', B', hq, o, fun ℓ hℓ => by
          simp only [EvParStar.leaves]
          exact below_left (bd ℓ hℓ)⟩
  | _, _, _, _, @EvParStar.wk _ _ _ Γ a b T d k hs, A, B, hp => by
      have ha : isPi a = true := by
        have := isPi_lift k 1 a
        rw [hp] at this
        exact this.symm
      obtain ⟨A₀, B₀, ha'⟩ := isPiD a ha
      rcases readStar X hs ha' with _ | ⟨A₀', B₀', hb, o₀, bd₀⟩
      · exact none
      · subst ha'
        subst hb
        have hp' : Expr.pi (lift k 1 A₀) (lift (k + 1) 1 B₀) = .pi A B := hp
        injection hp' with h1 h2
        subst h1; subst h2
        exact some ⟨lift k 1 A₀', lift (k + 1) 1 B₀', rfl, (.wk d k o₀.1, .wk d (k + 1) o₀.2),
          fun ℓ hℓ => by
            simp only [XOut.leaves, EvTc.leaves] at hℓ
            simp only [EvParStar.leaves]
            exact bd₀ ℓ hℓ⟩
  | _, _, _, _, @EvParStar.trans _ _ _ Γ a b c T h₁ h₂, A, B, hp => by
      rcases readStar X h₁ hp with _ | ⟨A₁, B₁, hm, o₁, bd₁⟩
      · exact none
      · rcases readStar X h₂ hm with _ | ⟨A', B', hq, o₂, bd₂⟩
        · exact none
        · refine some ⟨A', B', hq, (.trans o₁.1 o₂.1, .trans o₁.2 (X.K R o₁.1 o₂.2)), fun ℓ hℓ => ?_⟩
          simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
          simp only [EvParStar.leaves]
          rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
          · exact below_left (XOut.below_fst bd₁ hℓ)
          · exact below_right (XOut.below_fst bd₂ hℓ)
          · exact below_left (XOut.below_snd bd₁ hℓ)
          · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
            · exact below_left (XOut.below_fst bd₁ hℓ)
            · exact below_right (XOut.below_snd bd₂ hℓ)
  | _, _, _, _, @EvParStar.subst0 _ _ _ Γ a b T t v j hs hget hv, A, B, hp => by
      obtain (⟨A₀, B₀, h₁, hA, hB⟩ | ⟨_, _⟩) := instShape_pi hp
      · subst hA; subst hB
        rcases readStar X hs h₁ with _ | ⟨A₀', B₀', hq, o₀, bd₀⟩
        · exact none
        · subst hq
          refine some ⟨instantiate j (lift 0 j v) A₀',
            instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀', rfl,
            (.subst0 j o₀.1 hget hv,
             EvTc.cast rfl
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
               (.subst0 (j + 1) o₀.2 (by simpa using hget)
                 (substBinderArg (d := .assumption A₀) hv))),
            fun ℓ hℓ => ?_⟩
          simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
            List.mem_append] at hℓ
          simp only [EvParStar.leaves]
          rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
          · exact below_left (XOut.below_fst bd₀ hℓ)
          · exact below_right (below_of_mem hℓ)
          · exact below_left (XOut.below_snd bd₀ hℓ)
          · exact below_right (below_of_mem hℓ)
      · exact none
  | _, _, _, _, @EvParStar.substLet _ _ _ Γ a b T t w j hs hget hv, A, B, hp => by
      obtain (⟨A₀, B₀, h₁, hA, hB⟩ | ⟨_, _⟩) := instShape_pi hp
      · subst hA; subst hB
        rcases readStar X hs h₁ with _ | ⟨A₀', B₀', hq, o₀, bd₀⟩
        · exact none
        · subst hq
          refine some ⟨instantiate j (lift 0 j w) A₀',
            instantiate (j + 1) (lift 0 1 (lift 0 j w)) B₀', rfl,
            (.substLet j o₀.1 hget hv,
             EvTc.cast rfl
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
               (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
               (.substLet (j + 1) o₀.2 (by simpa using hget)
                 (substBinderArg (d := .assumption A₀) hv))),
            fun ℓ hℓ => ?_⟩
          simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
            List.mem_append] at hℓ
          simp only [EvParStar.leaves]
          rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
          · exact below_left (XOut.below_fst bd₀ hℓ)
          · exact below_right (below_of_mem hℓ)
          · exact below_left (XOut.below_snd bd₀ hℓ)
          · exact below_right (below_of_mem hℓ)
      · exact none

/-- the components of a valley between two Π's: both legs read to the common `N`, the right
    leg reversed, the codomains moved along the domain chain by `K`; or a refusal. -/
def readValley (X : Suppliers E n) {A B A' B' T : Expr Nat}
    (W : Valley R Γ (.pi A B) (.pi A' B') T) :
    Option (Σ' o : XOut R Γ A B A' B', ∀ ℓ ∈ XOut.leaves o, Below ℓ W.leaves) := by
  rcases readStar X W.left rfl with _ | ⟨AN, BN, hN, oL, bdL⟩
  · exact none
  · rcases readStar X W.right rfl with _ | ⟨AN', BN', hN', oR, bdR⟩
    · exact none
    · have hNN : Expr.pi AN BN = .pi AN' BN' := hN.symm.trans hN'
      injection hNN with h1 h2
      subst h1; subst h2
      refine some ⟨(.trans oL.1 (.symm oR.1),
        .trans oL.2 (X.K R (.trans oL.1 (.symm oR.1)) (.symm oR.2))), fun ℓ hℓ => ?_⟩
      have hL : ∀ x ∈ W.left.leaves, Below x W.leaves := fun x hx => below_of_mem (W.below_left hx)
      have hR : ∀ x ∈ W.right.leaves, Below x W.leaves := fun x hx => below_of_mem (W.below_right hx)
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · exact below_trans (XOut.below_fst bdL hℓ) hL
      · exact below_trans (XOut.below_fst bdR hℓ) hR
      · exact below_trans (XOut.below_snd bdL hℓ) hL
      · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
        · simp only [EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hℓ | hℓ
          · exact below_trans (XOut.below_fst bdL hℓ) hL
          · exact below_trans (XOut.below_fst bdR hℓ) hR
        · exact below_trans (XOut.below_snd bdR (by simpa only [EvTc.leaves] using hℓ)) hR

/-! ### segments -/

/-- a segment is admissible when it is one Π-spined link (Stratum A) or one valley link, or a
    longer `bPrefix`. -/
def Flat.segAdm : {P M : Expr Nat} → Flat R Γ P M → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ (.nil _) => piSpinedTc l || bLink l
  | _, _, .cons l _ (.cons l' hl' rest') => bLink l && (Flat.cons l' hl' rest').bPrefix

/-- the segments of a flat chain: prefixes cut at Π-shaped types. -/
inductive Segs (R : List (Jd E n)) (Γ : LCtx) : Expr Nat → Expr Nat → Type where
  | nil (Q : Expr Nat) : Segs R Γ Q Q
  | cons {P M Q : Expr Nat} (p : Flat R Γ P M) (hM : isPi M = true) (rest : Segs R Γ M Q) :
      Segs R Γ P Q

def Segs.leaves : {P Q : Expr Nat} → Segs R Γ P Q → List (Jd E n)
  | _, _, .nil _ => []
  | _, _, .cons p _ rest => p.leaves ++ rest.leaves

def Segs.adm : {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, .nil _ => true
  | _, _, .cons p _ rest => p.segAdm && rest.adm

/-- segmentation by iterated `splitPi`, fuelled by the length (structural; with the fuel
    exhausted the remainder is one segment, so leaves are preserved for ANY fuel). -/
def Flat.segmentF : Nat → {P Q : Expr Nat} → (f : Flat R Γ P Q) → isPi Q = true → Segs R Γ P Q
  | _, _, _, .nil _, _ => .nil _
  | 0, _, _, .cons l hl rest, hQ => .cons (.cons l hl rest) hQ (.nil _)
  | N + 1, _, _, .cons l hl rest, hQ =>
      let s := (Flat.cons l hl rest).splitPi hQ
      .cons s.2.2.1 s.2.1 (Flat.segmentF N s.2.2.2 hQ)

theorem Flat.segmentF_leaves : (N : Nat) → {P Q : Expr Nat} → (f : Flat R Γ P Q) →
    (hQ : isPi Q = true) → (Flat.segmentF N f hQ).leaves = f.leaves
  | 0, _, _, .nil _, _ => rfl
  | _ + 1, _, _, .nil _, _ => rfl
  | 0, _, _, .cons _ _ _, _ => by simp only [Flat.segmentF, Segs.leaves, List.append_nil]
  | N + 1, _, _, .cons l hl rest, hQ => by
      simp only [Flat.segmentF, Segs.leaves, Flat.segmentF_leaves N, Flat.splitPi_leaves]

/-- the segments of a flat chain. -/
def Flat.segment {P Q : Expr Nat} (f : Flat R Γ P Q) (hQ : isPi Q = true) : Segs R Γ P Q :=
  Flat.segmentF f.length f hQ

theorem Flat.segment_leaves {P Q : Expr Nat} (f : Flat R Γ P Q) (hQ : isPi Q = true) :
    (f.segment hQ).leaves = f.leaves :=
  Flat.segmentF_leaves f.length f hQ

/-- the bounded output of a segment or of the whole tile. -/
abbrev BOut (R : List (Jd E n)) (Γ : LCtx) (A B A' B' : Expr Nat) (L : List (Jd E n)) : Type :=
  Σ' o : XOut R Γ A B A' B', ∀ ℓ ∈ XOut.leaves o, Below ℓ L

/-- X on one segment between two Π's, or a refusal: a single Π-spined link goes to Stratum A
    (no supplier consulted); otherwise the valley route. -/
def xSeg (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P M : Expr Nat} → (p : Flat R Γ P M) →
    p.segAdm = true → ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (BOut R Γ A B A' B' p.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hM => by
      subst hP
      injection hM with h1 h2
      subst h1; subst h2
      exact some ⟨(.refl _ _, .refl _ _), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ⟩
  | _, _, .cons l hl (.nil _), hadm, A, B, A', B', hP, hM =>
      if hp : piSpinedTc l = true then
        some ⟨xStructTc X.K X.hK X.hsep l hp hP hM, fun ℓ hℓ => by
          simp only [Flat.leaves, List.append_nil]
          exact xStructTc_leaves X.K X.hK X.hsep l hp hP hM ℓ hℓ⟩
      else
        have hb : bLink l = true := by
          have h' : (piSpinedTc l || bLink l) = true := by simpa only [Flat.segAdm] using hadm
          simpa only [Bool.or_eq_true, hp, Bool.false_eq_true, false_or] using h'
        match linkValley X l hΓ hb with
        | none => none
        | some ⟨T, V, bdV⟩ => by
            subst hP; subst hM
            rcases readValley X V with _ | ⟨o, bd⟩
            · exact none
            · refine some ⟨o, fun ℓ hℓ => ?_⟩
              simp only [Flat.leaves, List.append_nil]
              exact below_trans (bd ℓ hℓ) bdV
  | _, _, .cons l hl (.cons l' hl' rest'), hadm, A, B, A', B', hP, hM =>
      have h' : bLink l = true ∧ (Flat.cons l' hl' rest').bPrefix = true := by
        simpa only [Flat.segAdm, Bool.and_eq_true] using hadm
      match prefixValley X hΓ l h'.1 (Flat.cons l' hl' rest') h'.2 with
      | none => none
      | some ⟨T, V, bdV⟩ => by
          subst hP; subst hM
          rcases readValley X V with _ | ⟨o, bd⟩
          · exact none
          · refine some ⟨o, fun ℓ hℓ => ?_⟩
            exact below_trans (bd ℓ hℓ) (fun x hx => by simpa only [Flat.leaves] using bdV x hx)

/-- X on the segments: components by `trans`, codomains moved by `K`; or a refusal. -/
def xSegs (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    s.adm = true → ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (BOut R Γ A B A' B' s.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hQ => by
      subst hP
      injection hQ with h1 h2
      subst h1; subst h2
      exact some ⟨(.refl _ _, .refl _ _), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil, List.not_mem_nil] at hℓ⟩
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, A, B, A', B', hP, hQ =>
      have h' : p.segAdm = true ∧ rest.adm = true := by
        simpa only [Segs.adm, Bool.and_eq_true] using hadm
      match isPiD M hM with
      | ⟨A₁, B₁, hM'⟩ =>
        match xSeg X hΓ p h'.1 hP hM', xSegs X hΓ rest h'.2 hM' hQ with
        | some ⟨o₁, bd₁⟩, some ⟨o₂, bd₂⟩ =>
            some ⟨(.trans o₁.1 o₂.1, .trans o₁.2 (X.K R o₁.1 o₂.2)), fun ℓ hℓ => by
              simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
              simp only [Segs.leaves]
              rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
              · exact below_left (XOut.below_fst bd₁ hℓ)
              · exact below_right (XOut.below_fst bd₂ hℓ)
              · exact below_left (XOut.below_snd bd₁ hℓ)
              · rcases List.mem_append.mp (X.hK R _ _ ℓ hℓ) with hℓ | hℓ
                · exact below_left (XOut.below_fst bd₁ hℓ)
                · exact below_right (XOut.below_snd bd₂ hℓ)⟩
        | _, _ => none

/-! ### the Stratum-B X -/

/-- admissibility of an X input under the current carrier: every segment is Stratum A or a
    valley prefix (`false` = W-X-SUBST / W-X-WK, reported). -/
def xAdm {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) : Bool :=
  ((flattenTc c).segment rfl).adm

/-- `XProcWf`'s shape on admissible inputs, bounded: the answer, or a refusal (a supplier
    declined). -/
def xValley? (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) : Option (BOut R Γ A B A' B' c.leaves) :=
  (xSegs X hΓ ((flattenTc c).segment rfl) hadm rfl rfl).map (fun r =>
    ⟨r.1, fun ℓ hℓ => by
      have bd := r.2 ℓ hℓ
      rw [Flat.segment_leaves] at bd
      exact below_trans bd (fun x hx => flattenTc_leaves c x hx)⟩)

/-- the components. -/
def xValley (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) :
    Option (EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B') :=
  (xValley? X hΓ c hadm).map (·.1)

/-- `XContractWf`'s clause on every answer. -/
theorem xValley_contract (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true)
    (o : EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B') (ho : xValley X hΓ c hadm = some o) :
    ∀ ℓ ∈ o.1.leaves ++ o.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  simp only [xValley, Option.map_eq_some'] at ho
  obtain ⟨r, _, rfl⟩ := ho
  exact r.2 ℓ hℓ

/-! ### pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the β-redex middle's two links form one admissible valley segment. -/
theorem pin_betaTwoLinks_segAdm : betaTwoLinks.segAdm = true := by
  simp only [betaTwoLinks, Flat.segAdm, Flat.bPrefix, betaLink₁, betaLink₂, bLink, bCv,
    Bool.and_self, Bool.and_true]

/-- the β fixture is an admissible X input: one Stratum-B segment (`Π ≡ redex ≡ Π`). -/
theorem pin_betaMiddle_xAdm :
    xAdm (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX) = true := by
  simp only [xAdm, betaMiddleT, flattenTc, flattenT, Flat.append, Flat.segment, Flat.segmentF,
    Flat.length, Flat.splitPi, Segs.adm, Flat.segAdm, Flat.bPrefix, bLink, bCv, Bool.and_self,
    Bool.and_true, Bool.true_and]

/-- the etaK fixture's request is an admissible X input: one Stratum-A segment. -/
theorem pin_request_xAdm : xAdm request = true := by
  simp only [xAdm, request, annotRequest, cL, cR, piConversion, flattenTc, flattenT,
    Flat.append, Flat.symm, linkSymm, Flat.segment, Flat.segmentF, Flat.length, Flat.splitPi,
    Segs.adm, Flat.segAdm, piSpinedTc, piSpinedCv, piSpinedConv, Bool.true_or, Bool.and_true,
    Bool.true_and]

/-- negative control (W-X-SUBST): a substitution link heading a longer segment is inadmissible. -/
theorem pin_segAdm_subst_false {Γ₀ : LCtx} {A₀ A₀' t v : Expr Nat} (j : Nat)
    (c : EvTc R Γ₀ A₀ A₀') (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)) (hl : isLink (EvTc.subst0 j c hget hv) = true)
    {M B : Expr Nat} (l' : EvTc R (substRemove v j Γ₀) (instantiate j (lift 0 j v) A₀') M)
    (hl' : isLink l' = true) (rest' : Flat R (substRemove v j Γ₀) M B) :
    (Flat.cons (EvTc.subst0 j c hget hv) hl (Flat.cons l' hl' rest')).segAdm = false := rfl

/-- negative control (W-X-WK): a weakening at cutoff `k+1` is not a valley link. -/
theorem pin_bLink_wk_succ_false {Γ₀ : LCtx} {A B : Expr Nat} (d : LocalDecl) (k : Nat)
    (l : EvTc R Γ₀ A B) : bLink (EvTc.wk d (k + 1) l) = false := rfl

/-- while a cutoff-0 weakening of a valley link is one. -/
theorem pin_bLink_wk_zero (d : LocalDecl) : bLink (EvTc.wk d 0 betaLink₁) = true := rfl

/-- the declining suppliers refuse the β valley segment (`betaTwoLinks`, S3a): its first link's
    literal is a J request, which is declined — an explicit refusal, never a stale answer. -/
theorem pin_betaTwoLinks_declined (hsep : SepAll emptyEnv 0) :
    xSegs (Suppliers.declining hsep) CtxWfT.nil (Segs.cons betaTwoLinks rfl (Segs.nil piX))
      (by decide) rfl rfl = none := rfl

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.subEq_trans
#print axioms Rcic.Declarative.F8Measure.Below
#print axioms Rcic.Declarative.F8Measure.below_of_mem
#print axioms Rcic.Declarative.F8Measure.below_left
#print axioms Rcic.Declarative.F8Measure.below_right
#print axioms Rcic.Declarative.F8Measure.below_trans
#print axioms Rcic.Declarative.F8Measure.below_append_elim
#print axioms Rcic.Declarative.F8Measure.isPi_lift
#print axioms Rcic.Declarative.F8Measure.ctxWfT_tail
#print axioms Rcic.Declarative.F8Measure.Valley.below_left
#print axioms Rcic.Declarative.F8Measure.Valley.below_right
#print axioms Rcic.Declarative.F8Measure.Valley.below_ty₁
#print axioms Rcic.Declarative.F8Measure.Valley.below_ty₂
#print axioms Rcic.Declarative.F8Measure.XOut.below_fst
#print axioms Rcic.Declarative.F8Measure.XOut.below_snd
#print axioms Rcic.Declarative.F8Measure.StructPiProc
#print axioms Rcic.Declarative.F8Measure.StructPiContract
#print axioms Rcic.Declarative.F8Measure.structPiSelf
#print axioms Rcic.Declarative.F8Measure.structPiSelf_contract
#print axioms Rcic.Declarative.F8Measure.JProcWfP
#print axioms Rcic.Declarative.F8Measure.JContractWfP
#print axioms Rcic.Declarative.F8Measure.DProcP
#print axioms Rcic.Declarative.F8Measure.DContractP
#print axioms Rcic.Declarative.F8Measure.UProcP
#print axioms Rcic.Declarative.F8Measure.UContractP
#print axioms Rcic.Declarative.F8Measure.StructPiProcP
#print axioms Rcic.Declarative.F8Measure.StructPiContractP
#print axioms Rcic.Declarative.F8Measure.JProcWfP.ofTotal
#print axioms Rcic.Declarative.F8Measure.JContractWfP.ofTotal
#print axioms Rcic.Declarative.F8Measure.DProcP.ofTotal
#print axioms Rcic.Declarative.F8Measure.DContractP.ofTotal
#print axioms Rcic.Declarative.F8Measure.UProcP.ofTotal
#print axioms Rcic.Declarative.F8Measure.UContractP.ofTotal
#print axioms Rcic.Declarative.F8Measure.StructPiProcP.ofTotal
#print axioms Rcic.Declarative.F8Measure.StructPiContractP.ofTotal
#print axioms Rcic.Declarative.F8Measure.Suppliers
#print axioms Rcic.Declarative.F8Measure.Suppliers.declining
#print axioms Rcic.Declarative.F8Measure.BValley
#print axioms Rcic.Declarative.F8Measure.joinValley
#print axioms Rcic.Declarative.F8Measure.alignJoin
#print axioms Rcic.Declarative.F8Measure.valleyCv
#print axioms Rcic.Declarative.F8Measure.linkValley
#print axioms Rcic.Declarative.F8Measure.prefixValley
#print axioms Rcic.Declarative.F8Measure.readStar
#print axioms Rcic.Declarative.F8Measure.readValley
#print axioms Rcic.Declarative.F8Measure.Flat.segAdm
#print axioms Rcic.Declarative.F8Measure.Segs
#print axioms Rcic.Declarative.F8Measure.Segs.leaves
#print axioms Rcic.Declarative.F8Measure.Segs.adm
#print axioms Rcic.Declarative.F8Measure.Flat.segmentF
#print axioms Rcic.Declarative.F8Measure.Flat.segmentF_leaves
#print axioms Rcic.Declarative.F8Measure.Flat.segment
#print axioms Rcic.Declarative.F8Measure.Flat.segment_leaves
#print axioms Rcic.Declarative.F8Measure.BOut
#print axioms Rcic.Declarative.F8Measure.xSeg
#print axioms Rcic.Declarative.F8Measure.xSegs
#print axioms Rcic.Declarative.F8Measure.xAdm
#print axioms Rcic.Declarative.F8Measure.xValley?
#print axioms Rcic.Declarative.F8Measure.xValley
#print axioms Rcic.Declarative.F8Measure.xValley_contract
#print axioms Rcic.Declarative.F8Measure.pin_betaTwoLinks_segAdm
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_xAdm
#print axioms Rcic.Declarative.F8Measure.pin_request_xAdm
#print axioms Rcic.Declarative.F8Measure.pin_segAdm_subst_false
#print axioms Rcic.Declarative.F8Measure.pin_bLink_wk_succ_false
#print axioms Rcic.Declarative.F8Measure.pin_bLink_wk_zero
#print axioms Rcic.Declarative.F8Measure.pin_betaTwoLinks_declined
