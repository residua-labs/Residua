import rcic.RcicParRedTPiDiamond
import rcic.RcicParRedCore

/-!
# Pi-source preservation and reversal for the original `ParRedT`

The direct `pi` arm is reversible. This module extends that result to
an arbitrary derivation whose source is a Pi: `refl` and all outer
`conv` nodes are absorbed, and `iotaSpine` is ruled out by recursion on
its original `hstep`. Its intermediate target must still be a Pi,
whereas both actual `DerivedIotaU` constructors have application sources.

The generic theorem names exactly the remaining leaf obligation: a
`PEq` leaf at a Pi source must preserve the Pi head and supply a reverse
step at its own index. The empty `PEq` instance discharges this obligation
by elimination, so its head preservation, reversal, and common-source
diamond have no additional semantic premises.

This does not discharge the leaf obligation for `PEqLeafT`/`PEqT`.
It introduces no new reduction judgment, uses no uniqueness or Pi-row
injectivity premise, and asserts no bound on the size of produced
derivations. Recursion is on the input `ParRedT`, not on an inversion
view or a generated endpoint derivation. `closure_claim = 0`.
-/

namespace Rcic.Declarative

/- Both union landings are genuine recursor applications. Reuse the
   existing syntax lemma rather than assuming the typed iota arm is
   impossible solely from its original source. -/
private theorem derivedIotaU_pi_source_false
    {E : ResolvedEnv} {lhs rhs A B : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (heq : lhs = .pi A B) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (ctorMajor w) w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
        w.preMajor heq

section PiSource

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Every Pi-source step preserves the head and reverses at the same
index, provided its actual `PEq` leaves do. The recursive calls below
are only on the original `iotaSpine.hstep` and `conv.h` fields. -/
def parRedT_pi_head_reverse_of_leaf
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hLeaf : ∀ {A B q T : Expr Nat}, PEq Γ (.pi A B) q T →
      Σ' (A' B' : Expr Nat), (q = .pi A' B') ×'
        ParRedT PEq E n Γ q (.pi A B) T) :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {A B : Expr Nat} → a = .pi A B →
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      ParRedT PEq E n Γ b (.pi A B) T
  | _, _, _, .refl _ a T h, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, .refl Γ (.pi A B) T h⟩
  | _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, .lam .., _, _, heq => nomatch heq
  | _, _, _, .pi _ A₀ A' B₀ B' u v hA hc hB hcB _, A, B, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      exact ⟨A', B', rfl,
        parRedT_pi_reverse_data (PEq := PEq) hW hΓ hA hc hB hcB⟩
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, A, B, heq => by
      let ⟨A', B', hhead, _⟩ :=
        parRedT_pi_head_reverse_of_leaf hW hΓ hLeaf hstep heq
      exact False.elim (derivedIotaU_pi_source_false hI hhead)
  | _, _, _, .iotaStarK .., _, _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, .eta .., _, _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ h, A, B, heq => by
      subst heq
      exact hLeaf h
  | _, b, _, .conv _ _ _ T₀ T₁ h hc, A, B, heq =>
      let ⟨A', B', hhead, hrev⟩ :=
        parRedT_pi_head_reverse_of_leaf hW hΓ hLeaf h heq
      ⟨A', B', hhead, .conv Γ b (.pi A B) T₀ T₁ hrev hc⟩

/-- The leaf premise is inhabited for empty `PEq`. This handles every
constructor of the actual `ParRedT`, including nested `conv` and the
`iotaSpine` case, rather than assuming that a direct `pi` arm is exposed. -/
def parRedT_pi_head_reverse_empty
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A B b T : Expr Nat}
    (h : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) b T) :
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      ParRedT (fun _ _ _ _ => Empty) E n Γ b (.pi A B) T :=
  parRedT_pi_head_reverse_of_leaf (PEq := fun _ _ _ _ => Empty)
    hW hΓ (fun h => nomatch h) h rfl

/-- Both arbitrary Pi-source steps return to their literal common
source at the original common index. The returned steps are Type data. -/
def parRedT_pi_source_common_data_empty
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A B b c T : Expr Nat}
    (h₁ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) b T)
    (h₂ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) c T) :
    ParRedT (fun _ _ _ _ => Empty) E n Γ b (.pi A B) T ×
    ParRedT (fun _ _ _ _ => Empty) E n Γ c (.pi A B) T :=
  let ⟨_, _, _, hr₁⟩ := parRedT_pi_head_reverse_empty hW hΓ h₁
  let ⟨_, _, _, hr₂⟩ := parRedT_pi_head_reverse_empty hW hΓ h₂
  ⟨hr₁, hr₂⟩

/-- Fixed-index stars for the same common-source join. Empty `PEq`
also discharges the original endpoint-typing projection's leaf premise. -/
def parRedT_pi_source_common_star_data_empty
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A B b c T : Expr Nat}
    (h₁ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) b T)
    (h₂ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) c T) :
    ParRedTStar (fun _ _ _ _ => Empty) E n Γ b (.pi A B) T ×
    ParRedTStar (fun _ _ _ _ => Empty) E n Γ c (.pi A B) T :=
  let ⟨hr₁, hr₂⟩ := parRedT_pi_source_common_data_empty hW hΓ h₁ h₂
  let hs := parRedT_hasTy_left (PEq := fun _ _ _ _ => Empty)
    (fun h => nomatch h) hΓ h₁
  ⟨.tail hr₁ (.refl Γ (.pi A B) T hs),
    .tail hr₂ (.refl Γ (.pi A B) T hs)⟩

/-- Diamond for all Pi-source steps of `ParRedT` instantiated with
empty `PEq`, under the existing environment/context well-formedness.
No property of the actual `PEqT` proof leaves is asserted here. -/
theorem parRedT_pi_source_diamond_empty
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A B b c T : Expr Nat}
    (h₁ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) b T)
    (h₂ : ParRedT (fun _ _ _ _ => Empty) E n Γ (.pi A B) c T) :
    ∃ d : Expr Nat,
      Nonempty (ParRedTStar (fun _ _ _ _ => Empty) E n Γ b d T) ∧
      Nonempty (ParRedTStar (fun _ _ _ _ => Empty) E n Γ c d T) := by
  let ⟨hs₁, hs₂⟩ := parRedT_pi_source_common_star_data_empty hW hΓ h₁ h₂
  exact ⟨.pi A B, ⟨hs₁⟩, ⟨hs₂⟩⟩

end PiSource

/-- A nonidentity `pi` arm beneath two index-conversion nodes is joined
with a reflexive step by the all-Pi-source theorem. The existing cycle
provides the actual typed input; the two `conv` nodes exercise peeling. -/
theorem pin_parRedT_pi_source_refl_conv_empty :
    Nonempty (ParRedTStar (fun _ _ _ _ => Empty) emptyEnv 0 []
      parRedTPiCycleTarget parRedTPiCycleSource parRedTPiCycleType) ∧
    Nonempty (ParRedTStar (fun _ _ _ _ => Empty) emptyEnv 0 []
      parRedTPiCycleSource parRedTPiCycleSource parRedTPiCycleType) := by
  obtain ⟨_, ⟨⟨hf, _⟩⟩⟩ := pin_parRedT_pi_sort_beta_cycle
  let hc : TyConvT emptyEnv 0 [] parRedTPiCycleType parRedTPiCycleType :=
    .refl [] parRedTPiCycleType
  let hconv : ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 []
      parRedTPiCycleSource parRedTPiCycleTarget parRedTPiCycleType :=
    .conv [] _ _ _ _ (.conv [] _ _ _ _ hf hc) hc
  let hsrc := parRedT_hasTy_left (PEq := fun _ _ _ _ => Empty)
    (fun h => nomatch h) CtxWfT.nil hf
  let hrefl : ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 []
      parRedTPiCycleSource parRedTPiCycleSource parRedTPiCycleType :=
    .refl [] _ _ hsrc
  let ⟨h₁, h₂⟩ := parRedT_pi_source_common_star_data_empty
    EnvWfT.empty CtxWfT.nil hconv hrefl
  exact ⟨⟨h₁⟩, ⟨h₂⟩⟩

#print axioms parRedT_pi_head_reverse_of_leaf
#print axioms parRedT_pi_head_reverse_empty
#print axioms parRedT_pi_source_common_data_empty
#print axioms parRedT_pi_source_common_star_data_empty
#print axioms parRedT_pi_source_diamond_empty
#print axioms pin_parRedT_pi_source_refl_conv_empty

end Rcic.Declarative
