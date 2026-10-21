import rcic.RcicAnnLRRows

/-!
# M2-e (4) — towards the semantic environment: the fundamental theorem in two
environments, and the clause at a member

The fundamental theorem (`fundA`) and the two Type-level rows (`sortConvCharA`,
`piConvInjA`) are conditional on `EnvSemA E`: every member related to its
`=ₙ`-level instantiations at its type. It is discharged for environments built
member by member (`EnvWfA`, main's `EnvWf` on the copy — in `RcicAnnEnvWf`, M2-e
(8), down to the clauses of the families and constructors (`EnvSemIndA`, M2-f (4)'s
content since M2-f (3b)) and of the recursors); this file holds what the induction
consumes:
the theorem re-assembled in two environments, and the clause at a rigid member
and at a definition.

The induction is on the environment's construction, and its content is where
the circularity breaks: the clause for a member needs the fundamental theorem on
the member's type (and body), whose derivation lives in the PREFIX `E₀` built so
far, while the relations wanted are those of the FULL environment `E`. So the
theorem is re-assembled in two environments (`fundHasTyPrefixA` /
`fundConvPrefixA`): structural recursion on an `E₀`-derivation, every arm the
`E`-arm already proved, fed with the derivation's typings weakened from `E₀` to
`E` (`hasTyEnvA` / `convEnvA`, a syntactic function: members of `E₀` are
members of `E` as is, and the head step agrees on terms whose constants are in
`E₀` — `hStepFnA_prefix`, which the ι rule's typed endpoint supplies through
`hasTyA_constsIn`) and with the `const`/`consts` arms at the DOMAIN of `E₀`
(`FundHasTyArmsA E … (domA E₀)`): the semantic clauses for `E₀`'s members in
`E`, the induction hypothesis. No monotonicity of the relation under
environment extension is used or true; the relations never leave `E`.

For the new member the clause is then: at a rigid member (axiom, theorem,
opaque: no δ, and ι refuses on its spines by `IotaRecHeadA` — ι fires only on
spines headed by a recursor of `E`), REFLECTION (`LRRelA_reflect`): the constant
is an extended neutral (`neutKA_const`), typed at its type, and convertible to
itself; its type is valid in every well-formed context by the fundamental
theorem on the type's derivation (read at the identity pair, `ValidSubstA_nil`).
At a definition, δ-EXPANSION on both sides (`LRRelA_expand_left/right`) to the
body, self-related by the fundamental theorem on the body's derivation. Members
with a body have arity `0` (00 §20.6 MONOMORPHIC DELTA, as on main), so the
`=ₙ`-level lists are both `[]` and no level metatheorem enters. The environment
judgment `EnvWfA` and the induction itself live in `RcicAnnEnvWf` (M2-e (8),
after the level lemmas): this file holds the two-environment assembly and the
clauses.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) sub-environments -/

/-- every member of `E₀` is a member of `E`, unchanged. -/
def PrefixA (E₀ E : ResolvedEnvA) : Prop :=
  ∀ r m, E₀.members r = some m → E.members r = some m

theorem prefixA_refl (E : ResolvedEnvA) : PrefixA E E := fun _ _ h => h

theorem prefixA_trans {E₀ E₁ E₂ : ResolvedEnvA} (h₁ : PrefixA E₀ E₁) (h₂ : PrefixA E₁ E₂) :
    PrefixA E₀ E₂ :=
  fun r m h => h₂ r m (h₁ r m h)

theorem members_extendEnvA_self (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA) :
    (extendEnvA E r m).members r = some m := by
  show (if r = r then some m else E.members r) = some m
  rw [if_pos rfl]

theorem members_extendEnvA_ne (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA) {r' : Nat}
    (h : r' ≠ r) : (extendEnvA E r m).members r' = E.members r' := by
  show (if r' = r then some m else E.members r') = E.members r'
  rw [if_neg h]

theorem prefixA_extend (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA)
    (hfresh : E.members r = none) : PrefixA E (extendEnvA E r m) := fun r' m' h => by
  by_cases hr : r' = r
  · subst hr; rw [hfresh] at h; exact Option.noConfusion h
  · rw [members_extendEnvA_ne E r m hr]; exact h

/-- the domain of an environment. -/
def domA (E : ResolvedEnvA) (r : Nat) : Prop := ∃ m, E.members r = some m

/-! ## (2) the constants of a term; the head step reads only the members it names -/

/-- every constant of the term satisfies `D`. -/
def ConstsInA (D : Nat → Prop) : ExprA → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => D r
  | .app f x => ConstsInA D f ∧ ConstsInA D x
  | .lam a _ b => ConstsInA D a ∧ ConstsInA D b
  | .pi a _ b _ => ConstsInA D a ∧ ConstsInA D b
  | .letE a w b => ConstsInA D a ∧ ConstsInA D w ∧ ConstsInA D b
  | .lit t =>
      match t with
      | 0 => D 1
      | _ + 1 => D 1 ∧ D 2

/-- the constants a literal names are the constants of its expansion: `natExpandA 0`
is `.const 1`, `natExpandA (n+1)` is `.app (.const 2) (natExpandA n)`. -/
theorem constsInA_of_natExpandA {D : Nat → Prop} : (t : Nat) →
    ConstsInA D (natExpandA t) → ConstsInA D (.lit t)
  | 0, h => h
  | 1, h => ⟨h.2, h.1⟩
  | n + 2, h => ⟨(constsInA_of_natExpandA (n + 1) h.2).1, h.1⟩

theorem hStepFnA_app_congr {E E' : ResolvedEnvA} (I : IotaFnA) (Γ : LCtxA) {f : ExprA}
    (x : ExprA) (hnl : ∀ A u b, f ≠ .lam A u b)
    (h : hStepFnA E I Γ f = hStepFnA E' I Γ f) (hrec : recAtMajorA E f = recAtMajorA E' f)
    (hu : unitMinorA E f = unitMinorA E' f) (hs : structArmA E f x = structArmA E' f x)
    (hh : structHeadA E f = structHeadA E' f) (hx : hStepFnA E I Γ x = hStepFnA E' I Γ x) :
    hStepFnA E I Γ (.app f x) = hStepFnA E' I Γ (.app f x) := by
  have hp : structPosA E f = structPosA E' f := by unfold structPosA; rw [hrec, hh]
  rw [hStepFnA_app_nonlam E I Γ x hnl, hStepFnA_app_nonlam E' I Γ x hnl, h, hp, hrec, hu, hs, hx]

/-- the head constant of a term all of whose constants satisfy `D`. -/
theorem constsInA_head {D : Nat → Prop} :
    (e : ExprA) → ConstsInA D e → ∀ r ls, (appsSpineA e).1 = .const r ls → D r
  | .const r' ls', h, r, ls, hsp => by
      have h' : ExprA.const r' ls' = .const r ls := hsp
      injection h' with h1 _
      subst h1
      exact h
  | .app f _, ⟨hf, _⟩, r, ls, hsp => constsInA_head f hf r ls hsp
  | .bvar _, _, _, _, h => by simp [appsSpineA] at h
  | .sort _, _, _, _, h => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, _, h => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, _, h => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, _, h => by simp [appsSpineA] at h
  | .lit _, _, _, _, h => by simp [appsSpineA] at h

theorem recAtMajorA'_congr {E₀ E : ResolvedEnvA} {r : Nat} (h : E₀.members r = E.members r)
    (ls : List Level) (k : Nat) :
    recAtMajorA' E₀ (.const r ls) k = recAtMajorA' E (.const r ls) k := by
  show (match E₀.members r with
    | some m => decide (m.mclass = MemberClass.recursorM ∧ k + 1 = piCountA m.mtypeA) && recHasCtorA r m
    | none => false) =
    (match E.members r with
    | some m => decide (m.mclass = MemberClass.recursorM ∧ k + 1 = piCountA m.mtypeA) && recHasCtorA r m
    | none => false)
  rw [h]

/-- the major arm reads the same member in `E₀` and in `E ⊇ E₀` on a term whose
    constants are members of `E₀`. -/
theorem recAtMajorA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {f : ExprA}
    (hf : ConstsInA (domA E₀) f) : recAtMajorA E₀ f = recAtMajorA E f := by
  unfold recAtMajorA
  cases hh : (appsSpineA f).1 with
  | const r ls =>
      obtain ⟨m, hm⟩ := constsInA_head f hf r ls hh
      exact recAtMajorA'_congr (by rw [hm, hpre r m hm]) ls _
  | bvar _ => rfl
  | sort _ => rfl
  | app _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

theorem unitHeadA_congr {E₀ E : ResolvedEnvA} {r : Nat} (h : E₀.members r = E.members r)
    (ls : List Level) : unitHeadA E₀ (.const r ls) = unitHeadA E (.const r ls) := by
  show (match E₀.members r with
    | some m => unitGroupA r m
    | none => false) =
    (match E.members r with
    | some m => unitGroupA r m
    | none => false)
  rw [h]

/-- the K-unit arm reads the head's member alone, the same in `E₀` and in `E ⊇ E₀` on a term whose
    constants are members of `E₀`. -/
theorem unitMinorA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {f : ExprA}
    (hf : ConstsInA (domA E₀) f) : unitMinorA E₀ f = unitMinorA E f := by
  cases f with
  | app g mn =>
      show (if unitHeadA E₀ (appsSpineA g).1 then some mn else none) =
        (if unitHeadA E (appsSpineA g).1 then some mn else none)
      cases hh : (appsSpineA g).1 with
      | const r ls =>
          obtain ⟨m, hm⟩ := constsInA_head g hf.1 r ls hh
          rw [unitHeadA_congr (E₀ := E₀) (E := E) (hm.trans (hpre r m hm).symm) ls]
      | bvar _ => rfl
      | sort _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | pi _ _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

/-- W-1 (a): the struct arm reads the head's member alone, the same in `E₀` and in `E ⊇ E₀` on a term
    whose constants are members of `E₀`. -/
theorem structSpineA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {f : ExprA}
    (hf : ConstsInA (domA E₀) f) : structSpineA E₀ f = structSpineA E f := by
  cases f with
  | app g mn =>
      dsimp only [structSpineA]
      cases hh : (appsSpineA g).1 with
      | const r ls =>
          obtain ⟨m, hm⟩ := constsInA_head g hf.1 r ls hh
          dsimp only
          rw [hm, hpre r m hm]
      | bvar _ => rfl
      | sort _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | pi _ _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

theorem structArmA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {f : ExprA}
    (hf : ConstsInA (domA E₀) f) (x : ExprA) : structArmA E₀ f x = structArmA E f x := by
  unfold structArmA
  rw [structSpineA_prefix hpre hf]

/-- W-1 (e): the struct head reads the head's member alone, the same in `E₀` and in `E ⊇ E₀` on a term
    whose constants are members of `E₀`. -/
theorem structHeadA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {f : ExprA}
    (hf : ConstsInA (domA E₀) f) : structHeadA E₀ f = structHeadA E f := by
  unfold structHeadA
  cases hh : (appsSpineA f).1 with
  | const r ls =>
      obtain ⟨m, hm⟩ := constsInA_head f hf r ls hh
      dsimp only
      rw [hm, hpre r m hm]
  | _ => rfl

/-- the head step in `E₀` and in `E ⊇ E₀` agree on a term whose constants are
    members of `E₀`: δ reads the same member, ι reads the term alone. -/
theorem hStepFnA_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) (I : IotaFnA) (Γ : LCtxA) :
    (e : ExprA) → ConstsInA (domA E₀) e → hStepFnA E₀ I Γ e = hStepFnA E I Γ e
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .const r _, ⟨m, hm⟩ => by simp only [hStepFnA, hm, hpre r m hm]
  | .app (.lam _ _ _) _, _ => rfl
  | .app (.bvar i) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.bvar i) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.sort l) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.sort l) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.const r ls) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.const r ls) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.app g y) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.app g y) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.pi a u b v) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.pi a u b v) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.letE a w b) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.letE a w b) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)
  | .app (.lit t) x, ⟨hf, hx⟩ =>
      hStepFnA_app_congr I Γ x (fun _ _ _ h => ExprA.noConfusion h)
        (hStepFnA_prefix hpre I Γ (.lit t) hf) (recAtMajorA_prefix hpre hf)
        (unitMinorA_prefix hpre hf) (structArmA_prefix hpre hf x) (structHeadA_prefix hpre hf)
        (hStepFnA_prefix hpre I Γ x hx)

section Consts
variable {E₀ : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

mutual

/-- a typed term names only members: every constant has a `const` leaf. -/
theorem hasTyA_constsIn :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E₀ I n Γ e A → ConstsInA (domA E₀) e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ _ _ => trivial
  | _, _, _, .const _ r _ m _ hres _ _ _ => ⟨m, hres⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => ⟨hasTyA_constsIn hA, hasTyA_constsIn hB⟩
  | _, _, _, .lam _ _ _ _ _ _ hA _ hbody => ⟨hasTyA_constsIn hA, hasTyA_constsIn hbody⟩
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf ha => ⟨hasTyA_constsIn hf, hasTyA_constsIn ha⟩
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv _ hb =>
      ⟨hasTyA_constsIn hA, hasTyA_constsIn hv, hasTyA_constsIn hb⟩
  | _, _, _, .lit _ t _ hexp => constsInA_of_natExpandA t (hasTyA_constsIn hexp)
  | _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_constsIn h

theorem convA_constsIn :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E₀ I n Γ a b A →
    ConstsInA (domA E₀) a ∧ ConstsInA (domA E₀) b
  | _, _, _, _, .refl _ _ _ h => ⟨hasTyA_constsIn h, hasTyA_constsIn h⟩
  | _, _, _, _, .symm _ _ _ _ h => (convA_constsIn h).symm
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => ⟨(convA_constsIn h1).1, (convA_constsIn h2).2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg hred =>
      ⟨⟨⟨hasTyA_constsIn hA, hasTyA_constsIn hbody⟩, hasTyA_constsIn harg⟩, hasTyA_constsIn hred⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hred =>
      ⟨⟨hasTyA_constsIn hA, hasTyA_constsIn hv, hasTyA_constsIn hb⟩, hasTyA_constsIn hred⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => ⟨trivial, hasTyA_constsIn hv⟩
  | _, _, _, _, .delta _ r _ m _ hres _ _ _ _ hb => ⟨⟨m, hres⟩, hasTyA_constsIn hb⟩
  | _, _, _, _, .iota _ _ _ _ _ hlhs hrhs => ⟨hasTyA_constsIn hlhs, hasTyA_constsIn hrhs⟩
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ hlhs hrhs _ => ⟨hasTyA_constsIn hlhs, hasTyA_constsIn hrhs⟩
  | _, _, _, _, .lit _ t _ hexp =>
      ⟨constsInA_of_natExpandA t (hasTyA_constsIn hexp), hasTyA_constsIn hexp⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 _ _ =>
      ⟨⟨(convA_constsIn h1).1, (convA_constsIn h2).1⟩,
       ⟨(convA_constsIn h1).2, (convA_constsIn h2).2⟩⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ hA hb hrt =>
      ⟨⟨(convA_constsIn hA).1, (convA_constsIn hb).1⟩, hasTyA_constsIn hrt⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hrt =>
      ⟨⟨(convA_constsIn hA).1, (convA_constsIn hB).1⟩, hasTyA_constsIn hrt⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hrt =>
      ⟨⟨(convA_constsIn hA).1, (convA_constsIn hv).1, (convA_constsIn hb).1⟩,
       hasTyA_constsIn hrt⟩
  | _, _, _, _, .sorts _ _ _ _ => ⟨trivial, trivial⟩
  | _, _, _, _, .consts _ r _ _ m hres _ _ _ _ _ => ⟨⟨m, hres⟩, ⟨m, hres⟩⟩
  | _, _, _, _, .eta _ _ _ _ _ _ h hrt => ⟨hasTyA_constsIn hrt, hasTyA_constsIn h⟩
  | _, _, _, _, .irr _ _ _ _ _ hp hq => ⟨hasTyA_constsIn hp, hasTyA_constsIn hq⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ _ _ _ => convA_constsIn h

end

end Consts

/-- a declarative ι step of `E₀` is one of `E ⊇ E₀` when its redex names only
    members of `E₀`. -/
theorem iotaRel_prefix {E₀ E : ResolvedEnvA} (hpre : PrefixA E₀ E) {I : IotaIfaceA} {Γ : LCtxA}
    {e e' : ExprA} (hc : ConstsInA (domA E₀) e) (h : I.rel E₀ Γ e e') : I.rel E Γ e e' :=
  ⟨h.1, by rw [← hStepFnA_prefix hpre I.fn Γ e hc]; exact h.2⟩

/-! ## (3) derivations weaken along the sub-environment -/

section EnvWeaken
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

mutual

def hasTyEnvA (hpre : PrefixA E₀ E) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E₀ I n Γ e A → HasTyA E I n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A u h hA => .bvar Γ i A u h (hasTyEnvA hpre hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      .const Γ r ls m u (hpre r m hres) hlen hwf (hasTyEnvA hpre hT)
  | _, _, _, .pi Γ A u B v hA hB => .pi Γ A u B v (hasTyEnvA hpre hA) (hasTyEnvA hpre hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam Γ A u body B v (hasTyEnvA hpre hA) (hasTyEnvA hpre hB) (hasTyEnvA hpre hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      .app Γ f a A B u v w (hasTyEnvA hpre hB) (hasTyEnvA hpre hTy) (hasTyEnvA hpre hf)
        (hasTyEnvA hpre ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      .letE Γ A u w value B body (hasTyEnvA hpre hA) (hasTyEnvA hpre hv) (hasTyEnvA hpre hTy)
        (hasTyEnvA hpre hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyEnvA hpre hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv Γ e A B l u (hasTyEnvA hpre h) (hasTyEnvA hpre hAl) hlu (hasTyEnvA hpre hB)
        (convEnvA hpre hc)

def convEnvA (hpre : PrefixA E₀ E) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E₀ I n Γ a b A → ConvA E I n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (hasTyEnvA hpre h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (convEnvA hpre h)
  | _, _, _, _, .trans Γ a b c A h1 h2 => .trans Γ a b c A (convEnvA hpre h1) (convEnvA hpre h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (hasTyEnvA hpre hA) (hasTyEnvA hpre hbody) (hasTyEnvA hpre harg)
        (hasTyEnvA hpre hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (hasTyEnvA hpre hA) (hasTyEnvA hpre hv) (hasTyEnvA hpre hb)
        (hasTyEnvA hpre hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv => .zetaLocal Γ i A v hval hty (hasTyEnvA hpre hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b (hpre r m hres) hbody htr hlen hwf (hasTyEnvA hpre hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T (iotaRel_prefix hpre (hasTyA_constsIn hlhs) h) (hasTyEnvA hpre hlhs)
        (hasTyEnvA hpre hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota Γ f a rhs e T (by rw [← recAtMajorA_prefix hpre (hasTyA_constsIn hlhs).1]; exact hrec)
        (by rw [← structArmA_prefix hpre (hasTyA_constsIn hlhs).1]; exact hs) h (hasTyEnvA hpre hlhs)
        (hasTyEnvA hpre hrhs) (convEnvA hpre hcv)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyEnvA hpre hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      .app Γ f g a b A B u v (convEnvA hpre h1) (convEnvA hpre h2) (hasTyEnvA hpre hB)
        (hasTyEnvA hpre hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      .lam Γ A A' b b' B u u' v hu (convEnvA hpre hA) (convEnvA hpre hb) (hasTyEnvA hpre hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi Γ A A' B B' u u' v v' hu hv (convEnvA hpre hA) (convEnvA hpre hB)
        (hasTyEnvA hpre hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      .letE Γ A A' v v' b b' B u (convEnvA hpre hA) (convEnvA hpre hv) (convEnvA hpre hb)
        (hasTyEnvA hpre hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      .consts Γ r ls ls' m (hpre r m hres) hlen hwf hwf' h (hasTyEnvA hpre hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt => .eta Γ f A B u v (hasTyEnvA hpre h) (hasTyEnvA hpre hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyEnvA hpre hP) (hasTyEnvA hpre hp) (hasTyEnvA hpre hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv Γ a b A A' l l' u (convEnvA hpre h) (hasTyEnvA hpre hAl) hlu (hasTyEnvA hpre hA'l)
        hl'u (convEnvA hpre hA)

/-- `TyConvA` transports along an env prefix (R-NoDeltaRec-4d-iii): each `.of` node's coherence
    data rides `hasTyEnvA`/`convEnvA`. -/
def tyConvA_env (hpre : PrefixA E₀ E) :
    {Γ : LCtxA} → {A B : ExprA} → TyConvA E₀ I n Γ A B → TyConvA E I n Γ A B
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      .of Γ A B l l' u (hasTyEnvA hpre hAl) hlu (hasTyEnvA hpre hBl) hl'u (convEnvA hpre h)
  | _, _, _, .trans Γ A B C h1 h2 =>
      .trans Γ A B C (tyConvA_env hpre h1) (tyConvA_env hpre h2)

end

end EnvWeaken

/-! ## (4) the fundamental theorem in two environments: `E₀`-derivations, `E`-relations -/

section Mixed
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

mutual

theorem fundHasTyPrefixA (hpre : PrefixA E₀ E) (ht : FundHasTyArmsA E I n ρ₀ (domA E₀))
    (hc : FundConvArmsA E I n ρ₀ (domA E₀)) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E₀ I n Γ e A → FundArmA E I n ρ₀ Γ e e A
  | _, _, _, .sort Γ l => ht.sortA Γ l
  | _, _, _, .bvar Γ i A u h hA =>
      ht.bvarA Γ i A u h (hasTyEnvA hpre hA) (fundHasTyPrefixA hpre ht hc hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      ht.constA Γ r ls m u ⟨m, hres⟩ (hpre r m hres) hlen hwf (hasTyEnvA hpre hT)
        (fundHasTyPrefixA hpre ht hc hT)
  | _, _, _, .pi Γ A u B v hA hB =>
      ht.piA Γ A u B v (hasTyEnvA hpre hA) (hasTyEnvA hpre hB) (fundHasTyPrefixA hpre ht hc hA)
        (fundHasTyPrefixA hpre ht hc hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      ht.lamA Γ A u body B v (hasTyEnvA hpre hA) (hasTyEnvA hpre hB) (hasTyEnvA hpre hbody)
        (fundHasTyPrefixA hpre ht hc hA) (fundHasTyPrefixA hpre ht hc hB)
        (fundHasTyPrefixA hpre ht hc hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      ht.appA Γ f a A B u v w (hasTyEnvA hpre hB) (hasTyEnvA hpre hTy) (hasTyEnvA hpre hf)
        (hasTyEnvA hpre ha) (fundHasTyPrefixA hpre ht hc hB) (fundHasTyPrefixA hpre ht hc hTy)
        (fundHasTyPrefixA hpre ht hc hf) (fundHasTyPrefixA hpre ht hc ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      ht.letEA Γ A u w value B body (hasTyEnvA hpre hA) (hasTyEnvA hpre hv) (hasTyEnvA hpre hTy)
        (hasTyEnvA hpre hb) (fundHasTyPrefixA hpre ht hc hA) (fundHasTyPrefixA hpre ht hc hv)
        (fundHasTyPrefixA hpre ht hc hTy) (fundHasTyPrefixA hpre ht hc hb)
  | _, _, _, .lit Γ t T hexp =>
      ht.litA Γ t T (hasTyEnvA hpre hexp) (fundHasTyPrefixA hpre ht hc hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hcv =>
      ht.convA Γ e A B l u (hasTyEnvA hpre h) (hasTyEnvA hpre hAl) hlu (hasTyEnvA hpre hB)
        (convEnvA hpre hcv) (fundHasTyPrefixA hpre ht hc h) (fundHasTyPrefixA hpre ht hc hAl)
        (fundHasTyPrefixA hpre ht hc hB) (fundConvPrefixA hpre ht hc hcv)

theorem fundConvPrefixA (hpre : PrefixA E₀ E) (ht : FundHasTyArmsA E I n ρ₀ (domA E₀))
    (hc : FundConvArmsA E I n ρ₀ (domA E₀)) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E₀ I n Γ a b A → FundArmA E I n ρ₀ Γ a b A
  | _, _, _, _, .refl Γ a A h => hc.reflA Γ a A (hasTyEnvA hpre h) (fundHasTyPrefixA hpre ht hc h)
  | _, _, _, _, .symm Γ a b A h => hc.symmA Γ a b A (convEnvA hpre h) (fundConvPrefixA hpre ht hc h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      hc.transA Γ a b c A (convEnvA hpre h1) (convEnvA hpre h2) (fundConvPrefixA hpre ht hc h1)
        (fundConvPrefixA hpre ht hc h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      hc.betaA Γ A u body arg B (hasTyEnvA hpre hA) (hasTyEnvA hpre hbody) (hasTyEnvA hpre harg)
        (hasTyEnvA hpre hred) (fundHasTyPrefixA hpre ht hc hA) (fundHasTyPrefixA hpre ht hc hbody)
        (fundHasTyPrefixA hpre ht hc harg) (fundHasTyPrefixA hpre ht hc hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      hc.zetaA Γ A value body B u (hasTyEnvA hpre hA) (hasTyEnvA hpre hv) (hasTyEnvA hpre hb)
        (hasTyEnvA hpre hred) (fundHasTyPrefixA hpre ht hc hA) (fundHasTyPrefixA hpre ht hc hv)
        (fundHasTyPrefixA hpre ht hc hb) (fundHasTyPrefixA hpre ht hc hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      hc.zetaLocalA Γ i A v hval hty (hasTyEnvA hpre hv) (fundHasTyPrefixA hpre ht hc hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      hc.deltaA Γ r ls m b (hpre r m hres) hbody htr hlen hwf (hasTyEnvA hpre hb)
        (fundHasTyPrefixA hpre ht hc hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      hc.iotaA Γ lhs rhs T (iotaRel_prefix hpre (hasTyA_constsIn hlhs) h) (hasTyEnvA hpre hlhs)
        (hasTyEnvA hpre hrhs) (fundHasTyPrefixA hpre ht hc hlhs) (fundHasTyPrefixA hpre ht hc hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      hc.structIotaA Γ f a rhs e T (by rw [← recAtMajorA_prefix hpre (hasTyA_constsIn hlhs).1]; exact hrec)
        (by rw [← structArmA_prefix hpre (hasTyA_constsIn hlhs).1]; exact hs) h (hasTyEnvA hpre hlhs)
        (hasTyEnvA hpre hrhs) (convEnvA hpre hcv) (fundHasTyPrefixA hpre ht hc hlhs)
        (fundHasTyPrefixA hpre ht hc hrhs) (fundConvPrefixA hpre ht hc hcv)
  | _, _, _, _, .lit Γ t T hexp =>
      hc.litA Γ t T (hasTyEnvA hpre hexp) (fundHasTyPrefixA hpre ht hc hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      hc.appA Γ f g a b A B u v (convEnvA hpre h1) (convEnvA hpre h2) (hasTyEnvA hpre hB)
        (hasTyEnvA hpre hrt) (fundConvPrefixA hpre ht hc h1) (fundConvPrefixA hpre ht hc h2)
        (fundHasTyPrefixA hpre ht hc hB) (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      hc.lamA Γ A A' b b' B u u' v hu (convEnvA hpre hA) (convEnvA hpre hb) (hasTyEnvA hpre hrt)
        (fundConvPrefixA hpre ht hc hA) (fundConvPrefixA hpre ht hc hb)
        (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      hc.piA Γ A A' B B' u u' v v' hu hv (convEnvA hpre hA) (convEnvA hpre hB)
        (hasTyEnvA hpre hrt) (fundConvPrefixA hpre ht hc hA) (fundConvPrefixA hpre ht hc hB)
        (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      hc.letEA Γ A A' v v' b b' B u (convEnvA hpre hA) (convEnvA hpre hv) (convEnvA hpre hb)
        (hasTyEnvA hpre hrt) (fundConvPrefixA hpre ht hc hA) (fundConvPrefixA hpre ht hc hv)
        (fundConvPrefixA hpre ht hc hb) (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => hc.sortsA Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      hc.constsA Γ r ls ls' m ⟨m, hres⟩ (hpre r m hres) hlen hwf hwf' h (hasTyEnvA hpre hrt)
        (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt =>
      hc.etaA Γ f A B u v (hasTyEnvA hpre h) (hasTyEnvA hpre hrt) (fundHasTyPrefixA hpre ht hc h)
        (fundHasTyPrefixA hpre ht hc hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      hc.irrA Γ P p q (hasTyEnvA hpre hP) (hasTyEnvA hpre hp) (hasTyEnvA hpre hq)
        (fundHasTyPrefixA hpre ht hc hP) (fundHasTyPrefixA hpre ht hc hp)
        (fundHasTyPrefixA hpre ht hc hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      hc.tyConvA Γ a b A A' l l' u (convEnvA hpre h) (hasTyEnvA hpre hAl) hlu (hasTyEnvA hpre hA'l)
        hl'u (convEnvA hpre hA) (fundConvPrefixA hpre ht hc h) (fundHasTyPrefixA hpre ht hc hAl)
        (fundHasTyPrefixA hpre ht hc hA'l) (fundConvPrefixA hpre ht hc hA)

end

end Mixed

/-! ## (5) level lists of length `0`; ι fires only on recursor spines -/

theorem instantiateLevelsA_nil : (e : ExprA) → instantiateLevelsA [] e = e
  | .bvar _ => rfl
  | .sort _ => by simp only [instantiateLevelsA, instLevel_nil]
  | .const _ _ => by simp only [instantiateLevelsA, instLevel_nil_map]
  | .app f x => by simp only [instantiateLevelsA, instantiateLevelsA_nil f, instantiateLevelsA_nil x]
  | .lam a _ b => by
      simp only [instantiateLevelsA, instLevel_nil, instantiateLevelsA_nil a, instantiateLevelsA_nil b]
  | .pi a _ b _ => by
      simp only [instantiateLevelsA, instLevel_nil, instantiateLevelsA_nil a, instantiateLevelsA_nil b]
  | .letE a w b => by
      simp only [instantiateLevelsA, instantiateLevelsA_nil a, instantiateLevelsA_nil w,
        instantiateLevelsA_nil b]
  | .lit _ => rfl

theorem list_nil_of_length_zero {α : Type} : (l : List α) → l.length = 0 → l = []
  | [], _ => rfl
  | _ :: _, h => absurd h (Nat.succ_ne_zero _)

/-- a spine headed by a member that is neither a transparent definition with a
    body nor a recursor never head-steps: no δ at the head, no β (the head is a
    constant), and ι refuses (`IotaRecHeadA`). -/
theorem hStepFnA_constSpine_none {E : ResolvedEnvA} {I : IotaIfaceA} (hR : IotaRecHeadA E I)
    {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hrigid : transparent m.mclass = false ∨ m.bodyA = none) (hnr : m.mclass ≠ .recursorM)
    (Γ : LCtxA) {ls : List Level} :
    (e : ExprA) → (appsSpineA e).1 = .const r ls → hStepFnA E I.fn Γ e = none
  | .bvar _, hsp => ExprA.noConfusion hsp
  | .sort _, hsp => ExprA.noConfusion hsp
  | .lam _ _ _, hsp => ExprA.noConfusion hsp
  | .pi _ _ _ _, hsp => ExprA.noConfusion hsp
  | .letE _ _ _, hsp => ExprA.noConfusion hsp
  | .lit _, hsp => ExprA.noConfusion hsp
  | .const r' ls', hsp => by
      have hsp' : ExprA.const r' ls' = .const r ls := hsp
      injection hsp' with h1 h2
      subst h1; subst h2
      show (match E.members r' with
        | some m => if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none
        | none => none) = none
      rw [hres]
      show (if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none) = none
      rcases hrigid with h | h
      · rw [h]; rfl
      · rw [h]; cases transparent m.mclass <;> rfl
  | .app f x, hsp => by
      have hf : (appsSpineA f).1 = .const r ls := hsp
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b hf' => by
        rw [hf'] at hf; exact ExprA.noConfusion hf
      have hi : I.fn (.app f x) = none := by
        cases hfn : I.fn (.app f x) with
        | none => rfl
        | some e' =>
            exfalso
            obtain ⟨r', ls', m', hsp', hres', hcls, _⟩ := hR _ _ hfn
            have h1 : ExprA.const r ls = .const r' ls' := hsp.symm.trans hsp'
            injection h1 with h1 _
            subst h1
            rw [hres] at hres'
            cases hres'
            exact hnr hcls
      exact hStepFnA_app_none E I.fn Γ hnl (hStepFnA_constSpine_none hR hres hrigid hnr Γ f hf) hi
        (recAtMajorA_of_not_rec hf hres hnr)

/-- such a constant is an extended neutral: stuck under every world and every
    further application, not shape-headed and not constructor-headed. Families and
    constructors are excluded (M2-f (3b)): a family application has the `fam`
    clause and a constructor application is that clause's constructor disjunct. -/
theorem neutKA_const {E : ResolvedEnvA} {I : IotaIfaceA} (hR : IotaRecHeadA E I) {r : Nat}
    {m : CheckedMemberA} (hres : E.members r = some m)
    (hrigid : transparent m.mclass = false ∨ m.bodyA = none) (hnr : m.mclass ≠ .recursorM)
    (hni : m.mclass ≠ .inductiveM) (hnc : m.mclass ≠ .constructorM) (Γ : LCtxA) (ls : List Level) :
    NeutKA E I Γ (.const r ls) := by
  refine ⟨fun ρ _ xs => ?_, not_isShapeHeadA_const hres hni, ?_⟩
  · rw [wkExprA_closed (fun _ => rfl) ρ]
    exact hStepFnA_constSpine_none hR hres hrigid hnr _ _ (by rw [appsSpineA_foldAppsA]; rfl)
  · rintro ⟨c, _, m', hsp, hm', hk'⟩
    injection hsp with hc _
    subst hc
    rw [hres] at hm'
    injection hm' with e
    subst e
    exact hnc hk'

/-! ## (6) the clause at a member -/

section Clause
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fundamental theorem's arm at the empty context, read at the identity pair:
    the term is related to itself at its type in every well-formed context. -/
theorem fundArmA_nil {e A : ExprA} (h : FundArmA E I n ρ₀ [] e e A) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelA E I n ρ₀ k Δ A e e := by
  obtain ⟨k₀, h⟩ := h
  refine ⟨k₀, fun k hk Δ hΔ => ?_⟩
  have := (h k hk Δ SubstA.id SubstA.id hΔ (ValidSubstA_nil Δ _ _)).2
  simp only [substA_id] at this
  exact this

/-- the clause at an arity-`0` RIGID member (no δ: not a transparent definition
    with a body; not a recursor, so ι refuses on its spines; not a family or a
    constructor, so it is a neutral) whose type is self-related at its sort in every
    well-formed context: by reflection. -/
theorem envSemClauseA_rigid (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m) (har : m.arity = 0)
    (hrigid : transparent m.mclass = false ∨ m.bodyA = none) (hnr : m.mclass ≠ .recursorM)
    (hni : m.mclass ≠ .inductiveM) (hnc : m.mclass ≠ .constructorM) {u : Level} {k₀ : Nat}
    (hT : ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelA E I n ρ₀ k Δ (.sort u) m.mtypeA m.mtypeA) :
    EnvSemClauseA E I n ρ₀ r m := by
  intro ls ls' hlen _ _ heq
  have hls : ls = [] := list_nil_of_length_zero ls (har ▸ hlen)
  have hls' : ls' = [] :=
    list_nil_of_length_zero ls' ((eqNList_length ls ls' heq).symm.trans (hls ▸ rfl))
  subst hls; subst hls'
  simp only [instantiateLevelsA_nil]
  refine ⟨k₀, fun k hk Δ hΔ => ?_⟩
  obtain ⟨_, hval, _, hty, _, _⟩ := LRRelA_sort_elim (hT k hk Δ hΔ)
  have htc : Nonempty (HasTyA E I n Δ (.const r []) m.mtypeA) := hty.elim fun t => by
    have hT0 : HasTyA E I n Δ (instantiateLevelsA [] m.mtypeA) (.sort u) := by
      simp only [instantiateLevelsA_nil]; exact t
    have hc0 := HasTyA.const Δ r [] m u hres (by rw [har]; rfl) rfl hT0
    simp only [instantiateLevelsA_nil] at hc0
    exact ⟨hc0⟩
  exact LRRelA_reflect hE hI hval (neutKA_const hR hres hrigid hnr hni hnc Δ [])
    (neutKA_const hR hres hrigid hnr hni hnc Δ []) htc htc (htc.elim fun t => ⟨.refl Δ _ _ t⟩)

/-- the clause at a DEFINITION: δ-expansion on both sides to the body, itself
    self-related at the type in every well-formed context. -/
theorem envSemClauseA_def (hE : EnvClosedA E) (hI : IotaLiftA I) {r : Nat} {A v : ExprA}
    (hres : E.members r = some ⟨.definitionM, 0, A, some v, 0, none⟩) {u : Level} {k₀ : Nat}
    (hT : ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelA E I n ρ₀ k Δ (.sort u) A A)
    (hv : ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) → LRRelA E I n ρ₀ k Δ A v v) :
    EnvSemClauseA E I n ρ₀ r ⟨.definitionM, 0, A, some v, 0, none⟩ := by
  intro ls ls' hlen _ _ heq
  have hls : ls = [] := list_nil_of_length_zero ls hlen
  have hls' : ls' = [] :=
    list_nil_of_length_zero ls' ((eqNList_length ls ls' heq).symm.trans (hls ▸ rfl))
  subst hls; subst hls'
  show ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
    LRRelA E I n ρ₀ k Δ (instantiateLevelsA [] A) (.const r []) (.const r [])
  simp only [instantiateLevelsA_nil]
  refine ⟨k₀, fun k hk Δ hΔ => ?_⟩
  have hvv := hv k hk Δ hΔ
  obtain ⟨_, _, _, hty, _, _⟩ := LRRelA_sort_elim (hT k hk Δ hΔ)
  obtain ⟨htv, _⟩ := LRRelA_hasTy hvv
  have hs : StepAtA E I n Δ (.const r []) v A := by
    refine ⟨hty.elim fun t => ?_, htv.elim fun x => ?_⟩
    · have hT0 : HasTyA E I n Δ (instantiateLevelsA [] A) (.sort u) := by
        simp only [instantiateLevelsA_nil]; exact t
      have hc0 := HasTyA.const Δ r [] ⟨.definitionM, 0, A, some v, 0, none⟩ u hres rfl rfl hT0
      simp only [instantiateLevelsA_nil] at hc0
      exact ⟨hc0⟩
    · have hx0 : HasTyA E I n Δ (instantiateLevelsA [] v) (instantiateLevelsA [] A) := by
        simp only [instantiateLevelsA_nil]; exact x
      have hd := TyHRedA.delta Δ r [] ⟨.definitionM, 0, A, some v, 0, none⟩ v hres rfl rfl rfl rfl hx0
      simp only [instantiateLevelsA_nil] at hd
      exact ⟨hd⟩
  exact LRRelA_expand_left hE hI hs (LRRelA_expand_right hE hI hs hvv)

end Clause


#print axioms hStepFnA_prefix
#print axioms hasTyA_constsIn
#print axioms fundHasTyPrefixA
#print axioms fundConvPrefixA
#print axioms hStepFnA_constSpine_none
#print axioms neutKA_const
#print axioms envSemClauseA_rigid
#print axioms envSemClauseA_def
#print axioms structArmA_prefix

end Rcic.Declarative.Ann
