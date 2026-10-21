/-
RCIC F-04: EnvWf transcribes 04 §6 singleton admission at a FIXED
universe arity n (02 §2: a declaration has a finite universe context
size n). EnvClosed / EnvSubst / EnvBodyTyped are theorems over it
(00 §19 O-1). DT-018 is the inductive-group add.

M-001 on EnvBodyTyped: 04 §6 checks the body at admission, not at
every n. Indexing EnvWf by that n (rather than quantifying a second
n₀ inside each constructor) is the statement fix — not universe
cumulativity (DT-021). []→Γ of a closed body is EG-023, folded like
ctxWfLookupValue (hasTyWeaken at cutoff 0). LitLift discharged
(`litLift`; constructor-level `natExpand` is closed).

00 §20.6 (the 02-universes segment) adds three DECLARATION-LEVEL checks
to `EnvWf.indMember` — `hlvlB` (02 §8 level boundedness at the member's
own arity), `hcanon` (05 §2 canonical family universe vector) and
`harities` (05 §3/§11 group arity coherence) — and with them the
corresponding premises on `DT018_inductive_extension_preserves`
(sealed-statement change, recorded at that declaration). The four
singleton constructors are deliberately UNCHANGED: they hardwire
`arity := 0`, so they are level-inert by `instantiateLevels_nil` — by
proof, not by an admission check. That is also why the readout
`envWf_decl_checks` carries a class premise, and why
`envWf_body_arity_zero` is a tripwire rather than a convention.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicIota
import rcic.RcicIndGroupJudgment

namespace Rcic.Declarative

theorem members_empty (r : Nat) : emptyEnv.members r = none := rfl

theorem members_extend_eq (E : ResolvedEnv) (r : Nat) (m : CheckedMember) :
    (extendEnv E r m).members r = some m :=
  if_pos (Eq.refl r)

theorem members_extend_ne (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
    (r' : Nat) (h : r' ≠ r) :
    (extendEnv E r m).members r' = E.members r' := by
  simp only [extendEnv, if_neg h]

/-- Extending a fresh ref preserves old memberships (DT-013 hext). -/
theorem members_extend_preserved {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) :
    ∀ r' m', E.members r' = some m' →
      (extendEnv E r m).members r' = some m' :=
  fun r' m' hm' => by
    have hne : r' ≠ r := by
      intro heq
      subst heq
      rw [hfresh] at hm'
      cases hm'
    rw [members_extend_ne E r m r' hne]
    exact hm'

/-- If `lift c 1 e = e`, then e has no free bvar ≥ c, so instantiating
at any index `j ≥ c` is the identity. -/
theorem lift_id_instantiate (e : Expr Nat) {c : Nat}
    (hc : lift c 1 e = e) (j : Nat) (hj : c ≤ j) (s : Expr Nat) :
    instantiate j s e = e := by
  induction e generalizing c j s with
  | bvar i =>
      have hlt : i < c := by
        cases Nat.lt_or_ge i c with
        | inl h => exact h
        | inr hle =>
            simp only [lift, if_pos hle] at hc
            injection hc with heq
            exact (Nat.ne_of_gt (Nat.lt_succ_self i) heq).elim
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        exact (Nat.not_lt_of_ge hj hlt).elim
      · by_cases hltj : j < i
        · exact (Nat.lt_irrefl i (Nat.lt_trans hlt (Nat.lt_of_le_of_lt hj hltj))).elim
        · rw [if_neg hij, if_neg hltj]
  | sort l => simp only [instantiate]
  | const r ls => simp only [instantiate]
  | app f x ihf ihx =>
      simp only [lift] at hc
      injection hc with hf hx
      simp only [instantiate, ihf hf j hj, ihx hx j hj]
  | lam A b ihA ihb =>
      simp only [lift] at hc
      injection hc with hA hb
      simp only [instantiate, ihA hA j hj, ihb hb (j+1) (Nat.succ_le_succ hj)]
  | pi A b ihA ihb =>
      simp only [lift] at hc
      injection hc with hA hb
      simp only [instantiate, ihA hA j hj, ihb hb (j+1) (Nat.succ_le_succ hj)]
  | letE A v b ihA ihv ihb =>
      simp only [lift] at hc
      injection hc with hA hv hb
      simp only [instantiate, ihA hA j hj, ihv hv j hj,
        ihb hb (j+1) (Nat.succ_le_succ hj)]
  | lit t => simp only [instantiate]

/-! ## 00 §20.6 declaration-level admission checks (05 §2 / §3 / §6)

Three checks that 04/05 perform at addGroup and the tree did not
transcribe. All three are `Bool`-valued and read only the member being
admitted plus the prefix it is admitted over, so each is exactly
"checkable at `indMember` time" — no forward reference, no search over
the group, nothing that a later extension can invalidate. -/

/-- 05 §2: an occurrence of an ALREADY-ADMITTED inductive FAMILY inside a
stored type carries the CANONICAL universe vector
`[param 0, …, param (nU-1)]` at that family's own arity `nU`.

Occurrences of anything else are unconstrained: 04 §6 checks a member
against the PREFIX it is admitted over, and of the group being added only
the family is in that prefix (05 §15 group order: family, constructors,
recursor). A ref absent from the prefix is therefore not a family
occurrence of this group at all. -/
def constLevelsCanonical (E : ResolvedEnv) (r : Nat) (ms : List Level) : Bool :=
  match E.members r with
  | some fm =>
      if fm.mclass = MemberClass.inductiveM then
        decide (ms = (List.range fm.arity).map Level.param)
      else true
  | none => true

/-- `constLevelsCanonical` at every `const` occurrence. Every constructor
IS traversed (02 §5); levels are not de Bruijn scoped, so there is no
cutoff and binders recurse unchanged. -/
def exprFamCanonical (E : ResolvedEnv) : Expr Nat → Bool
  | .bvar _ => true
  | .sort _ => true
  | .const r ms => constLevelsCanonical E r ms
  | .app f x => exprFamCanonical E f && exprFamCanonical E x
  | .lam a b => exprFamCanonical E a && exprFamCanonical E b
  | .pi a b => exprFamCanonical E a && exprFamCanonical E b
  | .letE a v b =>
      exprFamCanonical E a && exprFamCanonical E v && exprFamCanonical E b
  | .lit _ => true

/-- The three inductive-GROUP classes, as a Bool. Lets a `Σ'`-valued
readout refute the four singleton constructors without eliminating the
`Or` premise into `Type` (which large elimination forbids). -/
def isGroupClass : MemberClass → Bool
  | .inductiveM => true
  | .constructorM => true
  | .recursorM => true
  | _ => false

theorem isGroupClass_of {c : MemberClass}
    (h : c = .inductiveM ∨ c = .constructorM ∨ c = .recursorM) :
    isGroupClass c = true := by
  cases h with
  | inl h1 => rw [h1]; rfl
  | inr h1 =>
      cases h1 with
      | inl h2 => rw [h2]; rfl
      | inr h2 => rw [h2]; rfl

/- `piResult`, `piLastDom`, `spineHeadRef`, `memberFamRef` live in
`RcicFamRef`. `EnvWf.indMember` requires `IndGroupAdmitted`, and that
judgment names `memberFamRef`, so the functions cannot sit above it. -/

/-- 05 §3 group arity coherence, in the exact form checkable when a
SINGLE member is admitted over a prefix `E`: a CONSTRUCTOR or RECURSOR
must declare a family (05 §6 result head / 05 §13 major premise) that is
ALREADY in `E` as an inductive, and its universe arity must be the
family's `nU` (constructor) or `nU` / `nU + 1` (recursor — 05 §11: the
AnySort motive level is a suffix parameter). Inductive members and the
singleton classes are unconstrained.

FAIL-CLOSED on an unresolvable family. An earlier form of this check
returned `true` when the type declared no family head, or when the head
was not yet in the prefix. That was vacuous exactly where it had to
bite: 04 §6 / 05 §15 admit a group in order (family, then constructors,
then recursor), so a constructor whose family is NOT in the prefix is
not a group member at all, and letting it pass leaves the arity claim
unavailable at every `IotaWitness` — which is where 00 §20.6's
LevelCoherent discharge reads it (`w.lsC.length = w.famMember.arity`).
Refusing is the direction that adds refusals, never admissions.

M-003 (00 §20.6 DISCHARGE, W6). Content change to a W3 premise of
`EnvWf.indMember` / DT-018:
    old: `none` on either lookup ⇒ `true` (vacuous pass)
    new: `none` on either lookup ⇒ `false` for `.constructorM` /
         `.recursorM`; `.inductiveM` and the singleton classes stay `true`
Strengthening only; every carrier pin below keeps its value, and every
fixture group in `RcicFixtures` admits its family before its
constructors (measured in W3: `memberFamRef` resolves to the group's own
family for `Nat`, `List` and `Vec`). -/
def groupArityCoherent (E : ResolvedEnv) (m : CheckedMember) : Bool :=
  match m.mclass with
  | .constructorM =>
      match memberFamRef m with
      | none => false
      | some f =>
          match E.members f with
          | none => false
          | some fm =>
              decide (fm.mclass = MemberClass.inductiveM) &&
                decide (m.arity = fm.arity)
  | .recursorM =>
      match memberFamRef m with
      | none => false
      | some f =>
          match E.members f with
          | none => false
          | some fm =>
              decide (fm.mclass = MemberClass.inductiveM) &&
                (decide (m.arity = fm.arity) ||
                  decide (m.arity = fm.arity + 1))
  | _ => true

/-- `piCount T = 0` means `T` has no leading binder. -/
theorem piResult_of_piCount_zero : (T : Expr Nat) → piCount T = 0 → piResult T = T
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .pi _ B, h => absurd h (by simp only [piCount]; exact Nat.succ_ne_zero (piCount B))
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

theorem piLastDom_of_piCount_zero : (T : Expr Nat) → piCount T = 0 → piLastDom T = none
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .pi _ B, h => absurd h (by simp only [piCount]; exact Nat.succ_ne_zero (piCount B))
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

/-- A FULL peel identifies the telescope result: this is the bridge from
`IotaWitness.hpeel` (+ `hnpar`) to `memberFamRef` on a constructor. -/
theorem piResult_of_peelPis : (n : Nat) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → n = piCount T → piResult T = r
  | 0, T, ds, r, h, hc => by
      simp only [peelPis] at h
      injection h with h'
      injection h' with _ hr
      rw [← hr]
      exact piResult_of_piCount_zero T hc.symm
  | _ + 1, .bvar _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .sort _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .const _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .app _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lam _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .letE _ _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lit _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .pi A B, ds, r, h, hc => by
      simp only [peelPis] at h
      cases hB : peelPis n B with
      | none => rw [hB] at h; exact Option.noConfusion h
      | some p =>
          rw [hB] at h
          have hpair : (A :: p.1, p.2) = (ds, r) := Option.some.inj h
          have hr : p.2 = r := congrArg Prod.snd hpair
          have hn : n = piCount B := by
            simp only [piCount] at hc
            omega
          have hBs : peelPis n B = some (p.1, p.2) := by rw [hB]
          show piResult B = r
          rw [piResult_of_peelPis n B hBs hn, hr]

/-- A FULL peel identifies the LAST domain: the bridge from
`IotaWitness.hpeelRec` (+ `hnmin`, `hmajorTy`) to `memberFamRef` on a
recursor. `piCount r = 0` is what makes the peel full. -/
theorem piLastDom_of_peelPis : (n : Nat) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (n + 1) T = some (ds, r) → piCount r = 0 → piLastDom T = ds[n]?
  | 0, .pi A B, ds, r, h, hr => by
      simp only [peelPis] at h
      have hpair : ([A], B) = (ds, r) := Option.some.inj h
      have hds : [A] = ds := congrArg Prod.fst hpair
      have hrr : B = r := congrArg Prod.snd hpair
      have hnone : piLastDom B = none :=
        piLastDom_of_piCount_zero B (by rw [hrr]; exact hr)
      rw [← hds]
      simp only [piLastDom, hnone, List.getElem?_cons_zero]
  | 0, .bvar _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .sort _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .const _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .app _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .lam _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .letE _ _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | 0, .lit _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .bvar _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .sort _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .const _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .app _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lam _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .letE _ _ _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lit _, _, _, h, _ => by simp only [peelPis] at h; exact Option.noConfusion h
  | n + 1, .pi A B, ds, r, h, hr => by
      simp only [peelPis] at h
      cases hB : peelPis (n + 1) B with
      | none => rw [hB] at h; exact Option.noConfusion h
      | some p =>
          rw [hB] at h
          have hpair : (A :: p.1, p.2) = (ds, r) := Option.some.inj h
          have hds : A :: p.1 = ds := congrArg Prod.fst hpair
          have hrr : p.2 = r := congrArg Prod.snd hpair
          have hBs : peelPis (n + 1) B = some (p.1, p.2) := by rw [hB]
          have ih : piLastDom B = p.1[n]? :=
            piLastDom_of_peelPis n B hBs (by rw [hrr]; exact hr)
          have hlen : p.1.length = n + 1 := peelPis_length (n + 1) B hBs
          have hlt : n < p.1.length := by rw [hlen]; exact Nat.lt_succ_self n
          have hd : p.1[n]? = some p.1[n] := List.getElem?_eq_getElem hlt
          rw [← hds]
          simp only [piLastDom, ih, hd, List.getElem?_cons_succ]

/-- The ctor result's family head, read through `isFamilyApp`. -/
theorem spineHeadRef_of_isFamilyApp {fam : Nat} {e : Expr Nat}
    (h : isFamilyApp fam e = true) : spineHeadRef e = some fam := by
  unfold isFamilyApp at h
  unfold spineHeadRef
  revert h
  cases appsSpine e with
  | mk hd args =>
      cases hd with
      | const r ms =>
          intro h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          show some r = some fam
          rw [h.1]
      | bvar _ => intro h; exact Bool.noConfusion h
      | sort _ => intro h; exact Bool.noConfusion h
      | app _ _ => intro h; exact Bool.noConfusion h
      | lam _ _ => intro h; exact Bool.noConfusion h
      | pi _ _ => intro h; exact Bool.noConfusion h
      | letE _ _ _ => intro h; exact Bool.noConfusion h
      | lit _ => intro h; exact Bool.noConfusion h



/-! ### Carrier pins — the three §20.6 checks REFUSE something

A one-member prefix suffices to exhibit each check's teeth; the positive
side (every Nat / List / Vec member passing its own admitting prefix)
belongs with those members, in `RcicFixtures`. Each pin below could have
come out the other way. -/

/-- A one-member prefix: an inductive family at ref 0 with `nU = 1`. -/
def pinFamEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.inductiveM, 1, .sort .zero, none⟩

/-- `hlvlB` bites: at arity 1 a stored type may mention `param 0` and
may NOT mention `param 1`. This is what makes `instantiateLevels ls` and
`instantiateLevels (ls.take m.arity)` agree on a stored type. -/
theorem pin_lvlB_refuses :
    exprLevelsBounded 1 (.sort (.param 1) : Expr Nat) = false := rfl

theorem pin_lvlB_admits :
    exprLevelsBounded 1 (.sort (.param 0) : Expr Nat) = true := rfl

/-- `hcanon` bites: a family occurrence carrying anything but 05 §2's
canonical vector is refused. `[Level.zero]` has the right LENGTH and is
still refused — the check is on the vector, not on its arity. -/
theorem pin_canon_refuses :
    exprFamCanonical pinFamEnv (.const 0 [.zero] : Expr Nat) = false := rfl

theorem pin_canon_admits :
    exprFamCanonical pinFamEnv (.const 0 [.param 0] : Expr Nat) = true := rfl

/-- `harities` bites on 05 §3's constructor equality. -/
theorem pin_arity_ctor_refuses :
    groupArityCoherent pinFamEnv
      ⟨.constructorM, 2, .const 0 [.param 0], none⟩ = false := rfl

theorem pin_arity_ctor_admits :
    groupArityCoherent pinFamEnv
      ⟨.constructorM, 1, .const 0 [.param 0], none⟩ = true := rfl

/-- `harities` bites on 05 §11's recursor window: `nU` and `nU + 1` are
admitted (the AnySort motive level is a suffix parameter), `nU + 2` is
not. The family is read off the recursor's LAST domain. -/
theorem pin_arity_rec_admits_nU :
    groupArityCoherent pinFamEnv
      ⟨.recursorM, 1, .pi (.const 0 [.param 0]) (.sort .zero), none⟩ = true := rfl

theorem pin_arity_rec_admits_nU_succ :
    groupArityCoherent pinFamEnv
      ⟨.recursorM, 2, .pi (.const 0 [.param 0]) (.sort .zero), none⟩ = true := rfl

theorem pin_arity_rec_refuses_nU_two :
    groupArityCoherent pinFamEnv
      ⟨.recursorM, 3, .pi (.const 0 [.param 0]) (.sort .zero), none⟩ = false := rfl

/-- `harities` is FAIL-CLOSED: a constructor whose stored type declares
no family head at all is refused, not waved through. -/
theorem pin_arity_ctor_refuses_no_head :
    groupArityCoherent pinFamEnv
      ⟨.constructorM, 1, .sort .zero, none⟩ = false := rfl

/-- …and so is one whose declared family is not in the prefix. Ref 3 is
absent from `pinFamEnv`; the arity would otherwise be unconstrained. -/
theorem pin_arity_ctor_refuses_absent_family :
    groupArityCoherent pinFamEnv
      ⟨.constructorM, 1, .const 3 [.param 0], none⟩ = false := rfl

/-- An inductive member declares no family and stays unconstrained. -/
theorem pin_arity_ind_admits :
    groupArityCoherent pinFamEnv
      ⟨.inductiveM, 7, .sort .zero, none⟩ = true := rfl

/-- 04 §1/§6: environments arise from genesis and accepted addGroup,
at one universe arity n (02 §2). Singleton kinds only here; inductive
groups are DT-018. Closedness of stored types/bodies is the 04 §6
“no local references” check. Inductive/constructor/recursor members
store no delta body (04 §6/§13: the recursor is a checked type).

00 §20.6 MONOMORPHIC DELTA. Every constructor that stores a BODY
hardwires `arity := 0`, and `indMember` — the only one taking a
caller-chosen arity — carries `hnobody`. So delta is monomorphic under
this `EnvWf`: 02 §9's rule is transcribed faithfully but exercised only
at `ls = []`. `envWf_body_arity_zero` below is the tripwire that names
the day a polymorphic-definition constructor is added and reopens the
general level-substitution metatheorem. -/
inductive EnvWf : ResolvedEnv → Nat → Type
  | empty (n : Nat) : EnvWf emptyEnv n
  | axiom {n : Nat} (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level)
      (hE : EnvWf E n) (hfresh : E.members r = none)
      (hA : HasTy E n [] A (.sort u))
      (hcl : ∀ k, lift k 1 A = A) :
      EnvWf (extendEnv E r ⟨.axiomM, 0, A, none⟩) n
  | definition {n : Nat} (E : ResolvedEnv) (r : Nat) (A v : Expr Nat)
      (u : Level)
      (hE : EnvWf E n) (hfresh : E.members r = none)
      (hA : HasTy E n [] A (.sort u)) (hv : HasTy E n [] v A)
      (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v) :
      EnvWf (extendEnv E r ⟨.definitionM, 0, A, some v⟩) n
  | thm {n : Nat} (E : ResolvedEnv) (r : Nat) (A p : Expr Nat)
      (hE : EnvWf E n) (hfresh : E.members r = none)
      (hA : HasTy E n [] A (.sort .zero)) (hp : HasTy E n [] p A)
      (hclA : ∀ k, lift k 1 A = A) (hclp : ∀ k, lift k 1 p = p) :
      EnvWf (extendEnv E r ⟨.theoremM, 0, A, some p⟩) n
  | opaque {n : Nat} (E : ResolvedEnv) (r : Nat) (A v : Expr Nat)
      (u : Level)
      (hE : EnvWf E n) (hfresh : E.members r = none)
      (hA : HasTy E n [] A (.sort u)) (hv : HasTy E n [] v A)
      (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v) :
      EnvWf (extendEnv E r ⟨.opaqueM, 0, A, some v⟩) n
  | indMember {n : Nat} (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (hE : EnvWf E n) (hfresh : E.members r = none)
      (hind : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
        m.mclass = .recursorM)
      (hnobody : m.body = none)
      (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
      -- 00 §19.2 erratum 3 (E-arity): 04/05 check that an inductive
      -- FAMILY's stored type is an arity. Without it a family may be
      -- proof-valued and `Conv.irr` refutes injectivity at the family
      -- head in BOTH halves of `FamAppConvInj`.
      (harity : m.mclass = .inductiveM → isArity m.mtype = true)
      -- 00 §20.6 (02 §8 / 05 §2 / 05 §3), the declaration-level checks
      -- 04/05 perform at addGroup and this judgment did not transcribe.
      -- `hlvlB` is what makes the stored type POLYMORPHIC-but-bounded:
      -- every `param i` it mentions is a universe argument of THIS
      -- member, so `instantiateLevels ls` and `instantiateLevels
      -- (ls.take m.arity)` agree on it (`instantiateLevels_take`).
      (hlvlB : exprLevelsBounded m.arity m.mtype = true)
      (hcanon : exprFamCanonical E m.mtype = true)
      (harities : groupArityCoherent E m = true)
      (hidxAdm : m.mclass = .recursorM → RecursorGroupIdxAdmitted E r m)
      -- 04 §1 and 05 §§6–14, the one inductive-group judgment.
      (hadm : IndGroupAdmitted E r m) :
      EnvWf (extendEnv E r m) n

/-- F-04: EnvClosed is a theorem over EnvWf. -/
def envWf_closed : {E : ResolvedEnv} → {n : Nat} → EnvWf E n → EnvClosed E
  | _, _, .empty _ => fun r m hm => by
      simp only [emptyEnv] at hm
      cases hm
  | _, _, .axiom E r A u hE hfresh hA hcl =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hcl, fun b hb => by cases hb⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_closed hE r' m' hm'
  | _, _, .definition E r A v u hE hfresh hA hv hclA hclv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclv⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_closed hE r' m' hm'
  | _, _, .thm E r A p hE hfresh hA hp hclA hclp =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclp⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_closed hE r' m' hm'
  | _, _, .opaque E r A v u hE hfresh hA hv hclA hclv =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclA, fun b hb => by
            injection hb with hb'; subst hb'; exact hclv⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_closed hE r' m' hm'
  | _, _, .indMember E r m hE hfresh hind hnobody hclT _harity _hlvlB _hcanon
      _harities _hidxAdm _hadm =>
      fun r' m' hm' => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact ⟨hclT, fun b hb => by
            rw [hnobody] at hb
            cases hb⟩
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_closed hE r' m' hm'

/-- F-04: EnvSubst is a theorem over EnvWf. -/
def envWf_subst {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) : EnvSubst E :=
  fun r m hm =>
    let ⟨hclT, hclB⟩ := envWf_closed hE r m hm
    ⟨fun v k => lift_id_instantiate m.mtype (hclT 0) k (Nat.zero_le k) v,
     fun b hb v k => lift_id_instantiate b (hclB b hb 0) k (Nat.zero_le k) v⟩

/-- 00 §20.6 L2 corollary, `lift` side. Closedness survives level
instantiation, so a member's INSTANTIATED type/body is still
`lift`-invariant. This is exactly what `hasTyWeaken`'s `.const` arm and
`stepWeaken`'s `.delta` arm need once the conclusion indices read
`instantiateLevels ls …`: the raw `envWf_closed` equations no longer
match those goals syntactically. -/
theorem envWf_closed_inst {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    ∀ r m, E.members r = some m →
      (∀ ls k, lift k 1 (instantiateLevels ls m.mtype)
          = instantiateLevels ls m.mtype) ∧
      (∀ b, m.body = some b →
        ∀ ls k, lift k 1 (instantiateLevels ls b)
          = instantiateLevels ls b) :=
  fun r m hm =>
    let ⟨hclT, hclB⟩ := envWf_closed hE r m hm
    ⟨fun ls k => instantiateLevels_closed hclT ls k,
     fun b hb ls k => instantiateLevels_closed (hclB b hb) ls k⟩

/-- 00 §20.6 L2 corollary, `instantiate` side (plan B4). The mirror for
`hasTySubst` / `stepSubst` and their `SubstLet` twins. COMPOSED, not
re-proved: level instantiation preserves `lift`-closedness
(`instantiateLevels_closed`, `RcicLevelCalc`), and `lift`-closedness at
cutoff 0 gives `instantiate`-invariance at every index
(`lift_id_instantiate`, above). It lives in this file rather than in
`RcicLevelCalc` for that second ingredient — the reason W1 recorded for
deferring `instantiateLevels_subst_closed` out of `RcicLevelCalc`. -/
theorem envWf_subst_inst {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    ∀ r m, E.members r = some m →
      (∀ ls s k, instantiate k s (instantiateLevels ls m.mtype)
          = instantiateLevels ls m.mtype) ∧
      (∀ b, m.body = some b →
        ∀ ls s k, instantiate k s (instantiateLevels ls b)
          = instantiateLevels ls b) :=
  fun r m hm =>
    let ⟨hclT, hclB⟩ := envWf_closed hE r m hm
    ⟨fun ls s k =>
        lift_id_instantiate (instantiateLevels ls m.mtype)
          (instantiateLevels_closed hclT ls 0) k (Nat.zero_le k) s,
     fun b hb ls s k =>
        lift_id_instantiate (instantiateLevels ls b)
          (instantiateLevels_closed (hclB b hb) ls 0) k (Nat.zero_le k) s⟩


/-- delta is monomorphic under this EnvWf; 02 §9 transcribed faithfully,
exercised only at ls = [].

00 §20.6 TRIPWIRE. `axiom` stores no body; `definition` / `thm` /
`opaque` hardwire `arity := 0`; `indMember` — the only constructor
taking a caller-chosen arity — carries `hnobody`. So under `EnvWf` every
member that HAS a body has universe arity `0`, `HasTy.const`'s
`hlen : ls.length = m.arity` forces `ls = []` at every `Step.delta` /
`ParRed.delta`, and `instantiateLevels [] b = b` closes `oneStepSR`'s
delta arm without a level-substitution metatheorem. The day a
polymorphic-definition constructor is added, THIS lemma goes red — the
failure is loud, not silent, and it names the general
`hasTyInstLevels` / `IotaLevelSubst` obligation that then reopens. -/
def envWf_body_arity_zero : {E : ResolvedEnv} → {n : Nat} → EnvWf E n →
    ∀ r m b, E.members r = some m → m.body = some b → m.arity = 0
  | _, _, .empty _ => fun _ _ _ hm _ => by
      simp only [emptyEnv] at hm
      cases hm
  | _, _, .axiom E r A u hE hfresh _hA _hcl => fun r' m' b hm' hb => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        cases hb
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_body_arity_zero hE r' m' b hm' hb
  | _, _, .definition E r A v u hE hfresh _hA _hv _hclA _hclv =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          rfl
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_body_arity_zero hE r' m' b hm' hb
  | _, _, .thm E r A p hE hfresh _hA _hp _hclA _hclp => fun r' m' b hm' hb => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        rfl
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_body_arity_zero hE r' m' b hm' hb
  | _, _, .opaque E r A v u hE hfresh _hA _hv _hclA _hclv =>
      fun r' m' b hm' hb => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          rfl
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_body_arity_zero hE r' m' b hm' hb
  | _, _, .indMember E r m hE hfresh _hind hnobody _hclT _harity _hlvlB _hcanon
      _harities _hidxAdm _hadm => fun r' m' b hm' hb => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        rw [hnobody] at hb
        cases hb
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_body_arity_zero hE r' m' b hm' hb

/-- DT-018 (02 §14): inductive extension preserves environment
well-formedness — the EnvWf.indMember constructor, quoted.

SEALED STATEMENT CHANGE (M-003, 00 §20.6 F-04 footprint). OLD premises:
`hE hfresh hind hnobody hclT harity hidxAdm`. NEW: the same plus
`hlvlB` / `hcanon` / `harities`, the three declaration-level checks
§20.6 adds to `EnvWf.indMember`. This is a STRENGTHENING of the
premises, i.e. a weakening of the theorem as a rule of inference; it is
the price of 05 §2/§3/§6 being transcribed at all. Nothing that this
judgment previously CONCLUDED has changed. -/
def DT018_inductive_extension_preserves {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} (hE : EnvWf E n) (hfresh : E.members r = none)
    (hind : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
      m.mclass = .recursorM)
    (hnobody : m.body = none)
    (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
    (harity : m.mclass = .inductiveM → isArity m.mtype = true)
    (hlvlB : exprLevelsBounded m.arity m.mtype = true)
    (hcanon : exprFamCanonical E m.mtype = true)
    (harities : groupArityCoherent E m = true)
    (hidxAdm : m.mclass = .recursorM → RecursorGroupIdxAdmitted E r m)
    (hadm : IndGroupAdmitted E r m) :
    EnvWf (extendEnv E r m) n :=
  .indMember E r m hE hfresh hind hnobody hclT harity hlvlB hcanon harities
    hidxAdm hadm

/-- Admission rank: length of the EnvWf derivation (cons-shaped
prefix chain). Outer measure for Takahashi `devel`. -/
def envWf_rank {E : ResolvedEnv} {n : Nat} : EnvWf E n → Nat
  | .empty _ => 0
  | .axiom _ _ _ _ hE _ _ _ => envWf_rank hE + 1
  | .definition _ _ _ _ _ hE _ _ _ _ _ => envWf_rank hE + 1
  | .thm _ _ _ _ hE _ _ _ _ _ => envWf_rank hE + 1
  | .opaque _ _ _ _ _ hE _ _ _ _ _ => envWf_rank hE + 1
  | .indMember _ _ _ hE _ _ _ _ _ _ _ _ _ _ => envWf_rank hE + 1

/-- Invert membership through EnvWf: `m` at `r` was admitted over a
strict prefix `E0` (`hfresh` forbids a second extend of the same
ref). `extendEnv` is a function overlay; the DERIVATION is cons. -/
def envWf_of_member {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember} :
    (hE : EnvWf E n) → E.members r = some m →
    Σ' (E0 : ResolvedEnv) (hE0 : EnvWf E0 n),
      (E0.members r = none) ×' (envWf_rank hE0 < envWf_rank hE)
  | .empty _, hm => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A u hE0 hfresh _hA _hcl, hm =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hE0, hfresh, Nat.lt_succ_self (envWf_rank hE0)⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
          exact hm
        let ⟨E1, hE1, hnone, hlt⟩ := envWf_of_member hE0 hm0
        exact ⟨E1, hE1, hnone,
          Nat.lt_trans hlt (Nat.lt_succ_self (envWf_rank hE0))⟩
  | .definition E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hE0, hfresh, Nat.lt_succ_self (envWf_rank hE0)⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, hE1, hnone, hlt⟩ := envWf_of_member hE0 hm0
        exact ⟨E1, hE1, hnone,
          Nat.lt_trans hlt (Nat.lt_succ_self (envWf_rank hE0))⟩
  | .thm E0 r0 A p hE0 hfresh _hA _hp _hclA _hclp, hm =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hE0, hfresh, Nat.lt_succ_self (envWf_rank hE0)⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
          exact hm
        let ⟨E1, hE1, hnone, hlt⟩ := envWf_of_member hE0 hm0
        exact ⟨E1, hE1, hnone,
          Nat.lt_trans hlt (Nat.lt_succ_self (envWf_rank hE0))⟩
  | .opaque E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hE0, hfresh, Nat.lt_succ_self (envWf_rank hE0)⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, hE1, hnone, hlt⟩ := envWf_of_member hE0 hm0
        exact ⟨E1, hE1, hnone,
          Nat.lt_trans hlt (Nat.lt_succ_self (envWf_rank hE0))⟩
  | .indMember E0 r0 m0 hE0 hfresh _hind _hnobody _hclT _harity _hlvlB _hcanon
      _harities _hidxAdm _hadm, hm =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hE0, hfresh, Nat.lt_succ_self (envWf_rank hE0)⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 m0 r hrr] at hm
          exact hm
        let ⟨E1, hE1, hnone, hlt⟩ := envWf_of_member hE0 hm0
        exact ⟨E1, hE1, hnone,
          Nat.lt_trans hlt (Nat.lt_succ_self (envWf_rank hE0))⟩

/-- The prefix returned by `envWf_of_member` is a member-subset of `E`.
Proved by the same cons-walk as `envWf_of_member`. -/
def envWf_prefix_members {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} :
    (hE : EnvWf E n) → (hm : E.members r = some m) →
    ∀ r' m', (envWf_of_member hE hm).1.members r' = some m' →
      E.members r' = some m'
  | .empty _, hm => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A u hE0 hfresh hA hcl, hm =>
      fun r' m' hpre =>
        if hrr : r = r0 then by
          subst hrr
          have hm' := hm
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          revert hpre
          simp [envWf_of_member]
          intro hpre
          exact members_extend_preserved hfresh r' m' hpre
        else by
          have hm0 : E0.members r = some m := by
            rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
            exact hm
          revert hpre
          simp [envWf_of_member, dif_neg hrr]
          intro hpre
          have hmid := envWf_prefix_members hE0 hm0 r' m' hpre
          exact members_extend_preserved hfresh r' m' hmid
  | .definition E0 r0 A v u hE0 hfresh hA hv hclA hclv, hm =>
      fun r' m' hpre =>
        if hrr : r = r0 then by
          subst hrr
          have hm' := hm
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          revert hpre
          simp [envWf_of_member]
          intro hpre
          exact members_extend_preserved hfresh r' m' hpre
        else by
          have hm0 : E0.members r = some m := by
            rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr]
              at hm
            exact hm
          revert hpre
          simp [envWf_of_member, dif_neg hrr]
          intro hpre
          have hmid := envWf_prefix_members hE0 hm0 r' m' hpre
          exact members_extend_preserved hfresh r' m' hmid
  | .thm E0 r0 A p hE0 hfresh hA hp hclA hclp, hm =>
      fun r' m' hpre =>
        if hrr : r = r0 then by
          subst hrr
          have hm' := hm
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          revert hpre
          simp [envWf_of_member]
          intro hpre
          exact members_extend_preserved hfresh r' m' hpre
        else by
          have hm0 : E0.members r = some m := by
            rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
            exact hm
          revert hpre
          simp [envWf_of_member, dif_neg hrr]
          intro hpre
          have hmid := envWf_prefix_members hE0 hm0 r' m' hpre
          exact members_extend_preserved hfresh r' m' hmid
  | .opaque E0 r0 A v u hE0 hfresh hA hv hclA hclv, hm =>
      fun r' m' hpre =>
        if hrr : r = r0 then by
          subst hrr
          have hm' := hm
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          revert hpre
          simp [envWf_of_member]
          intro hpre
          exact members_extend_preserved hfresh r' m' hpre
        else by
          have hm0 : E0.members r = some m := by
            rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
            exact hm
          revert hpre
          simp [envWf_of_member, dif_neg hrr]
          intro hpre
          have hmid := envWf_prefix_members hE0 hm0 r' m' hpre
          exact members_extend_preserved hfresh r' m' hmid
  | .indMember E0 r0 m0 hE0 hfresh hind hnobody hclT _harity _hlvlB _hcanon
      _harities _hidxAdm _hadm, hm =>
      fun r' m' hpre =>
        if hrr : r = r0 then by
          subst hrr
          have hm' := hm
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          revert hpre
          simp [envWf_of_member]
          intro hpre
          exact members_extend_preserved hfresh r' m' hpre
        else by
          have hm0 : E0.members r = some m := by
            rw [members_extend_ne E0 r0 m0 r hrr] at hm
            exact hm
          revert hpre
          simp [envWf_of_member, dif_neg hrr]
          intro hpre
          have hmid := envWf_prefix_members hE0 hm0 r' m' hpre
          exact members_extend_preserved hfresh r' m' hmid

/-- The stored body of `m` at `r` is typed in the admitting prefix. -/
def envWf_of_member_typed {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} {b : Expr Nat} :
    (hE : EnvWf E n) → (hm : E.members r = some m) →
    (hb : m.body = some b) →
    HasTy (envWf_of_member hE hm).1 n [] b m.mtype
  | .empty _, hm, _ => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A u hE0 hfresh hA hcl, hm, hb =>
      if hrr : r = r0 then by
        subst hrr
        have hm' := hm
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        cases hb
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
          exact hm
        revert hb
        simp [envWf_of_member, dif_neg hrr]
        intro hb
        exact envWf_of_member_typed hE0 hm0 hb
  | .definition E0 r0 A v u hE0 hfresh hA hv hclA hclv, hm, hb =>
      if hrr : r = r0 then by
        subst hrr
        have hm' := hm
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        injection hb with hbv
        subst hbv
        simp [envWf_of_member]
        exact hv
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr] at hm
          exact hm
        revert hb
        simp [envWf_of_member, dif_neg hrr]
        intro hb
        exact envWf_of_member_typed hE0 hm0 hb
  | .thm E0 r0 A p hE0 hfresh hA hp hclA hclp, hm, hb =>
      if hrr : r = r0 then by
        subst hrr
        have hm' := hm
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        injection hb with hbp
        subst hbp
        simp [envWf_of_member]
        exact hp
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
          exact hm
        revert hb
        simp [envWf_of_member, dif_neg hrr]
        intro hb
        exact envWf_of_member_typed hE0 hm0 hb
  | .opaque E0 r0 A v u hE0 hfresh hA hv hclA hclv, hm, hb =>
      if hrr : r = r0 then by
        subst hrr
        have hm' := hm
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        injection hb with hbv
        subst hbv
        simp [envWf_of_member]
        exact hv
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
          exact hm
        revert hb
        simp [envWf_of_member, dif_neg hrr]
        intro hb
        exact envWf_of_member_typed hE0 hm0 hb
  | .indMember E0 r0 m0 hE0 hfresh hind hnobody hclT _harity _hlvlB _hcanon
      _harities _hidxAdm _hadm, hm, hb =>
      if hrr : r = r0 then by
        subst hrr
        have hm' := hm
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        rw [hnobody] at hb
        cases hb
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 m0 r hrr] at hm
          exact hm
        revert hb
        simp [envWf_of_member, dif_neg hrr]
        intro hb
        exact envWf_of_member_typed hE0 hm0 hb

/-- Invert a recursor membership to the 05 index-position admission
recorded at recursor-add. Prefix `E0` is the env *before* the
recursor (ctors already in `E0`). -/
def envWf_recursor_admitted {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} :
    (hE : EnvWf E n) → (hm : E.members r = some m) →
    (hk : m.mclass = .recursorM) →
    Σ' (E0 : ResolvedEnv),
      RecursorGroupIdxAdmitted E0 r m ×'
      (∀ r' m', E0.members r' = some m' → E.members r' = some m')
  | .empty _, hm, _ => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A u hE0 hfresh _hA _hcl, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        nomatch hk
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
          exact hm
        let ⟨E1, adm, hext⟩ := envWf_recursor_admitted hE0 hm0 hk
        exact ⟨E1, adm, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .definition E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        nomatch hk
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, adm, hext⟩ := envWf_recursor_admitted hE0 hm0 hk
        exact ⟨E1, adm, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .thm E0 r0 A p hE0 hfresh _hA _hp _hclA _hclp, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        nomatch hk
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
          exact hm
        let ⟨E1, adm, hext⟩ := envWf_recursor_admitted hE0 hm0 hk
        exact ⟨E1, adm, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .opaque E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        nomatch hk
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, adm, hext⟩ := envWf_recursor_admitted hE0 hm0 hk
        exact ⟨E1, adm, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .indMember E0 r0 m0 hE0 hfresh _hind _hnobody _hclT _harity _hlvlB _hcanon
      _harities hidxAdm _hadm, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hidxAdm hk, members_extend_preserved hfresh⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 m0 r hrr] at hm
          exact hm
        let ⟨E1, adm, hext⟩ := envWf_recursor_admitted hE0 hm0 hk
        exact ⟨E1, adm, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩


/-- 00 §20.6 readout of the three declaration-level checks, in the shape
`envWf_recursor_admitted` already uses: the E-relative checks are
recovered on the PREFIX `E0` the member was admitted over (04 §6 checks
a member against its prefix), together with `E0 ⊆ E`.

`exprLevelsBounded` is E-independent, so it comes back at `E` directly.
The class premise is required and cannot be dropped: 00 §20.6 leaves
`axiom` / `definition` / `thm` / `opaque` unchanged — they are level-
inert by `arity = 0` and `instantiateLevels_nil`, by PROOF rather than
by an admission check, so no level-boundedness claim holds of their
stored types.

WHAT IT BUYS (the F-04 footprint W2 recorded at `ctorSpine_famApp` /
`applyTel_recPrefix_idx_last`): `hcanon` says the family occurrence in a
constructor/recursor type carries `[param 0, …, param (nU-1)]`, and
`hlvlB` says every such `param i` has `i < m.arity`; together they give
`nU ≤ m.arity`, which `HasTy.const`'s `hlen` turns into the premise
`famMember.arity ≤ ls.length`. `harities` gives the sharp 05 §3 form
(`= nU` for a constructor, `∈ {nU, nU+1}` for a recursor) once the
family is identified — which `piResult_of_peelPis` /
`piLastDom_of_peelPis` + `spineHeadRef_of_isFamilyApp` do from
`hpeel`/`hfamApp` and `hpeelRec`/`hmajorTy`. -/
def envWf_decl_checks {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} :
    (hE : EnvWf E n) → (hm : E.members r = some m) →
    (hk : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
      m.mclass = .recursorM) →
    Σ' (E0 : ResolvedEnv),
      (exprLevelsBounded m.arity m.mtype = true) ×'
      (exprFamCanonical E0 m.mtype = true) ×'
      (groupArityCoherent E0 m = true) ×'
      (∀ r' m', E0.members r' = some m' → E.members r' = some m')
  | .empty _, hm, _ => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A u hE0 hfresh _hA _hcl, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact Bool.noConfusion (isGroupClass_of hk)
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
          exact hm
        let ⟨E1, hb, hc, ha, hext⟩ := envWf_decl_checks hE0 hm0 hk
        exact ⟨E1, hb, hc, ha, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .definition E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact Bool.noConfusion (isGroupClass_of hk)
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, hb, hc, ha, hext⟩ := envWf_decl_checks hE0 hm0 hk
        exact ⟨E1, hb, hc, ha, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .thm E0 r0 A p hE0 hfresh _hA _hp _hclA _hclp, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact Bool.noConfusion (isGroupClass_of hk)
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
          exact hm
        let ⟨E1, hb, hc, ha, hext⟩ := envWf_decl_checks hE0 hm0 hk
        exact ⟨E1, hb, hc, ha, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .opaque E0 r0 A v u hE0 hfresh _hA _hv _hclA _hclv, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact Bool.noConfusion (isGroupClass_of hk)
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
          exact hm
        let ⟨E1, hb, hc, ha, hext⟩ := envWf_decl_checks hE0 hm0 hk
        exact ⟨E1, hb, hc, ha, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩
  | .indMember E0 r0 m0 hE0 hfresh _hind _hnobody _hclT _harity hlvlB hcanon
      harities _hidxAdm _hadm, hm, hk =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact ⟨E0, hlvlB, hcanon, harities, members_extend_preserved hfresh⟩
      else by
        have hm0 : E0.members r = some m := by
          rw [members_extend_ne E0 r0 m0 r hrr] at hm
          exact hm
        let ⟨E1, hb, hc, ha, hext⟩ := envWf_decl_checks hE0 hm0 hk
        exact ⟨E1, hb, hc, ha, fun r' m' hpre =>
          members_extend_preserved hfresh r' m' (hext r' m' hpre)⟩

/-- 00 §20.6 DISCHARGE, the arity half. Reads 05 §3 group arity
coherence off `EnvWf` at the FULL environment: the member's stored type
declares family `f` (determinate from `m.mtype` — `memberFamRef`), the
admission check pinned that `f` was already an inductive in the prefix
with the 05 §3 arity, and prefix ⊆ E identifies that family member with
the one the caller sees in `E`.

This is exactly the step the vacuous form of `groupArityCoherent` could
not take: with the fail-closed form, `E0.members f` is `some`, so
`envWf_prefix_members`-style transport is available in the one direction
it is needed.

`hk` is the Bool reflection (`isGroupClass`) rather than an `Or`,
because the result is a `Σ'` in `Type` and large elimination on a `Prop`
disjunction is rejected. -/
def envWf_group_arity {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} {f : Nat} {fm : CheckedMember}
    (hE : EnvWf E n) (hm : E.members r = some m)
    (hk : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
      m.mclass = .recursorM)
    (hf : memberFamRef m = some f) (hfam : E.members f = some fm) :
    ((m.mclass = .constructorM) → m.arity = fm.arity) ×'
    ((m.mclass = .recursorM) →
      m.arity = fm.arity ∨ m.arity = fm.arity + 1) := by
  have ⟨E0, _hb, _hc, ha, hext⟩ := envWf_decl_checks hE hm hk
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
        exact ha'.2
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ha'
        exact ha'.2

/-- `spineHeadRef` of a const-headed `foldApps`. -/
theorem spineHeadRef_foldApps_const (f : Nat) (ms : List Level)
    (args : List (Expr Nat)) :
    spineHeadRef (foldApps (.const f ms) args) = some f := by
  unfold spineHeadRef
  rw [appsSpine_foldApps]
  simp only [appsSpine_const]

/-- 00 §20.6 DISCHARGE. An `IotaWitness`'s constructor member declares
the witness's own `familyRef`: `hpeel` + `hnpar` identify `piResult` with
`ctorResult`, and `hfamApp` fixes that result's head. -/
theorem memberFamRef_ctorMember {E : ResolvedEnv} (w : IotaWitness E) :
    memberFamRef w.ctorMember = some w.familyRef := by
  unfold memberFamRef
  rw [w.hctorK]
  have hpr : piResult w.ctorMember.mtype = w.ctorResult :=
    piResult_of_peelPis (w.nparams + w.fields.length) w.ctorMember.mtype
      w.hpeel w.hnpar
  rw [hpr]
  exact spineHeadRef_of_isFamilyApp w.hfamApp

/-- 00 §20.6 DISCHARGE, recursor side. `hpeelRec` + `hrecBody` put the
major premise in the LAST domain slot, and `hmajorTy` fixes its head. -/
theorem memberFamRef_recMember {E : ResolvedEnv} (w : IotaWitness E) :
    memberFamRef w.recMember = some w.familyRef := by
  have hbody0 : piCount w.recBody = 0 := by
    rw [w.hrecBody, foldApps_snoc]
    rfl
  have hld :
      piLastDom w.recMember.mtype =
        w.recDoms[w.nparams + 1 + w.nMinors + w.nindices]? :=
    piLastDom_of_peelPis (w.nparams + 1 + w.nMinors + w.nindices)
      w.recMember.mtype w.hpeelRec hbody0
  unfold memberFamRef
  rw [w.hrecK, hld, w.hmajorTy]
  exact spineHeadRef_foldApps_const _ _ _

/-- 05 §3 at an `IotaWitness`: the constructor's universe arity IS the
family's `nU`. This is the fact 00 §20.6's DISCHARGE needs to turn
`hasTyConstInv`'s `hlen` (`w.lsC.length = w.ctorMember.arity`) into
`w.lsC.length = w.famMember.arity`, i.e. into `w.lsC.take nU = w.lsC`. -/
theorem witness_ctorArity {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (w : IotaWitness E) : w.ctorMember.arity = w.famMember.arity :=
  (envWf_group_arity hE w.hctor (Or.inr (Or.inl w.hctorK))
    (memberFamRef_ctorMember w) w.hfam).1 w.hctorK

/-- 05 §11 at an `IotaWitness`: the recursor's universe arity is `nU` or
`nU + 1` (the AnySort motive level is a suffix parameter). Gives
`w.famMember.arity ≤ w.ls.length` once `hasTyConstInv`'s `hlen` supplies
`w.ls.length = w.recMember.arity`. -/
theorem witness_recArity {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (w : IotaWitness E) :
    w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 :=
  (envWf_group_arity hE w.hrec (Or.inr (Or.inr w.hrecK))
    (memberFamRef_recMember w) w.hfam).2 w.hrecK

/-- 00 §20.6 STORED-TYPE VIEWS, the boundedness behind view (2): a
constructor's stored type mentions no universe parameter beyond the
family arity. `hlvlB` gives it at `w.ctorMember.arity`; 05 §3
(`witness_ctorArity`) renames that to `w.famMember.arity`. -/
theorem witness_ctor_lvlB {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (w : IotaWitness E) :
    exprLevelsBounded w.famMember.arity w.ctorMember.mtype = true := by
  have ⟨_E0, hb, _hc, _ha, _hext⟩ :=
    envWf_decl_checks hE w.hctor (Or.inr (Or.inl w.hctorK))
  rw [← witness_ctorArity hE w]
  exact hb

/-- 00 §20.6 STORED-TYPE VIEW (2) = VIEW (1) on the constructor's stored
type: instantiating at a level list and instantiating at its `nU`-prefix
agree, because nothing past slot `nU` occurs. This is the equation that
lets the recursor-side view `instantiateLevels w.ls ctorMember.mtype`
(what `hctorAfter` / `hparamAlign` / `hidxTy` read) be compared with the
lhs-side view `instantiateLevels w.lsC ctorMember.mtype` (what the
major's own typing produces) through `eqNList w.lsC (w.ls.take nU)`
alone — a `Conv`, never a syntactic equation. -/
theorem witness_ctorMtype_view {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (w : IotaWitness E) (lvls : List Level) :
    instantiateLevels lvls w.ctorMember.mtype =
      instantiateLevels (lvls.take w.famMember.arity) w.ctorMember.mtype :=
  instantiateLevels_take w.famMember.arity lvls w.ctorMember.mtype
    (witness_ctor_lvlB hE w)

/-- `IotaTyping` is an EnvWf readout, not a HasTy-of-lhs property.
Walks are ctor-declaration positions (05 admission); lhs args are
instances. `oneStepSR` iota arm calls this with `hE`. -/
def envWf_iotaTyping {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) (w : IotaWitness E) : IotaTyping E w :=
  let ⟨_E0, adm, hext⟩ := envWf_recursor_admitted hE w.hrec w.hrecK
  adm.typing hext w.hrec w rfl rfl

end Rcic.Declarative
