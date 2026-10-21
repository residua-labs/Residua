import rcic.RcicTypedScopeAdmission
import rcic.RcicTypedStrengthen
import rcic.RcicIARecIH

/-!
# Route C, lane C2-1: the two recorded-telescope retyping residues

`RcicTypedScopeAdmission` leaves two named transports open:
`FamilyHeaderRetypingRemaining` (the family's telescope typed in HeaderScope
`E` at its recorded levels, from a view whose `domainsTyped` lives in the
self extension `extendEnv E f fm`) and `ConstructorRecordedRetypingRemaining`
(a constructor's telescope typed in ConstructorScope `S` at the levels recorded
against its actual admission prefix `A`).

This module separates what the group's own admission cells already supply from
the two residuals.

* **Free content, no transport.**  Admission stores whole-type typings in the
  target scope already: the family's `typeTyped` in `E`
  (`ScopeMemberAdmissionT`) and each constructor's `constructorScopeTyped` in
  `S`.  Both `storedType` fields present the stored type as a `policyPi` tower
  over the view's telescope, so iterated `hasTyTInv_pi`
  (`hasTyT_policyPi_invT`) types every telescope domain in the target scope —
  at *some* labels (`exists_telTypedT_headerScope`,
  `exists_telTypedT_constructorScope`).  No environment restriction is used.

* **Residual (label alignment).**  `TelTypedT` at the recorded
  `domainsTyped.levels` follows once those labels are `eqN` to some in-scope
  labels (`_of_aligned`), and the `iff` restatements say that is exactly the
  obligation: the recorded-labels version is an aligned telescope.  The
  missing theorem — `eqN` between the level a derivation in `E`/`S` inverts
  to and the label `hasType` recorded against `extendEnv E f fm`/`A` — is the
  level-uniqueness debt this lane does not discharge and does not assume.

* **Residual (clean transport).**  `hasTyT_strengthenC` restricts a derivation
  along `EnvAgreeBelow` only when the derivation is `cleanHasTyT`; admission's
  `IndGroupTypedT` evidence (`FamilyTypedT v` / `CtorTypedT c`) IS the
  recorded-labels `HasTyT` telescope in the extension/prefix, but it is
  `Nonempty`-wrapped and carries no cleanliness, so the transport is stated
  two ways: per-domain clean derivations as data (`_of_clean`) and the
  admission-shaped form taking `FamilyTypedT`/`CtorTypedT` plus
  "every derivation is clean below the cut" (`_of_familyTypedT`,
  `_of_ctorTypedT`).  For the family the agreement is
  `envAgreeBelow_extendEnv_self`; for a constructor the prefix `A` agrees
  with `S` below `f + 1` (`envAgreeBelow_groupEnvT_ctorScope`,
  `envAgreeBelow_extendEnv_foldl`).

The syntactic-support facts the module already extracts are reused:
`hasTyT_constsIn` + `constsIn_policyPi_domain` give `ConstsIn`-in-scope of
every domain (`familyHeaderDomain_constsIn`,
`constructorScope_domain_constsIn`), and `constsIn_drop_extension` drops
support out of the self extension where domains are `f`-free
(`familyHeaderDomain_constsIn_of_extension`).

No landed declaration is changed; nothing below asserts either obligation.
`closure_claim = 0`.
-/

namespace Rcic.Declarative

/-! ## (1) inversion in the target scope -/

/-- a `policyPi`-stored whole type supplies the telescope's typed content at
    SOME labels, in the same environment: `hasTyT_policyPi_invT` iterated to a
    label function, then flattened to `TelTypedT`'s empty-tail contexts. -/
theorem exists_telTypedT_of_policyPi {E : ResolvedEnv} {n : Nat}
    {ds : List (Expr Nat)} {body : Expr Nat} {u : Level}
    (h : Nonempty (HasTyT E n [] (policyPi ds body) (.sort u))) :
    ∃ ls : Fin ds.length → Level, TelTypedT E n ds ls := by
  obtain ⟨d⟩ := h
  obtain ⟨lv, hlv⟩ := hasTyT_policyPi_invT ds d
  exact ⟨lv, fun i => (hlv i).elim fun di =>
    ⟨by simpa only [List.append_nil] using di⟩⟩

/-! ## (2) label shifts and scope agreements -/

/-- telescope typings are `eqN`-closed in their labels: each domain's sort
    label shifts by `ConvT.sorts` under `HasTyT.conv`. -/
theorem telTypedT_of_eqN {E : ResolvedEnv} {n : Nat}
    {ds : List (Expr Nat)} {ls ls' : Fin ds.length → Level}
    (ht : TelTypedT E n ds ls) (halign : ∀ i, eqN (ls i) (ls' i)) :
    TelTypedT E n ds ls' :=
  fun i => (ht i).elim fun d =>
    ⟨.conv _ _ _ _ _ d (.sorts _ _ _ (halign i))⟩

/-- the family's own extension agrees with the base below `f`: the extension
    adds only the member at `f`. -/
theorem envAgreeBelow_extendEnv_self (E : ResolvedEnv) (f : Nat)
    (fm : CheckedMember) :
    EnvAgreeBelow (extendEnv E f fm) E f :=
  EnvAgreeBelow.extendEnv_left (EnvAgreeBelow.refl E f) (Nat.le_refl f)

/-- a prefix built by admitting members all at or above a cut keeps agreeing
    with the scope below the cut: the actual `GroupMembersT.cons` layering. -/
theorem envAgreeBelow_extendEnv_foldl {E : ResolvedEnv} {k : Nat} :
    ∀ (ms : List (Nat × CheckedMember)) {acc : ResolvedEnv},
      EnvAgreeBelow acc E k → (∀ p ∈ ms, k ≤ p.1) →
      EnvAgreeBelow (ms.foldl (fun a p => extendEnv a p.1 p.2) acc) E k
  | [], _, h, _ => h
  | p :: ms, _, h, hms => by
      simpa only [List.foldl_cons] using envAgreeBelow_extendEnv_foldl ms
        (EnvAgreeBelow.extendEnv_left h (hms p (List.mem_cons_self p ms)))
        (fun q hq => hms q (List.mem_cons.mpr (Or.inr hq)))

/-- the `groupEnvT` form: every constructor ref above `f` (`GroupInScopeT`'s
    `hlayout` supplies the bound at real groups), so a group prefix agrees
    with ConstructorScope `extendEnv E f fm` below `f + 1`. -/
theorem envAgreeBelow_groupEnvT_ctorScope {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} :
    ∀ (cs : List (Nat × CheckedMember)), (∀ c ∈ cs, f < c.1) →
      EnvAgreeBelow (groupEnvT E f fm cs) (extendEnv E f fm) (f + 1)
  | [], _ => EnvAgreeBelow.refl _ _
  | c :: cs, hcs =>
      EnvAgreeBelow.extendEnv_left
        (envAgreeBelow_groupEnvT_ctorScope cs
          (fun c' hc' => hcs c' (List.mem_cons.mpr (Or.inr hc'))))
        (hcs c (List.mem_cons_self c cs))

/-! ## (3) the one general strengthening instance -/

/-- the premise shape a clean transport needs: every domain has a derivation
    whose every node is clean below `k`. -/
def CleanTelDataT (E : ResolvedEnv) (n k : Nat) (ds : List (Expr Nat))
    (ls : Fin ds.length → Level) : Prop :=
  ∀ i : Fin ds.length,
    ∃ d : HasTyT E n (policyPrefixContext ds i.val) ds[i.val] (.sort (ls i)),
      cleanHasTyT k d

/-- telescope strengthening: `hasTyT_strengthenC` lifted from a single domain
    to the whole telescope.  The recorded labels are kept verbatim — the
    transport does not recompute universes. -/
theorem telTypedT_of_agreeBelow {E' E : ResolvedEnv} {n k : Nat}
    {ds : List (Expr Nat)} {ls : Fin ds.length → Level}
    (hagree : EnvAgreeBelow E' E k) (hclean : CleanTelDataT E' n k ds ls)
    (hctx : ∀ i : Fin ds.length,
      ctxConstsBelow k (policyPrefixContext ds i.val) = true) :
    TelTypedT E n ds ls :=
  fun i => (hclean i).elim fun d hc =>
    hasTyT_strengthenC hagree d hc (hctx i)

/-! ## (4) the family obligation -/

/-- HeaderScope content is admission's own supply: the family's whole-type
    typing `hT` already lives in `E`, and its stored type is the `policyPi`
    tower over `parameters ++ indices`, so inversion reads every domain in
    `E` at SOME labels. -/
theorem exists_telTypedT_headerScope {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)} {u : Level}
    (hT : Nonempty (HasTyT E v.member.arity [] v.member.mtype (.sort u))) :
    ∃ ls : Fin (v.parameters ++ v.indices).length → Level,
      TelTypedT E v.member.arity (v.parameters ++ v.indices) ls := by
  rw [v.storedType] at hT
  exact exists_telTypedT_of_policyPi hT

/-- the same content read off an actual admission receipt: `typeTyped` is the
    family's whole-type typing in its prefix `E` (the base, HeaderScope). -/
theorem exists_telTypedT_headerScope_of_admission {S E : ResolvedEnv}
    {f : Nat} {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)}
    (a : ScopeMemberAdmissionT S E f fm) (hm : v.member = fm) :
    ∃ ls : Fin (v.parameters ++ v.indices).length → Level,
      TelTypedT E v.member.arity (v.parameters ++ v.indices) ls := by
  have aux : ∀ m : CheckedMember, ScopeMemberAdmissionT S E f m →
      m = v.member →
      ∃ ls : Fin (v.parameters ++ v.indices).length → Level,
        TelTypedT E v.member.arity (v.parameters ++ v.indices) ls := by
    intro m a' heq
    subst heq
    exact exists_telTypedT_headerScope ⟨a'.typeTyped⟩
  exact aux fm a hm.symm

/-- `FamilyHeaderRetypingRemaining` under label alignment: any in-scope
    telescope typing at labels `eqN` to the recorded ones shifts to the
    recorded labels. -/
theorem familyHeaderRetypingRemaining_of_aligned {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)}
    {ls : Fin (v.parameters ++ v.indices).length → Level}
    (htel : TelTypedT E v.member.arity (v.parameters ++ v.indices) ls)
    (halign : ∀ i, eqN (ls i) (v.domainsTyped.levels i)) :
    FamilyHeaderRetypingRemaining E f fm v :=
  telTypedT_of_eqN htel halign

/-- `FamilyHeaderRetypingRemaining` under clean transport: the self extension
    agrees with `E` below `f`, so `cleanHasTyT f` derivations of the recorded
    typings strengthen to `E`, keeping the recorded labels exactly. -/
theorem familyHeaderRetypingRemaining_of_clean {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)}
    (hclean : CleanTelDataT (extendEnv E f fm) v.member.arity f
      (v.parameters ++ v.indices) v.domainsTyped.levels)
    (hctx : ∀ i : Fin (v.parameters ++ v.indices).length,
      ctxConstsBelow f (policyPrefixContext (v.parameters ++ v.indices) i.val)
        = true) :
    FamilyHeaderRetypingRemaining E f fm v :=
  telTypedT_of_agreeBelow (envAgreeBelow_extendEnv_self E f fm) hclean hctx

/-- `FamilyHeaderRetypingRemaining` from the admission-supplied typed
    telescope: `IndGroupTypedT` on the family cell gives `FamilyTypedT v`,
    the recorded-labels `HasTyT` derivations in the self extension.  If every
    derivation of those typings is clean below `f` — the part `Nonempty`
    hides — they strengthen to `E` verbatim, labels included. -/
theorem familyHeaderRetypingRemaining_of_familyTypedT {E : ResolvedEnv}
    {f : Nat} {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)}
    (hT : FamilyTypedT v)
    (hclean : ∀ i : Fin (v.parameters ++ v.indices).length,
      ∀ d : HasTyT (extendEnv E f fm) v.member.arity
        (policyPrefixContext (v.parameters ++ v.indices) i.val)
        (v.parameters ++ v.indices)[i.val] (.sort (v.domainsTyped.levels i)),
      cleanHasTyT f d)
    (hctx : ∀ i : Fin (v.parameters ++ v.indices).length,
      ctxConstsBelow f (policyPrefixContext (v.parameters ++ v.indices) i.val)
        = true) :
    FamilyHeaderRetypingRemaining E f fm v :=
  fun i => (hT i).elim fun d =>
    hasTyT_strengthenC (envAgreeBelow_extendEnv_self E f fm) d (hclean i d)
      (hctx i)

/-- the obligation, restated: it is exactly a HeaderScope telescope at some
    labels, `eqN`-aligned with the recorded labels. -/
theorem familyHeaderRetypingRemaining_iff {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)} :
    FamilyHeaderRetypingRemaining E f fm v ↔
      ∃ ls : Fin (v.parameters ++ v.indices).length → Level,
        TelTypedT E v.member.arity (v.parameters ++ v.indices) ls ∧
          ∀ i, eqN (ls i) (v.domainsTyped.levels i) :=
  ⟨fun h => ⟨v.domainsTyped.levels, h, fun _ _ => rfl⟩,
   fun ⟨_, ht, ha⟩ => familyHeaderRetypingRemaining_of_aligned ht ha⟩

/-! ## (5) the constructor obligation -/

/-- ConstructorScope content is admission's own supply: `constructorScopeTyped`
    (`hTc`) already types the whole stored type in `S`, and the stored type is
    the `policyPi` tower over `parameters ++ fields`, so inversion reads every
    domain in `S` at SOME labels. -/
theorem exists_telTypedT_constructorScope {S A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} {u : Level}
    (hTc : Nonempty (HasTyT S member.arity [] member.mtype (.sort u))) :
    ∃ ls : Fin (c.parameters ++ c.fields).length → Level,
      TelTypedT S family.member.arity (c.parameters ++ c.fields) ls := by
  rw [c.storedType] at hTc
  obtain ⟨ls, htel⟩ := exists_telTypedT_of_policyPi hTc
  exact ⟨ls, c.arity ▸ htel⟩

/-- the same content read off an actual admission receipt: `hTc` is
    `constructorScopeTyped` at the constructor's own chain cell. -/
theorem exists_telTypedT_constructorScope_of_admission {S A : ResolvedEnv}
    {r : Nat} {member : CheckedMember} {family : PolicyFamilyView A}
    {c : PolicyConstructorView A family member}
    (a : ScopeMemberAdmissionT S A r member)
    (hcls : member.mclass = .constructorM) :
    ∃ ls : Fin (c.parameters ++ c.fields).length → Level,
      TelTypedT S family.member.arity (c.parameters ++ c.fields) ls :=
  exists_telTypedT_constructorScope (a.constructorScopeTyped hcls)

/-- `ConstructorRecordedRetypingRemaining` under label alignment. -/
theorem constructorRecordedRetypingRemaining_of_aligned {S A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member}
    {ls : Fin (c.parameters ++ c.fields).length → Level}
    (htel : TelTypedT S family.member.arity (c.parameters ++ c.fields) ls)
    (halign : ∀ i, eqN (ls i) (c.domainsTyped.levels i)) :
    ConstructorRecordedRetypingRemaining S c :=
  telTypedT_of_eqN htel halign

/-- `ConstructorRecordedRetypingRemaining` under clean transport: if the
    admission prefix `A` agrees with `S` below `k`, `cleanHasTyT k`
    derivations of the recorded typings strengthen to `S`, keeping the
    recorded labels exactly.  At a real group `k = f + 1` and the agreement
    is `envAgreeBelow_groupEnvT_ctorScope` /
    `envAgreeBelow_extendEnv_foldl`. -/
theorem constructorRecordedRetypingRemaining_of_clean {S A : ResolvedEnv}
    {k : Nat} {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member}
    (hagree : EnvAgreeBelow A S k)
    (hclean : CleanTelDataT A family.member.arity k
      (c.parameters ++ c.fields) c.domainsTyped.levels)
    (hctx : ∀ i : Fin (c.parameters ++ c.fields).length,
      ctxConstsBelow k (policyPrefixContext (c.parameters ++ c.fields) i.val)
        = true) :
    ConstructorRecordedRetypingRemaining S c :=
  telTypedT_of_agreeBelow hagree hclean hctx

/-- `ConstructorRecordedRetypingRemaining` from the admission-supplied typed
    telescope: `IndGroupTypedT` on a constructor cell gives `CtorTypedT c`,
    whose first component is the recorded-labels `HasTyT` derivations in the
    admission prefix `A`.  If every derivation of those typings is clean
    below `k`, they strengthen to `S` verbatim, labels included.  At a real
    group `k = f + 1` and the agreement is
    `envAgreeBelow_groupEnvT_ctorScope`. -/
theorem constructorRecordedRetypingRemaining_of_ctorTypedT {S A : ResolvedEnv}
    {k : Nat} {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member}
    (hagree : EnvAgreeBelow A S k)
    (hT : CtorTypedT c)
    (hclean : ∀ i : Fin (c.parameters ++ c.fields).length,
      ∀ d : HasTyT A family.member.arity
        (policyPrefixContext (c.parameters ++ c.fields) i.val)
        (c.parameters ++ c.fields)[i.val] (.sort (c.domainsTyped.levels i)),
      cleanHasTyT k d)
    (hctx : ∀ i : Fin (c.parameters ++ c.fields).length,
      ctxConstsBelow k (policyPrefixContext (c.parameters ++ c.fields) i.val)
        = true) :
    ConstructorRecordedRetypingRemaining S c :=
  fun i => (hT.1 i).elim fun d =>
    hasTyT_strengthenC hagree d (hclean i d) (hctx i)

/-- the obligation, restated: it is exactly a ConstructorScope telescope at
    some labels, `eqN`-aligned with the recorded labels. -/
theorem constructorRecordedRetypingRemaining_iff {S A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} :
    ConstructorRecordedRetypingRemaining S c ↔
      ∃ ls : Fin (c.parameters ++ c.fields).length → Level,
        TelTypedT S family.member.arity (c.parameters ++ c.fields) ls ∧
          ∀ i, eqN (ls i) (c.domainsTyped.levels i) :=
  ⟨fun h => ⟨c.domainsTyped.levels, h, fun _ _ => rfl⟩,
   fun ⟨_, ht, ha⟩ => constructorRecordedRetypingRemaining_of_aligned ht ha⟩

/-! ## (6) syntactic support, reusing the landed extracts -/

/-- every domain of a `policyPi`-stored family type is supported in the base:
    `hasTyT_constsIn` of the HeaderScope whole-type typing plus
    `constsIn_policyPi_domain`. -/
theorem familyHeaderDomain_constsIn {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)} {u : Level}
    (hT : Nonempty (HasTyT E v.member.arity [] v.member.mtype (.sort u))) :
    ∀ D ∈ v.parameters ++ v.indices, ConstsIn E D := by
  obtain ⟨d⟩ := hT
  have hs := hasTyT_constsIn d
  rw [v.storedType] at hs
  exact constsIn_policyPi_domain (v.parameters ++ v.indices) _ hs

/-- the same support read across the self extension: a whole-type typing in
    `extendEnv E f fm` plus `f`-free domains drops to `E` by
    `constsIn_drop_extension`. -/
theorem familyHeaderDomain_constsIn_of_extension {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {v : PolicyFamilyView (extendEnv E f fm)} {u : Level}
    (hText : Nonempty (HasTyT (extendEnv E f fm) v.member.arity []
      v.member.mtype (.sort u)))
    (hf : ∀ D ∈ v.parameters ++ v.indices, occursConst f D = false) :
    ∀ D ∈ v.parameters ++ v.indices, ConstsIn E D := by
  obtain ⟨d⟩ := hText
  have hs := hasTyT_constsIn d
  rw [v.storedType] at hs
  exact fun D hD => constsIn_drop_extension D
    (constsIn_policyPi_domain (v.parameters ++ v.indices) _ hs D hD) (hf D hD)

/-- every domain (parameter or field) of a `policyPi`-stored constructor type
    is supported in ConstructorScope, extending
    `constructor_scope_raw_field_constsIn` to the parameter segment. -/
theorem constructorScope_domain_constsIn {S A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} {u : Level}
    (hT : HasTyT S member.arity [] member.mtype (.sort u)) :
    ∀ D ∈ c.parameters ++ c.fields, ConstsIn S D := by
  have hs := hasTyT_constsIn hT
  rw [c.storedType] at hs
  exact constsIn_policyPi_domain (c.parameters ++ c.fields) _ hs

end Rcic.Declarative

#print axioms Rcic.Declarative.exists_telTypedT_of_policyPi
#print axioms Rcic.Declarative.telTypedT_of_eqN
#print axioms Rcic.Declarative.envAgreeBelow_extendEnv_self
#print axioms Rcic.Declarative.envAgreeBelow_extendEnv_foldl
#print axioms Rcic.Declarative.envAgreeBelow_groupEnvT_ctorScope
#print axioms Rcic.Declarative.CleanTelDataT
#print axioms Rcic.Declarative.telTypedT_of_agreeBelow
#print axioms Rcic.Declarative.exists_telTypedT_headerScope
#print axioms Rcic.Declarative.exists_telTypedT_headerScope_of_admission
#print axioms Rcic.Declarative.familyHeaderRetypingRemaining_of_aligned
#print axioms Rcic.Declarative.familyHeaderRetypingRemaining_of_clean
#print axioms Rcic.Declarative.familyHeaderRetypingRemaining_of_familyTypedT
#print axioms Rcic.Declarative.familyHeaderRetypingRemaining_iff
#print axioms Rcic.Declarative.exists_telTypedT_constructorScope
#print axioms Rcic.Declarative.exists_telTypedT_constructorScope_of_admission
#print axioms Rcic.Declarative.constructorRecordedRetypingRemaining_of_aligned
#print axioms Rcic.Declarative.constructorRecordedRetypingRemaining_of_clean
#print axioms Rcic.Declarative.constructorRecordedRetypingRemaining_of_ctorTypedT
#print axioms Rcic.Declarative.constructorRecordedRetypingRemaining_iff
#print axioms Rcic.Declarative.familyHeaderDomain_constsIn
#print axioms Rcic.Declarative.familyHeaderDomain_constsIn_of_extension
#print axioms Rcic.Declarative.constructorScope_domain_constsIn
