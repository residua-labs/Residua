import rcic.RcicF3CandidateFields
import rcic.RcicF3CandidateBoundFields
import rcic.RcicF3CandidateFieldAdmission

/-!
# Candidate-to-raw field tuples from actual admission and BoundG

The original field scan supplies clean normalized domains and full arguments.
The Prop clause of the existing group bound supplies instance bounds and
reverse normalization at each growing raw ordinary prefix. Pointwise field
inclusion therefore composes into inclusion of the complete field tuple.
No reverse-normalization callback or constructor-closure premise remains.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateBoundFields
open Rcic.Declarative RawFamily PiIndex

/-- The actual group extends the predecessor by fresh bodyless members.
Its family-only prefix therefore inherits the predecessor's bounded
transparent bodies. This fact is independent of the chosen candidate. -/
theorem family_prefix_bodiesOK (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundG K hE)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    BodiesOK (extendEnv E f fm) σ K := by
  have hfresh : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  apply bodiesOK_of_envWfT K hE hB
    (fun r m hm => members_extend_preserved hfresh r m hm) ?_ σ
  intro r m hm hn
  by_cases hr : r = f
  · subst r
    rw [members_extend_eq] at hm
    cases Option.some.inj hm
    exact hbody
  · rw [members_extend_ne E f fm r hr] at hm
    rw [hn] at hm
    cases hm

/-- Every original field's constant instances satisfy the existing bound at
the full recursor universe vector. This is independent of inserted IHs. -/
theorem original_fields_instOK (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (h0 : evalTotal σ node.a.family.resultLevel = 0)
    (hpolicy : node.a.policy = .anySort)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length) :
    ∀ A ∈ (node.a.constructorViews j).fields, InstOK (extendEnv E f fm) σ K A := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨l, _hl, d, hd⟩ :=
    hB.2.2.2 node (selection_prop node.a σ h0 hpolicy).1 hpolicy j vs hvs ⟨k, hk⟩
  apply instOK_of_lokt σ 4 K d
  rw [hσ]
  exact hd

/-- The entire original constructor tuple passes from the candidate table to
the raw table. Typed reverse normalization is produced from BoundG at the
ordinary prefix already constructed by the induction. The same parameter,
field and dependent-index values are retained. -/
theorem field_tuple_raw (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (h0 : evalTotal σ node.a.family.resultLevel = 0)
    (hpolicy : node.a.policy = .anySort)
    (X R : Frame)
    (hX : Admissible (famDataOf node.a) X)
    (hR : Admissible (famDataOf node.a) R)
    (hsub : FrameSub X R)
    (hFamily : ∀ ls, Equiv (μ node.a.family.ref ls)
      (ofFrame P μ (famDataOf node.a) R ls))
    (hESR : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (hESC : EnvSound (mkM P (table P μ (famDataOf node.a) X)) σ K
      (extendEnv E f fm) node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length)
    (fuel : Nat) (ss : List FieldShape)
    (hshape : fieldShapesFuel node.E0 fuel node.a.family.ref node.a.family.member.arity
      node.a.family.parameters.length node.a.family.indices.length
      node.a.family.parameters.length (node.a.constructorViews j).fields = some ss)
    (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) σ node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf node.a) X)) σ
      (node.a.constructorViews j).fields (push ps ρ0) xs) :
    TelFits (mkM P μ) σ (node.a.constructorViews j).fields (push ps ρ0) xs := by
  have hcert := CandidateFieldAdmission.certificates_of_fields
    (node.a.constructorViews j).fields 0 ss (by simpa only [Nat.add_zero] using hshape)
  have hInst := original_fields_instOK σ K hE hfam hctors hrec hmem hB node
    h0 hpolicy vs hσ hvs j
  have hb := family_prefix_bodiesOK σ K hE hB.1 hmem
  apply CandidateFields.telFits_mono_prefix
    (mkM P (table P μ (famDataOf node.a) X)) (mkM P μ) σ
    (node.a.constructorViews j).fields (push ps ρ0) ?_ xs hxs
  intro k hk pre hpre
  obtain ⟨s, hClean⟩ := CandidateFieldAdmission.clean_at
    (node.a.constructorViews j).fields ss 0 hcert ⟨k, hk⟩
  apply CandidateFields.original_field_sub P μ (famDataOf node.a) X R hX hR hsub
    hFamily σ K (CandidateScope.recNode_transparentBody_prefix hmem node)
    hESC hb ((node.a.constructorViews j).fields[k]) s hClean
    (hInst _ (List.getElem_mem hk)) (push pre (push ps ρ0))
  intro ds b hw
  exact CandidateScope.original_field_normalized P μ σ K
    hE hfam hctors hrec hmem hB node hA hI h0 hpolicy hESR vs hσ hvs
    j ⟨k, hk⟩ ps pre hps hpre hw

end Rcic.F3.PSet.CandidateBoundFields
