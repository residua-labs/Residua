import rcic.RcicF3EvalPlanNormalSlice
import rcic.RcicF3CandidateBoundFields

/-!
# Guarded normalized tuples back to the original typed constructor fields

The same ordinary values pass through the two telescopes. Recursive field
transport uses the local slice predicate at actual semantic leaves. The
original Prop BoundG clause then supplies reverse normalization at each
already constructed target prefix. No reverse-normalization callback or
global inclusion of the guarded restriction is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormal
open Rcic.Declarative PiValueRule RawFamily

theorem specs_length {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs) :
    (specs p).length = Fs.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The actual retained field at a given ordinary position, together with
its exact original scope and normalized expression. -/
theorem field_at {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs) :
    ∀ k (hk : k < Fs.length),
      ∃ (prior' : Nat) (s : FieldShape)
        (q : EvalPlan.Field E fuel f nu np ni prior' (Fs[k]'hk) s),
        prior' = prior + k ∧
        ((specs p).map (fieldExpr f (canonL nu)))[k]? =
          some (fieldExpr f (canonL nu) (fieldSpec q)) := by
  induction p with
  | nil => intro k hk; exact (Nat.not_lt_zero k hk).elim
  | @cons prior s A ss Fs head tail ih =>
      intro k hk
      cases k with
      | zero =>
          refine ⟨prior, s, head, rfl, ?_⟩
          simp only [specs, List.map_cons, List.getElem?_cons_zero]
      | succ k =>
          obtain ⟨prior', s', q, hp, hq⟩ := ih k (Nat.lt_of_succ_lt_succ hk)
          refine ⟨prior', s', q, hp.trans (Nat.add_right_comm prior 1 k), ?_⟩
          simpa only [specs, List.map_cons, List.getElem?_cons_succ] using hq

/-- Two different dependent field lists transport using only the prefix
already built in the target list. The input values are kept literally. -/
theorem tuple_transport (M₁ M₂ : Interp.{4}) (σ : Nat → Nat) :
    ∀ (Fs Gs : List (Expr Nat)) (hlen : Gs.length = Fs.length),
      ∀ (ρ : Nat → PSet.{4}),
        (∀ k (hk : k < Fs.length) pre,
          TelFits M₂ σ (Fs.take k) ρ pre →
          Sub (Ed M₁ (den M₁ σ (push pre ρ)
            (Gs[k]'(by rw [hlen]; exact hk))))
            (Ed M₂ (den M₂ σ (push pre ρ) (Fs[k]'hk)))) →
        ∀ xs, TelFits M₁ σ Gs ρ xs → TelFits M₂ σ Fs ρ xs := by
  intro Fs
  induction Fs with
  | nil =>
      intro Gs hlen ρ _ xs hx
      have hg : Gs = [] := List.eq_nil_of_length_eq_zero hlen
      rw [hg] at hx
      cases xs <;> exact hx
  | cons A Fs ih =>
      intro Gs hlen ρ h xs hx
      cases Gs with
      | nil => cases hlen
      | cons B Gs =>
          have htail : Gs.length = Fs.length := Nat.succ.inj hlen
          cases xs with
          | nil => exact hx.elim
          | cons x xs =>
              have hhead := h 0 (Nat.succ_pos _) [] True.intro x hx.1
              refine ⟨hhead, ih Gs htail (vcons x ρ) ?_ xs hx.2⟩
              intro k hk pre hpre
              exact h (k + 1) (Nat.succ_lt_succ hk) (x :: pre) ⟨hhead, hpre⟩

/-- Actual bounded typing in the target candidate produces the entire
reverse tuple conversion. Only ordinary predecessor and prefix soundness
are inputs; the semantic normalization is derived internally. -/
theorem fields_to_raw_of_guarded (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (X D : Frame) (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hA : AllSound P (table P μ (famDataOf p.node.a) D) K p.E)
    (hI : ∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r)
    (hES : EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hsub : EvalPlanNormalSlice.GuardedSub p.node.a.family.member.arity
      p.node.a.family.parameters.length σ ps X D)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X))
      σ (fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs := by
  let R := X
  let MR := mkM P (table P μ (famDataOf p.node.a) R)
  let MD := mkM P (table P μ (famDataOf p.node.a) D)
  have hlen : (fields p j).length = (p.node.a.constructorViews j).fields.length := by
    exact (List.length_map _ _).trans (specs_length (p.constructors j).fields)
  apply tuple_transport MR MD σ (p.node.a.constructorViews j).fields (fields p j)
    hlen (push ps ρ0) ?_ xs hxs
  intro k hk pre hpre
  obtain ⟨prior, s, q, hprior, hq⟩ := field_at (p.constructors j).fields k hk
  have hkG : k < (fields p j).length := by rw [hlen]; exact hk
  have hget : (fields p j)[k]'hkG =
      fieldExpr p.node.a.family.ref (canonL p.node.a.family.member.arity)
        (fieldSpec q) :=
    Option.some.inj ((List.getElem?_eq_getElem hkG).symm.trans hq)
  have hpreLen : pre.length = prior := by
    have hl := hpre.length
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hl
    exact hl.trans (by simpa only [Nat.zero_add] using hprior.symm)
  rw [hget]
  cases q with
  | plain hfree =>
      have he := PiIndependent.den_free P μ (famDataOf p.node.a).fref
        (ofFrame P μ (famDataOf p.node.a) R) (ofFrame P μ (famDataOf p.node.a) D)
        σ ((p.node.a.constructorViews j).fields[k]) hfree (push pre (push ps ρ0))
      intro x hx
      change x ∈ Ed MD (den MR σ (push pre (push ps ρ0))
        ((p.node.a.constructorViews j).fields[k])) at hx
      change den MR σ (push pre (push ps ρ0))
          ((p.node.a.constructorViews j).fields[k]) =
        den MD σ (push pre (push ps ρ0))
          ((p.node.a.constructorViews j).fields[k]) at he
      rw [he] at hx
      exact hx
  | recursive r =>
      intro x hx
      have hxN := EvalPlanNormalSlice.recursive_sub_of_guarded P μ (famDataOf p.node.a)
        X D hX hD σ r ps pre hps.length hpreLen hsub x hx
      have hn := CandidateScope.original_field_normalized P
        (table P μ (famDataOf p.node.a) D) σ K hE hfam hctors hrec hmem hB
        p.node hA hI h0 hpolicy hES vs hσ hvs j ⟨k, hk⟩ ps pre hps hpre r.read
      exact mem_congr_right (ed_congr MD hn) hxN

/-- The comparison induction's restriction supplies the local relation
used by the general tuple bridge. All normalization remains produced from
the actual original BoundG clause in the target candidate. -/
theorem fields_to_raw (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (N D : Frame) (hN : Admissible (famDataOf p.node.a) N)
    (hD : Admissible (famDataOf p.node.a) D)
    (hA : AllSound P (table P μ (famDataOf p.node.a) D) K p.E)
    (hI : ∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r)
    (hES : EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits
      (mkM P (table P μ (famDataOf p.node.a)
        (restrict N (EvalPlanNormalSlice.Predicate p.node.a.family.member.arity
          p.node.a.family.parameters.length σ ps D))))
      σ (fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs := by
  apply fields_to_raw_of_guarded P μ σ K p fm ctors hE hfam hctors hrec hmem hB
    (restrict N (EvalPlanNormalSlice.Predicate p.node.a.family.member.arity
      p.node.a.family.parameters.length σ ps D)) D
    (restrict_admissible P (famDataOf p.node.a) N hN _) hD hA hI hES h0 hpolicy
    vs hσ hvs j ps xs hps ?_ hxs
  intro vs' i z hz hlevel hparam
  obtain ⟨a, hq, he⟩ := mem_sep.mp hz
  exact mem_congr_left he (hq hlevel hparam)

end Rcic.F3.PSet.EvalPlanNormal
