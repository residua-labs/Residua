import rcic.RcicTypedRowsWf
import rcic.RcicAnnIotaSR
import rcic.RcicAnnEnvBridge

/-!
# M3-b GLM-1 — the supplier: `AnnEnvA` gives `TypedRowsWf`

The chain adapter and the three fields, from the existing proofs only (annotation,
coherence `annCohA` / `annTyA`, sort and type uniqueness, the fixed-type rows
`sortConvCharT'` / `piConvInjT'` / `famAppConvInjT_any'`, erasure, `iotaSRA`).

The chain adapter `convT_of_tyConvT_sort`: with the LEFT end typed at a sort, every
`TyConvT` chain to any right end collapses to ONE `ConvT` at that sort.

* `refl`: the conversion is `refl` at the given typing — a refl chain invents no
  typing of its own; the premise supplies it.
* `of`: the step is at its own sort `v`. The step is annotated, the left end's typing
  is annotated, and `annTyA` (annotation coherence: two well-typed annotations of one
  erasure have convertible TYPES) converts between the two annotations of the left end
  and hence between the two type annotations; `convA_of_tyConvA` retypes the step;
  erasure returns a `ConvT` at the premise's sort. No `ConvT`/`TyConvT` definitional
  equality is assumed anywhere.
* `trans`: the first half collapses at the sort; its right end's typing at the same
  sort is read through the copy (`convA_hasTy_right` + erasure), and the second half
  collapses against it.

Row 3's family shape: an inductive member of an `EnvWfA`-admitted environment has a
sort-bodied stored type — read off the group admission's `FamViewA.stored` telescope
(`envWfA_famArity` below). The interface carries no shape premise; the supplier
recovers it from the admission, per the GLM-1 boundary.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

variable {E : ResolvedEnvA} {n : Nat}

/-! ## (1) the chain adapter -/

section Adapter

/-- The typing the adapter needs: a `ConvT` at a sort gives its left end's typing at
    that sort, through the copy's own left-typing rule. -/
theorem hasTyT_sort_of_convT (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ)
    {a b : Expr Nat} {u : Level} (h : ConvT (eraseEnv E) n Γ a b (.sort u)) :
    Nonempty (HasTyT (eraseEnv E) n Γ a (.sort u)) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvT' C hn h hΓA hctx
  obtain ⟨hW⟩ := C.wf
  have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨t'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) tA
  rw [ha, hT, hctx] at t'
  exact ⟨t'⟩

/-- The typing the adapter needs for `trans`: the right end at the same sort. -/
theorem hasTyT_sortRight_of_convT (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ)
    {a b : Expr Nat} {u : Level} (h : ConvT (eraseEnv E) n Γ a b (.sort u)) :
    Nonempty (HasTyT (eraseEnv E) n Γ b (.sort u)) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨c⟩⟩ := annConvT' C hn h hΓA hctx
  obtain ⟨hW⟩ := C.wf
  have tB := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓA c
  obtain ⟨t'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) tB
  rw [hb, hT, hctx] at t'
  exact ⟨t'⟩

/-- THE CHAIN ADAPTER: with the left end typed at a sort, a `TyConvT` chain to any
    right end is one `ConvT` at that sort. -/
theorem convT_of_tyConvT_sort (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ)
    {a b : Expr Nat} {u : Level} (hA : HasTyT (eraseEnv E) n Γ a (.sort u))
    (h : TyConvT (eraseEnv E) n Γ a b) :
    Nonempty (ConvT (eraseEnv E) n Γ a b (.sort u)) := by
  induction h with
  | refl => exact ⟨ConvT.refl _ _ _ hA⟩
  | of _ _ u h =>
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
      obtain ⟨aA, bA, TA, ha, hb, hTv, ⟨c⟩⟩ := annConvT' C hn h hΓA hctx
      obtain ⟨aA2, TA2, ha2, hTu, ⟨t2⟩⟩ := annHasTyT' C hn hA hΓA hctx
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c
      obtain ⟨t⟩ := annTyA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
        (ha.trans ha2.symm) tA t2
      obtain ⟨hW⟩ := C.wf
      obtain ⟨hc⟩ := convT_of_convA hW (C.hNS hn) (convA_of_tyConvA c t)
      rw [ha, hb, hTu, hctx] at hc
      exact ⟨hc⟩
  | trans _ _ _ h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1 hA
      obtain ⟨hmid⟩ := hasTyT_sortRight_of_convT C hn hΓ c1
      obtain ⟨c2⟩ := ih2 hmid
      exact ⟨ConvT.trans _ _ _ _ _ c1 c2⟩

end Adapter

/-! ## (2) row 3's family shape, recovered from the admission -/

/-- The body of a telescope built by `piTelA` over any domains, ending at a sort, is
    that sort. -/
theorem piBodyA_piTelA_sort : (ds : List (ExprA × Level)) → (s : Level) → (w : Level) →
    piBodyA (piTelA ds (.sort s) w).1 = .sort s
  | [], _, _ => rfl
  | (_, _) :: ds, s, w => piBodyA_piTelA_sort ds s w

/-- an inductive member of an `EnvWfA`-admitted environment has a sort-bodied stored
    type: the group admission's family view stores the type as a telescope ending at
    the view's sort. -/
theorem envWfA_famArity {I : IotaIfaceA} : {EA : ResolvedEnvA} → EnvWfA I EA →
    ∀ (r : Nat) (m : CheckedMemberA), EA.members r = some m → m.mclass = .inductiveM →
      ∃ u₀, piBodyA m.mtypeA = .sort u₀
  | _, .empty, r, _, hm, hind => by unfold emptyEnvA at hm; exact Option.noConfusion hm
  | _, .axiomM EA r' m' u hE hfresh hA hcl hlvl, r, m, hm, hind => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm
        cases hm
        simp at hind
      · rw [members_extendEnvA_ne EA r' _ (fun h => hr h.symm.symm)] at hm
        exact envWfA_famArity hE r m hm hind
  | _, .definitionM EA r' m' v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, hm, hind => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm
        cases hm
        simp at hind
      · rw [members_extendEnvA_ne EA r' _ (fun h => hr h.symm.symm)] at hm
        exact envWfA_famArity hE r m hm hind
  | _, .theoremM EA r' m' p hE hfresh hA hp hclA hclp hlvlA hlvlp, r, m, hm, hind => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm
        cases hm
        simp at hind
      · rw [members_extendEnvA_ne EA r' _ (fun h => hr h.symm.symm)] at hm
        exact envWfA_famArity hE r m hm hind
  | _, .opaqueM EA r' m' v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, hm, hind => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm
        cases hm
        simp at hind
      · rw [members_extendEnvA_ne EA r' _ (fun h => hr h.symm.symm)] at hm
        exact envWfA_famArity hE r m hm hind
  | _, .group EA f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh, r, m, hm, hind => by
      rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hc | hb
      · exact ⟨fv.sort, by rw [fv.stored]; exact piBodyA_piTelA_sort _ _ _⟩
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hmem : c.member = m := congrArg Prod.snd hce
        subst hmem
        rw [c.hcls] at hind; exact MemberClass.constructorM.noConfusion hind
      · exact envWfA_famArity hE r m hb hind
  | _, .groupRec EA f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh hlayout rec hrfresh, r, m, hm, hind => by
      simp only [groupRecEnvA] at hm
      by_cases hr : r = f + 1 + cs.length
      · subst hr; rw [members_extendEnvA_self] at hm
        cases hm
        rw [rec.hcls] at hind; exact MemberClass.recursorM.noConfusion hind
      · rw [members_extendEnvA_ne _ _ _ (fun h => hr h.symm.symm)] at hm
        rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hc | hb
        · exact ⟨fv.sort, by rw [fv.stored]; exact piBodyA_piTelA_sort _ _ _⟩
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hmem : c.member = m := congrArg Prod.snd hce
          subst hmem
          rw [c.hcls] at hind; exact MemberClass.constructorM.noConfusion hind
        · exact envWfA_famArity hE r m hb hind

/-- erasure inverted at a member: a member of the erased environment lifts to a member
    of the annotation erasing to it. -/
theorem memberA_of_eraseEnv {EA : ResolvedEnvA} {r : Nat} {m : CheckedMember}
    (hm : (eraseEnv EA).members r = some m) :
    ∃ mA, EA.members r = some mA ∧ eraseMember mA = m := by
  simp only [eraseEnv] at hm
  cases hE : EA.members r with
  | none => rw [hE] at hm; exact Option.noConfusion hm
  | some mA => rw [hE] at hm; exact ⟨mA, rfl, Option.some.inj hm⟩

/-! ## (3) the supplier -/

/-- THE SUPPLIER: every environment the copy admits bears the three chain rows on the
    typed judgment. No `RowsT`, `EnvSemA`, `IotaSRA`, `NoParamsA` or positive evidence
    is asked of the caller. -/
theorem typedRowsWf_of_annEnvA (C : AnnEnvA E) (hn : EnvNormEraseA E) (n : Nat) : TypedRowsWf (eraseEnv E) n where
  sortRow := fun {_} hΓ {_ _} h => by
    obtain ⟨c⟩ := convT_of_tyConvT_sort C hn hΓ (HasTyT.sort _ _) h
    exact sortConvCharT' C hn hΓ c
  piRow := fun {_} hΓ {_ _ _ _} h => by
    rcases TyConvT.firstOf h with he | ⟨X, u, ⟨hstep⟩, _⟩
    · -- a pure-refl chain: the two Π's are one, injectivity gives both halves
      rcases Expr.pi.inj he with ⟨rfl, rfl⟩
      exact ⟨⟨TyConvT.refl _ _⟩, ⟨TyConvT.refl _ _⟩⟩
    · -- a real step: the left Π is typed at the step's sort, the chain collapses
      obtain ⟨hty⟩ := hasTyT_sort_of_convT C hn hΓ hstep
      obtain ⟨c⟩ := convT_of_tyConvT_sort C hn hΓ hty h
      exact piConvInjT' C hn hΓ c
  famAppRow := fun {_} hΓ {r m ls ls' xs xs' w} hm hind hty h => by
      obtain ⟨mA, hmA, hmE⟩ := memberA_of_eraseEnv hm
      have hindA : mA.mclass = .inductiveM := by
        have hcl : mA.mclass = m.mclass := congrArg CheckedMember.mclass hmE
        exact hcl.trans hind
      obtain ⟨hW⟩ := C.wf
      obtain ⟨u₀, hsh⟩ := envWfA_famArity hW r mA hmA hindA
      obtain ⟨c⟩ := convT_of_tyConvT_sort C hn hΓ hty h
      obtain ⟨hl, hlen, hargs⟩ := famAppConvInjT_any' C hn hΓ hmA hindA hsh c
      have htyE : erase mA.mtypeA = m.mtype := by
        have := congrArg CheckedMember.mtype hmE
        simp only [eraseMember] at this
        exact this
      rw [htyE] at hargs
      exact ⟨hl, hlen, hargs⟩

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.hasTyT_sort_of_convT
#print axioms Rcic.Declarative.Ann.hasTyT_sortRight_of_convT
#print axioms Rcic.Declarative.Ann.convT_of_tyConvT_sort
#print axioms Rcic.Declarative.Ann.piBodyA_piTelA_sort
#print axioms Rcic.Declarative.Ann.envWfA_famArity
#print axioms Rcic.Declarative.Ann.memberA_of_eraseEnv
#print axioms Rcic.Declarative.Ann.typedRowsWf_of_annEnvA
