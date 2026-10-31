import rcic.RcicAnnEnvBridge
import rcic.RcicTypedGroup
import rcic.RcicAnnRecSem
import rcic.RcicAnnLRFundBind
import rcic.RcicAnnViewTy

/-!
# M3-e-2 — the environment bridge at an inductive group

`RcicAnnEnvBridge` bridges every `EnvWfT` environment without inductive groups. This module adds the
group step (`EnvWfT.group` → `EnvWfA.groupRec`).

`EnvWfT.group` is R-CIC's group admission: L-K1's checks and their typed content, for every group 05
admits. The copy's group step models fewer groups. The bridge's premise names which: a group is IN THE
COPY'S SCOPE when its members are given by structured views typed in 05 §4's scopes (`RcicTypedGroup`)
and it meets the copy's two profiles (`GroupInScopeT`, `EnvWfT.InScope`). The premise is never part of
`EnvWfT`.

(0) The premise, and what L-K1's checks give the bridge: freshness and the environment a group ends in.
(1)–(9) The copy's builders erase to `main`'s; the views' typed content annotates; levels close; the
    copy's group is built from the views.
(10) Arc D's contract: `CtorTyOfViewA` and `RecTyOfViewsA` stay hypotheses. `CtorTyOfViewSemA` and
    `RecTyOfViewsSemA` add the base's semantics at its own ι. They are not the original contract.
(11)–(12) The profiles along an extension; the group step, and the same step at the semantic prefix
    (`bridge_groupSem`), supplied from the strict prefix only.
(13) The bridge (`envBridge`), its semantic-prefix copy (`envBridgeSem`), and the three rows.
-/

namespace Rcic.Declarative

/-! ## (0) the copy's scope at a group: the bridge's premise -/

/-- O1-b-2: a UNIT GROUP read on the typed views — one constructor, without fields, and no index. Its
    recursor is the copy's unit group's (`unitGroupA_of_recTypeA`), where the head step reads no major. -/
def UnitGroupT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (cs : List (GroupCtorT E f fm fv)) : Prop :=
  cs.length = 1 ∧ fv.indices = [] ∧ ∀ c ∈ cs, c.view.fields = []

/-- W-1 (e-3): a STRUCT GROUP read on the typed views — one constructor, no index, and at least one
    field, every field plain with a recorded sort zero at every valuation: every field is a proof. Its
    recursor at a motive of any sort is the copy's struct group's (`structGroupA_of_keeps`), where the
    head step reads no major. -/
def StructGroupT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (cs : List (GroupCtorT E f fm fv)) : Prop :=
  cs.length = 1 ∧ fv.indices = [] ∧
    ∀ c ∈ cs, c.view.fields ≠ [] ∧ ∀ F ∈ c.view.fields, ∃ D u, F = .plain D u ∧ UniformProp u

/-- the copy's two named profiles, read on one group's views:
    - (O2) every index's recorded sort is at most the family's sort wherever that sort is positive
      (`SmallIndexProfileA`);
    - (O1) a `Prop` family with a constructor eliminates into `Prop` only (`PropElimStructA`). A `Prop`
      family without constructors (`False`) may eliminate into any sort (O1-a), and so may a unit group
      (`True`, O1-b-2: `UnitGroupT`) and a struct group (`S`, `And`, W-1 (e-3): `StructGroupT`). -/
def GroupProfileT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    {cs : List (GroupCtorT E f fm fv)} (rec : GroupRecT E f fm fv cs) : Prop :=
  (∀ v ∈ fv.indices.map Prod.snd, ∀ (ρ : Nat → Option Nat) (x y : Nat),
    eval ρ v = some x → eval ρ fv.sort = some y → 0 < y → x ≤ y) ∧
  (UniformProp fv.sort → cs ≠ [] → ¬ UnitGroupT cs → ¬ StructGroupT cs → rec.elim = .propOnly)

/-- the environment after a group with its recursor: the group's, then the recursor at `f + 1 + k`
    (05 §3: member `k + 1` of the group). -/
def groupRecEnvT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (cs : List (GroupCtorT E f fm fv)) (rec : GroupRecT E f fm fv cs) : ResolvedEnv :=
  extendEnv (groupEnvT E f fm (cs.map GroupCtorT.entry)) (f + 1 + cs.length) rec.member

/-- ONE GROUP IN THE COPY'S SCOPE: the group's members given by structured views typed in 05 §4's
    scopes, and the two profiles. A premise of the bridge, never part of `EnvWfT`.

    The views have two field kinds: plain (family-free, typed in the plain context in the base) and
    directly recursive (written `F (params ++ idx)`). So the scope leaves out, by construction, two
    kinds of group that 05 admits:
    - function-recursive fields (05 §8, §12; R-NoFunRec);
    - a recursive field reached only by reduction (05 §8 "T reduces to"; R-NoDeltaRec).

    Each view types its constructor with the family alone present (05 §4 ConstructorScope), and since
    M3-e-3 so does `EnvWfT`: every constant of an admitted constructor's stored type is a member of that
    scope (`hasTyT_constsIn`), so none is an earlier constructor. -/
structure GroupInScopeT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) : Type where
  fv : FamViewT fm
  htel : TelTyT E fm.arity [] (fv.params ++ fv.indices)
  cs : List (GroupCtorT E f fm fv)
  hctors : (cs.map GroupCtorT.entry).reverse = ctors
  hlayout : cs.reverse.map GroupCtorT.ref = List.range' (f + 1) cs.length
  grec : GroupRecT E f fm fv cs
  hrr : rr = f + 1 + cs.length
  hrm : grec.member = rm
  hprof : GroupProfileT grec
  /-- the family's telescope binder levels are within its arity — `instLevel`-closing is the
      identity on them, so the instantiated copy's stored type still erases to the family's
      (`instDomsA_map_eraseDom`; R-NoDeltaRec-4d-iii). `HasTyT.sort` carries no such premise and the
      erased telescope (`policyPi`) no binder level, so the scope carries it: a NAMED scope narrowing
      against `main`'s `GroupInScopeT`. The scope test certifies it (`famCheckB_levels`). -/
  hpb : ∀ d ∈ fv.params ++ fv.indices, levelBounded fm.arity d.2 = true
  /-- the group's constructors carry no δ-reached field. The annotation layer itself is
      `.drecD`-total (`annFieldsTyT` annotates a δ-reached field from `DrecDTypedT`), but the
      erased↔annotated lift (`annHasTyT` and the ι-correspondence built on it) needs
      `EnvNormEraseA` — normalized and stored constructor types erasing equally — which a
      `.drecD` member provably breaks (`drCtorMemberA_diverge`). This is not a by-design
      exclusion: `00_MASTER_CLOSURE_SPEC.md` Erratum E-RowsInScope (5)(b) records R-NoDeltaRec as
      open, and `hsnd` keeps `.drecD` groups off the typed in-scope path exactly as on `main`.
      `hsnd` is that gate: it admits every group whose fields are
      plain or genuinely `.drec`/`.frec`, and keeps `.drecD`-carrying groups out of the bridge
      scope. Direct (non-`envBridge`) construction on a `EnvNormEraseA`-clean base still annotates
      `.drecD` groups — their fields flow through `CtorCopyA.drecD_typed`, not this gate. -/
  hsnd : ∀ c ∈ cs, ∀ d ∈ c.view.fields, d.isDrecD = false

/-- every group of a derivation is in the copy's scope. -/
def EnvWfT.InScope : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => hE.InScope
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScope
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScope
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScope
  | _, .group E f fm ctors rr rm _ hE _ _ _ _ =>
      hE.InScope ∧ Nonempty (GroupInScopeT E f fm ctors rr rm)

/-- L-K1's checks along the constructors (the list's head added last) give each one fresh in the group
    built before it, and the checks of what follows. -/
theorem groupMembersT_ctors {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (h0 : E.members f = none) :
    (l : List (Nat × CheckedMember)) → {rest : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT (extendEnv E f fm) (extendEnv E f fm) (l.reverse ++ rest) E' →
    GroupFreshT E f fm l ∧ Nonempty (GroupMembersT (extendEnv E f fm) (groupEnvT E f fm l) rest E')
  | [], _, _, h => ⟨h0, ⟨h⟩⟩
  | c :: l, rest, E', h => by
      rw [List.reverse_cons, List.append_assoc] at h
      obtain ⟨hl, ⟨h'⟩⟩ := groupMembersT_ctors h0 l h
      cases h' with
      | cons _ _ _ _ _ hfr _ _ _ _ _ _ _ _ _ _ _ _ hrest => exact ⟨⟨hl, hfr⟩, ⟨hrest⟩⟩

end Rcic.Declarative

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- `groupEnvT` only adds members: under `GroupFreshT` the base is a prefix (`EnvSub`),
    member by member. -/
theorem envSub_groupEnvT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} :
    {cs : List (Nat × CheckedMember)} → GroupFreshT E f fm cs →
    EnvSub E (groupEnvT E f fm cs)
  | [], h => envSub_extendEnv h
  | _ :: cs, h => envSub_trans (envSub_groupEnvT h.1) (envSub_extendEnv h.2)

/-- the family extension itself is a prefix of the whole group environment: the
    family member is the group's first member, the constructors' walk only adds
    fresh references on top. -/
theorem envSub_extend_groupEnvT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} :
    {cs : List (Nat × CheckedMember)} → GroupFreshT E f fm cs →
    EnvSub (extendEnv E f fm) (groupEnvT E f fm cs)
  | [], _ => envSub_refl _
  | _ :: cs, h => envSub_trans (envSub_extend_groupEnvT h.1) (envSub_extendEnv h.2)

/-- `groupRecEnvT` adds the recursor on top of the group environment: the base is a
    prefix of the whole group's environment. -/
theorem envSub_groupRecEnvT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cs : List (GroupCtorT E f fm fv)} {rec : GroupRecT E f fm fv cs}
    (hfresh : GroupFreshT E f fm (cs.map GroupCtorT.entry))
    (hrfresh : (groupEnvT E f fm (cs.map GroupCtorT.entry)).members (f + 1 + cs.length) = none) :
    EnvSub E (groupRecEnvT cs rec) :=
  envSub_trans (envSub_groupEnvT hfresh) (envSub_extendEnv hrfresh)

/-- the family-extension environment `extendEnv E f fm` is a prefix of the whole
    group's environment `groupRecEnvT`: the family's extension, then the
    constructors' walk, then the recursor. -/
theorem envSub_famExt_groupRecEnvT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cs : List (GroupCtorT E f fm fv)} {rec : GroupRecT E f fm fv cs}
    (hfresh : GroupFreshT E f fm (cs.map GroupCtorT.entry))
    (hrfresh : (groupEnvT E f fm (cs.map GroupCtorT.entry)).members (f + 1 + cs.length) = none) :
    EnvSub (extendEnv E f fm) (groupRecEnvT cs rec) :=
  envSub_trans (envSub_extend_groupEnvT hfresh) (envSub_extendEnv hrfresh)

/-- an annotation-side one-member extension has the base's erasure as a prefix of
    its own erasure (`eraseEnv_extend` + `envSub_extendEnv`). -/
theorem envSub_erase_extendEnvA {E : ResolvedEnvA} {f : Nat} {fmA : CheckedMemberA}
    (hfr : E.members f = none) : EnvSub (eraseEnv E) (eraseEnv (extendEnvA E f fmA)) := by
  rw [eraseEnv_extend]
  exact envSub_extendEnv (by simp [members_eraseEnv, hfr])

/-- the correspondence at an environment the copy admits (`AnnEnvA`), from the
    certificates below it: `AnnEnvA.wf` is admission at `iotaIfaceA`, `AnnEnvA.noFun`
    the tree-restriction the erasure direction reads, and the certificates
    instantiate at the environment itself (`envSub_refl`).  This is the
    eliminator every `IotaCorrTA`-consumer goes through — the certificates are
    the premise, never a universal hypothesis. -/
theorem iotaCorrTA_of_annEnvA {EA : ResolvedEnvA} (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hC : CorrCertsBelow (eraseEnv EA)) : IotaCorrTA EA :=
  C.wf.elim fun hW =>
    iotaCorrTA_of_envWfA hW C.noFun hn (hC _ (envSub_refl _)).1 (hC _ (envSub_refl _)).2

/-- `IotaCorrTA` at an annotation env whose erasure is a prefix of a certified
    environment: restrict the certificates along the prefix, then
    `iotaCorrTA_of_annEnvA`.  The `.drecD` arm of `annFieldsTyT` needs exactly this
    transport — the arm's annotation runs at `extendEnvA E f fmA` while the
    caller's certificates quantify over the group's whole environment. -/
theorem iotaCorrTA_of_certs_prefix {EA : ResolvedEnvA} {E' : ResolvedEnv}
    (C : AnnEnvA EA) (hn : EnvNormEraseA EA) (hC : CorrCertsBelow E')
    (hsub : EnvSub (eraseEnv EA) E') : IotaCorrTA EA :=
  iotaCorrTA_of_annEnvA C hn (fun E₀ h => hC E₀ (envSub_trans h hsub))

/-! ## (1) erasure commutes with the builders -/

/-- a substitution's erasure. -/
def eraseSubst (σ : SubstA) : SubstT := fun i => erase (σ i)

theorem eraseSubst_up (σ : SubstA) : eraseSubst σ.up = (eraseSubst σ).up := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact erase_liftA (σ i) 0 1

theorem eraseSubst_shift1 (σ : SubstA) : eraseSubst σ.shift1 = (eraseSubst σ).shift1 := by
  funext i
  exact erase_liftA (σ i) 0 1

theorem eraseSubst_id : eraseSubst SubstA.id = SubstT.id := rfl

theorem erase_substA (σ : SubstA) (e : ExprA) :
    erase (substA σ e) = substT (eraseSubst σ) (erase e) := by
  induction e generalizing σ with
  | bvar i => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [substA, erase, substT, ihf, ihx]
  | lam a u b iha ihb => simp only [substA, erase, substT, iha, ihb, eraseSubst_up]
  | pi a u b v iha ihb => simp only [substA, erase, substT, iha, ihb, eraseSubst_up]
  | letE a w b iha ihw ihb => simp only [substA, erase, substT, iha, ihw, ihb, eraseSubst_up]
  | lit t => rfl

theorem erase_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) →
      erase (piTelA ds B w).1 = policyPi (ds.map fun d => erase d.1) (erase B)
  | [] => rfl
  | (D, u) :: ds => by
      simp only [piTelA, erase, List.map_cons, policyPi, erase_piTelA B w ds]

theorem erase_paramLocalsA : (n : Nat) → (paramLocalsA n).map erase = policyLocals n
  | 0 => rfl
  | n + 1 => by
      rw [paramLocalsA, List.map_cons, erase_paramLocalsA n]
      simp only [policyLocals, List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append, List.map_cons]
      rfl

/-- a field's erasure. `FieldT` has no function-recursive field until step 2; such a field erases to
    the directly recursive one at its indices, and the erasure laws below hold where no field is
    function-recursive (R-NoFunRec-1 step 1 (1c)). -/
def FieldA.erase : FieldA → FieldT
  | .plain D u => .plain (Ann.erase D) u
  | .drec idx | .frec _ _ _ idx => .drec (idx.map Ann.erase)
  | .drecD D idx => .drecD (Ann.erase D) (idx.map Ann.erase)

/-- a field whose erasure is not `drecD` is not δ-reached (R-NoDeltaRec-4d-ii). -/
theorem FieldA.noDelta_of_erase {x : FieldA} (h : x.erase.isDrecD = false) : x.NoDelta := by
  cases x <;> first | trivial | exact (Bool.noConfusion h).elim

/-- `norm` is invisible to the erasure inside its own scope (R-NoDeltaRec-3a/4a): a δ-reached
    field's erasure keeps its surface `drecD`, its norm's erasure the `drec` — different data,
    agreeing only after the copy reads the δ form (R-NoDeltaRec-4b rescopes this). -/
theorem FieldA.norm_erase (x : FieldA) (h : x.NoDelta) : x.norm.erase = x.erase := by
  rw [norm_self h]

/-- the erasure of a tree-shaped field is never δ-reached (R-NoDeltaRec-4a). -/
theorem FieldA.erase_noDrecD {x : FieldA} (h : x.TreeField) : x.erase.isDrecD = false := by
  cases x <;> first | rfl | exact h.elim

/-- `iotaGroupA` from its member hits and the middle-layer facts: the constructive half of
    `iotaGroupA_some` (R-NoDeltaRec-4d-ii). Every scrutinee rewrite is hypothesis-driven. -/
theorem iotaGroupA_of_mems {E : ResolvedEnvA} {recRef c : Nat}
    {recM ctorM famM : CheckedMemberA} {familyRef : Nat} {D : ExprA} {lsF : List Level}
    {np ni : Nat} (hrec : E.members recRef = some recM)
    (hctor : E.members c = some ctorM)
    (hcls : recM.mclass = .recursorM ∧ ctorM.mclass = .constructorM)
    (hD : (piDomsA recM.mtypeA).getLast? = some D)
    (hhead : (appsSpineA D).1 = .const familyRef lsF)
    (hfam : E.members familyRef = some famM)
    (hlay : famM.mclass = .inductiveM ∧ familyRef < c ∧ c < recRef)
    (hcnt : groupCountsA recM famM (recRef - familyRef - 1) = some (np, ni)) :
    iotaGroupA E recRef c = some ⟨recM, ctorM, famM, c, familyRef, np, ni,
      recRef - familyRef - 1, c - familyRef - 1⟩ := by
  simp only [iotaGroupA, hrec, hctor, if_pos hcls, hD, hhead, hfam, if_pos hlay, hcnt]

/-- `iotaGroupA`'s member lookups are all at refs the success proves are in `E`'s domain, so
    extending the environment at a fresh ref preserves a hit (R-NoDeltaRec-4d-ii). -/
theorem iotaGroupA_extend {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hfr : E.members r = none) {recRef c : Nat} {g : IotaGroupA}
    (h : iotaGroupA E recRef c = some g) : iotaGroupA (extendEnvA E r m) recRef c = some g := by
  unfold iotaGroupA at h
  split at h
  · rename_i recM ctorM hrec hctor
    split at h
    · rename_i hcls
      split at h
      · rename_i D hD
        split at h
        · rename_i familyRef lsF hhead
          split at h
          · rename_i famM hfam
            split at h
            · rename_i hlay
              split at h
              · rename_i np ni hcnt
                injection h with hg
                rw [← hg]
                refine iotaGroupA_of_mems ?_ ?_ hcls hD hhead ?_ hlay hcnt
                · rw [members_extendEnvA_ne E r m (fun hh => by
                      rw [← hh, hrec] at hfr; exact Option.noConfusion hfr)]
                  exact hrec
                · rw [members_extendEnvA_ne E r m (fun hh => by
                      rw [← hh, hctor] at hfr; exact Option.noConfusion hfr)]
                  exact hctor
                · rw [members_extendEnvA_ne E r m (fun hh => by
                      rw [← hh, hfam] at hfr; exact Option.noConfusion hfr)]
                  exact hfam
              · rename_i _ _; exact Option.noConfusion h
            · rename_i _; exact Option.noConfusion h
          · rename_i _; exact Option.noConfusion h
        · rename_i _; exact Option.noConfusion h
      · rename_i _; exact Option.noConfusion h
    · rename_i _; exact Option.noConfusion h
  · exact Option.noConfusion h

/-- `iotaFnA`-success extends to an environment extension at a fresh ref (R-NoDeltaRec-4d-ii):
    the redex's recursor/ctor/family lookups were `E`-hits, hence `extendEnvA`-hits. -/
theorem iotaFnA_extend {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hfr : E.members r = none) {e e' : ExprA} (h : iotaFnA E e = some e') :
    iotaFnA (extendEnvA E r m) e = some e' := by
  obtain ⟨s, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  simp only [iotaFnA, hs, Option.some_bind, hc, iotaGroupA_extend hfr hg, hr]

/-- `TyConvA` transports through an env extension + interface strengthening under the same
    pointwise premise (R-NoDeltaRec-4d-ii). -/
def tyConvA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {A B : ExprA} → TyConvA E I n Γ A B → TyConvA E' J n Γ A B
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      .of Γ A B l l' u (hasTyA_env_iface hpre hag hAl) hlu (hasTyA_env_iface hpre hag hBl)
        hl'u (convA_env_iface hpre hag h)
  | _, _, _, .trans Γ A B C h1 h2 =>
      .trans Γ A B C (tyConvA_env_iface hpre hag h1) (tyConvA_env_iface hpre hag h2)

/-- `ArgsTyA` transports (R-NoDeltaRec-4d-ii). -/
def argsTyA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {T : ExprA} → {as : List ExprA} → ArgsTyA E I n Γ T as →
      ArgsTyA E' J n Γ T as
  | _, _, _, .nil l => .nil l
  | _, _, _, .cons A u B v a as ha tl =>
      .cons A u B v a as (hasTyA_env_iface hpre hag ha) (argsTyA_env_iface hpre hag tl)

/-- `MirrorsConvA` transports (R-NoDeltaRec-4d-ii). -/
def mirrorsConvA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat}
    {I J : IotaIfaceA} (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {ms ps : List (ExprA × Level)} → MirrorsConvA E I n Γ ms ps →
      MirrorsConvA E' J n Γ ms ps
  | _, _, _, .nil Γ => .nil Γ
  | _, _, _, .cons Γ M um P up ms ps hc hl tl =>
      .cons Γ M um P up ms ps (tyConvA_env_iface hpre hag hc) hl
        (mirrorsConvA_env_iface hpre hag tl)

/-- `FieldsTyA` transports (R-NoDeltaRec-4d-ii). -/
def fieldsTyA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
      FieldsTyA E I n idxTel Γ k fs res → FieldsTyA E' J n idxTel Γ k fs res
  | _, _, _, _, .nil Γ k res hres => .nil Γ k res (argsTyA_env_iface hpre hag hres)
  | _, _, _, _, .plain Γ k D u fs res hD tl =>
      .plain Γ k D u fs res (hasTyA_env_iface hpre hag hD) (fieldsTyA_env_iface hpre hag tl)
  | _, _, _, _, .drec Γ k idx fs res hidx tl =>
      .drec Γ k idx fs res (argsTyA_env_iface hpre hag hidx) (fieldsTyA_env_iface hpre hag tl)
  | _, _, _, _, .frec Γ k B uB Bs idx fs res hdom tl =>
      .frec Γ k B uB Bs idx fs res (fieldsTyA_env_iface hpre hag hdom)
        (fieldsTyA_env_iface hpre hag tl)
  | _, _, _, _, .drecD Γ k D idx fs res hidx tl =>
      .drecD Γ k D idx fs res (argsTyA_env_iface hpre hag hidx) (fieldsTyA_env_iface hpre hag tl)

/-- `TelTyA` transports (R-NoDeltaRec-4d-ii). -/
def telTyA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds → TelTyA E' J n Γ ds
  | _, _, .nil Γ => .nil Γ
  | _, _, .cons Γ D u ds hD tl =>
      .cons Γ D u ds (hasTyA_env_iface hpre hag hD) (telTyA_env_iface hpre hag tl)

/-- `CtxWfA` transports (R-NoDeltaRec-4d-ii). -/
def ctxWfA_env_iface {E E' : ResolvedEnvA} (hpre : PrefixA E E') {n : Nat} {I J : IotaIfaceA}
    (hag : ∀ e, ConstsInA (domA E) e → I.fn e = J.fn e) :
    {Γ : LCtxA} → CtxWfA E I n Γ → CtxWfA E' J n Γ
  | _, .nil => .nil
  | _, .assumption hΓ hA => .assumption (ctxWfA_env_iface hpre hag hΓ) (hasTyA_env_iface hpre hag hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (ctxWfA_env_iface hpre hag hΓ) (hasTyA_env_iface hpre hag hA)
        (hasTyA_env_iface hpre hag hv)

/-- erasure commutes with context append. -/
theorem eraseCtx_append (Γ Γ' : LCtxA) :
    eraseCtx (Γ ++ Γ') = eraseCtx Γ ++ eraseCtx Γ' := by
  simp [eraseCtx]

/-- erasure distributes over the plain context of a field prefix (R-NoDeltaRec-4d-ii). -/
theorem eraseCtx_plainCtxA : (fs : List FieldA) → (Γ : LCtxA) →
    eraseCtx (plainCtxA fs Γ) = plainCtxT (fs.map FieldA.erase) (eraseCtx Γ)
  | [], _ => rfl
  | .plain D _u :: fs, Γ => eraseCtx_plainCtxA fs (.assumption D :: Γ)
  | .drec _ :: fs, Γ => eraseCtx_plainCtxA fs Γ
  | .frec _ _ _ _ :: fs, Γ => eraseCtx_plainCtxA fs Γ
  | .drecD _ _ :: fs, Γ => eraseCtx_plainCtxA fs Γ

theorem map_erase_liftA (c k : Nat) (xs : List ExprA) :
    (xs.map (liftA c k)).map erase = (xs.map erase).map (lift c k) := by
  simp only [List.map_map]
  exact List.map_congr_left (fun x _ => erase_liftA x c k)

theorem map_erase_substA (σ : SubstA) (xs : List ExprA) :
    (xs.map (substA σ)).map erase = (xs.map erase).map (substT (eraseSubst σ)) := by
  simp only [List.map_map]
  exact List.map_congr_left (fun x _ => erase_substA σ x)

theorem erase_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (∀ x ∈ fs, x.NoFun) → (pl : List ExprA) → (σ : SubstA) →
      erase (ctorFieldsA f ls w pl σ fs res).1 =
        ctorFieldsT f ls (pl.map erase) (eraseSubst σ) (fs.map FieldA.erase) (res.map erase)
  | [], _, pl, σ => by
      simp only [ctorFieldsA, List.map_nil, ctorFieldsT, erase_foldAppsA, erase, List.map_append,
        map_erase_substA]
  | .frec _ _ _ _ :: _, hnf, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .drecD D idx :: fs, hnf, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.erase, ctorFieldsT, erase, erase_substA,
        erase_ctorFieldsA f ls w res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)),
        map_erase_liftA, eraseSubst_shift1]
  | .plain D u :: fs, hnf, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.erase, ctorFieldsT, erase, erase_substA,
        erase_ctorFieldsA f ls w res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)), map_erase_liftA,
        eraseSubst_up]
  | .drec idx :: fs, hnf, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.erase, ctorFieldsT, erase, erase_foldAppsA,
        List.map_append, map_erase_substA,
        erase_ctorFieldsA f ls w res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)), map_erase_liftA,
        eraseSubst_shift1]

theorem erase_ctorTypeA (f : Nat) (ls : List Level) (w : Level) (mirrors : List (ExprA × Level))
    (fields : List FieldA) (res : List ExprA) (hnf : ∀ x ∈ fields, x.NoFun) :
    erase (ctorTypeA f ls w mirrors fields res) =
      ctorTypeT f ls (mirrors.map fun d => (erase d.1, d.2)) (fields.map FieldA.erase)
        (res.map erase) := by
  simp only [ctorTypeA, ctorTypeT, erase_piTelA, erase_ctorFieldsA f ls w res fields hnf, erase_paramLocalsA,
    eraseSubst_id, List.map_map, List.length_map]
  rfl

theorem erase_minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (fs : List FieldA) → (∀ x ∈ fs, x.NoFun) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) →
    (σ : SubstA) →
      erase (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 =
        minorFieldsT f c ls (pl.map erase) (erase mot) (fl.map erase) (eraseSubst σ)
          (fs.map FieldA.erase) (res.map erase)
  | [], _, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_nil, minorFieldsT, erase_foldAppsA, erase, List.map_append,
        map_erase_substA, List.map_cons]
  | .frec _ _ _ _ :: _, hnf, _, _, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .drecD D idx :: fs, hnf, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.erase, minorFieldsT, erase, erase_substA,
        erase_foldAppsA, List.map_append, map_erase_substA,
        erase_minorFieldsA f c ls wF wM res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)),
        map_erase_liftA, eraseSubst_shift1, erase_liftA, List.map_cons, List.map_nil]
  | .plain D u :: fs, hnf, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.erase, minorFieldsT, erase, erase_substA,
        erase_minorFieldsA f c ls wF wM res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)), map_erase_liftA,
        eraseSubst_up, erase_liftA, List.map_append, List.map_cons, List.map_nil]
  | .drec idx :: fs, hnf, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.erase, minorFieldsT, erase, erase_foldAppsA,
        List.map_append, map_erase_substA,
        erase_minorFieldsA f c ls wF wM res fs (fun x hx => hnf x (List.mem_cons_of_mem _ hx)), map_erase_liftA,
        eraseSubst_shift1, erase_liftA, List.map_cons, List.map_nil]

/-- a minor datum's erasure. -/
def MinorDataA.erase (cd : MinorDataA) : MinorDataT :=
  (cd.1, cd.2.1.map FieldA.erase, cd.2.2.map Ann.erase)

theorem erase_famLocalsA (f : Nat) (ls : List Level) (np ni : Nat) :
    erase (famLocalsA f ls np ni) = famLocalsT f ls np ni := by
  simp only [famLocalsA, famLocalsT, erase_foldAppsA, erase, List.map_append, map_erase_liftA,
    erase_paramLocalsA]

theorem erase_liftDomsA (a : Nat) : (c : Nat) → (ds : List (ExprA × Level)) →
    (liftDomsA c a ds).map (fun d => erase d.1) = liftDomsT c a (ds.map fun d => erase d.1)
  | _, [] => rfl
  | c, (D, u) :: ds => by
      simp only [liftDomsA, List.map_cons, liftDomsT, erase_liftA, erase_liftDomsA a (c + 1) ds]

theorem erase_motTyA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) :
    erase (motTyA f ls params indices wF wM).1 =
      motTyT f ls (params.map fun d => (erase d.1, d.2)) (indices.map fun d => (erase d.1, d.2)) wM := by
  simp only [motTyA, motTyT, erase_piTelA, erase, erase_famLocalsA, List.map_map, List.length_map]
  rfl

theorem erase_minorTyA (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) (cd : MinorDataA)
    (hnf : ∀ x ∈ cd.2.1, x.NoFun) :
    erase (minorTyA f ls wF wM np cd).1 = minorTyT f ls np cd.erase := by
  simp only [minorTyA, minorTyT, erase_minorFieldsA f cd.1 ls wF wM cd.2.2 cd.2.1 hnf, map_erase_liftA,
    erase_paramLocalsA, MinorDataA.erase, eraseSubst_shift1, eraseSubst_id]
  rfl

theorem erase_minorDomsA (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) :
    (j : Nat) → (cds : List MinorDataA) → (∀ cd ∈ cds, ∀ x ∈ cd.2.1, x.NoFun) →
      (minorDomsA f ls wF wM np j cds).map (fun d => erase d.1) =
        minorDomsT f ls np j (cds.map MinorDataA.erase)
  | _, [], _ => rfl
  | j, cd :: cds, hnf => by
      simp only [minorDomsA, List.map_cons, minorDomsT, erase_liftA,
        erase_minorTyA f ls wF wM np cd (hnf cd (List.mem_cons_self _ _)),
        erase_minorDomsA f ls wF wM np (j + 1) cds (fun cd' h => hnf cd' (List.mem_cons_of_mem _ h))]

theorem erase_recBodyA_T (ni k : Nat) : erase (recBodyA ni k) = recBodyT ni k := by
  simp only [recBodyA, recBodyT, erase_foldAppsA, erase, List.map_append, map_erase_liftA,
    erase_paramLocalsA, List.map_cons, List.map_nil]

theorem erase_recDomsA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) (hnf : ∀ cd ∈ cds, ∀ x ∈ cd.2.1, x.NoFun) :
    (recDomsA f ls params indices wF wM cds).map (fun d => erase d.1) =
      recDomsT f ls (params.map fun d => (erase d.1, d.2)) (indices.map fun d => (erase d.1, d.2)) wM
        (cds.map MinorDataA.erase) := by
  simp only [recDomsA, recDomsT, List.map_append, List.map_cons, List.map_nil, erase_motTyA,
    erase_minorDomsA f ls wF wM params.length 0 cds hnf, erase_liftDomsA, erase_liftA, erase_famLocalsA,
    List.map_map, List.length_map]
  rfl

theorem erase_recTypeA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) (hnf : ∀ cd ∈ cds, ∀ x ∈ cd.2.1, x.NoFun) :
    erase (recTypeA f ls params indices wF wM cds) =
      recTypeT f ls (params.map fun d => (erase d.1, d.2)) (indices.map fun d => (erase d.1, d.2)) wM
        (cds.map MinorDataA.erase) := by
  simp only [recTypeA, recTypeT, erase_piTelA, erase_recDomsA f ls params indices wF wM cds hnf,
    erase_recBodyA_T, List.length_map]

/-! ## (2) the views' typed content, annotated -/

/-- a domain-with-level's erasure. -/
def eraseDom (d : ExprA × Level) : Expr Nat × Level := (erase d.1, d.2)

theorem eraseCtx_telCtxA (ds : List (ExprA × Level)) :
    eraseCtx (telCtxA ds) = telCtxT (ds.map eraseDom) := by
  simp only [eraseCtx, telCtxA, telCtxT, List.map_reverse, List.map_map]
  rfl

section Annotate
variable {E : ResolvedEnvA} {n : Nat}

/-- a typed telescope annotated, at its recorded levels, in any well-formed annotation of its
    context. -/
theorem annTelTyT (C : AnnEnvA E) (hn : EnvNormEraseA E) : {Γ : LCtx} → {ds : List (Expr Nat × Level)} →
    TelTyT (eraseEnv E) n Γ ds → ∀ {ΓA : LCtxA}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      ∃ dsA : List (ExprA × Level), dsA.map eraseDom = ds ∧
        Nonempty (TelTyA E (iotaIfaceA E) n ΓA dsA)
  | _, _, .nil _, ΓA, _, _ => ⟨[], rfl, ⟨.nil ΓA⟩⟩
  | _, _, .cons _ _ u _ hD tl, ΓA, hΓ, hctx => by
      obtain ⟨DA, SA, hDe, hSe, ⟨tD⟩⟩ := annHasTyT' C hn hD hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨dsA, hdse, ⟨ttl⟩⟩ :=
        annTelTyT C hn tl (.assumption hΓ tD) (eraseCtx_assumption hDe hctx)
      exact ⟨(DA, u) :: dsA, by simp only [List.map_cons, eraseDom, hDe, hdse],
        ⟨.cons ΓA DA u dsA tD ttl⟩⟩

/-- a full application annotated along an annotation of its telescope that is typed at a sort. -/
theorem annArgsTyT (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} {ΓA : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n ΓA)
    (hctx : eraseCtx ΓA = Γ) : {T : Expr Nat} → {as : List (Expr Nat)} →
    ArgsTyT (eraseEnv E) n Γ T as → ∀ {TA : ExprA} {l : Level}, erase TA = T →
      HasTyA E (iotaIfaceA E) n ΓA TA (.sort l) →
      ∃ asA : List ExprA, asA.map erase = as ∧ Nonempty (ArgsTyA E (iotaIfaceA E) n ΓA TA asA)
  | _, _, .nil l, TA, _, hTe, _ => by
      obtain rfl := erase_eq_sort hTe
      exact ⟨[], rfl, ⟨.nil l⟩⟩
  | _, _, .cons A B a as ha tl, TA, _, hTe, hT => by
      obtain ⟨AA, u, BA, v, rfl, hAe, hBe⟩ := erase_eq_pi hTe
      obtain ⟨hA, hB⟩ := hasTyA_pi_parts hT
      obtain ⟨aA, A', hae, hA'e, ⟨ta⟩⟩ := annHasTyT' C hn ha hΓ hctx
      obtain ⟨ta'⟩ := hasTyA_reannot C hΓ ta (hA'e.trans hAe.symm) hA
      have hB' : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A aA BA) (.sort v) :=
        hasTyA_inst0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hB ta' hA
      obtain ⟨asA, hase, ⟨ttl⟩⟩ := annArgsTyT C hn hΓ hctx tl
        (by rw [erase_instantiate0A, hae, hBe]) hB'
      exact ⟨aA :: asA, by simp only [List.map_cons, hae, hase],
        ⟨.cons AA u BA v aA asA ta' ttl⟩⟩

/-- a type conversion annotated onto a typed annotation of its right side; the left side's
    annotation comes typed. -/
theorem annTyConvT (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} {ΓA : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n ΓA)
    (hctx : eraseCtx ΓA = Γ) : {M P : Expr Nat} → TyConvT (eraseEnv E) n Γ M P →
    ∀ {PA : ExprA} {l : Level}, erase PA = P → HasTyA E (iotaIfaceA E) n ΓA PA (.sort l) →
      ∃ (MA : ExprA) (l' : Level), erase MA = M ∧
        Nonempty (HasTyA E (iotaIfaceA E) n ΓA MA (.sort l')) ∧
        Nonempty (TyConvA E (iotaIfaceA E) n ΓA MA PA)
  | _, _, .refl _ _, PA, l, hPe, hP => ⟨PA, l, hPe, ⟨hP⟩, ⟨.refl _ _⟩⟩
  | _, _, .of _ _ _ u h, PA, _, hPe, hP => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c⟩⟩ := annConvT' C hn h hΓ hctx
      obtain rfl := erase_eq_sort hTe
      have ha := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c
      have hb := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c
      obtain ⟨t⟩ := tyConvA_of_erase C hΓ (hbe.trans hPe.symm) hb hP
      exact ⟨aA, u, hae, ⟨ha⟩,
        ⟨.trans _ _ _ _ (.of _ aA bA u u u ha (fun _ => rfl) hb (fun _ => rfl) c) t⟩⟩
  | _, _, .trans _ _ _ _ h1 h2, PA, _, hPe, hP => by
      obtain ⟨NA, _, hNe, ⟨hN⟩, ⟨t2⟩⟩ := annTyConvT C hn hΓ hctx h2 hPe hP
      obtain ⟨MA, lM, hMe, ⟨hM⟩, ⟨t1⟩⟩ := annTyConvT C hn hΓ hctx h1 hNe hN
      exact ⟨MA, lM, hMe, ⟨hM⟩, ⟨.trans _ _ _ _ t1 t2⟩⟩

/-- the parameter mirrors annotated against a typed annotation of the family's parameters. -/
theorem annMirrorsConvT (C : AnnEnvA E) (hn : EnvNormEraseA E) : {Γ : LCtx} → {ms ps : List (Expr Nat × Level)} →
    MirrorsConvT (eraseEnv E) n Γ ms ps →
    ∀ {ΓA : LCtxA} {psA : List (ExprA × Level)}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      psA.map eraseDom = ps → TelTyA E (iotaIfaceA E) n ΓA psA →
      ∃ msA : List (ExprA × Level), msA.map eraseDom = ms ∧
        Nonempty (MirrorsConvA E (iotaIfaceA E) n ΓA msA psA)
  | _, _, _, .nil _, ΓA, _, _, _, hps, htel => by
      cases htel with
      | nil => exact ⟨[], rfl, ⟨.nil ΓA⟩⟩
      | cons => exact absurd hps (by simp)
  | _, _, _, .cons _ M um P up ms ps hc hl tl, ΓA, _, hΓ, hctx, hps, htel => by
      cases htel with
      | nil => exact absurd hps (by simp)
      | cons _ PA up' psA hP htl =>
          simp only [List.map_cons, eraseDom, List.cons.injEq, Prod.mk.injEq] at hps
          obtain ⟨⟨hPe, rfl⟩, hps'⟩ := hps
          obtain ⟨MA, _, hMe, _, ⟨t⟩⟩ := annTyConvT C hn hΓ hctx hc hPe hP
          obtain ⟨msA, hmse, ⟨ttl⟩⟩ :=
            annMirrorsConvT C hn tl (.assumption hΓ hP) (eraseCtx_assumption hPe hctx) hps' htl
          exact ⟨(MA, um) :: msA, by simp only [List.map_cons, eraseDom, hMe, hmse],
            ⟨.cons ΓA MA um PA up' msA psA t hl ttl⟩⟩

/-- the split-position evidence the `.drecD` walk assembles: at every `drecD` occurrence the
    per-position property `P` holds of the consumed prefix (R-NoDeltaRec-4d-iii; at `acc = []`,
    `Γ₀ = telCtxA fv.params` this is `DrecDTypedA`'s ∀-shape). -/
def drecDSplitA (P : List FieldA → ExprA → List ExprA → Prop) (acc fs : List FieldA) : Prop :=
  ∀ fsPre D idx fsRest, fs = fsPre ++ .drecD D idx :: fsRest → P (acc ++ fsPre) D idx

theorem drecDSplitA_nil {P : List FieldA → ExprA → List ExprA → Prop} (acc : List FieldA) :
    drecDSplitA P acc [] := by
  intro fsPre D idx fsRest h
  cases fsPre <;> simp at h

theorem drecDSplitA_cons {P : List FieldA → ExprA → List ExprA → Prop} {x : FieldA}
    {acc rest : List FieldA}
    (hx : ∀ D idx, x = .drecD D idx → P acc D idx)
    (hrest : drecDSplitA P (acc ++ [x]) rest) :
    drecDSplitA P acc (x :: rest) := by
  intro fsPre D idx fsRest h
  cases fsPre with
  | nil =>
      obtain ⟨hxe, -⟩ := List.cons.inj h
      rw [List.append_nil]
      exact hx D idx hxe
  | cons y ys =>
      obtain ⟨rfl, hrest'⟩ := List.cons.inj h
      have := hrest ys D idx fsRest hrest'
      rw [show acc ++ x :: ys = acc ++ [x] ++ ys by simp [List.append_assoc]]
      exact this

/-- the parameter locals, `Θ` binders above the parameters' telescope-ctx, typed at their own
    domains — the `hc` conjunct's params part (R-NoDeltaRec-4d-iii). `viewTy_paramArgs`'s order
    flipped: the telescope is OUTER here. The args continue with `ys` at the rest-telescope;
    each `instantiate0A` residual is a lift because the locals ARE the telescope's variables
    (`viewTy_inst0_lift`). -/
def argsTyA_paramLocals {Θ : LCtxA} (hE : EnvClosedA E) (hI : IotaLiftA I)
    {rest : List (ExprA × Level)} {B : ExprA} {w : Level} {ys : List ExprA} :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
      ArgsTyA E I n (Θ ++ telCtxA ds ++ Γ) (liftA 0 Θ.length (piTelA rest B w).1) ys →
      ArgsTyA E I n (Θ ++ telCtxA ds ++ Γ)
        (liftA 0 (Θ.length + ds.length) (piTelA (ds ++ rest) B w).1)
        ((paramLocalsA ds.length).map (liftA 0 Θ.length) ++ ys)
  | _, [], .nil _, htail => by
      simpa only [piTelA, telCtxA, paramLocalsA, List.length_nil, List.map_nil, List.reverse_nil,
        List.nil_append, List.append_nil] using htail
  | Γ, (D, u) :: ds', .cons _ _ _ _ hD tl, htail => by
      rw [List.append_assoc, telCtxA_cons_append (D, u) ds' Γ]
      have hcons : (piTelA (((D, u) :: ds') ++ rest) B w).1 =
          .pi D u (piTelA (ds' ++ rest) B w).1 (piTelA (ds' ++ rest) B w).2 := rfl
      rw [hcons]
      simp only [List.length_cons, paramLocalsA, List.map_cons, List.cons_append]
      rw [liftA_pi]
      have hlift : liftA 0 Θ.length (.bvar ds'.length) = .bvar (ds'.length + Θ.length) := by
        simp only [liftA, if_pos (Nat.zero_le _)]
      rw [hlift, Nat.zero_add]
      have hlu : lookupTypeA (Θ ++ (telCtxA ds' ++ .assumption D :: Γ)) (Θ.length + ds'.length) =
          some (liftA 0 (Θ.length + ds'.length + 1) D) := by
        have h := viewTy_lookup_mid (Θ ++ telCtxA ds') D Γ
        rw [List.append_assoc] at h
        simp only [List.length_append, viewTy_telCtx_length] at h
        exact h
      have hDW : HasTyA E I n (Θ ++ (telCtxA ds' ++ .assumption D :: Γ))
          (liftA 0 (Θ.length + ds'.length + 1) D) (.sort u) := by
        have h := viewTy_wkBy hE hI (Θ ++ (telCtxA ds' ++ [.assumption D])) hD
        simp only [List.length_append, viewTy_telCtx_length, List.length_cons, List.length_nil]
          at h
        rw [show Θ ++ (telCtxA ds' ++ [.assumption D]) ++ Γ =
              Θ ++ (telCtxA ds' ++ .assumption D :: Γ) from by
              simp only [List.append_assoc, List.singleton_append, List.cons_append,
                List.nil_append]] at h
        simpa [liftA] using h
      have hHead : HasTyA E I n (Θ ++ (telCtxA ds' ++ .assumption D :: Γ))
          (.bvar (ds'.length + Θ.length)) (liftA 0 (Θ.length + ds'.length + 1) D) := by
        rw [show ds'.length + Θ.length = Θ.length + ds'.length from by omega]
        exact .bvar _ _ _ _ hlu hDW
      rw [List.append_assoc, telCtxA_cons_append (D, u) ds' Γ] at htail
      rw [← List.append_assoc] at htail
      have ih := argsTyA_paramLocals (Θ := Θ) (w := w) hE hI tl htail
      rw [List.append_assoc] at ih
      have hInst : instantiate0A (.bvar (ds'.length + Θ.length))
          (liftA 1 (Θ.length + (ds'.length + 1)) (piTelA (ds' ++ rest) B w).1) =
          liftA 0 (Θ.length + ds'.length) (piTelA (ds' ++ rest) B w).1 := by
        rw [show Θ.length + (ds'.length + 1) = (Θ.length + ds'.length) + 1 from by omega,
            show ds'.length + Θ.length = Θ.length + ds'.length from by omega]
        exact viewTy_inst0_lift (Θ.length + ds'.length) _
      exact ArgsTyA.cons (liftA 0 (Θ.length + (ds'.length + 1)) D) u
        (liftA 1 (Θ.length + (ds'.length + 1)) (piTelA (ds' ++ rest) B w).1)
        (piTelA (ds' ++ rest) B w).2 (.bvar (ds'.length + Θ.length))
        (((paramLocalsA ds'.length).map (liftA 0 Θ.length)) ++ ys) hHead
        (hInst ▸ ih)

/-- the `liftA`-shift as a parallel substitution (`argsTyA_piTelA_length` consumes `substA`-form
    spines — `liftA` is that form at the shift substitution, R-NoDeltaRec-4d-iii). -/
theorem liftA_eq_substA (c k : Nat) (e : ExprA) :
    liftA c k e = substA (fun i => if i < c then .bvar i else .bvar (i + k)) e := by
  induction e generalizing c with
  | bvar i =>
      simp only [liftA, substA]
      by_cases h : c ≤ i
      · simp [h, Nat.not_lt.mpr h]
      · simp [h, Nat.lt_of_not_le h]
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA, substA, ihf, ihx]
  | lam a u b iha ihb =>
      simp only [liftA, substA]
      have hup : (fun i => if i < c + 1 then ExprA.bvar i else ExprA.bvar (i + k)) =
          SubstA.up (fun i => if i < c then ExprA.bvar i else ExprA.bvar (i + k)) := by
        funext i
        cases i with
        | zero => simp
        | succ i =>
            simp only [SubstA.up_succ]
            show (if i + 1 < c + 1 then ExprA.bvar (i + 1) else ExprA.bvar (i + 1 + k)) =
              liftA 0 1 (if i < c then ExprA.bvar i else ExprA.bvar (i + k))
            by_cases h : i < c
            · rw [if_pos (by omega : i + 1 < c + 1), if_pos h]
              show ExprA.bvar (i + 1) = liftA 0 1 (ExprA.bvar i)
              simp [liftA]
            · rw [if_neg (by omega : ¬ i + 1 < c + 1), if_neg h]
              show ExprA.bvar (i + 1 + k) = liftA 0 1 (ExprA.bvar (i + k))
              have : liftA 0 1 (ExprA.bvar (i + k)) = ExprA.bvar (i + k + 1) :=
                if_pos (Nat.zero_le (i + k))
              rw [this, Nat.add_right_comm i 1 k]
      rw [iha, ihb (c + 1), hup]
  | pi a u b v iha ihb =>
      simp only [liftA, substA]
      have hup : (fun i => if i < c + 1 then ExprA.bvar i else ExprA.bvar (i + k)) =
          SubstA.up (fun i => if i < c then ExprA.bvar i else ExprA.bvar (i + k)) := by
        funext i
        cases i with
        | zero => simp
        | succ i =>
            simp only [SubstA.up_succ]
            show (if i + 1 < c + 1 then ExprA.bvar (i + 1) else ExprA.bvar (i + 1 + k)) =
              liftA 0 1 (if i < c then ExprA.bvar i else ExprA.bvar (i + k))
            by_cases h : i < c
            · rw [if_pos (by omega : i + 1 < c + 1), if_pos h]
              show ExprA.bvar (i + 1) = liftA 0 1 (ExprA.bvar i)
              simp [liftA]
            · rw [if_neg (by omega : ¬ i + 1 < c + 1), if_neg h]
              show ExprA.bvar (i + 1 + k) = liftA 0 1 (ExprA.bvar (i + k))
              have : liftA 0 1 (ExprA.bvar (i + k)) = ExprA.bvar (i + k + 1) :=
                if_pos (Nat.zero_le (i + k))
              rw [this, Nat.add_right_comm i 1 k]
      rw [iha, ihb (c + 1), hup]
  | letE a w b iha ihw ihb =>
      simp only [liftA, substA]
      have hup : (fun i => if i < c + 1 then ExprA.bvar i else ExprA.bvar (i + k)) =
          SubstA.up (fun i => if i < c then ExprA.bvar i else ExprA.bvar (i + k)) := by
        funext i
        cases i with
        | zero => simp
        | succ i =>
            simp only [SubstA.up_succ]
            show (if i + 1 < c + 1 then ExprA.bvar (i + 1) else ExprA.bvar (i + 1 + k)) =
              liftA 0 1 (if i < c then ExprA.bvar i else ExprA.bvar (i + k))
            by_cases h : i < c
            · rw [if_pos (by omega : i + 1 < c + 1), if_pos h]
              show ExprA.bvar (i + 1) = liftA 0 1 (ExprA.bvar i)
              simp [liftA]
            · rw [if_neg (by omega : ¬ i + 1 < c + 1), if_neg h]
              show ExprA.bvar (i + 1 + k) = liftA 0 1 (ExprA.bvar (i + k))
              have : liftA 0 1 (ExprA.bvar (i + k)) = ExprA.bvar (i + k + 1) :=
                if_pos (Nat.zero_le (i + k))
              rw [this, Nat.add_right_comm i 1 k]
      rw [iha, ihw, ihb (c + 1), hup]
  | lit t => rfl

/-- `plainIdxT` splits over concatenation (the `hke` invariant's `.plain`-arm,
    R-NoDeltaRec-4d-iii). -/
theorem plainIdxT_append : (xs ys : List FieldT) → (j : Nat) →
    plainIdxT (xs ++ ys) j = plainIdxT ys (plainIdxT xs j)
  | [], _, _ => rfl
  | .plain _ _ :: xs, ys, j => plainIdxT_append xs ys (j + 1)
  | .drec _ :: xs, ys, j => plainIdxT_append xs ys j
  | .drecD _ _ :: xs, ys, j => plainIdxT_append xs ys j

/-- the ann-side plain count is the tree-side count along erasure — `.drecD` counts nothing in
    either (R-NoDeltaRec-4d-iii). -/
theorem plainIdxA_map_erase : (fsA : List FieldA) → (j : Nat) →
    plainIdxA fsA j = plainIdxT (fsA.map FieldA.erase) j
  | [], _ => rfl
  | .plain _ _ :: fs, j => plainIdxA_map_erase fs (j + 1)
  | .drec _ :: fs, j => plainIdxA_map_erase fs j
  | .frec _ _ _ _ :: fs, j => plainIdxA_map_erase fs j
  | .drecD _ _ :: fs, j => plainIdxA_map_erase fs j

/-- `TelTyA` is `DomTyA` under another name — same constructors, same recursion. -/
def domTyA_of_telTyA : {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds →
    DomTyA E I n Γ ds
  | _, _, .nil _ => .nil _
  | _, _, .cons _ _ _ _ hD tl => .cons _ _ _ _ hD (domTyA_of_telTyA tl)

/-- the annotated family application erases to the tree's (`hPe` for `annTyConvT`,
    R-NoDeltaRec-4d-iii). -/
theorem erase_famApp (f n np : Nat) (c : Nat) (idxA : List ExprA) (idx : List (Expr Nat))
    (hidxe : idxA.map erase = idx) :
    erase (foldAppsA (.const f (canonLevelsA n))
        ((paramLocalsA np).map (liftA 0 c) ++ idxA)) =
      foldApps (.const f (canonLevels n))
        ((policyLocals np).map (lift 0 c) ++ idx) := by
  rw [erase_foldAppsA, erase, List.map_append, map_erase_liftA, erase_paramLocalsA, hidxe,
    show canonLevelsA n = canonLevels n from rfl]

/-- `SameDoms` on a `piTelA` chain is reflexive (the `hc` conjunct's spine-vs-member-type
    bridge — `T` lifts to `U` once both are closed, R-NoDeltaRec-4d-iii). -/
def sameDoms_piTel_refl : (ds : List (ExprA × Level)) → (s w : Level) →
    SameDoms (piTelA ds (.sort s) w).1 (piTelA ds (.sort s) w).1
  | [], s, _ => .done s _
  | (D, u) :: ds, s, w =>
      .step D u _ u _ _ _ (sameDoms_piTel_refl ds s w)

/-- a `DomTyA`'s domains are scope-bounded at their depths (each is typed in a context of exactly
    that length). -/
def domTyA_boundOk : {Γ : LCtxA} → {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
    ∀ (j : Nat) (D : ExprA) (u : Level), ds.get? j = some (D, u) →
      boundOkB (Γ.length + j) D = true
  | _, _, .nil _, _, _, _, h => absurd h Option.noConfusion
  | Γ, (D, u) :: ds, .cons _ _ _ _ hD tl, j, D', u', hj => by
      cases j with
      | zero =>
          obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp (Option.some.inj hj)
          exact hasTyA_boundOk hD
      | succ j =>
          have hd := domTyA_boundOk tl j D' u' (by simpa using hj)
          simp only [List.length_cons] at hd
          rw [show Γ.length + (j + 1) = Γ.length + 1 + j from by omega]
          exact hd

/-- `TelTyA` of a concatenation's prefix. -/
def telTyA_prefix : {Γ : LCtxA} → {xs ys : List (ExprA × Level)} →
    TelTyA E I n Γ (xs ++ ys) → TelTyA E I n Γ xs
  | _, [], _, _ => .nil _
  | _, (D, u) :: xs, ys, h => by
      cases h with
      | cons _ _ _ _ hD tl => exact .cons _ _ _ _ hD (telTyA_prefix tl)

/-- the plain context appends its base: `plainCtxA fs Γ` is the prefix's decls over `Γ`. -/
theorem plainCtxA_append_base : (fs : List FieldA) → (Γ : LCtxA) →
    plainCtxA fs Γ = plainCtxA fs [] ++ Γ
  | [], _ => rfl
  | .plain _ _ :: fs, Γ => by
      simp only [plainCtxA]
      rw [plainCtxA_append_base fs (.assumption _ :: Γ), plainCtxA_append_base fs [.assumption _]]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  | .drec _ :: fs, Γ => plainCtxA_append_base fs Γ
  | .frec _ _ _ _ :: fs, Γ => plainCtxA_append_base fs Γ
  | .drecD _ _ :: fs, Γ => plainCtxA_append_base fs Γ

/-- the plain context's length is the plain count. -/
theorem plainCtxA_nil_length : (fs : List FieldA) → (plainCtxA fs []).length = plainIdxA fs 0
  | [] => rfl
  | .plain D u :: fs => by
      simp only [plainCtxA, plainIdxA]
      rw [plainCtxA_append_base fs [.assumption D], List.length_append, List.length_cons,
        List.length_nil, plainIdxA_add, plainCtxA_nil_length fs]
      omega
  | .drec _ :: fs => plainCtxA_nil_length fs
  | .frec _ _ _ _ :: fs => plainCtxA_nil_length fs
  | .drecD _ _ :: fs => plainCtxA_nil_length fs



/-- the `hc` conjunct's right side: the family's self-application at the field's position —
    params as the telescope's own locals lifted over `Θ`, then the field's indices
    (R-NoDeltaRec-4d-iii). -/
def famApp_typed {n : Nat} {pA iA : List (ExprA × Level)} {s u : Level}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    (hEL : EnvLevelsA E) (hIL : IotaLevelsA I)
    {Θ Γ : LCtxA} (hΓ : CtxWfA E I n Γ) (hΘ : Γ = Θ ++ telCtxA pA)
    (ht : TelTyA E I n [] (pA ++ iA))
    {idxA : List ExprA} (hi : idxA.length = iA.length)
    (hidx : ArgsTyA E I n Γ (liftA 0 Θ.length (piTelA iA (.sort s) (.succ s)).1) idxA)
    {fmA : CheckedMemberA} (ha : fmA.arity = n)
    (hm : fmA.mtypeA = (piTelA (pA ++ iA) (.sort s) (.succ s)).1)
    {f : Nat} (hmf : E.members f = some fmA)
    (hTfm : HasTyA E I n [] fmA.mtypeA (.sort u)) :
    Nonempty (HasTyA E I n Γ
      (foldAppsA (.const f (canonLevelsA n))
        ((paramLocalsA pA.length).map (liftA 0 Θ.length) ++ idxA)) (.sort s)) := by
  subst hΘ
  have hidx : ArgsTyA E I n (Θ ++ telCtxA pA ++ [])
      (liftA 0 Θ.length (piTelA iA (.sort s) (.succ s)).1) idxA :=
    (List.append_nil _).symm ▸ hidx
  have hdPI := domTyA_of_telTyA ht
  have hp : DomTyA E I n [] pA := domTyA_of_telTyA (telTyA_prefix ht)
  have hargs := argsTyA_paramLocals (Θ := Θ) (w := s.succ) (B := .sort s) (rest := iA) hE hI hp hidx
  rw [List.append_nil] at hargs
  have hlen : (((paramLocalsA pA.length).map (liftA 0 Θ.length)) ++ idxA).length =
      (pA ++ iA).length := by
    rw [List.length_append, List.length_map, paramLocalsA_length, hi, List.length_append]
  have hb : boundOkB 0 (piTelA (pA ++ iA) (.sort s) (.succ s)).1 = true :=
    piTelA_boundOk (pA ++ iA) (.sort s) (.succ s) 0
      (fun j D u' hj => domTyA_boundOk hdPI j D u' hj) rfl
  have hUi : instantiateLevelsA (canonLevelsA n) fmA.mtypeA = fmA.mtypeA :=
    viewTy_instantiateLevelsA_canon n fmA.mtypeA
  have hUs : instantiateLevelsA (canonLevelsA n) (.sort u) = .sort u := by
    simp only [instantiateLevelsA, viewTy_instLevel_canon]
  have hbM : boundOkB 0 fmA.mtypeA = true := hm ▸ hb
  have hT : HasTyA E I n (Θ ++ telCtxA pA) (instantiateLevelsA (canonLevelsA n) fmA.mtypeA)
      (.sort u) := by
    have hi' := hasTyA_instLevels hEL hIL (levelsBounded_canonA n) (viewTy_canon_length n) hTfm
    rw [hUi, show instCtxA (canonLevelsA n) [] = [] from rfl] at hi'
    have hw := viewTy_wkBy hE hI (Θ ++ telCtxA pA) hi'
    rw [List.append_nil, hUs, liftA_of_boundOkB _ 0 _ hbM] at hw
    exact hUi.symm ▸ hw
  have hf : HasTyA E I n (Θ ++ telCtxA pA) (.const f (canonLevelsA n))
      (instantiateLevelsA (canonLevelsA n) fmA.mtypeA) :=
    .const _ f _ fmA u hmf ((viewTy_canon_length n).trans ha.symm)
      (ha ▸ levelsBounded_canonA n) hT
  have hTsp : liftA 0 (Θ.length + pA.length) (piTelA (pA ++ iA) (.sort s) (.succ s)).1 =
      (piTelA (pA ++ iA) (.sort s) (.succ s)).1 :=
    liftA_of_boundOkB _ 0 _ hb
  have hUsp : instantiateLevelsA (canonLevelsA n) fmA.mtypeA =
      (piTelA (pA ++ iA) (.sort s) (.succ s)).1 := hUi.trans hm
  have hsame : SameDoms
      (liftA 0 (Θ.length + pA.length) (piTelA (pA ++ iA) (.sort s) (.succ s)).1)
      (instantiateLevelsA (canonLevelsA n) fmA.mtypeA) := by
    rw [hTsp, hUsp]
    exact sameDoms_piTel_refl (pA ++ iA) s (.succ s)
  have hTpi : HasTyA E I n (Θ ++ telCtxA pA) (piTelA (pA ++ iA) (.sort s) (.succ s)).1
      (.sort u) := by
    have h := viewTy_wkBy hE hI (Θ ++ telCtxA pA) hTfm
    rw [List.append_nil, liftA_of_boundOkB _ 0 _ hbM, hm] at h
    exact h
  have hTsp' : HasTyA E I n (Θ ++ telCtxA pA)
      (liftA 0 (Θ.length + pA.length) (piTelA (pA ++ iA) (.sort s) (.succ s)).1) (.sort u) := by
    rwa [hTsp]
  have hfold := viewTy_peelApps hE hI hR hIS hΓ hsame hTsp' hT hf hargs
  have hres : instSpine (((paramLocalsA pA.length).map (liftA 0 Θ.length)) ++ idxA)
      (instantiateLevelsA (canonLevelsA n) fmA.mtypeA) = .sort s := by
    rw [hUsp]
    have h := instSpine_piTel (.sort s) (.succ s) (pA ++ iA)
      (((paramLocalsA pA.length).map (liftA 0 Θ.length)) ++ idxA) .id hlen
    rw [substA_id, substA_sort] at h
    exact h
  exact ⟨hres ▸ hfold⟩
/-- the fields annotated in the plain context, along an annotation `X` of the family's index
    telescope that is typed at a sort there. A `.drecD` field's surface domain is typed in the
    family's scope — the base env extended by the family member — so the annotation needs the
    extended `C'` and a positional premise `hdd` giving each δ-reached field's `HasTyT` at the
    plain context of the fields before it (R-NoDeltaRec-4d-ii): the caller's `DrecDTypedT`
    supplies it verbatim at `fs0 := c.view.fields`, `Γ₀ := telCtxT fv.params`. `fsCons` tracks
    the consumed prefix so the position inside `hdd` is nameable; the result's `NoFun` (not
    `TreeField`) records that `.drecD` annotations are function-free but not δ-free. -/
theorem annFieldsTyT (C : AnnEnvA E) (hn : EnvNormEraseA E) (X : ExprA)
    {f : Nat} {fm : CheckedMember} {fv : FamViewT fm} {fmA : CheckedMemberA}
    (hme : eraseMember fmA = fm) (hfr : E.members f = none)
    (C' : AnnEnvA (extendEnvA E f fmA)) (hn' : EnvNormEraseA (extendEnvA E f fmA))
    (hpreA : PrefixA E (extendEnvA E f fmA))
    {Γ₀ : LCtx} {fs0 : List FieldT}
    (hdd : ∀ (fsPre : List FieldT) (D : Expr Nat) (idx : List (Expr Nat)) (fsRest : List FieldT),
        fs0 = fsPre ++ FieldT.drecD D idx :: fsRest →
        Nonempty (HasTyT (extendEnv (eraseEnv E) f fm) n (plainCtxT fsPre Γ₀) D (.sort fv.sort)) ∧
        Nonempty (TyConvT (extendEnv (eraseEnv E) f fm) n (plainCtxT fsPre Γ₀) D
          (foldApps (.const f (canonLevels fm.arity))
            ((policyLocals fv.params.length).map (lift 0 (plainIdxT fsPre 0)) ++ idx))) ∧
        ∀ x ∈ idx, exprLevelsBounded fm.arity x = true)
    (pA iA : List (ExprA × Level)) (ΓA₀ : LCtxA)
    (hΓ₀pA : ΓA₀ = telCtxA pA) (hΓ₀e : eraseCtx ΓA₀ = Γ₀)
    (hXe : X = (piTelA iA (.sort fv.sort) (.succ fv.sort)).1)
    (hm : fmA.mtypeA = (piTelA (pA ++ iA) (.sort fv.sort) (.succ fv.sort)).1)
    (ha : fmA.arity = n) (htel : TelTyA E (iotaIfaceA E) n [] (pA ++ iA))
    (hplen : pA.length = fv.params.length) :
    ∀ (fsCons : List FieldT) (fsConsA : List FieldA) {Γ : LCtx} {k : Nat} {fs : List FieldT}
      {res : List (Expr Nat)},
      fsConsA.map FieldA.erase = fsCons →
      FieldsTyT (eraseEnv E) n (fun k => lift 0 k (erase X)) Γ k fs res →
      fs0 = fsCons ++ fs → Γ = plainCtxT fsCons Γ₀ → k = plainIdxT fsCons 0 →
      ∀ {ΓA : LCtxA} {l : Level}, ΓA = plainCtxA fsConsA ΓA₀ →
        CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
        HasTyA E (iotaIfaceA E) n ΓA (liftA 0 k X) (.sort l) →
        ∃ (fsA : List FieldA) (resA : List ExprA), fsA.map FieldA.erase = fs ∧
          resA.map erase = res ∧
          Nonempty (FieldsTyA E (iotaIfaceA E) n (fun k => liftA 0 k X) ΓA k fsA resA) ∧
          (∀ x ∈ fsA, x.NoFun) ∧
          drecDSplitA (fun fsPre DA idxA =>
            Nonempty (HasTyA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
              (plainCtxA fsPre ΓA₀) DA (.sort fv.sort)) ∧
            Nonempty (ConvA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
              (plainCtxA fsPre ΓA₀) DA
              (foldAppsA (.const f (canonLevelsA n))
                ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idxA))
              (.sort fv.sort)) ∧
            ∀ x ∈ idxA, exprLevelsBounded n (erase x) = true) fsConsA fsA
  | fsCons, fsConsA, _, k, _, _, _, .nil _ _ _ hres, hcons, hΓe, _hke, ΓA, _, hΓAe, hΓ, hctx, hX => by
      obtain ⟨resA, hrese, ⟨tres⟩⟩ := annArgsTyT C hn hΓ hctx hres (erase_liftA X 0 k) hX
      exact ⟨[], resA, rfl, hrese, ⟨.nil ΓA k resA tres⟩, fun _ h => absurd h (List.not_mem_nil _),
        drecDSplitA_nil fsConsA⟩
  | fsCons, fsConsA, _, k, _, _, hconsAE, .plain _ _ D u fs res hD tl, hcons, hΓe, hke, ΓA, l, hΓAe, hΓ, hctx, hX => by
      obtain ⟨DA, SA, hDe, hSe, ⟨tD⟩⟩ := annHasTyT' C hn hD hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have hX' : HasTyA E (iotaIfaceA E) n (.assumption DA :: ΓA) (liftA 0 (k + 1) X)
          (.sort l) := by
        have h := hasTyWeakenA C.hE C.hI (.assumption DA) (Nat.zero_le _) hX
        rw [liftA_liftA_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le _)] at h
        exact h
      obtain ⟨fsA, resA, hfse, hrese, ⟨ttl⟩, hnf, hsp⟩ :=
        annFieldsTyT C hn X hme hfr C' hn' hpreA hdd pA iA ΓA₀ hΓ₀pA hΓ₀e hXe hm ha htel hplen (fsCons ++ [.plain D u]) (fsConsA ++ [.plain DA u])
          (by simp only [List.map_append, List.map_cons, List.map_nil, FieldA.erase, hDe, hconsAE])
          tl
          (by rw [hcons, List.append_assoc]; rfl)
          (by rw [hΓe, plainCtxT_append]; rfl)
          (by rw [plainIdxT_append]; show k + 1 = plainIdxT fsCons 0 + 1; omega)
          (by rw [hΓAe, plainCtxA_append]; rfl)
          (.assumption hΓ tD) (eraseCtx_assumption hDe hctx) hX'
      exact ⟨.plain DA u :: fsA, resA, by simp only [List.map_cons, FieldA.erase, hDe, hfse],
        hrese, ⟨.plain ΓA k DA u fsA resA tD ttl⟩, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · trivial
          · exact hnf x hx,
        drecDSplitA_cons (fun _ _ h => FieldA.noConfusion h) hsp⟩
  | fsCons, fsConsA, _, k, _, _, hconsAE, .drec _ _ idx fs res hidx tl, hcons, hΓe, hke, ΓA, _, hΓAe, hΓ, hctx, hX => by
      obtain ⟨idxA, hidxe, ⟨tidx⟩⟩ := annArgsTyT C hn hΓ hctx hidx (erase_liftA X 0 k) hX
      obtain ⟨fsA, resA, hfse, hrese, ⟨ttl⟩, hnf, hsp⟩ :=
        annFieldsTyT C hn X hme hfr C' hn' hpreA hdd pA iA ΓA₀ hΓ₀pA hΓ₀e hXe hm ha htel hplen (fsCons ++ [.drec idx]) (fsConsA ++ [.drec idxA])
          (by simp only [List.map_append, List.map_cons, List.map_nil, FieldA.erase, List.map_map,
            hidxe, hconsAE])
          tl
          (by rw [hcons, List.append_assoc]; rfl)
          (by rw [hΓe, plainCtxT_append]; rfl)
          (by rw [plainIdxT_append]; exact hke)
          (by rw [plainCtxA_append]; exact hΓAe)
          hΓ hctx hX
      exact ⟨.drec idxA :: fsA, resA, by simp only [List.map_cons, FieldA.erase, hidxe, hfse],
        hrese, ⟨.drec ΓA k idxA fsA resA tidx ttl⟩, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · trivial
          · exact hnf x hx,
        drecDSplitA_cons (fun _ _ h => FieldA.noConfusion h) hsp⟩
  | fsCons, fsConsA, _, k, _, _, hconsAE, .drecD _ _ D idx fs res hidx tl, hcons, hΓe, hke, ΓA, l, hΓAe, hΓ, hctx, hX => by
      -- the surface domain's typing at THIS position: `plainCtxT fsCons Γ₀` = Γ.
      obtain ⟨⟨hD⟩, ⟨hconvT⟩, hidxB⟩ := hdd fsCons D idx fs hcons
      have hDA : HasTyT (eraseEnv (extendEnvA E f fmA)) n (plainCtxT fsCons Γ₀) D
          (.sort fv.sort) := by
        have he := eraseEnv_extend E f fmA
        rw [he, hme] ; exact hD
      obtain ⟨hW⟩ := C.wf
      have hag : ∀ e, ConstsInA (domA E) e →
          (iotaIfaceA E).fn e = (iotaIfaceA (extendEnvA E f fmA)).fn e :=
        fun e hce => (iotaFnA_prefix hW hpreA hce).symm
      have hΓ' : CtxWfA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n ΓA :=
        ctxWfA_env_iface hpreA hag hΓ
      obtain ⟨DA, SA, hDe, hSe, ⟨tD⟩⟩ := annHasTyT' C' hn' hDA hΓ' (hctx.trans hΓe)
      obtain rfl := erase_eq_sort hSe
      obtain ⟨idxA, hidxe, ⟨tidx⟩⟩ := annArgsTyT C hn hΓ hctx hidx (erase_liftA X 0 k) hX
      obtain ⟨fsA, resA, hfse, hrese, ⟨ttl⟩, hnf, hsp⟩ :=
        annFieldsTyT C hn X hme hfr C' hn' hpreA hdd pA iA ΓA₀ hΓ₀pA hΓ₀e hXe hm ha htel hplen (fsCons ++ [.drecD D idx]) (fsConsA ++ [.drecD DA idxA])
          (by simp only [List.map_append, List.map_cons, List.map_nil, FieldA.erase, List.map_map,
            hDe, hidxe, hconsAE])
          tl
          (by rw [hcons, List.append_assoc]; rfl)
          (by rw [hΓe, plainCtxT_append]; rfl)
          (by rw [plainIdxT_append]; exact hke)
          (by rw [plainCtxA_append]; exact hΓAe)
          hΓ hctx hX
      refine ⟨.drecD DA idxA :: fsA, resA, ?_, hrese, ⟨.drecD ΓA k DA idxA fsA resA tidx ttl⟩,
        ?_, ?_⟩
      · simp only [List.map_cons, FieldA.erase, hDe, hidxe, hfse]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · trivial
        · exact hnf x hx
      · apply drecDSplitA_cons _ hsp
        intro D' idx' h
        obtain ⟨rfl, rfl⟩ := (FieldA.drecD.injEq _ _ _ _).mp h
        have hΓ'' : CtxWfA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
            (plainCtxA fsConsA ΓA₀) := hΓAe ▸ hΓ'
        have hctx'' : eraseCtx (plainCtxA fsConsA ΓA₀) = plainCtxT fsCons Γ₀ := by
          rw [eraseCtx_plainCtxA, hconsAE, hΓ₀e]
        have tD' : HasTyA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
            (plainCtxA fsConsA ΓA₀) DA (.sort fv.sort) := hΓAe ▸ tD
        have hPlen : (plainCtxA fsConsA []).length = k := by
          rw [plainCtxA_nil_length, plainIdxA_map_erase, hconsAE]
          exact hke.symm
        have hidx' : ArgsTyA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
            (plainCtxA fsConsA ΓA₀)
            (liftA 0 (plainCtxA fsConsA []).length
              (piTelA iA (.sort fv.sort) (.succ fv.sort)).1) idxA := by
          have h1 := argsTyA_env_iface hpreA hag tidx
          rw [hΓAe, hXe, ← hPlen] at h1
          exact h1
        have hidx_len : idxA.length = iA.length := by
          have h2 : ArgsTyA E (iotaIfaceA E) n ΓA
              (substA (fun i => if i < 0 then ExprA.bvar i else ExprA.bvar (i + k))
                (piTelA iA (.sort fv.sort) (.succ fv.sort)).1) idxA := by
            rw [← liftA_eq_substA, ← hXe]
            exact tidx
          exact argsTyA_piTelA_length _ _ _ _ h2
        have hPe : erase (foldAppsA (.const f (canonLevelsA n))
              ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsConsA 0)) ++ idxA)) =
            foldApps (.const f (canonLevels fm.arity))
              ((policyLocals fv.params.length).map (lift 0 (plainIdxT fsCons 0)) ++ idx) := by
          simp only [erase_foldAppsA, erase, List.map_append]
          congr 1
          · exact congrArg (Expr.const f) (congrArg canonLevels
              ((congrArg CheckedMember.arity hme).symm.trans ha).symm)
          · rw [map_erase_liftA, erase_paramLocalsA, plainIdxA_map_erase, hconsAE, hidxe]
        have hconvT' : TyConvT (eraseEnv (extendEnvA E f fmA)) n (plainCtxT fsCons Γ₀) D
            (foldApps (.const f (canonLevels fm.arity))
              ((policyLocals fv.params.length).map (lift 0 (plainIdxT fsCons 0)) ++ idx)) := by
          rw [eraseEnv_extend, hme]; exact hconvT
        obtain ⟨hΓwf⟩ := C'.wf
        obtain ⟨u, ⟨hTfm⟩⟩ := envWfA_memberTy hΓwf f fmA (members_extendEnvA_self _ _ _)
        obtain ⟨hP⟩ := famApp_typed C'.hE C'.hI C'.hR C'.hIS C'.hEL C'.hIL hΓ''
          (Θ := plainCtxA fsConsA [])
          (by rw [← hΓ₀pA]; exact plainCtxA_append_base fsConsA ΓA₀)
          (telTyA_env_iface hpreA hag htel) hidx_len hidx' ha hm
          (members_extendEnvA_self _ _ _) (ha ▸ hTfm)
        rw [plainCtxA_nil_length] at hP
        have hP' := hplen ▸ hP
        obtain ⟨MA, l', hMe, ⟨tM⟩, ⟨tc⟩⟩ := annTyConvT C' hn' hΓ'' hctx'' hconvT' hPe hP'
        obtain ⟨hDMA⟩ := annCohA C'.hE C'.hI C'.hIS C'.hENC C'.hEN C'.hR (C'.hS n) posValA_one DA hΓ''
          (hDe.trans hMe.symm) tD' tM
        have hMPA : ConvA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) n
            (plainCtxA fsConsA ΓA₀) MA
            (foldAppsA (.const f (canonLevelsA n))
              ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsConsA 0)) ++ idxA))
            (.sort l') :=
          tyConvA_collapse C'.hE C'.hI C'.hIS C'.hENC C'.hEN C'.hR (C'.hS n) posValA_one hΓ'' tc tM
        have hMrt := convA_hasTy_right C'.hE C'.hI C'.hR C'.hIS hΓ'' hDMA
        have hsu : eqN fv.sort l' := sortUniqA C'.hE C'.hI C'.hIS C'.hENC C'.hEN C'.hR (C'.hS n) posValA_one
          hΓ'' hMrt tM
        have hMPA' := convA_sort_eqN hMPA (fun ρ => (hsu ρ).symm)
        exact ⟨⟨tD'⟩, ⟨.trans _ _ _ _ _ hDMA hMPA'⟩, fun x hx => by
          have hm' : erase x ∈ idx := hidxe ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
          exact (congrArg CheckedMember.arity hme).symm.trans ha ▸ hidxB (erase x) hm'⟩

end Annotate

/-! ## (3) closing the views' levels at the family's arity

Annotation copies binder levels from derivations, and those may name level parameters past the
family's arity. The closing list `closeLs a M` keeps the family's own parameters and sends the next
`M` to `zero`; a level context weakened to `a + M` and instantiated at it lands back at `a`. -/

section Close

def TelTyA.close (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I a Γ ds →
    TelTyA E I a (instCtxA (closeLs a M) Γ) (instDomsA (closeLs a M) ds)
  | _, _, .nil _ => .nil _
  | _, _, .cons Γ D u ds hD tl =>
      .cons _ _ _ _ (closeTyA hEL hIL a M hD) (TelTyA.close hEL hIL a M tl)

def ArgsTyA.close (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) {Γ : LCtxA} :
    {T : ExprA} → {as : List ExprA} → ArgsTyA E I a Γ T as →
    ArgsTyA E I a (instCtxA (closeLs a M) Γ) (instantiateLevelsA (closeLs a M) T)
      (as.map (instantiateLevelsA (closeLs a M)))
  | _, _, .nil l => .nil _
  | _, _, .cons A u B v x xs hx tl =>
      .cons _ _ _ _ _ _ (closeTyA hEL hIL a M hx)
        ((instantiateLevelsA_instantiate0A (closeLs a M) x B) ▸ ArgsTyA.close hEL hIL a M tl)

def TyConvA.close (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) :
    {Γ : LCtxA} → {A B : ExprA} → TyConvA E I a Γ A B →
    TyConvA E I a (instCtxA (closeLs a M) Γ) (instantiateLevelsA (closeLs a M) A)
      (instantiateLevelsA (closeLs a M) B)
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .of _ _ _ l l' u hAl hlu hBl hl'u h =>
      .of _ _ _ _ _ _ (closeTyA hEL hIL a M hAl) (eqN_instLevel hlu _) (closeTyA hEL hIL a M hBl)
        (eqN_instLevel hl'u _) (closeConvA hEL hIL a M h)
  | _, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (TyConvA.close hEL hIL a M h1) (TyConvA.close hEL hIL a M h2)

def MirrorsConvA.close (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) :
    {Γ : LCtxA} → {ms ps : List (ExprA × Level)} → MirrorsConvA E I a Γ ms ps →
    MirrorsConvA E I a (instCtxA (closeLs a M) Γ) (instDomsA (closeLs a M) ms)
      (instDomsA (closeLs a M) ps)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons _ _ _ _ _ _ _ hc hl tl =>
      .cons _ _ _ _ _ _ _ (TyConvA.close hEL hIL a M hc) (eqN_instLevel hl _)
        (MirrorsConvA.close hEL hIL a M tl)

def FieldsTyA.close (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (a M : Nat) (X : ExprA) :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I a (fun k => liftA 0 k X) Γ k fs res →
    FieldsTyA E I a (fun k => liftA 0 k (instantiateLevelsA (closeLs a M) X))
      (instCtxA (closeLs a M) Γ) k (fs.map (FieldA.instLevels (closeLs a M)))
      (res.map (instantiateLevelsA (closeLs a M)))
  | _, k, _, _, .nil _ _ _ hres =>
      .nil _ _ _ ((instantiateLevelsA_liftA (closeLs a M) 0 k X) ▸ ArgsTyA.close hEL hIL a M hres)
  | _, _, _, _, .plain _ _ _ _ _ _ hD tl =>
      .plain _ _ _ _ _ _ (closeTyA hEL hIL a M hD) (FieldsTyA.close hEL hIL a M X tl)
  | _, k, _, _, .drec _ _ _ _ _ hidx tl =>
      .drec _ _ _ _ _ ((instantiateLevelsA_liftA (closeLs a M) 0 k X) ▸ ArgsTyA.close hEL hIL a M hidx)
        (FieldsTyA.close hEL hIL a M X tl)
  | _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom tl =>
      .frec _ _ _ _ _ _ _ _
        (by
          have h := FieldsTyA.close hEL hIL a M X hdom
          rw [plainA_instLevels] at h
          exact h)
        (FieldsTyA.close hEL hIL a M X tl)
  | _, k, _, _, .drecD _ _ _ _ _ _ hidx tl =>
      .drecD _ _ _ _ _ _ ((instantiateLevelsA_liftA (closeLs a M) 0 k X) ▸ ArgsTyA.close hEL hIL a M hidx)
        (FieldsTyA.close hEL hIL a M X tl)

/-- closing does not depend on how far past the bound the list reaches. -/
theorem instLevel_closeLs_indep {a M₁ M₂ : Nat} : (l : Level) → levelBounded (a + M₁) l = true →
    levelBounded (a + M₂) l = true → instLevel (closeLs a M₁) l = instLevel (closeLs a M₂) l
  | .zero, _, _ => rfl
  | .succ l, h₁, h₂ => congrArg Level.succ (instLevel_closeLs_indep l h₁ h₂)
  | .max x y, h₁, h₂ => by
      simp only [levelBounded, Bool.and_eq_true] at h₁ h₂
      show Level.max (instLevel _ x) (instLevel _ y) = Level.max (instLevel _ x) (instLevel _ y)
      rw [instLevel_closeLs_indep x h₁.1 h₂.1, instLevel_closeLs_indep y h₁.2 h₂.2]
  | .imax x y, h₁, h₂ => by
      simp only [levelBounded, Bool.and_eq_true] at h₁ h₂
      show Level.imax (instLevel _ x) (instLevel _ y) = Level.imax (instLevel _ x) (instLevel _ y)
      rw [instLevel_closeLs_indep x h₁.1 h₂.1, instLevel_closeLs_indep y h₁.2 h₂.2]
  | .param i, h₁, h₂ => by
      simp only [levelBounded, decide_eq_true_eq] at h₁ h₂
      rw [instLevel_param, instLevel_param]
      by_cases hi : i < a
      · rw [closeLs_get_lt hi, closeLs_get_lt hi]
      · rw [closeLs_get_ge (by omega) h₁, closeLs_get_ge (by omega) h₂]

theorem levels_closeLs_indep {a M₁ M₂ : Nat} : (ls : List Level) → levelsBounded (a + M₁) ls = true →
    levelsBounded (a + M₂) ls = true → ls.map (instLevel (closeLs a M₁)) = ls.map (instLevel (closeLs a M₂))
  | [], _, _ => rfl
  | l :: ls, h₁, h₂ => by
      simp only [levelsBounded, Bool.and_eq_true] at h₁ h₂
      simp only [List.map_cons, instLevel_closeLs_indep l h₁.1 h₂.1, levels_closeLs_indep ls h₁.2 h₂.2]

theorem inst_closeLs_indep {a M₁ M₂ : Nat} : (e : ExprA) → exprLevelsBoundedA (a + M₁) e = true →
    exprLevelsBoundedA (a + M₂) e = true →
    instantiateLevelsA (closeLs a M₁) e = instantiateLevelsA (closeLs a M₂) e
  | .bvar _, _, _ => rfl
  | .sort l, h₁, h₂ => by
      simp only [instantiateLevelsA]; rw [instLevel_closeLs_indep l h₁ h₂]
  | .const r ms, h₁, h₂ => by
      simp only [instantiateLevelsA]; rw [levels_closeLs_indep ms h₁ h₂]
  | .app f x, h₁, h₂ => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h₁ h₂
      simp only [instantiateLevelsA, inst_closeLs_indep f h₁.1 h₂.1, inst_closeLs_indep x h₁.2 h₂.2]
  | .lam x u b, h₁, h₂ => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h₁ h₂
      simp only [instantiateLevelsA, inst_closeLs_indep x h₁.1.1 h₂.1.1,
        instLevel_closeLs_indep u h₁.1.2 h₂.1.2, inst_closeLs_indep b h₁.2 h₂.2]
  | .pi x u b v, h₁, h₂ => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h₁ h₂
      simp only [instantiateLevelsA, inst_closeLs_indep x h₁.1.1.1 h₂.1.1.1,
        instLevel_closeLs_indep u h₁.1.1.2 h₂.1.1.2, inst_closeLs_indep b h₁.1.2 h₂.1.2,
        instLevel_closeLs_indep v h₁.2 h₂.2]
  | .letE x w b, h₁, h₂ => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h₁ h₂
      simp only [instantiateLevelsA, inst_closeLs_indep x h₁.1.1 h₂.1.1, inst_closeLs_indep w h₁.1.2 h₂.1.2,
        inst_closeLs_indep b h₁.2 h₂.2]
  | .lit _, _, _ => rfl

/-- a telescope's domains bounded at `k`. -/
def DomsBoundedA (k : Nat) (ds : List (ExprA × Level)) : Prop :=
  ∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true

/-- a bound for a telescope's domains. -/
def domsBoundA : List (ExprA × Level) → Nat
  | [] => 0
  | d :: ds => max (max (lvlBoundA d.1) (lvlBound d.2)) (domsBoundA ds)

theorem domsBoundedA_mono {j k : Nat} (h : j ≤ k) {ds : List (ExprA × Level)} (hds : DomsBoundedA j ds) :
    DomsBoundedA k ds := fun d hd =>
  ⟨exprLevelsBoundedA_mono h _ (hds d hd).1, levelBounded_mono h _ (hds d hd).2⟩

theorem domsBoundedA_domsBoundA : (ds : List (ExprA × Level)) → DomsBoundedA (domsBoundA ds) ds
  | [] => fun _ h => absurd h (List.not_mem_nil _)
  | (D, u) :: ds => fun d hd => by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨exprLevelsBoundedA_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) _
            (exprLevelsBoundedA_lvlBoundA _),
          levelBounded_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) _
            (levelBounded_lvlBound _)⟩
      · exact domsBoundedA_mono (Nat.le_max_right _ _) (domsBoundedA_domsBoundA ds) d hd

theorem instDomsA_closeLs_indep {a M₁ M₂ : Nat} {ds : List (ExprA × Level)} (h₁ : DomsBoundedA (a + M₁) ds)
    (h₂ : DomsBoundedA (a + M₂) ds) : instDomsA (closeLs a M₁) ds = instDomsA (closeLs a M₂) ds := by
  unfold instDomsA
  apply List.map_congr_left
  intro d hd
  rw [inst_closeLs_indep d.1 (h₁ d hd).1 (h₂ d hd).1, instLevel_closeLs_indep d.2 (h₁ d hd).2 (h₂ d hd).2]

theorem domsBoundedA_close {a M : Nat} {ds : List (ExprA × Level)} (h : DomsBoundedA (a + M) ds) :
    DomsBoundedA a (instDomsA (closeLs a M) ds) := fun d hd => by
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  exact ⟨exprLevelsBoundedA_inst_closeLs _ (h d' hd').1, levelBounded_inst_closeLs _ (h d' hd').2⟩

end Close

/-! ## (4) the builders keep levels bounded -/

section Bounds
variable (k : Nat)

theorem exprLevelsBoundedA_liftA (c n : Nat) : (e : ExprA) →
    exprLevelsBoundedA k (liftA c n e) = exprLevelsBoundedA k e
  | .bvar i => by simp only [liftA]; split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f x => by
      simp only [liftA, exprLevelsBoundedA, exprLevelsBoundedA_liftA c n f, exprLevelsBoundedA_liftA c n x]
  | .lam x u b => by
      simp only [liftA, exprLevelsBoundedA, exprLevelsBoundedA_liftA c n x,
        exprLevelsBoundedA_liftA (c + 1) n b]
  | .pi x u b v => by
      simp only [liftA, exprLevelsBoundedA, exprLevelsBoundedA_liftA c n x,
        exprLevelsBoundedA_liftA (c + 1) n b]
  | .letE x w b => by
      simp only [liftA, exprLevelsBoundedA, exprLevelsBoundedA_liftA c n x, exprLevelsBoundedA_liftA c n w,
        exprLevelsBoundedA_liftA (c + 1) n b]
  | .lit _ => rfl

theorem exprLevelsBoundedA_substA : (e : ExprA) → (σ : SubstA) →
    (∀ i, exprLevelsBoundedA k (σ i) = true) → exprLevelsBoundedA k e = true →
    exprLevelsBoundedA k (substA σ e) = true
  | .bvar i, _, hσ, _ => hσ i
  | .sort _, _, _, h => h
  | .const _ _, _, _, h => h
  | .app f x, σ, hσ, h => by
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA f σ hσ (boolAnd_left h), exprLevelsBoundedA_substA x σ hσ (boolAnd_right h)]
      rfl
  | .lam x u b, σ, hσ, h => by
      have hup : ∀ i, exprLevelsBoundedA k (σ.up i) = true := fun i => by
        cases i with
        | zero => rfl
        | succ i => rw [SubstA.up_succ, exprLevelsBoundedA_liftA]; exact hσ i
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA x σ hσ (boolAnd_left (boolAnd_left h)), boolAnd_right (boolAnd_left h),
        exprLevelsBoundedA_substA b σ.up hup (boolAnd_right h)]
      rfl
  | .pi x u b v, σ, hσ, h => by
      have hup : ∀ i, exprLevelsBoundedA k (σ.up i) = true := fun i => by
        cases i with
        | zero => rfl
        | succ i => rw [SubstA.up_succ, exprLevelsBoundedA_liftA]; exact hσ i
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA x σ hσ (boolAnd_left (boolAnd_left (boolAnd_left h))),
        boolAnd_right (boolAnd_left (boolAnd_left h)),
        exprLevelsBoundedA_substA b σ.up hup (boolAnd_right (boolAnd_left h)), boolAnd_right h]
      rfl
  | .letE x w b, σ, hσ, h => by
      have hup : ∀ i, exprLevelsBoundedA k (σ.up i) = true := fun i => by
        cases i with
        | zero => rfl
        | succ i => rw [SubstA.up_succ, exprLevelsBoundedA_liftA]; exact hσ i
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA x σ hσ (boolAnd_left (boolAnd_left h)),
        exprLevelsBoundedA_substA w σ hσ (boolAnd_right (boolAnd_left h)),
        exprLevelsBoundedA_substA b σ.up hup (boolAnd_right h)]
      rfl
  | .lit _, _, _, h => h

theorem exprLevelsBoundedA_foldAppsA : (h : ExprA) → (xs : List ExprA) → exprLevelsBoundedA k h = true →
    (∀ x ∈ xs, exprLevelsBoundedA k x = true) → exprLevelsBoundedA k (foldAppsA h xs) = true
  | _, [], hh, _ => hh
  | h, x :: xs, hh, hxs =>
      exprLevelsBoundedA_foldAppsA (.app h x) xs
        (by simp only [exprLevelsBoundedA, hh, hxs x (List.mem_cons_self _ _)]; rfl)
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

theorem paramLocalsA_bounded : (n : Nat) → ∀ x ∈ paramLocalsA n, exprLevelsBoundedA k x = true
  | 0 => fun _ h => absurd h (List.not_mem_nil _)
  | n + 1 => fun x h => by
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact paramLocalsA_bounded n x h

theorem piTelA_bounded_fwd (B : ExprA) (w : Level) (hB : exprLevelsBoundedA k B = true)
    (hw : levelBounded k w = true) : (ds : List (ExprA × Level)) →
    (∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) →
    exprLevelsBoundedA k (piTelA ds B w).1 = true ∧ levelBounded k (piTelA ds B w).2 = true
  | [], _ => ⟨hB, hw⟩
  | (D, u) :: ds, hds => by
      obtain ⟨ih1, ih2⟩ := piTelA_bounded_fwd B w hB hw ds (fun d hd => hds d (List.mem_cons_of_mem _ hd))
      obtain ⟨hD, hu⟩ := hds (D, u) (List.mem_cons_self _ _)
      simp only [piTelA, exprLevelsBoundedA, levelBounded, hD, hu, ih1, ih2]
      exact ⟨rfl, rfl⟩

theorem FieldA.BoundedA.lift {F : FieldA} : F.BoundedA k → True := fun _ => trivial

/-- the plain-context substitutions the builders use name variables only. -/
theorem bvarSubst_up {σ : SubstA} (h : ∀ i, exprLevelsBoundedA k (σ i) = true) :
    ∀ i, exprLevelsBoundedA k (σ.up i) = true := fun i => by
  cases i with
  | zero => rfl
  | succ i => rw [SubstA.up_succ, exprLevelsBoundedA_liftA]; exact h i

theorem bvarSubst_shift1 {σ : SubstA} (h : ∀ i, exprLevelsBoundedA k (σ i) = true) :
    ∀ i, exprLevelsBoundedA k (σ.shift1 i) = true := fun i => by
  show exprLevelsBoundedA k (liftA 0 1 (σ i)) = true
  rw [exprLevelsBoundedA_liftA]; exact h i

theorem exprLevelsBoundedA_pi_of {a b : ExprA} {u v : Level} (ha : exprLevelsBoundedA k a = true)
    (hu : levelBounded k u = true) (hb : exprLevelsBoundedA k b = true) (hv : levelBounded k v = true) :
    exprLevelsBoundedA k (.pi a u b v) = true := by
  simp [exprLevelsBoundedA, ha, hu, hb, hv]

theorem levelBounded_imax_of {u v : Level} (hu : levelBounded k u = true) (hv : levelBounded k v = true) :
    levelBounded k (.imax u v) = true := by
  simp [levelBounded, hu, hv]

/-- a function-recursive field's domain is bounded when its inner binders, its indices, the levels,
    the parameter locals and the plain substitution are. -/
theorem frecDomA_bounded_fwd (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA)
    (hls : levelsBounded k ls = true) (hw : levelBounded k w = true)
    (hidx : ∀ x ∈ idx, exprLevelsBoundedA k x = true) :
    (ds : List (ExprA × Level)) → DomsBoundedA k ds → (pl : List ExprA) →
    (∀ x ∈ pl, exprLevelsBoundedA k x = true) → (σ : SubstA) → (∀ i, exprLevelsBoundedA k (σ i) = true) →
    exprLevelsBoundedA k (frecDomA f ls w pl σ ds idx).1 = true ∧
      levelBounded k (frecDomA f ls w pl σ ds idx).2 = true
  | [], _, pl, hpl, σ, hσ => by
      refine ⟨exprLevelsBoundedA_foldAppsA k _ _ hls (fun x hx => ?_), hw⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hpl x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hidx y hy)
  | (D, u) :: ds, hds, pl, hpl, σ, hσ => by
      obtain ⟨hD, hu⟩ := hds (D, u) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := frecDomA_bounded_fwd f ls w idx hls hw hidx ds
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy) σ.up (bvarSubst_up k hσ)
      exact ⟨exprLevelsBoundedA_pi_of k (exprLevelsBoundedA_substA k D σ hσ hD) hu ih1 ih2,
        levelBounded_imax_of k hu ih2⟩

/-- a function-recursive field's induction hypothesis is bounded likewise, with the motive. -/
theorem frecIHA_bounded_fwd (wM : Level) (idx : List ExprA) (m : Nat) (hwM : levelBounded k wM = true)
    (hidx : ∀ x ∈ idx, exprLevelsBoundedA k x = true) :
    (ds : List (ExprA × Level)) → DomsBoundedA k ds → (mot : ExprA) → exprLevelsBoundedA k mot = true →
    (j : Nat) → (σ : SubstA) → (∀ i, exprLevelsBoundedA k (σ i) = true) →
    exprLevelsBoundedA k (frecIHA wM mot j σ ds idx m).1 = true ∧
      levelBounded k (frecIHA wM mot j σ ds idx m).2 = true
  | [], _, mot, hmot, j, σ, hσ => by
      refine ⟨exprLevelsBoundedA_foldAppsA k _ _ hmot (fun x hx => ?_), hwM⟩
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hidx y hy)
      · rcases List.mem_singleton.mp hx with rfl
        exact exprLevelsBoundedA_foldAppsA k _ _ rfl (fun z hz => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
          rfl)
  | (D, u) :: ds, hds, mot, hmot, j, σ, hσ => by
      obtain ⟨hD, hu⟩ := hds (D, u) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := frecIHA_bounded_fwd wM idx m hwM hidx ds
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) (liftA 0 1 mot)
        (by rw [exprLevelsBoundedA_liftA]; exact hmot) (j + 1) σ.up (bvarSubst_up k hσ)
      exact ⟨exprLevelsBoundedA_pi_of k (exprLevelsBoundedA_substA k D σ hσ hD) hu ih1 ih2,
        levelBounded_imax_of k hu ih2⟩

theorem ctorFieldsA_bounded_fwd (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (hls : levelsBounded k ls = true) (hw : levelBounded k w = true)
    (hres : ∀ x ∈ res, exprLevelsBoundedA k x = true) :
    (fs : List FieldA) → (∀ F ∈ fs, F.BoundedA k) → (pl : List ExprA) →
    (∀ x ∈ pl, exprLevelsBoundedA k x = true) → (σ : SubstA) → (∀ i, exprLevelsBoundedA k (σ i) = true) →
    exprLevelsBoundedA k (ctorFieldsA f ls w pl σ fs res).1 = true ∧
      levelBounded k (ctorFieldsA f ls w pl σ fs res).2 = true
  | [], _, pl, hpl, σ, hσ => by
      refine ⟨exprLevelsBoundedA_foldAppsA k _ _ hls (fun x hx => ?_), hw⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hpl x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hres y hy)
  | .plain D u :: fs, hfs, pl, hpl, σ, hσ => by
      obtain ⟨hD, hu⟩ := hfs (.plain D u) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := ctorFieldsA_bounded_fwd f ls w res hls hw hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy) σ.up (bvarSubst_up k hσ)
      simp only [ctorFieldsA, exprLevelsBoundedA, levelBounded, exprLevelsBoundedA_substA k D σ hσ hD, hu, ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .drec idx :: fs, hfs, pl, hpl, σ, hσ => by
      have hidx := hfs (.drec idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := ctorFieldsA_bounded_fwd f ls w res hls hw hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy) σ.shift1 (bvarSubst_shift1 k hσ)
      have hfam : exprLevelsBoundedA k (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) = true :=
        exprLevelsBoundedA_foldAppsA k _ _ hls (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hpl x hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact exprLevelsBoundedA_substA k y σ hσ (hidx y hy))
      simp only [ctorFieldsA, exprLevelsBoundedA, levelBounded, hfam, hw, ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .drecD D idx :: fs, hfs, pl, hpl, σ, hσ => by
      obtain ⟨hD, hidx⟩ := hfs (.drecD D idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := ctorFieldsA_bounded_fwd f ls w res hls hw hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy) σ.shift1 (bvarSubst_shift1 k hσ)
      simp only [ctorFieldsA, exprLevelsBoundedA, levelBounded, exprLevelsBoundedA_substA k D σ hσ hD, hw,
        ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .frec B uB Bs idx :: fs, hfs, pl, hpl, σ, hσ => by
      obtain ⟨hds, hidx⟩ := hfs (.frec B uB Bs idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := ctorFieldsA_bounded_fwd f ls w res hls hw hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy) σ.shift1 (bvarSubst_shift1 k hσ)
      obtain ⟨hd1, hd2⟩ := frecDomA_bounded_fwd k f ls w idx hls hw hidx ((B, uB) :: Bs) hds pl hpl σ hσ
      exact ⟨exprLevelsBoundedA_pi_of k hd1 hd2 ih1 ih2, levelBounded_imax_of k hd2 ih2⟩

theorem ctorTypeA_bounded_fwd (f : Nat) (ls : List Level) (w : Level) (mirrors : List (ExprA × Level))
    (fields : List FieldA) (res : List ExprA) (hls : levelsBounded k ls = true) (hw : levelBounded k w = true)
    (hms : ∀ d ∈ mirrors, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true)
    (hfs : ∀ F ∈ fields, F.BoundedA k) (hres : ∀ x ∈ res, exprLevelsBoundedA k x = true) :
    exprLevelsBoundedA k (ctorTypeA f ls w mirrors fields res) = true := by
  obtain ⟨h1, h2⟩ := ctorFieldsA_bounded_fwd k f ls w res hls hw hres fields hfs
    (paramLocalsA mirrors.length) (paramLocalsA_bounded k _) SubstA.id (fun _ => rfl)
  exact (piTelA_bounded_fwd k _ _ h1 h2 mirrors hms).1

theorem minorFieldsA_bounded_fwd (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (hls : levelsBounded k ls = true) (hwF : levelBounded k wF = true) (hwM : levelBounded k wM = true)
    (hres : ∀ x ∈ res, exprLevelsBoundedA k x = true) :
    (fs : List FieldA) → (∀ F ∈ fs, F.BoundedA k) → (pl : List ExprA) →
    (∀ x ∈ pl, exprLevelsBoundedA k x = true) → (mot : ExprA) → exprLevelsBoundedA k mot = true →
    (fl : List ExprA) → (∀ x ∈ fl, exprLevelsBoundedA k x = true) →
    (σ : SubstA) → (∀ i, exprLevelsBoundedA k (σ i) = true) →
    exprLevelsBoundedA k (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 = true ∧
      levelBounded k (minorFieldsA f c ls wF wM pl mot fl σ fs res).2 = true
  | [], _, pl, hpl, mot, hmot, fl, hfl, σ, hσ => by
      refine ⟨exprLevelsBoundedA_foldAppsA k _ _ hmot (fun x hx => ?_), hwM⟩
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hres y hy)
      · rcases List.mem_singleton.mp hx with rfl
        exact exprLevelsBoundedA_foldAppsA k _ _ hls (fun z hz => by
          rcases List.mem_append.mp hz with hz | hz
          · exact hpl z hz
          · exact hfl z hz)
  | .plain D u :: fs, hfs, pl, hpl, mot, hmot, fl, hfl, σ, hσ => by
      obtain ⟨hD, hu⟩ := hfs (.plain D u) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := minorFieldsA_bounded_fwd f c ls wF wM res hls hwF hwM hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 1))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy)
        (liftA 0 1 mot) (by rw [exprLevelsBoundedA_liftA]; exact hmot)
        (fl.map (liftA 0 1) ++ [.bvar 0])
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hfl y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
        σ.up (bvarSubst_up k hσ)
      simp only [minorFieldsA, exprLevelsBoundedA, levelBounded, exprLevelsBoundedA_substA k D σ hσ hD, hu, ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .drec idx :: fs, hfs, pl, hpl, mot, hmot, fl, hfl, σ, hσ => by
      have hidx := hfs (.drec idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := minorFieldsA_bounded_fwd f c ls wF wM res hls hwF hwM hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 2))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy)
        (liftA 0 2 mot) (by rw [exprLevelsBoundedA_liftA]; exact hmot)
        (fl.map (liftA 0 2) ++ [.bvar 1])
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hfl y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
        σ.shift1.shift1 (bvarSubst_shift1 k (bvarSubst_shift1 k hσ))
      have hsx : ∀ x ∈ idx.map (substA σ), exprLevelsBoundedA k x = true := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hidx y hy)
      have hfam : exprLevelsBoundedA k (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) = true :=
        exprLevelsBoundedA_foldAppsA k _ _ hls (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hpl x hx
          · exact hsx x hx)
      have hih : exprLevelsBoundedA k
          (foldAppsA (liftA 0 1 mot) ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])) = true :=
        exprLevelsBoundedA_foldAppsA k _ _ (by rw [exprLevelsBoundedA_liftA]; exact hmot) (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hsx y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
      simp only [minorFieldsA, exprLevelsBoundedA, levelBounded, hfam, hwF, hih, hwM, ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .drecD D idx :: fs, hfs, pl, hpl, mot, hmot, fl, hfl, σ, hσ => by
      obtain ⟨hD, hidx⟩ := hfs (.drecD D idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := minorFieldsA_bounded_fwd f c ls wF wM res hls hwF hwM hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 2))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy)
        (liftA 0 2 mot) (by rw [exprLevelsBoundedA_liftA]; exact hmot)
        (fl.map (liftA 0 2) ++ [.bvar 1])
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hfl y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
        σ.shift1.shift1 (bvarSubst_shift1 k (bvarSubst_shift1 k hσ))
      have hsx : ∀ x ∈ idx.map (substA σ), exprLevelsBoundedA k x = true := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_substA k y σ hσ (hidx y hy)
      have hfam : exprLevelsBoundedA k (substA σ D) = true := exprLevelsBoundedA_substA k D σ hσ hD
      have hih : exprLevelsBoundedA k
          (foldAppsA (liftA 0 1 mot) ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])) = true :=
        exprLevelsBoundedA_foldAppsA k _ _ (by rw [exprLevelsBoundedA_liftA]; exact hmot) (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hsx y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
      simp only [minorFieldsA, exprLevelsBoundedA, levelBounded, hfam, hwF, hih, hwM, ih1, ih2]
      exact ⟨rfl, rfl⟩
  | .frec B uB Bs idx :: fs, hfs, pl, hpl, mot, hmot, fl, hfl, σ, hσ => by
      obtain ⟨hds, hidx⟩ := hfs (.frec B uB Bs idx) (List.mem_cons_self _ _)
      obtain ⟨ih1, ih2⟩ := minorFieldsA_bounded_fwd f c ls wF wM res hls hwF hwM hres fs
        (fun F hF => hfs F (List.mem_cons_of_mem _ hF)) (pl.map (liftA 0 2))
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [exprLevelsBoundedA_liftA]; exact hpl y hy)
        (liftA 0 2 mot) (by rw [exprLevelsBoundedA_liftA]; exact hmot)
        (fl.map (liftA 0 2) ++ [.bvar 1])
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [exprLevelsBoundedA_liftA]; exact hfl y hy
          · rcases List.mem_singleton.mp hx with rfl; rfl)
        σ.shift1.shift1 (bvarSubst_shift1 k (bvarSubst_shift1 k hσ))
      obtain ⟨hd1, hd2⟩ := frecDomA_bounded_fwd k f ls wF idx hls hwF hidx ((B, uB) :: Bs) hds pl hpl σ hσ
      obtain ⟨hi1, hi2⟩ := frecIHA_bounded_fwd k wM idx (Bs.length + 1) hwM hidx ((B, uB) :: Bs) hds
        (liftA 0 1 mot) (by rw [exprLevelsBoundedA_liftA]; exact hmot) 0 σ.shift1 (bvarSubst_shift1 k hσ)
      exact ⟨exprLevelsBoundedA_pi_of k hd1 hd2 (exprLevelsBoundedA_pi_of k hi1 hi2 ih1 ih2)
          (levelBounded_imax_of k hi2 ih2),
        levelBounded_imax_of k hd2 (levelBounded_imax_of k hi2 ih2)⟩

theorem famLocalsA_bounded (f : Nat) (ls : List Level) (np ni : Nat) (hls : levelsBounded k ls = true) :
    exprLevelsBoundedA k (famLocalsA f ls np ni) = true :=
  exprLevelsBoundedA_foldAppsA k _ _ hls (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [exprLevelsBoundedA_liftA]; exact paramLocalsA_bounded k np y hy
    · exact paramLocalsA_bounded k ni x hx)

theorem liftDomsA_bounded (a : Nat) : (c : Nat) → (ds : List (ExprA × Level)) →
    (∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) →
    ∀ d ∈ liftDomsA c a ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true
  | _, [], _ => fun _ h => absurd h (List.not_mem_nil _)
  | c, (D, u) :: ds, hds => fun d hd => by
      rcases List.mem_cons.mp hd with rfl | hd
      · obtain ⟨hD, hu⟩ := hds (D, u) (List.mem_cons_self _ _)
        exact ⟨by show exprLevelsBoundedA k (liftA c a D) = true; rw [exprLevelsBoundedA_liftA]; exact hD, hu⟩
      · exact liftDomsA_bounded a (c + 1) ds (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd')) d hd

theorem recTypeA_bounded_fwd (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) (hls : levelsBounded k ls = true)
    (hwF : levelBounded k wF = true) (hwM : levelBounded k wM = true)
    (hps : ∀ d ∈ params, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true)
    (his : ∀ d ∈ indices, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true)
    (hcds : ∀ cd ∈ cds, (∀ F ∈ cd.2.1, F.BoundedA k) ∧ ∀ x ∈ cd.2.2, exprLevelsBoundedA k x = true) :
    exprLevelsBoundedA k (recTypeA f ls params indices wF wM cds) = true := by
  have hmot : exprLevelsBoundedA k (motTyA f ls params indices wF wM).1 = true ∧
      levelBounded k (motTyA f ls params indices wF wM).2 = true := by
    apply piTelA_bounded_fwd k _ _ ?_ ?_ indices his
    · simp only [exprLevelsBoundedA, famLocalsA_bounded k f ls _ _ hls, hwF, levelBounded, hwM]; rfl
    · simp only [levelBounded, hwF, hwM]; rfl
  have hminor : ∀ cd ∈ cds, exprLevelsBoundedA k (minorTyA f ls wF wM params.length cd).1 = true ∧
      levelBounded k (minorTyA f ls wF wM params.length cd).2 = true := fun cd hcd =>
    minorFieldsA_bounded_fwd k f cd.1 ls wF wM cd.2.2 hls hwF hwM (hcds cd hcd).2 cd.2.1 (hcds cd hcd).1
      _ (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [exprLevelsBoundedA_liftA]; exact paramLocalsA_bounded k _ y hy)
      (.bvar 0) rfl [] (fun _ h => absurd h (List.not_mem_nil _)) SubstA.id.shift1
      (bvarSubst_shift1 k (fun _ => rfl))
  have hminors : ∀ j, ∀ d ∈ minorDomsA f ls wF wM params.length j cds,
      exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true := by
    intro j
    induction cds generalizing j with
    | nil => intro d hd; exact absurd hd (List.not_mem_nil _)
    | cons cd cds ih =>
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · obtain ⟨h1, h2⟩ := hminor cd (List.mem_cons_self _ _)
          exact ⟨by show exprLevelsBoundedA k (liftA 0 j _) = true; rw [exprLevelsBoundedA_liftA]; exact h1, h2⟩
        · exact ih (fun cd' hcd' => hcds cd' (List.mem_cons_of_mem _ hcd'))
            (fun cd' hcd' => hminor cd' (List.mem_cons_of_mem _ hcd')) (j + 1) d hd
  have hdoms : ∀ d ∈ recDomsA f ls params indices wF wM cds,
      exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true := by
    intro d hd
    simp only [recDomsA, List.mem_append, List.mem_singleton] at hd
    rcases hd with (((hd | rfl) | hd) | hd) | rfl
    · exact hps d hd
    · exact hmot
    · exact hminors 0 d hd
    · exact liftDomsA_bounded k _ 0 indices his d hd
    · exact ⟨by show exprLevelsBoundedA k (liftA _ _ _) = true
                rw [exprLevelsBoundedA_liftA]; exact famLocalsA_bounded k f ls _ _ hls, hwF⟩
  have hbody : exprLevelsBoundedA k (recBodyA indices.length cds.length) = true :=
    exprLevelsBoundedA_foldAppsA k _ _ rfl (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [exprLevelsBoundedA_liftA]; exact paramLocalsA_bounded k _ y hy
      · rcases List.mem_singleton.mp hx with rfl; rfl)
  exact (piTelA_bounded_fwd k _ _ hbody hwM _ hdoms).1

end Bounds

/-! ## (5) the view data between agreeing ι interfaces -/

section Iface
variable {E : ResolvedEnvA} {I J : IotaIfaceA} {n : Nat}

def TelTyA.iface (hag : IfaceAgreeA E I J) : {Γ : LCtxA} → {ds : List (ExprA × Level)} →
    TelTyA E I n Γ ds → TelTyA E J n Γ ds
  | _, _, .nil _ => .nil _
  | _, _, .cons _ _ _ _ hD tl => .cons _ _ _ _ (hasTyIfaceA hag hD) (TelTyA.iface hag tl)

def ArgsTyA.iface (hag : IfaceAgreeA E I J) {Γ : LCtxA} : {T : ExprA} → {as : List ExprA} →
    ArgsTyA E I n Γ T as → ArgsTyA E J n Γ T as
  | _, _, .nil l => .nil l
  | _, _, .cons _ _ _ _ _ _ hx tl => .cons _ _ _ _ _ _ (hasTyIfaceA hag hx) (ArgsTyA.iface hag tl)

def TyConvA.iface (hag : IfaceAgreeA E I J) : {Γ : LCtxA} → {A B : ExprA} →
    TyConvA E I n Γ A B → TyConvA E J n Γ A B
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .of _ _ _ _ _ _ hAl hlu hBl hl'u h =>
      .of _ _ _ _ _ _ (hasTyIfaceA hag hAl) hlu (hasTyIfaceA hag hBl) hl'u (convIfaceA hag h)
  | _, _, _, .trans _ _ _ _ h1 h2 => .trans _ _ _ _ (TyConvA.iface hag h1) (TyConvA.iface hag h2)

def MirrorsConvA.iface (hag : IfaceAgreeA E I J) : {Γ : LCtxA} → {ms ps : List (ExprA × Level)} →
    MirrorsConvA E I n Γ ms ps → MirrorsConvA E J n Γ ms ps
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons _ _ _ _ _ _ _ hc hl tl =>
      .cons _ _ _ _ _ _ _ (TyConvA.iface hag hc) hl (MirrorsConvA.iface hag tl)

def FieldsTyA.iface (hag : IfaceAgreeA E I J) {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I n idxTel Γ k fs res → FieldsTyA E J n idxTel Γ k fs res
  | _, _, _, _, .nil _ _ _ hres => .nil _ _ _ (ArgsTyA.iface hag hres)
  | _, _, _, _, .plain _ _ _ _ _ _ hD tl => .plain _ _ _ _ _ _ (hasTyIfaceA hag hD) (FieldsTyA.iface hag tl)
  | _, _, _, _, .drec _ _ _ _ _ hidx tl => .drec _ _ _ _ _ (ArgsTyA.iface hag hidx) (FieldsTyA.iface hag tl)
  | _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom tl =>
      .frec _ _ _ _ _ _ _ _ (FieldsTyA.iface hag hdom) (FieldsTyA.iface hag tl)
  | _, _, _, _, .drecD _ _ _ _ _ _ hidx tl =>
      .drecD _ _ _ _ _ _ (ArgsTyA.iface hag hidx) (FieldsTyA.iface hag tl)

/-- a constructor view between agreeing interfaces: its data unchanged; the δ evidence rides the
    extended environment's agreement (R-NoDeltaRec-4d-iii). -/
def CtorViewA.iface {f : Nat} {fm cm : CheckedMemberA} {fv : FamViewA fm} (hag : IfaceAgreeA E I J)
    (hag' : IfaceAgreeA (extendEnvA E f fm) I J)
    (v : CtorViewA E I f fm fv cm) : CtorViewA E J f fm fv cm where
  mirrors := v.mirrors
  fields := v.fields
  res := v.res
  stored := v.stored
  mirrorsConv := v.mirrorsConv.iface hag
  typed := v.typed.iface hag
  univ := v.univ
  univI := v.univI
  drecD_typed := fun fsPre D idx fsRest h =>
    match v.drecD_typed fsPre D idx fsRest h with
    | ⟨⟨hd⟩, ⟨hc⟩, hb⟩ => ⟨⟨hasTyIfaceA hag' hd⟩, ⟨convIfaceA hag' hc⟩, hb⟩
  normConv := match v.normConv with | ⟨tc⟩ => ⟨tc.iface hag'⟩
  normTyped := match v.normTyped with | ⟨l, ⟨h⟩⟩ => ⟨l, ⟨hasTyIfaceA hag' h⟩⟩

end Iface

/-! ## (5b) transport into the family extension; the telescope conversion congruence

`CtorCopyA`'s data is typed at the base's own interface; the δ evidence lives in the family's
extended scope. `normConv`/`normTyped` assemble at the copy's interface over the extension, so the
copy's mirror/field/substitution data moves along the `ConstsInA`-conditioned agreement — the moved
derivations never mention the extension's own constant (R-NoDeltaRec-4d-iii). -/

section EnvIface

variable {E₀ E : ResolvedEnvA} {I J : IotaIfaceA} {n : Nat}
variable (hpre : PrefixA E₀ E) (hag : ∀ e, ConstsInA (domA E₀) e → I.fn e = J.fn e)

def substTyA_env_iface {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E₀ I n Δ σ Γ) :
    SubstTyA E J n Δ σ Γ where
  ty := fun i A h => hasTyA_env_iface hpre hag (hσ.ty i A h)
  val := fun i A v hty hval => convA_env_iface hpre hag (hσ.val i A v hty hval)

end EnvIface

section ViewSortUniq
variable {E : ResolvedEnvA} {I J : IotaIfaceA} {n : Nat}

/-- context well-formedness at an agreeing interface (`ctxWfIfaceA` lives in `RcicAnnViewTySem`,
    above this module; the walk is the same). -/
def ctxWfA_iface (hag : IfaceAgreeA E I J) : {Γ : LCtxA} → CtxWfA E I n Γ → CtxWfA E J n Γ
  | _, .nil => .nil
  | _, .assumption hΓ hA => .assumption (ctxWfA_iface hag hΓ) (hasTyIfaceA hag hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (ctxWfA_iface hag hΓ) (hasTyIfaceA hag hA) (hasTyIfaceA hag hv)

/-- sort uniqueness transports across agreeing interfaces: the premises move down by `symm`. -/
theorem viewTySortUniqA_iface (hag : IfaceAgreeA E I J)
    (hu : ViewTySortUniqA E I n) : ViewTySortUniqA E J n :=
  fun hΓ ha hb => hu (ctxWfA_iface hag.symm hΓ) (hasTyIfaceA hag.symm ha) (hasTyIfaceA hag.symm hb)

/-- `piTelA`'s `.2` is the domain sorts' `imax`-fold over the annotation. -/
theorem piTelA_snd (ds : List (ExprA × Level)) (B : ExprA) (w : Level) :
    (piTelA ds B w).2 = ds.foldr (fun d l => .imax d.2 l) w := by
  induction ds with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨D, u⟩ := x
      simp only [piTelA, List.foldr_cons]
      exact congrArg (Level.imax u) ih

/-- `ConvA` folds under a shared telescope: the domains are identical (`refl` per step), the
    inner conversion comes out at the left sort. The right typing follows `viewTy_pi`. -/
def convA_piTelA : {Γ : LCtxA} → {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
    {A B : ExprA} → {s : Level} →
    ConvA E I n (telCtxA ds ++ Γ) A B (.sort s) →
    HasTyA E I n (telCtxA ds ++ Γ) B (.sort s) →
    ConvA E I n Γ (piTelA ds A s).1 (piTelA ds B s).1 (.sort (piTelA ds A s).2)
  | _, _, .nil _, _, _, _, h, _ => h
  | _, _, .cons Γ D u ds hD tl, A, B, s, h, hB => by
      have h' : ConvA E I n (telCtxA ds ++ (.assumption D :: Γ)) A B (.sort s) :=
        telCtxA_cons_append (D, u) ds Γ ▸ h
      have hB' : HasTyA E I n (telCtxA ds ++ (.assumption D :: Γ)) B (.sort s) :=
        telCtxA_cons_append (D, u) ds Γ ▸ hB
      have hih := convA_piTelA tl h' hB'
      have hv : eqN (piTelA ds A s).2 (piTelA ds B s).2 := fun ρ => by simp only [piTelA_snd]
      have hrt : HasTyA E I n Γ (.pi D u (piTelA ds B s).1 (piTelA ds B s).2)
          (.sort (.imax u (piTelA ds A s).2)) :=
        hasTyA_retype_sort (.pi Γ D u _ _ hD (viewTy_pi tl hB'))
          (eqNA_imax_local (eqNA_refl u) (eqNA_symm hv))
      exact ConvA.pi Γ D D _ _ u u _ _ (eqNA_refl u) hv (.refl Γ D (.sort u) hD) hih hrt

end ViewSortUniq

/-! ## (6) the group's annotated views -/

section GroupAnn
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

theorem telCtxA_append_nil (ds : List (ExprA × Level)) : telCtxA ds ++ [] = telCtxA ds :=
  List.append_nil _

/-- the parameter locals carry no levels; instantiation fixes them. -/
theorem paramLocalsA_instLevels (ls : List Level) : (n : Nat) →
    (paramLocalsA n).map (instantiateLevelsA ls) = paramLocalsA n
  | 0 => rfl
  | n + 1 => by
      simp only [paramLocalsA, List.map, instantiateLevelsA, paramLocalsA_instLevels ls n]

/-- a `drecD` split of an instantiated field list unrolls to a split of the source
    (R-NoDeltaRec-4d-iii): position, domain and indices all read off the unclosed side. -/
theorem fieldA_map_instLevels_split {fsA : List FieldA} {ls : List Level}
    {fsPre : List FieldA} {D : ExprA} {idx : List ExprA} {fsRest : List FieldA}
    (h : fsA.map (FieldA.instLevels ls) = fsPre ++ .drecD D idx :: fsRest) :
    ∃ fsPreA D₀ idx₀ fsRestA, fsA = fsPreA ++ .drecD D₀ idx₀ :: fsRestA ∧
      fsPre = fsPreA.map (FieldA.instLevels ls) ∧ D = instantiateLevelsA ls D₀ ∧
      idx = idx₀.map (instantiateLevelsA ls) ∧ fsRest = fsRestA.map (FieldA.instLevels ls) := by
  have hle : fsPre.length ≤ fsA.length := by
    have h1 := congrArg List.length h
    simp only [List.length_map, List.length_append, List.length_cons] at h1
    omega
  have hcut : fsA.take fsPre.length ++ fsA.drop fsPre.length = fsA :=
    List.take_append_drop fsPre.length fsA
  conv at h =>
    rw [← hcut, List.map_append]
  have htk : ((fsA.take fsPre.length).map (FieldA.instLevels ls)).length = fsPre.length := by
    simp only [List.length_map, List.length_take, Nat.min_eq_left hle]
  obtain ⟨hpre, hdr⟩ := List.append_inj h htk
  obtain ⟨x, xs, hxs⟩ : ∃ x xs, fsA.drop fsPre.length = x :: xs := by
    cases hdr' : fsA.drop fsPre.length with
    | nil => rw [hdr'] at hdr; simp only [List.map_nil] at hdr; cases hdr
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [hxs, List.map_cons] at hdr
  obtain ⟨hxeq, hres⟩ := List.cons.inj hdr
  cases x with
  | plain D₀ u₀ => simp only [FieldA.instLevels] at hxeq; cases hxeq
  | drec idx₀ => simp only [FieldA.instLevels] at hxeq; cases hxeq
  | frec B₀ u₀ Bs₀ idx₀ => simp only [FieldA.instLevels] at hxeq; cases hxeq
  | drecD D₀ idx₀ =>
      simp only [FieldA.instLevels, FieldA.drecD.injEq] at hxeq
      obtain ⟨hD, hidx⟩ := hxeq
      refine ⟨fsA.take fsPre.length, D₀, idx₀, xs, ?_, hpre.symm, hD.symm, hidx.symm, hres.symm⟩
      exact hcut.symm.trans (by rw [hxs])

/-- the family's canonical parameters are fixed by the closing list (R-NoDeltaRec-4d-iii). -/
theorem instantiateLevelsA_closeLs_canon (a M n : Nat) (h : n ≤ a) :
    (canonLevelsA n).map (instLevel (closeLs a M)) = canonLevelsA n := by
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro l hl
  simp only [canonLevelsA, List.mem_map] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  have hia : i < a := Nat.lt_of_lt_of_le (List.mem_range.mp hi) h
  rw [instLevel_param, closeLs_get_lt hia]
  rfl

/-- a longer closing list's `a + M` prefix is the shorter one. -/
theorem closeLs_take (a M M' : Nat) (h : M ≤ M') : (closeLs a M').take (a + M) = closeLs a M := by
  simp only [closeLs]
  rw [List.take_append_eq_append_take]
  have hlen : (canonLevelsA a).length = a := by
    simp only [canonLevelsA, List.length_map, List.length_range]
  rw [List.take_of_length_le (by rw [hlen]; omega), hlen]
  rw [show a + M - a = M from by omega, List.take_replicate, Nat.min_eq_left h]

/-- domain lists bounded below `a + M` instantiate the same at any longer closing list —
    the closed telescope's `CtorCopyA` side is `Mf`-closed while the fields close at `Mc`
    (R-NoDeltaRec-4d-iii). -/
theorem instDomsA_closeLs_take {a M M' : Nat} (hM : M ≤ M') {ds : List (ExprA × Level)}
    (hb : DomsBoundedA (a + M) ds) :
    instDomsA (closeLs a M') ds = instDomsA (closeLs a M) ds := by
  apply List.map_congr_left
  intro d hd
  obtain ⟨h1, h2⟩ := hb d hd
  show (instantiateLevelsA (closeLs a M') d.1, instLevel (closeLs a M') d.2) =
      (instantiateLevelsA (closeLs a M) d.1, instLevel (closeLs a M) d.2)
  rw [instantiateLevelsA_take _ _ _ h1, instLevel_take _ _ _ h2, closeLs_take a M M' hM]

/-- main's telescope's domains bounded, from the telescope's bound. -/
theorem exprLevelsBounded_policyPi (k : Nat) : (ds : List (Expr Nat)) → (B : Expr Nat) →
    exprLevelsBounded k (policyPi ds B) = true →
    (∀ D ∈ ds, exprLevelsBounded k D = true) ∧ exprLevelsBounded k B = true
  | [], _, h => ⟨fun _ hD => absurd hD (List.not_mem_nil _), h⟩
  | D :: ds, B, h => by
      simp only [policyPi, exprLevelsBounded, Bool.and_eq_true] at h
      obtain ⟨ih1, ih2⟩ := exprLevelsBounded_policyPi k ds B h.2
      exact ⟨fun D' hD' => by
        rcases List.mem_cons.mp hD' with rfl | hD'
        · exact h.1
        · exact ih1 D' hD', ih2⟩

/-- THE FAMILY, ANNOTATED: its telescope typed on the copy at its recorded levels, the parameters
    and the indices erasing to the view's. -/
theorem famAnn (C : AnnEnvA E) (hn : EnvNormEraseA E) {fm : CheckedMember} {fv : FamViewT fm}
    (htel : TelTyT (eraseEnv E) fm.arity [] (fv.params ++ fv.indices)) :
    ∃ pA iA : List (ExprA × Level), pA.map eraseDom = fv.params ∧ iA.map eraseDom = fv.indices ∧
      Nonempty (TelTyA E (iotaIfaceA E) fm.arity [] (pA ++ iA)) := by
  obtain ⟨dsA, hdse, ⟨tel⟩⟩ := annTelTyT C hn htel CtxWfA.nil rfl
  refine ⟨dsA.take fv.params.length, dsA.drop fv.params.length, ?_, ?_, ?_⟩
  · rw [List.map_take, hdse, List.take_left' rfl]
  · rw [List.map_drop, hdse, List.drop_left' rfl]
  · rw [List.take_append_drop]; exact ⟨tel⟩

/-- A CONSTRUCTOR, ANNOTATED against the family's annotated telescope: its mirrors and its fields in
    the plain context, erasing to the view's. -/
theorem ctorAnn (C : AnnEnvA E) (hn : EnvNormEraseA E) {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    {pA iA : List (ExprA × Level)} (hpe : pA.map eraseDom = fv.params) (hie : iA.map eraseDom = fv.indices)
    (htel : TelTyA E (iotaIfaceA E) fm.arity [] (pA ++ iA)) (c : GroupCtorT (eraseEnv E) f fm fv)
    {fmA : CheckedMemberA} (hme : eraseMember fmA = fm) (hfr : E.members f = none)
    (C' : AnnEnvA (extendEnvA E f fmA)) (hn' : EnvNormEraseA (extendEnvA E f fmA))
    (hpreA : PrefixA E (extendEnvA E f fmA))
    (hm : fmA.mtypeA = (piTelA (pA ++ iA) (.sort fv.sort) (.succ fv.sort)).1)
    (ha : fmA.arity = fm.arity) :
    ∃ (msA : List (ExprA × Level)) (fsA : List FieldA) (resA : List ExprA),
      msA.map eraseDom = c.view.mirrors ∧ fsA.map FieldA.erase = c.view.fields ∧
      resA.map erase = c.view.res ∧ Nonempty (MirrorsConvA E (iotaIfaceA E) fm.arity [] msA pA) ∧
      Nonempty (FieldsTyA E (iotaIfaceA E) fm.arity
        (fun k => liftA 0 k (piTelA iA (.sort fv.sort) (.succ fv.sort)).1) (telCtxA pA) 0 fsA resA) ∧
      (∀ x ∈ fsA, x.NoFun) ∧
      drecDSplitA (fun fsPre DA idxA =>
        Nonempty (HasTyA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) fm.arity
          (plainCtxA fsPre (telCtxA pA)) DA (.sort fv.sort)) ∧
        Nonempty (ConvA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) fm.arity
          (plainCtxA fsPre (telCtxA pA)) DA
          (foldAppsA (.const f (canonLevelsA fm.arity))
            ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idxA))
          (.sort fv.sort)) ∧
        ∀ x ∈ idxA, exprLevelsBounded fm.arity (erase x) = true) [] fsA := by
  let tp := (TelTyA.split pA htel).1
  let ti := (TelTyA.split pA htel).2
  have hΓp : CtxWfA E (iotaIfaceA E) fm.arity (telCtxA pA) :=
    telCtxA_append_nil pA ▸ ctxWfA_telCtx tp CtxWfA.nil
  have hctxp : eraseCtx (telCtxA pA) = telCtxT fv.params := by rw [eraseCtx_telCtxA, hpe]
  obtain ⟨msA, hmse, ⟨mc⟩⟩ := annMirrorsConvT C hn c.view.mirrorsConv CtxWfA.nil rfl hpe tp
  have ti' : TelTyA E (iotaIfaceA E) fm.arity (telCtxA pA) iA := telCtxA_append_nil pA ▸ ti
  have hX : HasTyA E (iotaIfaceA E) fm.arity (telCtxA pA) (liftA 0 0 (piTelA iA (.sort fv.sort) (.succ fv.sort)).1)
      (.sort (piTelA iA (.sort fv.sort) (.succ fv.sort)).2) := by
    rw [liftA_zero]; exact hasTyA_piTelA ti' (.sort _ fv.sort)
  have hXe : erase (piTelA iA (.sort fv.sort) (.succ fv.sort)).1 = fv.idxTel := by
    rw [erase_piTelA, FamViewT.idxTel, ← hie, List.map_map]; rfl
  have typed := c.view.typed
  rw [show (fun k => lift 0 k fv.idxTel) = (fun k => lift 0 k (erase (piTelA iA (.sort fv.sort) (.succ fv.sort)).1))
    by rw [hXe]] at typed
  rw [← hctxp] at typed
  obtain ⟨fsA, resA, hfse, hrese, ⟨ft⟩, hnf, hsp⟩ :=
    annFieldsTyT C hn _ hme hfr C' hn' hpreA
      (fun fsPre D idx fsRest h => (c.view.drecD_typed fsPre D idx fsRest h))
      pA iA (telCtxA pA) rfl hctxp rfl hm ha htel
        (by rw [← List.length_map, hpe])
      [] [] rfl typed rfl hctxp rfl rfl hΓp rfl hX
  exact ⟨msA, fsA, resA, hmse, hfse, hrese, ⟨mc⟩, ⟨ft⟩, hnf, hsp⟩

end GroupAnn

/-! ## (7) main's views bounded at the family's arity; closing keeps erasures

`main`'s member types are bounded at their arity, so every part of a view is. Closing an annotation
of a bounded part leaves its erasure. Main's minor and recursor builders read the recorded levels
nowhere, so the closed views erase to the same built types. -/

section MainBounds

theorem exprLevelsBounded_substT_rev (k : Nat) : (e : Expr Nat) → (σ : SubstT) →
    exprLevelsBounded k (substT σ e) = true → exprLevelsBounded k e = true
  | .bvar _, _, _ => rfl
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .app f x, σ, h => by
      simp only [substT, exprLevelsBounded] at h ⊢
      rw [exprLevelsBounded_substT_rev k f σ (boolAnd_left h), exprLevelsBounded_substT_rev k x σ (boolAnd_right h)]
      rfl
  | .lam x b, σ, h => by
      simp only [substT, exprLevelsBounded] at h ⊢
      rw [exprLevelsBounded_substT_rev k x σ (boolAnd_left h), exprLevelsBounded_substT_rev k b σ.up (boolAnd_right h)]
      rfl
  | .pi x b, σ, h => by
      simp only [substT, exprLevelsBounded] at h ⊢
      rw [exprLevelsBounded_substT_rev k x σ (boolAnd_left h), exprLevelsBounded_substT_rev k b σ.up (boolAnd_right h)]
      rfl
  | .letE x w b, σ, h => by
      simp only [substT, exprLevelsBounded] at h ⊢
      rw [exprLevelsBounded_substT_rev k x σ (boolAnd_left (boolAnd_left h)),
        exprLevelsBounded_substT_rev k w σ (boolAnd_right (boolAnd_left h)),
        exprLevelsBounded_substT_rev k b σ.up (boolAnd_right h)]
      rfl
  | .lit _, _, _ => rfl

theorem exprLevelsBounded_foldApps_rev (k : Nat) : (h : Expr Nat) → (xs : List (Expr Nat)) →
    exprLevelsBounded k (foldApps h xs) = true →
    exprLevelsBounded k h = true ∧ ∀ x ∈ xs, exprLevelsBounded k x = true
  | _, [], hb => ⟨hb, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | h, x :: xs, hb => by
      obtain ⟨hhx, hxs⟩ := exprLevelsBounded_foldApps_rev k (.app h x) xs hb
      simp only [exprLevelsBounded] at hhx
      refine ⟨boolAnd_left hhx, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact boolAnd_right hhx
      · exact hxs y hy

/-- a main field's terms bounded at `k`: a δ-reached field's surface domain AND its indices — the
    indices do not occur in the constructor's type, so the reversal below stays in the
    `drecD`-free scope (`hnd`, R-NoDeltaRec-4a); the field's own close/erase laws still see them. -/
def _root_.Rcic.Declarative.FieldT.Bounded (k : Nat) : FieldT → Prop
  | .plain D _ => exprLevelsBounded k D = true
  | .drec idx => ∀ x ∈ idx, exprLevelsBounded k x = true
  | .drecD D idx => exprLevelsBounded k D = true ∧ ∀ x ∈ idx, exprLevelsBounded k x = true

theorem ctorFieldsT_bounded_rev (k f : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) →
    (∀ D idx, FieldT.drecD D idx ∈ fs → ∀ x ∈ idx, exprLevelsBounded k x = true) →
    (pl : List (Expr Nat)) → (σ : SubstT) →
    exprLevelsBounded k (ctorFieldsT f ls pl σ fs res) = true →
    (∀ F ∈ fs, F.Bounded k) ∧ ∀ x ∈ res, exprLevelsBounded k x = true
  | [], _, pl, σ, hb => by
      obtain ⟨_, hxs⟩ := exprLevelsBounded_foldApps_rev k _ _ hb
      exact ⟨fun _ h => absurd h (List.not_mem_nil _), fun x hx =>
        exprLevelsBounded_substT_rev k x σ (hxs _ (List.mem_append_right _ (List.mem_map_of_mem _ hx)))⟩
  | .plain D u :: fs, hix, pl, σ, hb => by
      simp only [ctorFieldsT, exprLevelsBounded] at hb
      obtain ⟨ih1, ih2⟩ := ctorFieldsT_bounded_rev k f ls res fs
        (fun D idx hd => hix D idx (List.mem_cons_of_mem _ hd)) _ _ (boolAnd_right hb)
      refine ⟨fun F hF => ?_, ih2⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · exact exprLevelsBounded_substT_rev k D σ (boolAnd_left hb)
      · exact ih1 F hF
  | .drec idx :: fs, hix, pl, σ, hb => by
      simp only [ctorFieldsT, exprLevelsBounded] at hb
      obtain ⟨ih1, ih2⟩ := ctorFieldsT_bounded_rev k f ls res fs
        (fun D idx hd => hix D idx (List.mem_cons_of_mem _ hd)) _ _ (boolAnd_right hb)
      refine ⟨fun F hF => ?_, ih2⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · intro x hx
        obtain ⟨_, hxs⟩ := exprLevelsBounded_foldApps_rev k _ _ (boolAnd_left hb)
        exact exprLevelsBounded_substT_rev k x σ (hxs _ (List.mem_append_right _ (List.mem_map_of_mem _ hx)))
      · exact ih1 F hF
  | .drecD D idx :: fs, hix, pl, σ, hb => by
      simp only [ctorFieldsT, exprLevelsBounded] at hb
      obtain ⟨ih1, ih2⟩ := ctorFieldsT_bounded_rev k f ls res fs
        (fun D₀ idx₀ hd => hix D₀ idx₀ (List.mem_cons_of_mem _ hd)) _ _ (boolAnd_right hb)
      refine ⟨fun F hF => ?_, ih2⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨exprLevelsBounded_substT_rev k D σ (boolAnd_left hb),
          hix D idx (List.mem_cons_self _ _)⟩
      · exact ih1 F hF

theorem ctorTypeT_bounded_rev (k f : Nat) (ls : List Level) (mirrors : List (Expr Nat × Level))
    (fields : List FieldT) (res : List (Expr Nat))
    (hix : ∀ D idx, FieldT.drecD D idx ∈ fields → ∀ x ∈ idx, exprLevelsBounded k x = true)
    (h : exprLevelsBounded k (ctorTypeT f ls mirrors fields res) = true) :
    (∀ d ∈ mirrors, exprLevelsBounded k d.1 = true) ∧ (∀ F ∈ fields, F.Bounded k) ∧
      ∀ x ∈ res, exprLevelsBounded k x = true := by
  obtain ⟨h1, h2⟩ := exprLevelsBounded_policyPi k _ _ h
  obtain ⟨h3, h4⟩ := ctorFieldsT_bounded_rev k f ls res fields hix _ _ h2
  exact ⟨fun d hd => h1 d.1 (List.mem_map_of_mem _ hd), h3, h4⟩

/-- the recorded levels play no part in main's minor premises. -/
def _root_.Rcic.Declarative.FieldT.unlevel : FieldT → FieldT
  | .plain D _ => .plain D .zero
  | .drec idx => .drec idx
  | .drecD D idx => .drecD D idx

theorem minorFieldsT_unlevel (f c : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (mot : Expr Nat) → (fl : List (Expr Nat)) →
    (σ : SubstT) →
    minorFieldsT f c ls pl mot fl σ (fs.map FieldT.unlevel) res = minorFieldsT f c ls pl mot fl σ fs res
  | [], _, _, _, _ => rfl
  | .plain D u :: fs, pl, mot, fl, σ => by
      simp only [List.map_cons, FieldT.unlevel, minorFieldsT, minorFieldsT_unlevel f c ls res fs]
  | .drec idx :: fs, pl, mot, fl, σ => by
      simp only [List.map_cons, FieldT.unlevel, minorFieldsT, minorFieldsT_unlevel f c ls res fs]
  | .drecD D idx :: fs, pl, mot, fl, σ => by
      simp only [List.map_cons, FieldT.unlevel, minorFieldsT, minorFieldsT_unlevel f c ls res fs]

theorem recTypeT_congr (f : Nat) (ls : List Level) {params params' indices indices' : List (Expr Nat × Level)}
    (wM : Level) {cds cds' : List MinorDataT} (hp : params.map Prod.fst = params'.map Prod.fst)
    (hi : indices.map Prod.fst = indices'.map Prod.fst)
    (hc : cds.map (fun cd => (cd.1, cd.2.1.map FieldT.unlevel, cd.2.2)) =
      cds'.map (fun cd => (cd.1, cd.2.1.map FieldT.unlevel, cd.2.2))) :
    recTypeT f ls params indices wM cds = recTypeT f ls params' indices' wM cds' := by
  have hpl : params.length = params'.length := by
    rw [← List.length_map params Prod.fst, hp, List.length_map]
  have hil : indices.length = indices'.length := by
    rw [← List.length_map indices Prod.fst, hi, List.length_map]
  have hcl : cds.length = cds'.length := by
    rw [← List.length_map cds (fun cd => (cd.1, cd.2.1.map FieldT.unlevel, cd.2.2)), hc, List.length_map]
  have hmin : ∀ (j : Nat), minorDomsT f ls params.length j cds = minorDomsT f ls params'.length j cds' := by
    rw [hpl]
    induction cds generalizing cds' with
    | nil =>
        cases cds' with
        | nil => intro j; rfl
        | cons _ _ => exact absurd hc (by simp)
    | cons cd cds ih =>
        cases cds' with
        | nil => exact absurd hc (by simp)
        | cons cd' cds' =>
            simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hc
            obtain ⟨⟨h1, h2, h3⟩, hrest⟩ := hc
            intro j
            simp only [minorDomsT, minorTyT]
            rw [← minorFieldsT_unlevel f cd.1 ls cd.2.2 cd.2.1, h2, h1, h3, minorFieldsT_unlevel,
              ih hrest (by simpa using congrArg List.length hrest)]
  simp only [recTypeT, recDomsT]
  rw [hmin 0]
  simp only [motTyT, hp, hi, hpl, hil, hcl]

end MainBounds

/-! ## (8) closing a constructor's annotated view -/

section CloseCtor

def exprsBoundA (xs : List ExprA) : Nat := xs.foldr (fun x m => max (lvlBoundA x) m) 0

/-- a bound for a field list. -/
def fieldsBoundA : List FieldA → Nat
  | [] => 0
  | .plain D u :: fs => max (max (lvlBoundA D) (lvlBound u)) (fieldsBoundA fs)
  | .drec idx :: fs => max (exprsBoundA idx) (fieldsBoundA fs)
  | .drecD D idx :: fs => max (max (lvlBoundA D) (exprsBoundA idx)) (fieldsBoundA fs)
  | .frec B uB Bs idx :: fs => max (max (domsBoundA ((B, uB) :: Bs)) (exprsBoundA idx)) (fieldsBoundA fs)

theorem exprsBoundA_bounded : (xs : List ExprA) → ∀ x ∈ xs, exprLevelsBoundedA (exprsBoundA xs) x = true
  | [] => fun _ h => absurd h (List.not_mem_nil _)
  | y :: ys => fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact exprLevelsBoundedA_mono (Nat.le_max_left _ _) _ (exprLevelsBoundedA_lvlBoundA _)
      · exact exprLevelsBoundedA_mono (Nat.le_max_right _ _) _ (exprsBoundA_bounded ys x hx)

theorem FieldA.BoundedA.mono {j k : Nat} (h : j ≤ k) : {F : FieldA} → F.BoundedA j → F.BoundedA k
  | .plain _ _, hF => ⟨exprLevelsBoundedA_mono h _ hF.1, levelBounded_mono h _ hF.2⟩
  | .drec _, hF => fun x hx => exprLevelsBoundedA_mono h _ (hF x hx)
  | .frec _ _ _ _, hF => ⟨domsBoundedA_mono h hF.1, fun x hx => exprLevelsBoundedA_mono h _ (hF.2 x hx)⟩
  | .drecD _ _, hF => ⟨exprLevelsBoundedA_mono h _ hF.1, fun x hx => exprLevelsBoundedA_mono h _ (hF.2 x hx)⟩

theorem fieldsBoundA_bounded : (fs : List FieldA) → ∀ F ∈ fs, F.BoundedA (fieldsBoundA fs)
  | [] => fun _ h => absurd h (List.not_mem_nil _)
  | .plain D u :: fs => fun F hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨exprLevelsBoundedA_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) _
            (exprLevelsBoundedA_lvlBoundA _),
          levelBounded_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) _
            (levelBounded_lvlBound _)⟩
      · exact FieldA.BoundedA.mono (Nat.le_max_right _ _) (fieldsBoundA_bounded fs F hF)
  | .drec idx :: fs => fun F hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact fun x hx => exprLevelsBoundedA_mono (Nat.le_max_left _ _) _ (exprsBoundA_bounded idx x hx)
      · exact FieldA.BoundedA.mono (Nat.le_max_right _ _) (fieldsBoundA_bounded fs F hF)
  | .drecD D idx :: fs => fun F hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨exprLevelsBoundedA_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) _
            (exprLevelsBoundedA_lvlBoundA _),
          fun x hx => exprLevelsBoundedA_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) _
            (exprsBoundA_bounded idx x hx)⟩
      · exact FieldA.BoundedA.mono (Nat.le_max_right _ _) (fieldsBoundA_bounded fs F hF)
  | .frec B uB Bs idx :: fs => fun F hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨domsBoundedA_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (domsBoundedA_domsBoundA _),
          fun x hx => exprLevelsBoundedA_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) _
            (exprsBoundA_bounded idx x hx)⟩
      · exact FieldA.BoundedA.mono (Nat.le_max_right _ _) (fieldsBoundA_bounded fs F hF)

theorem FieldA.BoundedA.close {a M : Nat} : {F : FieldA} → F.BoundedA (a + M) →
    (F.instLevels (closeLs a M)).BoundedA a
  | .plain _ _, hF => ⟨exprLevelsBoundedA_inst_closeLs _ hF.1, levelBounded_inst_closeLs _ hF.2⟩
  | .drec _, hF => fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact exprLevelsBoundedA_inst_closeLs _ (hF y hy)
  | .frec _ _ _ _, hF => ⟨domsBoundedA_close hF.1, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact exprLevelsBoundedA_inst_closeLs _ (hF.2 y hy)⟩
  | .drecD _ _, hF => ⟨exprLevelsBoundedA_inst_closeLs _ hF.1, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact exprLevelsBoundedA_inst_closeLs _ (hF.2 y hy)⟩

/-- closing an annotation of a bounded part leaves its erasure. -/
theorem erase_close_of_bounded {a M : Nat} {e : ExprA} (h : exprLevelsBounded a (erase e) = true) :
    erase (instantiateLevelsA (closeLs a M) e) = erase e := by
  rw [erase_instantiateLevelsA, instantiateLevels_closeLs _ h]

theorem FieldA.erase_close_unlevel {a M : Nat} : (F : FieldA) → (F.erase).Bounded a →
    ((F.instLevels (closeLs a M)).erase).unlevel = F.erase.unlevel
  | .plain D u, h => by
      simp only [FieldA.instLevels, FieldA.erase, FieldT.unlevel]
      rw [erase_close_of_bounded h]
  | .drec idx, h | .frec _ _ _ idx, h => by
      simp only [FieldA.instLevels, FieldA.erase, FieldT.unlevel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact erase_close_of_bounded (h _ (List.mem_map_of_mem _ hx))
  | .drecD D idx, h => by
      simp only [FieldA.instLevels, FieldA.erase, FieldT.unlevel, List.map_map]
      rw [erase_close_of_bounded h.1]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact erase_close_of_bounded (h.2 _ (List.mem_map_of_mem _ hx))

theorem domsBoundedA_append {k : Nat} {xs ys : List (ExprA × Level)} (h : DomsBoundedA k (xs ++ ys)) :
    DomsBoundedA k xs ∧ DomsBoundedA k ys :=
  ⟨fun d hd => h d (List.mem_append_left _ hd), fun d hd => h d (List.mem_append_right _ hd)⟩

/-- the family's index telescope, closed: the closed indices under the (bounded) sort. -/
theorem inst_piTelA_sort_closeLs {a M : Nat} {s : Level} (hs : levelBounded a s = true)
    (ds : List (ExprA × Level)) :
    instantiateLevelsA (closeLs a M) (piTelA ds (.sort s) (.succ s)).1 =
      (piTelA (instDomsA (closeLs a M) ds) (.sort s) (.succ s)).1 := by
  have h := congrArg Prod.fst (instantiateLevelsA_piTelA (closeLs a M) (.sort s) (.succ s) ds)
  simp only at h
  rw [h]
  have hs' : instLevel (closeLs a M) s = s := instLevel_closeLs_of_bounded s hs
  have hs'' : instLevel (closeLs a M) (.succ s) = .succ s := by
    show Level.succ (instLevel (closeLs a M) s) = _
    rw [hs']
  simp only [instantiateLevelsA, hs', hs'']

/-- an annotation's level bound descends to its erasure (the binder levels drop with it). -/
theorem exprLevelsBounded_of_A {k : Nat} : (e : ExprA) →
    exprLevelsBoundedA k e = true → exprLevelsBounded k (erase e) = true
  | .bvar _, _ => rfl
  | .sort _, h => h
  | .const _ _, h => h
  | .lit _, _ => rfl
  | .app f x, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [erase, exprLevelsBounded, Bool.and_eq_true]
      exact ⟨exprLevelsBounded_of_A f h.1, exprLevelsBounded_of_A x h.2⟩
  | .lam a u b, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [erase, exprLevelsBounded, Bool.and_eq_true]
      exact ⟨exprLevelsBounded_of_A a h.1.1, exprLevelsBounded_of_A b h.2⟩
  | .pi a u b v, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [erase, exprLevelsBounded, Bool.and_eq_true]
      exact ⟨exprLevelsBounded_of_A a h.1.1.1, exprLevelsBounded_of_A b h.1.2⟩
  | .letE a w b, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [erase, exprLevelsBounded, Bool.and_eq_true]
      exact ⟨⟨exprLevelsBounded_of_A a h.1.1, exprLevelsBounded_of_A w h.1.2⟩,
        exprLevelsBounded_of_A b h.2⟩

/-- closing a bounded telescope leaves its domain-pair erasures (R-NoDeltaRec-4d-ii). -/
theorem instDomsA_map_eraseDom {a M : Nat} {ds : List (ExprA × Level)}
    (hb1 : ∀ d ∈ ds, exprLevelsBounded a (erase d.1) = true)
    (hb2 : ∀ d ∈ ds, levelBounded a d.2 = true) :
    (instDomsA (closeLs a M) ds).map eraseDom = ds.map eraseDom := by
  simp only [instDomsA, List.map_map]
  apply List.map_congr_left
  intro d hd
  show (erase (instantiateLevelsA _ d.1), instLevel _ d.2) = (erase d.1, d.2)
  rw [erase_close_of_bounded (hb1 d hd), instLevel_closeLs_of_bounded d.2 (hb2 d hd)]

/-- on the copy's syntax, a term within the family's arity is fixed by the closing list. -/
theorem instantiateLevelsA_closeLs_of_bounded {a M : Nat} : (e : ExprA) →
    exprLevelsBoundedA a e = true → instantiateLevelsA (closeLs a M) e = e
  | .bvar _, _ => rfl
  | .sort l, h => by simp only [instantiateLevelsA, instLevel_closeLs_of_bounded l h]
  | .const r ms, h => by
      simp only [instantiateLevelsA]
      congr 1
      induction ms with
      | nil => rfl
      | cons l t ih =>
          simp only [exprLevelsBoundedA, levelsBounded, Bool.and_eq_true] at h
          simp only [List.map_cons, instLevel_closeLs_of_bounded l h.1, ih h.2]
  | .app f x, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [instantiateLevelsA, instantiateLevelsA_closeLs_of_bounded f h.1,
        instantiateLevelsA_closeLs_of_bounded x h.2]
  | .lam x u b, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [instantiateLevelsA, instantiateLevelsA_closeLs_of_bounded x h.1.1,
        instLevel_closeLs_of_bounded u h.1.2, instantiateLevelsA_closeLs_of_bounded b h.2]
  | .pi x u b v, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [instantiateLevelsA, instantiateLevelsA_closeLs_of_bounded x h.1.1.1,
        instLevel_closeLs_of_bounded u h.1.1.2, instantiateLevelsA_closeLs_of_bounded b h.1.2,
        instLevel_closeLs_of_bounded v h.2]
  | .letE x w b, h => by
      simp only [exprLevelsBoundedA, Bool.and_eq_true] at h
      simp only [instantiateLevelsA, instantiateLevelsA_closeLs_of_bounded x h.1.1,
        instantiateLevelsA_closeLs_of_bounded w h.1.2,
        instantiateLevelsA_closeLs_of_bounded b h.2]
  | .lit _, _ => rfl


/-- an already-closed telescope domain-pair is fixed by a second closing (`instDomsA_map_eraseDom`'s
    identity companion, R-NoDeltaRec-4d-iii). -/
theorem instDomsA_closeLs_of_bounded {a M : Nat} {ds : List (ExprA × Level)}
    (hb : DomsBoundedA a ds) : instDomsA (closeLs a M) ds = ds := by
  simp only [instDomsA]
  induction ds with
  | nil => rfl
  | cons d t iht =>
      obtain ⟨h1, h2⟩ := hb d (List.mem_cons_self _ _)
      obtain ⟨e, u⟩ := d
      rw [List.map_cons]
      rw [show (instantiateLevelsA (closeLs a M) e, instLevel (closeLs a M) u) = (e, u) from
        Prod.ext (instantiateLevelsA_closeLs_of_bounded e h1) (instLevel_closeLs_of_bounded u h2),
        iht (fun x hx => hb x (List.mem_cons_of_mem _ hx))]

/-- the copy's family member: its type built from the views, its parameter count the view's. -/
def famMemberA (a : Nat) (pA iA : List (ExprA × Level)) (s : Level) : CheckedMemberA :=
  ⟨.inductiveM, a, (piTelA (pA ++ iA) (.sort s) (.succ s)).1, none, pA.length, none⟩

/-- A CONSTRUCTOR'S VIEW, ANNOTATED AND CLOSED against the family's closed telescope. -/
theorem ctorClosed {E : ResolvedEnvA} (C : AnnEnvA E) (hn : EnvNormEraseA E) {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (hs : levelBounded fm.arity fv.sort = true) {pA iA : List (ExprA × Level)}
    (hpe : pA.map eraseDom = fv.params) (hie : iA.map eraseDom = fv.indices)
    (htel : TelTyA E (iotaIfaceA E) fm.arity [] (pA ++ iA)) {Mf : Nat}
    (hbf : DomsBoundedA (fm.arity + Mf) (pA ++ iA))
    (hpl : ∀ d ∈ pA, levelBounded fm.arity d.2 = true)
    (hil : ∀ d ∈ iA, levelBounded fm.arity d.2 = true)
    (hparts : ∀ d ∈ (fv.params ++ fv.indices).map Prod.fst,
      exprLevelsBounded fm.arity d = true)
    (c : GroupCtorT (eraseEnv E) f fm fv)
    {fmA : CheckedMemberA} (hme : eraseMember fmA = fm) (hfr : E.members f = none)
    (C' : AnnEnvA (extendEnvA E f fmA)) (hpreA : PrefixA E (extendEnvA E f fmA))
    (hm : fmA.mtypeA = (piTelA (instDomsA (closeLs fm.arity Mf) pA ++
        instDomsA (closeLs fm.arity Mf) iA) (.sort fv.sort) (.succ fv.sort)).1)
    (ha : fmA.arity = fm.arity)
    (hfme : fmA = famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
        (instDomsA (closeLs fm.arity Mf) iA) fv.sort) :
    ∃ (ms : List (ExprA × Level)) (fs : List FieldA) (res : List ExprA),
      Nonempty (MirrorsConvA E (iotaIfaceA E) fm.arity [] ms (instDomsA (closeLs fm.arity Mf) pA)) ∧
      Nonempty (FieldsTyA E (iotaIfaceA E) fm.arity
        (fun k => liftA 0 k (piTelA (instDomsA (closeLs fm.arity Mf) iA) (.sort fv.sort) (.succ fv.sort)).1)
        (telCtxA (instDomsA (closeLs fm.arity Mf) pA)) 0 fs res) ∧
      DomsBoundedA fm.arity ms ∧ (∀ F ∈ fs, F.BoundedA fm.arity) ∧
      (∀ x ∈ res, exprLevelsBoundedA fm.arity x = true) ∧
      ms.map (fun d => erase d.1) = c.view.mirrors.map Prod.fst ∧
      (fs.map FieldA.erase).map FieldT.unlevel = c.view.fields.map FieldT.unlevel ∧
      res.map erase = c.view.res ∧
      (∀ D u, FieldA.plain D u ∈ fs →
        ∃ D₀ u₀ ls, FieldT.plain D₀ u₀ ∈ c.view.fields ∧ u = instLevel ls u₀) ∧
      (∀ D u, FieldA.plain D u ∈ fs → UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN u fv.sort)) ∧
      (∀ x ∈ fs, x.NoFun) ∧
      (∀ fsPre D idx fsRest, fs = fsPre ++ .drecD D idx :: fsRest →
        Nonempty (HasTyA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) fm.arity
            (plainCtxA fsPre (telCtxA (instDomsA (closeLs fm.arity Mf) pA))) D (.sort fv.sort)) ∧
        Nonempty (ConvA (extendEnvA E f fmA) (iotaIfaceA (extendEnvA E f fmA)) fm.arity
            (plainCtxA fsPre (telCtxA (instDomsA (closeLs fm.arity Mf) pA))) D
            (foldAppsA (.const f (canonLevelsA fm.arity))
              ((paramLocalsA (instDomsA (closeLs fm.arity Mf) pA).length).map
                (liftA 0 (plainIdxA fsPre 0)) ++ idx)) (.sort fv.sort)) ∧
        ∀ x ∈ idx, exprLevelsBoundedA fm.arity x = true) := by
  -- main's view parts are bounded at the family's arity; the view's `drecD` evidence supplies the
  -- index bounds the type itself cannot carry (R-NoDeltaRec-4c)
  have hlvl := c.hlvl
  rw [c.harity, c.view.stored] at hlvl
  obtain ⟨hmM, hfM, hrM⟩ := ctorTypeT_bounded_rev fm.arity f _ _ _ _
    (fun D idx hd => drecDTypedT_idxBounded c.view.drecD_typed hd) hlvl
  have hpartsF : ∀ d ∈ fv.params.map Prod.fst, exprLevelsBounded fm.arity d = true :=
    fun d hd => hparts d (by rw [List.map_append]; exact List.mem_append_left _ hd)
  have hpartsI : ∀ d ∈ fv.indices.map Prod.fst, exprLevelsBounded fm.arity d = true :=
    fun d hd => hparts d (by rw [List.map_append]; exact List.mem_append_right _ hd)
  have hpa : ∀ d ∈ pA, exprLevelsBounded fm.arity (erase d.1) = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.params := by rw [← hpe]; exact List.mem_map_of_mem _ hd
    exact hpartsF (eraseDom d).1 (List.mem_map_of_mem Prod.fst hm)
  have hia : ∀ d ∈ iA, exprLevelsBounded fm.arity (erase d.1) = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.indices := by rw [← hie]; exact List.mem_map_of_mem _ hd
    exact hpartsI (eraseDom d).1 (List.mem_map_of_mem Prod.fst hm)
  obtain ⟨msA, fsA, resA, hmse, hfse, hrese, ⟨mc⟩, ⟨ft⟩, hnf, hsp⟩ :=
    ctorAnn C hn (pA := instDomsA (closeLs fm.arity Mf) pA) (iA := instDomsA (closeLs fm.arity Mf) iA)
      ((instDomsA_map_eraseDom hpa hpl).trans hpe)
      ((instDomsA_map_eraseDom hia hil).trans hie)
      (by rw [← instDomsA_append]; exact TelTyA.close C.hEL C.hIL fm.arity Mf htel)
      c hme hfr C' (hn.extend fun h => by rw [hfme] at h; cases h) hpreA hm ha
  -- one bound for the constructor's annotated data and the family's
  let Mc := Mf + domsBoundA msA + fieldsBoundA fsA + exprsBoundA resA
  have hMf : Mf ≤ Mc := by omega
  have hpbD := (domsBoundedA_append hbf).1
  have hib := (domsBoundedA_append hbf).2
  have hpb' : DomsBoundedA (fm.arity + Mc) pA := domsBoundedA_mono (by omega) hpbD
  have hib' : DomsBoundedA (fm.arity + Mc) iA := domsBoundedA_mono (by omega) hib
  have hmb : DomsBoundedA (fm.arity + Mc) msA :=
    domsBoundedA_mono (by omega) (domsBoundedA_domsBoundA msA)
  have hfb : ∀ F ∈ fsA, F.BoundedA (fm.arity + Mc) := fun F hF =>
    FieldA.BoundedA.mono (by omega) (fieldsBoundA_bounded fsA F hF)
  have hrb : ∀ x ∈ resA, exprLevelsBoundedA (fm.arity + Mc) x = true := fun x hx =>
    exprLevelsBoundedA_mono (by omega) _ (exprsBoundA_bounded resA x hx)
  -- close the mirrors and the fields
  have mc' := MirrorsConvA.close C.hEL C.hIL fm.arity Mc mc
  rw [instDomsA_closeLs_of_bounded (domsBoundedA_close hpbD)] at mc'
  have ft' := FieldsTyA.close C.hEL C.hIL fm.arity Mc _ ft
  rw [inst_piTelA_sort_closeLs hs, instCtxA_telCtxA,
    instDomsA_closeLs_of_bounded (domsBoundedA_close hpbD),
    instDomsA_closeLs_of_bounded (domsBoundedA_close hib)] at ft'
  refine ⟨instDomsA (closeLs fm.arity Mc) msA, fsA.map (FieldA.instLevels (closeLs fm.arity Mc)),
    resA.map (instantiateLevelsA (closeLs fm.arity Mc)), ⟨mc'⟩, ⟨ft'⟩, domsBoundedA_close hmb,
    fun F hF => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F', hF', rfl⟩ := List.mem_map.mp hF
    exact FieldA.BoundedA.close (hfb F' hF')
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact exprLevelsBoundedA_inst_closeLs _ (hrb y hy)
  · rw [← hmse]
    simp only [instDomsA, List.map_map]
    apply List.map_congr_left
    intro d hd
    show erase (instantiateLevelsA _ d.1) = erase d.1
    apply erase_close_of_bounded
    apply hmM (eraseDom d)
    rw [← hmse]; exact List.mem_map_of_mem _ hd
  · rw [← hfse]
    simp only [List.map_map]
    apply List.map_congr_left
    intro F hF
    exact FieldA.erase_close_unlevel F (hfM _ (by rw [← hfse]; exact List.mem_map_of_mem _ hF))
  · rw [← hrese, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact erase_close_of_bounded (hrM _ (by rw [← hrese]; exact List.mem_map_of_mem _ hx))
  · -- each plain field's level is main's, instantiated at the closing levels
    intro D u hDu
    obtain ⟨F, hF, hFe⟩ := List.mem_map.mp hDu
    cases F with
    | drec idx | frec _ _ _ idx | drecD _ idx => simp [FieldA.instLevels] at hFe
    | plain D₀ u₀ =>
        simp only [FieldA.instLevels, FieldA.plain.injEq] at hFe
        obtain ⟨rfl, rfl⟩ := hFe
        exact ⟨erase D₀, u₀, closeLs fm.arity Mc,
          by rw [← hfse]; exact List.mem_map_of_mem FieldA.erase hF, rfl⟩
  · intro D u hDu
    obtain ⟨F, hF, hFe⟩ := List.mem_map.mp hDu
    cases F with
    | drec idx | frec _ _ _ idx | drecD _ idx => simp [FieldA.instLevels] at hFe
    | plain D₀ u₀ =>
        simp only [FieldA.instLevels, FieldA.plain.injEq] at hFe
        obtain ⟨rfl, rfl⟩ := hFe
        have hmem : FieldT.plain (erase D₀) u₀ ∈ c.view.fields := by
          rw [← hfse]; exact List.mem_map_of_mem FieldA.erase hF
        rcases c.view.univ _ _ hmem with h | ⟨ht, hle⟩
        · exact Or.inl h
        · refine Or.inr ⟨ht, ?_⟩
          have := leN_instLevel hle (closeLs fm.arity Mc)
          rwa [instLevel_closeLs_of_bounded fv.sort hs] at this
  · -- no function-recursive field; the δ-reached fields carry real evidence now
    constructor
    · intro y hy
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy
      exact FieldA.noFun_instLevels _ (hnf F hF)
    · -- `annFieldsTyT`'s collected evidence, closed at `Mc`; the `Mf`-closed parameter context is
      -- already fixed at `Mc` (R-NoDeltaRec-4d-iii)
      intro fsPre D idx fsRest hfs
      obtain ⟨fsPreA, D₀, idx₀, fsRestA, hfsA, hpreE, hDE, hidxE, _⟩ :=
        fieldA_map_instLevels_split hfs
      obtain ⟨⟨tD⟩, ⟨tc⟩, -⟩ := hsp fsPreA D₀ idx₀ fsRestA hfsA
      simp only [List.nil_append] at tD tc
      have hmem0 : .drecD D₀ idx₀ ∈ fsA := by
        rw [hfsA]; exact List.mem_append_right _ (List.mem_cons_self _ _)
      obtain ⟨_, hidxB⟩ := hfb _ hmem0
      have hctx : instCtxA (closeLs fm.arity Mc)
          (plainCtxA fsPreA (telCtxA (instDomsA (closeLs fm.arity Mf) pA))) =
          plainCtxA fsPre (telCtxA (instDomsA (closeLs fm.arity Mf) pA)) := by
        rw [instCtxA_plainCtxA, instCtxA_telCtxA,
          instDomsA_closeLs_of_bounded (domsBoundedA_close hpbD), hpreE]
      have hsort : instantiateLevelsA (closeLs fm.arity Mc) (.sort fv.sort) = .sort fv.sort := by
        simp only [instantiateLevelsA]; rw [instLevel_closeLs_of_bounded fv.sort hs]
      have hlen : (instDomsA (closeLs fm.arity Mf) pA).length = fv.params.length := by
        simp only [instDomsA, List.length_map]
        rw [← List.length_map, hpe]
      have hpli : ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPreA 0))).map
          (instantiateLevelsA (closeLs fm.arity Mc)) =
          (paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPreA 0)) := by
        rw [List.map_map]
        rw [show instantiateLevelsA (closeLs fm.arity Mc) ∘ liftA 0 (plainIdxA fsPreA 0) =
            liftA 0 (plainIdxA fsPreA 0) ∘ instantiateLevelsA (closeLs fm.arity Mc) from
          funext fun x => instantiateLevelsA_liftA _ _ _ x]
        rw [← List.map_map, paramLocalsA_instLevels]
      have hfam : instantiateLevelsA (closeLs fm.arity Mc)
          (foldAppsA (.const f (canonLevelsA fm.arity))
            ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPreA 0)) ++ idx₀)) =
          foldAppsA (.const f (canonLevelsA fm.arity))
            ((paramLocalsA (instDomsA (closeLs fm.arity Mf) pA).length).map
              (liftA 0 (plainIdxA fsPre 0)) ++ idx) := by
        rw [instantiateLevelsA_foldAppsA, List.map_append, hpli, hidxE]
        simp only [instantiateLevelsA]
        rw [instantiateLevelsA_closeLs_canon fm.arity Mc fm.arity (Nat.le_refl _)]
        congr 1
        rw [hlen, hpreE, plainIdxA_instLevels]
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨?_⟩
        have hD' := closeTyA C'.hEL C'.hIL fm.arity Mc tD
        rwa [hctx, hsort, ← hDE] at hD'
      · refine ⟨?_⟩
        have hcv := closeConvA C'.hEL C'.hIL fm.arity Mc tc
        rwa [hctx, hsort, ← hDE, hfam] at hcv
      · intro x hx
        rw [hidxE] at hx
        obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
        exact exprLevelsBoundedA_inst_closeLs _ (hidxB x₀ hx₀)

theorem ctorFieldsT_unlevel (f : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (σ : SubstT) →
    ctorFieldsT f ls pl σ (fs.map FieldT.unlevel) res = ctorFieldsT f ls pl σ fs res
  | [], _, _ => rfl
  | .plain D u :: fs, pl, σ => by
      simp only [List.map_cons, FieldT.unlevel, ctorFieldsT, ctorFieldsT_unlevel f ls res fs]
  | .drec idx :: fs, pl, σ => by
      simp only [List.map_cons, FieldT.unlevel, ctorFieldsT, ctorFieldsT_unlevel f ls res fs]
  | .drecD D idx :: fs, pl, σ => by
      simp only [List.map_cons, FieldT.unlevel, ctorFieldsT, ctorFieldsT_unlevel f ls res fs]

theorem ctorTypeT_congr (f : Nat) (ls : List Level) {ms ms' : List (Expr Nat × Level)}
    {fs fs' : List FieldT} (res : List (Expr Nat)) (hm : ms.map Prod.fst = ms'.map Prod.fst)
    (hf : fs.map FieldT.unlevel = fs'.map FieldT.unlevel) :
    ctorTypeT f ls ms fs res = ctorTypeT f ls ms' fs' res := by
  have hl : ms.length = ms'.length := by rw [← List.length_map ms Prod.fst, hm, List.length_map]
  unfold ctorTypeT
  rw [hm, hl, ← ctorFieldsT_unlevel f ls res fs, hf, ctorFieldsT_unlevel]

/-- the policies agree: main's elimination policy as the copy's. -/
def _root_.Rcic.Declarative.EliminationPolicy.toA : EliminationPolicy → RecElimA
  | .anySort => .anySort
  | .propOnly => .propOnly

theorem _root_.Rcic.Declarative.EliminationPolicy.toA_motiveLevel (a : Nat) :
    (p : EliminationPolicy) → p.toA.motiveLevel a = policyMotiveLevel a p
  | .anySort => rfl
  | .propOnly => rfl

theorem _root_.Rcic.Declarative.EliminationPolicy.toA_arity (a : Nat) :
    (p : EliminationPolicy) → a + p.toA.extra = policyRecursorArity a p
  | .anySort => rfl
  | .propOnly => rfl

/-- a group's environment, erased, is main's group environment over the erased members. -/
theorem eraseEnv_groupEnvA (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) :
    (es : List (Nat × CheckedMemberA)) →
    eraseEnv (groupEnvA E f fm es) =
      groupEnvT (eraseEnv E) f (eraseMember fm) (es.map fun e => (e.1, eraseMember e.2))
  | [] => eraseEnv_extend E f fm
  | e :: es => by
      simp only [groupEnvA, groupEnvT, List.map_cons]
      rw [eraseEnv_extend, eraseEnv_groupEnvA E f fm es]

theorem groupFreshA_of_erase {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} :
    (es : List (Nat × CheckedMemberA)) →
    GroupFreshT (eraseEnv E) f (eraseMember fm) (es.map fun e => (e.1, eraseMember e.2)) →
    GroupFreshA E f fm es
  | [], h => members_none_of_erase h
  | e :: es, h => by
      simp only [List.map_cons, GroupFreshT] at h
      refine ⟨groupFreshA_of_erase es h.1, members_none_of_erase ?_⟩
      rw [eraseEnv_groupEnvA]; exact h.2



end CloseCtor

/-! ## (9) the copy's group from closed views, at any interface -/

section CopyGroup

def famViewOfA (a : Nat) (pA iA : List (ExprA × Level)) (s : Level) (hp : UniformProp s ∨ UniformType s) :
    FamViewA (famMemberA a pA iA s) :=
  ⟨pA, iA, s, rfl, rfl, hp⟩

/-- the copy's constructor member: its type built from its view. `normA` is the same build over
    `fs.map FieldA.norm` — each δ-reached field read as the family application — which is what ι's
    shape reader needs (R-NoDeltaRec-3a); under `noDelta` it is the stored type itself. -/
def ctorMemberA (a f : Nat) (s : Level) (ms : List (ExprA × Level)) (fs : List FieldA) (res : List ExprA) :
    CheckedMemberA :=
  ⟨.constructorM, a, ctorTypeA f (canonLevelsA a) s ms fs res, none, 0,
    some (ctorTypeA f (canonLevelsA a) s ms (fs.map FieldA.norm) res)⟩

/-- a constructor's closed view data, typed in the base at the base's own interface. -/
structure CtorCopyA (E : ResolvedEnvA) (f : Nat) (a : Nat) (s : Level)
    (pA iA : List (ExprA × Level)) : Type where
  ms : List (ExprA × Level)
  fs : List FieldA
  res : List ExprA
  mc : MirrorsConvA E (iotaIfaceA E) a [] ms pA
  ft : FieldsTyA E (iotaIfaceA E) a (fun k => liftA 0 k (piTelA iA (.sort s) (.succ s)).1) (telCtxA pA) 0 fs res
  hms : DomsBoundedA a ms
  hfs : ∀ F ∈ fs, F.BoundedA a
  hres : ∀ x ∈ res, exprLevelsBoundedA a x = true
  univ : ∀ D u, FieldA.plain D u ∈ fs → UniformProp s ∨ (UniformType s ∧ leN u s)
  /-- annotated from `main`'s views, which have no function-recursive field (R-NoFunRec-1);
      `NoFun`, not `TreeField` — `.drecD` fields annotate now (R-NoDeltaRec-4d-ii). -/
  noFun : ∀ x ∈ fs, x.NoFun
  /-- a δ-reached field's evidence, collected by `annFieldsTyT` and closed at the fields' bound:
      the domain typed in the family's extended scope at the field's position, convertible to
      the family application at its indices, the indices bounded (R-NoDeltaRec-4d-iii). -/
  drecD_typed : ∀ fsPre D idx fsRest, fs = fsPre ++ .drecD D idx :: fsRest →
    Nonempty (HasTyA (extendEnvA E f (famMemberA a pA iA s)) (iotaIfaceA (extendEnvA E f (famMemberA a pA iA s))) a
        (plainCtxA fsPre (telCtxA pA)) D (.sort s)) ∧
    Nonempty (ConvA (extendEnvA E f (famMemberA a pA iA s)) (iotaIfaceA (extendEnvA E f (famMemberA a pA iA s))) a
        (plainCtxA fsPre (telCtxA pA)) D
        (foldAppsA (.const f (canonLevelsA a))
          ((paramLocalsA pA.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx)) (.sort s)) ∧
    ∀ x ∈ idx, exprLevelsBoundedA a x = true

/-- the constructor view at an interface agreeing with the base's own. -/
def CtorCopyA.view {E : ResolvedEnvA} {a f : Nat} {s : Level} {pA iA : List (ExprA × Level)}
    {hp : UniformProp s ∨ UniformType s} (K : IotaIfaceA) (hag : IfaceAgreeA E (iotaIfaceA E) K)
    (hag' : IfaceAgreeA (extendEnvA E f (famMemberA a pA iA s))
      (iotaIfaceA (extendEnvA E f (famMemberA a pA iA s))) K)
    (d : CtorCopyA E f a s pA iA)
    (hnc : Nonempty (TyConvA (extendEnvA E f (famMemberA a pA iA s)) K a []
      (ctorTypeA f (canonLevelsA a) s d.ms d.fs d.res)
      (ctorTypeA f (canonLevelsA a) s d.ms (d.fs.map FieldA.norm) d.res)))
    (hnt : ∃ l', Nonempty (HasTyA (extendEnvA E f (famMemberA a pA iA s)) K a []
      (ctorTypeA f (canonLevelsA a) s d.ms (d.fs.map FieldA.norm) d.res) (.sort l'))) :
    CtorViewA E K f (famMemberA a pA iA s) (famViewOfA a pA iA s hp) (ctorMemberA a f s d.ms d.fs d.res) where
  mirrors := d.ms
  fields := d.fs
  res := d.res
  stored := rfl
  mirrorsConv := d.mc.iface hag
  typed := d.ft.iface hag
  univ := d.univ
  univI := fun _ _ _ _ h => (d.noFun _ h).elim
  drecD_typed := fun fsPre D idx fsRest h =>
    match d.drecD_typed fsPre D idx fsRest h with
    | ⟨⟨hd⟩, ⟨hc⟩, hb⟩ => ⟨⟨hasTyIfaceA hag' hd⟩, ⟨convIfaceA hag' hc⟩, hb⟩
  normConv := hnc
  normTyped := hnt

/-- the group constructor at an interface, from its closed view and a typing of its type there. -/
def CtorCopyA.groupCtor {E : ResolvedEnvA} {a f : Nat} {s : Level} {pA iA : List (ExprA × Level)}
    {hp : UniformProp s ∨ UniformType s} (hs : levelBounded a s = true) (K : IotaIfaceA)
    (hag : IfaceAgreeA E (iotaIfaceA E) K)
    (hag' : IfaceAgreeA (extendEnvA E f (famMemberA a pA iA s))
      (iotaIfaceA (extendEnvA E f (famMemberA a pA iA s))) K)
    (ref : Nat) (d : CtorCopyA E f a s pA iA)
    (hparams : ∀ j (P : ExprA) (u : Level), pA.get? j = some (P, u) → boundOkB j P = true)
    (hclT : ∀ k, liftA k 1 (ctorTypeA f (canonLevelsA a) s d.ms d.fs d.res) =
      ctorTypeA f (canonLevelsA a) s d.ms d.fs d.res) (u : Level)
    (hT : HasTyA (extendEnvA E f (famMemberA a pA iA s)) K a []
      (ctorTypeA f (canonLevelsA a) s d.ms d.fs d.res) (.sort u))
    (hnc : Nonempty (TyConvA (extendEnvA E f (famMemberA a pA iA s)) K a []
      (ctorTypeA f (canonLevelsA a) s d.ms d.fs d.res)
      (ctorTypeA f (canonLevelsA a) s d.ms (d.fs.map FieldA.norm) d.res)))
    (hnt : ∃ l', Nonempty (HasTyA (extendEnvA E f (famMemberA a pA iA s)) K a []
      (ctorTypeA f (canonLevelsA a) s d.ms (d.fs.map FieldA.norm) d.res) (.sort l'))) :
    GroupCtorA K E f (famMemberA a pA iA s) (famViewOfA a pA iA s hp) where
  ref := ref
  member := ctorMemberA a f s d.ms d.fs d.res
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := hclT
  u := u
  hT := hT
  hlvl := ctorTypeA_bounded_fwd a f (canonLevelsA a) s d.ms d.fs d.res (levelsBounded_canonA a) hs d.hms
    d.hfs d.hres
  view := d.view K hag hag' hnc hnt
  hnorm := rfl
  hclN := fun k => liftA_of_boundOkB 1 k _
    (boundOkB_add k 0 _ (ctorTypeA_norm_boundOk (d.view K hag hag' hnc hnt) hparams))
  hlvlN := ctorTypeA_bounded_fwd a f (canonLevelsA a) s d.ms (d.fs.map FieldA.norm) d.res
    (levelsBounded_canonA a) hs d.hms (fun F hF => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
      exact y.BoundedA_norm (d.hfs y hy)) d.hres

/-- a group constructor between agreeing interfaces. -/
def GroupCtorA.iface {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {K K' : IotaIfaceA} (hag : IfaceAgreeA (extendEnvA E f fm) K K') (hfr : E.members f = none)
    (c : GroupCtorA K E f fm fv) : GroupCtorA K' E f fm fv where
  ref := c.ref
  member := c.member
  hcls := c.hcls
  hnobody := c.hnobody
  harity := c.harity
  hnp := c.hnp
  hclT := c.hclT
  u := c.u
  hT := hasTyIfaceA hag c.hT
  hlvl := c.hlvl
  view := c.view.iface (hag.prefix (prefixA_extend E f fm hfr)) hag
  hnorm := c.hnorm
  hclN := c.hclN
  hlvlN := c.hlvlN

theorem GroupCtorA.iface_entries {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {K K' : IotaIfaceA} (hag : IfaceAgreeA (extendEnvA E f fm) K K') (hfr : E.members f = none)
    (cs : List (GroupCtorA K E f fm fv)) :
    (cs.map (GroupCtorA.iface hag hfr)).map GroupCtorA.entry = cs.map GroupCtorA.entry := by
  simp only [List.map_map]; rfl

theorem GroupCtorA.iface_minors {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {K K' : IotaIfaceA} (hag : IfaceAgreeA (extendEnvA E f fm) K K') (hfr : E.members f = none)
    (cs : List (GroupCtorA K E f fm fv)) :
    (cs.map (GroupCtorA.iface hag hfr)).reverse.map GroupCtorA.minorData = cs.reverse.map GroupCtorA.minorData := by
  simp only [List.map_reverse, List.map_map]; rfl

theorem GroupCtorA.iface_refs {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {K K' : IotaIfaceA} (hag : IfaceAgreeA (extendEnvA E f fm) K K') (hfr : E.members f = none)
    (cs : List (GroupCtorA K E f fm fv)) :
    (cs.map (GroupCtorA.iface hag hfr)).reverse.map GroupCtorA.ref = cs.reverse.map GroupCtorA.ref := by
  simp only [List.map_reverse, List.map_map]; rfl

/-- every recursor of a group's environment is a base member: the family and its constructors are not
    recursors. -/
theorem recHead_of_groupEnvA {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    (hfm : fm.mclass = .inductiveM) {es : List (Nat × CheckedMemberA)}
    (hes : ∀ e ∈ es, e.2.mclass = .constructorM) {I : IotaIfaceA}
    (h : IotaRecHeadA (groupEnvA E₀ f fm es) I) : IotaRecHeadA E₀ I := by
  intro e e' he
  obtain ⟨r, ls, m, hhead, hm, hcls, hlen⟩ := h e e' he
  refine ⟨r, ls, m, hhead, ?_, hcls, hlen⟩
  rcases members_groupEnvA es r m hm with ⟨_, rfl⟩ | hin | hbase
  · rw [hfm] at hcls; exact absurd hcls (by decide)
  · rw [hes _ hin] at hcls; exact absurd hcls (by decide)
  · exact hbase

end CopyGroup

/-! ## (10) arc D's contract: the built member types typed from the views

`CtorTyOfViewA` and `RecTyOfViewsA` are the two statements `ctorsTyped`, `bridge_group` and
`envBridge` consume. They stay hypotheses. `CtorTyOfViewSemA` and `RecTyOfViewsSemA` add the
base's semantics at its own ι and agreement with the conclusion's interface. Those are not the
original universal contract. -/

/-- (T1) a constructor view's built type is typed in the base and the family. -/
def CtorTyOfViewA : Prop :=
  ∀ {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA} {u : Level},
    EnvClosedA E → EnvClosedA (extendEnvA E f fm) → EnvNormCtorTypeA E → EnvNormClosedA E →
    EnvLevelsA E → EnvLevelsA (extendEnvA E f fm) →
    IotaLiftA I → IotaSubstA I → IotaLevelsA I → IotaRecHeadA E I → IotaRecHeadA (extendEnvA E f fm) I →
    E.members f = none → fm.mclass = .inductiveM → HasTyA E I fm.arity [] fm.mtypeA (.sort u) →
    (fv : FamViewA fm) → (v : CtorViewA E I f fm fv cm) →
    ∃ w, Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors v.fields v.res) (.sort w))

/-- (T2) a group's built recursor type is typed with its constructors present. -/
def RecTyOfViewsA : Prop :=
  ∀ {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA} {u : Level} {fv : FamViewA fm}
    (cs : List (GroupCtorA I E f fm fv)) (elim : RecElimA),
    EnvClosedA E → EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)) → EnvNormCtorTypeA E →
    EnvNormClosedA E → EnvLevelsA E →
    EnvLevelsA (groupEnvA E f fm (cs.map GroupCtorA.entry)) →
    IotaLiftA I → IotaSubstA I → IotaLevelsA I → IotaRecHeadA E I → IotaRecHeadA (extendEnvA E f fm) I →
    IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I →
    GroupFreshA E f fm (cs.map GroupCtorA.entry) → fm.mclass = .inductiveM →
    HasTyA E I fm.arity [] fm.mtypeA (.sort u) →
    ∃ w, Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) []
      (groupRecTypeA fv cs elim) (.sort w))

/-- (T1) at the base's own ι. `CtorTyOfViewA`'s premises, plus the base's semantics at
    `iotaIfaceA E` and agreement with the conclusion's interface. Not `CtorTyOfViewA`.
    `EnvNormClosedA E` (R-NoDeltaRec-3b) feeds the base's own ι laws on `normA`. -/
def CtorTyOfViewSemA : Prop :=
  ∀ {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA} {u : Level},
    EnvClosedA E → EnvClosedA (extendEnvA E f fm) → EnvNormClosedA E → EnvNormCtorTypeA E →
    EnvLevelsA E → EnvLevelsA (extendEnvA E f fm) →
    IotaLiftA I → IotaSubstA I → IotaLevelsA I → IotaRecHeadA E I → IotaRecHeadA (extendEnvA E f fm) I →
    E.members f = none → fm.mclass = .inductiveM → HasTyA E I fm.arity [] fm.mtypeA (.sort u) →
    (fv : FamViewA fm) → (v : CtorViewA E I f fm fv cm) →
    (ρ₀ : Nat → Nat) → PosValA ρ₀ → EnvSemA E (iotaIfaceA E) fm.arity ρ₀ →
    IfaceAgreeA E (iotaIfaceA E) I →
    ∃ w, Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors v.fields v.res) (.sort w))

/-- (T2) at the base's own ι. `RecTyOfViewsA`'s premises, plus the base's semantics at
    `iotaIfaceA E` and agreement with the conclusion's interface. Not `RecTyOfViewsA`. -/
def RecTyOfViewsSemA : Prop :=
  ∀ {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA} {u : Level} {fv : FamViewA fm}
    (cs : List (GroupCtorA I E f fm fv)) (elim : RecElimA),
    EnvClosedA E → EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)) → EnvNormClosedA E →
    EnvNormCtorTypeA E → EnvLevelsA E →
    EnvLevelsA (groupEnvA E f fm (cs.map GroupCtorA.entry)) →
    IotaLiftA I → IotaSubstA I → IotaLevelsA I → IotaRecHeadA E I → IotaRecHeadA (extendEnvA E f fm) I →
    IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I →
    GroupFreshA E f fm (cs.map GroupCtorA.entry) → fm.mclass = .inductiveM →
    HasTyA E I fm.arity [] fm.mtypeA (.sort u) →
    (ρ₀ : Nat → Nat) → PosValA ρ₀ → EnvSemA E (iotaIfaceA E) fm.arity ρ₀ →
    IfaceAgreeA E (iotaIfaceA E) I →
    ∃ w, Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) []
      (groupRecTypeA fv cs elim) (.sort w))

/-! ## (11) the profiles along an extension -/

section ProfilesA

/-- a recursor of an admitted base keeps (O1) in any extension of it: its major names a family of the
    base, which the extension keeps. -/
theorem propElimStructA_base {I : IotaIfaceA} {EA EA' : ResolvedEnvA} (hW : EnvWfA I EA)
    (hpre : PrefixA EA EA') (h : PropElimStructA EA) {r : Nat} {rm : CheckedMemberA} {D : ExprA} {f' : Nat}
    {ls' : List Level} {fm' : CheckedMemberA} {u₀ : Level} (hrm : EA.members r = some rm)
    (hcl : rm.mclass = .recursorM) (hlast : (piDomsA rm.mtypeA).getLast? = some D)
    (hhead : (appsSpineA D).1 = .const f' ls') (hfm' : EA'.members f' = some fm')
    (hfcl : fm'.mclass = .inductiveM) (hbody : piBodyA fm'.mtypeA = .sort u₀) (hprop : UniformProp u₀)
    (hne : r ≠ f' + 1) (hun : unitGroupA r rm = false) (hns : structGroupA r rm = false) (M : ExprA)
    (hM : (piDomsA rm.mtypeA)[fm'.nparamsA]? = some M) :
    piBodyA M = .sort .zero := by
  obtain ⟨_, ⟨hty⟩⟩ := envWfA_memberTy hW r rm hrm
  have hDc := constsInA_piDomsA _ (hasTyA_constsIn hty) D (List.mem_of_getLast?_eq_some hlast)
  have hheadc : ConstsInA (domA EA) (appsSpineA D).1 := by
    rw [← foldAppsA_appsSpineA D] at hDc
    exact (constsInA_foldAppsA_inv _ _ hDc).1
  rw [hhead] at hheadc
  obtain ⟨m0, hm0⟩ := hheadc
  have hfe : m0 = fm' := Option.some.inj ((hpre f' m0 hm0).symm.trans hfm')
  exact h r rm D f' ls' fm' u₀ hrm hcl hlast hhead (hfe ▸ hm0) hfcl hbody hprop hne hun hns M hM

/-- both profiles survive an extension by a member that is neither a family nor a recursor. -/
theorem profilesA_extend {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA) {r : Nat}
    {m : CheckedMemberA} (hfr : EA.members r = none) (hi : m.mclass ≠ .inductiveM)
    (hrc : m.mclass ≠ .recursorM) (hsm : SmallIndexProfileA EA) (hpo : PropElimStructA EA) :
    SmallIndexProfileA (extendEnvA EA r m) ∧ PropElimStructA (extendEnvA EA r m) := by
  refine ⟨fun r' m' u₀ hm' hcl => ?_, fun r' rm D f' ls' fm' u₀ hrm hcl hlast hhead hfm' => ?_⟩
  · by_cases hr : r' = r
    · subst hr; rw [members_extendEnvA_self] at hm'; cases hm'; exact absurd hcl hi
    · rw [members_extendEnvA_ne _ _ _ hr] at hm'; exact hsm r' m' u₀ hm' hcl
  · by_cases hr : r' = r
    · subst hr; rw [members_extendEnvA_self] at hrm; cases hrm; exact absurd hcl hrc
    · rw [members_extendEnvA_ne _ _ _ hr] at hrm
      exact propElimStructA_base hW (prefixA_extend EA r m hfr) hpo hrm hcl hlast hhead hfm'

/-- the closed telescope's index levels inherit the family's smallness: `instLevel`-closing is an
    `eval`-substitution, and the premise quantifies over every valuation (R-NoDeltaRec-4d-ii). -/
theorem idxLevels_small_close {a M : Nat} {s : Level} {iA : List (ExprA × Level)}
    {idxs : List (Expr Nat × Level)}
    (hie : iA.map eraseDom = idxs)
    (hsi : ∀ v ∈ idxs.map Prod.snd, ∀ (ρ : Nat → Option Nat) (x y : Nat),
      eval ρ v = some x → eval ρ s = some y → 0 < y → x ≤ y)
    (hs : levelBounded a s = true) :
    ∀ v ∈ (instDomsA (closeLs a M) iA).map Prod.snd, ∀ (ρ : Nat → Option Nat) (x y : Nat),
      eval ρ v = some x → eval ρ s = some y → 0 < y → x ≤ y := by
  intro v hv ρ x y hx hy hpos
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
  obtain ⟨d₀, hd₀, hde⟩ := List.mem_map.mp hd
  obtain ⟨d₁, d₂⟩ := d
  obtain ⟨-, rfl⟩ := Prod.mk.inj hde
  have hmem : (eraseDom d₀).2 ∈ idxs.map Prod.snd := by
    rw [← hie]; exact List.mem_map_of_mem Prod.snd (List.mem_map_of_mem eraseDom hd₀)
  rw [eval_instLevel] at hx
  rw [← instLevel_closeLs_of_bounded (M := M) s hs, eval_instLevel] at hy
  exact hsi d₀.2 hmem _ x y hx hy hpos

/-- the family's own smallness holds at its extension: the index sorts' levels bound at every
    valuation (R-NoDeltaRec-4d-ii; the premise is the group's profile). -/
theorem smallIndexProfileA_fam {EA : ResolvedEnvA} {f : Nat} {a : Nat}
    {pA iA : List (ExprA × Level)} {s : Level}
    (hsi : ∀ v ∈ iA.map Prod.snd, ∀ (ρ : Nat → Option Nat) (x y : Nat),
      eval ρ v = some x → eval ρ s = some y → 0 < y → x ≤ y)
    (hsmall0 : SmallIndexProfileA EA) (hfr : EA.members f = none) :
    SmallIndexProfileA (extendEnvA EA f (famMemberA a pA iA s)) := by
  intro r m u₀ hm hcl hbody v hv ρ x y hx hy hpos
  by_cases hr : r = f
  · subst hr
    rw [members_extendEnvA_self] at hm
    cases hm
    have hb : piBodyA (famMemberA a pA iA s).mtypeA = .sort s := by
      show piBodyA (piTelA _ _ _).1 = _
      rw [piBodyA_piTelA]; rfl
    rw [hb] at hbody
    cases hbody
    have hdl : (piDomLevelsA (famMemberA a pA iA s).mtypeA).drop
        (famMemberA a pA iA s).nparamsA = iA.map Prod.snd := by
      show (piDomLevelsA (piTelA _ _ _).1).drop pA.length = _
      rw [piDomLevelsA_piTelA, List.map_append, List.append_assoc, List.drop_left' (by simp)]
      show _ ++ ([] : List Level) = _
      rw [List.append_nil]
    rw [hdl] at hv
    exact hsi v hv ρ x y hx hy hpos
  · rw [members_extendEnvA_ne _ _ _ hr] at hm
    exact hsmall0 r m u₀ hm hcl hbody v hv ρ x y hx hy hpos

/-- `PropElimStructA` survives an inductive's extension: the new member is no recursor. -/
theorem propElimStructA_extendFam {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    {f : Nat} {m : CheckedMemberA} (hfr : EA.members f = none)
    (hrc : m.mclass ≠ .recursorM) (hpo : PropElimStructA EA) :
    PropElimStructA (extendEnvA EA f m) := by
  intro r' rm D f' ls' fm' u₀ hrm hcl hlast hhead hfm' hfcl hbody hprop hne hun hns M hM
  by_cases hr : r' = f
  · subst hr; rw [members_extendEnvA_self] at hrm; cases hrm; exact absurd hcl hrc
  · rw [members_extendEnvA_ne _ _ _ hr] at hrm
    exact propElimStructA_base hW (prefixA_extend EA f m hfr) hpo hrm hcl hlast hhead hfm'
      hfcl hbody hprop hne hun hns M hM

/-- the restriction survives an extension by a member that is not a constructor. -/
theorem envNoFunA_extend {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA) (hnf : EnvNoFunA EA)
  {r : Nat}
    {m : CheckedMemberA} (hfr : EA.members r = none) (hct : m.mclass ≠ .constructorM) :
    EnvNoFunA (extendEnvA EA r m) := by
  intro c cm f fm shapes hc hcl hfam hf hsh s hs j
  by_cases hcr : c = r
  · subst hcr; rw [members_extendEnvA_self] at hc; cases hc; exact absurd hcl hct
  · rw [members_extendEnvA_ne _ _ _ hcr] at hc
    obtain ⟨fm', hf'⟩ := ctorFamInA_of_envWfA hW c cm f hc hcl hfam
    have hfr' : f ≠ r := fun h => by rw [h, hfr] at hf'; cases hf'
    rw [members_extendEnvA_ne _ _ _ hfr'] at hf
    exact hnf c cm f fm shapes hc hcl hfam hf hsh s hs j

/-- the restriction survives a group with its recursor,
  whose constructors have no function-recursive field. -/
theorem envNoFunA_groupRec {I J : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA) (hnf : EnvNoFunA EA)
    {f : Nat} {fmA : CheckedMemberA} {fvA : FamViewA fmA} {csA : List (GroupCtorA J EA f fmA fvA)}
    {rm : CheckedMemberA} (hfresh : GroupFreshA EA f fmA (csA.map GroupCtorA.entry))
    (hrfresh : (groupEnvA EA f fmA (csA.map GroupCtorA.entry)).members (f + 1 + csA.length) = none)
    (hnfc : ∀ c ∈ csA, ∀ x ∈ c.view.fields, x.NoFun) (hfcl : fmA.mclass ≠ .constructorM)
    (hrm : rm.mclass ≠ .constructorM) :
    EnvNoFunA (extendEnvA (groupEnvA EA f fmA (csA.map GroupCtorA.entry)) (f + 1 + csA.length) rm) := by
  intro c cm f' fm shapes hc hcl hfam hf hsh s hs j
  by_cases hcr : c = f + 1 + csA.length
  · subst hcr; rw [members_extendEnvA_self] at hc; cases hc; exact absurd hcl hrm
  · rw [members_extendEnvA_ne _ _ _ hcr] at hc
    rcases members_groupEnvA _ c cm hc with ⟨rfl, rfl⟩ | hin | hbase
    · exact absurd hcl hfcl
    · obtain ⟨gc, hgc, hge⟩ := List.mem_map.mp hin
      have hgm : gc.member = cm := congrArg Prod.snd hge
      subst hgm
      have hff : f' = f := by
        have h := gc.view.famRef
        rw [hfam] at h
        exact Option.some.inj h
      subst hff
      have hfne : f' ≠ f' + 1 + csA.length := by omega
      rw [members_extendEnvA_ne _ _ _ hfne, members_groupEnvA_family hfresh] at hf
      cases hf
      have hshv := gc.view.shapes hfresh.base
      rw [gc.normA_getD, hshv] at hsh
      cases hsh
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      exact FieldA.shape_ne_succ (hnfc gc hgc x hx) j
    · obtain ⟨fm', hf'⟩ := ctorFamInA_of_envWfA hW c cm f' hbase hcl hfam
      have hpre := prefixA_trans (prefixA_groupEnvA hfresh) (prefixA_extend _ _ rm hrfresh)
      rw [hpre f' fm' hf'] at hf
      cases hf
      exact hnf c cm f' fm shapes hbase hcl hfam hf' hsh s hs j

end ProfilesA

/-! ## (12) the group step, assembled -/

section GroupStep

/-- the relation a closed constructor copy bears to main's constructor: the parts erase to main's, the
    fields up to their recorded levels, and each plain field's level is an instance of a level main
    records for a plain field (W-1 (e-3)). -/
def CtorMatches {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (c : GroupCtorT E f fm fv) (ms : List (ExprA × Level)) (fs : List FieldA) (res : List ExprA) : Prop :=
  ms.map (fun x => erase x.1) = c.view.mirrors.map Prod.fst ∧
  (fs.map FieldA.erase).map FieldT.unlevel = c.view.fields.map FieldT.unlevel ∧ res.map erase = c.view.res ∧
  ∀ D u, FieldA.plain D u ∈ fs → ∃ D₀ u₀ ls, FieldT.plain D₀ u₀ ∈ c.view.fields ∧ u = instLevel ls u₀

/-- two lists related pointwise. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} (h : R x y) (t : ListRel R xs ys) :
      ListRel R (x :: xs) (y :: ys)

theorem ListRel.length_eq {α β : Type} {R : α → β → Prop} :
    {xs : List α} → {ys : List β} → ListRel R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => congrArg Nat.succ t.length_eq

theorem exists_forall₂ {α β : Type} {R : α → β → Prop} :
    (xs : List α) → (∀ x ∈ xs, ∃ y, R x y) → ∃ ys : List β, ListRel R xs ys
  | [], _ => ⟨[], .nil⟩
  | x :: xs, h => by
      obtain ⟨y, hy⟩ := h x (List.mem_cons_self _ _)
      obtain ⟨ys, hys⟩ := exists_forall₂ xs (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
      exact ⟨y :: ys, .cons hy hys⟩

/-- THE FAMILY, CLOSED. -/
theorem famClosed {E : ResolvedEnvA} (C : AnnEnvA E) (hn : EnvNormEraseA E) {fm : CheckedMember} {fv : FamViewT fm}
    (htel : TelTyT (eraseEnv E) fm.arity [] (fv.params ++ fv.indices)) :
    ∃ (pA iA : List (ExprA × Level)) (Mf : Nat), pA.map eraseDom = fv.params ∧
      iA.map eraseDom = fv.indices ∧ DomsBoundedA (fm.arity + Mf) (pA ++ iA) ∧
      Nonempty (TelTyA E (iotaIfaceA E) fm.arity [] (pA ++ iA)) := by
  obtain ⟨pA, iA, hpe, hie, htelA⟩ := famAnn C hn htel
  exact ⟨pA, iA, domsBoundA (pA ++ iA), hpe, hie,
    domsBoundedA_mono (Nat.le_add_left _ _) (domsBoundedA_domsBoundA _), htelA⟩

/-- THE CONSTRUCTORS, CLOSED, one copy per main constructor. -/
theorem ctorsClosed {E : ResolvedEnvA} (C : AnnEnvA E) (hn : EnvNormEraseA E) {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (hs : levelBounded fm.arity fv.sort = true) {pA iA : List (ExprA × Level)}
    (hpe : pA.map eraseDom = fv.params) (hie : iA.map eraseDom = fv.indices)
    (htel : TelTyA E (iotaIfaceA E) fm.arity [] (pA ++ iA)) {Mf : Nat}
    (hbf : DomsBoundedA (fm.arity + Mf) (pA ++ iA))
    (hpl : ∀ d ∈ pA, levelBounded fm.arity d.2 = true)
    (hil : ∀ d ∈ iA, levelBounded fm.arity d.2 = true)
    (hparts : ∀ d ∈ (fv.params ++ fv.indices).map Prod.fst,
      exprLevelsBounded fm.arity d = true)
    (cs : List (GroupCtorT (eraseEnv E) f fm fv))
    {fmA : CheckedMemberA} (hme : eraseMember fmA = fm) (hfr : E.members f = none)
    (C' : AnnEnvA (extendEnvA E f fmA)) (hpreA : PrefixA E (extendEnvA E f fmA))
    (hm : fmA.mtypeA = (piTelA (instDomsA (closeLs fm.arity Mf) pA ++
        instDomsA (closeLs fm.arity Mf) iA) (.sort fv.sort) (.succ fv.sort)).1)
    (ha : fmA.arity = fm.arity)
    (hfme : fmA = famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
        (instDomsA (closeLs fm.arity Mf) iA) fv.sort) :
    ∃ ds : List (CtorCopyA E f fm.arity fv.sort (instDomsA (closeLs fm.arity Mf) pA)
        (instDomsA (closeLs fm.arity Mf) iA)),
      ListRel (fun c d => CtorMatches c d.ms d.fs d.res) cs ds :=
  exists_forall₂ cs (fun c hc => by
    obtain ⟨ms, fs, res, ⟨mc⟩, ⟨ft⟩, hmb, hfb, hrb, hm, hf, hr, hlev, huniv, hnf, hdt⟩ :=
      ctorClosed C hn hs hpe hie htel hbf hpl hil hparts c hme hfr C' hpreA hm ha hfme
    exact ⟨⟨ms, fs, res, mc, ft, hmb, hfb, hrb, huniv, hnf, hfme ▸ hdt⟩, hm, hf, hr, hlev⟩)

/-- the copy's constructor member erases to main's. -/
theorem eraseMember_ctorMemberA {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (c : GroupCtorT E f fm fv) {ms : List (ExprA × Level)} {fs : List FieldA} {res : List ExprA}
    (h : CtorMatches c ms fs res) (hnf : ∀ x ∈ fs, x.NoFun) :
    eraseMember (ctorMemberA fm.arity f fv.sort ms fs res) = c.member := by
  obtain ⟨hm, hf, hr, -⟩ := h
  have hty : erase (ctorTypeA f (canonLevelsA fm.arity) fv.sort ms fs res) = c.member.mtype := by
    rw [erase_ctorTypeA _ _ _ _ _ _ hnf, c.view.stored, hr]
    apply ctorTypeT_congr
    · rw [List.map_map, ← hm]; rfl
    · exact hf
  have hcls := c.hcls
  have hnb := c.hnobody
  have har := c.harity
  calc eraseMember (ctorMemberA fm.arity f fv.sort ms fs res)
      = ⟨c.member.mclass, c.member.arity, c.member.mtype, c.member.body⟩ := by
        simp only [eraseMember, ctorMemberA, hty, hcls, hnb, har, Option.map_none']
    _ = c.member := rfl

/-- what a typed copy constructor keeps of main's. The member's `normA` is certified populated with
    the view-built normed type (R-NoDeltaRec-3c): the SOME direction `hnorm` conditions on, so a
    keeps-related copy member always carries its normal form — `CtorCopyA.groupCtor` discharges it
    by `rfl`. -/
def CtorKeeps {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm} {K : IotaIfaceA}
    {EA : ResolvedEnvA} {fmA : CheckedMemberA} {fvA : FamViewA fmA}
    (c : GroupCtorT E f fm fv) (cA : GroupCtorA K EA f fmA fvA) : Prop :=
  cA.ref = c.ref ∧ eraseMember cA.member = c.member ∧
    CtorMatches c cA.view.mirrors cA.view.fields cA.view.res ∧
    (∀ x ∈ cA.view.fields, x.NoFun) ∧
    cA.member.normA = some (ctorTypeA f (canonLevelsA fmA.arity) fvA.sort cA.view.mirrors
      (cA.view.fields.map FieldA.norm) cA.view.res)

/-- THE CONSTRUCTORS TYPED at an interface where (T1)'s side conditions hold. -/
theorem ctorsTyped (hT1 : CtorTyOfViewA) {E : ResolvedEnvA} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {pA iA : List (ExprA × Level)} {hp : UniformProp fv.sort ∨ UniformType fv.sort}
    (hs : levelBounded fm.arity fv.sort = true) (K : IotaIfaceA) (hag : IfaceAgreeA E (iotaIfaceA E) K)
    (hE : EnvClosedA E) (hEf : EnvClosedA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)))
    (hENC : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hEL : EnvLevelsA E) (hELf : EnvLevelsA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)))
    (hI : IotaLiftA K) (hIS : IotaSubstA K) (hIL : IotaLevelsA K) (hR : IotaRecHeadA E K)
    (hRf : IotaRecHeadA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K)
    (hfr : E.members f = none) {uf : Level}
    (hTf : HasTyA E K fm.arity [] (famMemberA fm.arity pA iA fv.sort).mtypeA (.sort uf))
    (hagf : IfaceAgreeA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort))
      (iotaIfaceA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort))) K)
    (huniq : ViewTySortUniqA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity) :
    {cs : List (GroupCtorT (eraseEnv E) f fm fv)} → {ds : List (CtorCopyA E f fm.arity fv.sort pA iA)} →
    ListRel (fun c d => CtorMatches c d.ms d.fs d.res) cs ds →
    ∃ csA : List (GroupCtorA K E f (famMemberA fm.arity pA iA fv.sort) (famViewOfA fm.arity pA iA fv.sort hp)),
      ListRel CtorKeeps cs csA
  | _, _, .nil => ⟨[], .nil⟩
  | c :: _, d :: _, .cons hm hrest => by
      obtain ⟨csA, hcsA⟩ := ctorsTyped (hp := hp) hT1 hs K hag hE hEf hENC hNC hEL hELf hI hIS hIL hR hRf
        hfr hTf hagf huniq hrest
      -- the δ-normal evidence, assembled in the family's extended scope at the copy's interface:
      -- `viewTy_mirrors` gives the params↔mirrors substitution under the scope's sort uniqueness,
      -- `ctorFieldsA_conv_norm` the per-field conversion from the δ evidence (R-NoDeltaRec-4d-iii).
      have hpre : PrefixA E (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) :=
        prefixA_extend E f _ hfr
      have hRT := iotaRecHeadTypedA_of hRf
      have hFam : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (famMemberA fm.arity pA iA fv.sort).mtypeA (.sort uf) := hasTyEnvA hpre hTf
      have op := viewTy_openFam (fv := famViewOfA fm.arity pA iA fv.sort hp) hEf hI hFam
        (members_extendEnvA_self E f _) (Nat.le_refl _) fv.sort
      have mcK := mirrorsConvA_env_iface hpre hag d.mc
      have hFamPi : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (piTelA pA (famViewOfA fm.arity pA iA fv.sort hp).idxTelA
            (piTelA iA (.sort fv.sort) (.succ fv.sort)).2).1 (.sort uf) := by
        simpa [famMemberA, piTelA_append, FamViewA.idxTelA] using hFam
      have mpack := viewTy_mirrors hEf hI hIS hRf huniq (substTyA_id hEf hI .nil) .nil .nil hFamPi mcK
      have ctxM : CtxWfA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms) := by simpa [List.append_nil] using mpack.ctxM
      have hσ : SubstTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms) SubstA.id (telCtxA pA) := by
        simpa [List.append_nil] using mpack.substTy
      have hdd : ∀ fsPre D idx fsRest,
          d.fs = fsPre ++ .drecD D idx :: fsRest →
          Nonempty (HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
            (plainCtxA fsPre (telCtxA pA)) D (.sort fv.sort)) ∧
          Nonempty (ConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
            (plainCtxA fsPre (telCtxA pA)) D
            (foldAppsA (.const f (canonLevelsA fm.arity))
              ((paramLocalsA pA.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
            (.sort fv.sort)) :=
        fun fsPre D idx fsRest hsplt =>
          match d.drecD_typed fsPre D idx fsRest hsplt with
          | ⟨⟨hd⟩, ⟨hc⟩, _⟩ => ⟨⟨hasTyIfaceA hagf hd⟩, ⟨convIfaceA hagf hc⟩⟩
      have hFT := fieldsTyA_env_iface hpre hag d.ft
      have hFp : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA pA)
          (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA pA.length))
          (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA) := by
        rw [liftA_zero]; exact op.atParams
      have hIdx : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA pA) (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA)
          (.sort (piTelA iA (.sort fv.sort) (.succ fv.sort)).2) := by
        rw [liftA_zero]; exact op.idxTy
      have hTel : IsIdxTel (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA) fv.sort := by
        rw [liftA_zero]; exact isIdxTel_piTel fv.sort (.succ fv.sort) iA
      have hpl : paramLocalsA d.ms.length =
          (paramLocalsA pA.length).map (substA SubstA.id) :=
        (congrArg paramLocalsA mcK.length).trans (map_substA_id _).symm
      have hplN : paramLocalsA d.ms.length =
          (paramLocalsA pA.length).map (liftA 0 0) :=
        (congrArg paramLocalsA mcK.length).trans (map_liftA_zero _).symm
      obtain ⟨hconv⟩ := ctorFieldsA_conv_norm hEf hI hRT hIS
        (fm := famMemberA fm.arity pA iA fv.sort) (fv := famViewOfA fm.arity pA iA fv.sort hp)
        (w := fv.sort) rfl hdd hσ op.ctxP ctxM
        (k := 0) (j := 0) (d := 0) (s := (piTelA iA (.sort fv.sort) (.succ fv.sort)).2)
        hpl hplN substA_walk_ge_id hFp hIdx hTel
        (List.nil_append _).symm rfl rfl rfl hFT
      -- the normed side's own typing: `viewTy_fields` on `FieldsTyA.norm`, whose `.drecD` arm is
      -- vacuous (`norm` erases the δ). The raw side follows by `convA_hasTy_left`.
      have hN := viewTy_fields hEf hI hRT hIS hσ op.ctxP ctxM hpl hFp hIdx hTel hFT.norm
        (fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact y.norm_noDelta)
      have hcfR := convA_hasTy_left hEf hI hRf hIS ctxM hconv
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
          SubstA.id (d.fs.map FieldA.norm) d.res).2 =
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hconv0 : ConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).1
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [List.append_nil]; exact hconv
      have hcfR0 : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [List.append_nil]; exact hcfR
      have hN0 : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id (d.fs.map FieldA.norm) d.res).2) := by
        rw [List.append_nil]; exact hN
      have hNs : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [← hsnd]; exact hN0
      have hFoldTy := viewTy_pi mpack.dom hcfR0
      have hFoldN := viewTy_pi mpack.dom hN0
      have hBcast : (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
            (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1
            (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
              d.fs d.res).2).1 =
          (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
            (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1
            (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
              (d.fs.map FieldA.norm) d.res).2).1 :=
        congrArg (fun w => (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
          (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1 w).1) hsnd.symm
      have hnc : Nonempty (TyConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res)
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms (d.fs.map FieldA.norm) d.res)) :=
        have hcF := convA_piTelA mpack.dom hconv0 hNs
        by rw [hBcast] at hcF
           exact ⟨.of _ _ _ _ _ _ hFoldTy (eqNA_refl _) hFoldN
             (fun ρ => by simp only [piTelA_snd]; rw [hsnd]) hcF⟩
      have hnt : ∃ l', Nonempty (HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K
          fm.arity []
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms (d.fs.map FieldA.norm) d.res)
          (.sort l')) := ⟨_, ⟨hFoldN⟩⟩
      obtain ⟨w, ⟨hT⟩⟩ := hT1 hE hEf hENC hNC hEL hELf hI hIS hIL hR hRf hfr rfl hTf
        (famViewOfA fm.arity pA iA fv.sort hp) (d.view (f := f) K hag hagf hnc hnt)
      have hmem := eraseMember_ctorMemberA c hm d.noFun
      have hty : erase (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res) = c.member.mtype :=
        congrArg CheckedMember.mtype hmem
      have hclT : ∀ k, liftA k 1 (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res) =
          ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res := fun k =>
        liftA_eq_of_erase _ k (by rw [hty]; exact c.hclT k)
      have hparams : ∀ j (P : ExprA) (u : Level), pA.get? j = some (P, u) →
          boundOkB j P = true := fun j P u hP => by
        rw [List.get?_eq_getElem?] at hP
        have hlt : j < pA.length := (List.getElem?_eq_some_iff.mp hP).1
        have h0 := (piTelA_boundOk_rev (pA ++ iA) (.sort fv.sort) (.succ fv.sort) 0
          (by simpa [famMemberA] using hasTyA_boundOk hTf)).1 j P u
        have hP' : (pA ++ iA).get? j = some (P, u) := by
          rw [List.get?_eq_getElem?]; exact (List.getElem?_append_left hlt (l₂ := iA)).trans hP
        exact Nat.zero_add j ▸ h0 hP'
      exact ⟨d.groupCtor hs K hag hagf c.ref hparams hclT w hT hnc hnt :: csA,
        .cons ⟨rfl, hmem, hm, d.noFun, rfl⟩ hcsA⟩

/-- THE CONSTRUCTORS TYPED, given `CtorTyOfViewSemA`. The caller supplies the base's semantics
    and `hag` is the agreement; this theorem does not choose either. -/
theorem ctorsTypedSem (hT1 : CtorTyOfViewSemA) {E : ResolvedEnvA} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {pA iA : List (ExprA × Level)} {hp : UniformProp fv.sort ∨ UniformType fv.sort}
    (hs : levelBounded fm.arity fv.sort = true) (K : IotaIfaceA) (hag : IfaceAgreeA E (iotaIfaceA E) K)
    {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀) (hSem : EnvSemA E (iotaIfaceA E) fm.arity ρ₀)
    (hE : EnvClosedA E) (hEf : EnvClosedA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)))
    (hEN : EnvNormClosedA E) (hENC : EnvNormCtorTypeA E)
    (hEL : EnvLevelsA E) (hELf : EnvLevelsA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)))
    (hI : IotaLiftA K) (hIS : IotaSubstA K) (hIL : IotaLevelsA K) (hR : IotaRecHeadA E K)
    (hRf : IotaRecHeadA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K)
    (hfr : E.members f = none) {uf : Level}
    (hTf : HasTyA E K fm.arity [] (famMemberA fm.arity pA iA fv.sort).mtypeA (.sort uf))
    (hagf : IfaceAgreeA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort))
      (iotaIfaceA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort))) K)
    (huniq : ViewTySortUniqA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity) :
    {cs : List (GroupCtorT (eraseEnv E) f fm fv)} → {ds : List (CtorCopyA E f fm.arity fv.sort pA iA)} →
    ListRel (fun c d => CtorMatches c d.ms d.fs d.res) cs ds →
    ∃ csA : List (GroupCtorA K E f (famMemberA fm.arity pA iA fv.sort) (famViewOfA fm.arity pA iA fv.sort hp)),
      ListRel CtorKeeps cs csA
  | _, _, .nil => ⟨[], .nil⟩
  | c :: _, d :: _, .cons hm hrest => by
      obtain ⟨csA, hcsA⟩ := ctorsTypedSem (hp := hp) hT1 hs K hag hρ hSem hE hEf hEN hENC hEL hELf
        hI hIS hIL hR hRf hfr hTf hagf huniq hrest
      -- the δ-normal evidence, as in `ctorsTyped`: the mirror substitution under the scope's sort
      -- uniqueness, the per-field conversion from the δ evidence (R-NoDeltaRec-4d-iii).
      have hpre : PrefixA E (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) :=
        prefixA_extend E f _ hfr
      have hRT := iotaRecHeadTypedA_of hRf
      have hFam : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (famMemberA fm.arity pA iA fv.sort).mtypeA (.sort uf) := hasTyEnvA hpre hTf
      have op := viewTy_openFam (fv := famViewOfA fm.arity pA iA fv.sort hp) hEf hI hFam
        (members_extendEnvA_self E f _) (Nat.le_refl _) fv.sort
      have mcK := mirrorsConvA_env_iface hpre hag d.mc
      have hFamPi : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (piTelA pA (famViewOfA fm.arity pA iA fv.sort hp).idxTelA
            (piTelA iA (.sort fv.sort) (.succ fv.sort)).2).1 (.sort uf) := by
        simpa [famMemberA, piTelA_append, FamViewA.idxTelA] using hFam
      have mpack := viewTy_mirrors hEf hI hIS hRf huniq (substTyA_id hEf hI .nil) .nil .nil hFamPi mcK
      have ctxM : CtxWfA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms) := by simpa [List.append_nil] using mpack.ctxM
      have hσ : SubstTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms) SubstA.id (telCtxA pA) := by
        simpa [List.append_nil] using mpack.substTy
      have hdd : ∀ fsPre D idx fsRest,
          d.fs = fsPre ++ .drecD D idx :: fsRest →
          Nonempty (HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
            (plainCtxA fsPre (telCtxA pA)) D (.sort fv.sort)) ∧
          Nonempty (ConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
            (plainCtxA fsPre (telCtxA pA)) D
            (foldAppsA (.const f (canonLevelsA fm.arity))
              ((paramLocalsA pA.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
            (.sort fv.sort)) :=
        fun fsPre D idx fsRest hsplt =>
          match d.drecD_typed fsPre D idx fsRest hsplt with
          | ⟨⟨hd⟩, ⟨hc⟩, _⟩ => ⟨⟨hasTyIfaceA hagf hd⟩, ⟨convIfaceA hagf hc⟩⟩
      have hFT := fieldsTyA_env_iface hpre hag d.ft
      have hFp : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA pA)
          (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA pA.length))
          (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA) := by
        rw [liftA_zero]; exact op.atParams
      have hIdx : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA pA) (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA)
          (.sort (piTelA iA (.sort fv.sort) (.succ fv.sort)).2) := by
        rw [liftA_zero]; exact op.idxTy
      have hTel : IsIdxTel (liftA 0 0 (famViewOfA fm.arity pA iA fv.sort hp).idxTelA) fv.sort := by
        rw [liftA_zero]; exact isIdxTel_piTel fv.sort (.succ fv.sort) iA
      have hpl : paramLocalsA d.ms.length =
          (paramLocalsA pA.length).map (substA SubstA.id) :=
        (congrArg paramLocalsA mcK.length).trans (map_substA_id _).symm
      have hplN : paramLocalsA d.ms.length =
          (paramLocalsA pA.length).map (liftA 0 0) :=
        (congrArg paramLocalsA mcK.length).trans (map_liftA_zero _).symm
      obtain ⟨hconv⟩ := ctorFieldsA_conv_norm hEf hI hRT hIS
        (fm := famMemberA fm.arity pA iA fv.sort) (fv := famViewOfA fm.arity pA iA fv.sort hp)
        (w := fv.sort) rfl hdd hσ op.ctxP ctxM
        (k := 0) (j := 0) (d := 0) (s := (piTelA iA (.sort fv.sort) (.succ fv.sort)).2)
        hpl hplN substA_walk_ge_id hFp hIdx hTel
        (List.nil_append _).symm rfl rfl rfl hFT
      have hN := viewTy_fields hEf hI hRT hIS hσ op.ctxP ctxM hpl hFp hIdx hTel hFT.norm
        (fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact y.norm_noDelta)
      have hcfR := convA_hasTy_left hEf hI hRf hIS ctxM hconv
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
          SubstA.id (d.fs.map FieldA.norm) d.res).2 =
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hconv0 : ConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).1
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [List.append_nil]; exact hconv
      have hcfR0 : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            d.fs d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [List.append_nil]; exact hcfR
      have hN0 : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id (d.fs.map FieldA.norm) d.res).2) := by
        rw [List.append_nil]; exact hN
      have hNs : HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity
          (telCtxA d.ms ++ [])
          (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
            (d.fs.map FieldA.norm) d.res).1
          (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length)
            SubstA.id d.fs d.res).2) := by
        rw [← hsnd]; exact hN0
      have hFoldTy := viewTy_pi mpack.dom hcfR0
      have hFoldN := viewTy_pi mpack.dom hN0
      have hBcast : (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
            (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1
            (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
              d.fs d.res).2).1 =
          (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
            (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1
            (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA d.ms.length) SubstA.id
              (d.fs.map FieldA.norm) d.res).2).1 :=
        congrArg (fun w => (piTelA d.ms (ctorFieldsA f (canonLevelsA fm.arity) fv.sort
          (paramLocalsA d.ms.length) SubstA.id (d.fs.map FieldA.norm) d.res).1 w).1) hsnd.symm
      have hnc : Nonempty (TyConvA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K fm.arity []
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res)
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms (d.fs.map FieldA.norm) d.res)) :=
        have hcF := convA_piTelA mpack.dom hconv0 hNs
        by rw [hBcast] at hcF
           exact ⟨.of _ _ _ _ _ _ hFoldTy (eqNA_refl _) hFoldN
             (fun ρ => by simp only [piTelA_snd]; rw [hsnd]) hcF⟩
      have hnt : ∃ l', Nonempty (HasTyA (extendEnvA E f (famMemberA fm.arity pA iA fv.sort)) K
          fm.arity []
          (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms (d.fs.map FieldA.norm) d.res)
          (.sort l')) := ⟨_, ⟨hFoldN⟩⟩
      obtain ⟨w, ⟨hT⟩⟩ := hT1 hE hEf hEN hENC hEL hELf hI hIS hIL hR hRf hfr rfl hTf
        (famViewOfA fm.arity pA iA fv.sort hp) (d.view (f := f) K hag hagf hnc hnt) ρ₀ hρ hSem hag
      have hmem := eraseMember_ctorMemberA c hm d.noFun
      have hty : erase (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res) = c.member.mtype :=
        congrArg CheckedMember.mtype hmem
      have hclT : ∀ k, liftA k 1 (ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res) =
          ctorTypeA f (canonLevelsA fm.arity) fv.sort d.ms d.fs d.res := fun k =>
        liftA_eq_of_erase _ k (by rw [hty]; exact c.hclT k)
      have hparams : ∀ j (P : ExprA) (u : Level), pA.get? j = some (P, u) →
          boundOkB j P = true := fun j P u hP => by
        rw [List.get?_eq_getElem?] at hP
        have hlt : j < pA.length := (List.getElem?_eq_some_iff.mp hP).1
        have h0 := (piTelA_boundOk_rev (pA ++ iA) (.sort fv.sort) (.succ fv.sort) 0
          (by simpa [famMemberA] using hasTyA_boundOk hTf)).1 j P u
        have hP' : (pA ++ iA).get? j = some (P, u) := by
          rw [List.get?_eq_getElem?]; exact (List.getElem?_append_left hlt (l₂ := iA)).trans hP
        exact Nat.zero_add j ▸ h0 hP'
      exact ⟨d.groupCtor hs K hag hagf c.ref hparams hclT w hT hnc hnt :: csA,
        .cons ⟨rfl, hmem, hm, d.noFun, rfl⟩ hcsA⟩

theorem groupFreshT_base {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} :
    {es : List (Nat × CheckedMember)} → GroupFreshT E f fm es → E.members f = none
  | [], h => h
  | _ :: _, h => groupFreshT_base h.1

theorem iotaRecHeadA_mono {E₀ E₁ : ResolvedEnvA} {I : IotaIfaceA} (h : IotaRecHeadA E₀ I)
    (hpre : PrefixA E₀ E₁) : IotaRecHeadA E₁ I := fun e e' he => by
  obtain ⟨r, ls, m, hh, hm, hc, hl⟩ := h e e' he
  exact ⟨r, ls, m, hh, hpre r m hm, hc, hl⟩

section Keeps
variable {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm} {K : IotaIfaceA}
  {EA : ResolvedEnvA} {fmA : CheckedMemberA} {fvA : FamViewA fmA}

theorem ListRel.keeps_entries : {cs : List (GroupCtorT E f fm fv)} → {csA : List (GroupCtorA K EA f fmA fvA)} →
    ListRel CtorKeeps cs csA →
    (csA.map GroupCtorA.entry).map (fun e => (e.1, eraseMember e.2)) = cs.map GroupCtorT.entry
  | _, _, .nil => rfl
  | _, _, .cons ⟨hr, hm, _, _⟩ t => by
      simp only [List.map_cons, GroupCtorA.entry, GroupCtorT.entry, hr, hm, ListRel.keeps_entries t]

theorem ListRel.keeps_refs : {cs : List (GroupCtorT E f fm fv)} → {csA : List (GroupCtorA K EA f fmA fvA)} →
    ListRel CtorKeeps cs csA → csA.map GroupCtorA.ref = cs.map GroupCtorT.ref
  | _, _, .nil => rfl
  | _, _, .cons ⟨hr, _, _, _⟩ t => by simp only [List.map_cons, hr, ListRel.keeps_refs t]

theorem ListRel.keeps_noFun : {cs : List (GroupCtorT E f fm fv)} → {csA : List (GroupCtorA K EA f fmA fvA)} →
    ListRel CtorKeeps cs csA → ∀ c ∈ csA, ∀ x ∈ c.view.fields, x.NoFun
  | _, _, .nil, _, hc => absurd hc (List.not_mem_nil _)
  | _, _, .cons ⟨_, _, _, hnf, _⟩ t, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hnf
      · exact ListRel.keeps_noFun t c hc

/-- every member a keeps-related copy carries the normed view type in `normA` (R-NoDeltaRec-3c). -/
theorem ListRel.keeps_normA : {cs : List (GroupCtorT E f fm fv)} → {csA : List (GroupCtorA K EA f fmA fvA)} →
    ListRel CtorKeeps cs csA →
    ∀ c ∈ csA, c.member.normA = some (ctorTypeA f (canonLevelsA fmA.arity) fvA.sort c.view.mirrors
      (c.view.fields.map FieldA.norm) c.view.res)
  | _, _, .nil, _, hc => absurd hc (List.not_mem_nil _)
  | _, _, .cons ⟨_, _, _, _, hnormA⟩ t, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hnormA
      · exact ListRel.keeps_normA t c hc

/-- `unlevel` reads the δ flag through: it only rewrites the plain field's level. -/
theorem FieldT.unlevel_isDrecD (t : FieldT) : t.unlevel.isDrecD = t.isDrecD := by cases t <;> rfl

/-- the scope's `.drecD`-free gate transfers along `CtorKeeps` to the copy's fields: erasure and
    `unlevel` both read the δ flag, so a copy field whose erasure maps onto a δ-free main field is
    itself δ-free. This is `EnvNormEraseA`'s group step (R-NoDeltaRec-4d-iii). -/
theorem ListRel.keeps_noDelta {cs : List (GroupCtorT E f fm fv)} {csA : List (GroupCtorA K EA f fmA fvA)} :
    (∀ c ∈ cs, ∀ d ∈ c.view.fields, d.isDrecD = false) → ListRel CtorKeeps cs csA →
    ∀ c ∈ csA, ∀ x ∈ c.view.fields, x.NoDelta
  | _, .nil, _, hc => absurd hc (List.not_mem_nil _)
  | hsnd, .cons ⟨_, _, hmat, _, _⟩ t, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · intro x hx
        apply FieldA.noDelta_of_erase
        have hm : (x.erase).unlevel ∈ (c.view.fields.map FieldA.erase).map FieldT.unlevel :=
          List.mem_map_of_mem _ (List.mem_map_of_mem _ hx)
        rw [hmat.2.1] at hm
        obtain ⟨y, hy, hye⟩ := List.mem_map.mp hm
        have h1 : x.erase.isDrecD = y.isDrecD := by
          rw [← FieldT.unlevel_isDrecD x.erase, ← hye, FieldT.unlevel_isDrecD]
        rw [h1]
        exact hsnd _ (List.mem_cons_self _ _) _ hy
      · exact ListRel.keeps_noDelta (fun c hc' d hd => hsnd c (List.mem_cons_of_mem _ hc') d hd) t c hc

theorem GroupCtorA.minorData_noFun_of_all {I : IotaIfaceA} {E₁ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₁ f fm fv)} (h : ∀ c ∈ cs, ∀ x ∈ c.view.fields, x.NoFun) :
    ∀ cd ∈ cs.map GroupCtorA.minorData, ∀ x ∈ cd.2.1, x.NoFun := fun _ hcd => by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcd
  exact h c hc

theorem GroupCtorA.minorData_noFun_of_keeps {cs : List (GroupCtorT E f fm fv)}
    {csA : List (GroupCtorA K EA f fmA fvA)} (hk : ListRel CtorKeeps cs csA) :
    ∀ cd ∈ csA.reverse.map GroupCtorA.minorData, ∀ x ∈ cd.2.1, x.NoFun :=
  GroupCtorA.minorData_noFun_of_all fun c hc => ListRel.keeps_noFun hk c (List.mem_reverse.mp hc)

/-- the minor data a typed copy keeps, up to recorded levels. -/
def minorUnlevel (cd : MinorDataT) : MinorDataT := (cd.1, cd.2.1.map FieldT.unlevel, cd.2.2)

theorem ListRel.keeps_minors : {cs : List (GroupCtorT E f fm fv)} → {csA : List (GroupCtorA K EA f fmA fvA)} →
    ListRel CtorKeeps cs csA →
    (csA.map (fun c => MinorDataA.erase c.minorData)).map minorUnlevel =
      (cs.map GroupCtorT.minorData).map minorUnlevel
  | _, _, .nil => rfl
  | _, _, .cons ⟨hr, _, ⟨_, hf, hres, _⟩, _, _⟩ t => by
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ListRel.keeps_minors t]
      congr 1
      simp only [MinorDataA.erase, GroupCtorA.minorData, GroupCtorT.minorData, minorUnlevel, hr, hf, hres]

/-- W-1 (e-3): THE COPY KEEPS A STRUCT GROUP. The typed copy of a struct group of main's views has one
    constructor, whose fields are plain as main's are, each at an instance of main's level and so zero.
    Over a family in `Prop` without index, at a motive whose level is not zero, its recursor passes the
    copy's struct test (`structGroupA_of_recTypeA`). -/
theorem structGroupA_of_keeps {cs : List (GroupCtorT E f fm fv)} {csA : List (GroupCtorA K EA f fmA fvA)}
    (hk : ListRel CtorKeeps cs csA) (hS : StructGroupT cs) {m : CheckedMemberA} {elim : RecElimA}
    (hst : m.mtypeA = groupRecTypeA fvA csA elim) (hidx : fvA.indices = [])
    (hz : levelIsZero fvA.sort = true) (hwM : levelIsZero (elim.motiveLevel fmA.arity) = false) :
    structGroupA (f + 1 + csA.length) m = true := by
  obtain ⟨hlen, -, hfs⟩ := hS
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
    match cs, hlen with
    | [c], _ => exact ⟨c, rfl⟩
  obtain ⟨cA, rfl, hkc⟩ : ∃ cA, csA = [cA] ∧ CtorKeeps c cA := by
    cases hk with
    | cons h t => cases t with
      | nil => exact ⟨_, rfl, h⟩
  obtain ⟨-, -, ⟨-, hfE, -, hlev⟩, hnfc, -⟩ := hkc
  obtain ⟨hne, hpl⟩ := hfs c (List.mem_singleton_self c)
  -- the copy's fields are plain: erasure keeps each field's kind, and main's are plain
  have hplA : ∀ F ∈ cA.view.fields, ∃ D u, F = .plain D u := by
    intro F hF
    have hm : FieldT.unlevel F.erase ∈ c.view.fields.map FieldT.unlevel := by
      rw [← hfE, List.map_map]; exact List.mem_map_of_mem _ hF
    obtain ⟨F', hF', hF'e⟩ := List.mem_map.mp hm
    obtain ⟨D', u', rfl, -⟩ := hpl F' hF'
    cases F with
    | plain D u => exact ⟨D, u, rfl⟩
    | frec _ _ _ _ => exact (hnfc _ hF).elim
    | _ => simp [FieldT.unlevel, FieldA.erase] at hF'e
  have hplain := fields_plainTelA _ hplA
  -- at least one field, as main has
  have hneA : plainTelA cA.view.fields ≠ [] := by
    intro h
    rw [h, List.map_nil] at hplain
    have hl := congrArg List.length hfE
    rw [hplain] at hl
    simp only [List.map_nil, List.length_nil, List.length_map] at hl
    exact hne (List.eq_nil_of_length_eq_zero hl.symm)
  -- each field's level is an instance of main's, which is zero at every valuation
  have hzds : ∀ d ∈ plainTelA cA.view.fields, levelIsZero d.2 = true := by
    intro d hd
    obtain ⟨D₀, u₀, ls, hmem, hu⟩ := hlev d.1 d.2 (mem_plainTelA _ hd)
    obtain ⟨D', u', he, hU⟩ := hpl _ hmem
    injection he with _ he2
    rw [hu, he2]
    exact (levelIsZero_iff _).mpr (uniformProp_eqN_zero (uniformProp_instLevel hU ls))
  have hst' : m.mtypeA = recTypeA f (canonLevelsA fmA.arity) fvA.params [] fvA.sort
      (elim.motiveLevel fmA.arity) [(cA.ref, (plainTelA cA.view.fields).map plainA, cA.view.res)] := by
    rw [hst]
    show recTypeA f (canonLevelsA fmA.arity) fvA.params fvA.indices fvA.sort (elim.motiveLevel fmA.arity)
      [(cA.ref, cA.view.fields, cA.view.res)] = _
    rw [hidx, ← hplain]
  exact structGroupA_of_recTypeA hst' hneA hzds rfl hz hwM

end Keeps

/-- a closed annotated telescope erases to main's, where main's terms are within the arity. -/
theorem closed_map_erase {a M : Nat} {ds : List (ExprA × Level)} {main : List (Expr Nat × Level)}
    (h : ds.map eraseDom = main) (hb : ∀ x ∈ main.map Prod.fst, exprLevelsBounded a x = true) :
    (instDomsA (closeLs a M) ds).map (fun d => erase d.1) = main.map Prod.fst := by
  rw [← h]
  simp only [instDomsA, List.map_map]
  apply List.map_congr_left
  intro d hd
  show erase (instantiateLevelsA _ d.1) = (eraseDom d).1
  apply erase_close_of_bounded
  apply hb
  rw [← h, List.map_map]; exact List.mem_map_of_mem _ hd

/-- THE GROUP STEP OF THE ENVIRONMENT BRIDGE (M3-e-2), given arc D's (T1) and (T2). A group in the
    copy's scope over a bridged base erases from the copy's `groupRec` over an annotation of that
    base. That `groupRec` is admitted at every interface that agrees with its own, and both profiles
    carry over. -/
theorem bridge_group (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) {EA0 : ResolvedEnvA} (C0 : AnnEnvA EA0)
    (hn : EnvNormEraseA EA0)
    (hW0 : ∀ J, IfaceAgreeA EA0 (iotaIfaceA EA0) J → Nonempty (EnvWfA J EA0))
    {f : Nat} {fm : CheckedMember} (hcls : fm.mclass = .inductiveM) (hnobody : fm.body = none)
    (hclT : ∀ k, lift k 1 fm.mtype = fm.mtype) (hlvl : exprLevelsBounded fm.arity fm.mtype = true)
    (fv : FamViewT fm) (htel : TelTyT (eraseEnv EA0) fm.arity [] (fv.params ++ fv.indices))
    (cs : List (GroupCtorT (eraseEnv EA0) f fm fv))
    (hfresh : GroupFreshT (eraseEnv EA0) f fm (cs.map GroupCtorT.entry))
    (hlayout : cs.reverse.map GroupCtorT.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecT (eraseEnv EA0) f fm fv cs)
    (hrfresh : (groupEnvT (eraseEnv EA0) f fm (cs.map GroupCtorT.entry)).members (f + 1 + cs.length) = none)
    (hprof : GroupProfileT rec)
    (hpb : ∀ d ∈ fv.params ++ fv.indices, levelBounded fm.arity d.2 = true)
    (hsnd : ∀ c ∈ cs, ∀ d ∈ c.view.fields, d.isDrecD = false)
    (hsmall0 : SmallIndexProfileA EA0) (hprop0 : PropElimStructA EA0) :
    ∃ EA : ResolvedEnvA, eraseEnv EA =
      groupRecEnvT cs rec ∧ SmallIndexProfileA EA ∧ PropElimStructA EA ∧ EnvNoFunA EA ∧
      EnvNormEraseA EA ∧ ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA) := by
  -- (0) the family's parts and sort, within its arity
  have hlvl' : exprLevelsBounded fm.arity
      (policyPi ((fv.params ++ fv.indices).map Prod.fst) (.sort fv.sort)) = true := by
    rw [← fv.stored]; exact hlvl
  obtain ⟨hpartsM, hsB⟩ := exprLevelsBounded_policyPi fm.arity _ _ hlvl'
  have hs : levelBounded fm.arity fv.sort = true := hsB
  have hs1 : levelBounded fm.arity (.succ fv.sort) = true := hsB
  have hfr : EA0.members f = none := members_none_of_erase (groupFreshT_base hfresh)
  -- (1) the family, annotated and closed
  obtain ⟨pA, iA, Mf, hpe, hie, hbf, ⟨tel⟩⟩ := famClosed C0 hn htel
  have tel' : TelTyA EA0 (iotaIfaceA EA0) fm.arity []
      (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA) := by
    have h := TelTyA.close C0.hEL C0.hIL fm.arity Mf tel
    rw [instDomsA_append] at h
    exact h
  have hpbD := (domsBoundedA_append hbf).1
  have hib := (domsBoundedA_append hbf).2
  have hpE : (instDomsA (closeLs fm.arity Mf) pA).map (fun d => erase d.1) = fv.params.map Prod.fst :=
    closed_map_erase hpe (fun x hx => hpartsM x (by rw [List.map_append]; exact List.mem_append_left _ hx))
  have hiE : (instDomsA (closeLs fm.arity Mf) iA).map (fun d => erase d.1) = fv.indices.map Prod.fst :=
    closed_map_erase hie (fun x hx => hpartsM x (by rw [List.map_append]; exact List.mem_append_right _ hx))
  have hTfam0 : HasTyA EA0 (iotaIfaceA EA0) fm.arity []
      (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
        fv.sort).mtypeA
      (.sort (piTelA (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA)
        (.sort fv.sort) (.succ fv.sort)).2) :=
    hasTyA_piTelA tel' (by rw [telCtxA_append_nil]; exact .sort _ _)
  have hfamTyE : erase (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA = fm.mtype := by
    show erase (piTelA _ _ _).1 = _
    rw [erase_piTelA, List.map_append, hpE, hiE, fv.stored, List.map_append]
    rfl
  have hfmE : eraseMember (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort) = fm := by
    calc eraseMember (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
          (instDomsA (closeLs fm.arity Mf) iA) fv.sort)
        = ⟨fm.mclass, fm.arity, fm.mtype, fm.body⟩ := by
          have h' : erase (piTelA (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA)
              (.sort fv.sort) (.succ fv.sort)).1 = fm.mtype := hfamTyE
          simp only [eraseMember, famMemberA, hcls, hnobody, Option.map_none', h']
      _ = fm := rfl
  have hclTA : ∀ k, liftA k 1 (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA =
      (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
        fv.sort).mtypeA := fun k =>
    liftA_eq_of_erase _ k (by rw [hfamTyE]; exact hclT k)
  have hlvlA : exprLevelsBoundedA fm.arity (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA = true :=
    (piTelA_bounded_fwd fm.arity (.sort fv.sort) (.succ fv.sort) hs hs1 _
      (by rw [← instDomsA_append]; exact domsBoundedA_close hbf)).1
  let fmA := famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
    fv.sort
  let fvA := famViewOfA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
    fv.sort fv.profile
  -- the family-scope annotation env, before the constructors' walk needs it (R-NoDeltaRec-4d-ii)
  obtain ⟨hW0I0⟩ := hW0 _ (IfaceAgreeA.refl _ _)
  have hpreA : PrefixA EA0 (extendEnvA EA0 f fmA) := prefixA_extend EA0 f fmA hfr
  have hag0' : IfaceAgreeA EA0 (iotaIfaceA EA0) (iotaIfaceA (extendEnvA EA0 f fmA)) :=
    ifaceAgreeA_prefix hW0I0 hpreA
  obtain ⟨hW0I'⟩ := hW0 _ hag0'
  have hWf' : EnvWfA (iotaIfaceA (extendEnvA EA0 f fmA)) (extendEnvA EA0 f fmA) :=
    .group EA0 f fmA _ hW0I' rfl rfl hclTA (hasTyIfaceA hag0' hTfam0) hlvlA fvA [] hfr
  have hC' : AnnEnvA (extendEnvA EA0 f fmA) :=
    ⟨⟨hWf'⟩,
      smallIndexProfileA_fam (idxLevels_small_close hie hprof.1 hs) hsmall0 hfr,
      propElimStructA_extendFam hW0I' hfr (fun h => MemberClass.noConfusion h) hprop0,
      envNoFunA_extend hW0I' C0.noFun hfr (fun h => MemberClass.noConfusion h)⟩
  -- (2) the constructors, annotated and closed
  have hpl : ∀ d ∈ pA, levelBounded fm.arity d.2 = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.params := by rw [← hpe]; exact List.mem_map_of_mem _ hd
    exact hpb _ (List.mem_append_left _ hm)
  have hil : ∀ d ∈ iA, levelBounded fm.arity d.2 = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.indices := by rw [← hie]; exact List.mem_map_of_mem _ hd
    exact hpb _ (List.mem_append_right _ hm)
  obtain ⟨ds, hds⟩ := ctorsClosed C0 hn hs hpe hie tel hbf hpl hil hpartsM cs hfmE hfr hC' hpreA rfl rfl rfl
  -- (3) the family alone, admitted; the constructors typed by (T1) at its interface
  have hWf : EnvWfA (iotaIfaceA EA0) (extendEnvA EA0 f fmA) :=
    .group EA0 f fmA _ hW0I0 rfl rfl hclTA hTfam0 hlvlA fvA [] hfr
  have hEf := envWfA_closed hWf
  have hELf := envWfA_levels hWf
  have hENf := envWfA_normClosed hWf
  have hENLf := envWfA_normLevels hWf
  have hRf' : IotaRecHeadA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA)) := iotaFnA_recHead _
  have hR0' : IotaRecHeadA EA0 (iotaIfaceA (extendEnvA EA0 f fmA)) :=
    recHead_of_groupEnvA (fm := fmA) (es := []) rfl (fun _ h => absurd h (List.not_mem_nil _)) hRf'
  obtain ⟨csI', hcsI'⟩ := ctorsTyped (hp := fv.profile) hT1 hs _ hag0' C0.hE hEf C0.hENC C0.hEN
    C0.hEL hELf
    (iotaFnA_lift hEf hENf) (iotaFnA_subst hEf hENf) (iotaFnA_levels hELf hENLf) hR0' hRf' hfr
    (hasTyIfaceA hag0' hTfam0) (IfaceAgreeA.refl _ _)
    (fun hΓ ha hb => sortUniqA_rec hWf' hC'.small hC'.propElim hΓ ha hb) hds
  -- (4) the group without its recursor, admitted; the recursor typed by (T2) at its interface
  have hentries := hcsI'.keeps_entries
  have hlen : csI'.length = cs.length := hcsI'.length_eq.symm
  have hfreshA : GroupFreshA EA0 f fmA (csI'.map GroupCtorA.entry) :=
    groupFreshA_of_erase _ (by rw [hentries, hfmE]; exact hfresh)
  obtain ⟨hW0I'⟩ := hW0 _ hag0'
  have hWg : EnvWfA (iotaIfaceA (extendEnvA EA0 f fmA)) (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) :=
    .group EA0 f fmA _ hW0I' rfl rfl hclTA (hasTyIfaceA hag0' hTfam0) hlvlA fvA csI' hfreshA
  have hagf'' : IfaceAgreeA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA))
      (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    ifaceAgreeA_prefix hWf (prefixA_extend_groupEnvA hfreshA)
  have hag0'' : IfaceAgreeA EA0 (iotaIfaceA EA0) (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    ifaceAgreeA_prefix hW0I0 (prefixA_groupEnvA hfreshA)
  have hEg := envWfA_closed hWg
  have hELg := envWfA_levels hWg
  have hENg := envWfA_normClosed hWg
  have hENLg := envWfA_normLevels hWg
  have hRg : IotaRecHeadA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))
      (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) := iotaFnA_recHead _
  have hctorcls : ∀ e ∈ csI'.map GroupCtorA.entry, e.2.mclass = .constructorM := fun e he => by
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp he; exact c.hcls
  have hR0g : IotaRecHeadA EA0 (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    recHead_of_groupEnvA (fm := fmA) rfl hctorcls hRg
  have hRfg := iotaRecHeadA_mono hR0g (prefixA_extend EA0 f fmA hfr)
  have hentries'' := GroupCtorA.iface_entries hagf'' hfr csI'
  obtain ⟨wR, ⟨hTrec⟩⟩ := hT2 (csI'.map (GroupCtorA.iface hagf'' hfr)) rec.elim.toA C0.hE
    (by rw [hentries'']; exact hEg) C0.hENC C0.hEN C0.hEL (by rw [hentries'']; exact hELg)
    (iotaFnA_lift hEg hENg)
    (iotaFnA_subst hEg hENg) (iotaFnA_levels hELg hENLg) hR0g hRfg (by rw [hentries'']; exact hRg)
    (by rw [hentries'']; exact hfreshA) rfl (hasTyIfaceA hag0'' hTfam0)
  rw [hentries''] at hTrec
  have hrecTy : groupRecTypeA fvA (csI'.map (GroupCtorA.iface hagf'' hfr)) rec.elim.toA =
      groupRecTypeA fvA csI' rec.elim.toA := by
    simp only [groupRecTypeA, GroupCtorA.iface_minors]
  rw [hrecTy] at hTrec
  -- (5) the recursor member and the copy's environment
  let rmA : CheckedMemberA :=
    ⟨.recursorM, fm.arity + rec.elim.toA.extra, groupRecTypeA fvA csI' rec.elim.toA, none, 0, none⟩
  have hrfreshA : (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)).members (f + 1 + csI'.length) = none :=
    members_none_of_erase (by rw [eraseEnv_groupEnvA, hentries, hfmE, hlen]; exact hrfresh)
  have hminE : ((csI'.reverse.map GroupCtorA.minorData).map MinorDataA.erase).map minorUnlevel =
      (cs.reverse.map GroupCtorT.minorData).map minorUnlevel := by
    have h := hcsI'.keeps_minors
    simp only [List.map_map] at h
    simp only [List.map_map, List.map_reverse]
    exact congrArg List.reverse h
  have hrecTyE : erase (groupRecTypeA fvA csI' rec.elim.toA) = rec.member.mtype := by
    rw [rec.stored]
    show erase (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort (rec.elim.toA.motiveLevel fm.arity) _) = _
    rw [erase_recTypeA _ _ _ _ _ _ _ (GroupCtorA.minorData_noFun_of_keeps hcsI'),
      EliminationPolicy.toA_motiveLevel]
    apply recTypeT_congr
    · rw [List.map_map]; exact hpE
    · rw [List.map_map]; exact hiE
    · exact hminE
  have hrmE : eraseMember rmA = rec.member := by
    have hc := rec.hcls
    have hn := rec.hnobody
    have ha := rec.harity
    rw [← EliminationPolicy.toA_arity] at ha
    calc eraseMember rmA = ⟨rec.member.mclass, rec.member.arity, rec.member.mtype, rec.member.body⟩ := by
          simp only [eraseMember, rmA, hc, hn, ha, hrecTyE, Option.map_none']
      _ = rec.member := rfl
  have hclTR : ∀ k, liftA k 1 rmA.mtypeA = rmA.mtypeA := fun k =>
    liftA_eq_of_erase _ k (by show lift k 1 (erase (groupRecTypeA fvA csI' rec.elim.toA)) = _
                              rw [hrecTyE]; exact rec.hclT k)
  have hlvlR : exprLevelsBoundedA rmA.arity rmA.mtypeA = true := by
    show exprLevelsBoundedA (fm.arity + rec.elim.toA.extra)
      (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort (rec.elim.toA.motiveLevel fm.arity) _) = true
    have hk : fm.arity ≤ fm.arity + rec.elim.toA.extra := Nat.le_add_right _ _
    apply recTypeA_bounded_fwd
    · exact levelsBounded_mono hk _ (levelsBounded_canonA fm.arity)
    · exact levelBounded_mono hk _ hs
    · cases h : rec.elim <;> simp [EliminationPolicy.toA, RecElimA.motiveLevel, RecElimA.extra, levelBounded]
    · exact domsBoundedA_mono hk (domsBoundedA_close hpbD)
    · exact domsBoundedA_mono hk (domsBoundedA_close hib)
    · intro cd hcd
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcd
      have hl := c.hlvl
      rw [c.view.stored, c.harity] at hl
      have hfr' := (piTelA_bounded fm.arity _ _ _ hl).2
      obtain ⟨hF, hR⟩ := ctorFieldsA_bounded fm.arity f _ _ _ _ _ _
        (fun D idx hd => drecDTypedA_idxBounded c.view.drecD_typed hd) hfr'
      exact ⟨fun F hF' => FieldA.BoundedA.mono hk (hF F hF'),
        fun x hx => exprLevelsBoundedA_mono hk _ (hR x hx)⟩
  refine ⟨extendEnvA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) (f + 1 + csI'.length) rmA,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eraseEnv_extend, eraseEnv_groupEnvA, hentries, hfmE, hrmE, hlen]
    rfl
  · -- (O2) the new family's indices are sorted within its sort; the rest is the base's
    intro r m u₀ hm hcl hbody v hv ρ x y hx hy hpos
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hm
      cases hm
      exact MemberClass.noConfusion hcl
    · rw [members_extendEnvA_ne _ _ _ hr] at hm
      rcases members_groupEnvA _ r m hm with ⟨rfl, rfl⟩ | hin | hbase
      · -- the family: its index sorts are main's recorded ones, closed
        have hb : piBodyA fmA.mtypeA = .sort fv.sort := by
          show piBodyA (piTelA _ _ _).1 = _
          rw [piBodyA_piTelA]; rfl
        rw [hb] at hbody
        cases hbody
        have hdl : (piDomLevelsA fmA.mtypeA).drop fmA.nparamsA =
            (instDomsA (closeLs fm.arity Mf) iA).map Prod.snd := by
          show (piDomLevelsA (piTelA _ _ _).1).drop (instDomsA (closeLs fm.arity Mf) pA).length = _
          rw [piDomLevelsA_piTelA, List.map_append, List.append_assoc,
            List.drop_left' (by simp)]
          show _ ++ ([] : List Level) = _
          rw [List.append_nil]
        rw [hdl] at hv
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
        obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hd
        have hv₀ : d₀.2 ∈ fv.indices.map Prod.snd := by
          rw [← hie, List.map_map]; exact List.mem_map_of_mem (fun d => (eraseDom d).2) hd₀
        have hx' : eval (fun i => eval ρ (((closeLs fm.arity Mf)[i]?).getD (.param i))) d₀.2 = some x := by
          rw [← eval_instLevel]; exact hx
        have hy' : eval (fun i => eval ρ (((closeLs fm.arity Mf)[i]?).getD (.param i))) fv.sort = some y := by
          rw [← eval_instLevel, instLevel_closeLs_of_bounded fv.sort hs]; exact hy
        exact hprof.1 d₀.2 hv₀ _ x y hx' hy' hpos
      · obtain ⟨c, _, hc⟩ := List.mem_map.mp hin
        have hm' : c.member = m := (Prod.mk.inj hc).2
        rw [← hm', c.hcls] at hcl
        exact MemberClass.noConfusion hcl
      · exact hsmall0 r m u₀ hbase hcl hbody v hv ρ x y hx hy hpos
  · -- (O1) the new recursor eliminates into `Prop` where its family is a proposition with a constructor
    -- (O1-a exempts a group without one); the rest is the base's, whose recursors name only base families
    intro r rm D f' ls' fm' u₀ hrm hcl hlast hhead hfm' hfcl hbody hprop hne hun hns M hM
    have hpreG := prefixA_extend (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) _ rmA hrfreshA
    have hpre0 := prefixA_trans (prefixA_groupEnvA hfreshA) hpreG
    have hpref := prefixA_trans (prefixA_extend_groupEnvA hfreshA) hpreG
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hrm
      cases hrm
      change (piDomsA (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort _ _)).getLast? = some D at hlast
      rw [piDomsA_recTypeA_getLast] at hlast
      cases hlast
      rw [appsSpineA_majorDom] at hhead
      cases hhead
      rw [hpref f fmA (members_extendEnvA_self EA0 f fmA)] at hfm'
      cases hfm'
      have hb : piBodyA fmA.mtypeA = .sort fv.sort := by
        show piBodyA (piTelA _ _ _).1 = _
        rw [piBodyA_piTelA]; rfl
      rw [hb] at hbody
      cases hbody
      have hpo : rec.elim = .propOnly := by
        cases helim : rec.elim with
        | propOnly => rfl
        | anySort =>
            -- (O1) exempts a unit group and a struct group. At a motive of any sort the copy's
            -- recursor passes the copy's test for each, which `hun` and `hns` refute.
            have h := hprof.2 hprop (fun h => hne (by rw [hlen, h]; rfl)) (fun hU => by
              -- O1-b-2: at a unit group the copy's recursor passes the unit test, which `hun` refutes
              obtain ⟨hU1, hU2, hU3⟩ := hU
              have hiA : instDomsA (closeLs fm.arity Mf) iA = [] := by
                have h := hiE
                rw [hU2, List.map_nil] at h
                exact List.map_eq_nil_iff.mp h
              obtain ⟨gcA, hgcA⟩ : ∃ gc, csI'.reverse = [gc] := by
                match csI'.reverse, (List.length_reverse csI').trans (hlen.trans hU1) with
                | [gc], _ => exact ⟨gc, rfl⟩
              obtain ⟨gcT, hgcT⟩ : ∃ gc, cs.reverse = [gc] := by
                match cs.reverse, (List.length_reverse cs).trans hU1 with
                | [gc], _ => exact ⟨gc, rfl⟩
              have hfT : gcT.view.fields = [] :=
                hU3 gcT (List.mem_reverse.mp (by rw [hgcT]; exact List.mem_singleton_self _))
              have hfA : gcA.view.fields = [] := by
                have h := congrArg (fun l => l.map (fun cd => cd.2.1.length)) hminE
                rw [hgcA, hgcT] at h
                simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, GroupCtorT.minorData,
                  MinorDataA.erase, minorUnlevel, List.length_map, hfT, List.length_nil, List.cons.injEq,
                  and_true] at h
                exact List.eq_nil_of_length_eq_zero h.1
              have hmd : csI'.reverse.map GroupCtorA.minorData = [gcA.minorData] := by rw [hgcA]; rfl
              have hst : rmA.mtypeA = recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA) []
                  fv.sort (rec.elim.toA.motiveLevel fm.arity) [gcA.minorData] := by
                show recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA)
                  (instDomsA (closeLs fm.arity Mf) iA) fv.sort (rec.elim.toA.motiveLevel fm.arity)
                  (csI'.reverse.map GroupCtorA.minorData) = _
                rw [hmd]
                exact congrArg (fun I => recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA) I fv.sort
                  (rec.elim.toA.motiveLevel fm.arity) [gcA.minorData]) hiA
              have hu := unitGroupA_of_recTypeA (r := f + 1 + csI'.length) hst hfA (by rw [hlen, hU1])
                ((levelIsZero_iff _).mpr (uniformProp_eqN_zero hprop))
              rw [hu] at hun
              exact Bool.noConfusion hun) (fun hS => by
                -- W-1 (e-3): at a struct group, the struct test
                have hiA : instDomsA (closeLs fm.arity Mf) iA = [] := by
                  have h := hiE
                  rw [hS.2.1, List.map_nil] at h
                  exact List.map_eq_nil_iff.mp h
                have hsg := structGroupA_of_keeps hcsI' hS (m := rmA) (elim := rec.elim.toA) rfl hiA
                  ((levelIsZero_iff _).mpr (uniformProp_eqN_zero hprop)) (by rw [helim]; rfl)
                rw [hsg] at hns
                exact Bool.noConfusion hns)
            rw [helim] at h
            cases h
      change (piDomsA (recTypeA f (canonLevelsA fm.arity) fvA.params fvA.indices fv.sort _ _))[
        fvA.params.length]? = some M at hM
      rw [piDomsA_recTypeA_motive] at hM
      cases hM
      rw [piBodyA_motTyA, hpo]
      rfl
    · rw [members_extendEnvA_ne _ _ _ hr] at hrm
      rcases members_groupEnvA _ r rm hrm with ⟨rfl, rfl⟩ | hin | hbase
      · exact MemberClass.noConfusion hcl
      · obtain ⟨c, _, hc⟩ := List.mem_map.mp hin
        have hm' : c.member = rm := (Prod.mk.inj hc).2
        rw [← hm', c.hcls] at hcl
        exact MemberClass.noConfusion hcl
      · exact propElimStructA_base hW0I0 hpre0 hprop0 hbase hcl hlast hhead hfm' hfcl hbody hprop hne hun hns M hM
  · exact envNoFunA_groupRec hW0I0 C0.noFun hfreshA hrfreshA
      (ListRel.keeps_noFun hcsI') (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
  · -- `EnvNormEraseA` of the group env: only `.constructorM` members are constrained; the scope's
    -- `hsnd` makes each keeps-related copy field δ-free, so `norm` is the identity on them and the
    -- normed stored type erases to the stored one (R-NoDeltaRec-4d-iii).
    intro r m hm hcl T hT
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hm
      cases hm
      exact MemberClass.noConfusion hcl
    · rw [members_extendEnvA_ne _ _ _ hr] at hm
      rcases members_groupEnvA _ r m hm with ⟨rfl, rfl⟩ | hin | hbase
      · exact MemberClass.noConfusion hcl
      · obtain ⟨gc, hgc, hge⟩ := List.mem_map.mp hin
        have hgm : gc.member = m := congrArg Prod.snd hge
        subst hgm
        have hTe : T = ctorTypeA f (canonLevelsA fmA.arity) fvA.sort gc.view.mirrors
            (gc.view.fields.map FieldA.norm) gc.view.res :=
          Option.some.inj (hT.symm.trans (hcsI'.keeps_normA gc hgc))
        subst hTe
        rw [gc.view.stored, FieldA.map_norm_self (hcsI'.keeps_noDelta hsnd gc hgc)]
      · exact hn r m hbase hcl T hT
  · intro J hJ
    have hpreG := prefixA_extend (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) _ rmA hrfreshA
    have hpre0 := prefixA_trans (prefixA_groupEnvA hfreshA) hpreG
    have hpref := prefixA_trans (prefixA_extend_groupEnvA hfreshA) hpreG
    have hagJ0 : IfaceAgreeA EA0 (iotaIfaceA EA0) J :=
      (ifaceAgreeA_prefix hW0I0 hpre0).trans (hJ.prefix hpre0)
    have hagJf : IfaceAgreeA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA)) J :=
      (ifaceAgreeA_prefix hWf hpref).trans (hJ.prefix hpref)
    have hagJg : IfaceAgreeA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))
        (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) J :=
      (ifaceAgreeA_prefix hWg hpreG).trans (hJ.prefix hpreG)
    obtain ⟨hW0J⟩ := hW0 J hagJ0
    have hentJ := GroupCtorA.iface_entries hagJf hfr csI'
    have hrefJ := GroupCtorA.iface_refs hagJf hfr csI'
    have hlenJ : (csI'.map (GroupCtorA.iface hagJf hfr)).length = csI'.length := List.length_map _ _
    let recJ : GroupRecA J EA0 f fmA fvA (csI'.map (GroupCtorA.iface hagJf hfr)) :=
      { member := rmA
        hcls := rfl
        hnobody := rfl
        hnp := rfl
        elim := rec.elim.toA
        harity := rfl
        stored := by
          show groupRecTypeA fvA csI' rec.elim.toA = _
          simp only [groupRecTypeA, GroupCtorA.iface_minors]
        hclT := hclTR
        u := wR
        hT := by rw [hentJ]; exact hasTyIfaceA hagJg hTrec
        hlvl := hlvlR }
    have hW := EnvWfA.groupRec EA0 f fmA _ hW0J rfl rfl hclTA (hasTyIfaceA hagJ0 hTfam0) hlvlA fvA
      (csI'.map (GroupCtorA.iface hagJf hfr)) (by rw [hentJ]; exact hfreshA)
      (by rw [hrefJ, hlenJ, List.map_reverse, hcsI'.keeps_refs, ← List.map_reverse, hlayout, hlen])
      recJ (by rw [hentJ, hlenJ]; exact hrfreshA)
    have hEnv : groupRecEnvA (csI'.map (GroupCtorA.iface hagJf hfr)) recJ =
        extendEnvA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) (f + 1 + csI'.length) rmA := by
      simp only [groupRecEnvA, hentJ, hlenJ]
    exact ⟨hEnv ▸ hW⟩

/-- THE GROUP STEP, given the semantic-prefix typings. The base's semantics are the strict prefix's:
    `hW0` at `iotaIfaceA EA0`, with `hsmall0` and `hprop0`, through `envSemA_of_envWfA_recStruct` at
    `ρ₀ := fun _ => 1`. Agreement is `hag0'` for (T1) and `hag0''` for (T2). The group environment
    being built is not given to `EnvSemA`. This is not a proof of `CtorTyOfViewA` or `RecTyOfViewsA`. -/
theorem bridge_groupSem (hT1 : CtorTyOfViewSemA) (hT2 : RecTyOfViewsSemA) {EA0 : ResolvedEnvA} (C0 : AnnEnvA EA0)
    (hn : EnvNormEraseA EA0)
    (hW0 : ∀ J, IfaceAgreeA EA0 (iotaIfaceA EA0) J → Nonempty (EnvWfA J EA0))
    {f : Nat} {fm : CheckedMember} (hcls : fm.mclass = .inductiveM) (hnobody : fm.body = none)
    (hclT : ∀ k, lift k 1 fm.mtype = fm.mtype) (hlvl : exprLevelsBounded fm.arity fm.mtype = true)
    (fv : FamViewT fm) (htel : TelTyT (eraseEnv EA0) fm.arity [] (fv.params ++ fv.indices))
    (cs : List (GroupCtorT (eraseEnv EA0) f fm fv))
    (hfresh : GroupFreshT (eraseEnv EA0) f fm (cs.map GroupCtorT.entry))
    (hlayout : cs.reverse.map GroupCtorT.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecT (eraseEnv EA0) f fm fv cs)
    (hrfresh : (groupEnvT (eraseEnv EA0) f fm (cs.map GroupCtorT.entry)).members (f + 1 + cs.length) = none)
    (hprof : GroupProfileT rec)
    (hpb : ∀ d ∈ fv.params ++ fv.indices, levelBounded fm.arity d.2 = true)
    (hsnd : ∀ c ∈ cs, ∀ d ∈ c.view.fields, d.isDrecD = false)
    (hsmall0 : SmallIndexProfileA EA0) (hprop0 : PropElimStructA EA0) :
    ∃ EA : ResolvedEnvA, eraseEnv EA =
      groupRecEnvT cs rec ∧ SmallIndexProfileA EA ∧ PropElimStructA EA ∧ EnvNoFunA EA ∧
      EnvNormEraseA EA ∧ ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA) := by
  -- (0) the family's parts and sort, within its arity
  have hlvl' : exprLevelsBounded fm.arity
      (policyPi ((fv.params ++ fv.indices).map Prod.fst) (.sort fv.sort)) = true := by
    rw [← fv.stored]; exact hlvl
  obtain ⟨hpartsM, hsB⟩ := exprLevelsBounded_policyPi fm.arity _ _ hlvl'
  have hs : levelBounded fm.arity fv.sort = true := hsB
  have hs1 : levelBounded fm.arity (.succ fv.sort) = true := hsB
  have hfr : EA0.members f = none := members_none_of_erase (groupFreshT_base hfresh)
  -- (1) the family, annotated and closed
  obtain ⟨pA, iA, Mf, hpe, hie, hbf, ⟨tel⟩⟩ := famClosed C0 hn htel
  have tel' : TelTyA EA0 (iotaIfaceA EA0) fm.arity []
      (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA) := by
    have h := TelTyA.close C0.hEL C0.hIL fm.arity Mf tel
    rw [instDomsA_append] at h
    exact h
  have hpbD := (domsBoundedA_append hbf).1
  have hib := (domsBoundedA_append hbf).2
  have hpE : (instDomsA (closeLs fm.arity Mf) pA).map (fun d => erase d.1) = fv.params.map Prod.fst :=
    closed_map_erase hpe (fun x hx => hpartsM x (by rw [List.map_append]; exact List.mem_append_left _ hx))
  have hiE : (instDomsA (closeLs fm.arity Mf) iA).map (fun d => erase d.1) = fv.indices.map Prod.fst :=
    closed_map_erase hie (fun x hx => hpartsM x (by rw [List.map_append]; exact List.mem_append_right _ hx))
  have hTfam0 : HasTyA EA0 (iotaIfaceA EA0) fm.arity []
      (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
        fv.sort).mtypeA
      (.sort (piTelA (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA)
        (.sort fv.sort) (.succ fv.sort)).2) :=
    hasTyA_piTelA tel' (by rw [telCtxA_append_nil]; exact .sort _ _)
  have hfamTyE : erase (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA = fm.mtype := by
    show erase (piTelA _ _ _).1 = _
    rw [erase_piTelA, List.map_append, hpE, hiE, fv.stored, List.map_append]
    rfl
  have hfmE : eraseMember (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort) = fm := by
    calc eraseMember (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
          (instDomsA (closeLs fm.arity Mf) iA) fv.sort)
        = ⟨fm.mclass, fm.arity, fm.mtype, fm.body⟩ := by
          have h' : erase (piTelA (instDomsA (closeLs fm.arity Mf) pA ++ instDomsA (closeLs fm.arity Mf) iA)
              (.sort fv.sort) (.succ fv.sort)).1 = fm.mtype := hfamTyE
          simp only [eraseMember, famMemberA, hcls, hnobody, Option.map_none', h']
      _ = fm := rfl
  have hclTA : ∀ k, liftA k 1 (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA =
      (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
        fv.sort).mtypeA := fun k =>
    liftA_eq_of_erase _ k (by rw [hfamTyE]; exact hclT k)
  have hlvlA : exprLevelsBoundedA fm.arity (famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA)
      (instDomsA (closeLs fm.arity Mf) iA) fv.sort).mtypeA = true :=
    (piTelA_bounded_fwd fm.arity (.sort fv.sort) (.succ fv.sort) hs hs1 _
      (by rw [← instDomsA_append]; exact domsBoundedA_close hbf)).1
  let fmA := famMemberA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
    fv.sort
  let fvA := famViewOfA fm.arity (instDomsA (closeLs fm.arity Mf) pA) (instDomsA (closeLs fm.arity Mf) iA)
    fv.sort fv.profile
  -- the family-scope annotation env, before the constructors' walk needs it (R-NoDeltaRec-4d-ii)
  obtain ⟨hW0I0⟩ := hW0 _ (IfaceAgreeA.refl _ _)
  have hpreA : PrefixA EA0 (extendEnvA EA0 f fmA) := prefixA_extend EA0 f fmA hfr
  have hag0' : IfaceAgreeA EA0 (iotaIfaceA EA0) (iotaIfaceA (extendEnvA EA0 f fmA)) :=
    ifaceAgreeA_prefix hW0I0 hpreA
  obtain ⟨hW0I'⟩ := hW0 _ hag0'
  have hWf' : EnvWfA (iotaIfaceA (extendEnvA EA0 f fmA)) (extendEnvA EA0 f fmA) :=
    .group EA0 f fmA _ hW0I' rfl rfl hclTA (hasTyIfaceA hag0' hTfam0) hlvlA fvA [] hfr
  have hC' : AnnEnvA (extendEnvA EA0 f fmA) :=
    ⟨⟨hWf'⟩,
      smallIndexProfileA_fam (idxLevels_small_close hie hprof.1 hs) hsmall0 hfr,
      propElimStructA_extendFam hW0I' hfr (fun h => MemberClass.noConfusion h) hprop0,
      envNoFunA_extend hW0I' C0.noFun hfr (fun h => MemberClass.noConfusion h)⟩
  -- (2) the constructors, annotated and closed
  have hpl : ∀ d ∈ pA, levelBounded fm.arity d.2 = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.params := by rw [← hpe]; exact List.mem_map_of_mem _ hd
    exact hpb _ (List.mem_append_left _ hm)
  have hil : ∀ d ∈ iA, levelBounded fm.arity d.2 = true := by
    intro d hd
    have hm : eraseDom d ∈ fv.indices := by rw [← hie]; exact List.mem_map_of_mem _ hd
    exact hpb _ (List.mem_append_right _ hm)
  obtain ⟨ds, hds⟩ := ctorsClosed C0 hn hs hpe hie tel hbf hpl hil hpartsM cs hfmE hfr hC' hpreA rfl rfl rfl
  -- (3) the family alone, admitted; the constructors typed by (T1) at its interface
  have hSem0 : EnvSemA EA0 (iotaIfaceA EA0) fm.arity (fun _ => 1) :=
    envSemA_of_envWfA_recStruct (n := fm.arity) (ρ₀ := fun _ => 1) hW0I0 posValA_one hsmall0 hprop0
  have hWf : EnvWfA (iotaIfaceA EA0) (extendEnvA EA0 f fmA) :=
    .group EA0 f fmA _ hW0I0 rfl rfl hclTA hTfam0 hlvlA fvA [] hfr
  have hEf := envWfA_closed hWf
  have hELf := envWfA_levels hWf
  have hENf := envWfA_normClosed hWf
  have hENLf := envWfA_normLevels hWf
  have hRf' : IotaRecHeadA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA)) := iotaFnA_recHead _
  have hR0' : IotaRecHeadA EA0 (iotaIfaceA (extendEnvA EA0 f fmA)) :=
    recHead_of_groupEnvA (fm := fmA) (es := []) rfl (fun _ h => absurd h (List.not_mem_nil _)) hRf'
  obtain ⟨csI', hcsI'⟩ := ctorsTypedSem (hp := fv.profile) hT1 hs _ hag0' posValA_one hSem0 C0.hE hEf
    C0.hEN C0.hENC C0.hEL hELf
    (iotaFnA_lift hEf hENf) (iotaFnA_subst hEf hENf) (iotaFnA_levels hELf hENLf) hR0' hRf' hfr
    (hasTyIfaceA hag0' hTfam0) (IfaceAgreeA.refl _ _)
    (fun hΓ ha hb => sortUniqA_rec hWf' hC'.small hC'.propElim hΓ ha hb) hds
  -- (4) the group without its recursor, admitted; the recursor typed by (T2) at its interface
  have hentries := hcsI'.keeps_entries
  have hlen : csI'.length = cs.length := hcsI'.length_eq.symm
  have hfreshA : GroupFreshA EA0 f fmA (csI'.map GroupCtorA.entry) :=
    groupFreshA_of_erase _ (by rw [hentries, hfmE]; exact hfresh)
  have hWg : EnvWfA (iotaIfaceA (extendEnvA EA0 f fmA)) (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) :=
    .group EA0 f fmA _ hW0I' rfl rfl hclTA (hasTyIfaceA hag0' hTfam0) hlvlA fvA csI' hfreshA
  have hagf'' : IfaceAgreeA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA))
      (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    ifaceAgreeA_prefix hWf (prefixA_extend_groupEnvA hfreshA)
  have hag0'' : IfaceAgreeA EA0 (iotaIfaceA EA0) (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    ifaceAgreeA_prefix hW0I0 (prefixA_groupEnvA hfreshA)
  have hEg := envWfA_closed hWg
  have hELg := envWfA_levels hWg
  have hENg := envWfA_normClosed hWg
  have hENLg := envWfA_normLevels hWg
  have hRg : IotaRecHeadA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))
      (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) := iotaFnA_recHead _
  have hctorcls : ∀ e ∈ csI'.map GroupCtorA.entry, e.2.mclass = .constructorM := fun e he => by
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp he; exact c.hcls
  have hR0g : IotaRecHeadA EA0 (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) :=
    recHead_of_groupEnvA (fm := fmA) rfl hctorcls hRg
  have hRfg := iotaRecHeadA_mono hR0g (prefixA_extend EA0 f fmA hfr)
  have hentries'' := GroupCtorA.iface_entries hagf'' hfr csI'
  obtain ⟨wR, ⟨hTrec⟩⟩ := hT2 (csI'.map (GroupCtorA.iface hagf'' hfr)) rec.elim.toA C0.hE
    (by rw [hentries'']; exact hEg) C0.hEN C0.hENC C0.hEL (by rw [hentries'']; exact hELg)
    (iotaFnA_lift hEg hENg)
    (iotaFnA_subst hEg hENg) (iotaFnA_levels hELg hENLg) hR0g hRfg (by rw [hentries'']; exact hRg)
    (by rw [hentries'']; exact hfreshA) rfl (hasTyIfaceA hag0'' hTfam0)
    (fun _ => 1) posValA_one hSem0 hag0''
  rw [hentries''] at hTrec
  have hrecTy : groupRecTypeA fvA (csI'.map (GroupCtorA.iface hagf'' hfr)) rec.elim.toA =
      groupRecTypeA fvA csI' rec.elim.toA := by
    simp only [groupRecTypeA, GroupCtorA.iface_minors]
  rw [hrecTy] at hTrec
  -- (5) the recursor member and the copy's environment
  let rmA : CheckedMemberA :=
    ⟨.recursorM, fm.arity + rec.elim.toA.extra, groupRecTypeA fvA csI' rec.elim.toA, none, 0, none⟩
  have hrfreshA : (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)).members (f + 1 + csI'.length) = none :=
    members_none_of_erase (by rw [eraseEnv_groupEnvA, hentries, hfmE, hlen]; exact hrfresh)
  have hminE : ((csI'.reverse.map GroupCtorA.minorData).map MinorDataA.erase).map minorUnlevel =
      (cs.reverse.map GroupCtorT.minorData).map minorUnlevel := by
    have h := hcsI'.keeps_minors
    simp only [List.map_map] at h
    simp only [List.map_map, List.map_reverse]
    exact congrArg List.reverse h
  have hrecTyE : erase (groupRecTypeA fvA csI' rec.elim.toA) = rec.member.mtype := by
    rw [rec.stored]
    show erase (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort (rec.elim.toA.motiveLevel fm.arity) _) = _
    rw [erase_recTypeA _ _ _ _ _ _ _ (GroupCtorA.minorData_noFun_of_keeps hcsI'),
      EliminationPolicy.toA_motiveLevel]
    apply recTypeT_congr
    · rw [List.map_map]; exact hpE
    · rw [List.map_map]; exact hiE
    · exact hminE
  have hrmE : eraseMember rmA = rec.member := by
    have hc := rec.hcls
    have hn := rec.hnobody
    have ha := rec.harity
    rw [← EliminationPolicy.toA_arity] at ha
    calc eraseMember rmA = ⟨rec.member.mclass, rec.member.arity, rec.member.mtype, rec.member.body⟩ := by
          simp only [eraseMember, rmA, hc, hn, ha, hrecTyE, Option.map_none']
      _ = rec.member := rfl
  have hclTR : ∀ k, liftA k 1 rmA.mtypeA = rmA.mtypeA := fun k =>
    liftA_eq_of_erase _ k (by show lift k 1 (erase (groupRecTypeA fvA csI' rec.elim.toA)) = _
                              rw [hrecTyE]; exact rec.hclT k)
  have hlvlR : exprLevelsBoundedA rmA.arity rmA.mtypeA = true := by
    show exprLevelsBoundedA (fm.arity + rec.elim.toA.extra)
      (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort (rec.elim.toA.motiveLevel fm.arity) _) = true
    have hk : fm.arity ≤ fm.arity + rec.elim.toA.extra := Nat.le_add_right _ _
    apply recTypeA_bounded_fwd
    · exact levelsBounded_mono hk _ (levelsBounded_canonA fm.arity)
    · exact levelBounded_mono hk _ hs
    · cases h : rec.elim <;> simp [EliminationPolicy.toA, RecElimA.motiveLevel, RecElimA.extra, levelBounded]
    · exact domsBoundedA_mono hk (domsBoundedA_close hpbD)
    · exact domsBoundedA_mono hk (domsBoundedA_close hib)
    · intro cd hcd
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcd
      have hl := c.hlvl
      rw [c.view.stored, c.harity] at hl
      have hfr' := (piTelA_bounded fm.arity _ _ _ hl).2
      obtain ⟨hF, hR⟩ := ctorFieldsA_bounded fm.arity f _ _ _ _ _ _
        (fun D idx hd => drecDTypedA_idxBounded c.view.drecD_typed hd) hfr'
      exact ⟨fun F hF' => FieldA.BoundedA.mono hk (hF F hF'),
        fun x hx => exprLevelsBoundedA_mono hk _ (hR x hx)⟩
  refine ⟨extendEnvA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) (f + 1 + csI'.length) rmA,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eraseEnv_extend, eraseEnv_groupEnvA, hentries, hfmE, hrmE, hlen]
    rfl
  · -- (O2) the new family's indices are sorted within its sort; the rest is the base's
    intro r m u₀ hm hcl hbody v hv ρ x y hx hy hpos
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hm
      cases hm
      exact MemberClass.noConfusion hcl
    · rw [members_extendEnvA_ne _ _ _ hr] at hm
      rcases members_groupEnvA _ r m hm with ⟨rfl, rfl⟩ | hin | hbase
      · -- the family: its index sorts are main's recorded ones, closed
        have hb : piBodyA fmA.mtypeA = .sort fv.sort := by
          show piBodyA (piTelA _ _ _).1 = _
          rw [piBodyA_piTelA]; rfl
        rw [hb] at hbody
        cases hbody
        have hdl : (piDomLevelsA fmA.mtypeA).drop fmA.nparamsA =
            (instDomsA (closeLs fm.arity Mf) iA).map Prod.snd := by
          show (piDomLevelsA (piTelA _ _ _).1).drop (instDomsA (closeLs fm.arity Mf) pA).length = _
          rw [piDomLevelsA_piTelA, List.map_append, List.append_assoc,
            List.drop_left' (by simp)]
          show _ ++ ([] : List Level) = _
          rw [List.append_nil]
        rw [hdl] at hv
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
        obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hd
        have hv₀ : d₀.2 ∈ fv.indices.map Prod.snd := by
          rw [← hie, List.map_map]; exact List.mem_map_of_mem (fun d => (eraseDom d).2) hd₀
        have hx' : eval (fun i => eval ρ (((closeLs fm.arity Mf)[i]?).getD (.param i))) d₀.2 = some x := by
          rw [← eval_instLevel]; exact hx
        have hy' : eval (fun i => eval ρ (((closeLs fm.arity Mf)[i]?).getD (.param i))) fv.sort = some y := by
          rw [← eval_instLevel, instLevel_closeLs_of_bounded fv.sort hs]; exact hy
        exact hprof.1 d₀.2 hv₀ _ x y hx' hy' hpos
      · obtain ⟨c, _, hc⟩ := List.mem_map.mp hin
        have hm' : c.member = m := (Prod.mk.inj hc).2
        rw [← hm', c.hcls] at hcl
        exact MemberClass.noConfusion hcl
      · exact hsmall0 r m u₀ hbase hcl hbody v hv ρ x y hx hy hpos
  · -- (O1) the new recursor eliminates into `Prop` where its family is a proposition with a constructor
    -- (O1-a exempts a group without one); the rest is the base's, whose recursors name only base families
    intro r rm D f' ls' fm' u₀ hrm hcl hlast hhead hfm' hfcl hbody hprop hne hun hns M hM
    have hpreG := prefixA_extend (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) _ rmA hrfreshA
    have hpre0 := prefixA_trans (prefixA_groupEnvA hfreshA) hpreG
    have hpref := prefixA_trans (prefixA_extend_groupEnvA hfreshA) hpreG
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hrm
      cases hrm
      change (piDomsA (recTypeA f (canonLevelsA fm.arity) _ _ fv.sort _ _)).getLast? = some D at hlast
      rw [piDomsA_recTypeA_getLast] at hlast
      cases hlast
      rw [appsSpineA_majorDom] at hhead
      cases hhead
      rw [hpref f fmA (members_extendEnvA_self EA0 f fmA)] at hfm'
      cases hfm'
      have hb : piBodyA fmA.mtypeA = .sort fv.sort := by
        show piBodyA (piTelA _ _ _).1 = _
        rw [piBodyA_piTelA]; rfl
      rw [hb] at hbody
      cases hbody
      have hpo : rec.elim = .propOnly := by
        cases helim : rec.elim with
        | propOnly => rfl
        | anySort =>
            -- (O1) exempts a unit group and a struct group. At a motive of any sort the copy's
            -- recursor passes the copy's test for each, which `hun` and `hns` refute.
            have h := hprof.2 hprop (fun h => hne (by rw [hlen, h]; rfl)) (fun hU => by
              -- O1-b-2: at a unit group the copy's recursor passes the unit test, which `hun` refutes
              obtain ⟨hU1, hU2, hU3⟩ := hU
              have hiA : instDomsA (closeLs fm.arity Mf) iA = [] := by
                have h := hiE
                rw [hU2, List.map_nil] at h
                exact List.map_eq_nil_iff.mp h
              obtain ⟨gcA, hgcA⟩ : ∃ gc, csI'.reverse = [gc] := by
                match csI'.reverse, (List.length_reverse csI').trans (hlen.trans hU1) with
                | [gc], _ => exact ⟨gc, rfl⟩
              obtain ⟨gcT, hgcT⟩ : ∃ gc, cs.reverse = [gc] := by
                match cs.reverse, (List.length_reverse cs).trans hU1 with
                | [gc], _ => exact ⟨gc, rfl⟩
              have hfT : gcT.view.fields = [] :=
                hU3 gcT (List.mem_reverse.mp (by rw [hgcT]; exact List.mem_singleton_self _))
              have hfA : gcA.view.fields = [] := by
                have h := congrArg (fun l => l.map (fun cd => cd.2.1.length)) hminE
                rw [hgcA, hgcT] at h
                simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, GroupCtorT.minorData,
                  MinorDataA.erase, minorUnlevel, List.length_map, hfT, List.length_nil, List.cons.injEq,
                  and_true] at h
                exact List.eq_nil_of_length_eq_zero h.1
              have hmd : csI'.reverse.map GroupCtorA.minorData = [gcA.minorData] := by rw [hgcA]; rfl
              have hst : rmA.mtypeA = recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA) []
                  fv.sort (rec.elim.toA.motiveLevel fm.arity) [gcA.minorData] := by
                show recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA)
                  (instDomsA (closeLs fm.arity Mf) iA) fv.sort (rec.elim.toA.motiveLevel fm.arity)
                  (csI'.reverse.map GroupCtorA.minorData) = _
                rw [hmd]
                exact congrArg (fun I => recTypeA f (canonLevelsA fm.arity) (instDomsA (closeLs fm.arity Mf) pA) I fv.sort
                  (rec.elim.toA.motiveLevel fm.arity) [gcA.minorData]) hiA
              have hu := unitGroupA_of_recTypeA (r := f + 1 + csI'.length) hst hfA (by rw [hlen, hU1])
                ((levelIsZero_iff _).mpr (uniformProp_eqN_zero hprop))
              rw [hu] at hun
              exact Bool.noConfusion hun) (fun hS => by
                -- W-1 (e-3): at a struct group, the struct test
                have hiA : instDomsA (closeLs fm.arity Mf) iA = [] := by
                  have h := hiE
                  rw [hS.2.1, List.map_nil] at h
                  exact List.map_eq_nil_iff.mp h
                have hsg := structGroupA_of_keeps hcsI' hS (m := rmA) (elim := rec.elim.toA) rfl hiA
                  ((levelIsZero_iff _).mpr (uniformProp_eqN_zero hprop)) (by rw [helim]; rfl)
                rw [hsg] at hns
                exact Bool.noConfusion hns)
            rw [helim] at h
            cases h
      change (piDomsA (recTypeA f (canonLevelsA fm.arity) fvA.params fvA.indices fv.sort _ _))[
        fvA.params.length]? = some M at hM
      rw [piDomsA_recTypeA_motive] at hM
      cases hM
      rw [piBodyA_motTyA, hpo]
      rfl
    · rw [members_extendEnvA_ne _ _ _ hr] at hrm
      rcases members_groupEnvA _ r rm hrm with ⟨rfl, rfl⟩ | hin | hbase
      · exact MemberClass.noConfusion hcl
      · obtain ⟨c, _, hc⟩ := List.mem_map.mp hin
        have hm' : c.member = rm := (Prod.mk.inj hc).2
        rw [← hm', c.hcls] at hcl
        exact MemberClass.noConfusion hcl
      · exact propElimStructA_base hW0I0 hpre0 hprop0 hbase hcl hlast hhead hfm' hfcl hbody hprop hne hun hns M hM
  · exact envNoFunA_groupRec hW0I0 C0.noFun hfreshA hrfreshA
      (ListRel.keeps_noFun hcsI') (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
  · -- `EnvNormEraseA` of the group env: only `.constructorM` members are constrained; the scope's
    -- `hsnd` makes each keeps-related copy field δ-free, so `norm` is the identity on them and the
    -- normed stored type erases to the stored one (R-NoDeltaRec-4d-iii).
    intro r m hm hcl T hT
    by_cases hr : r = f + 1 + csI'.length
    · subst hr
      rw [members_extendEnvA_self] at hm
      cases hm
      exact MemberClass.noConfusion hcl
    · rw [members_extendEnvA_ne _ _ _ hr] at hm
      rcases members_groupEnvA _ r m hm with ⟨rfl, rfl⟩ | hin | hbase
      · exact MemberClass.noConfusion hcl
      · obtain ⟨gc, hgc, hge⟩ := List.mem_map.mp hin
        have hgm : gc.member = m := congrArg Prod.snd hge
        subst hgm
        have hTe : T = ctorTypeA f (canonLevelsA fmA.arity) fvA.sort gc.view.mirrors
            (gc.view.fields.map FieldA.norm) gc.view.res :=
          Option.some.inj (hT.symm.trans (hcsI'.keeps_normA gc hgc))
        subst hTe
        rw [gc.view.stored, FieldA.map_norm_self (hcsI'.keeps_noDelta hsnd gc hgc)]
      · exact hn r m hbase hcl T hT
  · intro J hJ
    have hpreG := prefixA_extend (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) _ rmA hrfreshA
    have hpre0 := prefixA_trans (prefixA_groupEnvA hfreshA) hpreG
    have hpref := prefixA_trans (prefixA_extend_groupEnvA hfreshA) hpreG
    have hagJ0 : IfaceAgreeA EA0 (iotaIfaceA EA0) J :=
      (ifaceAgreeA_prefix hW0I0 hpre0).trans (hJ.prefix hpre0)
    have hagJf : IfaceAgreeA (extendEnvA EA0 f fmA) (iotaIfaceA (extendEnvA EA0 f fmA)) J :=
      (ifaceAgreeA_prefix hWf hpref).trans (hJ.prefix hpref)
    have hagJg : IfaceAgreeA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))
        (iotaIfaceA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry))) J :=
      (ifaceAgreeA_prefix hWg hpreG).trans (hJ.prefix hpreG)
    obtain ⟨hW0J⟩ := hW0 J hagJ0
    have hentJ := GroupCtorA.iface_entries hagJf hfr csI'
    have hrefJ := GroupCtorA.iface_refs hagJf hfr csI'
    have hlenJ : (csI'.map (GroupCtorA.iface hagJf hfr)).length = csI'.length := List.length_map _ _
    let recJ : GroupRecA J EA0 f fmA fvA (csI'.map (GroupCtorA.iface hagJf hfr)) :=
      { member := rmA
        hcls := rfl
        hnobody := rfl
        hnp := rfl
        elim := rec.elim.toA
        harity := rfl
        stored := by
          show groupRecTypeA fvA csI' rec.elim.toA = _
          simp only [groupRecTypeA, GroupCtorA.iface_minors]
        hclT := hclTR
        u := wR
        hT := by rw [hentJ]; exact hasTyIfaceA hagJg hTrec
        hlvl := hlvlR }
    have hW := EnvWfA.groupRec EA0 f fmA _ hW0J rfl rfl hclTA (hasTyIfaceA hagJ0 hTfam0) hlvlA fvA
      (csI'.map (GroupCtorA.iface hagJf hfr)) (by rw [hentJ]; exact hfreshA)
      (by rw [hrefJ, hlenJ, List.map_reverse, hcsI'.keeps_refs, ← List.map_reverse, hlayout, hlen])
      recJ (by rw [hentJ, hlenJ]; exact hrfreshA)
    have hEnv : groupRecEnvA (csI'.map (GroupCtorA.iface hagJf hfr)) recJ =
        extendEnvA (groupEnvA EA0 f fmA (csI'.map GroupCtorA.entry)) (f + 1 + csI'.length) rmA := by
      simp only [groupRecEnvA, hentJ, hlenJ]
    exact ⟨hEnv ▸ hW⟩

end GroupStep

/-! ## (13) THE ENVIRONMENT BRIDGE, with inductive groups in the copy's scope -/

section EnvBridge

/-- every family the copy admits is a telescope over a sort. -/
theorem envWfA_famShape {I : IotaIfaceA} : {E : ResolvedEnvA} → EnvWfA I E →
    ∀ r m, E.members r = some m → m.mclass = .inductiveM → ∃ u₀, piBodyA m.mtypeA = .sort u₀
  | _, .empty, _, _, h, _ => Option.noConfusion h
  | _, .axiomM E r' _ _ hE _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm; cases hm; cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm; exact envWfA_famShape hE r m hm hk
  | _, .definitionM E r' _ _ _ hE _ _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm; cases hm; cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm; exact envWfA_famShape hE r m hm hk
  | _, .theoremM E r' _ _ hE _ _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm; cases hm; cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm; exact envWfA_famShape hE r m hm hk
  | _, .opaqueM E r' _ _ _ hE _ _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr; rw [members_extendEnvA_self] at hm; cases hm; cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm; exact envWfA_famShape hE r m hm hk
  | _, .group E _ _ _ hE _ _ _ _ _ fv _ _, r, m, hm, hk => by
      rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hin | hb
      · exact ⟨fv.sort, by rw [fv.stored, piBodyA_piTelA]; rfl⟩
      · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
        have hgm : gc.member = m := congrArg Prod.snd hge
        rw [← hgm, gc.hcls] at hk; cases hk
      · exact envWfA_famShape hE r m hb hk
  | _, .groupRec E f _ _ hE _ _ _ _ _ fv cs _ _ rec _, r, m, hm, hk => by
      unfold groupRecEnvA at hm
      by_cases hr : r = f + 1 + cs.length
      · subst hr; rw [members_extendEnvA_self] at hm; cases hm; rw [rec.hcls] at hk; cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hin | hb
        · exact ⟨fv.sort, by rw [fv.stored, piBodyA_piTelA]; rfl⟩
        · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
          have hgm : gc.member = m := congrArg Prod.snd hge
          rw [← hgm, gc.hcls] at hk; cases hk
        · exact envWfA_famShape hE r m hb hk

/-- THE ENVIRONMENT BRIDGE (M3-e-2). Take an environment of R-CIC's typed environment judgment whose
    groups are all in the copy's scope. It is the erasure of an environment the copy admits, with both
    profiles, at every interface that agrees with that environment's own on its terms. Conditional on
    arc D's two typings (`CtorTyOfViewA`, `RecTyOfViewsA`). -/
theorem envBridge (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → hW.InScope →
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ SmallIndexProfileA EA ∧ PropElimStructA EA ∧ EnvNoFunA EA ∧
      EnvNormEraseA EA ∧ ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)
  | _, .empty, _ => ⟨emptyEnvA, rfl, fun _ _ _ hm => Option.noConfusion hm,
      fun _ _ _ _ _ _ _ hm => Option.noConfusion hm, fun _ _ _ _ _ hm => Option.noConfusion hm,
      fun _ _ hm => Option.noConfusion hm, fun _ _ => ⟨.empty⟩⟩
  | _, .axiom E r A u hE hfresh hA hcl hlvl, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridge hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ :=
        bridgeStep_axiom ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW hfresh hA hcl hlvl
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridge hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_definition ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hv hclA hclv hlvlA hlvlv
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridge hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_thm ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hp hclA hclp hlvlA hlvlp
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridge hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_opaque ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hv hclA hclv hlvlA hlvlv
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .group E f fm ctors rr rm E' hE hfam _ _ hmem, hP => by
      obtain ⟨EA0, rfl, hsm, hpo, hnf, hn0, hW⟩ := envBridge hT1 hT2 hE hP.1
      obtain ⟨⟨fv, htel, cs, hcs, hlayout, rec, hrr, hrm, hprof, hpb, hsnd⟩⟩ := hP.2
      subst hcs hrr hrm
      -- L-K1's checks: the family's, then each constructor fresh, then the recursor fresh
      cases hmem with
      | cons _ _ _ _ _ h0 hnobody hclT _ hlvl _ _ _ _ _ _ _ _ hrest =>
        obtain ⟨hfresh, ⟨hr⟩⟩ := groupMembersT_ctors h0 (cs.map GroupCtorT.entry) hrest
        cases hr with
        | cons _ _ _ _ _ hrfresh _ _ _ _ _ _ _ _ _ _ _ _ hend =>
          cases hend
          exact bridge_group hT1 hT2 ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn0 hW hfam hnobody
            hclT hlvl fv htel cs hfresh hlayout rec hrfresh hprof hpb hsnd hsm hpo

/-- THE ENVIRONMENT BRIDGE AT THE SEMANTIC PREFIX. The same induction as `envBridge`, consuming
    `CtorTyOfViewSemA` and `RecTyOfViewsSemA`. The group step supplies those from the strict prefix
    only. This is not a proof of `CtorTyOfViewA` or `RecTyOfViewsA`. -/
theorem envBridgeSem (hT1 : CtorTyOfViewSemA) (hT2 : RecTyOfViewsSemA) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → hW.InScope →
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ SmallIndexProfileA EA ∧ PropElimStructA EA ∧ EnvNoFunA EA ∧
      EnvNormEraseA EA ∧ ∀ J, IfaceAgreeA EA (iotaIfaceA EA) J → Nonempty (EnvWfA J EA)
  | _, .empty, _ => ⟨emptyEnvA, rfl, fun _ _ _ hm => Option.noConfusion hm,
      fun _ _ _ _ _ _ _ hm => Option.noConfusion hm, fun _ _ _ _ _ hm => Option.noConfusion hm,
      fun _ _ hm => Option.noConfusion hm, fun _ _ => ⟨.empty⟩⟩
  | _, .axiom E r A u hE hfresh hA hcl hlvl, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridgeSem hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ :=
        bridgeStep_axiom ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW hfresh hA hcl hlvl
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridgeSem hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_definition ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hv hclA hclv hlvlA hlvlv
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridgeSem hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_thm ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hp hclA hclp hlvlA hlvlp
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hP => by
      obtain ⟨EA, rfl, hsm, hpo, hnf, hn, hW⟩ := envBridgeSem hT1 hT2 hE hP
      obtain ⟨_, hc, hEnv, hW'⟩ := bridgeStep_opaque ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn hW
        hfresh hA hv hclA hclv hlvlA hlvlv
      obtain ⟨hW0⟩ := hW _ (IfaceAgreeA.refl _ _)
      obtain ⟨hsm', hpo'⟩ := profilesA_extend hW0 (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h))
        (fun h => MemberClass.noConfusion (hc.symm.trans h)) hsm hpo
      exact ⟨_, hEnv, hsm', hpo', envNoFunA_extend hW0 hnf (members_none_of_erase hfresh)
        (fun h => MemberClass.noConfusion (hc.symm.trans h)),
        hn.extend (fun h => MemberClass.noConfusion (hc.symm.trans h)), hW'⟩
  | _, .group E f fm ctors rr rm E' hE hfam _ _ hmem, hP => by
      obtain ⟨EA0, rfl, hsm, hpo, hnf, hn0, hW⟩ := envBridgeSem hT1 hT2 hE hP.1
      obtain ⟨⟨fv, htel, cs, hcs, hlayout, rec, hrr, hrm, hprof, hpb, hsnd⟩⟩ := hP.2
      subst hcs hrr hrm
      -- L-K1's checks: the family's, then each constructor fresh, then the recursor fresh
      cases hmem with
      | cons _ _ _ _ _ h0 hnobody hclT _ hlvl _ _ _ _ _ _ _ _ hrest =>
        obtain ⟨hfresh, ⟨hr⟩⟩ := groupMembersT_ctors h0 (cs.map GroupCtorT.entry) hrest
        cases hr with
        | cons _ _ _ _ _ hrfresh _ _ _ _ _ _ _ _ _ _ _ _ hend =>
          cases hend
          exact bridge_groupSem hT1 hT2 ⟨hW _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩ hn0 hW hfam hnobody
            hclT hlvl fv htel cs hfresh hlayout rec hrfresh hprof hpb hsnd hsm hpo

/-- every environment of the typed environment judgment whose groups are in the copy's scope is the
    erasure of one the copy admits. -/
theorem annEnvA_of_envWfT_inScope (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ AnnEnvA EA ∧ EnvNormEraseA EA := by
  obtain ⟨EA, hE, hsm, hpo, hnf, hn, hWA⟩ := envBridge hT1 hT2 hW hP
  exact ⟨EA, hE, ⟨hWA _ (IfaceAgreeA.refl _ _), hsm, hpo, hnf⟩, hn⟩

/-- ROW 1 OVER THE TYPED ENVIRONMENT JUDGMENT, its groups in the copy's scope. -/
theorem sortConvCharT_inScope (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level}
    {T : Expr Nat} (h : ConvT E n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_inScope hT1 hT2 hW hP
  exact sortConvCharT' C hn hΓ h

/-- ROW 2 OVER THE TYPED ENVIRONMENT JUDGMENT, its groups in the copy's scope. -/
theorem piConvInjT_inScope (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' T : Expr Nat} (h : ConvT E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_inScope hT1 hT2 hW hP
  exact piConvInjT' C hn hΓ h

/-- ROW 3 OVER THE TYPED ENVIRONMENT JUDGMENT, its groups in the copy's scope: two applications of one
    family of `E` convertible at a sort have componentwise convertible level lists and argument
    lists. -/
theorem famAppConvInjT_inScope (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat}
    {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (h : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧ ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_inScope hT1 hT2 hW hP
  rw [members_eraseEnv] at hm
  cases hmA : EA.members r with
  | none => rw [hmA] at hm; exact Option.noConfusion hm
  | some mA =>
      rw [hmA] at hm
      cases hm
      obtain ⟨hWA⟩ := C.wf
      obtain ⟨u₀, hsh⟩ := envWfA_famShape hWA r mA hmA hind
      exact famAppConvInjT_any' C hn hΓ hmA hind hsh h

end EnvBridge

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.groupMembersT_ctors
#print axioms Rcic.Declarative.Ann.erase_ctorTypeA
#print axioms Rcic.Declarative.Ann.erase_recTypeA
#print axioms Rcic.Declarative.Ann.annMirrorsConvT
#print axioms Rcic.Declarative.Ann.annFieldsTyT
#print axioms Rcic.Declarative.Ann.instantiateLevels_closeLs
#print axioms Rcic.Declarative.Ann.ctorTypeA_bounded_fwd
#print axioms Rcic.Declarative.Ann.recTypeA_bounded_fwd
#print axioms Rcic.Declarative.Ann.ctorTypeT_bounded_rev
#print axioms Rcic.Declarative.Ann.recTypeT_congr
#print axioms Rcic.Declarative.Ann.ctorClosed
#print axioms Rcic.Declarative.Ann.famClosed
#print axioms Rcic.Declarative.Ann.ctorsTyped
#print axioms Rcic.Declarative.Ann.propElimStructA_base
#print axioms Rcic.Declarative.Ann.profilesA_extend
#print axioms Rcic.Declarative.Ann.bridge_group
#print axioms Rcic.Declarative.Ann.envWfA_famShape
#print axioms Rcic.Declarative.Ann.envBridge
#print axioms Rcic.Declarative.Ann.annEnvA_of_envWfT_inScope
#print axioms Rcic.Declarative.Ann.sortConvCharT_inScope
#print axioms Rcic.Declarative.Ann.piConvInjT_inScope
#print axioms Rcic.Declarative.Ann.famAppConvInjT_inScope
#print axioms Rcic.Declarative.Ann.ctorsTypedSem
#print axioms Rcic.Declarative.Ann.bridge_groupSem
#print axioms Rcic.Declarative.Ann.envBridgeSem
#print axioms Rcic.Declarative.Ann.structGroupA_of_keeps
#print axioms Rcic.Declarative.Ann.ListRel.keeps_normA
