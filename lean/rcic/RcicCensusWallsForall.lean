import rcic.RcicConvPlus
import rcic.RcicDTMetaTyped
import rcic.RcicDTMetaTypedEnv
import rcic.RcicDTMetaTypedEmbed
import rcic.RcicTypedEnv
import rcic.RcicTypedGroupPins
import rcic.RcicEGTypedGroup
import rcic.RcicFixtures

/-!
# Census walls outside BelowC — Wall F, Part I

`research/rcic/sortrow/CENSUS_WALLS_FORALL_RM.md` (ChatGPT, J line), rows
DT-013 / EG-023 / DT-018 / DT-020 — the named `∀`-premises, each either
restated at its specified precondition or produced from the admitted
object, plus the necessity countermodels.

- **DT-013 / EG-023** — the `hext` member-extensionality premise of
  `DT013T_environment_weakening` IS `Rcic.Syn.EnvExt` (spec 04 §16's
  precondition: extension preserves old members). Restated anchors
  `DT013T_weaken_of_envExt` / `DT013T_environment_weakening_of_envExt`
  ride the existing `hasTyTExt`/`convTExt` transport; the producer over
  an actual extension lineage is `envExt_extendEnv` under `envExt_trans`;
  the necessity control is one axiom `c : Sort 0` against `emptyEnv`.
- **DT-018** — the typed anchor `DT018T_inductive_extension_preserves`
  is `EG010T_group_accepted` (typed `EnvWfT`, accepted `GroupAcceptChain`)
  — no legacy-`EnvWf` conjunction. The per-node producer notes live on
  the declaration's doc.
- **DT-020** — the source-profile embedding: `HasTyLambda`/`ConvLambda`
  (0λ derivations = derivations whose `NoIota*` profile holds), the
  embed projections, `noIotaTy_ext`/`noIotaConvT_ext` (ι-freeness is
  extension-stable), and the `trueEnvU` counterexample derivation `H`
  with `NoIotaTy H = (True ∧ False)` — a real `HasTyT` whose profile is
  kernel-refuted, refuting "well-formed env ⇒ every derivation is
  ι-free" without touching the embedding. `noDerivedIota_of_noGroupEnv`
  discharges the old global `hno` exactly where it holds: group-free
  member tables.

`closure_claim = 0`: these are row-local anchors and producers, not a
closure statement.
-/

namespace Rcic.Declarative

/-! ## DT-013 / EG-023 — `hext` restated as `EnvExt`, produced, and shown
necessary

The open premise of `DT013T_environment_weakening`
(`∀ r m, E.members r = some m → E'.members r = some m`) is, term for
term, `Rcic.Syn.EnvExt E E'` — the specified extension precondition of
spec 04 §16. The transport is the existing mutual `hasTyTExt` /
`convTExt` / `derivedIotaExt`: const, δ and const-level conversion keep
the lookup through `hExt`, ι through `derivedIotaExt`, children
transported. EG-023's typing leg is the same precondition; the
ref/byte-preservation and store-binding halves stay their own object
obligations (`apps/rcic-env-weaken` compares presented canonical
images). -/

/-- the restated weakening producer: `EnvExt` is the premise, not an
    open hypothesis — the typing transports along it. -/
def DT013T_weaken_of_envExt {E E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (hExt : Rcic.Syn.EnvExt E E')
    (h : HasTyT E n Γ e A) : HasTyT E' n Γ e A :=
  hasTyTExt hExt h

/-- the `DT013T_`-named anchor at `EnvExt`: the extensionality
    hypothesis presented as the specified precondition. -/
theorem DT013T_environment_weakening_of_envExt {E E' : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {e A : Expr Nat} (hExt : Rcic.Syn.EnvExt E E')
    (h : HasTyT E n Γ e A) : Nonempty (HasTyT E' n Γ e A) :=
  ⟨hasTyTExt hExt h⟩

/-- EnvExt over an actual extension lineage: two fresh `extendEnv`
    steps pay the premise through `envExt_extendEnv` chained by
    `envExt_trans` — each step's freshness field is the admission
    object's own data. -/
theorem envExt_lineage2 {E : ResolvedEnv} {r₁ r₂ : Nat}
    {m₁ m₂ : CheckedMember} (h1 : E.members r₁ = none)
    (h2 : (extendEnv E r₁ m₁).members r₂ = none) :
    Rcic.Syn.EnvExt E (extendEnv (extendEnv E r₁ m₁) r₂ m₂) :=
  Rcic.Syn.envExt_trans (Rcic.Syn.envExt_extendEnv m₁ h1)
    (Rcic.Syn.envExt_extendEnv m₂ h2)

/-- PIN (DT-013 / EG-023): the Nat family at 0, `zero` at 1, `succ`
    at 2 — a real two-step lineage over the admitted family env.
    `EnvExt` is produced from the two freshness fields, never
    presented; the `const 0` typing transports through `hasTyTExt`. -/
theorem pin_DT013T_envExt_lineage {n : Nat} :
    Nonempty (HasTyT (extendEnv (extendEnv (extendEnv emptyEnv 0
      natFamMember) 1 natZeroMember) 2 natSuccMember) n []
      (.const 0 []) (instantiateLevels [] (.sort (.succ .zero)))) :=
  DT013T_environment_weakening_of_envExt
    (envExt_lineage2 rfl rfl)
    (.const [] 0 [] natFamMember rfl rfl rfl)

/-- the one-axiom environment for the necessity control: `c : Sort 0`
    at ref 0 over `emptyEnv`. -/
def axSortEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort .zero, none⟩

/-- NECESSITY (DT-013 / EG-023): the premise cannot be deleted —
    `axSortEnv` (one axiom `c : Sort 0`) and `emptyEnv` are each fine,
    but `c` types in `axSortEnv` while no `EnvExt axSortEnv emptyEnv`
    exists and `c` has no typing at `emptyEnv` at all
    (`hasTyT_constsIn`). The premise is exactly what certifies the
    target as an extension. -/
theorem pin_DT013T_hext_necessary {n : Nat} :
    Nonempty (HasTyT axSortEnv n [] (.const 0 [])
        (instantiateLevels [] (.sort .zero))) ∧
    ¬ Rcic.Syn.EnvExt axSortEnv emptyEnv ∧
    ∀ T, ¬ Nonempty (HasTyT emptyEnv n [] (.const 0 []) T) := by
  refine ⟨⟨.const [] 0 [] ⟨.axiomM, 0, .sort .zero, none⟩ rfl rfl rfl⟩,
      ?_, fun T ⟨h⟩ => ?_⟩
  · intro h
    have h0 := h 0 ⟨.axiomM, 0, .sort .zero, none⟩ rfl
    simp [emptyEnv] at h0
  · obtain ⟨m, hm⟩ := hasTyT_constsIn h
    simp [emptyEnv] at hm

/-! ## DT-018 — the alias at the accepted typed group chain

The row's anchor is the typed `EnvWfT` extension — `EG010T_group_accepted`
under the census name; no legacy-`EnvWf` conjunction. The producer is
already the chain: per `GroupAcceptChain.cons` node the freshness is
`hadm.fresh`; the accepted check splits into
`memberStructB` / `memberScopeB` / `memberContentB`, where
`memberStructB_of` gives `exprClosedAt 0 m.mtype = true` — hence
`∀ k, lift k 1 m.mtype = m.mtype` by `lift_id_of_exprClosedAt_zero` —
plus no body, family-arity shape, level boundedness, family
canonicality and group-arity coherence; the successful `sortTyAtC`
leaf supplies `⟨u, hT⟩`; `memberScopeB_of` the constructor's
exact-sort typing in the family-only source env; `memberContentB_of
hadm` per admission constructor (family `famTypedT_of`; constructor
`famTypedT_of` + `ctorTypedT_of`; recursor `famTypedT_of` +
`ctorTypedAll_of` + `idxT_of` + `iotaEqsT_of`); the chain recurses into
`GroupMembersT.cons`; `consRec` re-sources the recursor link via
`IA021T_recursor_typed`, `consRecCheck` via `IA021T_minorDomains_of_check`;
`groupClassB_of` gives the class family. `IndGroupAdmitted` alone is
insufficient (`badAdmittedRec`,
`pin_EG010T_badGroup_content_refused`). Not a checker-completeness
claim. -/

/-- DT-018 restated: the admitted inductive extension preserves `EnvWfT`
    — the accepted typed group chain is the producer. -/
def DT018T_inductive_extension_preserves {E : ResolvedEnv} (hE : EnvWfT E)
    (fuel : Nat) {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {E' : ResolvedEnv} (hclass : groupClassB fm ctors rm = true)
    (hchain : GroupAcceptChain (extendEnv E f fm) fuel E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : EnvWfT E' :=
  EG010T_group_accepted hE fuel hclass hchain

/-! ## DT-020 — the 0λ embedding subtype, its extension transport, and
the `trueEnvU` counterexample

`HasTyLambda`/`ConvLambda` are the 0λ grammar as subtypes of the full
typed judgment: every constructor except `ConvT.iota`. `noIotaTy_ext` /
`noIotaConvT_ext` show the profile is preserved by the environment
transport — the embedding commutes with extension. The old global `hno`
is a sufficient condition that holds exactly on group-free member
tables (`noDerivedIota_of_noGroupEnv`); it is NOT derivable from
`EnvWfT` — the counterexample `H` below is a real derivation in the
admitted `trueEnvU` whose `NoIotaTy` kernel-reduces to `True ∧ False`. -/

/-- the 0λ typing subtype: a `HasTyT` derivation carrying its
    no-ι profile. -/
def HasTyLambda (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) :=
  { h : HasTyT E n Γ e A // NoIotaTy h }

/-- the 0λ conversion subtype. -/
def ConvLambda (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b T : Expr Nat) :=
  { c : ConvT E n Γ a b T // NoIotaConvT c }

/-- embedding forgets the profile. -/
def DT020T_embed_ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTyLambda E n Γ e A) : HasTyT E n Γ e A :=
  h.1

/-- embedding forgets the profile, conversion side. -/
def DT020T_embed_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (c : ConvLambda E n Γ a b T) :
    ConvT E n Γ a b T :=
  c.1

mutual

/-- the no-ι profile is extension-stable, typing side: the transport
    `hasTyTExt` rebuilds each arm and hands the `conv` field to
    `convTExt`, so `NoIotaTy` survives by mutual induction. -/
theorem noIotaTy_ext {E E' : ResolvedEnv} (hExt : Rcic.Syn.EnvExt E E') :
    {n : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    (h : HasTyT E n Γ e A) → NoIotaTy h →
      NoIotaTy (hasTyTExt hExt h)
  | _, _, _, _, .sort _ _, _ => trivial
  | _, _, _, _, .bvar _ _ _ _, _ => trivial
  | _, _, _, _, .const _ _ _ _ _ _ _, _ => trivial
  | _, _, _, _, .pi _ _ _ _ _ hA hB, h' =>
      ⟨noIotaTy_ext hExt hA h'.1, noIotaTy_ext hExt hB h'.2⟩
  | _, _, _, _, .lam _ _ _ _ _ hA hbody, h' =>
      ⟨noIotaTy_ext hExt hA h'.1, noIotaTy_ext hExt hbody h'.2⟩
  | _, _, _, _, .app _ _ _ _ _ hf ha, h' =>
      ⟨noIotaTy_ext hExt hf h'.1, noIotaTy_ext hExt ha h'.2⟩
  | _, _, _, _, .letE _ _ _ _ _ _ hA hv hb, h' =>
      ⟨noIotaTy_ext hExt hA h'.1, noIotaTy_ext hExt hv h'.2.1,
        noIotaTy_ext hExt hb h'.2.2⟩
  | _, _, _, _, .lit _ _ _ hexp, h' => noIotaTy_ext hExt hexp h'
  | _, _, _, _, .conv _ _ _ _ _ h hc, h' =>
      ⟨noIotaTy_ext hExt h h'.1, noIotaConvT_ext hExt hc h'.2⟩

/-- the no-ι profile is extension-stable, conversion side. The `iota`
    arm is vacuous: its premise is `False`. -/
theorem noIotaConvT_ext {E E' : ResolvedEnv}
    (hExt : Rcic.Syn.EnvExt E E') : {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (c : ConvT E n Γ a b T) → NoIotaConvT c →
      NoIotaConvT (convTExt hExt c)
  | _, _, _, _, _, .refl _ _ _ hA, h' => noIotaTy_ext hExt hA h'
  | _, _, _, _, _, .symm _ _ _ _ h, h' => noIotaConvT_ext hExt h h'
  | _, _, _, _, _, .trans _ _ _ _ _ h1 h2, h' =>
      ⟨noIotaConvT_ext hExt h1 h'.1, noIotaConvT_ext hExt h2 h'.2⟩
  | _, _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg, h' =>
      ⟨noIotaTy_ext hExt hA h'.1, noIotaTy_ext hExt hbody h'.2.1,
        noIotaTy_ext hExt harg h'.2.2⟩
  | _, _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, h' =>
      ⟨noIotaTy_ext hExt hA h'.1, noIotaTy_ext hExt hv h'.2.1,
        noIotaTy_ext hExt hb h'.2.2⟩
  | _, _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, h' =>
      noIotaTy_ext hExt hv h'
  | _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb, h' =>
      noIotaTy_ext hExt hb h'
  | _, _, _, _, _, .iota _ _ _ _ _ _ _, h' => h'.elim
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, h' => noIotaTy_ext hExt hexp h'
  | _, _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, h' =>
      ⟨noIotaConvT_ext hExt h1 h'.1, noIotaConvT_ext hExt h2 h'.2⟩
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, h' =>
      ⟨noIotaConvT_ext hExt hA h'.1, noIotaConvT_ext hExt hb h'.2⟩
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, h' =>
      ⟨noIotaConvT_ext hExt hA h'.1, noIotaConvT_ext hExt hB h'.2⟩
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, h' =>
      ⟨noIotaConvT_ext hExt hA h'.1, noIotaConvT_ext hExt hv h'.2.1,
        noIotaConvT_ext hExt hb h'.2.2⟩
  | _, _, _, _, _, .sorts _ _ _ _, _ => trivial
  | _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _, _ => trivial
  | _, _, _, _, _, .eta _ _ _ _ h, h' => noIotaTy_ext hExt h h'
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, h' =>
      ⟨noIotaTy_ext hExt hP h'.1, noIotaTy_ext hExt hp h'.2.1,
        noIotaTy_ext hExt hq h'.2.2⟩
  | _, _, _, _, _, .tyConv _ _ _ _ _ _ h hA, h' =>
      ⟨noIotaConvT_ext hExt h h'.1, noIotaConvT_ext hExt hA h'.2⟩

end

/-- the subtype transports under extension: the embedding commutes
    with `EnvExt`. -/
def DT020T_embed_ty_under_extension {E E' : ResolvedEnv}
    (hExt : Rcic.Syn.EnvExt E E') {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyLambda E n Γ e A) : HasTyLambda E' n Γ e A :=
  ⟨hasTyTExt hExt h.1, noIotaTy_ext hExt h.1 h.2⟩

/-- the old `hno` on a group-free member table: no inductive, no
    constructor, no recursor member ⇒ no `IotaWitness`, hence no
    `DerivedIota`. -/
theorem noDerivedIota_of_noGroupEnv {E : ResolvedEnv}
    (hG : NoGroupEnv E) :
    ∀ lhs rhs, DerivedIota E lhs rhs → False
  | _, _, .of w => (hG w.recRef w.recMember w.hrec).2.2 w.hrecK

/-- group-free discharge of the old `hno` anchor: on a `NoGroupEnv`
    member table every derivation is ι-free. -/
theorem DT020T_lambda_embeds_into_iota_of_noGroupEnv {E : ResolvedEnv}
    (hG : NoGroupEnv E) {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT E n Γ e A) : NoIotaTy h :=
  DT020T_lambda_embeds_into_iota (noDerivedIota_of_noGroupEnv hG) h

/-- `NoGroupEnv` at the empty table — the vacuous lineage base. -/
theorem noGroupEnv_empty : NoGroupEnv emptyEnv := by
  intro r m hm; simp [emptyEnv] at hm

/-- `NoGroupEnv` by lineage: extending a group-free table with a
    non-group member (axiom / definition / theorem / opaque) keeps it
    group-free — the inductive step over an
    empty/axiom/definition/theorem/opaque lineage. -/
theorem noGroupEnv_extend_nonGroup {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hG : NoGroupEnv E) (hfresh : E.members r = none)
    (hk : m.mclass = .axiomM ∨ m.mclass = .definitionM ∨
      m.mclass = .theoremM ∨ m.mclass = .opaqueM) :
    NoGroupEnv (extendEnv E r m) := by
  intro r' m' hm'
  by_cases h0 : r' = r
  · subst h0
    simp only [extendEnv, ↓reduceIte] at hm'
    obtain rfl := Option.some.inj hm'
    obtain k | k | k | k := hk <;>
      simp only [k] <;> decide
  · unfold extendEnv at hm'
    simp only [h0, ↓reduceIte] at hm'
    exact hG r' m' hm'

/-! ### the `trueEnvU` counterexample

The admitted True group (`trueEnvUWfT`): `0 : True : Prop`,
`1 : intro`, `2 : True.rec.{u} : Π (M : True → Sort u), M intro → Π t,
M t`. With `F = const 0 []`, `tt = const 1 []`, `M = lam F S1`,
`L = True.rec.{2} M S0 tt`, the witness `wTrueRecU` gives
`L →ι S0`. In `Γx = [assumption L]` the derivation
`H : bvar 0 : S0` goes through `ConvT.iota` — `NoIotaTy H` is
`True ∧ False` by kernel reduction. -/

/-- the `True.rec` iota witness at `trueEnvU`: `True.rec.{2} M S0 tt
    →ι S0`. All fields concrete. -/
def wTrueRecU : IotaWitness trueEnvU where
  recRef := 2
  ctorRef := 1
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := trueRecMemberU
  ctorMember := trueIntroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.lam (.const 0 []) (.sort (.succ .zero)), .sort .zero]
  fields := []
  ctorParams := []
  kinds := []
  minor := .sort .zero
  hlen := rfl
  familyRef := 0
  famMember := trueFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := []
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 0 []) (.sort (.param 0)),
    .app (.bvar 0) (.const 1 []), .const 0 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 0 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `F : S0` at `trueEnvU` — the family constant types at its stored
    sort. -/
def trueEnvUF_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ (.const 0 []) (.sort .zero) :=
  .const _ 0 [] trueFamMember rfl rfl rfl

/-- `tt : F` — `intro : True`. -/
def trueEnvUtt_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ (.const 1 []) (.const 0 []) :=
  .const _ 1 [] trueIntroMember rfl rfl rfl

/-- `M = λ _ : F. S1 : Π F S2` — the motive at `ls = [.succ (.succ
    .zero)]`. -/
def trueEnvUM_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ (.lam (.const 0 []) (.sort (.succ .zero)))
      (.pi (.const 0 []) (.sort (.succ (.succ .zero)))) :=
  .lam _ _ .zero _ _ trueEnvUF_ty (.sort _ (.succ .zero))

/-- `K = M tt : S2` and its β-reduction `K ≈ S1 : S2`. -/
def trueEnvUK_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ
      (.app (.lam (.const 0 []) (.sort (.succ .zero))) (.const 1 []))
      (.sort (.succ (.succ .zero))) :=
  .app _ _ _ _ _ trueEnvUM_ty trueEnvUtt_ty

def trueEnvU_betaK {n : Nat} {Γ : LCtx} :
    ConvT trueEnvU n Γ
      (.app (.lam (.const 0 []) (.sort (.succ .zero))) (.const 1 []))
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .beta _ _ _ _ _ .zero trueEnvUF_ty (.sort _ (.succ .zero)) trueEnvUtt_ty

/-- `S0 : K` — the minor's real type, converted along `βK.symm`. -/
def trueEnvUS0_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ (.sort .zero)
      (.app (.lam (.const 0 []) (.sort (.succ .zero))) (.const 1 [])) :=
  .conv _ _ _ _ (.succ (.succ .zero)) (.sort _ .zero)
    (.symm _ _ _ _ trueEnvU_betaK)

/-- `L : K` — the recursor applied at `ls = [.succ (.succ .zero)]`:
    `const 2 [SS0]` at `instantiateLevels [SS0] trueRecTypeU`, applied
    to `M`, the minor `S0` (at `K`), and the major `tt : F`. -/
def trueEnvUL_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ
      (.app (.app (.app (.const 2 [.succ (.succ .zero)])
        (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
        (.const 1 []))
      (.app (.lam (.const 0 []) (.sort (.succ .zero))) (.const 1 [])) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.const _ 2 [.succ (.succ .zero)] trueRecMemberU rfl rfl rfl)
        trueEnvUM_ty)
      trueEnvUS0_ty)
    trueEnvUtt_ty

/-- `L : S1` — converting `L : K` along `βK`. -/
def trueEnvUL_tyS1 {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ
      (.app (.app (.app (.const 2 [.succ (.succ .zero)])
        (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
        (.const 1 []))
      (.sort (.succ .zero)) :=
  .conv _ _ _ _ (.succ (.succ .zero)) trueEnvUL_ty trueEnvU_betaK

/-- `L ≈ S0 : S1` — the iota conversion. -/
def trueEnvU_ci {n : Nat} {Γ : LCtx} :
    ConvT trueEnvU n Γ
      (.app (.app (.app (.const 2 [.succ (.succ .zero)])
        (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
        (.const 1 []))
      (.sort .zero) (.sort (.succ .zero)) :=
  .iota _ _ _ _ (.of wTrueRecU) trueEnvUL_tyS1 (.sort _ .zero)

/-- COUNTEREXAMPLE (DT-020): `H : HasTyT trueEnvU 0 [.assumption L]
    (.bvar 0) (.sort .zero)` — a real derivation in the admitted
    `trueEnvU` whose conversion step is `ConvT.iota`. -/
def pin_DT020T_trueEnvU_H :
    HasTyT trueEnvU 0 [.assumption
      (.app (.app (.app (.const 2 [.succ (.succ .zero)])
        (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
        (.const 1 []))]
      (.bvar 0) (.sort .zero) :=
  .conv _ _ _ _ (.succ .zero)
    (.bvar _ _ _ rfl) trueEnvU_ci

/-- the profile refuted by the kernel: `NoIotaTy H` reduces to
    `True ∧ False`. -/
theorem pin_DT020T_noIotaTy_trueEnvU_kernel :
    NoIotaTy pin_DT020T_trueEnvU_H = (True ∧ False) := rfl

/-- hence no ι-free proof of `H` — the counterexample to `hno` from a
    well-formed environment: `NoIotaTy H` is uninhabited. -/
theorem pin_DT020T_noIotaTy_trueEnvU_refused :
    NoIotaTy pin_DT020T_trueEnvU_H → False := And.right

end Rcic.Declarative

#print axioms Rcic.Declarative.DT013T_weaken_of_envExt
#print axioms Rcic.Declarative.DT013T_environment_weakening_of_envExt
#print axioms Rcic.Declarative.envExt_lineage2
#print axioms Rcic.Declarative.pin_DT013T_envExt_lineage
#print axioms Rcic.Declarative.pin_DT013T_hext_necessary
#print axioms Rcic.Declarative.DT018T_inductive_extension_preserves
#print axioms Rcic.Declarative.noIotaTy_ext
#print axioms Rcic.Declarative.noIotaConvT_ext
#print axioms Rcic.Declarative.DT020T_embed_ty_under_extension
#print axioms Rcic.Declarative.noDerivedIota_of_noGroupEnv
#print axioms Rcic.Declarative.DT020T_lambda_embeds_into_iota_of_noGroupEnv
#print axioms Rcic.Declarative.noGroupEnv_empty
#print axioms Rcic.Declarative.noGroupEnv_extend_nonGroup
#print axioms Rcic.Declarative.wTrueRecU
#print axioms Rcic.Declarative.pin_DT020T_trueEnvU_H
#print axioms Rcic.Declarative.pin_DT020T_noIotaTy_trueEnvU_kernel
