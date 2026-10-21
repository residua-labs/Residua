import rcic.RcicTypedJ
import rcic.RcicEnv

/-!
# M3-e-2 — an inductive group's structured views on `main`'s syntax: the copy's scope

05 admits an inductive group through VIEWS (05 §5–§13):

- the family's parameters and indices with their sorts, and its result sort;
- each constructor's parameter mirrors, its fields, its result indices;
- the recursor's type, DERIVED from them.

L-K1's `IndGroupAdmitted` states these views on the untyped root, as flat field lists in each
constructor's own telescope, typed where the member is admitted.

This module states views in the copy's form (`RcicAnnGroup`, `RcicAnnRecView`) on `main`'s syntax:

- field KINDS (`FieldT`): plain, or directly recursive;
- the constructor's and the recursor's types BUILT from the views (`ctorTypeT`, `recTypeT`);
- the views' typed content in the typed judgment (`TelTyT`, `ArgsTyT`, `MirrorsConvT`, `FieldsTyT`),
  in 05 §4's scopes: the family's header in the base (HeaderScope), a constructor's type in the base
  and the family (ConstructorScope), the recursor's type with the constructors too (DerivationScope).

The family-free parts (a plain field's domain, a recursive field's indices, the result indices) are
typed in the PLAIN context: over the parameters and the earlier plain fields, in the base.

These views describe fewer groups than 05 admits. So they are the bridge's PREMISE
(`GroupInScopeT`, `RcicAnnEnvBridgeGroup`), never part of `EnvWfT`. The views have no kind for:

- a function-recursive field (05 §8, `inner > 0`): R-NoFunRec;
- a recursive field reached only by reduction (05 §8, "T reduces to"): R-NoDeltaRec.

The plain context holds no recursive field. Whether a family-free part of a 05 group can name a
recursive field's variable is not settled here.

The builders mirror the copy's with the binder levels dropped. They are stated here on their own; the
bridge proves the copy's erase to them.
-/

namespace Rcic.Declarative

/-! ## (1) parallel substitution: the plain context into a telescope's context -/

/-- a parallel substitution on `main`'s syntax. -/
abbrev SubstT : Type := Nat → Expr Nat

namespace SubstT

def id : SubstT := fun i => .bvar i

/-- under one binder: the bound variable stays, the images move up. -/
def up (σ : SubstT) : SubstT
  | 0 => .bvar 0
  | i + 1 => lift 0 1 (σ i)

/-- one binder deeper in the target, none in the source (past a recursive field). -/
def shift1 (σ : SubstT) : SubstT := fun i => lift 0 1 (σ i)

end SubstT

/-- apply a parallel substitution. -/
def substT (σ : SubstT) : Expr Nat → Expr Nat
  | .bvar i => σ i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (substT σ f) (substT σ x)
  | .lam a b => .lam (substT σ a) (substT σ.up b)
  | .pi a b => .pi (substT σ a) (substT σ.up b)
  | .letE a w b => .letE (substT σ a) (substT σ w) (substT σ.up b)
  | .lit t => .lit t

/-! ## (2) the builders (05 §6, §8, §11–§13) -/

/-- a constructor field in the PLAIN context (the parameters and the earlier plain fields): a plain
    field's domain and its sort, or a directly recursive field's indices. `drecD D idx` is the
    δ-reached directly recursive field (R-NoDeltaRec-4): its SURFACE domain `D` does not head-match
    the family, but its δ-normal form is the family application at `idx`. -/
inductive FieldT : Type
  | plain (D : Expr Nat) (u : Level)
  | drec (idx : List (Expr Nat))
  | drecD (D : Expr Nat) (idx : List (Expr Nat))

/-- the family's canonical universe vector (05 §2). -/
def canonLevels (n : Nat) : List Level := (List.range n).map Level.param

/-- the canonical level vector is the identity on every level (the typed-root
    `instLevel_canonA`). -/
theorem instLevel_canon (a : Nat) : (l : Level) → instLevel (canonLevels a) l = l
  | .zero => rfl
  | .succ l => congrArg Level.succ (instLevel_canon a l)
  | .max x y => by
      show Level.max (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_canon a x, instLevel_canon a y]
  | .imax x y => by
      show Level.imax (instLevel _ x) (instLevel _ y) = _
      rw [instLevel_canon a x, instLevel_canon a y]
  | .param i => by
      rw [instLevel_param]
      by_cases h : i < a
      · simp [canonLevels, h]
      · have : (canonLevels a)[i]? = none := by
          simp only [canonLevels, List.getElem?_map, List.getElem?_range]
          simp [h, Nat.le_of_not_lt h]
        rw [this]; rfl

/-- the canonical vector is level-bounded at its own arity (the typed-root
    `levelsBounded_canonA`). -/
theorem levelsBounded_canon (a : Nat) : levelsBounded a (canonLevels a) = true := by
  have : ∀ (xs : List Nat), (∀ i ∈ xs, i < a) → levelsBounded a (xs.map Level.param) = true := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons i xs ih =>
        intro h
        simp only [List.map_cons, levelsBounded, Bool.and_eq_true]
        exact ⟨by simp [levelBounded, h i (List.mem_cons_self _ _)],
          ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩
  exact this _ (fun i hi => List.mem_range.mp hi)

/-- the canonical level vector is the identity on every expression (the typed-root
    `instantiateLevels_canonA`). -/
theorem instantiateLevels_canon (a : Nat) : (e : Expr Nat) →
    instantiateLevels (canonLevels a) e = e
  | .bvar _ => rfl
  | .sort l => by simp only [instantiateLevels, instLevel_canon]
  | .const r ms => by
      simp only [instantiateLevels]
      congr 1
      conv => rhs; rw [← List.map_id ms]
      exact List.map_congr_left (fun l _ => instLevel_canon a l)
  | .app f x => by simp only [instantiateLevels, instantiateLevels_canon a f, instantiateLevels_canon a x]
  | .lam x b => by simp only [instantiateLevels, instantiateLevels_canon a x, instantiateLevels_canon a b]
  | .pi x b => by simp only [instantiateLevels, instantiateLevels_canon a x, instantiateLevels_canon a b]
  | .letE x v b => by
      simp only [instantiateLevels, instantiateLevels_canon a x, instantiateLevels_canon a v,
        instantiateLevels_canon a b]
  | .lit _ => rfl

/-- the fields' telescope and the result `F ls (pl ++ res)`: `pl` the parameter locals at the current
    depth, `σ` the plain context into the current one. -/
def ctorFieldsT (f : Nat) (ls : List Level) :
    List (Expr Nat) → SubstT → List FieldT → List (Expr Nat) → Expr Nat
  | pl, σ, [], res => foldApps (.const f ls) (pl ++ res.map (substT σ))
  | pl, σ, .plain D _ :: fs, res =>
      .pi (substT σ D) (ctorFieldsT f ls (pl.map (lift 0 1)) σ.up fs res)
  | pl, σ, .drec idx :: fs, res =>
      .pi (foldApps (.const f ls) (pl ++ idx.map (substT σ)))
        (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res)
  | pl, σ, .drecD D _ :: fs, res =>
      .pi (substT σ D) (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res)

/-- the constructor's type BUILT from its view: the mirrors, then the fields from the exact
    parameter locals and the identity on the plain context. -/
def ctorTypeT (f : Nat) (ls : List Level) (mirrors : List (Expr Nat × Level)) (fields : List FieldT)
    (res : List (Expr Nat)) : Expr Nat :=
  policyPi (mirrors.map Prod.fst)
    (ctorFieldsT f ls (policyLocals mirrors.length) SubstT.id fields res)

/-- a minor premise's fields with their induction hypotheses, then its conclusion (05 §12): `pl` the
    parameter locals, `mot` the motive, `fl` the field locals so far, `σ` the plain context. After a
    directly recursive field its induction hypothesis `mot idx x`; the conclusion
    `mot res (c (pl ++ fl))`. -/
def minorFieldsT (f c : Nat) (ls : List Level) :
    List (Expr Nat) → Expr Nat → List (Expr Nat) → SubstT → List FieldT → List (Expr Nat) → Expr Nat
  | pl, mot, fl, σ, [], res =>
      foldApps mot (res.map (substT σ) ++ [foldApps (.const c ls) (pl ++ fl)])
  | pl, mot, fl, σ, .plain D _ :: fs, res =>
      .pi (substT σ D)
        (minorFieldsT f c ls (pl.map (lift 0 1)) (lift 0 1 mot) (fl.map (lift 0 1) ++ [.bvar 0])
          σ.up fs res)
  | pl, mot, fl, σ, .drec idx :: fs, res =>
      .pi (foldApps (.const f ls) (pl ++ idx.map (substT σ)))
        (.pi (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0]))
          (minorFieldsT f c ls (pl.map (lift 0 2)) (lift 0 2 mot) (fl.map (lift 0 2) ++ [.bvar 1])
            σ.shift1.shift1 fs res))
  | pl, mot, fl, σ, .drecD D idx :: fs, res =>
      .pi (substT σ D)
        (.pi (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0]))
          (minorFieldsT f c ls (pl.map (lift 0 2)) (lift 0 2 mot) (fl.map (lift 0 2) ++ [.bvar 1])
            σ.shift1.shift1 fs res))

/-- a constructor's data for its minor: reference, fields, result indices. -/
abbrev MinorDataT : Type := Nat × List FieldT × List (Expr Nat)

/-- `F ls (params ++ indices)` over the locals, in the context of the parameters and `ni` indices. -/
def famLocalsT (f : Nat) (ls : List Level) (np ni : Nat) : Expr Nat :=
  foldApps (.const f ls) ((policyLocals np).map (lift 0 ni) ++ policyLocals ni)

/-- a telescope's domains lifted past `a` binders inserted below it. -/
def liftDomsT (c a : Nat) : List (Expr Nat) → List (Expr Nat)
  | [] => []
  | D :: ds => lift c a D :: liftDomsT (c + 1) a ds

/-- the motive's type in the context of the parameters (05 §11). -/
def motTyT (f : Nat) (ls : List Level) (params indices : List (Expr Nat × Level)) (wM : Level) :
    Expr Nat :=
  policyPi (indices.map Prod.fst)
    (.pi (famLocalsT f ls params.length indices.length) (.sort wM))

/-- a constructor's minor premise type in the context of the parameters and the motive (05 §12). -/
def minorTyT (f : Nat) (ls : List Level) (np : Nat) (cd : MinorDataT) : Expr Nat :=
  minorFieldsT f cd.1 ls ((policyLocals np).map (lift 0 1)) (.bvar 0) [] SubstT.id.shift1
    cd.2.1 cd.2.2

/-- the minors' telescope: the `j`-th minor lifted past the `j` earlier ones. -/
def minorDomsT (f : Nat) (ls : List Level) (np : Nat) : Nat → List MinorDataT → List (Expr Nat)
  | _, [] => []
  | j, cd :: cds => lift 0 j (minorTyT f ls np cd) :: minorDomsT f ls np (j + 1) cds

/-- the recursor's body: `motive indices major`. -/
def recBodyT (ni k : Nat) : Expr Nat :=
  foldApps (.bvar (ni + k + 1)) ((policyLocals ni).map (lift 0 1) ++ [.bvar 0])

/-- the recursor's binders in 05 §11's order: the parameters, the motive, the minors, the indices,
    the major. -/
def recDomsT (f : Nat) (ls : List Level) (params indices : List (Expr Nat × Level)) (wM : Level)
    (cds : List MinorDataT) : List (Expr Nat) :=
  params.map Prod.fst ++ [motTyT f ls params indices wM] ++ minorDomsT f ls params.length 0 cds ++
    liftDomsT 0 (cds.length + 1) (indices.map Prod.fst) ++
    [lift indices.length (cds.length + 1) (famLocalsT f ls params.length indices.length)]

/-- THE RECURSOR'S TYPE built from the views (05 §13). -/
def recTypeT (f : Nat) (ls : List Level) (params indices : List (Expr Nat × Level)) (wM : Level)
    (cds : List MinorDataT) : Expr Nat :=
  policyPi (recDomsT f ls params indices wM cds) (recBodyT indices.length cds.length)

/-! ## (3) the views' typed content -/

/-- a telescope's domains as a context: the earliest outermost (innermost first). -/
def telCtxT (ds : List (Expr Nat × Level)) : LCtx :=
  (ds.map fun d => LocalDecl.assumption d.1).reverse

/-- a telescope's domains typed one after another, each at its recorded sort. -/
inductive TelTyT (E : ResolvedEnv) (n : Nat) : LCtx → List (Expr Nat × Level) → Type
  | nil (Γ : LCtx) : TelTyT E n Γ []
  | cons (Γ : LCtx) (D : Expr Nat) (u : Level) (ds : List (Expr Nat × Level))
      (hD : HasTyT E n Γ D (.sort u)) (tl : TelTyT E n (.assumption D :: Γ) ds) :
      TelTyT E n Γ ((D, u) :: ds)

/-- arguments typed along a Π-telescope down to its sort: a FULL application. -/
inductive ArgsTyT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → List (Expr Nat) → Type
  | nil (l : Level) : ArgsTyT E n Γ (.sort l) []
  | cons (A B a : Expr Nat) (as : List (Expr Nat)) (ha : HasTyT E n Γ a A)
      (tl : ArgsTyT E n Γ (instantiate0 a B) as) : ArgsTyT E n Γ (.pi A B) (a :: as)

/-- the parameter mirrors type-convertible to the family's parameters, position by position, in the
    context of the family's earlier parameters (05 §6.1), their sorts `=ₙ`. -/
inductive MirrorsConvT (E : ResolvedEnv) (n : Nat) :
    LCtx → List (Expr Nat × Level) → List (Expr Nat × Level) → Type
  | nil (Γ : LCtx) : MirrorsConvT E n Γ [] []
  | cons (Γ : LCtx) (M : Expr Nat) (um : Level) (P : Expr Nat) (up : Level)
      (ms ps : List (Expr Nat × Level)) (hc : TyConvT E n Γ M P) (hl : eqN um up)
      (tl : MirrorsConvT E n (.assumption P :: Γ) ms ps) :
      MirrorsConvT E n Γ ((M, um) :: ms) ((P, up) :: ps)

/-- the fields typed in the PLAIN context: a plain domain at its sort (the context grows by it); a
    recursive field's indices along the family's index telescope `idxTel k` (`k` plain fields so
    far); then the result indices. -/
inductive FieldsTyT (E : ResolvedEnv) (n : Nat) (idxTel : Nat → Expr Nat) :
    LCtx → Nat → List FieldT → List (Expr Nat) → Type
  | nil (Γ : LCtx) (k : Nat) (res : List (Expr Nat)) (hres : ArgsTyT E n Γ (idxTel k) res) :
      FieldsTyT E n idxTel Γ k [] res
  | plain (Γ : LCtx) (k : Nat) (D : Expr Nat) (u : Level) (fs : List FieldT) (res : List (Expr Nat))
      (hD : HasTyT E n Γ D (.sort u))
      (tl : FieldsTyT E n idxTel (.assumption D :: Γ) (k + 1) fs res) :
      FieldsTyT E n idxTel Γ k (.plain D u :: fs) res
  | drec (Γ : LCtx) (k : Nat) (idx : List (Expr Nat)) (fs : List FieldT) (res : List (Expr Nat))
      (hidx : ArgsTyT E n Γ (idxTel k) idx) (tl : FieldsTyT E n idxTel Γ k fs res) :
      FieldsTyT E n idxTel Γ k (.drec idx :: fs) res
  | drecD (Γ : LCtx) (k : Nat) (D : Expr Nat) (idx : List (Expr Nat)) (fs : List FieldT)
      (res : List (Expr Nat))
      (hidx : ArgsTyT E n Γ (idxTel k) idx) (tl : FieldsTyT E n idxTel Γ k fs res) :
      FieldsTyT E n idxTel Γ k (.drecD D idx :: fs) res

/-- the context of a field prefix's PLAIN fields (the δ-reached field's binder leaves the plain
    context, as `drec` does — the copy's `plainCtxA`, R-NoDeltaRec-4). -/
def plainCtxT : List FieldT → LCtx → LCtx
  | [], Γ => Γ
  | .plain D _ :: fs, Γ => plainCtxT fs (.assumption D :: Γ)
  | .drec _ :: fs, Γ => plainCtxT fs Γ
  | .drecD _ _ :: fs, Γ => plainCtxT fs Γ

/-- the consumed prefix commutes with the tail's context (plain binders stack inward). -/
theorem plainCtxT_append : (xs ys : List FieldT) → (Γ : LCtx) →
    plainCtxT (xs ++ ys) Γ = plainCtxT ys (plainCtxT xs Γ)
  | [], _, _ => rfl
  | .plain _ _ :: xs, ys, Γ => plainCtxT_append xs ys (.assumption _ :: Γ)
  | .drec _ :: xs, ys, Γ => plainCtxT_append xs ys Γ
  | .drecD _ _ :: xs, ys, Γ => plainCtxT_append xs ys Γ

/-! ## (3b) env extension at a fresh ref (R-NoDeltaRec-4d-ii)

The `.drecD` annotation arm annotates the surface domain under `extendEnv E f fm` — the
tree-side typings (`DrecDTypedT`, the walk's contexts) must first be weakened there. Every
member lookup an `E`-derivation makes is at an `E`-domain ref, hence fresh for `r`. -/

theorem members_extendEnv_ne (E : ResolvedEnv) (r : Nat) (m : CheckedMember) {r' : Nat}
    (h : r' ≠ r) : (extendEnv E r m).members r' = E.members r' := if_neg h

/-- a member hit in `E` is a member hit in its fresh-ref extension. -/
theorem members_extendEnv_of_some (E : ResolvedEnv) (r : Nat) (m : CheckedMember) {r' m'}
    (hfr : E.members r = none) (h : E.members r' = some m') :
    (extendEnv E r m).members r' = some m' := by
  have hne : r' ≠ r := fun hh => by rw [← hh, h] at hfr; exact Option.noConfusion hfr
  rw [members_extendEnv_ne E r m hne]; exact h

/-- an iota witness carries three member lookups, all at refs the witness proves are in `E`'s
    domain — the same lookups succeed in the extended environment. -/
def iotaWitness_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) (w : IotaWitness E) : IotaWitness (extendEnv E r m) :=
  { w with
    hrec := members_extendEnv_of_some E r m hfr w.hrec
    hctor := members_extendEnv_of_some E r m hfr w.hctor
    hfam := members_extendEnv_of_some E r m hfr w.hfam }

/-- the transported witness computes the same redex/contractum — only the proof fields moved. -/
def derivedIota_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) {lhs rhs : Expr Nat} :
    DerivedIota E lhs rhs → DerivedIota (extendEnv E r m) lhs rhs
  | .of w => .of (iotaWitness_extend hfr w)

mutual

/-- the tree's typing transports into an extension at a fresh ref (R-NoDeltaRec-4d-ii): every
    member read is at an `E`-domain ref. -/
def hasTyT_extendEnv {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → HasTyT (extendEnv E r m) n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A h => .bvar Γ i A h
  | _, _, _, .const Γ r' ls m' hres hlen hwf =>
      .const Γ r' ls m' (members_extendEnv_of_some E r m hfr hres) hlen hwf
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A u B v (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam Γ A u body B (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hbody)
  | _, _, _, .app Γ f a A B hf ha =>
      .app Γ f a A B (hasTyT_extendEnv hfr hf) (hasTyT_extendEnv hfr ha)
  | _, _, _, .letE Γ A u value B body hA hv hb =>
      .letE Γ A u value B body (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hv)
        (hasTyT_extendEnv hfr hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyT_extendEnv hfr hexp)
  | _, _, _, .conv Γ e A B u h hc =>
      .conv Γ e A B u (hasTyT_extendEnv hfr h) (convT_extendEnv hfr hc)

def convT_extendEnv {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → ConvT (extendEnv E r m) n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (hasTyT_extendEnv hfr h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (convT_extendEnv hfr h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      .trans Γ a b c A (convT_extendEnv hfr h1) (convT_extendEnv hfr h2)
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg =>
      .beta Γ A body arg B u (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hbody)
        (hasTyT_extendEnv hfr harg)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb =>
      .zeta Γ A value body B u (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hv)
        (hasTyT_extendEnv hfr hb)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (hasTyT_extendEnv hfr hv)
  | _, _, _, _, .delta Γ r' ls m' b hres hbody htr hlen hwf hb =>
      .delta Γ r' ls m' b (members_extendEnv_of_some E r m hfr hres)
        hbody htr hlen hwf (hasTyT_extendEnv hfr hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T (derivedIota_extend hfr h) (hasTyT_extendEnv hfr hlhs)
        (hasTyT_extendEnv hfr hrhs)
  | _, _, _, _, .lit Γ t exp T h hexp => .lit Γ t exp T h (hasTyT_extendEnv hfr hexp)
  | _, _, _, _, .app Γ f g a b A B h1 h2 =>
      .app Γ f g a b A B (convT_extendEnv hfr h1) (convT_extendEnv hfr h2)
  | _, _, _, _, .lam Γ A A' b b' B u hA hb =>
      .lam Γ A A' b b' B u (convT_extendEnv hfr hA) (convT_extendEnv hfr hb)
  | _, _, _, _, .pi Γ A A' B B' u v hA hB =>
      .pi Γ A A' B B' u v (convT_extendEnv hfr hA) (convT_extendEnv hfr hB)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb =>
      .letE Γ A A' v v' b b' B u (convT_extendEnv hfr hA) (convT_extendEnv hfr hv)
        (convT_extendEnv hfr hb)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r' ls ls' m' hres hlen hwf hwf' h =>
      .consts Γ r' ls ls' m' (members_extendEnv_of_some E r m hfr hres)
        hlen hwf hwf' h
  | _, _, _, _, .eta Γ f A B h => .eta Γ f A B (hasTyT_extendEnv hfr h)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyT_extendEnv hfr hP) (hasTyT_extendEnv hfr hp) (hasTyT_extendEnv hfr hq)
  | _, _, _, _, .tyConv Γ a b A A' u h hA =>
      .tyConv Γ a b A A' u (convT_extendEnv hfr h) (convT_extendEnv hfr hA)

end

/-- `TyConvT` transports to a fresh-ref extension (R-NoDeltaRec-4d-ii). -/
def tyConvT_extendEnv {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → TyConvT (extendEnv E r m) n Γ A B
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B u h => .of Γ A B u (convT_extendEnv hfr h)
  | _, _, _, .trans Γ A B C h1 h2 =>
      .trans Γ A B C (tyConvT_extendEnv hfr h1) (tyConvT_extendEnv hfr h2)

/-- `CtxWfT` transports to a fresh-ref extension (R-NoDeltaRec-4d-ii). -/
def ctxWfT_extendEnv {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (hfr : E.members r = none) :
    {Γ : LCtx} → CtxWfT E n Γ → CtxWfT (extendEnv E r m) n Γ
  | _, .nil => .nil
  | _, .assumption _ _ _ hΓ hA => .assumption _ _ _ (ctxWfT_extendEnv hfr hΓ) (hasTyT_extendEnv hfr hA)
  | _, .letBinding _ _ _ _ hΓ hA hv =>
      .letBinding _ _ _ _ (ctxWfT_extendEnv hfr hΓ) (hasTyT_extendEnv hfr hA) (hasTyT_extendEnv hfr hv)

/-- the plain-field count after some fields, from a start. -/
def plainIdxT : List FieldT → Nat → Nat
  | [], j => j
  | .plain _ _ :: fs, j => plainIdxT fs (j + 1)
  | .drec _ :: fs, j => plainIdxT fs j
  | .drecD _ _ :: fs, j => plainIdxT fs j

/-- does the field reach the family only through δ? -/
def FieldT.isDrecD : FieldT → Bool
  | .drecD _ _ => true
  | _ => false

/-! ## (4) the views -/

/-- the family view (05 §5): its parameters and indices with their sorts, its result sort; the stored
    type is the telescope over them. The parameter count is the group's declared one,
    `params.length`. -/
structure FamViewT (fm : CheckedMember) : Type where
  params : List (Expr Nat × Level)
  indices : List (Expr Nat × Level)
  sort : Level
  stored : fm.mtype = policyPi ((params ++ indices).map Prod.fst) (.sort sort)
  profile : UniformProp sort ∨ UniformType sort

/-- the family's index telescope, `Π indices, Sort sort`, in the context of its parameters. -/
def FamViewT.idxTel {fm : CheckedMember} (fv : FamViewT fm) : Expr Nat :=
  policyPi (fv.indices.map Prod.fst) (.sort fv.sort)

/-- the evidence a `drecD` field carries at view scope (the copy's `DrecDTypedA`, R-NoDeltaRec-4):
    its surface domain `D` types in the family's scope at the family's sort — in the plain context
    of the fields before it — converts there to the family application at its δ-normal indices, and
    its indices are level-bounded at the family's arity (the indices do not occur in the
    constructor's type, so their bound is evidence, not derivable). -/
def DrecDTypedT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (fv : FamViewT fm)
    (fields : List FieldT) : Prop :=
  ∀ (fsPre : List FieldT) (D : Expr Nat) (idx : List (Expr Nat)) (fsRest : List FieldT),
    fields = fsPre ++ FieldT.drecD D idx :: fsRest →
    Nonempty (HasTyT (extendEnv E f fm) fm.arity (plainCtxT fsPre (telCtxT fv.params)) D
      (.sort fv.sort)) ∧
    Nonempty (TyConvT (extendEnv E f fm) fm.arity (plainCtxT fsPre (telCtxT fv.params)) D
      (foldApps (.const f (canonLevels fm.arity))
        ((policyLocals fv.params.length).map (lift 0 (plainIdxT fsPre 0)) ++ idx))) ∧
    ∀ x ∈ idx, exprLevelsBounded fm.arity x = true

/-- vacuous when no field is δ-reached — how today's views discharge it. -/
theorem drecDTypedT_of_absent {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    {fields : List FieldT} (h : ∀ d ∈ fields, d.isDrecD = false) : DrecDTypedT E f fm fv fields :=
  fun fsPre D idx fsRest hfs => by
    have hmem : FieldT.drecD D idx ∈ fields := by
      rw [hfs]; exact List.mem_append_right _ (List.mem_cons_self _ _)
    exact Bool.noConfusion (h _ hmem)

/-- membership gives a split. -/
theorem List.mem_split' {α : Type} {a : α} {l : List α} (h : a ∈ l) : ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons x xs ih =>
      cases h with
      | head => exact ⟨[], xs, rfl⟩
      | tail _ h' => obtain ⟨s, t, rfl⟩ := ih h'; exact ⟨x :: s, t, rfl⟩

/-- the per-member bound — a `drecD` field's `∀ idx` side is evidence, read off the view. -/
theorem drecDTypedT_idxBounded {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    {fields : List FieldT} (hdd : DrecDTypedT E f fm fv fields)
    {D : Expr Nat} {idx : List (Expr Nat)} (hmem : FieldT.drecD D idx ∈ fields) :
    ∀ x ∈ idx, exprLevelsBounded fm.arity x = true := by
  obtain ⟨fsPre, fsRest, hfs⟩ := List.mem_split' hmem
  exact (hdd fsPre D idx fsRest hfs).2.2

/-- the constructor view (05 §6–§8) in the base `E`: the mirrors, the fields and the result indices
    in the plain context, typed there; the stored type BUILT from them. -/
structure CtorViewT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (fv : FamViewT fm)
    (cm : CheckedMember) : Type where
  mirrors : List (Expr Nat × Level)
  fields : List FieldT
  res : List (Expr Nat)
  stored : cm.mtype = ctorTypeT f (canonLevels fm.arity) mirrors fields res
  mirrorsConv : MirrorsConvT E fm.arity [] mirrors fv.params
  typed : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel) (telCtxT fv.params) 0 fields res
  univ : ∀ D u, FieldT.plain D u ∈ fields →
    UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN u fv.sort)
  /-- a δ-reached field carries its typing and conversion evidence in the family scope
      (R-NoDeltaRec-4); vacuous for views whose fields have no `drecD`. The checker's
      `drecDsCheckB` supplies it (-4c); consumers needing a `drecD`-free view take the
      absence as a premise. -/
  drecD_typed : DrecDTypedT E f fm fv fields

/-- a constructor of the group: its reference, its member, the member checks, its type typed in the
    base and the family (05 §4 ConstructorScope), its view. -/
structure GroupCtorT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (fv : FamViewT fm) : Type where
  ref : Nat
  member : CheckedMember
  hcls : member.mclass = .constructorM
  hnobody : member.body = none
  harity : member.arity = fm.arity
  hclT : ∀ k, lift k 1 member.mtype = member.mtype
  u : Level
  hT : HasTyT (extendEnv E f fm) member.arity [] member.mtype (.sort u)
  hlvl : exprLevelsBounded member.arity member.mtype = true
  view : CtorViewT E f fm fv member

def GroupCtorT.entry {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (c : GroupCtorT E f fm fv) : Nat × CheckedMember :=
  (c.ref, c.member)

def GroupCtorT.minorData {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (c : GroupCtorT E f fm fv) : MinorDataT :=
  (c.ref, c.view.fields, c.view.res)

/-- the environment after a group: the family at `f`, then its constructors (the list's head added
    last). -/
def groupEnvT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) :
    List (Nat × CheckedMember) → ResolvedEnv
  | [] => extendEnv E f fm
  | c :: cs => extendEnv (groupEnvT E f fm cs) c.1 c.2

/-- the group's references fresh one by one. -/
def GroupFreshT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) :
    List (Nat × CheckedMember) → Prop
  | [] => E.members f = none
  | c :: cs => GroupFreshT E f fm cs ∧ (groupEnvT E f fm cs).members c.1 = none

/-- the recursor type a group derives under a policy, from the family view and the constructors in
    candidate order (the list reversed), at the family's canonical levels. -/
def groupRecTypeT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (cs : List (GroupCtorT E f fm fv)) (elim : EliminationPolicy) : Expr Nat :=
  recTypeT f (canonLevels fm.arity) fv.params fv.indices (policyMotiveLevel fm.arity elim)
    (cs.reverse.map GroupCtorT.minorData)

/-- a group's recursor (05 §11–§13): the member, its checks, the elimination policy, the stored type
    BUILT from the views, typed with the constructors present (05 §4 DerivationScope). -/
structure GroupRecT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (fv : FamViewT fm)
    (cs : List (GroupCtorT E f fm fv)) : Type where
  member : CheckedMember
  hcls : member.mclass = .recursorM
  hnobody : member.body = none
  elim : EliminationPolicy
  harity : member.arity = policyRecursorArity fm.arity elim
  stored : member.mtype = groupRecTypeT cs elim
  hclT : ∀ k, lift k 1 member.mtype = member.mtype
  u : Level
  hT : HasTyT (groupEnvT E f fm (cs.map GroupCtorT.entry)) member.arity [] member.mtype (.sort u)
  hlvl : exprLevelsBounded member.arity member.mtype = true

end Rcic.Declarative
