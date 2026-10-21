import rcic.RcicTypedScopeCheck
import rcic.RcicIotaShapeAdapter

/-!
# W-3 — a certified checker with conversion

W-2's scope test runs with a checker (`CheckerT`). Its checker, `checkT`, compares types as written, so
a group whose typing needs a conversion step stays outside the scope. This module builds a checker that
takes such steps (`checkC`) and gives it to the test as `convChecker`.

* (1) Conversion, certified. Every step the checker takes is a derivation of the typed judgment, so the
  checker is sound by construction, as `checkT` is.
  - A head step on a type (`headStep?`): δ at a transparent constant (`ConvT.delta`), β at a λ applied to
    an argument (`ConvT.beta`), lifted through the spine by application congruence (`liftSpine`). Its
    parts are typed by `checkT`.
  - Head steps up to a fuel, each at a sort (`whnfTy`): a chain of type conversions (`TyConvT`).
  - Two types (`tyConv?`): equal as written; else head steps on both sides, then sorts at levels that
    `decEqN` equates (`ConvT.sorts`), or Π types domain- and codomain-wise (`ConvT.pi`), or two
    applications congruence-wise (arm 1 below).
  - Two terms at a type (`convAt?`), each part typed by the checker at one fuel less: equal as written;
    a head step on either side, moved to the type (`stepAt?`); and three arms:
    (1) application congruence (`appConvWith`, `ConvT.app`): the heads at the Π type the checker reads
        off the left head, the arguments at its domain;
    (2) literal expansion (`litAt?`, `ConvT.lit`): a numeral on either side through its expansion;
    (3) proof irrelevance (`irrAt?`, `ConvT.irr`): at a type the checker types at `Sort 0`, two terms
        it types there.
    `tyConv?` reaches `convAt?` only through arm 1, when head steps leave two applications that are not
    equal. Before the arms, `tyConv?` refused there. So the arms only turn a refusal into a
    derivation, and every answer the checker gave before, it gives again with the same derivation.
    Arms 2 and 3, and a δ step inside an argument, are reached inside an application (its head or an
    argument).
* (2) The checker (`checkC`): `checkT`'s rules (a numeral through its expansion, `checkLitT`), where a
  type that must be a sort or a Π type is read after head steps, and an argument's type is converted to
  the domain. Its rules are `checkWith`'s at `tyConv?`; `tyConv?`'s arms type their parts with
  `checkWith` at one fuel less. `tyAtC` checks a term against a type; `convChecker fuel` is the checker
  the test takes.
* (3) The fourth arm, ι (`iotaStepWith?`/`iotaBetaStep?`/`iotaMid?`, `ConvT.iota`): when head steps
  leave a recursor-on-constructor redex that the structural arms cannot compare — `recBL`'s
  applications inside `recNthB`-typed positions is the working example — `iotaReductCert` rebuilds
  the legacy `IotaWitness` (post-#6196 `ConvT.iota` carries `DerivedIota`, not `DerivedIotaT`), both
  sides are typed by `checkWith`, and `tyConv?`/`convAt?` continue on the reduct. `iotaBetaStep?`
  is the shared ι-or-β selector (`iotaStepWith?`, else `betaStepWith?`) at the step's own inferred
  type: the arm sits after whnf on the two sides `tyConv?` compares (typing the step needs `conv`,
  which only exists inside the mutual block) and alongside `stepAt?` inside `convAt?` — where its
  `none` falls through to the application-congruence and literal arms, so `convAt?` only ever
  gains `some`s.

What it does not do: η, ζ, a let-bound variable's value; congruence under a λ, a Π or a let between
two terms (`convAt?` relates such terms only when equal as written or after head steps), and two sorts
as terms; and the parts of a step (a δ body, a β argument) are typed as written.
-/

namespace Rcic.Declarative

/-! ## (1) conversion, certified -/

/-- a type conversion chain read backwards. -/
def TyConvT.symmT {E : ResolvedEnv} {n : Nat} : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B →
    TyConvT E n Γ B A
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B u c => .of Γ B A u (.symm Γ A B _ c)
  | _, _, _, .trans Γ A B C c₁ c₂ => .trans Γ C B A c₂.symmT c₁.symmT

/-- a typing moved along a type conversion chain. -/
def hasTyT_of_tyConv {E : ResolvedEnv} {n : Nat} {a : Expr Nat} :
    {Γ : LCtx} → {A B : Expr Nat} → HasTyT E n Γ a A → TyConvT E n Γ A B → HasTyT E n Γ a B
  | _, _, _, d, .refl _ _ => d
  | _, _, _, d, .of _ _ _ u c => .conv _ a _ _ u d c
  | _, _, _, d, .trans _ _ _ _ c₁ c₂ => hasTyT_of_tyConv (hasTyT_of_tyConv d c₁) c₂

/-- a conversion moved along a type conversion chain (`ConvT.tyConv` at each step). -/
def convT_of_tyConv {E : ResolvedEnv} {n : Nat} {a b : Expr Nat} :
    {Γ : LCtx} → {A B : Expr Nat} → ConvT E n Γ a b A → TyConvT E n Γ A B → ConvT E n Γ a b B
  | _, _, _, c, .refl _ _ => c
  | _, _, _, c, .of _ _ _ u cT => .tyConv _ a b _ _ u c cT
  | _, _, _, c, .trans _ _ _ _ c₁ c₂ => convT_of_tyConv (convT_of_tyConv c c₁) c₂

/-- a conversion of a spine's head lifted through its arguments (application congruence), each
    argument typed at its domain as written. -/
def liftSpine (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    (f g T : Expr Nat) → ConvT E n Γ f g T → (args : List (Expr Nat)) →
    Option (Σ T', ConvT E n Γ (foldApps f args) (foldApps g args) T')
  | _, _, T, c, [] => some ⟨T, c⟩
  | f, g, .pi A B, c, a :: as =>
      match synCheck E n Γ a A with
      | some ha =>
          liftSpine E n Γ (.app f a) (.app g a) (instantiate0 a B) (.app Γ f g a a A B c (.refl Γ a A ha)) as
      | none => none
  | _, _, _, _, _ :: _ => none

/-- one head step with its conversion: δ at a transparent constant, β at a λ applied to an argument. -/
def headStep? (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    (hd : Expr Nat) → (args : List (Expr Nat)) → Option (Σ T e', ConvT E n Γ (foldApps hd args) e' T)
  | .const r ls, args =>
      match hres : E.members r with
      | some m =>
          if htr : transparent m.mclass = true then
            match hbody : m.body with
            | some b =>
                if hlen : ls.length = m.arity then
                  if hwf : levelsBounded n ls = true then
                    match synCheck E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) with
                    | some hb =>
                        (liftSpine E n Γ _ _ _ (.delta Γ r ls m b hres hbody htr hlen hwf hb) args).map
                          fun p => ⟨p.1, _, p.2⟩
                    | none => none
                  else none
                else none
            | none => none
          else none
      | none => none
  | .lam A body, arg :: rest =>
      match checkT E n Γ A, checkT E n (.assumption A :: Γ) body, synCheck E n Γ arg A with
      | some ⟨.sort u, hA⟩, some ⟨B, hbody⟩, some harg =>
          (liftSpine E n Γ _ _ _ (.beta Γ A body arg B u hA hbody harg) rest).map fun p => ⟨p.1, _, p.2⟩
      | _, _, _ => none
  | _, _ => none

/-- head steps on a type, each at a sort, up to `fuel`: a type conversion chain to the result. -/
def whnfTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Nat → (T : Expr Nat) → Σ T', TyConvT E n Γ T T'
  | 0, T => ⟨T, .refl Γ T⟩
  | fuel + 1, T =>
      match headStep? E n Γ (appsSpine T).1 (appsSpine T).2 with
      | some ⟨.sort u, T', c⟩ =>
          let r := whnfTy E n Γ fuel T'
          ⟨r.1, .trans Γ T T' r.1 (.of Γ T T' u (foldApps_appsSpine T ▸ c)) r.2⟩
      | _ => ⟨T, .refl Γ T⟩

/-- a type read as a sort after head steps. -/
def toSort? (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (T : Expr Nat) :
    Option (Σ u, TyConvT E n Γ T (.sort u)) :=
  let r := whnfTy E n Γ fuel T
  match h : r.1 with
  | .sort u => some ⟨u, h ▸ r.2⟩
  | _ => none

/-- a type read as a Π type after head steps. -/
def toPi? (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (T : Expr Nat) :
    Option (Σ A B, TyConvT E n Γ T (.pi A B)) :=
  let r := whnfTy E n Γ fuel T
  match h : r.1 with
  | .pi A B => some ⟨A, B, h ▸ r.2⟩
  | _ => none

/-- THE CHECKER'S RULES over a type conversion `conv`: `checkT`'s rules, where a type that must be a
    sort or a Π type is read after head steps, and an argument's type (a let value's) is converted to
    the domain by `conv`. Each answer carries its derivation. The checker with conversion is this at
    `tyConv?` (`checkC`); `tyConv?`'s arms type their parts with it at one fuel less. -/
def checkWith (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)) :
    (Γ : LCtx) → (e : Expr Nat) → Option (Σ T, HasTyT E n Γ e T)
  | Γ, .sort l => some ⟨_, .sort Γ l⟩
  | Γ, .bvar i =>
      match h : lookupType Γ i with
      | some A => some ⟨A, .bvar Γ i A h⟩
      | none => none
  | Γ, .const r ls => checkConstT E n Γ r ls
  | Γ, .pi A B =>
      match checkWith E n fuel conv Γ A, checkWith E n fuel conv (.assumption A :: Γ) B with
      | some ⟨TA, dA⟩, some ⟨TB, dB⟩ =>
          match toSort? E n fuel Γ TA, toSort? E n fuel (.assumption A :: Γ) TB with
          | some ⟨u, cA⟩, some ⟨v, cB⟩ =>
              some ⟨_, .pi Γ A u B v (hasTyT_of_tyConv dA cA) (hasTyT_of_tyConv dB cB)⟩
          | _, _ => none
      | _, _ => none
  | Γ, .lam A b =>
      match checkWith E n fuel conv Γ A, checkWith E n fuel conv (.assumption A :: Γ) b with
      | some ⟨TA, dA⟩, some ⟨B, db⟩ =>
          match toSort? E n fuel Γ TA with
          | some ⟨u, cA⟩ => some ⟨_, .lam Γ A u b B (hasTyT_of_tyConv dA cA) db⟩
          | none => none
      | _, _ => none
  | Γ, .app f a =>
      match checkWith E n fuel conv Γ f, checkWith E n fuel conv Γ a with
      | some ⟨Tf, df⟩, some ⟨Ta, da⟩ =>
          match toPi? E n fuel Γ Tf with
          | some ⟨A, B, cf⟩ =>
              match conv Γ Ta A with
              | some ca => some ⟨_, .app Γ f a A B (hasTyT_of_tyConv df cf) (hasTyT_of_tyConv da ca)⟩
              | none => none
          | none => none
      | _, _ => none
  | Γ, .letE A v b =>
      match checkWith E n fuel conv Γ A, checkWith E n fuel conv Γ v,
          checkWith E n fuel conv (.letBinding A v :: Γ) b with
      | some ⟨TA, dA⟩, some ⟨Tv, dv⟩, some ⟨B, db⟩ =>
          match toSort? E n fuel Γ TA, conv Γ Tv A with
          | some ⟨u, cA⟩, some cv =>
              some ⟨_, .letE Γ A u v B b (hasTyT_of_tyConv dA cA) (hasTyT_of_tyConv dv cv) db⟩
          | _, _ => none
      | _, _, _ => none
  | Γ, .lit t => (checkLitT E n Γ t).map fun p => ⟨p.1, .lit Γ t p.1 p.2⟩

/-- a term checked against a type by `checkWith`: its type converted to the one asked for by `conv`. -/
def tyAtWith (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (e T : Expr Nat) : Option (HasTyT E n Γ e T) :=
  match checkWith E n fuel conv Γ e with
  | some ⟨T', d⟩ => (conv Γ T' T).map (hasTyT_of_tyConv d)
  | none => none

/-- a head step on a term (`headStep?`), its conversion moved to the type `T` asked for by `conv`. -/
def stepAt? (E : ResolvedEnv) (n : Nat) (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (e T : Expr Nat) : Option (Σ e', ConvT E n Γ e e' T) :=
  match headStep? E n Γ (appsSpine e).1 (appsSpine e).2 with
  | some ⟨U, e', c⟩ => (conv Γ U T).map fun cU => ⟨e', convT_of_tyConv (foldApps_appsSpine e ▸ c) cU⟩
  | none => none

/-- ARM (1), APPLICATION CONGRUENCE: two applications `f a` and `g b`; the heads converted by `convAt`
    at the Π type the checker reads off `f` (`checkWith`, then `toPi?`), the arguments at its domain;
    the conversion at the type `ConvT.app` gives. -/
def appConvWith (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (convAt : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T))
    (Γ : LCtx) (f a g b : Expr Nat) : Option (Σ U, ConvT E n Γ (.app f a) (.app g b) U) :=
  match checkWith E n fuel conv Γ f with
  | some ⟨Tf, _⟩ =>
      match toPi? E n fuel Γ Tf with
      | some ⟨A, B, _⟩ =>
          match convAt Γ f g (.pi A B), convAt Γ a b A with
          | some c₁, some c₂ => some ⟨_, .app Γ f g a b A B c₁ c₂⟩
          | _, _ => none
      | none => none
  | none => none

/-- ARM (2), LITERAL EXPANSION: a numeral converted to its expansion (`ConvT.lit`), the expansion typed
    as the checker types a numeral (`checkLitT`), moved to the type `T` asked for by `conv`. -/
def litAt? (E : ResolvedEnv) (n : Nat) (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (t : Nat) (T : Expr Nat) : Option (ConvT E n Γ (.lit t) (natExpand t) T) :=
  match checkLitT E n Γ t with
  | some ⟨U, hexp⟩ => (conv Γ U T).map (convT_of_tyConv (.lit Γ t _ U (.of t) hexp))
  | none => none

/-- ARM (3), PROOF IRRELEVANCE: at a type `P` the checker types at `Sort 0`, two terms it types at `P`
    (`ConvT.irr`). -/
def irrAt? (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (p q P : Expr Nat) : Option (ConvT E n Γ p q P) :=
  match tyAtWith E n fuel conv Γ P (.sort .zero) with
  | some hP =>
      match tyAtWith E n fuel conv Γ p P, tyAtWith E n fuel conv Γ q P with
      | some hp, some hq => some (.irr Γ P p q hP hp hq)
      | _, _ => none
  | none => none

/-- the spine of a λ-headed application, read back as a single `foldApps`: the β step's lhs. -/
theorem foldApps_lam_spine {a A body arg : Expr Nat} {rest : List (Expr Nat)}
    (h : appsSpine a = (.lam A body, arg :: rest)) :
    a = foldApps (.app (.lam A body) arg) rest := by
  calc a = foldApps (appsSpine a).1 (appsSpine a).2 := (foldApps_appsSpine a).symm
    _ = foldApps (.app (.lam A body) arg) rest := by rw [h]; rfl

/-- `liftSpine` with each argument typed at its domain by conversion: `tyAtWith` at `conv`
    instead of `synCheck`. `betaStepWith?`'s spine carrier — an ι reduct like a minor-case lam
    applied to the constructor fields and the recursive call has a `rec`-application argument
    whose type only converts to the lam's domain, so `synCheck` would refuse it as written. -/
def liftSpineWith (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) :
    (f g T : Expr Nat) → ConvT E n Γ f g T → (args : List (Expr Nat)) →
    Option (Σ T', ConvT E n Γ (foldApps f args) (foldApps g args) T')
  | _, _, T, c, [] => some ⟨T, c⟩
  | f, g, .pi A B, c, a :: as =>
      match tyAtWith E n fuel conv Γ a A with
      | some ha =>
          liftSpineWith E n fuel conv Γ (.app f a) (.app g a) (instantiate0 a B)
            (.app Γ f g a a A B c (.refl Γ a A ha)) as
      | none => none
  | _, _, _, _, _ :: _ => none

/-- a β spine step whose parts are typed by `checkWith` at `conv` rather than `checkT` as written:
    `headStep?`'s β case where the λ's domain, body, and first argument may need conversion to
    type (a motive lam whose body applies a recursor, for instance). The step is legal inside
    `tyConv?`/`convAt?`, where `conv` exists. The remaining spine arguments are carried by
    `liftSpineWith`: they too may need conversion (`rec`-application arguments of an ι reduct). -/
def betaStepWith? (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (a : Expr Nat) : Option (Σ U e', ConvT E n Γ a e' U) :=
  match hs : appsSpine a with
  | (.lam A body, arg :: rest) =>
      match checkWith E n fuel conv Γ A,
          checkWith E n fuel conv (.assumption A :: Γ) body,
          tyAtWith E n fuel conv Γ arg A with
      | some ⟨.sort u, hA⟩, some ⟨B, hbody⟩, some harg =>
          (liftSpineWith E n fuel conv Γ _ _ _ (.beta Γ A body arg B u hA hbody harg) rest).map
            fun ⟨U, c⟩ => ⟨U, _, (foldApps_lam_spine hs).symm ▸ c⟩
      | _, _, _ => none
  | _ => none

/-- ARM (4), IOTA: a recursor-on-constructor redex. `iotaReductCert` (the legacy recognizer)
    finds the `IotaWitness`; `ConvT.iota` emits the step with a real `DerivedIota`
    (`DerivedIota.of w`). Both sides are typed by `checkWith` at `conv`, the reduct's inferred
    type converted to the redex's (`conv Γ U' U`), and the step is placed at the redex's own
    inferred type `U` — each caller moves it where it needs it (a sort for `tyConv?`'s middle,
    the asked-for `T` for `convAt?`). Unlike `headStep?`'s β/δ, the ι step is not folded into
    `whnfTy`: typing the two sides needs the conversion `conv`, which only exists inside
    `tyConv?`'s mutual block, so the arm fires on the whnf'ed sides `tyConv?` compares and
    inside `convAt?`'s step selector. -/
def iotaStepWith? (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (a : Expr Nat) : Option (Σ U e', ConvT E n Γ a e' U) :=
  match iotaReductCert E a with
  | some ⟨w, hwl⟩ =>
      match checkWith E n fuel conv Γ a, checkWith E n fuel conv Γ (iotaRhsOf w) with
      | some ⟨U, hl⟩, some ⟨U', hr⟩ =>
          (conv Γ U' U).map fun cU'U => ⟨U, iotaRhsOf w,
            hwl ▸ ConvT.iota Γ (iotaLhsOf w) (iotaRhsOf w) U (DerivedIota.of w)
              (hwl.symm ▸ hl) (hasTyT_of_tyConv hr cU'U)⟩
      | _, _ => none
  | none => none

/-- the extra-step selector `tyConv?`'s middle (`iotaMid?`) and `convAt?` share: a
    recursor-on-constructor redex (`iotaStepWith?`) or a λ-headed application the syntactic
    head stepper could not type (`betaStepWith?`) — whichever fires first, at the step's own
    inferred type; each site places it (a sort / the asked-for `T`). -/
def iotaBetaStep? (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (a : Expr Nat) : Option (Σ U e', ConvT E n Γ a e' U) :=
  match iotaStepWith? E n fuel conv Γ a with
  | some s => some s
  | none => betaStepWith? E n fuel conv Γ a

/-- the extra-step arm inside `tyConv?`'s middle: whichever whnf'ed side still steps under
    `iotaBetaStep?` steps first, the step placed at the sort `toSort?` reads off the step's
    inferred type, then `conv` continues the search on the reduct. The right-side step is a
    `ConvT.symm` before `TyConvT.of`. -/
def iotaMid? (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (rA rB : Expr Nat) : Option (TyConvT E n Γ rA rB) :=
  let step? := fun (a : Expr Nat) =>
    (match iotaBetaStep? E n fuel conv Γ a with
    | some ⟨U, a', c⟩ =>
        (toSort? E n fuel Γ U).map fun ⟨u, cU⟩ => ⟨u, a', convT_of_tyConv c cU⟩
    | none => none : Option (Σ' u e', ConvT E n Γ a e' (.sort u)))
  match step? rA, step? rB with
  | some ⟨u, a', c⟩, _ =>
      (conv Γ a' rB).map fun d => .trans Γ rA a' rB (.of Γ rA a' u c) d
  | none, some ⟨u, b', c⟩ =>
      (conv Γ rA b').map fun d =>
        .trans Γ rA b' rB d (.of Γ b' rB u (ConvT.symm Γ rB b' (.sort u) c))
  | none, none => none

mutual

/-- a type conversion the checker builds: equal as written; after up to `fuel` head steps on each side,
    sorts at levels `decEqN` equates, Π types domain- and codomain-wise (one fuel less), (arm 1) two
    applications congruence-wise (`appConvWith`, one fuel less), at the sort `toSort?` reads off the
    rule's type, and (arm 4) a recursor-on-constructor redex on either side stepped by `ConvT.iota`
    (`iotaMid?`, one fuel less). At no fuel, equal as written. -/
def tyConv? (E : ResolvedEnv) (n : Nat) : Nat → (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)
  | 0, Γ, A, B => if h : A = B then some (h ▸ .refl Γ A) else none
  | fuel + 1, Γ, A, B =>
      if h : A = B then some (h ▸ .refl Γ A) else
      let rA := whnfTy E n Γ (fuel + 1) A
      let rB := whnfTy E n Γ (fuel + 1) B
      let mid : Option (TyConvT E n Γ rA.1 rB.1) :=
        if h' : rA.1 = rB.1 then some (h' ▸ .refl Γ rA.1) else
        match rA.1, rB.1 with
        | .sort l₁, .sort l₂ =>
            if hl : decEqN l₁ l₂ = true then some (.of Γ _ _ _ (.sorts Γ l₁ l₂ (decEqN_sound l₁ l₂ hl)))
            else none
        | .pi A₁ B₁, .pi A₂ B₂ =>
            match tyConv? E n fuel Γ A₁ A₂, tyConv? E n fuel (.assumption A₁ :: Γ) B₁ B₂ with
            | some cA, some cB =>
                piCongr? E n fuel (tyConv? E n fuel) Γ A₁ A₂ B₁ B₂ cA cB
            | _, _ => none
        | .app f a, .app g b =>
            match appConvWith E n fuel (tyConv? E n fuel) (convAt? E n fuel) Γ f a g b with
            | some ⟨U, c⟩ =>
                (toSort? E n fuel Γ U).map fun s => TyConvT.of Γ _ _ s.1 (convT_of_tyConv c s.2)
            | none => none
        | _, _ => none
      let mid := match mid with
        | some c => some c
        | none => iotaMid? E n fuel (tyConv? E n fuel) Γ rA.1 rB.1
      mid.map fun c => .trans Γ A rA.1 B rA.2 (.trans Γ rA.1 rB.1 B c rB.2.symmT)
where
  /-- a Π type converted codomain-first (under the old domain), then domain-wise (under the new
      codomain). The domain is typed by `checkWith` at `conv`: a domain that only converts to a
      sort (a motive application, for instance) still yields the `ConvT.pi` step. -/
  piCongr? (E : ResolvedEnv) (n fuel : Nat)
      (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
      (Γ : LCtx) (A₁ A₂ B₁ B₂ : Expr Nat)
      (cA : TyConvT E n Γ A₁ A₂) (cB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
      Option (TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :=
    match checkWith E n fuel conv Γ A₁ with
    | some ⟨TA₁, dA⟩ =>
        match toSort? E n fuel Γ TA₁ with
        | some ⟨u, cAs⟩ =>
            match codChain E n Γ A₁ u (hasTyT_of_tyConv dA cAs) cB,
                domChain E n fuel conv Γ B₂ cA with
            | some c₁, some c₂ => some (.trans Γ _ _ _ c₁ c₂)
            | _, _ => none
        | none => none
    | _ => none
  /-- each codomain step under the fixed domain. -/
  codChain (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (hA : HasTyT E n Γ A (.sort u)) :
      {B B' : Expr Nat} → TyConvT E n (.assumption A :: Γ) B B' → Option (TyConvT E n Γ (.pi A B) (.pi A B'))
    | _, _, .refl _ B => some (.refl Γ (.pi A B))
    | _, _, .of _ X Y v c => some (.of Γ _ _ _ (.pi Γ A A X Y u v (.refl Γ A (.sort u) hA) c))
    | _, _, .trans _ _ _ _ c₁ c₂ =>
        match codChain E n Γ A u hA c₁, codChain E n Γ A u hA c₂ with
        | some d₁, some d₂ => some (.trans Γ _ _ _ d₁ d₂)
        | _, _ => none
  /-- each domain step under the fixed codomain, the codomain typed under the step's source —
      again by `checkWith`: a codomain that only converts to a sort still yields the step. -/
  domChain (E : ResolvedEnv) (n fuel : Nat)
      (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
      (Γ : LCtx) (B : Expr Nat) :
      {A A' : Expr Nat} → TyConvT E n Γ A A' → Option (TyConvT E n Γ (.pi A B) (.pi A' B))
    | _, _, .refl _ A => some (.refl Γ (.pi A B))
    | _, _, .of _ X Y u c =>
        match checkWith E n fuel conv (.assumption X :: Γ) B with
        | some ⟨TB, dB⟩ =>
            match toSort? E n fuel (.assumption X :: Γ) TB with
            | some ⟨v, cBs⟩ =>
                some (.of Γ _ _ _
                  (.pi Γ X Y B B u v c
                    (.refl (.assumption X :: Γ) B (.sort v) (hasTyT_of_tyConv dB cBs))))
            | none => none
        | _ => none
    | _, _, .trans _ _ _ _ c₁ c₂ =>
        match domChain E n fuel conv Γ B c₁, domChain E n fuel conv Γ B c₂ with
        | some d₁, some d₂ => some (.trans Γ _ _ _ d₁ d₂)
        | _, _ => none

/-- a conversion at a type `T` the checker builds, between two terms, each part typed by the checker at
    one fuel less (`checkWith` at `tyConv?`). In this order: equal as written, typed at `T` (at no fuel,
    typed as written); (arm 3) proof irrelevance at `T` (`irrAt?`); a head step on either side, moved to
    `T` (`stepAt?`); (arm 4) a recursor-on-constructor redex or a λ-headed application the head stepper
    could not type on either side, stepped by `iotaBetaStep?` and moved to `T` — on `none` the search
    falls through to the rest (<|>), so `convAt?` only ever gains `some`s;
    (arm 1) two applications congruence-wise (`appConvWith`), moved to `T`; (arm 2) a numeral on
    either side through its expansion (`litAt?`), then the rest. -/
def convAt? (E : ResolvedEnv) (n : Nat) : Nat → (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)
  | 0, Γ, a, b, T =>
      if h : a = b then
        match synCheck E n Γ a T with
        | some d => some (h ▸ .refl Γ a T d)
        | none => none
      else none
  | fuel + 1, Γ, a, b, T =>
      if h : a = b then
        match tyAtWith E n fuel (tyConv? E n fuel) Γ a T with
        | some d => some (h ▸ .refl Γ a T d)
        | none => none
      else
      match irrAt? E n fuel (tyConv? E n fuel) Γ a b T with
      | some c => some c
      | none =>
        match stepAt? E n (tyConv? E n fuel) Γ a T, stepAt? E n (tyConv? E n fuel) Γ b T with
        | some ⟨a', c⟩, _ => (convAt? E n fuel Γ a' b T).map (ConvT.trans Γ a a' b T c)
        | none, some ⟨b', c⟩ =>
            (convAt? E n fuel Γ a b' T).map fun c' => ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c)
        | none, none =>
          let step? := fun (x : Expr Nat) =>
            (match iotaBetaStep? E n fuel (tyConv? E n fuel) Γ x with
            | some ⟨U, x', c⟩ =>
                (tyConv? E n fuel Γ U T).map fun cU => ⟨x', convT_of_tyConv c cU⟩
            | none => none : Option (Σ e', ConvT E n Γ x e' T))
          (match step? a, step? b with
          | some ⟨a', c⟩, _ =>
              (convAt? E n fuel Γ a' b T).map (ConvT.trans Γ a a' b T c)
          | none, some ⟨b', c⟩ =>
              (convAt? E n fuel Γ a b' T).map fun c' =>
                ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c)
          | none, none => none) <|>
          match a, b with
          | .app f x, .app g y =>
              match appConvWith E n fuel (tyConv? E n fuel) (convAt? E n fuel) Γ f x g y with
              | some ⟨U, c⟩ => (tyConv? E n fuel Γ U T).map (convT_of_tyConv c)
              | none => none
          | .lit t, b' =>
              match litAt? E n (tyConv? E n fuel) Γ t T, convAt? E n fuel Γ (natExpand t) b' T with
              | some c, some c' => some (ConvT.trans Γ _ _ _ T c c')
              | _, _ => none
          | a', .lit t =>
              match litAt? E n (tyConv? E n fuel) Γ t T, convAt? E n fuel Γ a' (natExpand t) T with
              | some c, some c' => some (ConvT.trans Γ _ _ _ T c' (ConvT.symm Γ _ _ T c))
              | _, _ => none
          | _, _ => none

end

/-! ## (2) the checker with conversion -/

/-- THE CHECKER WITH CONVERSION: the checker's rules (`checkWith`) at the conversion `tyConv?`. Each
    answer carries its derivation. -/
def checkC (E : ResolvedEnv) (n fuel : Nat) : (Γ : LCtx) → (e : Expr Nat) → Option (Σ T, HasTyT E n Γ e T) :=
  checkWith E n fuel (tyConv? E n fuel)

/-- the checker's type. -/
def inferC (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (e : Expr Nat) : Option (Expr Nat) :=
  (checkC E n fuel Γ e).map Sigma.fst

/-- a term checked against a type: its type converted to the one asked for. -/
def tyAtC (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (e T : Expr Nat) : Option (HasTyT E n Γ e T) :=
  tyAtWith E n fuel (tyConv? E n fuel) Γ e T

/-- the sort a type lives in, read after head steps. -/
def sortOfC (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (e : Expr Nat) : Option Level :=
  match checkC E n fuel Γ e with
  | some ⟨T, _⟩ => (toSort? E n fuel Γ T).map Sigma.fst
  | none => none

/-- W-3's checker for the scope test, at a fuel: types converted by `tyConv?`, levels ordered by
    `geq`. -/
def convChecker (fuel : Nat) : CheckerT where
  check E n Γ e T := tyAtC E n fuel Γ e T
  sortOf E n Γ e := sortOfC E n fuel Γ e
  conv E n Γ A B := tyConv? E n fuel Γ A B
  levelLe u s := geq s u 0
  levelLe_sound _ _ h := leN_of_geq h

end Rcic.Declarative

#print axioms Rcic.Declarative.TyConvT.symmT
#print axioms Rcic.Declarative.hasTyT_of_tyConv
#print axioms Rcic.Declarative.convT_of_tyConv
#print axioms Rcic.Declarative.liftSpine
#print axioms Rcic.Declarative.headStep?
#print axioms Rcic.Declarative.whnfTy
#print axioms Rcic.Declarative.toSort?
#print axioms Rcic.Declarative.toPi?
#print axioms Rcic.Declarative.checkWith
#print axioms Rcic.Declarative.tyAtWith
#print axioms Rcic.Declarative.stepAt?
#print axioms Rcic.Declarative.appConvWith
#print axioms Rcic.Declarative.litAt?
#print axioms Rcic.Declarative.irrAt?
#print axioms Rcic.Declarative.foldApps_lam_spine
#print axioms Rcic.Declarative.liftSpineWith
#print axioms Rcic.Declarative.betaStepWith?
#print axioms Rcic.Declarative.iotaStepWith?
#print axioms Rcic.Declarative.iotaBetaStep?
#print axioms Rcic.Declarative.iotaMid?
#print axioms Rcic.Declarative.tyConv?
#print axioms Rcic.Declarative.convAt?
#print axioms Rcic.Declarative.checkC
#print axioms Rcic.Declarative.tyAtC
#print axioms Rcic.Declarative.convChecker
