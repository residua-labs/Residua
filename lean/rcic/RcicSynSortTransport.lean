import rcic.RcicTypedSubstLet
import rcic.RcicTypedLevels
import rcic.RcicSynTable

/-!
# Native transport chains for stored sort witnesses

An indexed chain records only the landed native weakening, substitution and
level-instantiation operations. Its evaluator materializes an actual native
typing from the original witness. It does not assume sort coherence or identify
that witness with an independently chosen enriched derivation.

The original ambient-prefix receipt is external to this chain: appending a
transport does not assert a decrease of the materialized derivation's weight.
`closure_claim` remains 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A finite, forward transport of a sort-typed domain witness, at fixed `E`.
    The source endpoint is a parameter; the current endpoint is indexed. -/
inductive SortTyTransport (E : ResolvedEnv) (a : Nat) (Δ₀ : LCtx)
    (A₀ : Expr Nat) (u₀ : Level) : Nat → LCtx → Expr Nat → Level → Type
  | refl : SortTyTransport E a Δ₀ A₀ u₀ a Δ₀ A₀ u₀
  | wk {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
      (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
      (d : LocalDecl) (c : Nat) (hcl : EnvClosed E) :
      SortTyTransport E a Δ₀ A₀ u₀ n (insertAt d c Δ) (lift c 1 A) u
  | esub {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
      (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
      (v t : Expr Nat) (j : Nat)
      (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
      (hget : Δ[j]? = some (.assumption t))
      (hv : HasTyT E n (substRemove v j Δ) (lift 0 j v) (lift 0 j t)) :
      SortTyTransport E a Δ₀ A₀ u₀ n (substRemove v j Δ)
        (instantiate j (lift 0 j v) A) u
  | lsub {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
      (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
      (t w0 : Expr Nat) (j : Nat)
      (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
      (hget : Δ[j]? = some (.letBinding t w0))
      (hv : HasTyT E n (substRemove w0 j Δ) (lift 0 j w0) (lift 0 j t)) :
      SortTyTransport E a Δ₀ A₀ u₀ n (substRemove w0 j Δ)
        (instantiate j (lift 0 j w0) A) u
  | linst {m : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
      (path : SortTyTransport E a Δ₀ A₀ u₀ m Δ A u)
      (n : Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = m)
      (hEL : EnvLevelsT E) (hIL : IotaLevelsT E) :
      SortTyTransport E a Δ₀ A₀ u₀ n (instLvlsCtx ls Δ)
        (instantiateLevels ls A) (instLevel ls u)

namespace SortTyTransport

variable {E : ResolvedEnv} {a : Nat} {Δ₀ : LCtx} {A₀ : Expr Nat} {u₀ : Level}

/-- Materialize precisely the native operations recorded by the chain. -/
def run {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (chain : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) : HasTyT E n Δ A (.sort u) :=
  match chain with
  | .refl => hA₀
  | .wk path d c hcl => hasTyTWeaken d hcl (c := c) (path.run hA₀)
  | .esub path v t j hcl hinst hget hv =>
      hasTyT_substS hcl hinst v t (j := j) (path.run hA₀) hget hv
  | .lsub path t w0 j hcl hinst hget hv =>
      hasTyT_substLetS hcl hinst t w0 (j := j) (path.run hA₀) hget hv
  | .linst path _ ls hls hlen hEL hIL =>
      hasTyT_instLevels hEL hIL hls hlen (path.run hA₀)

/-- Number of recorded transports; not a bound on the resulting typing weight. -/
def length {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level} :
    SortTyTransport E a Δ₀ A₀ u₀ n Δ A u → Nat
  | .refl => 0
  | .wk path _ _ _ => path.length + 1
  | .esub path _ _ _ _ _ _ _ => path.length + 1
  | .lsub path _ _ _ _ _ _ _ => path.length + 1
  | .linst path _ _ _ _ _ _ => path.length + 1

/-- Compose forward chains, retaining every recorded native operation. -/
def append {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (p : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    {k : Nat} {Ξ : LCtx} {B : Expr Nat} {v : Level}
    (q : SortTyTransport E n Δ A u k Ξ B v) :
    SortTyTransport E a Δ₀ A₀ u₀ k Ξ B v :=
  match q with
  | .refl => p
  | .wk path d c hcl => (p.append path).wk d c hcl
  | .esub path value t j hcl hinst hget hv =>
      (p.append path).esub value t j hcl hinst hget hv
  | .lsub path t w0 j hcl hinst hget hv =>
      (p.append path).lsub t w0 j hcl hinst hget hv
  | .linst path n ls hls hlen hEL hIL =>
      (p.append path).linst n ls hls hlen hEL hIL

/-- Materialization composes using precisely the two recorded chains. -/
theorem run_append {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (p : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    {k : Nat} {Ξ : LCtx} {B : Expr Nat} {v : Level}
    (q : SortTyTransport E n Δ A u k Ξ B v)
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (p.append q).run hA₀ = q.run (p.run hA₀) := by
  induction q with
  | refl => rfl
  | wk path d c hcl ih => simp only [append, run, ih]
  | esub path value t j hcl hinst hget hv ih => simp only [append, run, ih]
  | lsub path t w0 j hcl hinst hget hv ih => simp only [append, run, ih]
  | linst path n ls hls hlen hEL hIL ih => simp only [append, run, ih]

theorem length_append {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (p : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    {k : Nat} {Ξ : LCtx} {B : Expr Nat} {v : Level}
    (q : SortTyTransport E n Δ A u k Ξ B v) :
    (p.append q).length = p.length + q.length := by
  induction q with
  | refl => rfl
  | wk path d c hcl ih => simp only [append, length, ih, Nat.add_assoc]
  | esub path value t j hcl hinst hget hv ih =>
      simp only [append, length, ih, Nat.add_assoc]
  | lsub path t w0 j hcl hinst hget hv ih =>
      simp only [append, length, ih, Nat.add_assoc]
  | linst path n ls hls hlen hEL hIL ih =>
      simp only [append, length, ih, Nat.add_assoc]

@[simp] theorem run_refl (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (.refl : SortTyTransport E a Δ₀ A₀ u₀ a Δ₀ A₀ u₀).run hA₀ = hA₀ := rfl

@[simp] theorem run_wk {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    (d : LocalDecl) (c : Nat) (hcl : EnvClosed E)
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (path.wk d c hcl).run hA₀ = hasTyTWeaken d hcl (c := c) (path.run hA₀) := rfl

@[simp] theorem run_esub {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    (v t : Expr Nat) (j : Nat)
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hget : Δ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Δ) (lift 0 j v) (lift 0 j t))
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (path.esub v t j hcl hinst hget hv).run hA₀ =
      hasTyT_substS hcl hinst v t (j := j) (path.run hA₀) hget hv := rfl

@[simp] theorem run_lsub {n : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (path : SortTyTransport E a Δ₀ A₀ u₀ n Δ A u)
    (t w0 : Expr Nat) (j : Nat)
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hget : Δ[j]? = some (.letBinding t w0))
    (hv : HasTyT E n (substRemove w0 j Δ) (lift 0 j w0) (lift 0 j t))
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (path.lsub t w0 j hcl hinst hget hv).run hA₀ =
      hasTyT_substLetS hcl hinst t w0 (j := j) (path.run hA₀) hget hv := rfl

@[simp] theorem run_linst {m : Nat} {Δ : LCtx} {A : Expr Nat} {u : Level}
    (path : SortTyTransport E a Δ₀ A₀ u₀ m Δ A u)
    (n : Nat) (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = m)
    (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    (hA₀ : HasTyT E a Δ₀ A₀ (.sort u₀)) :
    (path.linst n ls hls hlen hEL hIL).run hA₀ =
      hasTyT_instLevels hEL hIL hls hlen (path.run hA₀) := rfl

end SortTyTransport

/-- The exact source-map composition used while reading a level transport. -/
theorem sortTransport_levelSub_linst {σ : Level → Level} (hσ : LevelSub σ)
    (ls : List Level) : LevelSub (fun l => σ (instLevel ls l)) :=
  hσ.linst ls

/-- The same source-map composition preserves the stronger syntactic map laws. -/
theorem sortTransport_levelHom_linst {σ : Level → Level} (hσ : LevelHom σ)
    (ls : List Level) : LevelHom (fun l => σ (instLevel ls l)) :=
  hσ.linst ls

/-- Moving a level homomorphism into the list requires the recorded bound. -/
theorem sortTransport_linst_map {σ : Level → Level} (hσ : LevelHom σ)
    (ls : List Level) (u : Level) (hu : levelBounded ls.length u = true) :
    instLevel (ls.map σ) u = σ (instLevel ls u) :=
  instLevel_map_of_levelHom hσ ls u hu

/-- The bounded mapped-list law, projected to the proof bit. -/
theorem sortTransport_linst_map_bit {σ : Level → Level} (hσ : LevelHom σ)
    (ls : List Level) (u : Level) (hu : levelBounded ls.length u = true) :
    levelIsZero (instLevel (ls.map σ) u) = levelIsZero (σ (instLevel ls u)) :=
  congrArg levelIsZero (sortTransport_linst_map hσ ls u hu)

end Rcic.Syn
