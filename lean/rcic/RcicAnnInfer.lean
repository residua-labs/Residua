import rcic.RcicAnnStep

/-!
# M1-b (ii) — type SYNTHESIS on the annotated copy

`inferA` reads 02 §8's rules bottom-up as a FUNCTION with NO conversion check
anywhere: where the tree's rule reads a binder sort off a derivation, the copy
reads it off the annotation (`pi A u B v ↦ sort (imax u v)`; the lam's domain
sort `u` is the subject's, its codomain sort is the inferred sort of the body's
type), and `app` exposes the pi of the head's type by `whnfA`. It SYNTHESISES;
it does not CHECK — the predicate that validates annotations against inferred
sorts, and the argument of an `app` against the pi's domain, is M1-c's
(`ConvAlgA` and the well-annotatedness predicate), and nothing here claims
soundness against `HasTy`.

Fuel, because the lam arm infers the sort of a TYPE it just computed (not a
subterm). `none` means "no answer under this fuel", never a wrong answer.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- `inferA fuel Γ e`: the type of `e`, read off the syntax and the environment
    twin, or `none`. -/
def inferA (E : ResolvedEnvA) (iota : IotaFnA) : Nat → LCtxA → ExprA → Option ExprA
  | 0, _, _ => none
  | fuel + 1, Γ, e =>
    match e with
    | .bvar i => lookupTypeA Γ i
    | .sort l => some (.sort (.succ l))
    | .const r ls =>
        match E.members r with
        | some m => if ls.length = m.arity then some (instantiateLevelsA ls m.mtypeA) else none
        | none => none
    | .pi _A u _B v => some (.sort (.imax u v))
    | .lam A u body =>
        match inferA E iota fuel (.assumption A :: Γ) body with
        | some B =>
            match inferA E iota fuel (.assumption A :: Γ) B with
            | some TB =>
                match whnfA E iota (.assumption A :: Γ) fuel TB with
                | some (.sort v) => some (.pi A u B v)
                | _ => none
            | none => none
        | none => none
    | .app f a =>
        match inferA E iota fuel Γ f with
        | some Tf =>
            match whnfA E iota Γ fuel Tf with
            | some (.pi _A _u B _v) => some (instantiate0A a B)
            | _ => none
        | none => none
    | .letE A value body =>
        match inferA E iota fuel (.letBinding A value :: Γ) body with
        | some B => some (instantiate0A value B)
        | none => none
    | .lit t => inferA E iota fuel Γ (natExpandA t)

/-- the sort a TYPE lives in: the whnf of its inferred type must be a `sort`. -/
def inferSortA (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (T : ExprA) : Option Level :=
  match inferA E iota fuel Γ T with
  | some TT =>
      match whnfA E iota Γ fuel TT with
      | some (.sort l) => some l
      | _ => none
  | none => none

/-! ## pins — the sort of a pi is a FUNCTION OF ITS SYNTAX

Two pis with the same erasure and different annotations get different sorts
(`pinPiA`/`pinPiAlt` erase alike, `erase_blind`); the tree's `HasTy.pi` would
have to be told `u` by a derivation. This is the datum the Prop clause of
`LR_A` will be keyed on. -/

example (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (A B : ExprA) (u v : Level) :
    inferA E iota (fuel + 1) Γ (.pi A u B v) = some (.sort (.imax u v)) := rfl

example (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA) (l : Level) :
    inferA E iota (fuel + 1) Γ (.sort l) = some (.sort (.succ l)) := rfl

example : inferSortA emptyEnvA (fun _ => none) 1 [] pinPiA
    = some (.imax (.succ .zero) (.succ .zero)) := by decide

example : inferSortA emptyEnvA (fun _ => none) 1 [] pinPiAlt
    = some (.imax .zero (.succ .zero)) := by decide

/-- the two sorts differ although the erasures agree. -/
example : inferSortA emptyEnvA (fun _ => none) 1 [] pinPiA
    ≠ inferSortA emptyEnvA (fun _ => none) 1 [] pinPiAlt := by decide

/-- a lam's type reads its domain sort off the subject and its codomain sort off
    the body's type: `λ (x : Sort 0). x` at `Π (x : Sort 0), Sort 0`, codomain sort 1. -/
example : inferA emptyEnvA (fun _ => none) 3 [] (.lam (.sort .zero) (.succ .zero) (.bvar 0))
    = some (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)) := by decide

/-- an application exposes the pi of its head's type: `(λ (x : Sort 0). x) (Sort 0 → Sort 0)`
    would need `Sort 0 → Sort 0 : Sort 0`, which synthesis does NOT check — it
    returns the codomain instantiated, as 02 §8's Application rule reads. -/
example : inferA emptyEnvA (fun _ => none) 3 []
    (.app (.lam (.sort .zero) (.succ .zero) (.bvar 0)) (.sort .zero))
    = some (.sort .zero) := by decide

/-- fuel 0 answers nothing. -/
example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (e : ExprA) :
    inferA E iota 0 Γ e = none := rfl

end Rcic.Declarative.Ann
