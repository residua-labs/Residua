import rcic.RcicAnnLR3EnvironmentEvalComposition

/-!
# Native recursor and constructor terms with exact forward computation

The native evaluator `denI` is an untyped approximation semantics with exact
lambda application (`FunctionEval.native_lambda_application`) and exact
application (`NeutralPi.applyValue_denI`). This file builds closed native
combinators from these laws only, and proves their raw computations as value
equalities:

* `lams n b` binds `n` arguments; `drops n b` consumes `n` arguments that the
  body never sees (each binder is followed by `lift 0 1`);
* `pairN`, `selN` and `nthN` give a selector indexed by a constructor
  *reference* (not by a position counted from a group), so a constructor term
  needs only its own reference and arity;
* `yN` is the untyped fixed-point combinator: `fix_unfold` is a single native
  beta computation in the approximation model, with no normalization premise;
* `ctorN c n` is the selector encoding of a constructor with `n` arguments, and
  `recN` / `genN` the fixed point of a recursor body over its minors, with
  parameters, motive and indices dropped.

`recN_apply` is the forward unfolding: applying the fixed point to any raw
parameter/motive/minor/index list and any major gives the recursor body at the
minors and the major, independently of the dropped arguments. No source
judgment, admission, Fundamental or decoder premise occurs here.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IotaRecursor

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

/-! ## Iterated application and environment extension -/

/-- Iterated raw application, first argument first. -/
def applyAll (f : Value) (xs : List Value) : Value :=
  xs.foldl NeutralPi.applyValue f

theorem applyAll_nil (f : Value) : applyAll f [] = f := rfl

theorem applyAll_cons (f x : Value) (xs : List Value) :
    applyAll f (x :: xs) = applyAll (NeutralPi.applyValue f x) xs := rfl

theorem applyAll_append (f : Value) (xs ys : List Value) :
    applyAll f (xs ++ ys) = applyAll (applyAll f xs) ys := by
  unfold applyAll
  exact List.foldl_append _ _ _ _

theorem applyAll_singleton (f x : Value) :
    applyAll f [x] = NeutralPi.applyValue f x := rfl

/-- Push values onto an environment; the last value becomes variable `0`. -/
def pushAll : List Value → EnvI → EnvI
  | [], ρ => ρ
  | x :: xs, ρ => pushAll xs (EnvI.cons x ρ)

theorem pushAll_append (xs ys : List Value) (ρ : EnvI) :
    pushAll (xs ++ ys) ρ = pushAll ys (pushAll xs ρ) := by
  induction xs generalizing ρ with
  | nil => rfl
  | cons x xs ih => exact ih (EnvI.cons x ρ)

theorem pushAll_singleton (x : Value) (ρ : EnvI) : pushAll [x] ρ = EnvI.cons x ρ := rfl

theorem pushAll_ge : ∀ (xs : List Value) (ρ : EnvI) (i : Nat), xs.length ≤ i →
    pushAll xs ρ i = ρ (i - xs.length)
  | [], ρ, i, _ => by simp [pushAll]
  | x :: xs, ρ, i, h => by
      have h' : xs.length ≤ i := by simp at h; omega
      show pushAll xs (EnvI.cons x ρ) i = ρ (i - (xs.length + 1))
      rw [pushAll_ge xs (EnvI.cons x ρ) i h']
      have hi : i - xs.length = (i - (xs.length + 1)) + 1 := by simp at h; omega
      rw [hi]
      rfl

theorem pushAll_lookup : ∀ (xs : List Value) (ρ : EnvI) (j : Nat) (hj : j < xs.length),
    pushAll xs ρ (xs.length - 1 - j) = xs[j]
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, ρ, 0, _ => by
      show pushAll xs (EnvI.cons x ρ) (xs.length + 1 - 1 - 0) = x
      rw [pushAll_ge xs (EnvI.cons x ρ) _ (by omega)]
      have : xs.length + 1 - 1 - 0 - xs.length = 0 := by omega
      rw [this]
      rfl
  | x :: xs, ρ, j + 1, hj => by
      have hj' : j < xs.length := by simp at hj; omega
      show pushAll xs (EnvI.cons x ρ) (xs.length + 1 - 1 - (j + 1)) = xs[j]
      have : xs.length + 1 - 1 - (j + 1) = xs.length - 1 - j := by omega
      rw [this]
      exact pushAll_lookup xs (EnvI.cons x ρ) j hj'

/-! ## Equational native laws -/

theorem denI_app (ρ : EnvI) (f a : Expr Nat) :
    denI ρ (.app f a) = NeutralPi.applyValue (denI ρ f) (denI ρ a) :=
  (NeutralCodes.valueEq_eq (NeutralPi.applyValue_denI ρ f a)).symm

theorem denI_lam_apply (ρ : EnvI) (A b : Expr Nat) (x : Value) :
    NeutralPi.applyValue (denI ρ (.lam A b)) x = denI (EnvI.cons x ρ) b :=
  NeutralCodes.valueEq_eq (FunctionEval.native_lambda_application ρ A b x)

theorem denI_bot (ρ : EnvI) (e : Expr Nat) : denI ρ e .bot := ApproxI.bot ρ e

theorem denI_bvar {ρ : EnvI} {i : Nat} (h : ρ i .bot) : denI ρ (.bvar i) = ρ i := by
  funext c
  apply propext
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with hc | hc
    · subst hc; exact h
    · exact hc
  · intro hc
    exact ApproxI.bvar hc

/-- A lifted term ignores the new outermost variable. -/
theorem denI_lift_cons (S : Value) (ρ : EnvI) (t : Expr Nat) :
    denI (EnvI.cons S ρ) (lift 0 1 t) = denI ρ t := by
  funext c
  apply propext
  constructor
  · intro h
    have h' : ApproxI (EnvI.insert ρ 0 S) (lift 0 1 t) c := by
      rw [EnvI.insert_zero]; exact h
    exact approxI_lift_elim t h'
  · intro h
    have h' := approxI_lift_intro h 0 S
    rw [EnvI.insert_zero] at h'
    exact h'

theorem applyAll_bot (f : Value) (hf : f .bot) : ∀ xs : List Value, applyAll f xs .bot
  | [] => hf
  | x :: xs => applyAll_bot (NeutralPi.applyValue f x) (Or.inl rfl) xs

/-! ## Binders, dropped binders, spines and variable lists -/

/-- The placeholder annotation and dummy argument. -/
def dummy : Expr Nat := .sort .zero

/-- `n` binders. -/
def lams : Nat → Expr Nat → Expr Nat
  | 0, b => b
  | n + 1, b => .lam dummy (lams n b)

/-- `n` binders whose variables the body never sees. -/
def drops : Nat → Expr Nat → Expr Nat
  | 0, b => b
  | n + 1, b => .lam dummy (lift 0 1 (drops n b))

theorem lams_apply : ∀ (n : Nat) (b : Expr Nat) (ρ : EnvI) (xs : List Value),
    xs.length = n → applyAll (denI ρ (lams n b)) xs = denI (pushAll xs ρ) b
  | 0, b, ρ, [], _ => rfl
  | n + 1, b, ρ, x :: xs, h => by
      rw [applyAll_cons]
      show applyAll (NeutralPi.applyValue (denI ρ (.lam dummy (lams n b))) x) xs = _
      rw [denI_lam_apply]
      exact lams_apply n b (EnvI.cons x ρ) xs (Nat.succ.inj h)
  | 0, _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, _, _, [], h => absurd h (Nat.succ_ne_zero _).symm

theorem drops_apply : ∀ (n : Nat) (b : Expr Nat) (ρ : EnvI) (xs : List Value),
    xs.length = n → applyAll (denI ρ (drops n b)) xs = denI ρ b
  | 0, b, ρ, [], _ => rfl
  | n + 1, b, ρ, x :: xs, h => by
      rw [applyAll_cons]
      show applyAll (NeutralPi.applyValue (denI ρ (.lam dummy (lift 0 1 (drops n b)))) x) xs = _
      rw [denI_lam_apply, denI_lift_cons]
      exact drops_apply n b ρ xs (Nat.succ.inj h)
  | 0, _, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, _, _, [], h => absurd h (Nat.succ_ne_zero _).symm

theorem foldApps_denI (ρ : EnvI) : ∀ (f : Expr Nat) (args : List (Expr Nat)),
    denI ρ (foldApps f args) = applyAll (denI ρ f) (args.map (denI ρ))
  | f, [] => rfl
  | f, a :: args => by
      show denI ρ (foldApps (.app f a) args) = _
      rw [foldApps_denI ρ (.app f a) args, denI_app]
      rfl

/-- `argVars base n = [bvar (base + n - 1), …, bvar base]`: the `n` variables
bound immediately below `base` further binders, outermost first. -/
def argVars (base : Nat) : Nat → List (Expr Nat)
  | 0 => []
  | n + 1 => .bvar (base + n) :: argVars base n

theorem argVars_length (base : Nat) : ∀ n, (argVars base n).length = n
  | 0 => rfl
  | n + 1 => by simp [argVars, argVars_length base n]

/-- The variables of a pushed list read back exactly that list, below any
further pushed binders, when every value observes bottom. -/
theorem argVars_denI : ∀ (xs : List Value) (ρ : EnvI) (ys : List Value),
    (∀ x ∈ xs, x .bot) →
    (argVars ys.length xs.length).map (denI (pushAll ys (pushAll xs ρ))) = xs
  | [], _, _, _ => rfl
  | x :: xs, ρ, ys, hb => by
      show denI (pushAll ys (pushAll xs (EnvI.cons x ρ))) (.bvar (ys.length + xs.length)) ::
          (argVars ys.length xs.length).map (denI (pushAll ys (pushAll xs (EnvI.cons x ρ)))) =
        x :: xs
      have hx : pushAll ys (pushAll xs (EnvI.cons x ρ)) (ys.length + xs.length) = x := by
        rw [pushAll_ge ys _ _ (by omega)]
        rw [show ys.length + xs.length - ys.length = xs.length by omega]
        rw [pushAll_ge xs _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      have hbx : pushAll ys (pushAll xs (EnvI.cons x ρ)) (ys.length + xs.length) .bot := by
        rw [hx]; exact hb x (by simp)
      rw [denI_bvar hbx, hx,
        argVars_denI xs (EnvI.cons x ρ) ys (fun y hy => hb y (List.mem_cons_of_mem x hy))]

theorem bvar_lookup_denI (xs : List Value) (ρ : EnvI) (ys : List Value) (j : Nat)
    (hj : j < xs.length) (hb : xs[j] .bot) :
    denI (pushAll ys (pushAll xs ρ)) (.bvar (ys.length + (xs.length - 1 - j))) = xs[j] := by
  have hx : pushAll ys (pushAll xs ρ) (ys.length + (xs.length - 1 - j)) = xs[j] := by
    rw [pushAll_ge ys _ _ (by omega)]
    rw [show ys.length + (xs.length - 1 - j) - ys.length = xs.length - 1 - j by omega]
    exact pushAll_lookup xs ρ j hj
  have hbx : pushAll ys (pushAll xs ρ) (ys.length + (xs.length - 1 - j)) .bot := by
    rw [hx]; exact hb
  rw [denI_bvar hbx, hx]

/-! ## Pairs and the reference-indexed selector -/

def kFstN : Expr Nat := .lam dummy (.lam dummy (.bvar 1))
def kSndN : Expr Nat := .lam dummy (.lam dummy (.bvar 0))
def fstN : Expr Nat := .lam dummy (.app (.bvar 0) kFstN)
def sndN : Expr Nat := .lam dummy (.app (.bvar 0) kSndN)

def pairN (a b : Expr Nat) : Expr Nat :=
  .lam dummy (.app (.app (.bvar 0) (lift 0 1 a)) (lift 0 1 b))

theorem pairN_apply (σ : EnvI) (a b : Expr Nat) (K : Value) (hK : K .bot) :
    NeutralPi.applyValue (denI σ (pairN a b)) K =
      NeutralPi.applyValue (NeutralPi.applyValue K (denI σ a)) (denI σ b) := by
  unfold pairN
  rw [denI_lam_apply, denI_app, denI_app, denI_bvar (ρ := EnvI.cons K σ) (i := 0) hK,
    denI_lift_cons, denI_lift_cons]
  rfl

theorem fstN_pair (τ σ : EnvI) (a b : Expr Nat) :
    NeutralPi.applyValue (denI τ fstN) (denI σ (pairN a b)) = denI σ a := by
  unfold fstN
  rw [denI_lam_apply, denI_app, denI_bvar (ρ := EnvI.cons (denI σ (pairN a b)) τ) (i := 0)
    (denI_bot σ _)]
  show NeutralPi.applyValue (denI σ (pairN a b)) (denI _ kFstN) = _
  rw [pairN_apply σ a b _ (denI_bot _ _)]
  unfold kFstN
  rw [denI_lam_apply, denI_lam_apply]
  exact denI_bvar (ρ := EnvI.cons (denI σ b) (EnvI.cons (denI σ a) _)) (i := 1) (denI_bot σ a)

theorem sndN_pair (τ σ : EnvI) (a b : Expr Nat) :
    NeutralPi.applyValue (denI τ sndN) (denI σ (pairN a b)) = denI σ b := by
  unfold sndN
  rw [denI_lam_apply, denI_app, denI_bvar (ρ := EnvI.cons (denI σ (pairN a b)) τ) (i := 0)
    (denI_bot σ _)]
  show NeutralPi.applyValue (denI σ (pairN a b)) (denI _ kSndN) = _
  rw [pairN_apply σ a b _ (denI_bot _ _)]
  unfold kSndN
  rw [denI_lam_apply, denI_lam_apply]
  exact denI_bvar (ρ := EnvI.cons (denI σ b) (EnvI.cons (denI σ a) _)) (i := 0) (denI_bot σ b)

/-- A finite selector: component `c` is the `c`-th list entry. -/
def selN : List (Expr Nat) → Expr Nat
  | [] => dummy
  | a :: as => pairN a (selN as)

/-- Extraction of component `c`, from the constructor side. -/
def nthN : Nat → Expr Nat → Expr Nat
  | 0, t => .app fstN t
  | c + 1, t => nthN c (.app sndN t)

theorem nthN_sel : ∀ (c : Nat) (t : Expr Nat) (τ σ : EnvI) (comps : List (Expr Nat))
    (hc : c < comps.length), denI τ t = denI σ (selN comps) →
    denI τ (nthN c t) = denI σ (comps[c])
  | _, _, _, _, [], hc, _ => absurd hc (Nat.not_lt_zero _)
  | 0, t, τ, σ, a :: as, _, ht => by
      show denI τ (.app fstN t) = denI σ a
      rw [denI_app, ht]
      exact fstN_pair τ σ a (selN as)
  | c + 1, t, τ, σ, a :: as, hc, ht => by
      show denI τ (nthN c (.app sndN t)) = denI σ (as[c]'(by simp at hc; omega))
      apply nthN_sel c (.app sndN t) τ σ as (by simp at hc; omega)
      rw [denI_app, ht]
      exact sndN_pair τ σ a (selN as)

/-! ## The untyped fixed point -/

def wN : Expr Nat := .lam dummy (.app (.bvar 1) (.app (.bvar 0) (.bvar 0)))
def yN : Expr Nat := .lam dummy (.app wN wN)

/-- The fixed point of a native generator at an environment. -/
def fixValue (G : Expr Nat) (ρ : EnvI) : Value := denI (EnvI.cons (denI ρ G) ρ) (.app wN wN)

theorem fix_denI (G : Expr Nat) (ρ : EnvI) : denI ρ (.app yN G) = fixValue G ρ := by
  rw [denI_app]
  unfold yN
  rw [denI_lam_apply]
  rfl

/-- One native beta step: the fixed point is a fixed point. -/
theorem fix_unfold (G : Expr Nat) (ρ : EnvI) :
    fixValue G ρ = NeutralPi.applyValue (denI ρ G) (fixValue G ρ) := by
  unfold fixValue
  have hW : denI (EnvI.cons (denI ρ G) ρ) (.app wN wN) =
      denI (EnvI.cons (denI (EnvI.cons (denI ρ G) ρ) wN) (EnvI.cons (denI ρ G) ρ))
        (.app (.bvar 1) (.app (.bvar 0) (.bvar 0))) := by
    rw [denI_app]
    exact denI_lam_apply _ dummy _ _
  calc denI (EnvI.cons (denI ρ G) ρ) (.app wN wN)
      = denI (EnvI.cons (denI (EnvI.cons (denI ρ G) ρ) wN) (EnvI.cons (denI ρ G) ρ))
          (.app (.bvar 1) (.app (.bvar 0) (.bvar 0))) := hW
    _ = NeutralPi.applyValue (denI ρ G)
          (NeutralPi.applyValue (denI (EnvI.cons (denI ρ G) ρ) wN)
            (denI (EnvI.cons (denI ρ G) ρ) wN)) := by
        rw [denI_app, denI_app]
        rw [denI_bvar (ρ := EnvI.cons (denI (EnvI.cons (denI ρ G) ρ) wN)
            (EnvI.cons (denI ρ G) ρ)) (i := 1) (denI_bot ρ G)]
        rw [denI_bvar (ρ := EnvI.cons (denI (EnvI.cons (denI ρ G) ρ) wN)
            (EnvI.cons (denI ρ G) ρ)) (i := 0) (denI_bot _ wN)]
        rfl
    _ = NeutralPi.applyValue (denI ρ G) (denI (EnvI.cons (denI ρ G) ρ) (.app wN wN)) := by
        rw [← denI_app]

/-! ## Constructor and recursor terms -/

/-- The selector encoding of constructor reference `c` with `n` arguments: after its
arguments it waits for a selector and applies the selector's component `c` to all
of them. -/
def ctorN (c n : Nat) : Expr Nat :=
  lams n (.lam dummy (foldApps (nthN c (.bvar 0)) (argVars 1 n)))

theorem ctorN_apply (c : Nat) (ρ : EnvI) (args : List Value) (hb : ∀ x ∈ args, x .bot)
    (σ : EnvI) (comps : List (Expr Nat)) (hc : c < comps.length) :
    NeutralPi.applyValue (applyAll (denI ρ (ctorN c args.length)) args) (denI σ (selN comps)) =
      applyAll (denI σ (comps[c])) args := by
  unfold ctorN
  rw [lams_apply _ _ ρ args rfl, denI_lam_apply, foldApps_denI]
  have hargs := argVars_denI args ρ [denI σ (selN comps)] hb
  simp only [pushAll_singleton, List.length_singleton] at hargs
  rw [hargs, nthN_sel c (.bvar 0) _ σ comps hc
    (denI_bvar (ρ := EnvI.cons (denI σ (selN comps)) (pushAll args ρ)) (i := 0)
      (denI_bot σ _))]

/-- The generator of a recursor fixed point: `self`, then `np + 1` dropped
parameters and motive, `nm` minors, `ni` dropped indices and the major; the body
applies the major to the selector of the component terms. -/
def genN (np nm ni : Nat) (comps : List (Expr Nat)) : Expr Nat :=
  .lam dummy (drops (np + 1) (lams nm (drops ni
    (.lam dummy (.app (.bvar 0) (selN comps))))))

/-- The recursor body's environment: major, then minors, then the fixed point. -/
def bodyEnv (Θ : Value) (ρ : EnvI) (ms : List Value) (maj : Value) : EnvI :=
  EnvI.cons maj (pushAll ms (EnvI.cons Θ ρ))

/-- The recursor body at minors and major. -/
def bodyValue (np nm ni : Nat) (comps : List (Expr Nat)) (ρ : EnvI)
    (ms : List Value) (maj : Value) : Value :=
  NeutralPi.applyValue maj
    (denI (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ ms maj) (selN comps))

/-- Forward unfolding at an explicit split of the arguments. -/
theorem recN_apply_split (np nm ni : Nat) (comps : List (Expr Nat)) (ρ : EnvI)
    (ps ms is : List Value) (hps : ps.length = np + 1) (hms : ms.length = nm)
    (his : is.length = ni) (maj : Value) (hmaj : maj .bot) :
    applyAll (fixValue (genN np nm ni comps) ρ) (ps ++ ms ++ is ++ [maj]) =
      bodyValue np nm ni comps ρ ms maj := by
  conv => lhs; rw [fix_unfold]
  rw [applyAll_append, applyAll_append, applyAll_append]
  unfold genN
  rw [denI_lam_apply, drops_apply (np + 1) _ _ _ hps, lams_apply nm _ _ _ hms,
    drops_apply ni _ _ _ his, applyAll_singleton, denI_lam_apply, denI_app,
    denI_bvar (ρ := EnvI.cons maj _) (i := 0) hmaj]
  rfl

/-- Forward unfolding of the recursor fixed point on any raw argument list of the
recursor's telescope arity: parameters, motive and indices are dropped. -/
theorem recN_apply (np nm ni : Nat) (comps : List (Expr Nat)) (ρ : EnvI)
    (xs : List Value) (hxs : xs.length = np + 1 + nm + ni) (maj : Value) (hmaj : maj .bot) :
    applyAll (fixValue (genN np nm ni comps) ρ) (xs ++ [maj]) =
      bodyValue np nm ni comps ρ ((xs.drop (np + 1)).take nm) maj := by
  have hsplit : xs = xs.take (np + 1) ++ (xs.drop (np + 1)).take nm ++
      (xs.drop (np + 1)).drop nm := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have h1 : (xs.take (np + 1)).length = np + 1 := by simp; omega
  have h2 : ((xs.drop (np + 1)).take nm).length = nm := by simp; omega
  have h3 : ((xs.drop (np + 1)).drop nm).length = ni := by simp; omega
  have h := recN_apply_split np nm ni comps ρ _ _ _ h1 h2 h3 maj hmaj
  rw [← hsplit] at h
  exact h

end Rcic.Declarative.Ann.LR3.IotaRecursor
