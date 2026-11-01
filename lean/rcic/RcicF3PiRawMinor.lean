import rcic.RcicF3PiRawIH
/-! Application semantics for the actual executable minor builder at any
recursive Pi depth. Inputs record individual field and IH memberships; they
contain no result-typing or minor-typing premise. Constructing these inputs
for every admitted raw group remains open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawMinor
open Rcic.Declarative
universe u

/-- The actual dependent argument spine, including every inserted IH binder.
The endpoint is calculated at the terminal constructor/motive application. -/
inductive Inputs (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat) :
    Expr Nat → Expr Nat → List FieldShape → Expr Nat → (Nat → PSet.{u}) →
      List PSet.{u} → List PSet.{u} → PSet.{u} → Prop where
  | done (Mx acc T : Expr Nat) (ρ : Nat → PSet.{u}) :
      Inputs M σ E fuel np Mx acc [] T ρ [] []
        (den M σ ρ (.app (foldApps Mx (familyIdx np T)) acc))
  | plain {Mx acc A B : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
      {xs ys : List PSet.{u}} {out : PSet.{u}} (x : PSet.{u})
      (hx : x ∈ Ed M (den M σ ρ A))
      (tail : Inputs M σ E fuel np (Rcic.Declarative.lift 0 1 Mx)
        (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss B (vcons x ρ) xs ys out) :
      Inputs M σ E fuel np Mx acc (.nonrecursive :: ss) (.pi A B) ρ
        (x :: xs) (x :: ys) out
  | recursive {Mx acc A B : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
      {xs ys : List PSet.{u}} {out : PSet.{u}} (inner : Nat) (ihT : Expr Nat)
      (hread : funIHType E fuel np A Mx inner = some ihT) (x ih : PSet.{u})
      (hx : x ∈ Ed M (den M σ ρ A))
      (hih : ih ∈ Ed M (den M σ (vcons x ρ) ihT))
      (tail : Inputs M σ E fuel np (Rcic.Declarative.lift 0 2 Mx)
        (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
        (Rcic.Declarative.lift 0 1 B) (vcons ih (vcons x ρ)) xs ys out) :
      Inputs M σ E fuel np Mx acc (.recursive inner :: ss) (.pi A B) ρ
        (x :: xs) (x :: ih :: ys) out

/-- A typed executable minor consumes exactly the field/IH spine. No opaque
family-head, depth-one or global recursive-map condition is used. -/
theorem apply (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat)
    {Mx acc T R : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
    {xs ys : List PSet.{u}} {out F : PSet.{u}}
    (h : Inputs M σ E fuel np Mx acc ss T ρ xs ys out)
    (hR : minorFromTelescope E fuel np Mx acc ss T = some R)
    (hF : F ∈ Ed M (den M σ ρ R)) : fapps F ys ∈ Ed M out := by
  induction h generalizing R F with
  | done Mx acc T ρ =>
      have he : .app (foldApps Mx (familyIdx np T)) acc = R := Option.some.inj hR
      exact he ▸ hF
  | @plain Mx acc A B ss ρ xs ys out x hx tail ih =>
      have he : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 1 Mx)
          (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss B).map
          (fun rest => .pi A rest) = some R := hR
      obtain ⟨R', hR', rfl⟩ := Option.map_eq_some'.mp he
      have ht := app_mem M (fun y y' hy => den_congr M σ R'
        (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
      exact ih hR' ht
  | @recursive Mx acc A B ss ρ xs ys out inner ihT hr x i hx hi tail ih =>
      have he : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
          (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
          (Rcic.Declarative.lift 0 1 B)).map
          (fun rest => .pi A (.pi ihT rest)) = some R := by
        simpa only [minorFromTelescope, hr] using hR
      obtain ⟨R', hR', rfl⟩ := Option.map_eq_some'.mp he
      have h1 := app_mem M (fun y y' hy => den_congr M σ (.pi ihT R')
        (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hF hx
      have h2 := app_mem M (fun y y' hy => den_congr M σ R'
        (vcons_congr (ρ := vcons x ρ) (ρ' := vcons x ρ) hy (fun _ => Equiv.rfl))) h1 hi
      exact ih hR' h2
/-- Inserted IH binders preserve the actual constructor field spine and
its dependent result indices. The endpoint contains the original motive. -/
theorem endpoint (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat)
    {Mx acc T : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
    {xs ys : List PSet.{u}} {out : PSet.{u}}
    (h : Inputs M σ E fuel np Mx acc ss T ρ xs ys out)
    (Fs : List (Expr Nat)) (Tend : Expr Nat) (hT : T = policyPi Fs Tend)
    (hl : Fs.length = xs.length) :
    out = fapp (fapps (den M σ ρ Mx)
      ((familyIdx np Tend).map (den M σ (push xs ρ))))
      (fapps (den M σ ρ acc) xs) := by
  induction h generalizing Fs Tend with
  | done Mx acc T ρ =>
      have hf : Fs = [] := List.length_eq_zero.mp hl
      subst Fs
      subst T
      change fapp (den M σ ρ (foldApps Mx (familyIdx np Tend))) (den M σ ρ acc) = _
      rw [den_foldApps]
      rfl
  | @plain Mx acc A B ss ρ xs ys out x hx tail ih =>
      cases Fs with
      | nil => exact False.elim (Nat.noConfusion hl.symm)
      | cons A' Fs =>
          have ht : A = A' ∧ B = policyPi Fs Tend := Expr.pi.inj hT
          have he := ih Fs Tend ht.2 (Nat.succ.inj hl)
          rw [he]
          have hm0 : den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 Mx) =
              den M σ ρ Mx := den_lift0_push M σ [x] ρ Mx
          rw [hm0]
          change fapp (fapps (den M σ ρ Mx) _) (fapps
            (fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc)) x) xs) = _
          have ha0 : den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc) =
              den M σ ρ acc := den_lift0_push M σ [x] ρ acc
          rw [ha0]
          rfl
  | @recursive Mx acc A B ss ρ xs ys out inner ihT hr x i hx hi tail ih =>
      cases Fs with
      | nil => exact False.elim (Nat.noConfusion hl.symm)
      | cons A' Fs =>
          have ht : A = A' ∧ B = policyPi Fs Tend := Expr.pi.inj hT
          have ht' : Rcic.Declarative.lift 0 1 B = policyPi (liftFields 1 Fs 0)
              (Rcic.Declarative.lift Fs.length 1 Tend) := by
            rw [ht.2, lift_policyPi, Nat.zero_add]
          have he := ih (liftFields 1 Fs 0) (Rcic.Declarative.lift Fs.length 1 Tend)
            ht' (by rw [liftFields_length']; exact Nat.succ.inj hl)
          rw [he, familyIdx_lift, List.map_map]
          have hm : (den M σ (push xs (vcons i (vcons x ρ))) ∘
              Rcic.Declarative.lift Fs.length 1) = den M σ (push xs (vcons x ρ)) := by
            funext e
            rw [Nat.succ.inj hl]
            exact den_lift_push M σ xs [i] (vcons x ρ) e
          have hm0 : den M σ (vcons i (vcons x ρ)) (Rcic.Declarative.lift 0 2 Mx) =
              den M σ ρ Mx := den_lift0_push M σ [x, i] ρ Mx
          rw [hm, hm0]
          change fapp (fapps (den M σ ρ Mx) _) (fapps
            (fapp (den M σ (vcons i (vcons x ρ)) (Rcic.Declarative.lift 0 2 acc)) x) xs) = _
          have ha0 : den M σ (vcons i (vcons x ρ)) (Rcic.Declarative.lift 0 2 acc) =
              den M σ ρ acc := den_lift0_push M σ [x, i] ρ acc
          rw [ha0]
          rfl

/-- Elementary composition: actual executable minors produce the original
motive at the original constructor spine and dependent result indices. -/
theorem apply_endpoint (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv) (fuel np : Nat)
    {Mx acc T R : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
    {xs ys : List PSet.{u}} {out F : PSet.{u}}
    (h : Inputs M σ E fuel np Mx acc ss T ρ xs ys out)
    (hR : minorFromTelescope E fuel np Mx acc ss T = some R)
    (hF : F ∈ Ed M (den M σ ρ R))
    (Fs : List (Expr Nat)) (Tend : Expr Nat) (hT : T = policyPi Fs Tend)
    (hl : Fs.length = xs.length) :
    fapps F ys ∈ Ed M (fapp (fapps (den M σ ρ Mx)
      ((familyIdx np Tend).map (den M σ (push xs ρ))))
      (fapps (den M σ ρ acc) xs)) := by
  rw [← endpoint M σ E fuel np h Fs Tend hT hl]
  exact apply M σ E fuel np h hR hF

end Rcic.F3.PSet.PiRawMinor
