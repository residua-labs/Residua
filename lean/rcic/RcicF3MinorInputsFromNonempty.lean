import rcic.RcicF3IndexedPropSpine
import rcic.RcicF3PiRawMinor

/-!
# Actual field/IH input recovery from an executable minor

The packed argument relation records only the placement of ordinary fields
and inserted IHs. From the executable stored minor equation, its membership,
and a nonempty complete application, the input producer proves each original
field and IH membership at its actual dependent domain. Original field
TelFits is then recovered by removing exactly the inserted IH binders.

No environment soundness, source-context well-formedness, field erasure,
index agreement, or evaluation-existence premise is used.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.MinorInputsFromNonempty
open Rcic.Declarative
universe u

/-- Only the placement of each field and IH, with no semantic hypothesis. -/
inductive Packed : List FieldShape → List PSet.{u} → List PSet.{u} → Prop
  | nil : Packed [] [] []
  | plain {ss : List FieldShape} {xs ys : List PSet.{u}}
      (x : PSet.{u}) (tail : Packed ss xs ys) :
      Packed (.nonrecursive :: ss) (x :: xs) (x :: ys)
  | recursive {ss : List FieldShape} {xs ys : List PSet.{u}}
      (inner : Nat) (x ih : PSet.{u}) (tail : Packed ss xs ys) :
      Packed (.recursive inner :: ss) (x :: xs) (x :: ih :: ys)

theorem Packed.fields_length {ss : List FieldShape} {xs ys : List PSet.{u}}
    (h : Packed ss xs ys) : xs.length = ss.length := by
  induction h with
  | nil => rfl
  | plain _ _ ih => exact congrArg Nat.succ ih
  | recursive _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Every actual field and inserted IH fits its stored domain. The proof
works at arbitrary recursive Pi depth because the depth affects only the
already executable IH type, whose two application domains are recovered. -/
theorem inputs (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv)
    (fuel np : Nat)
    {ss : List FieldShape} {xs ys : List PSet.{u}} (hp : Packed ss xs ys)
    {Mx acc T R : Expr Nat} {ρ : Nat → PSet.{u}} {F : PSet.{u}}
    (hR : minorFromTelescope E fuel np Mx acc ss T = some R)
    (hF : F ∈ Ed M (den M σ ρ R))
    (hne : ¬ Equiv (fapps F ys) pempty) :
    ∃ out, PiRawMinor.Inputs M σ E fuel np Mx acc ss T ρ xs ys out := by
  induction hp generalizing Mx acc T R ρ F with
  | nil =>
      exact ⟨_, .done Mx acc T ρ⟩
  | @plain ss xs ys x hp ih =>
      cases T with
      | pi A B =>
          have he : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 1 Mx)
              (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss B).map
              (fun rest => .pi A rest) = some R := hR
          obtain ⟨R', hR', rfl⟩ := Option.map_eq_some'.mp he
          have hB := den_resp M σ ρ R'
          have hx : x ∈ Ed M (den M σ ρ A) :=
            mem_dom_of_fapp_ne M hB hF
              (fun he => hne (fapps_of_pempty he ys))
          have hTail : fapp F x ∈ Ed M (den M σ (vcons x ρ) R') :=
            app_mem M hB hF hx
          obtain ⟨out, hout⟩ := ih hR' hTail hne
          exact ⟨out, .plain x hx hout⟩
      | bvar => cases hR
      | sort => cases hR
      | const => cases hR
      | app => cases hR
      | lam => cases hR
      | letE => cases hR
      | lit => cases hR
  | @recursive ss xs ys inner x i hp ih =>
      cases T with
      | pi A B =>
          cases hread : funIHType E fuel np A Mx inner with
          | none =>
              simp only [minorFromTelescope, hread] at hR
              cases hR
          | some ihT =>
              have he : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
                  (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
                  (Rcic.Declarative.lift 0 1 B)).map
                  (fun rest => .pi A (.pi ihT rest)) = some R := by
                simpa only [minorFromTelescope, hread] using hR
              obtain ⟨R', hR', rfl⟩ := Option.map_eq_some'.mp he
              have hx : x ∈ Ed M (den M σ ρ A) :=
                mem_dom_of_fapp_ne M (den_resp M σ ρ (.pi ihT R')) hF
                  (fun he => hne (fapps_of_pempty he (i :: ys)))
              have hFx : fapp F x ∈ Ed M
                  (den M σ (vcons x ρ) (.pi ihT R')) :=
                app_mem M (den_resp M σ ρ (.pi ihT R')) hF hx
              have hi : i ∈ Ed M (den M σ (vcons x ρ) ihT) :=
                mem_dom_of_fapp_ne M (den_resp M σ (vcons x ρ) R') hFx
                  (fun he => hne (fapps_of_pempty he ys))
              have hTail : fapp (fapp F x) i ∈ Ed M
                  (den M σ (vcons i (vcons x ρ)) R') :=
                app_mem M (den_resp M σ (vcons x ρ) R') hFx hi
              obtain ⟨out, hout⟩ := ih hR' hTail hne
              exact ⟨out, .recursive inner ihT hread x i hx hi hout⟩
      | bvar => cases hR
      | sort => cases hR
      | const => cases hR
      | app => cases hR
      | lam => cases hR
      | letE => cases hR
      | lit => cases hR

/-- Remove precisely the IH binder introduced at every recursive field;
the literal original dependent field telescope is recovered. -/
theorem fields_fit (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv)
    (fuel np : Nat)
    {Mx acc T : Expr Nat} {ss : List FieldShape} {ρ : Nat → PSet.{u}}
    {xs ys : List PSet.{u}} {out : PSet.{u}}
    (h : PiRawMinor.Inputs M σ E fuel np Mx acc ss T ρ xs ys out)
    (Fs : List (Expr Nat)) (Tend : Expr Nat) (hT : T = policyPi Fs Tend)
    (hl : Fs.length = xs.length) : TelFits M σ Fs ρ xs := by
  induction h generalizing Fs Tend with
  | done Mx acc T ρ =>
      have hf : Fs = [] := List.eq_nil_of_length_eq_zero hl
      subst Fs
      trivial
  | @plain Mx acc A B ss ρ xs ys out x hx tail ih =>
      cases Fs with
      | nil => exact False.elim (Nat.noConfusion hl.symm)
      | cons A' Fs =>
          have ht : A = A' ∧ B = policyPi Fs Tend := Expr.pi.inj hT
          exact ⟨ht.1 ▸ hx, ih Fs Tend ht.2 (Nat.succ.inj hl)⟩
  | @recursive Mx acc A B ss ρ xs ys out inner ihT hr x i hx hi tail ih =>
      cases Fs with
      | nil => exact False.elim (Nat.noConfusion hl.symm)
      | cons A' Fs =>
          have ht : A = A' ∧ B = policyPi Fs Tend := Expr.pi.inj hT
          have ht' : Rcic.Declarative.lift 0 1 B = policyPi (liftFields 1 Fs 0)
              (Rcic.Declarative.lift Fs.length 1 Tend) := by
            rw [ht.2, lift_policyPi, Nat.zero_add]
          have htail := ih (liftFields 1 Fs 0)
            (Rcic.Declarative.lift Fs.length 1 Tend) ht'
            (by rw [liftFields_length']; exact Nat.succ.inj hl)
          exact ⟨ht.1 ▸ hx,
            (TelFits_liftFields M σ [i] (vcons x ρ) Fs [] xs).mp htail⟩

/-- The complete reconstruction composed, with packing supplied by the
actual raw RHS argument computation in the legacy specialization below. -/
theorem original_fields (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv)
    (fuel np : Nat)
    {ss : List FieldShape} {xs ys : List PSet.{u}} (hp : Packed ss xs ys)
    {Mx acc T R : Expr Nat} {ρ : Nat → PSet.{u}} {F : PSet.{u}}
    (hR : minorFromTelescope E fuel np Mx acc ss T = some R)
    (hF : F ∈ Ed M (den M σ ρ R))
    (hne : ¬ Equiv (fapps F ys) pempty)
    (Fs : List (Expr Nat)) (Tend : Expr Nat) (hT : T = policyPi Fs Tend)
    (hl : Fs.length = ss.length) : TelFits M σ Fs ρ xs := by
  obtain ⟨out, hout⟩ := inputs M σ E fuel np hp hR hF hne
  exact fields_fit M σ E fuel np hout Fs Tend hT
    (hl.trans hp.fields_length.symm)

/-- The exact shape mask of legacy rhsArgs; no field type is classified here. -/
def legacyShapes : List RecKind → List FieldShape
  | [] => []
  | .plain :: ks => .nonrecursive :: legacyShapes ks
  | .directRec :: ks => .recursive 0 :: legacyShapes ks

private theorem piTel_instantiate : (k j : Nat) → (s T : Expr Nat) →
    isPiTel k T = true → isPiTel k (instantiate j s T) = true
  | 0, _, _, _, _ => rfl
  | k + 1, j, s, .pi _ B, h =>
      piTel_instantiate k (j + 1) (Rcic.Declarative.lift 0 1 s) B h
  | _ + 1, _, _, .bvar _, h => by cases h
  | _ + 1, _, _, .sort _, h => by cases h
  | _ + 1, _, _, .const _ _, h => by cases h
  | _ + 1, _, _, .app _ _, h => by cases h
  | _ + 1, _, _, .lam _ _, h => by cases h
  | _ + 1, _, _, .letE _ _ _, h => by cases h
  | _ + 1, _, _, .lit _, h => by cases h

/-- Packing is produced by the actual rhsArgs computation, not assumed
as an arbitrary correspondence between field values and application values. -/
theorem packed_rhsArgs (M : Interp.{u}) (σ : Nat → Nat) (ρ : Nat → PSet.{u})
    (rec : Expr Nat) (pre : List (Expr Nat)) (np nm : Nat) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (T : Expr Nat) →
    ks.length = fs.length → isPiTel ks.length T = true →
      Packed (legacyShapes ks) (fs.map (den M σ ρ))
        ((rhsArgs rec pre np nm fs ks T).map (den M σ ρ))
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, hl, _ => False.elim (Nat.noConfusion hl)
  | _ :: _, [], _, hl, _ => False.elim (Nat.noConfusion hl)
  | f :: fs, k :: ks, .pi A B, hl, ht => by
      have htail := packed_rhsArgs M σ ρ rec pre np nm fs ks (instantiate0 f B)
        (Nat.succ.inj hl) (piTel_instantiate ks.length 0 f B ht)
      cases k with
      | plain => exact .plain _ htail
      | directRec => exact .recursive 0 _ _ htail
  | _ :: _, _ :: _, .bvar _, _, ht => by cases ht
  | _ :: _, _ :: _, .sort _, _, ht => by cases ht
  | _ :: _, _ :: _, .const _ _, _, ht => by cases ht
  | _ :: _, _ :: _, .app _ _, _, ht => by cases ht
  | _ :: _, _ :: _, .lam _ _, _, ht => by cases ht
  | _ :: _, _ :: _, .letE _ _ _, _, ht => by cases ht
  | _ :: _, _ :: _, .lit _, _, ht => by cases ht

theorem witness_packed (M : Interp.{u}) (σ : Nat → Nat) (ρ : Nat → PSet.{u})
    {S : ResolvedEnv} (w : IotaWitness S) :
    Packed (legacyShapes w.kinds) (w.fields.map (den M σ ρ))
      ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.kinds w.ctorAfterParams).map (den M σ ρ)) :=
  packed_rhsArgs M σ ρ (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
    w.fields w.kinds w.ctorAfterParams w.hlen w.hctorTel

/-- The actual legacy RHS recovers the original field tuple whenever the
stored executable minor uses its literal field/IH mask. Alignment of this
mask with a chosen admitted plan is a separate syntactic source obligation. -/
theorem original_fields_of_witness (M : Interp.{u}) (τ σ : Nat → Nat)
    (E : ResolvedEnv) (fuel np : Nat) {S : ResolvedEnv} (w : IotaWitness S)
    (ρsrc ρminor : Nat → PSet.{u}) {Mx acc T R : Expr Nat}
    (hR : minorFromTelescope E fuel np Mx acc (legacyShapes w.kinds) T = some R)
    (hminor : den M σ ρsrc w.minor ∈ Ed M (den M τ ρminor R))
    (hne : ¬ Equiv (den M σ ρsrc (iotaRhsOf w)) pempty)
    (Fs : List (Expr Nat)) (Tend : Expr Nat) (hT : T = policyPi Fs Tend)
    (hl : Fs.length = (legacyShapes w.kinds).length) :
    TelFits M τ Fs ρminor (w.fields.map (den M σ ρsrc)) := by
  apply original_fields M τ E fuel np (witness_packed M σ ρsrc w)
    hR hminor ?_ Fs Tend hT hl
  simpa only [iotaRhsOf, den_foldApps] using hne

end Rcic.F3.PSet.MinorInputsFromNonempty

#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.inputs
#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.fields_fit
#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.original_fields
#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.packed_rhsArgs
#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.witness_packed
#print axioms Rcic.F3.PSet.MinorInputsFromNonempty.original_fields_of_witness
