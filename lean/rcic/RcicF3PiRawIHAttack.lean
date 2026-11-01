import rcic.RcicF3PiRawIH
import rcic.RcicF3PiValueAttack
/-! General-depth raw IH non-vacuity and refusal attacks. The semantic
fixture constructs its table, motive, field and IH under Premises4, at every
numeric label. Hidden-reader pins include beta/delta/let; the delta pin
asserts computation only. Universal raw group assembly is open.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawIHAttack
open Rcic.Declarative PiIndex PiRawIH

def base : Nat → List Nat → PSet.{4} := fun _ _ => tyv PiPropPrefixAttack.domain
def dom (f : Nat) : Expr Nat := .const (f + 1) []
def ds (f : Nat) : List (Expr Nat) := [dom f, dom f, dom f]
def args : List (Expr Nat) := [.bvar 0]
def leaf (f : Nat) : Expr Nat := foldApps (.const f []) args
def field (f : Nat) : Expr Nat := policyPi (ds f) (leaf f)
def μ (P : Premises4) (f : Nat) :=
  upd base f (PiValue.table P base (fun _ _ => True) [dom f])
def model (P : Premises4) (f : Nat) := mkM P (μ P f)
def major (f : Nat) : Expr Nat := foldApps (.const f []) (policyLocals 1)
def motive (P : Premises4) (f : Nat) :=
  PiValue.value (model P f) (σOf []) (fun _ => True) [dom f, major f] ρ0

theorem family (P : Premises4) (f : Nat) :
    Equiv ((model P f).μ f [])
      (PiValue.value (model P f) (σOf []) (fun _ => True) [dom f] ρ0) := by
  have clean : ∀ A ∈ [dom f], occursConst f A = false := by
    intro A hA
    have ha := List.mem_singleton.mp hA
    subst A
    have hn : f + 1 ≠ f := by omega
    simp [dom, occursConst, hn]
  have he := PiValue.value_free P base f
    (PiValue.table P base (fun _ _ => True) [dom f]) (base f)
    (σOf []) (fun _ => True) [dom f] clean ρ0
  rw [PiIndependent.upd_self] at he
  change Equiv ((upd base f (PiValue.table P base (fun _ _ => True) [dom f])) f []) _
  rw [upd_eq]
  exact he.symm ▸ Equiv.rfl

theorem field_equiv (P : Premises4) (f : Nat) (ρ : Nat → PSet.{4}) :
    Equiv (((tel (model P f) (σOf []) (ds f) args ρ).erasedType
      (model P f) (fun _ => tv True)))
      (den (model P f) (σOf []) ρ (field f)) := by
  let M := model P f
  apply PiSyntaxCompile.compile_spec M (σOf []) (read M (σOf []) args)
    (fun _ => tv True) (fun _ => dich_tv True) (leaf f)
  apply (PiSyntaxCompile.endEq_iff M (σOf []) (read M (σOf []) args)
    (fun _ => tv True) (leaf f) (ds f) ρ).mpr
  intro xs hxs
  cases xs with
  | nil => exact False.elim hxs
  | cons a xs =>
    cases xs with
    | nil => exact False.elim hxs.2
    | cons b xs =>
      cases xs with
      | nil => exact False.elim hxs.2.2
      | cons c xs =>
        cases xs with
        | nil =>
          have hf : TelFits M (σOf []) [dom f] ρ0 [c] := ⟨hxs.2.2.1, True.intro⟩
          have he := (fapps_congr (family P f) [c]).trans
            (PiValue.apply_value M (σOf []) (fun _ => True) [dom f] ρ0 [c] hf)
          exact he.symm
        | cons _ _ => exact False.elim hxs.2.2.2

def assignment (P : Premises4) (f : Nat) : Nat → PSet.{4} :=
  vcons pempty (vcons (motive P f) ρ0)
def ihExpr (f : Nat) : Expr Nat := policyPi (ds f)
  (foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
    (args ++ [fieldApp (ds f).length]))

/-- Inhabited depth-three, data-indexed raw IH fidelity at every numeric label. -/
theorem inhabited (P : Premises4) (f : Nat) :
    let M := model P f
    let ρ := assignment P f
    motive P f ∈ Ed M (den M (σOf []) ρ0
      (policyPi [dom f, major f] (.sort .zero))) ∧
      TelFits M (σOf []) (ds f) ρ
        [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum] ∧
      pempty ∈ Ed M (den M (σOf []) ρ (field f)) ∧
      ∃ ih, ih ∈ Ed M (den M (σOf []) ρ (ihExpr f)) := by
  dsimp only
  let M := model P f
  let ρ := assignment P f
  let t := tel M (σOf []) (ds f) args ρ
  let mo := motive P f
  let C := PiRawMotive.guarded M (σOf []) (M.μ f []) mo [] [dom f] ρ0
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M (σOf []) _ (ds f) ρ
  have hsem : pempty ∈ Ed M (t.erasedType M (fun _ => tv True)) :=
    (PiPropField.member_iff M t ht (fun _ => True) pempty).mpr
      ⟨Equiv.rfl, fun _ => True.intro⟩
  have hx : pempty ∈ Ed M (den M (σOf []) ρ (field f)) :=
    mem_congr_right (ed_congr M (field_equiv P f ρ)) hsem
  have hmo : mo ∈ Ed M (den M (σOf []) ρ0
      (policyPi [dom f, major f] (.sort .zero))) :=
    PiValue.value_mem P (μ P f) (σOf []) (fun _ => True) [dom f, major f] ρ0
  have hC : ∀ i z, pempty ∈ C i z := by
    intro i z
    apply mem_tv.mpr
    refine ⟨?_, Equiv.rfl⟩
    intro is _ his hz
    have hden := Fapp_den M (σOf []) f [] [] is ρ0
    rw [his.length] at hden
    change den M (σOf []) (push is ρ0) (major f) = fapps (M.μ f []) is at hden
    have hfit : TelFits M (σOf []) [dom f, major f] ρ0 (is ++ [z]) :=
      TelFits.append his ⟨by rw [hden]; exact hz, True.intro⟩
    exact mem_congr_right (PiValue.apply_ed M (σOf []) (fun _ => True)
      [dom f, major f] ρ0 (is ++ [z]) hfit).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hih := t.erasedIH_mem M ht (fun _ => tv True) (fun _ => dich_tv True)
    C (PiRawMotive.guarded_dich M (σOf []) (M.μ f []) mo [] [dom f] ρ0)
    (fun _ => pempty) (fun i z _ => hC i z) hsem
  have he := normalized_spec M rfl (σOf []) f [] (fun _ => True) [] [dom f] []
    rfl (family P f) mo hmo (ds f) args rfl ρ (fun _ _ => rfl) (.bvar 1) rfl hx
  have hn : f + 1 ≠ f := by omega
  have hdatum : PiPropPrefixAttack.datum ∈ Ed M (tyv PiPropPrefixAttack.domain) :=
    mem_congr_right (ed_tyv M (Or.inr (fun h => dataVal_ne_pempty 7 []
      (mem_singleton.mp h).symm))).symm (mem_singleton.mpr Equiv.rfl)
  have hd' : ∀ τ : Nat → PSet.{4}, PiPropPrefixAttack.datum ∈ Ed M
      (den M (σOf []) τ (dom f)) := by
    intro τ
    change PiPropPrefixAttack.datum ∈ Ed M ((upd base f
      (PiValue.table P base (fun _ _ => True) [dom f])) (f + 1) [])
    rw [upd_ne _ _ _ hn]; exact hdatum
  exact ⟨hmo, ⟨hd' _, hd' _, hd' _, True.intro⟩, hx,
    ⟨_, mem_congr_right (ed_congr M he) hih⟩⟩

def beta (f : Nat) : Expr Nat :=
  .app (.lam (.sort .zero) (.bvar 0)) (field f)
def zeta (f : Nat) : Expr Nat := .letE (.sort .zero) (field f) (.bvar 0)
def aliasMember (f : Nat) : CheckedMember :=
  ⟨.definitionM, 0, .sort .zero, some (field f)⟩
def env (f : Nat) : ResolvedEnv := extendEnv emptyEnv (f + 2) (aliasMember f)
def delta (f : Nat) : Expr Nat := .const (f + 2) []

/-- Elementary executable pins. The delta environment here is a reader
fixture; this theorem makes no raw environment typing claim. -/
theorem hidden_builders : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      funIHType (env f) 32 0 A (.bvar 0) 3 = some (ihExpr f) := by
  decide

/-- The inhabited family still refuses an actual out-of-domain data index. -/
theorem invalid_index (P : Premises4) (f : Nat) (z : PSet.{4}) :
    z ∉ Ed (model P f) (fapps ((model P f).μ f []) [dataVal 8 []]) := by
  intro hz
  let M := model P f
  have hm := mem_congr_right (ed_congr M (fapps_congr (family P f) [dataVal 8 []])) hz
  have hf := ((PiValue.apply_mem_iff M (σOf []) (fun _ => True) [dom f] ρ0
    [dataVal 8 []] rfl z).mp hm).1.1
  have hn : f + 1 ≠ f := by omega
  change dataVal 8 [] ∈ Ed M ((upd base f
    (PiValue.table P base (fun _ _ => True) [dom f])) (f + 1) []) at hf
  rw [upd_ne _ _ _ hn] at hf
  have hd : Dich (PiPropPrefixAttack.domain : PSet.{4}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have he := mem_singleton.mp (mem_congr_right (ed_tyv M hd) hf)
  have htags : 8 = 7 := (dataVal_inj rfl he).1
  cases htags
end Rcic.F3.PSet.PiRawIHAttack
