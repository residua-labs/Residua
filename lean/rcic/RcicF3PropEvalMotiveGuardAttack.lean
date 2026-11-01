import rcic.RcicF3PropEvalMotiveGuard
import rcic.RcicF3PropEvalPacket
import rcic.RcicF3PropEvalAttack

/-!
# Typed-motive inversion at the actual admitted AccR fixture

The installed raw family supplies its Prop face. The actual stored motive
and produced evaluation then supply guarded membership by the new inversion
theorem, without separate index-fitting or constructor-typing inputs. The
evaluated result is the existing nonempty data value at the extra motive
universe. This is a local composition witness; closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalMotiveGuardAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack

noncomputable def ctx (P : Premises4) : PropEval.Context :=
  PropEvalAttack.context P (installed P)

/-- Full application membership in the installed AccR family has the proof
face, including fitting arguments other than the fixture's chosen parameter. -/
theorem family_proof (P : Premises4) (ys : List PSet.{4}) (hlen : ys.length = 1)
    (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (installed P)) (fapps (installed P 0 []) ys)) :
    Equiv z pempty := by
  let μ := installed P
  let M := mkM P μ
  let F := frame P μ fd
  have hRaw : Admissible fd F := (RawFamilyPropAttack.acc_closed P μ).1
  have hz' : z ∈ Ed M (fapps (ofFrame P μ fd F []) ys) :=
    mem_congr_right (ed_congr M (fapps_congr (installed_family P) ys)) hz
  have hne : ¬ Equiv (fapps (ofFrame P μ fd F []) ys) pempty := by
    intro he
    exact not_mem_pempty (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hz')
  have hfit : TelFits M (σOf []) (fd.params ++ fd.indices) ρ0 ys :=
    fits_of_fapps_ne M (σOf []) (endValue_resp F [] _)
      (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 ys hlen hne
  have hzF : z ∈ F [] (key ys) :=
    mem_congr_right (apply_ofFrame_ed P μ fd F hRaw [] ys hfit) hz'
  have hface := (hRaw [] (key ys)).2
  change ∀ y, y ∈ F [] (key ys) → Equiv y pempty at hface
  exact hface z hzF

/-- Guarded output membership is produced from the actual typed motive and
the endpoint of the evaluation, without constructor/index callbacks. -/
theorem guarded (P : Premises4) {i : Index.{4}} {z : PSet.{4}}
    (he : PropEval.Eval (ctx P) i z) :
    z ∈ PropEval.childCarrier (ctx P) (.param 0) i := by
  exact he.mem_guarded_of_typed_motive (.param 0) rfl
    (motive_mem P (installed P)) (family_proof P)

def Witness (P : Premises4) : Prop :=
  PropEval.Eval (ctx P) (key [parameter]) datum ∧
  datum ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
  ¬ Equiv datum pempty

/-- A nonempty value is evaluated and admitted by the guarded motive at its
actual extra universe slot; all hypotheses of the inversion are produced. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨PropEvalAttack.inhabited P, guarded P (PropEvalAttack.inhabited P),
    dataVal_ne_pempty _ _⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalMotiveGuardAttack
