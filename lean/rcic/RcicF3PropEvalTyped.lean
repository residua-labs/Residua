import rcic.RcicF3PropEvalUnique
import rcic.RcicF3FieldSmall

/-!
# Mutual evaluation comparison from bounded typed proof fields

This extends the existing propTel_of_typings argument to an arbitrary syntax
valuation, preserving recursor motive levels outside the family arity. The
ordinary sound prefix and each bounded field typing are explicit. The
admitted elimination selection supplies the singleton constructor census.
No completed-group soundness or evaluation existence is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet
open Rcic.Declarative

/-- Bounded original field typings produce PropTel at the actual syntax valuation.
This extends propTel_of_typings from RcicF3FieldSmall.lean. -/
theorem propTel_of_typings_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K σ : Nat → Nat) {S : ResolvedEnv} {ar : Nat}
    (Ps Fs : List (Expr Nat)) (hES : EnvSound (mkM P μ) σ K S ar)
    (hB : ∀ k : Fin Fs.length, ∃ l : Level, evalTotal σ l = 0 ∧
      ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val))
        (Fs[k]) (.sort l), LOKt σ 4 K d)
    (ps : List PSet.{4}) (hps : TelFits (mkM P μ) σ Ps ρ0 ps) :
    PropTel (mkM P μ) σ Fs (push ps ρ0) := by
  suffices H : ∀ (d m : Nat), Fs.length - m = d → ∀ zs : List PSet.{4}, zs.length = m →
      TelFits (mkM P μ) σ (Ps ++ Fs.take m) ρ0 (ps ++ zs) →
      PropTel (mkM P μ) σ (Fs.drop m) (push zs (push ps ρ0)) by
    have := H Fs.length 0 (Nat.sub_zero _) [] rfl (by simpa using hps)
    simpa using this
  intro d
  induction d with
  | zero =>
      intro m hd zs _ _
      rw [List.drop_eq_nil_of_le (by omega)]
      trivial
  | succ d ih =>
      intro m hd zs hzl hz
      have hm : m < Fs.length := by omega
      rw [List.drop_eq_getElem_cons hm]
      have henv : push zs (push ps ρ0) = push (ps ++ zs) ρ0 := (push_append ps zs ρ0).symm
      have hprop : ∀ y, y ∈ Ed (mkM P μ)
          (den (mkM P μ) σ (push zs (push ps ρ0)) Fs[m]) → Equiv y pempty := by
        intro y hy
        obtain ⟨l, h0, dd, hdd⟩ := hB ⟨m, hm⟩
        have hctx : policyPrefixContext (Ps ++ Fs) (Ps.length + m) =
            ((Ps ++ Fs.take m).take (Ps ++ Fs.take m).length).reverse.map LocalDecl.assumption := by
          unfold policyPrefixContext
          rw [List.take_length, List.take_append_eq_append_take, List.take_of_length_le (by omega),
            Nat.add_sub_cancel_left]
        have hfits := fits_prefixContext (mkM P μ) σ _ ρ0 _ hz
          (Ps ++ Fs.take m).length (Nat.le_refl _)
        rw [← hctx, List.take_of_length_le (Nat.le_of_eq hz.length)] at hfits
        have hs := sound_ty (P.good _ rfl) hES dd hdd _ hfits
        have e : den (mkM P μ) σ (push (ps ++ zs) ρ0) (.sort l) = tyv (U W4 0) := by
          show tyv (U W4 (evalTotal σ l)) = _
          rw [h0]
        rw [e] at hs
        have hX := mem_congr_right (ed_tyv _ (U4_dich _)) hs
        rw [henv] at hy
        exact ed_of_mem_U0 _ hX hy
      refine ⟨hprop, fun hin => ?_⟩
      have hz' : TelFits (mkM P μ) σ (Ps ++ Fs.take (m + 1)) ρ0 (ps ++ (zs ++ [pempty])) := by
        rw [List.take_succ, List.getElem?_eq_getElem hm, ← List.append_assoc, ← List.append_assoc]
        refine TelFits.append hz ⟨?_, trivial⟩
        rw [← henv]
        exact hin
      have := ih (m + 1) (by omega) (zs ++ [pempty]) (by simp [hzl]) hz'
      rw [push_append] at this
      exact this

namespace PropEval
open PiIndex

/-- Typed-prefix soundness and the existing proof-field typings pay both root conditions.
The recursor syntax valuation is left arbitrary. -/
theorem Eval.functional_of_typed_proof_fields (C : Context)
    (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (S : ResolvedEnv) (ar : Nat) (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K S ar)
    (hB : ∀ (j : Fin C.node.a.constructors.length)
      (k : Fin (C.node.a.constructorViews j).fields.length),
      ∃ l : Level, evalTotal C.σ l = 0 ∧
        ∃ d : HasTyT S ar
          (policyPrefixContext (C.node.a.family.parameters ++ (C.node.a.constructorViews j).fields)
            (C.node.a.family.parameters.length + k.val))
          ((C.node.a.constructorViews j).fields[k]) (.sort l), LOKt C.σ 4 K d)
    {i : Index.{4}} {z z' : PSet.{4}} (h : Eval C i z) (h' : Eval C i z') :
    Equiv z z' := by
  apply h.functional_of_proof_fields C (selection_prop C.node.a C.σ h0 hpolicy).2
    (fun j ps hps _ => ?_) h'
  rw [hM] at hps ⊢
  exact propTel_of_typings_at P μ K C.σ C.node.a.family.parameters
    (C.node.a.constructorViews j).fields hES (hB j) ps hps


/-- The existing BoundG clause supplies the typed proof fields at the full
recursor universe vector, including the extra motive slot. It places no
family-arity length restriction on that vector. Prefix soundness remains
an explicit input; neither evaluation existence nor group closure is assumed. -/
theorem Eval.functional_of_boundG (C : Context)
    (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hB : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K (extendEnv C.E C.f fm)
      C.node.a.family.member.arity)
    (vs : List Nat) (hσ : C.σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K C.rr)
    {i : Index.{4}} {z z' : PSet.{4}} (h : Eval C i z) (h' : Eval C i z') :
    Equiv z z' := by
  apply Eval.functional_of_typed_proof_fields C P μ K
    (extendEnv C.E C.f fm) C.node.a.family.member.arity hM h0 hpolicy hES ?_ h h'
  intro j k
  obtain ⟨l, hl, d, hd⟩ :=
    hB.2.2.2 C.node (selection_prop C.node.a C.σ h0 hpolicy).1 hpolicy j vs hvs k
  exact ⟨l, hl C.σ, d, by rw [hσ]; exact hd⟩

end PropEval
end Rcic.F3.PSet
