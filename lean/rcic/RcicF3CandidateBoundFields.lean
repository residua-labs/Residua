import rcic.RcicF3CandidateScope
import rcic.RcicF3PropEvalTyped

/-!
# Original field normalization from the actual Prop BoundG clause

The ordinary parameter and preceding-field values supply the exact original
typing context. The existing Prop large-elimination clause of BoundG then
supplies each bounded field typing at the full recursor level vector. The
actual-node reader is transported to the sound family-only prefix before
typed normalization is applied. Neither candidate closure nor typing of
inserted motive, minor or IH values is assumed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateScope
open Rcic.Declarative

/-- Fitting ordinary parameters and the ordinary fields preceding the selected
field give its exact admission context. No inserted recursor locals occur. -/
theorem fits_original_prefix (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (Ps Fs : List (Expr Nat)) (k : Fin Fs.length)
    (ps pre : List PSet.{4})
    (hps : TelFits (mkM P μ) σ Ps ρ0 ps)
    (hpre : TelFits (mkM P μ) σ (Fs.take k.val) (push ps ρ0) pre) :
    Fits (mkM P μ) σ
      (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val))
      (push pre (push ps ρ0)) := by
  have hz : TelFits (mkM P μ) σ (Ps ++ Fs.take k.val) ρ0 (ps ++ pre) :=
    TelFits.append hps hpre
  have hctx : policyPrefixContext (Ps ++ Fs) (Ps.length + k.val) =
      ((Ps ++ Fs.take k.val).take (Ps ++ Fs.take k.val).length).reverse.map
        LocalDecl.assumption := by
    unfold policyPrefixContext
    rw [List.take_length, List.take_append_eq_append_take,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  have hfits := fits_prefixContext (mkM P μ) σ _ ρ0 _ hz
    (Ps ++ Fs.take k.val).length (Nat.le_refl _)
  rw [← hctx, List.take_of_length_le (Nat.le_of_eq hz.length)] at hfits
  rw [push_append] at hfits
  exact hfits

/-- The existing group bound produces normalization of every actual original
Prop field at every fitting ordinary prefix. The level vector keeps all
recursor slots, including the extra motive universe. -/
theorem original_field_normalized (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (h0 : evalTotal σ node.a.family.resultLevel = 0)
    (hpolicy : node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length)
    (k : Fin (node.a.constructorViews j).fields.length)
    (ps pre : List PSet.{4})
    (hps : TelFits (mkM P μ) σ node.a.family.parameters ρ0 ps)
    (hpre : TelFits (mkM P μ) σ ((node.a.constructorViews j).fields.take k.val)
      (push ps ρ0) pre)
    {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel node.E0 fuel ((node.a.constructorViews j).fields[k]) =
      some (ds, b)) :
    Equiv
      (den (mkM P μ) σ (push pre (push ps ρ0)) (policyPi ds b))
      (den (mkM P μ) σ (push pre (push ps ρ0)) ((node.a.constructorViews j).fields[k])) := by
  obtain ⟨l, _hl, d, hd⟩ :=
    hB.2.2.2 node (selection_prop node.a σ h0 hpolicy).1 hpolicy j vs hvs k
  have hdσ : LOKt σ 4 K d := by
    rw [hσ]
    exact hd
  exact recNode_den_piTelescope P μ σ K hE hB.1 hA hI hmem node hES d hdσ hw
    (push pre (push ps ρ0))
    (fits_original_prefix P μ σ node.a.family.parameters
      (node.a.constructorViews j).fields k ps pre hps hpre)

end Rcic.F3.PSet.CandidateScope
