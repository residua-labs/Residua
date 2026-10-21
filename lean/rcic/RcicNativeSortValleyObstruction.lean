import rcic.RcicNativeKPartialPeak
import rcic.RcicNativeKPartialObstruction

set_option autoImplicit false
set_option maxRecDepth 16384

/-!
# Sort-indexed native valleys still fail

The admitted True counterexample from `RcicNativeKPartialPeak` has
function-indexed endpoints `g` and `h`.  Put them under one fresh
assumption `F : minorIndex -> Sort 1`.  The actual native application
conversion gives `F g = F h : Sort 1`, but every raw star retains the
assumption head and the two incompatible argument invariants.

Thus restricting a native-valley supplier to *sorting indices* is still
false.  This does not refute the narrower supplier whose endpoints are
two written Pi expressions: both endpoints here are applications.

The positive context, typings and native conversion use no sorting
coherence or rows supplier.  The negative proof is a concrete client of
the same existing `sortUnique_of_inScope trueEnvUWfT trueEnvUWfT_inScope`
supplier as the imported all-star obstruction.  That supplier uses the
rows route internally; it is not a positive construction of sorting,
Pi injectivity, or confluence on arbitrary admitted environments.

All raw constructors, including plain K, eta-K and both union-iota arms,
are retained.  Argument changes, lambda annotation changes, universe
retagging and arbitrary index conversion remain allowed.  Recursive
calls inspect only original raw children or literal star tails.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeSortValleyObstructionAudit

open StarStripUnitPeakAudit
open StarStripUnitObstructionAudit (RecSpine)
open NativeKPartialPeakAudit
open NativeKPartialObstructionAudit (recSpine_step doubleLam_step)

private abbrev one : Level := .succ .zero
private abbrev two : Level := .succ (.succ .zero)
private abbrev minorSort : Level := .imax two (.imax .zero two)
private abbrev neutralSort : Level := .imax minorSort two

/-! ## Positive admitted context and actual sorting-index conversion -/

/-- The existing function index has its literal Pi-formation sorting. -/
def minorIndexSort {Γ : LCtx} :
    HasTyT trueEnvU 0 Γ minorIndex (.sort minorSort) :=
  .pi Γ (.sort one) two unitIndex (.imax .zero two) (.sort Γ one)
    (.pi _ unitDomain .zero (.sort one) two trueEnvUF_ty (.sort _ one))

/-- The fresh neutral function returns types at `Sort 1`. -/
def neutralType : Expr Nat := .pi minorIndex (.sort one)

/-- Its type is sorted by two ordinary Pi-formation derivations. -/
def neutralTypeSort {Γ : LCtx} :
    HasTyT trueEnvU 0 Γ neutralType (.sort neutralSort) :=
  .pi Γ minorIndex minorSort (.sort one) two minorIndexSort (.sort _ one)

/-- Only one new assumption is needed; the environment is unchanged. -/
def sortContext : LCtx := [.assumption neutralType]

/-- The context is admitted by the constructed positive sorting above. -/
def sortContextWf : CtxWfT trueEnvU 0 sortContext :=
  .assumption [] neutralType neutralSort .nil neutralTypeSort

/-- The exact assumption lookup; the stored type is closed. -/
def neutralHeadTy : HasTyT trueEnvU 0 sortContext (.bvar 0) neutralType :=
  .bvar sortContext 0 neutralType rfl

/-- The original actual conversion is weakened under the fresh assumption. -/
def minorConversionInContext : ConvT trueEnvU 0 sortContext
    minorPartialRec minorContracted minorIndex :=
  convTWeaken (.assumption neutralType) (envClosed_of_envWfT trueEnvUWfT)
    (c := 0) minorConversion

/-- The left endpoint is an application, not a written Pi expression. -/
def sortLeft : Expr Nat := .app (.bvar 0) minorPartialRec

/-- The right endpoint has the same neutral function and the other argument. -/
def sortRight : Expr Nat := .app (.bvar 0) minorContracted

def sortLeftTy : HasTyT trueEnvU 0 sortContext sortLeft (.sort one) :=
  .app _ _ _ _ _ neutralHeadTy minorPartialTy

def sortRightTy : HasTyT trueEnvU 0 sortContext sortRight (.sort one) :=
  .app _ _ _ _ _ neutralHeadTy
    (hasTyTWeaken (.assumption neutralType) (envClosed_of_envWfT trueEnvUWfT)
      (c := 0) minorContractedTy)

/-- A native conversion at a literal sorting index, built by application
congruence from the original certified peak's actual conversion. -/
def sortConversion : ConvT trueEnvU 0 sortContext sortLeft sortRight (.sort one) :=
  .app sortContext (.bvar 0) (.bvar 0) minorPartialRec minorContracted
    minorIndex (.sort one) (.refl _ _ _ neutralHeadTy) minorConversionInContext

/-! ## Negative client of the concrete admitted sorting supplier -/

private theorem unitSortUnique : F8A2Support.SortUnique trueEnvU 0 :=
  sortUnique_of_inScope trueEnvUWfT trueEnvUWfT_inScope 0

/-- Inverting the one assumption's original lookup transports a proposed
proof sorting back to its positively sorted stored type. -/
private theorem neutralHead_notProof :
    NotProof trueEnvU 0 sortContext (.bvar 0) := by
  intro P hp hP
  obtain ⟨T, hlk, c⟩ := hasTyTInv_bvar hp rfl
  have he : T = neutralType := by
    have hlk' : lookupType sortContext 0 = some neutralType := rfl
    exact Option.some.inj (hlk.symm.trans hlk')
  subst T
  obtain ⟨h0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT
    sortContextWf c.symmT hP
  have bad := unitSortUnique trueEnvUWfT sortContextWf neutralTypeSort h0
    (fun _ => none)
  simp [neutralSort, minorSort, two, eval] at bad

/-- This applies to every argument and every possible proof index.
Proofhood of an application would make its fixed function a proof. -/
private theorem neutralApp_notProof (a : Expr Nat) :
    NotProof trueEnvU 0 sortContext (.app (.bvar 0) a) := by
  intro P hp hP
  obtain ⟨Q, ⟨hQ⟩, ⟨hq⟩⟩ := F8A2Support.proof_app_function
    unitSortUnique trueEnvUWfT sortContextWf ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  exact neutralHead_notProof hq hQ

/-- The assumption head remains the exact variable through every raw
constructor.  The recursive subjects are `conv` and iota preparation
children; the assumption cannot fire local zeta. -/
private theorem neutralHead_step :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext x j T →
    x = .bvar 0 → j = .bvar 0
  | _, _, _, .refl .., hx => hx
  | _, _, _, .conv _ _ _ _ _ p _, hx => neutralHead_step p hx
  | _, _, _, .peq _ _ _ _ h, hx => by
      subst hx
      exact (neutralHead_notProof h.hp h.hT).elim
  | _, _, _, .bvarZeta _ _ _ _ _ _ hget _ _ _, hx => by
      injection hx with hi
      subst hi
      change some (LocalDecl.assumption neutralType) =
        some (LocalDecl.letBinding _ _) at hget
      exact nomatch hget
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, hx =>
      (F8EtaK.derivedIotaU_bvar_source_false hI (neutralHead_step prep hx)).elim
  | _, _, _, .iotaStarK .., hx => by
      simp only [recCall, foldApps_snoc] at hx
      exact nomatch hx
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., hx => by
      have hh := (iotaStarKEta_head happ).1
      rw [hx] at hh
      exact nomatch hh
  | _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, .consts .., hx => nomatch hx
  | _, _, _, .delta .., hx => nomatch hx
  | _, _, _, .app .., hx => nomatch hx
  | _, _, _, .beta .., hx => nomatch hx
  | _, _, _, .lam .., hx => nomatch hx
  | _, _, _, .pi .., hx => nomatch hx
  | _, _, _, .letE .., hx => nomatch hx
  | _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, .lit .., hx => nomatch hx
  | _, _, _, .eta .., hx => nomatch hx

/-- Both union-iota arms have a constant spine head and cannot fire
at an application of the neutral assumption. -/
private theorem neutralApp_no_iota {x rhs a : Expr Nat}
    (hI : DerivedIotaU trueEnvU x rhs) (hx : x = .app (.bvar 0) a) : False := by
  cases hI with
  | ofU w =>
      have hh := congrArg (fun e : Expr Nat => (appsSpine e).1) hx
      simp only [iotaLhsOf, recCall, appsSpine_foldApps_const, appsSpine] at hh
      exact nomatch hh
  | ofUS w =>
      have hh := congrArg (fun e : Expr Nat => (appsSpine e).1) hx
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const, appsSpine] at hh
      exact nomatch hh

/-- An invariant of the argument is preserved under the fixed neutral
application.  `hQ` is instantiated below with the two existing constructed
raw-step invariants; it is never a final supplier premise.  In the app
arm it is applied to the actual original argument child at that child's
own native index. -/
private theorem neutralApp_step (Q : Expr Nat → Prop)
    (hQ : ∀ {a b T : Expr Nat},
      ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext a b T → Q a → Q b) :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext x j T →
    (a : Expr Nat) → x = .app (.bvar 0) a → Q a →
    ∃ b : Expr Nat, j = .app (.bvar 0) b ∧ Q b
  | _, _, _, .refl .., a, hx, ha => ⟨a, hx, ha⟩
  | _, _, _, .conv _ _ _ _ _ p _, a, hx, ha =>
      neutralApp_step Q hQ p a hx ha
  | _, _, _, .peq _ _ _ _ h, a, hx, _ => by
      subst hx
      exact (neutralApp_notProof a h.hp h.hT).elim
  | _, _, _, .app _ f f' a a' _ _ _ _ _ pf _ _ _ pa _, b, hx, hb => by
      obtain ⟨hf, ha⟩ := Expr.app.inj hx
      subst ha
      have hf' := neutralHead_step pf hf
      exact ⟨a', congrArg (fun f : Expr Nat => Expr.app f a') hf', hQ pa hb⟩
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, a, hx, ha => by
      obtain ⟨b, he, _⟩ := neutralApp_step Q hQ prep a hx ha
      exact (neutralApp_no_iota hI he).elim
  | _, _, _, .iotaStarK .., _, hx, _ => by
      have hh := congrArg (fun e : Expr Nat => (appsSpine e).1) hx
      simp only [recCall, appsSpine_foldApps_const, appsSpine] at hh
      exact nomatch hh
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, hx, _ => by
      have hh := (iotaStarKEta_head happ).1
      rw [hx] at hh
      exact nomatch hh
  | _, _, _, .beta .., _, hx, _ => by
      have hh := (Expr.app.inj hx).1
      exact nomatch hh
  | _, _, _, .sortEq .., _, hx, _ => nomatch hx
  | _, _, _, .consts .., _, hx, _ => nomatch hx
  | _, _, _, .bvarZeta .., _, hx, _ => nomatch hx
  | _, _, _, .delta .., _, hx, _ => nomatch hx
  | _, _, _, .lam .., _, hx, _ => nomatch hx
  | _, _, _, .pi .., _, hx, _ => nomatch hx
  | _, _, _, .letE .., _, hx, _ => nomatch hx
  | _, _, _, .zeta .., _, hx, _ => nomatch hx
  | _, _, _, .lit .., _, hx, _ => nomatch hx
  | _, _, _, .eta .., _, hx, _ => nomatch hx

/-- Literal-tail induction, allowing each original argument child to
have its own independently chosen type index. -/
private theorem neutralApp_star (Q : Expr Nat → Prop)
    (hQ : ∀ {a b T : Expr Nat},
      ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext a b T → Q a → Q b) :
    {x j T : Expr Nat} →
    ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext x j T →
    (a : Expr Nat) → x = .app (.bvar 0) a → Q a →
    ∃ b : Expr Nat, j = .app (.bvar 0) b ∧ Q b
  | _, _, _, .refl .., a, hx, ha => ⟨a, hx, ha⟩
  | _, _, _, .tail p ps, a, hx, ha => by
      obtain ⟨b, he, hb⟩ := neutralApp_step Q hQ p a hx ha
      exact neutralApp_star Q hQ ps b he hb

/-- The right argument retains two lambdas, an assumption minor, and
an actual positive sorting of its possibly changed outer annotation. -/
private def DoubleLam (e : Expr Nat) : Prop :=
  ∃ A B : Expr Nat, e = .lam A (.lam B (.bvar 1)) ∧
    Nonempty (HasTyT trueEnvU 0 sortContext A (.sort two))

private theorem doubleLam_preserved {a b T : Expr Nat}
    (p : ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 sortContext a b T)
    (ha : DoubleLam a) : DoubleLam b := by
  obtain ⟨A, B, he, ⟨hA⟩⟩ := ha
  exact doubleLam_step sortContextWf p A B hA he

/-- The left endpoint's argument may change arbitrarily inside its
one-argument recursor spine; its head and arity remain. -/
theorem sortLeft_star_shape {j T : Expr Nat}
    (s : PiStar trueEnvU 0 sortContext sortLeft j T) :
    ∃ a : Expr Nat, j = .app (.bvar 0) a ∧ RecSpine 1 a :=
  neutralApp_star (RecSpine 1)
    (fun p ha => recSpine_step sortContextWf p 1 (by decide) ha)
    s minorPartialRec rfl ⟨[two], rfl, eqNList_refl [two], rfl⟩

/-- The right endpoint's two lambda annotations may change by native
conversion; the inner bound minor and the positive outer sorting remain. -/
theorem sortRight_star_shape {j T : Expr Nat}
    (s : PiStar trueEnvU 0 sortContext sortRight j T) :
    ∃ a A B : Expr Nat, j = .app (.bvar 0) a ∧
      a = .lam A (.lam B (.bvar 1)) ∧
      Nonempty (HasTyT trueEnvU 0 sortContext A (.sort two)) := by
  obtain ⟨a, hj, A, B, ha, hA⟩ := neutralApp_star DoubleLam
    doubleLam_preserved s minorContracted rfl
      ⟨.sort one, unitDomain, rfl, ⟨.sort sortContext one⟩⟩
  exact ⟨a, A, B, hj, ha, hA⟩

/-- No length of full raw stars joins these sort-typed terms.  The two
joining indices may be unrelated; no certificate or decoration is required. -/
theorem admitted_sort_no_valley {j T₁ T₂ : Expr Nat}
    (s : PiStar trueEnvU 0 sortContext sortLeft j T₁)
    (t : PiStar trueEnvU 0 sortContext sortRight j T₂) : False := by
  obtain ⟨a, hs, ls, hh, _, _⟩ := sortLeft_star_shape s
  obtain ⟨b, A, B, ht, hb, _⟩ := sortRight_star_shape t
  have hab : a = b := (Expr.app.inj (hs.symm.trans ht)).2
  rw [hab, hb] at hh
  exact nomatch hh

/-- The existing full native-valley carrier is empty at the actual
sorting-index conversion's endpoints, even at any alternative index. -/
theorem admitted_no_sort_raw_valley {T : Expr Nat} :
    ¬ Nonempty (NativeValley trueEnvU 0 sortContext sortLeft sortRight T) := by
  rintro ⟨V⟩
  exact admitted_sort_no_valley V.left V.right

/-- The candidate restriction to sorting indices; the endpoints remain
arbitrary terms.  The next theorem refutes this precise proposition. -/
def SortConvValleys (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b : Expr Nat} {u : Level},
    ConvT E n Γ a b (.sort u) →
    Nonempty (NativeValley E n Γ a b (.sort u))

/-- An actual admitted native conversion at a sort refutes the proposed
sort-index-only restriction.  Nothing here refutes written-Pi endpoints. -/
theorem admitted_no_sortConvValleys : ¬ SortConvValleys trueEnvU 0 := by
  intro join
  exact admitted_no_sort_raw_valley (join sortContextWf sortConversion)

#print axioms minorIndexSort
#print axioms neutralType
#print axioms neutralTypeSort
#print axioms sortContext
#print axioms sortContextWf
#print axioms neutralHeadTy
#print axioms minorConversionInContext
#print axioms sortLeft
#print axioms sortRight
#print axioms sortLeftTy
#print axioms sortRightTy
#print axioms sortConversion
#print axioms unitSortUnique
#print axioms neutralHead_notProof
#print axioms neutralApp_notProof
#print axioms neutralHead_step
#print axioms neutralApp_no_iota
#print axioms neutralApp_step
#print axioms neutralApp_star
#print axioms DoubleLam
#print axioms doubleLam_preserved
#print axioms sortLeft_star_shape
#print axioms sortRight_star_shape
#print axioms admitted_sort_no_valley
#print axioms admitted_no_sort_raw_valley
#print axioms SortConvValleys
#print axioms admitted_no_sortConvValleys

end Rcic.Declarative.NativeValleys.NativeSortValleyObstructionAudit
