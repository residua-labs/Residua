import rcic.RcicF3PiAdmission
import rcic.RcicF3PiRawFieldViews

/-!
# Admission's independence evidence through IH insertion

The actual admitted field reader supplies family-free normalized domains and
the complete argument list. These facts survive every binder insertion.
They accompany the original field view; no arity-only replacement is made.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCleanViews
open Rcic.Declarative

def Clean (E : ResolvedEnv) (fuel f nu np ni : Nat)
    (A : Expr Nat) : FieldShape → Prop
  | .nonrecursive => occursConst f A = false
  | .recursive inner =>
      ∃ ds args : List (Expr Nat), ds.length = inner ∧ args.length = np + ni ∧
        piTelescopeFuel E fuel A = some (ds, foldApps (.const f (canonL nu)) args) ∧
        (∀ e ∈ ds, occursConst f e = false) ∧
        (∀ e ∈ args, occursConst f e = false)

theorem of_admitted {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni (np + prior) A = .permitted s idx) :
    Clean E fuel f nu np ni A s := by
  cases s with
  | nonrecursive => exact fieldAnalyze_nonrec_free h
  | recursive inner =>
      obtain ⟨ds, args, hd, ha, hr, hf, hi⟩ :=
        PiIndependent.admitted_shape h (by omega)
      exact ⟨ds, args, hd, ha, piTelescopeFuel_mono E (Nat.sub_le fuel 1) hr, hf, hi⟩

theorem liftFields_free (f a : Nat) (ds : List (Expr Nat))
    (h : ∀ e ∈ ds, occursConst f e = false) (c : Nat) :
    ∀ e ∈ liftFields a ds c, occursConst f e = false := by
  induction ds generalizing c with
  | nil => intro e he; exact (List.not_mem_nil _ he).elim
  | cons A ds ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rw [occursConst_lift]
        exact h A (List.mem_cons_self _ _)
      · exact ih (fun e he => h e (List.mem_cons_of_mem _ he)) (c + 1) e he

theorem Clean.lift {E : ResolvedEnv} (hcl : EnvClosed E)
    {fuel f nu np ni : Nat} {A : Expr Nat} {s : FieldShape}
    (h : Clean E fuel f nu np ni A s) (c a : Nat) :
    Clean E fuel f nu np ni (Rcic.Declarative.lift c a A) s := by
  cases s with
  | nonrecursive =>
      change occursConst f (Rcic.Declarative.lift c a A) = false
      rw [occursConst_lift]
      exact h
  | recursive inner =>
      obtain ⟨ds, args, hd, ha, hr, hf, hi⟩ := h
      have ht := PiRawRename.read_lift E hcl fuel hr c a
      rw [foldApps_lift, Rcic.Declarative.lift] at ht
      refine ⟨liftFields a ds c, args.map (Rcic.Declarative.lift (c + ds.length) a),
        ?_, ?_, ht, liftFields_free f a ds hf c, ?_⟩
      · rw [liftFields_length']; exact hd
      · rw [List.length_map]; exact ha
      · intro e he
        obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
        rw [occursConst_lift]
        exact hi e₀ he₀

/-- Any successful read at the recorded fuel has the admitted clean domains
and full argument list, including its dependent indices. -/
theorem Clean.recursive_frees {E : ResolvedEnv} {fuel f nu np ni inner : Nat}
    {A : Expr Nat} (h : Clean E fuel f nu np ni A (.recursive inner))
    {ds args : List (Expr Nat)}
    (hr : piTelescopeFuel E fuel A = some (ds, foldApps (.const f (canonL nu)) args)) :
    (∀ e ∈ ds, occursConst f e = false) ∧ (∀ e ∈ args, occursConst f e = false) := by
  obtain ⟨ds₀, args₀, _, _, hr₀, hf, hi⟩ := h
  have he := Option.some.inj (hr₀.symm.trans hr)
  have hd : ds₀ = ds := congrArg Prod.fst he
  subst ds₀
  have ha : args₀ = args := (foldApps_const_inj (congrArg Prod.snd he)).2
  subst args₀
  exact ⟨hf, hi⟩

end Rcic.F3.PSet.PiCleanViews
