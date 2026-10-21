/-
06 §19 `→` direction, expression layer (twin of `ScmElabErase`): a typed
`CoreExpr` elaborates — `elabE` accepts `e.erase` at its own type whenever
the fuel covers the expression's decode depth.  `exprFuel` is the wire
decoder's depth measure, and `exprFuel e ≤ (encExpr e).length`
(`ScmWireInv`) makes the carrier's `fuel = b.length` convention adequate.

The auxiliary list/branches/fields/args completeness lemmas take the
fuel-`f` instance of the main theorem as a parameter (the `ScmElabErase`
pattern).  `toArgs_of_mapFst` discharges the signature match once the
elaborated list's types are exactly the parameter list.
-/
import rcic.ScmWireInv
import rcic.ScmElabErase

namespace Rcic.Scm.ElabComplete

open Rcic.Scm Rcic.Scm.Erase Rcic.Scm.Wire

variable {S : Sig}

/-- `Except.ok` under `bind` reduces to the continuation applied. -/
theorem ok_bind {α β : Type} (a : α) (g : α → Except String β) :
    ((Except.ok a : Except String α) >>= g) = g a := rfl

/-- `pure` for `Except` is `.ok`. -/
theorem pure_ok {α : Type} (a : α) : (pure a : Except String α) = .ok a := rfl

/-- The carrier's prim lookup accepts every `PrimOp` under its own name. -/
theorem primOfString_primName (op : PrimOp) :
    primOfString (primName op) = some op := by
  cases op <;> rfl

theorem Args_erase_length : ∀ {Γ : List CoreTy} {ps : List CoreTy}
    (as : Args S Γ ps), as.erase.length = ps.length
  | _, _, .nil => rfl
  | _, _, .cons _ xs => congrArg Nat.succ (Args_erase_length xs)

theorem Branches_erase_length : ∀ {Γ : List CoreTy} {ts : List CoreTy}
    {T : CoreTy} (bs : Branches S Γ ts T), bs.erase.length = ts.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ bs => congrArg Nat.succ (Branches_erase_length bs)

theorem Fields_erase_length : ∀ {Γ : List CoreTy} {fs : List (String × CoreTy)}
    (xs : Fields S Γ fs), xs.erase.length = fs.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ xs => congrArg Nat.succ (Fields_erase_length xs)

/-- `toArgs` succeeds when the elaborated list's types are exactly `ps`. -/
theorem toArgs_of_mapFst {Γ : List CoreTy} :
    ∀ {ps : List CoreTy} (xs : List (Σ T, CoreExpr S Γ T)),
    xs.map Sigma.fst = ps → ∃ a : Args S Γ ps, toArgs xs ps = some a
  | [], xs, h => by
      cases xs with
      | nil => exact ⟨.nil, rfl⟩
      | cons x xs' => simp at h
  | p :: ps', xs, h => by
      cases xs with
      | nil => simp at h
      | cons x xs' =>
        obtain ⟨T, e⟩ := x
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, hps⟩ := h
        obtain ⟨a, ha⟩ := toArgs_of_mapFst xs' hps
        refine ⟨.cons e a, ?_⟩
        dsimp only [toArgs]
        rw [dif_pos rfl, ha]
        rfl

/-- `elabListWith` accepts an `Args` erasure whose member fuel is covered,
    returning elaborations at exactly the parameter types. -/
theorem elabListWith_of_Args {Γ : List CoreTy} (f : Nat)
    (g : RawExpr → Elab S Γ)
    (hg : ∀ {T' : CoreTy} (e : CoreExpr S Γ T'), exprFuel e.erase < f →
      ∃ e', g e.erase = .ok ⟨T', e'⟩) :
    ∀ {ps : List CoreTy} (as : Args S Γ ps), exprsFuel as.erase < f →
      ∃ xs : List (Σ T, CoreExpr S Γ T), elabListWith g as.erase = .ok xs ∧
        xs.map Sigma.fst = ps
  | _, .nil, _ => ⟨[], rfl, rfl⟩
  | _, .cons x xs, hf => by
      have h' : max (exprFuel x.erase) (exprsFuel xs.erase) < f := hf
      obtain ⟨e', he'⟩ := hg x (by omega)
      obtain ⟨xs', hxs', hmap⟩ := elabListWith_of_Args f g hg xs (by omega)
      refine ⟨⟨_, e'⟩ :: xs', ?_, ?_⟩
      · show elabListWith g (x.erase :: xs.erase) = .ok (⟨_, e'⟩ :: xs')
        dsimp only [elabListWith]
        rw [he', hxs']
        simp only [ok_bind]
        rfl
      · show ((⟨_, e'⟩ :: xs').map Sigma.fst) = _
        rw [List.map_cons, hmap]

/-- `exprFuel` of a cons-list head. -/
theorem exprFuel_head_le {e : RawExpr} {es : List RawExpr} :
    exprFuel e ≤ exprsFuel (e :: es) := by
  show exprFuel e ≤ max (exprFuel e) (exprsFuel es)
  omega

/-- `exprsFuel` of a cons-list tail. -/
theorem exprsFuel_tail_le {e : RawExpr} {es : List RawExpr} :
    exprsFuel es ≤ exprsFuel (e :: es) := by
  show exprsFuel es ≤ max (exprFuel e) (exprsFuel es)
  omega

/-- `elabBranchesWith` accepts a `Branches` erasure — every branch types at
    `T` under its payload-extended context. -/
theorem elabBranchesWith_of_Branches (f : Nat)
    (g : (Γ' : List CoreTy) → RawExpr → Elab S Γ')
    (hg : ∀ {Γ' : List CoreTy} {T' : CoreTy} (e : CoreExpr S Γ' T'),
      exprFuel e.erase < f → ∃ e', g Γ' e.erase = .ok ⟨T', e'⟩)
    {Γ : List CoreTy} {T : CoreTy} :
    ∀ {ts : List CoreTy} (bs : Branches S Γ ts T), exprsFuel bs.erase < f →
      ∃ bs' : Branches S Γ ts T,
        elabBranchesWith g Γ T ts bs.erase = .ok bs'
  | _, .nil, _ => ⟨.nil, rfl⟩
  | _, .cons b bs, hf => by
      rename_i A ts'
      have h' : max (exprFuel b.erase) (exprsFuel bs.erase) < f := hf
      obtain ⟨e', he'⟩ := hg b (by omega)
      obtain ⟨rest, hrest⟩ := elabBranchesWith_of_Branches f g hg bs (by omega)
      refine ⟨.cons e' rest, ?_⟩
      show elabBranchesWith g Γ _ (_ :: _) (b.erase :: bs.erase) = .ok _
      dsimp only [elabBranchesWith]
      rw [he']
      simp only [ok_bind]
      rw [hrest]
      simp only [ok_bind]
      rfl

/-- `elabFieldsWith` accepts a `Fields` erasure at its own schema,
    returning exactly the field list it was called on. -/
theorem elabFieldsWith_of_Fields {Γ : List CoreTy} (f : Nat)
    (g : RawExpr → Elab S Γ)
    (hg : ∀ {T' : CoreTy} (e : CoreExpr S Γ T'), exprFuel e.erase < f →
      ∃ e', g e.erase = .ok ⟨T', e'⟩) :
    ∀ {fs : List (String × CoreTy)} (xs : Fields S Γ fs),
      exprsFuel xs.erase < f →
      ∃ xs' : Fields S Γ fs, ∃ hk',
        elabFieldsWith g (fs.map Prod.fst) xs.erase = .ok ⟨fs, xs', hk'⟩
  | _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | _, .cons k x xs, hf => by
      rename_i fs'
      have h' : max (exprFuel x.erase) (exprsFuel xs.erase) < f := hf
      obtain ⟨e', he'⟩ := hg x (by omega)
      obtain ⟨xs', hkf, hrest⟩ := elabFieldsWith_of_Fields f g hg xs (by omega)
      refine ⟨.cons k e' xs', rfl, ?_⟩
      show elabFieldsWith g (((_, _) :: fs').map Prod.fst)
          (x.erase :: xs.erase) = .ok _
      dsimp only [elabFieldsWith, List.map_cons]
      rw [he', hrest]
      simp only [ok_bind]
      rfl

/-- The completeness half of `elabE` (06 §19 `→`, expression layer):
    every typed `CoreExpr` elaborates at its own type once the fuel covers
    its `exprFuel` decode depth. -/
theorem elabE_of_coreExpr : ∀ (n : Nat) {S : Sig} {Γ : List CoreTy}
    {T : CoreTy} (e : CoreExpr S Γ T), exprFuel e.erase < n →
    ∃ e' : CoreExpr S Γ T, elabE n S Γ e.erase = .ok ⟨T, e'⟩
  | 0, _, _, _, _, h => (Nat.not_lt_zero _ h).elim
  | f + 1, S, Γ, T, e, h => by
    have ih : ∀ {Γ' : List CoreTy} {T' : CoreTy} (e' : CoreExpr S Γ' T'),
        exprFuel e'.erase < f →
        ∃ e'', elabE f S Γ' e'.erase = .ok ⟨T', e''⟩ :=
      fun e' hf => elabE_of_coreExpr f e' hf
    cases e with
    | lit v =>
      dsimp only [CoreExpr.erase, elabE]
      rw [erase_toCore]
      exact ⟨.lit v, rfl⟩
    | var i hv =>
      dsimp only [CoreExpr.erase, elabE]
      have hni : ¬ ((i : Int) < 0) := by omega
      rw [if_neg hni]
      have hti : ((i : Int).toNat) = i := rfl
      rw [hti]
      split
      · rename_i T' h'
        rw [h'] at hv
        have := Option.some.inj hv; subst this
        exact ⟨.var i h', rfl⟩
      · rename_i h'
        rw [h'] at hv; exact Option.noConfusion hv
    | letE a b =>
      have h' : max (exprFuel a.erase) (exprFuel b.erase) + 1 < f + 1 := h
      obtain ⟨ea', ha'⟩ := ih a (by omega)
      obtain ⟨eb', hb'⟩ := ih b (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [ha']
      simp only [ok_bind]
      rw [hb']
      simp only [ok_bind, pure_ok]
      exact ⟨.letE ea' eb', rfl⟩
    | ifE c th el =>
      have h' : max (exprFuel c.erase)
          (max (exprFuel th.erase) (exprFuel el.erase)) + 1 < f + 1 := h
      obtain ⟨ec', hc'⟩ := ih c (by omega)
      obtain ⟨et', ht'⟩ := ih th (by omega)
      obtain ⟨ee', he'⟩ := ih el (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [hc', ht', he']
      simp only [ok_bind]
      exact ⟨_, rfl⟩
    | pairE a b =>
      have h' : max (exprFuel a.erase) (exprFuel b.erase) + 1 < f + 1 := h
      obtain ⟨ea', ha'⟩ := ih a (by omega)
      obtain ⟨eb', hb'⟩ := ih b (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [ha', hb']
      simp only [ok_bind, pure_ok]
      exact ⟨.pairE ea' eb', rfl⟩
    | fstE a =>
      have h' : exprFuel a.erase + 1 < f + 1 := h
      obtain ⟨ea', ha'⟩ := ih a (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [ha']
      simp only [ok_bind, pure_ok]
      exact ⟨.fstE ea', rfl⟩
    | sndE a =>
      have h' : exprFuel a.erase + 1 < f + 1 := h
      obtain ⟨ea', ha'⟩ := ih a (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [ha']
      simp only [ok_bind, pure_ok]
      exact ⟨.sndE ea', rfl⟩
    | injE ts i hv a =>
      have h' : max (tysFuel ts + 1) (exprFuel a.erase + 1) < f + 1 := h
      obtain ⟨ea', ha'⟩ := ih a (by omega)
      dsimp only [CoreExpr.erase, elabE]
      have hni : ¬ ((i : Int) < 0) := by omega
      rw [if_neg hni]
      have hti : ((i : Int).toNat) = i := rfl
      rw [hti]
      split
      · rename_i h'
        rw [h'] at hv; exact Option.noConfusion hv
      · rename_i A' h'
        rw [h'] at hv
        have := Option.some.inj hv; subst this
        rw [ha']
        simp only [ok_bind]
        exact ⟨_, rfl⟩
    | matchSum s bs hne =>
      obtain ⟨es', hs'⟩ := ih s (by
        have h' : max (exprFuel s.erase + 1) (exprsFuel bs.erase + 1)
            < f + 1 := h
        omega)
      cases bs with
      | nil => exact (hne rfl).elim
      | cons b bs' =>
        have h' : max (exprFuel s.erase + 1)
            (max (exprFuel b.erase) (exprsFuel bs'.erase) + 1) < f + 1 := h
        obtain ⟨eb', heb'⟩ := ih b (by omega)
        obtain ⟨rest', hrest'⟩ := elabBranchesWith_of_Branches f (elabE f S)
          (fun e' hf => ih e' hf) bs' (by omega)
        dsimp only [CoreExpr.erase, Branches.erase, elabE]
        rw [hs']
        simp only [ok_bind]
        rw [if_pos (Branches_erase_length bs')]
        rw [heb']
        simp only [ok_bind]
        rw [hrest']
        simp only [ok_bind]
        exact ⟨_, rfl⟩
    | recordE xs hk =>
      have h' : max 1 (exprsFuel xs.erase + 1) < f + 1 := h
      obtain ⟨xs', hkf, hfs'⟩ := elabFieldsWith_of_Fields f (elabE f S Γ)
        (fun e' hf => ih e' hf) xs (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [if_neg (fun hne => hne (by
        rw [List.length_map, Fields_erase_length]))]
      rw [dif_pos hk]
      rw [hfs']
      simp only [ok_bind, pure_ok]
      exact ⟨.recordE xs' hk, rfl⟩
    | fieldE i k hv r =>
      have h' : exprFuel r.erase + 1 < f + 1 := h
      obtain ⟨er', hr'⟩ := ih r (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [hr']
      simp only [ok_bind]
      have hni : ¬ ((i : Int) < 0) := by omega
      rw [if_neg hni]
      have hti : ((i : Int).toNat) = i := rfl
      rw [hti]
      split
      · rename_i k' A' h'
        rw [h'] at hv
        have := Prod.mk.inj (Option.some.inj hv)
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨_, rfl⟩
      · rename_i h'
        rw [h'] at hv; exact Option.noConfusion hv
    | nilE =>
      dsimp only [CoreExpr.erase, elabE]
      exact ⟨.nilE, rfl⟩
    | consE hd tl =>
      have h' : max (exprFuel hd.erase) (exprFuel tl.erase) + 1 < f + 1 := h
      obtain ⟨eh', hh'⟩ := ih hd (by omega)
      obtain ⟨et', ht'⟩ := ih tl (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [hh', ht']
      simp only [ok_bind]
      exact ⟨_, rfl⟩
    | foldList l init body =>
      have h' : max (exprFuel l.erase)
          (max (exprFuel init.erase) (exprFuel body.erase)) + 1 < f + 1 := h
      obtain ⟨el', hl'⟩ := ih l (by omega)
      obtain ⟨ei', hi'⟩ := ih init (by omega)
      obtain ⟨eb', hb'⟩ := ih body (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [hl', hi']
      simp only [ok_bind]
      rw [hb']
      simp only [ok_bind]
      exact ⟨_, rfl⟩
    | boundedFix init limit stop step =>
      have h' : max (exprFuel init.erase) (max (exprFuel limit.erase)
          (max (exprFuel stop.erase) (exprFuel step.erase))) + 1 < f + 1 := h
      obtain ⟨ei', hi'⟩ := ih init (by omega)
      obtain ⟨el', hl'⟩ := ih limit (by omega)
      obtain ⟨es', hs'⟩ := ih stop (by omega)
      obtain ⟨ep', hp'⟩ := ih step (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [hi', hl']
      simp only [ok_bind]
      rw [hs']
      simp only [ok_bind]
      rw [hp']
      simp only [ok_bind]
      exact ⟨_, rfl⟩
    | prim op args =>
      have h' : max 1 (exprsFuel args.erase + 1) < f + 1 := h
      obtain ⟨xs', hxs', hmap⟩ := elabListWith_of_Args f (elabE f S Γ)
        (fun e' hf => ih e' hf) args (by omega)
      dsimp only [CoreExpr.erase, elabE]
      rw [primOfString_primName, hxs']
      simp only [ok_bind]
      obtain ⟨a, ha⟩ := toArgs_of_mapFst xs' hmap
      rw [ha]
      exact ⟨.prim op a, rfl⟩
    | call fr args =>
      cases fr with
      | «local» i fs hf' =>
        have h' : exprsFuel args.erase + 1 < f + 1 := h
        obtain ⟨xs', hxs', hmap⟩ := elabListWith_of_Args f (elabE f S Γ)
          (fun e' hf => ih e' hf) args (by omega)
        dsimp only [CoreExpr.erase, elabE]
        have hni : ¬ ((i : Int) < 0) := by omega
        rw [if_neg hni]
        have hti : ((i : Int).toNat) = i := rfl
        rw [hti]
        split
        · rename_i h'
          rw [h'] at hf'; exact Option.noConfusion hf'
        · rename_i fs' h'
          rw [h'] at hf'
          have := Option.some.inj hf'; subst this
          rw [hxs']
          simp only [ok_bind]
          obtain ⟨a, ha⟩ := toArgs_of_mapFst xs' hmap
          rw [ha]
          exact ⟨_, rfl⟩
      | external r x hf' =>
        have h' : exprsFuel args.erase + 1 < f + 1 := h
        obtain ⟨xs', hxs', hmap⟩ := elabListWith_of_Args f (elabE f S Γ)
          (fun e' hf => ih e' hf) args (by omega)
        dsimp only [CoreExpr.erase, elabE]
        split
        · rename_i h'
          rw [h'] at hf'; exact Option.noConfusion hf'
        · rename_i x' h'
          rw [h'] at hf'
          have := Option.some.inj hf'; subst this
          rw [hxs']
          simp only [ok_bind]
          obtain ⟨a, ha⟩ := toArgs_of_mapFst xs' hmap
          rw [ha]
          exact ⟨_, rfl⟩
    | raise r hp p =>
      have h' : max 1 (max (exprFuel p.erase + 1) (tyFuel _ + 1)) < f + 1 := h
      obtain ⟨ep', hp'⟩ := ih p (by omega)
      dsimp only [CoreExpr.erase, elabE]
      split
      · rename_i h'
        rw [h'] at hp; exact Option.noConfusion hp
      · rename_i P' h'
        rw [h'] at hp
        have := Option.some.inj hp; subst this
        rw [hp']
        simp only [ok_bind]
        exact ⟨_, rfl⟩
    | handle r hh body hd =>
      have h' : max 1 (max (exprFuel body.erase + 1)
          (exprFuel hd.erase + 1)) < f + 1 := h
      obtain ⟨eb', hb'⟩ := ih body (by omega)
      obtain ⟨eh', hh'⟩ := ih hd (by omega)
      dsimp only [CoreExpr.erase, elabE]
      split
      · rename_i h'
        rw [h'] at hh; exact Option.noConfusion hh
      · rename_i P' h'
        rw [h'] at hh
        have := Option.some.inj hh; subst this
        rw [hb', hh']
        simp only [ok_bind]
        exact ⟨_, rfl⟩

/-- `hasTy` accepts a typed expression's erasure at its own type. -/
theorem hasTy_of_coreExpr {p : RawProg} {Γ : List CoreTy} {T : CoreTy}
    (e : CoreExpr (sigOf p) Γ T) (fuel : Int)
    (hf : (exprFuel e.erase : Int) ≤ fuel) :
    CfgAt.hasTy fuel p Γ e.erase T = true := by
  unfold CfgAt.hasTy
  obtain ⟨e', he'⟩ := elabE_of_coreExpr (fuelN fuel) e (by
    unfold fuelN
    split
    · omega
    · have h2 : ((fuel.toNat : Int)) = fuel := Int.toNat_of_nonneg (by omega)
      omega)
  rw [he']
  exact CoreTy.beq_refl T

end Rcic.Scm.ElabComplete
