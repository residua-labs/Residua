import rcic.RcicWasmNormTy
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm

private theorem map_some_inv {α β} {o : Option α} {g : α → β} {b : β}
    (h : o.map g = some b) : ∃ a, o = some a ∧ g a = b := by
  cases o with
  | none => exact absurd h (by simp)
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

private theorem bind_some_inv {α β} {o : Option α} {g : α → Option β} {b : β}
    (h : o.bind g = some b) : ∃ a, o = some a ∧ g a = some b := by
  cases o with
  | none => exact absurd h (by simp)
  | some a => exact ⟨a, rfl, h⟩

/-- `body.drop n` starts with `body[n]` when it exists. -/
private theorem drop_eq_cons_of_get? {α : Type _} {l : List α} {n : Nat}
    {a : α} (h : l.get? n = some a) : l.drop n = a :: l.drop (n + 1) := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.get?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    | succ n =>
      simp only [List.get?_cons_succ] at h
      simp only [List.drop_succ_cons]
      exact ih h

/-- The validator run over `k ≥ 1` steps of a `drop` suffix decomposes into
the step at `j` plus the rest. -/
private theorem vrun_drop_take {C : NormVCtx} {body : List NormInstr}
    {s s' : NormVSt} {j k : Nat} {i : NormInstr}
    (hi : body.get? j = some i) (hk : 0 < k)
    (h : normVRun C s ((body.drop j).take k) = some s') :
    ∃ s₁, normVStep C i s = some s₁ ∧
      normVRun C s₁ ((body.drop (j + 1)).take (k - 1)) = some s' := by
  rw [drop_eq_cons_of_get? hi] at h
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [← hsub, List.take_succ_cons] at h
  obtain ⟨s₁, hs, hr⟩ := normVRun_cons_inv _ _ _ _ _ h
  exact ⟨s₁, hs, hr⟩

/-- One `normElseEnd.go` step (the `Nat.brecOn` encoding computes). -/
private theorem go_succ (body : List NormInstr) (fuel j depth : Nat)
    (elsePc : Option Nat) :
    normElseEnd.go body (fuel + 1) j depth elsePc =
      (match body.get? j with
      | none => none
      | some .block | some .loop | some .ifE =>
          normElseEnd.go body fuel (j + 1) (depth + 1) elsePc
      | some .endI =>
          if depth = 0 then some (elsePc, j + 1)
          else normElseEnd.go body fuel (j + 1) (depth - 1) elsePc
      | some .elseE =>
          if depth = 0 then normElseEnd.go body fuel (j + 1) depth
            (elsePc.orElse (fun _ => some j))
          else normElseEnd.go body fuel (j + 1) depth elsePc
      | _ => normElseEnd.go body fuel (j + 1) depth elsePc) := rfl

/-- `normVBrk` keeps the frame stack's tail and marks its head
unreachable. -/
private theorem normVBrk_cs {s : NormVSt} {lrt : Option NormTy} {s' : NormVSt}
    (h : normVBrk s lrt = some s') :
    ∃ f rest, s.cs = f :: rest ∧
      s'.cs = ⟨f.tag, f.rt, f.entry, true⟩ :: rest := by
  unfold normVBrk at h
  split at h
  · exact Option.noConfusion h
  · rename_i f rest hcs
    obtain ⟨os₁, hp1, hb1⟩ := bind_some_inv h
    simp only [Option.some.injEq] at hb1
    subst hb1
    exact ⟨f, rest, hcs, rfl⟩

/-- `normVBr` finds the target at depth `n` and delegates to `normVBrk`. -/
private theorem normVBr_inv {s : NormVSt} {n : Nat} {s' : NormVSt}
    (h : normVBr s n = some s') :
    ∃ tgt rest', s.cs.drop n = tgt :: rest' ∧
      normVBrk s (if tgt.tag = .lp then none else tgt.rt) = some s' := by
  unfold normVBr at h
  split at h
  · exact Option.noConfusion h
  · rename_i tgt rest' hdrop
    dsimp only at h
    split at h
    · rename_i hok
      exact ⟨tgt, rest', hdrop, h⟩
    · exact Option.noConfusion h

/-- `normVBrIf` finds the target, pops the condition, and leaves `cs`
    unchanged on success. -/
private theorem normVBrIf_cs {s : NormVSt} {n : Nat} {s' : NormVSt}
    (h : normVBrIf s n = some s') : s'.cs = s.cs := by
  unfold normVBrIf at h
  split at h
  · exact Option.noConfusion h
  · rename_i tgt ts hdrop
    dsimp only at h
    obtain ⟨o1, hp1, hb1⟩ := bind_some_inv h
    obtain ⟨o2, hp2, hb2⟩ := bind_some_inv hb1
    split at hb2
    · simp only [Option.some.injEq] at hb2
      subst hb2; rfl
    · exact Option.noConfusion hb2

/-- The frame-stack effect of a successful `normVStep`: push (openers),
pop (`endI`), head-mutate (`elseE`/br-family), or unchanged. -/
theorem normVStep_cs_cases {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    (h : normVStep C i s = some s') :
    (∃ f, s'.cs = f :: s.cs) ∨
    (∃ f rest, s.cs = f :: rest ∧ s'.cs = rest ∧ f.tag ≠ .fn) ∨
    (∃ f f' rest, s.cs = f :: rest ∧ s'.cs = f' :: rest ∧
        f'.rt = f.rt ∧ f'.entry = f.entry ∧
        (f.tag = .fn → f' = ⟨f.tag, f.rt, f.entry, true⟩)) ∨
    s'.cs = s.cs := by
  cases i with
  | block =>
    simp only [normVStep, Option.some.injEq] at h
    subst h; exact Or.inl ⟨_, rfl⟩
  | loop =>
    simp only [normVStep, Option.some.injEq] at h
    subst h; exact Or.inl ⟨_, rfl⟩
  | ifE =>
    simp only [normVStep] at h
    obtain ⟨o, ho, hs⟩ := map_some_inv h
    subst hs; exact Or.inl ⟨_, rfl⟩
  | elseE =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      split at h
      · rename_i htag
        obtain ⟨o, ho, hs⟩ := map_some_inv h
        subst hs
        refine Or.inr (Or.inr (Or.inl
          ⟨f, _, rest, hcs, rfl, rfl, rfl, fun hf => ?_⟩))
        rw [htag] at hf; exact NormTTag.noConfusion hf
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | endI =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      split at h
      · exact Option.noConfusion h
      · rename_i htag
        obtain ⟨o, ho, hs⟩ := map_some_inv h
        subst hs
        exact Or.inr (Or.inl ⟨f, rest, hcs, rfl, htag⟩)
    · exact Option.noConfusion h
  | br n =>
    simp only [normVStep] at h
    obtain ⟨tgt, ts, hdrop, hbrk⟩ := normVBr_inv h
    obtain ⟨f, rest, hcs, hf'⟩ := normVBrk_cs hbrk
    exact Or.inr (Or.inr (Or.inl
      ⟨f, ⟨f.tag, f.rt, f.entry, true⟩, rest, hcs, hf', rfl, rfl,
        fun _ => rfl⟩))
  | brIf n =>
    simp only [normVStep] at h
    exact Or.inr (Or.inr (Or.inr (normVBrIf_cs h)))
  | call f =>
    simp only [normVStep] at h
    split at h
    · exact Option.noConfusion h
    · rename_i x sig hf
      obtain ⟨o, ho, hs⟩ := map_some_inv h
      subst hs; exact Or.inr (Or.inr (Or.inr rfl))
  | «return» =>
    simp only [normVStep] at h
    obtain ⟨f, rest, hcs, hf'⟩ := normVBrk_cs h
    exact Or.inr (Or.inr (Or.inl
      ⟨f, ⟨f.tag, f.rt, f.entry, true⟩, rest, hcs, hf', rfl, rfl,
        fun _ => rfl⟩))
  | drop =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      obtain ⟨o, ho, hs⟩ := map_some_inv h
      subst hs; exact Or.inr (Or.inr (Or.inr rfl))
    · exact Option.noConfusion h
  | select =>
    simp only [normVStep] at h
    obtain ⟨o1, hp1, hb1⟩ := bind_some_inv h
    split at hb1
    · rename_i x f rest hcs
      obtain ⟨a, ha, hb2⟩ := bind_some_inv hb1
      split at hb2
      · rename_i ht
        simp only [Option.some.injEq] at hb2
        subst hb2
        exact Or.inr (Or.inr (Or.inr rfl))
      · rename_i ht
        obtain ⟨o3, ho3, hb3⟩ := map_some_inv hb2
        subst hb3
        exact Or.inr (Or.inr (Or.inr rfl))
    · exact Option.noConfusion hb1
  | localGet i =>
    simp only [normVStep] at h
    obtain ⟨o, ho, hs⟩ := map_some_inv h
    subst hs; exact Or.inr (Or.inr (Or.inr rfl))
  | localSet i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; exact Or.inr (Or.inr (Or.inr rfl))
  | localTee i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; exact Or.inr (Or.inr (Or.inr rfl))
  | _ =>
    simp only [normVStep] at h
    obtain ⟨sig, hsig, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; exact Or.inr (Or.inr (Or.inr rfl))

/-- A successful `normVStep` changes the frame stack's length by at most
one (a corollary of the classification). -/
theorem normVStep_cs_ge {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    (h : normVStep C i s = some s') :
    s'.cs.length ≤ s.cs.length + 1 := by
  obtain h1 | h2 | h3 | h4 := normVStep_cs_cases h
  · obtain ⟨f, hf⟩ := h1
    simp only [hf, List.length_cons]; omega
  · obtain ⟨f, rest, hf, hf'⟩ := h2
    simp only [hf, hf', List.length_cons]; omega
  · obtain ⟨f, f', rest, hf, hf'⟩ := h3
    simp only [hf, hf', List.length_cons]; omega
  · rw [h4]; omega

/-- The exact cs-length delta per instruction: openers push (+1), `endI`
pops (−1, via the `+1` carried on the left), everything else preserves. -/
theorem normVStep_cs_len {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    (h : normVStep C i s = some s') :
    s'.cs.length +
      (match i with | .endI => 1 | _ => 0) =
    s.cs.length +
      (match i with | .block | .loop | .ifE => 1 | _ => 0) := by
  cases i with
  | block =>
    simp only [normVStep, Option.some.injEq] at h
    subst h; rfl
  | loop =>
    simp only [normVStep, Option.some.injEq] at h
    subst h; rfl
  | ifE =>
    simp only [normVStep] at h
    obtain ⟨o, ho, hs⟩ := map_some_inv h
    subst hs; rfl
  | elseE =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      split at h
      · rename_i htag
        obtain ⟨o, ho, hs⟩ := map_some_inv h
        subst hs; simp [hcs]
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | endI =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      split at h
      · exact Option.noConfusion h
      · rename_i htag
        obtain ⟨o, ho, hs⟩ := map_some_inv h
        subst hs; simp [hcs]
    · exact Option.noConfusion h
  | br n =>
    simp only [normVStep] at h
    obtain ⟨tgt, ts, hdrop, hbrk⟩ := normVBr_inv h
    obtain ⟨f, rest, hcs, hf'⟩ := normVBrk_cs hbrk
    simp [hcs, hf']
  | brIf n =>
    simp only [normVStep] at h
    rw [normVBrIf_cs h]
  | call f =>
    simp only [normVStep] at h
    split at h
    · exact Option.noConfusion h
    · rename_i x sig hf
      obtain ⟨o, ho, hs⟩ := map_some_inv h
      subst hs; rfl
  | «return» =>
    simp only [normVStep] at h
    obtain ⟨f, rest, hcs, hf'⟩ := normVBrk_cs h
    simp [hcs, hf']
  | drop =>
    simp only [normVStep] at h
    split at h
    · rename_i x f rest hcs
      obtain ⟨o, ho, hs⟩ := map_some_inv h
      subst hs; rfl
    · exact Option.noConfusion h
  | select =>
    simp only [normVStep] at h
    obtain ⟨o1, hp1, hb1⟩ := bind_some_inv h
    split at hb1
    · rename_i x f rest hcs
      obtain ⟨a, ha, hb2⟩ := bind_some_inv hb1
      split at hb2
      · rename_i ht
        simp only [Option.some.injEq] at hb2
        subst hb2; rfl
      · rename_i ht
        obtain ⟨o3, ho3, hb3⟩ := map_some_inv hb2
        subst hb3; rfl
    · exact Option.noConfusion hb1
  | localGet i =>
    simp only [normVStep] at h
    obtain ⟨o, ho, hs⟩ := map_some_inv h
    subst hs; rfl
  | localSet i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; rfl
  | localTee i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; rfl
  | _ =>
    simp only [normVStep] at h
    obtain ⟨sig, hsig, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'
    subst hs; rfl

theorem getLast?_cons_of_ne {α : Type _} {f : α} {rest : List α}
    (h : rest ≠ []) : (f :: rest).getLast? = rest.getLast? := by
  cases rest with
  | nil => exact absurd rfl h
  | cons g tl => rfl

theorem ne_nil_of_getLast? {α : Type _} {cs : List α} {f : α}
    (h : cs.getLast? = some f) : cs ≠ [] := by
  intro hcon; rw [hcon] at h; simp at h

theorem lt_of_get? {α : Type _} {l : List α} {j : Nat} {a : α}
    (h : l.get? j = some a) : j < l.length :=
  (List.get?_eq_some.1 h).1


/-- The control-map scan (`normElseEnd.go`) finds a matching `endI`
whenever the validator's walk over the same stretch succeeds with the
frame-stack shrinking back to `base`. Invariant: at scan position `j`
the validator frame-stack length is `base + 1 + depth` — every opener
pushes, every `endI` pops, everything else preserves length — so a
successful run that ends at `≤ base` must have passed a depth-0 `endI`,
which is exactly where the scan returns. -/
theorem go_finds_aux {body : List NormInstr} {base : Nat} :
    ∀ {fuel j depth : Nat} {el : Option Nat} {C : NormVCtx} {s sf : NormVSt},
    (body.drop j).length ≤ fuel →
    normVRun C s (body.drop j) = some sf →
    s.cs.length = base + 1 + depth →
    sf.cs.length ≤ base →
    (normElseEnd.go body fuel j depth el).isSome := by
  intro fuel
  induction fuel with
  | zero =>
    intro j depth el C s sf hfuel hrun hlen hfin
    have hnil : body.drop j = [] := by
      have h0 : (body.drop j).length = 0 := by
        have := hfuel; simp only [List.length_drop] at this; omega
      exact List.length_eq_zero.1 h0
    rw [hnil, normVRun_nil] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun; omega
  | succ fuel ih =>
    intro j depth el C s sf hfuel hrun hlen hfin
    show ((match body.get? j with
      | none => none
      | some .block => normElseEnd.go body fuel (j + 1) (depth + 1) el
      | some .loop => normElseEnd.go body fuel (j + 1) (depth + 1) el
      | some .ifE => normElseEnd.go body fuel (j + 1) (depth + 1) el
      | some .endI =>
          if depth = 0 then some (el, j + 1)
          else normElseEnd.go body fuel (j + 1) (depth - 1) el
      | some .elseE =>
          if depth = 0 then
            normElseEnd.go body fuel (j + 1) depth
              (Option.orElse el (fun _ => some j))
          else normElseEnd.go body fuel (j + 1) depth el
      | _ => normElseEnd.go body fuel (j + 1) depth el).isSome)
    cases hg : body.get? j with
    | none =>
      exfalso
      have hnil : body.drop j = [] :=
        List.drop_eq_nil_of_le (List.get?_eq_none.1 hg)
      rw [hnil, normVRun_nil] at hrun
      simp only [Option.some.injEq] at hrun
      subst hrun; omega
    | some i =>
      rw [drop_eq_cons_of_get? hg, normVRun_cons] at hrun
      obtain ⟨s₁, hstep, hrun'⟩ := bind_some_inv hrun
      have hdelta := normVStep_cs_len hstep
      have hfl : (body.drop (j + 1)).length ≤ fuel := by
        have := hfuel
        rw [drop_eq_cons_of_get? hg, List.length_cons] at this
        omega
      cases i with
      | block =>
        have h1 : s₁.cs.length = s.cs.length + 1 := hdelta
        exact ih hfl hrun' (by omega) hfin
      | loop =>
        have h1 : s₁.cs.length = s.cs.length + 1 := hdelta
        exact ih hfl hrun' (by omega) hfin
      | ifE =>
        have h1 : s₁.cs.length = s.cs.length + 1 := hdelta
        exact ih hfl hrun' (by omega) hfin
      | endI =>
        cases depth with
        | zero => rfl
        | succ d =>
          have h1 : s₁.cs.length + 1 = s.cs.length := hdelta
          exact ih hfl hrun' (by omega) hfin
      | elseE =>
        cases depth with
        | zero =>
          have h1 : s₁.cs.length = s.cs.length := hdelta
          exact ih hfl hrun' (by omega) hfin
        | succ d =>
          have h1 : s₁.cs.length = s.cs.length := hdelta
          exact ih hfl hrun' (by omega) hfin
      | _ =>
        have h1 : s₁.cs.length = s.cs.length := hdelta
        exact ih hfl hrun' (by omega) hfin

/-- A successfully validated structured opener has a matching `endI` (and
possibly `elseE`) in the body: the scan always terminates. -/
theorem normElseEnd_of_open {C : NormVCtx} {body : List NormInstr} {pc : Nat}
    {i : NormInstr} {s s' sf : NormVSt}
    (hstruct : i = .block ∨ i = .loop ∨ i = .ifE)
    (hstep : normVStep C i s = some s')
    (hrun : normVRun C s' (body.drop (pc + 1)) = some sf)
    (hfin : sf.cs.length ≤ s.cs.length) :
    (normElseEnd body pc).isSome := by
  have h1 : s'.cs.length = s.cs.length + 1 := by
    obtain rfl | rfl | rfl := hstruct
    · exact normVStep_cs_len hstep
    · exact normVStep_cs_len hstep
    · exact normVStep_cs_len hstep
  show (normElseEnd.go body (body.length - pc) (pc + 1) 0 none).isSome
  apply go_finds_aux (base := s.cs.length)
  · rw [List.length_drop]; omega
  · exact hrun
  · omega
  · exact hfin

/-! ## Live-pops: validated pops under all-live frames are real head pops -/

/-- A live (`un = false`) pop is a real head pop. -/
theorem normTckPop_live {os : List NormTy} {base : Nat} {t : NormTy}
    {os' : List NormTy} (h : normTckPop os base false t = some os') :
    os = t :: os' := by
  unfold normTckPop at h
  split at h
  · rename_i hlen
    split at h
    · rename_i t' rest
      split at h
      · rename_i htt
        simp only [Option.some.injEq] at h; subst h
        subst htt; rfl
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · simp at h

/-- Frame-bounded live pop. -/
theorem normVPop_live {os : List NormTy} {cs : List NormTFrame} {t : NormTy}
    {os' : List NormTy} (hlive : ∀ f ∈ cs, f.un = false)
    (h : normVPop os cs t = some os') : os = t :: os' := by
  unfold normVPop at h
  split at h
  · rename_i f rest
    have hf : f.un = false := hlive f (List.mem_cons_self ..)
    rw [hf] at h
    exact normTckPop_live h
  · exact Option.noConfusion h

/-- List-order live pops strip the popped prefix. -/
theorem normVPops_live {os : List NormTy} {cs : List NormTFrame}
    (hlive : ∀ f ∈ cs, f.un = false) :
    ∀ {ps os'}, normVPops os cs ps = some os' → os = ps ++ os' := by
  intro ps
  induction ps generalizing os with
  | nil =>
    intro os' h
    simp [normVPops] at h
    subst h; rfl
  | cons t ts ih =>
    intro os' h
    simp [normVPops] at h
    obtain ⟨o1, hp, hrest⟩ := bind_some_inv h
    have h1 := normVPop_live hlive hp
    have h2 := ih hrest
    rw [h1, h2]; rfl

/-- Sig application on live frames: the stack is `ps ++ rest` and the
result is `rs ++ rest`. -/
theorem normVApply_live {os : List NormTy} {cs : List NormTFrame}
    {ps rs os' : List NormTy} (hlive : ∀ f ∈ cs, f.un = false)
    (h : normVApply os cs ps rs = some os') :
    ∃ rest, os = ps ++ rest ∧ os' = rs ++ rest := by
  unfold normVApply at h
  obtain ⟨o1, hp, hm⟩ := map_some_inv h
  rw [normVPops_live hlive hp]
  exact ⟨o1, rfl, hm.symm⟩

/-- Live any-pop returns the head type. -/
theorem normTckAny_live {os : List NormTy} {base : Nat}
    {r : Option NormTy × List NormTy}
    (h : normTckAny os base false = some r) :
    ∃ t, r.1 = some t ∧ os = t :: r.2 := by
  unfold normTckAny at h
  split at h
  · rename_i hlen
    split at h
    · rename_i t' rest
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨t', rfl, rfl⟩
    · exact Option.noConfusion h
  · simp at h

/-! ## Local updates -/

theorem localsSet_go_succ (v : NormVal) (fuel : Nat) (ls : List NormVal)
    (i : Nat) :
    normLocalsSet.go v (fuel + 1) ls i =
      match ls, i with
      | [], _ => none
      | _ :: tl, 0 => some (v :: tl)
      | h :: tl, i + 1 => (normLocalsSet.go v fuel tl i).map (h :: ·) := rfl

/-- In-bounds `local.set`/`local.tee` always succeed (the machine walks
`i` positions; the fuel of `ls.length` covers any `i < ls.length`). -/
theorem normLocalsSet_of_lt {ls : List NormVal} {i : Nat} {v : NormVal}
    (h : i < ls.length) :
    normLocalsSet ls i v = some (ls.take i ++ v :: ls.drop (i + 1)) := by
  induction ls generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      show normLocalsSet (hd :: tl) 0 v = some (v :: tl)
      rfl
    | succ i =>
      have hi : i < tl.length := Nat.lt_of_succ_lt_succ h
      show (normLocalsSet tl i v).map (hd :: ·) =
        some (hd :: tl.take i ++ v :: tl.drop (i + 1))
      rw [ih hi]; rfl

/-! ## The implicit `fn` bottom frame -/

/-- A successful `normVStep` preserves the implicit `fn` bottom frame's
identity up to its `un` flag (a `fn` frame is only ever `normVBrk`-marked). -/
theorem normVStep_bottom_shape {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    {rt : Option NormTy} {en : List NormTy} {un : Bool}
    (h : normVStep C i s = some s')
    (hb : s.cs.getLast? = some ⟨.fn, rt, en, un⟩) :
    ∃ un', s'.cs.getLast? = some ⟨.fn, rt, en, un'⟩ := by
  obtain h1 | h2 | h3 | h4 := normVStep_cs_cases h
  · obtain ⟨f, hf⟩ := h1
    refine ⟨un, ?_⟩
    rw [hf, getLast?_cons_of_ne (ne_nil_of_getLast? hb)]
    exact hb
  · obtain ⟨f, rest, hf, hf', htag⟩ := h2
    cases he : rest with
    | nil =>
      rw [he] at hf hf'
      rw [hf] at hb
      have : (f :: []).getLast? = some f := rfl
      rw [this] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact absurd rfl htag
    | cons g tl =>
      rw [he] at hf hf'
      rw [hf] at hb
      rw [getLast?_cons_of_ne (by simp)] at hb
      rw [hf']; exact ⟨un, hb⟩
  · obtain ⟨f, f', rest, hf, hf', hrt, hen, hfn⟩ := h3
    cases he : rest with
    | nil =>
      rw [he] at hf hf'
      rw [hf] at hb
      have hgl : (f :: []).getLast? = some f := rfl
      rw [hgl] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      have hf'' := hfn rfl
      refine ⟨true, ?_⟩
      rw [hf']
      have : (f' :: []).getLast? = some f' := rfl
      rw [this, hf'']
    | cons g tl =>
      rw [he] at hf hf'
      rw [hf] at hb
      rw [getLast?_cons_of_ne (by simp)] at hb
      refine ⟨un, ?_⟩
      rw [hf', getLast?_cons_of_ne (by simp)]
      exact hb
  · exact ⟨un, by rw [h4]; exact hb⟩

/-- The `fn` bottom frame persists through a whole validating run. -/
theorem normVRun_fn_frame {C : NormVCtx} {body : List NormInstr}
    {s s' : NormVSt} {rt : Option NormTy} {en : List NormTy} {un : Bool}
    (h : normVRun C s body = some s')
    (hb : s.cs.getLast? = some ⟨.fn, rt, en, un⟩) :
    ∃ un', s'.cs.getLast? = some ⟨.fn, rt, en, un'⟩ := by
  induction body generalizing s un with
  | nil =>
    rw [normVRun_nil] at h
    simp only [Option.some.injEq] at h
    subst h; exact ⟨un, hb⟩
  | cons i is ih =>
    rw [normVRun_cons] at h
    obtain ⟨s₁, hstep, hrest⟩ := bind_some_inv h
    obtain ⟨un₁, hb₁⟩ := normVStep_bottom_shape hstep hb
    exact ih hrest hb₁

/-- A validated `return` cannot hit `.stuck`: the only stuck path needs a
declared result with an empty operand stack. -/
theorem normReturn_not_stuck {st : NormState} {f : NormFunc}
    (hfunc : st.module.funcs.get? st.funcIdx = some f)
    (hres : f.result.isSome → st.operandStack ≠ []) :
    normReturn st ≠ .stuck := by
  intro hcon
  unfold normReturn at hcon
  rw [List.get?_eq_getElem?] at hfunc
  cases hcs : st.callStack with
  | cons fr rest =>
    simp [hcs] at hcon
  | nil =>
    cases hrt : f.result with
    | none =>
      cases hop : st.operandStack with
      | nil => simp [hfunc, hcs, hrt, hop] at hcon
      | cons v vs => simp [hfunc, hcs, hrt, hop] at hcon
    | some rt =>
      have hne := hres (by simp [hrt])
      cases hop : st.operandStack with
      | nil => exact absurd hop hne
      | cons v vs =>
        cases v with
        | i64 x => simp [hfunc, hcs, hrt, hop] at hcon
        | i32 x => simp [hfunc, hcs, hrt, hop] at hcon

/-! ## Operand extraction and branch targets -/

/-- `map f l = a :: l'` pulls back to a cons on `l`. -/
theorem map_cons_inv {α β : Type _} {l : List α} {f : α → β} {b : β} {l' : List β}
    (h : l.map f = b :: l') :
    ∃ a t, l = a :: t ∧ f a = b ∧ t.map f = l' := by
  cases l with
  | nil => simp at h
  | cons a t =>
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨a, t, rfl, h.1, h.2⟩

/-- The head of the validator's type stack is the head value's type. -/
theorem operand_head {ops : List NormVal} {os os' : List NormTy} {t : NormTy}
    (hos : os = ops.map NormVal.ty)
    (hpop : os = t :: os') :
    ∃ v rest, ops = v :: rest ∧ v.ty = t ∧ rest.map NormVal.ty = os' := by
  rw [hos] at hpop
  obtain ⟨v, tl, h1, h2, h3⟩ := map_cons_inv hpop
  exact ⟨v, tl, h1, h2, h3⟩

/-- Two operands under two pops. -/
theorem operand_two {ops : List NormVal} {os os' : List NormTy} {t1 t2 : NormTy}
    (hos : os = ops.map NormVal.ty)
    (hpop : os = t1 :: t2 :: os') :
    ∃ v1 v2 rest, ops = v1 :: v2 :: rest ∧
      v1.ty = t1 ∧ v2.ty = t2 ∧ rest.map NormVal.ty = os' := by
  obtain ⟨v1, r1, h1, ht1, hm1⟩ := operand_head hos hpop
  obtain ⟨v2, r2, h2, ht2, hm2⟩ := operand_head hm1.symm rfl
  rw [h1, h2]
  exact ⟨v1, v2, r2, rfl, ht1, ht2, hm2⟩

theorem val_i32_of_ty {v : NormVal} (h : v.ty = .i32Ty) : ∃ x, v = .i32 x := by
  cases v with
  | i32 x => exact ⟨x, rfl⟩
  | i64 x => simp [NormVal.ty] at h

theorem val_i64_of_ty {v : NormVal} (h : v.ty = .i64Ty) : ∃ x, v = .i64 x := by
  cases v with
  | i32 x => simp [NormVal.ty] at h
  | i64 x => exact ⟨x, rfl⟩

/-- `drop (length - 1)` exposes the last element. -/
theorem drop_len_sub_one {α : Type _} {l : List α} {a : α}
    (h : l.getLast? = some a) : l.drop (l.length - 1) = [a] := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.1 h
  rw [List.length_append, List.length_singleton]
  have : init.length + 1 - 1 = init.length := by omega
  rw [this, List.drop_left]

/-- The validator frame at depth `n` corresponds to the machine label at
`n`: same tag-kind, same height, matching end. -/
theorem cs_cons_of_labels {body : List NormInstr} {ls : List NormLabel}
    {cs : List NormTFrame} {n : Nat}
    (hc : NormLabelsCorrespond body ls cs) (hn : n < ls.length) :
    ∃ f l ts tls, cs.drop n = f :: ts ∧ ls.drop n = l :: tls ∧
      (match f.tag with
       | .blk => l.kind = .blockK
       | .lp => l.kind = .loopK
       | .ift | .els => l.kind = .ifK
       | .fn => False) ∧
      l.height = f.entry.length ∧
      (∃ elsePc, normElseEnd body l.startPc = some (elsePc, l.endPc)) := by
  obtain ⟨hlen, hbot, hall⟩ := hc
  have hnc : n < cs.length := by omega
  have hcs : cs.get? n = some cs[n] := by
    rw [List.get?_eq_getElem?]
    exact List.getElem?_eq_getElem hnc
  have hls : ls.get? n = some ls[n] := by
    rw [List.get?_eq_getElem?]
    exact List.getElem?_eq_getElem hn
  refine ⟨cs[n], ls[n], cs.drop (n+1), ls.drop (n+1),
    drop_eq_cons_of_get? hcs, drop_eq_cons_of_get? hls, ?_⟩
  obtain ⟨hncc, hk, hh, hend, hstart⟩ := hall n hn
  exact ⟨hk, hh, hend⟩

/-- A `br n` target exists in the machine's control stack whenever the
validator's frame stack has one — the only remaining `.stuck` path is the
function-boundary `return`, which the `hres` obligation discharges. -/
theorem normBr_ne_stuck {st : NormState} {body : List NormInstr}
    {s : NormVSt} {f : NormFunc} {n : Nat}
    (hfunc : st.module.funcs.get? st.funcIdx = some f)
    (hlt : ∃ tgt ts, s.cs.drop n = tgt :: ts)
    (hcorr : NormLabelsCorrespond body st.controlStack s.cs)
    (hres : st.controlStack.drop n = [] → f.result.isSome →
      st.operandStack ≠ []) :
    normBr st n ≠ .stuck := by
  obtain ⟨tgt, ts, hdrop⟩ := hlt
  have hlt' : n < s.cs.length := by
    have hne : s.cs.drop n ≠ [] := by rw [hdrop]; simp
    have := mt List.drop_eq_nil_iff.2 hne
    omega
  have hcl : s.cs.length = st.controlStack.length + 1 := hcorr.1
  intro hcon
  unfold normBr at hcon
  split at hcon
  · rename_i hldrop
    have hge : st.controlStack.length ≤ n := List.drop_eq_nil_iff.1 hldrop
    split at hcon
    · rename_i hlen
      exact absurd hcon (normReturn_not_stuck hfunc (hres hldrop))
    · rename_i hlen
      have : s.cs.length ≤ n := by omega
      rw [List.drop_eq_nil_iff.2 this] at hdrop
      simp at hdrop
  · rename_i l outer hldrop
    split at hcon
    all_goals exact NormStepResult.noConfusion hcon

/-- At the function boundary (`drop n = []`), a successful `normVBr`
supplies a result operand whenever the function declares one. -/
theorem normBr_hres {st : NormState} {body : List NormInstr}
    {s s' : NormVSt} {f : NormFunc} {n : Nat}
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond body st.controlStack s.cs)
    (hbot : ∃ un, s.cs.getLast? = some ⟨.fn, f.result, [], un⟩)
    (h : normVBr s n = some s')
    (hldrop : st.controlStack.drop n = []) :
    f.result.isSome → st.operandStack ≠ [] := by
  obtain ⟨tgt, ts, hdrop, hbrk⟩ := normVBr_inv h
  have hlt' : n < s.cs.length := by
    have hne : s.cs.drop n ≠ [] := by rw [hdrop]; simp
    have := mt List.drop_eq_nil_iff.2 hne
    omega
  have hcl : s.cs.length = st.controlStack.length + 1 := hcorr.1
  have hge : st.controlStack.length ≤ n := List.drop_eq_nil_iff.1 hldrop
  have hn : n = s.cs.length - 1 := by omega
  intro his
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 his
  obtain ⟨un, hbot'⟩ := hbot
  have hb2 : s.cs.drop n = [⟨.fn, f.result, [], un⟩] := by
    rw [hn]; exact drop_len_sub_one hbot'
  rw [hb2] at hdrop
  simp only [List.cons.injEq, List.nil_eq] at hdrop
  obtain ⟨htgt, -⟩ := hdrop
  subst htgt
  simp only [reduceCtorEq, if_false] at hbrk
  unfold normVBrk at hbrk
  split at hbrk
  · exact Option.noConfusion hbrk
  · rename_i hd tl hcs
    rw [ht] at hbrk
    obtain ⟨os1, hp1, hfin⟩ := bind_some_inv hbrk
    have hpop := normVPop_live hlive hp1
    rw [hos] at hpop
    obtain ⟨v, tl', h1, -, -⟩ := map_cons_inv hpop
    rw [h1]; simp

/-- `normVBrIf` inversion: the target, the condition pop, and the arity
    pop-push (when the target carries a result type). -/
theorem normVBrIf_inv {s : NormVSt} {n : Nat} {s' : NormVSt}
    (h : normVBrIf s n = some s') :
    ∃ tgt ts os1, s.cs.drop n = tgt :: ts ∧
      normVPop s.os s.cs .i32Ty = some os1 ∧
      (∀ t, (if tgt.tag = .lp then none else tgt.rt) = some t →
        ∃ os2, normVPop os1 s.cs t = some os2) := by
  unfold normVBrIf at h
  split at h
  · exact Option.noConfusion h
  · rename_i tgt ts hdrop
    dsimp only at h
    obtain ⟨os1, hp1, hb1⟩ := bind_some_inv h
    refine ⟨tgt, ts, os1, hdrop, hp1, ?_⟩
    intro t hlrt
    rw [hlrt] at hb1
    obtain ⟨x, hx, hb2⟩ := bind_some_inv hb1
    obtain ⟨os2, hp2, hm⟩ := map_some_inv hx
    exact ⟨os2, hp2⟩

/-- The context's function table is the module's signature map. -/
theorem funcs_get_of_ctx {m : NormModule} {f : NormFunc} {i : Nat}
    {ps : List NormTy} {rs : Option NormTy}
    (h : (NormVCtx.ofModule m f).funcs.get? i = some (ps, rs)) :
    ∃ g, m.funcs.get? i = some g ∧ g.params = ps ∧ g.result = rs := by
  unfold NormVCtx.ofModule at h
  rw [List.get?_eq_getElem?, List.getElem?_map] at h
  obtain ⟨g, hg, heq⟩ := map_some_inv h
  injection heq with hp hr
  exact ⟨g, by rw [List.get?_eq_getElem?]; exact hg, hp, hr⟩

/-- A type lookup through the locals map. -/
theorem map_get?_of_ty {ops : List NormVal} {i : Nat} {t : NormTy}
    (h : (ops.map NormVal.ty).get? i = some t) :
    ∃ v, ops.get? i = some v ∧ v.ty = t := by
  rw [List.get?_eq_getElem?, List.getElem?_map] at h
  obtain ⟨v, hv, he⟩ := map_some_inv h
  exact ⟨v, by rw [List.get?_eq_getElem?]; exact hv, he⟩

theorem flat_op_progress {st : NormState} {s : NormVSt} {i : NormInstr}
    {ps rs os' : List NormTy}
    (hlive : ∀ f ∈ s.cs, f.un = false)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hsig : normInstrSig i = some (ps, rs))
    (happly : normVApply s.os s.cs ps rs = some os')
    (hcon : normStepInstr st i = .stuck) : False := by
  obtain ⟨rest, hos', -⟩ := normVApply_live hlive happly
  have hosmap : st.operandStack.map NormVal.ty = ps ++ rest := hos ▸ hos'
  cases i with
  | block => simp [normInstrSig] at hsig
  | loop => simp [normInstrSig] at hsig
  | ifE => simp [normInstrSig] at hsig
  | elseE => simp [normInstrSig] at hsig
  | endI => simp [normInstrSig] at hsig
  | br n => simp [normInstrSig] at hsig
  | brIf n => simp [normInstrSig] at hsig
  | call f => simp [normInstrSig] at hsig
  | «return» => simp [normInstrSig] at hsig
  | drop => simp [normInstrSig] at hsig
  | select => simp [normInstrSig] at hsig
  | localGet x => simp [normInstrSig] at hsig
  | localSet x => simp [normInstrSig] at hsig
  | localTee x => simp [normInstrSig] at hsig
  | i32Const v => simp [normStepInstr] at hcon
  | i64Const v => simp [normStepInstr] at hcon
  | memorySize => simp [normStepInstr] at hcon
  | i32Eqz =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp [normStepInstr, normUnOp32, hop] at hcon
  | i32Cmp op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normCmpOp32, hop] at hcon
  | i32Add =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normBinOp32, hop] at hcon
  | i32Sub =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normBinOp32, hop] at hcon
  | i32Mul =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normBinOp32, hop] at hcon
  | i32Bit op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normBinOp32, hop] at hcon
  | i32Shift op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp [normStepInstr, normBinOp32, hop] at hcon
  | i64Eqz =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    simp [normStepInstr, normUnOp64, hop] at hcon
  | i64Cmp op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normCmpOp64, hop] at hcon
  | i64Add =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normBinOp64, hop] at hcon
  | i64Sub =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normBinOp64, hop] at hcon
  | i64Mul =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normBinOp64, hop] at hcon
  | i64Bit op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normBinOp64, hop] at hcon
  | i64Shift op =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp [normStepInstr, normBinOp64, hop] at hcon
  | i64DivS =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp only [normStepInstr, normDivRem64, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i64RemS =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i64_of_ty ht2
    simp only [normStepInstr, normDivRem64, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i32WrapI64 =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    simp [normStepInstr, hop] at hcon
  | i64ExtendI32U =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp [normStepInstr, hop] at hcon
  | i64ExtendI32S =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp [normStepInstr, hop] at hcon
  | i32Load a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp only [normStepInstr, normLoad, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i64Load a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp only [normStepInstr, normLoad, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i32Load8U a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp only [normStepInstr, normLoad, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i64Load8U a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, rr, hop, ht1, -⟩ := operand_head rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    simp only [normStepInstr, normLoad, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i32Store a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp only [normStepInstr, normStore, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i32Store8 a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i32_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp only [normStepInstr, normStore, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i64Store a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp only [normStepInstr, normStore, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon
  | i64Store8 a =>
    simp only [normInstrSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨hps, -⟩ := hsig; subst hps
    obtain ⟨v1, v2, rr, hop, ht1, ht2, -⟩ := operand_two rfl hosmap
    obtain ⟨x1, rfl⟩ := val_i64_of_ty ht1
    obtain ⟨x2, rfl⟩ := val_i32_of_ty ht2
    simp only [normStepInstr, normStore, hop] at hcon
    split at hcon <;> exact NormStepResult.noConfusion hcon

/-! ## WX-002 progress -/

/-- WX-002 progress: a valid module's well-formed machine state is never
`.stuck` — every instruction the validator accepts has a machine
transition (or a lawful trap/return). `hlive` is the reachability
side-condition: machine-reachable states have all-live frames (a `br`
jumps over the unreachable stretch, so the machine's `un`-marked frames
never sit on its control stack). -/
theorem wx002_progress {st : NormState} {f : NormFunc} {s : NormVSt}
    (hvalid : NormValidModule st.module)
    (hfunc : st.module.funcs.get? st.funcIdx = some f)
    (hs : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hlive : ∀ fr ∈ s.cs, fr.un = false) :
    NormStep st ≠ .stuck := by
  obtain ⟨unb, hbot⟩ := normVRun_fn_frame hs (by rfl)
  have hacc := hvalid.2.1 f (List.get?_mem hfunc)
  unfold normVAccept at hacc
  intro hcon
  unfold NormStep at hcon
  cases hfg : st.module.funcs.get? st.funcIdx with
  | none =>
    rw [hfg] at hfunc; simp at hfunc
  | some g =>
    rw [hfg] at hfunc
    simp only [Option.some.injEq] at hfunc
    subst hfunc
    rw [List.get?_eq_getElem?] at hfg
    simp only [List.get?_eq_getElem?, hfg] at hcon
    split at hcon
    · rename_i i hi
      rw [← List.get?_eq_getElem?] at hi
      -- instruction case: split the body run at pc
      split at hacc
      · rename_i x os' f0 hrun
        have hbd : g.body = g.body.take st.pc ++ i :: g.body.drop (st.pc + 1) := by
          rw [← drop_eq_cons_of_get? hi]
          exact (List.take_append_drop st.pc g.body).symm
        rw [hbd, normVRun_append, hs] at hrun
        obtain ⟨x, hx, hrun⟩ := bind_some_inv hrun
        simp only [Option.some.injEq] at hx
        subst hx
        rw [normVRun_cons] at hrun
        obtain ⟨s', hstep, hrest⟩ := bind_some_inv hrun
        have hfin : (⟨os', [f0]⟩ : NormVSt).cs.length ≤ s.cs.length := by
          have hcl := hcorr.1
          show 1 ≤ s.cs.length; omega
        have hC : (NormVCtx.ofModule st.module g).locals =
            g.params ++ g.locals := rfl
        cases i with
        | block =>
          obtain ⟨⟨el, ep⟩, hend⟩ := Option.isSome_iff_exists.1
            (normElseEnd_of_open (Or.inl rfl) hstep hrest hfin)
          simp [normStepInstr, hfg, hend] at hcon
        | loop =>
          obtain ⟨⟨el, ep⟩, hend⟩ := Option.isSome_iff_exists.1
            (normElseEnd_of_open (Or.inr (Or.inl rfl)) hstep hrest hfin)
          simp [normStepInstr, hfg, hend] at hcon
        | ifE =>
          simp only [normVStep] at hstep
          obtain ⟨o1, hp1, hs'⟩ := map_some_inv hstep
          have hos1 := normVPop_live hlive hp1
          obtain ⟨v, rest, hop, ht, hm1⟩ := operand_head hos hos1
          obtain ⟨c, hv⟩ := val_i32_of_ty ht
          subst hv
          obtain ⟨⟨el, ep⟩, hend⟩ := Option.isSome_iff_exists.1
            (normElseEnd_of_open (Or.inr (Or.inr rfl)) hstep hrest hfin)
          have hb2 : (Option.map NormFunc.body (some g)).getD [] = g.body := rfl
          simp only [normStepInstr, List.get?_eq_getElem?, hfg, hb2, hop, hend]
            at hcon
          cases hc : (c != 0) with
          | true =>
            simp only [hc] at hcon
            exact NormStepResult.noConfusion hcon
          | false =>
            cases el <;>
              simp only [hc] at hcon <;>
              exact NormStepResult.noConfusion hcon
        | elseE =>
          simp only [normVStep] at hstep
          split at hstep
          · rename_i fr rest hcs
            split at hstep
            · rename_i htag
              have hne : rest ≠ [] := by
                intro hre
                rw [hre] at hcs
                have hgl : (fr :: []).getLast? = some fr := rfl
                rw [hcs, hgl] at hbot
                simp only [Option.some.injEq] at hbot
                subst hbot
                simp at htag
              have hcl := hcorr.1
              rw [hcs] at hcl
              have hz : rest.length ≠ 0 :=
                fun h => hne (List.length_eq_zero.1 h)
              simp only [List.length_cons] at hcl
              have hpos : 0 < st.controlStack.length := by omega
              cases hcs' : st.controlStack with
              | nil => rw [hcs'] at hpos; simp at hpos
              | cons lab tl =>
                simp only [normStepInstr, hcs'] at hcon
                exact NormStepResult.noConfusion hcon
            · exact Option.noConfusion hstep
          · exact Option.noConfusion hstep
        | endI =>
          simp only [normVStep] at hstep
          split at hstep
          · rename_i fr rest hcs
            split at hstep
            · exact Option.noConfusion hstep
            · rename_i htag
              have hne : rest ≠ [] := by
                intro hre
                rw [hre] at hcs
                have hgl : (fr :: []).getLast? = some fr := rfl
                rw [hcs, hgl] at hbot
                simp only [Option.some.injEq] at hbot
                subst hbot
                exact absurd rfl htag
              have hcl := hcorr.1
              rw [hcs] at hcl
              have hz : rest.length ≠ 0 :=
                fun h => hne (List.length_eq_zero.1 h)
              simp only [List.length_cons] at hcl
              have hpos : 0 < st.controlStack.length := by omega
              cases hcs' : st.controlStack with
              | nil => rw [hcs'] at hpos; simp at hpos
              | cons lab tl =>
                simp only [normStepInstr, hcs'] at hcon
                exact NormStepResult.noConfusion hcon
          · exact Option.noConfusion hstep
        | br n =>
          simp only [normVStep] at hstep
          obtain ⟨tgt, ts, hdrop, -⟩ := normVBr_inv hstep
          have hfg' : st.module.funcs.get? st.funcIdx = some g := by
            rw [List.get?_eq_getElem?]; exact hfg
          simp only [normStepInstr] at hcon
          exact normBr_ne_stuck hfg' ⟨tgt, ts, hdrop⟩ hcorr
            (fun hd => normBr_hres hlive hos hcorr ⟨unb, hbot⟩ hstep hd) hcon
        | brIf n =>
          simp only [normVStep] at hstep
          obtain ⟨tgt, ts, os1, hdrop, hp1, hlrt⟩ := normVBrIf_inv hstep
          have hos1 := normVPop_live hlive hp1
          obtain ⟨v, rest, hop, ht, hm1⟩ := operand_head hos hos1
          obtain ⟨c, rfl⟩ := val_i32_of_ty ht
          have hfg' : st.module.funcs.get? st.funcIdx = some g := by
            rw [List.get?_eq_getElem?]; exact hfg
          simp only [normStepInstr, hop] at hcon
          cases hc : (c != 0) with
          | false =>
            simp only [hc] at hcon
            exact NormStepResult.noConfusion hcon
          | true =>
            simp [hc] at hcon
            refine normBr_ne_stuck (st := { st with operandStack := rest })
              hfg' ⟨tgt, ts, hdrop⟩ hcorr ?_ hcon
            intro hld his
            have hld' : st.controlStack.drop n = [] := hld
            have hge := List.drop_eq_nil_iff.1 hld'
            have hcl := hcorr.1
            have hlt' : n < s.cs.length := by
              have hne2 : s.cs.drop n ≠ [] := by rw [hdrop]; simp
              have := mt List.drop_eq_nil_iff.2 hne2
              omega
            have hn : n = s.cs.length - 1 := by omega
            obtain ⟨t, hteq⟩ := Option.isSome_iff_exists.1 his
            have hb2 : s.cs.drop n = [⟨.fn, g.result, [], unb⟩] := by
              rw [hn]; exact drop_len_sub_one hbot
            rw [hb2] at hdrop
            simp only [List.cons.injEq, List.nil_eq] at hdrop
            obtain ⟨htgt, -⟩ := hdrop
            subst htgt
            obtain ⟨os2, hp2⟩ := hlrt t (by simp [hteq])
            have hpop2 := normVPop_live hlive hp2
            rw [← hm1] at hpop2
            obtain ⟨v2, tl2, h1, -, -⟩ := map_cons_inv hpop2
            show rest ≠ []
            rw [h1]; simp
        | call g' =>
          simp only [normVStep] at hstep
          cases hcg : (NormVCtx.ofModule st.module g).funcs.get? g' with
          | none =>
            simp only [← List.get?_eq_getElem?, hcg] at hstep
            exact Option.noConfusion hstep
          | some pr =>
            simp only [← List.get?_eq_getElem?, hcg] at hstep
            obtain ⟨cg, hcg', hps, hrs⟩ := funcs_get_of_ctx hcg
            obtain ⟨os1, hp1, -⟩ := map_some_inv hstep
            have hpops := normVPops_live hlive hp1
            have h1 : s.os.length = st.operandStack.length := by
              rw [hos, List.length_map]
            rw [hpops, List.length_append, List.length_reverse, ← hps] at h1
            have hlen : cg.params.length ≤ st.operandStack.length := by omega
            have harg : (st.operandStack.take cg.params.length).length =
                cg.params.length := by
              rw [List.length_take, Nat.min_eq_left hlen]
            rw [List.get?_eq_getElem?] at hcg'
            simp [normStepInstr, hcg', harg] at hcon
        | «return» =>
          simp only [normVStep] at hstep
          have hfg' : st.module.funcs.get? st.funcIdx = some g := by
            rw [List.get?_eq_getElem?]; exact hfg
          simp only [normStepInstr] at hcon
          refine normReturn_not_stuck hfg' ?_ hcon
          intro his
          obtain ⟨t, hteq⟩ := Option.isSome_iff_exists.1 his
          rw [hbot, hteq] at hstep
          have hstep' : normVBrk s (some t) = some s' := hstep
          unfold normVBrk at hstep'
          split at hstep'
          · exact Option.noConfusion hstep'
          · rename_i hd tl hcs
            obtain ⟨os1, hp1, -⟩ := bind_some_inv hstep'
            have hp1' : normVPop s.os s.cs t = some os1 := hp1
            have hos1 := normVPop_live hlive hp1'
            obtain ⟨v, tl', h1, -, -⟩ := operand_head hos hos1
            rw [h1]; simp
        | drop =>
          simp only [normVStep] at hstep
          split at hstep
          · rename_i fr rest hcs
            obtain ⟨r, hr, -⟩ := map_some_inv hstep
            have hfun : fr.un = false :=
              hlive fr (by rw [hcs]; exact List.mem_cons_self ..)
            rw [hfun] at hr
            obtain ⟨t, -, hos'⟩ := normTckAny_live hr
            obtain ⟨v, tl, h1, -, -⟩ := operand_head hos hos'
            simp [normStepInstr, h1] at hcon
          · exact Option.noConfusion hstep
        | select =>
          simp only [normVStep] at hstep
          obtain ⟨os', hp1, hb1⟩ := bind_some_inv hstep
          have hos1 := normVPop_live hlive hp1
          obtain ⟨v1, r1, hop1, ht1, hm1⟩ := operand_head hos hos1
          obtain ⟨c, rfl⟩ := val_i32_of_ty ht1
          split at hb1
          · rename_i fr rest hcs
            obtain ⟨r, hr, hb2⟩ := bind_some_inv hb1
            have hfun : fr.un = false :=
              hlive fr (by rw [hcs]; exact List.mem_cons_self ..)
            rw [hfun] at hr
            obtain ⟨t, ht1', hos'⟩ := normTckAny_live hr
            obtain ⟨v2, r2, hop2, ht2, hm2⟩ := operand_head hm1.symm hos'
            rw [ht1'] at hb2
            obtain ⟨os3, hp3, -⟩ := map_some_inv hb2
            have hos'' := normVPop_live hlive hp3
            obtain ⟨v3, r3, hop3, ht3, hm3⟩ := operand_head hm2.symm hos''
            simp [normStepInstr, hop1, hop2, hop3] at hcon
          · exact Option.noConfusion hb1
        | localGet x =>
          simp only [normVStep] at hstep
          obtain ⟨lt, hlt, -⟩ := map_some_inv hstep
          rw [hC, ← hloc] at hlt
          obtain ⟨v, hv, -⟩ := map_get?_of_ty hlt
          rw [List.get?_eq_getElem?] at hv
          simp [normStepInstr, hv] at hcon
        | localSet x =>
          simp only [normVStep] at hstep
          obtain ⟨lt, hlt, hb⟩ := bind_some_inv hstep
          obtain ⟨os', hp1, -⟩ := map_some_inv hb
          have hos1 := normVPop_live hlive hp1
          obtain ⟨v, rest, hop, ht, hm1⟩ := operand_head hos hos1
          rw [hC, ← hloc] at hlt
          obtain ⟨lv, hv, -⟩ := map_get?_of_ty hlt
          have hlt2 : x < st.locals.length := lt_of_get? hv
          have hset := normLocalsSet_of_lt hlt2 (v := v)
          simp [normStepInstr, hop, hset] at hcon
        | localTee x =>
          simp only [normVStep] at hstep
          obtain ⟨lt, hlt, hb⟩ := bind_some_inv hstep
          obtain ⟨os', hp1, -⟩ := map_some_inv hb
          have hos1 := normVPop_live hlive hp1
          obtain ⟨v, rest, hop, ht, hm1⟩ := operand_head hos hos1
          rw [hC, ← hloc] at hlt
          obtain ⟨lv, hv, -⟩ := map_get?_of_ty hlt
          have hlt2 : x < st.locals.length := lt_of_get? hv
          have hset := normLocalsSet_of_lt hlt2 (v := v)
          simp [normStepInstr, hop, hset] at hcon
        | _ =>
          simp only [normVStep] at hstep
          obtain ⟨⟨ps, rs⟩, hsig, hb⟩ := bind_some_inv hstep
          obtain ⟨os', happly, -⟩ := map_some_inv hb
          exact flat_op_progress hlive hos hsig happly hcon
      · simp at hacc
    · rename_i hpc
      have hge : g.body.length ≤ st.pc := by
        have hnlt : ¬ (st.pc < g.body.length) := by
          intro h2
          rw [List.getElem?_eq_getElem h2] at hpc
          simp at hpc
        omega
      have htake : g.body.take st.pc = g.body := List.take_of_length_le hge
      rw [htake] at hs
      have hfg' : st.module.funcs.get? st.funcIdx = some g := by
        rw [List.get?_eq_getElem?]; exact hfg
      refine normReturn_not_stuck hfg' ?_ hcon
      intro his
      obtain ⟨t, hteq⟩ := Option.isSome_iff_exists.1 his
      split at hacc
      · rename_i x os' f0 hrun
        rw [hs] at hrun
        simp only [Option.some.injEq] at hrun
        subst hrun
        have hgl : ([f0] : List NormTFrame).getLast? = some f0 := rfl
        have hbot' : ([f0] : List NormTFrame).getLast? =
            some ⟨.fn, g.result, [], unb⟩ := hbot
        rw [hgl] at hbot'
        simp only [Option.some.injEq] at hbot'
        subst hbot'
        have hun : unb = false :=
          hlive ⟨.fn, g.result, [], unb⟩ (by simp)
        subst hun
        cases hfchk : normVFchk os' ⟨.fn, g.result, [], false⟩ with
        | none => simp [hfchk] at hacc
        | some rem =>
          unfold normVFchk at hfchk
          rw [hteq] at hfchk
          obtain ⟨os2, hp, hlen⟩ := bind_some_inv hfchk
          have hp' : normTckPop os' 0 false t = some os2 := hp
          have hos1 := normTckPop_live hp'
          obtain ⟨v, tl, h1, -, -⟩ := operand_head hos hos1
          rw [h1]; simp
      · simp at hacc
