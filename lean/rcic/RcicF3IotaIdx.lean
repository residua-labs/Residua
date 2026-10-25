import rcic.RcicF3PropIota

/-!
# F3 S5b-7: ι with recursive fields, with or without indices

`RecFieldsDirect f lsF np nq Fs d`: every field is family-free or the family
applied to the parameter locals and `nq` family-free indices.
`rhsArgs_den`: the ι right-hand side's arguments denote the fields with the
recursor's values inserted after the recursive ones; each recursive call's
indices are read through the constructor telescope (`SemTel`).
`iota_group`: ι at a recursor admitted by `a`: for a `Type` family whose
recursive fields have this shape (indexed families included); for a `Prop`
family eliminating into `Prop` (both sides are proofs); and for a `Prop`
family with large elimination whose fields are proofs, none revealed in the
result indices (read off the right-hand side's typing, `RcicF3PropIota`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- Every field from depth `d` on is family-free, or the family at levels
`lsF` applied to the parameter locals and `nq` family-free indices. -/
def RecFieldsDirect (f : Nat) (lsF : List Level) (np nq : Nat) : List (Expr Nat) → Nat → Prop
  | [], _ => True
  | A :: Fs, d => (occursConst f A = false ∨ ∃ idx : List (Expr Nat),
      A = foldApps (.const f lsF) (policyParameterLocals np d ++ idx) ∧ idx.length = nq ∧
        ∀ e, e ∈ idx → occursConst f e = false) ∧ RecFieldsDirect f lsF np nq Fs (d + 1)

theorem recFieldsDirect_of_free {f : Nat} {lsF : List Level} {np nq : Nat} : (Fs : List (Expr Nat)) → (d : Nat) →
    (∀ T, T ∈ Fs → occursConst f T = false) → RecFieldsDirect f lsF np nq Fs d
  | [], _, _ => trivial
  | A :: Fs, d, h => ⟨Or.inl (h A (List.mem_cons_self _ _)),
      recFieldsDirect_of_free Fs (d + 1) fun T hT => h T (List.mem_cons_of_mem _ hT)⟩

/-- `RecFieldsDirect` fields are non-`pi` where they recurse — `ihChild` vacuous. -/
theorem ihChildL_of_recFieldsDirect {f : Nat} {lsF : List Level} {np nq : Nat} (z : PSet.{T}) :
    (Fs : List (Expr Nat)) → (xs : List PSet.{T}) → (d : Nat) →
    RecFieldsDirect f lsF np nq Fs d → ihChildL f z Fs xs
  | [], _, _, _ => trivial
  | A :: Fs, [], _, _ => trivial
  | A :: Fs, x :: xs, d, ⟨hA, hFs⟩ =>
      ⟨fun hocc => by
         rcases hA with h0 | ⟨idx, rfl, _, _⟩
         · simp [h0] at hocc
         · exact ihChild_foldApps z (fun _ _ h => Expr.noConfusion h)
             (policyParameterLocals np d ++ idx) x,
       ihChildL_of_recFieldsDirect z Fs xs (d + 1) hFs⟩

/-- `ihChildL` when admission's field analysis classified every field —
`occursConst`-true fields went through `isFamilyApp` (non-`pi`, `ihDepth` `0`). -/
theorem ihChildL_of_analyze {f : Nat} (z : PSet.{T}) :
    (As : List (Expr Nat)) → (xs : List PSet.{T}) → (ks : List RecKind) →
    analyzeFields f As = some ks → ihChildL f z As xs
  | [], _, _, _ => trivial
  | A :: As, [], _, _ => trivial
  | A :: As, x :: xs, ks, h => by
      unfold analyzeFields at h
      cases ha : analyzeField f A with
      | none => rw [ha] at h; simp at h
      | some k =>
          cases hb : analyzeFields f As with
          | none => rw [ha, hb] at h; simp at h
          | some ks' =>
              rw [ha, hb] at h
              refine ⟨fun hocc => ?_, ihChildL_of_analyze z As xs ks' hb⟩
              unfold analyzeField at ha
              rw [hocc] at ha; simp at ha
              cases hf : isFamilyApp f A with
              | true => exact ihChild_of_depth0 z (ihDepth_eq_zero_of_isFamilyApp hf) x
              | false => rw [hf] at ha; simp at ha

theorem RecFieldsDirect.get {f : Nat} {lsF : List Level} {np nq : Nat} : {Fs : List (Expr Nat)} → {d : Nat} →
    RecFieldsDirect f lsF np nq Fs d → (k : Nat) → (F : Expr Nat) → Fs[k]? = some F → occursConst f F = true →
    ∃ idx : List (Expr Nat), F = foldApps (.const f lsF) (policyParameterLocals np (d + k) ++ idx) ∧
      idx.length = nq ∧ ∀ e, e ∈ idx → occursConst f e = false
  | A :: Fs, d, ⟨hA, _⟩, 0, F, h, ho => by
      rw [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rcases hA with h0 | h0
      · rw [h0] at ho; cases ho
      · exact h0
  | A :: Fs, d, ⟨_, hFs⟩, k + 1, F, h, ho => by
      rw [List.getElem?_cons_succ] at h
      rw [show d + (k + 1) = d + 1 + k by omega]
      exact RecFieldsDirect.get hFs k F h ho

theorem LEq.take : {xs ys : List PSet.{T}} → LEq xs ys → (k : Nat) → LEq (xs.take k) (ys.take k)
  | [], [], k, _ => by rw [List.take_nil]; trivial
  | _ :: _, _ :: _, _, 0 => trivial
  | _ :: _, _ :: _, ⟨hx, h⟩, k + 1 => ⟨hx, LEq.take h k⟩

theorem LEq_map_of {α : Type} {f g : α → PSet.{T}} : (l : List α) → (∀ e, e ∈ l → Equiv (f e) (g e)) →
    LEq (l.map f) (l.map g)
  | [], _ => trivial
  | e :: l, h => ⟨h e (List.mem_cons_self _ _), LEq_map_of l fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

/-- **The ι right-hand side's arguments**: each field, and after each
recursive field the recursive call's value. The recursive call's indices are
the field's indices, read at the fields before it. -/
theorem rhsArgs_den (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (rec : Expr Nat) (pre : List (Expr Nat))
    (np nM f nq : Nat) (lsF : List Level) (g : PSet.{T} → PSet.{T}) (σF : Nat → Nat) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (Tl : Expr Nat) → (Fs : List (Expr Nat)) → (d : Nat) →
    (ρF : Nat → PSet.{T}) →
    SemTel M σ ρ Tl Fs σF ρF → analyzeFields f Fs = some ks → RecFieldsDirect f lsF np nq Fs d →
    fs.length = Fs.length →
    (∀ (k : Nat) (x A : Expr Nat) (idx : List (Expr Nat)), fs[k]? = some x → ks[k]? = some .directRec →
      Fs[k]? = some (foldApps (.const f lsF) (policyParameterLocals np (d + k) ++ idx)) → idx.length = nq →
      (familyIdx np A).map (den M σ ρ) = idx.map (den M σF (push ((fs.take k).map (den M σ ρ)) ρF)) →
      Equiv (den M σ ρ (recCallField rec pre np nM x A)) (g (den M σ ρ x))) →
    LEq ((rhsArgs rec pre np nM fs ks Tl).map (den M σ ρ)) (ihArgs f g Fs (fs.map (den M σ ρ)))
  | [], _, _, [], _, _, _, _, _, _, _ => trivial
  | x :: fs, ks, Tl, F :: Fs, d, ρF, hT, hk, ⟨hF, hFs⟩, hl, hcall => by
      obtain ⟨Ds, b, hTe, hDl, _⟩ := hT
      cases Ds with
      | nil => exact (Nat.succ_ne_zero _ hDl.symm).elim
      | cons A Ds =>
          have hTe' : Tl = .pi A (policyPi Ds b) := hTe
          subst hTe'
          have hshape : SemTel M σ ρ (.pi A (policyPi Ds b)) (F :: Fs) σF ρF := ⟨A :: Ds, b, rfl, hDl, by assumption⟩
          obtain ⟨I, hI, hIA, hIs⟩ := hshape.head
          cases hkF : analyzeField f F with
          | none => simp [analyzeFields, hkF] at hk
          | some kF =>
            cases hks : analyzeFields f Fs with
            | none => simp [analyzeFields, hkF, hks] at hk
            | some ks' =>
              have hk' : ks = kF :: ks' := by simp [analyzeFields, hkF, hks] at hk; exact hk.symm
              subst hk'
              have ih := rhsArgs_den M σ ρ rec pre np nM f nq lsF g σF fs ks' (instantiate0 x (policyPi Ds b)) Fs
                (d + 1) (vcons (den M σ ρ x) ρF) (hshape.step x) hks hFs (Nat.succ.inj hl)
                (fun k y A' idx h1 h2 h3 h4 h5 => hcall (k + 1) y A' idx (by simpa using h1) (by simpa using h2)
                  (by rw [List.getElem?_cons_succ, show d + (k + 1) = d + 1 + k by omega]; exact h3) h4 h5)
              cases kF with
              | plain =>
                  have ho := analyzeField_plain_iff hkF
                  show LEq ((x :: rhsArgs rec pre np nM fs ks' (instantiate0 x (policyPi Ds b))).map (den M σ ρ))
                    (ihArgs f g (F :: Fs) (den M σ ρ x :: fs.map (den M σ ρ)))
                  unfold ihArgs
                  rw [ho, if_neg (by decide)]
                  exact ⟨Equiv.rfl, ih⟩
              | directRec =>
                  have ho := analyzeField_rec hkF
                  obtain ⟨idx, hFe, hidxl, _⟩ : ∃ idx : List (Expr Nat),
                      F = foldApps (.const f lsF) (policyParameterLocals np d ++ idx) ∧ idx.length = nq ∧
                        ∀ e, e ∈ idx → occursConst f e = false := by
                    rcases hF with h | h
                    · rw [h] at ho; cases ho
                    · exact h
                  have hfam : (familyIdx np A).map (den M σ ρ) = idx.map (den M σF ρF) := by
                    rw [hIA, hFe, hI.map_foldApps]
                    obtain ⟨ls', hc⟩ := hI.2 f lsF
                    rw [hc, familyIdx_foldApps_const, List.map_append,
                      List.drop_left' (by rw [List.length_map, length_paramLocals]), List.map_map]
                    exact List.map_congr_left fun e _ => hIs e
                  show LEq ((x :: recCallField rec pre np nM x A ::
                      rhsArgs rec pre np nM fs ks' (instantiate0 x (policyPi Ds b))).map (den M σ ρ))
                    (ihArgs f g (F :: Fs) (den M σ ρ x :: fs.map (den M σ ρ)))
                  unfold ihArgs
                  rw [ho, if_pos rfl, hFe, ihAt_foldApps (fun _ _ h => Expr.noConfusion h)]
                  exact ⟨Equiv.rfl, hcall 0 x A idx List.getElem?_cons_zero List.getElem?_cons_zero
                    (by rw [List.getElem?_cons_zero, Nat.add_zero, hFe]) hidxl hfam, ih⟩
  | [], _, _, _ :: _, _, _, _, _, _, hl, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, _, _, [], _, _, _, _, _, hl, _ => (Nat.succ_ne_zero _ hl).elim

/-- The agreement ι needs at a constructor of a `Prop` family with large
elimination: at every split of the recursor's arguments before the major
premise into parameters, motive, minors and indices `is`, the minor applied to
the fields reconstructed from `is` agrees with the minor applied to the
fields' values. (Without a field revealed in the indices it holds by
`spine_proofs`; with one, it is the index agreement the left-hand side's
typing carries.) -/
def IotaAgree {E E0 : ResolvedEnv} {r : Nat} {m : CheckedMember} (M : Interp.{T}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{T}) (a : RecursorEliminationAdmitted E0 r m) (w : IotaWitness E)
    (j : Fin a.constructors.length) : Prop :=
  ∀ ps mo ms is, w.preMajor.map (den M σ ρ) = ps ++ mo :: (ms ++ is) →
    ps.length = a.family.parameters.length → ms.length = a.constructors.length →
    is.length = a.family.indices.length →
    TelFits M (σOf (w.ls.map (evalTotal σ))) (recPreDomsOf a) (fun _ => pempty) (w.preMajor.map (den M σ ρ)) →
    ∀ c, (famDataOf a).ctors = [c] →
      Equiv (fapps (den M σ ρ w.minor) (recon c is)) (fapps (den M σ ρ w.minor) (w.fields.map (den M σ ρ)))

/-- A witness's fields are its constructor's fields. -/
theorem witness_fields_length {E E0 : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E0 r m) (w : IotaWitness E) (hrec : w.recRef = r) (hm : w.recMember = m)
    (j : Fin a.constructors.length) (hcm : w.ctorMember = a.constructors[j.val]) :
    w.fields.length = (a.constructorViews j).fields.length := by
  obtain ⟨hnp, _, _, _⟩ := iota_align a w hrec hm
  have hcpl := (a.constructorViews j).parameterCount
  have hctm : w.ctorMember.mtype = policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
          (a.constructorViews j).resultIndices)) := by rw [hcm]; exact (a.constructorViews j).storedType
  have hnpar := w.hnpar
  rw [hctm, piCount_policyPi, piCount_foldApps _ (fun _ _ h => Expr.noConfusion h), List.length_append] at hnpar
  omega

/-- **ι**: at a `DerivedIota` witness whose recursor is admitted by `a`, the
two sides denote `≈`-equal values, given the recursor's, the family's and the
constructor's values, a uniform universe profile, recursive fields of the
direct shape (`RecFieldsDirect`, indices allowed), the constructor's levels
bounded by the family's arity, and, for `Prop` large elimination, family-free
fields none revealed in the result indices, the minor's type over the lifted
fields, the fields forming a telescope of propositions, and the facts the
right-hand side's typing gives along its spine (`hspine`). -/
theorem iota_group {M : Interp.{T}} (W : Nat → PSet.{T}) {E E0 : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E0 r m) (w : IotaWitness E) (hrec : w.recRef = r) (hm : w.recMember = m)
    (σ : Nat → Nat) (ρ : Nat → PSet.{T}) {X : PSet.{T}}
    (hrecμ : Equiv (M.μ r (w.ls.map (evalTotal σ)))
      (piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd M (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
        (fun _ => pempty) m.mtype))
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf (w.ls.map (evalTotal σ))))))
      (piLam M (σOf (w.ls.map (evalTotal σ))) (famEnd M W (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
        (fun _ => pempty) (famType (famDataOf a))))
    (j : Fin a.constructors.length) (hj : w.ctorIdx = j.val) (hcm : w.ctorMember = a.constructors[j.val])
    (hctorμ : Equiv (M.μ w.ctorRef (w.lsC.map (evalTotal σ)))
      (piLam M (σOf (w.lsC.map (evalTotal σ))) (ctorEnd M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
        (a.constructorViews j).fields.length) (fun _ => pempty) (a.constructors[j.val]).mtype))
    (huni : evalTotal (σOf (w.ls.map (evalTotal σ))) a.family.resultLevel = 0 ↔
      evalTotal (σOf (w.lsC.map (evalTotal σ))) a.family.resultLevel = 0)
    (hrf : RecFieldsDirect a.family.ref (policyFamilyLevels a.family) a.family.parameters.length
      a.family.indices.length (a.constructorViews j).fields 0)
    (hlvC : exprLevelsBounded a.family.member.arity (a.constructors[j.val]).mtype = true)
    (hpf : evalTotal (σOf (w.ls.map (evalTotal σ))) a.family.resultLevel = 0 → a.policy = .anySort →
      ((∀ T, T ∈ (a.constructorViews j).fields → occursConst a.family.ref T = false) ∧
      (((∀ k, k < (a.constructorViews j).fields.length →
        posOf (.bvar ((a.constructorViews j).fields.length - 1 - k)) (a.constructorViews j).resultIndices = none) ∧
      (∃ b, a.minorTypes[j.val]? = some (policyPi (liftFields (1 + j.val) (a.constructorViews j).fields 0) b)) ∧
      ∀ ps, TelFits M (σOf (w.ls.map (evalTotal σ))) a.family.parameters (fun _ => pempty) ps →
        PropTel M (σOf (w.ls.map (evalTotal σ))) (a.constructorViews j).fields (push ps (fun _ => pempty))) ∨
      IotaAgree M σ ρ a w j)) ∨
      PropEmpty M (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
    (hspine : SpineFacts M (den M σ ρ w.minor) ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      w.fields w.kinds w.ctorAfterParams).map (den M σ ρ)))
    (ml : den M σ ρ (iotaLhsOf w) ∈ Ed M X) (mr : den M σ ρ (iotaRhsOf w) ∈ Ed M X) :
    Equiv (den M σ ρ (iotaLhsOf w)) (den M σ ρ (iotaRhsOf w)) := by
  obtain ⟨hnp, hnM, hnq, hfr⟩ := iota_align a w hrec hm
  cases hl0 : M.dec (Equiv (den M σ ρ (iotaLhsOf w)) pempty) with
  | isTrue h0 => exact rhs_eq_ed_pempty ml mr h0
  | isFalse hne =>
  -- the left-hand side as an application of the recursor's value
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hjk : j.val < a.constructors.length := j.isLt
  have hlhs : den M σ ρ (iotaLhsOf w) =
      fapps (M.μ r (w.ls.map (evalTotal σ))) (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) := by
    unfold iotaLhsOf recCall
    rw [fapps_den_append_singleton, hrec]
    rfl
  have hpvl : (w.preMajor.map (den M σ ρ)).length =
      a.family.parameters.length + 1 + a.constructors.length + a.family.indices.length := by
    rw [List.length_map, w.hpre, hnp, hnM, hnq]
  rw [recType_eq a] at hrecμ
  have hne' : ¬ Equiv (fapps (piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd M (σOf (w.ls.map (evalTotal σ)))
      (famDataOf a)) (fun _ => pempty) (policyPi (recPreDomsOf a ++ [recMajorOf a]) (recResultOf a)))
      (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)])) pempty := fun h =>
    hne (by rw [hlhs]; exact (fapps_congr hrecμ _).trans h)
  have hlenD : (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]).length =
      (recPreDomsOf a ++ [recMajorOf a]).length := by
    rw [List.length_append, List.length_append, hpvl, recPreDomsOf_length]; rfl
  have hfit := fits_of_fapps_ne M (σOf (w.ls.map (evalTotal σ))) (recEnd_resp M (σOf (w.ls.map (evalTotal σ))) (famDataOf a))
    (recResultOf a) (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty) _ hlenD hne'
  have heq := fapps_piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd_resp M (σOf (w.ls.map (evalTotal σ))) (famDataOf a)) (recResultOf a)
    (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty) _ hfit
  rw [show recResultOf a = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1)) _ from rfl,
    piLam_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h)] at heq
  have hL : Equiv (den M σ ρ (iotaLhsOf w)) (recEnd M (σOf (w.ls.map (evalTotal σ))) (famDataOf a)
      (push (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) (fun _ => pempty))) := by
    rw [hlhs]; exact (fapps_congr hrecμ _).trans heq
  -- the major premise's membership
  obtain ⟨xs0, ys0, hxy, hf1, hf2⟩ := TelFits_split _ _ _ _ hfit
  have hx0 : xs0 = w.preMajor.map (den M σ ρ) := by
    have h1 := hf1.length
    have := List.append_inj hxy.symm (by rw [h1, hpvl, recPreDomsOf_length])
    exact this.1
  subst hx0
  have hy0 : ys0 = [den M σ ρ (ctorMajor w)] := (List.append_cancel_left hxy).symm
  subst hy0
  have hmaj : den M σ ρ (ctorMajor w) ∈ Ed M (den M (σOf (w.ls.map (evalTotal σ)))
      (push (w.preMajor.map (den M σ ρ)) (fun _ => pempty)) (recMajorOf a)) := hf2.1
  -- splitting the prefix
  have hsplit := list_split4 (w.preMajor.map (den M σ ρ)) a.family.parameters.length a.constructors.length
    a.family.indices.length hpvl pempty
  generalize hps : (w.preMajor.map (den M σ ρ)).take a.family.parameters.length = ps at hsplit
  generalize hmo : (w.preMajor.map (den M σ ρ)).getD a.family.parameters.length pempty = mo at hsplit
  generalize hms : ((w.preMajor.map (den M σ ρ)).drop (a.family.parameters.length + 1)).take
    a.constructors.length = ms at hsplit
  generalize his : (w.preMajor.map (den M σ ρ)).drop
    (a.family.parameters.length + 1 + a.constructors.length) = is at hsplit
  have hpsl : ps.length = a.family.parameters.length := by rw [← hps, List.length_take]; omega
  have hmsl : ms.length = a.constructors.length := by
    rw [← hms, List.length_take, List.length_drop]; omega
  have hisl : is.length = a.family.indices.length := by rw [← his, List.length_drop]; omega
  have henv : w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)] =
      ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)])) := by
    rw [hsplit]; simp only [List.append_assoc, List.cons_append]
  rw [henv] at hL
  rw [hsplit, den_recMajor M _ a ps mo ms is _ hpsl (by rw [hmsl, hk]) hisl] at hmaj
  -- the selected minor
  have hmin : ms.getD j.val pempty = den M σ ρ w.minor := by
    have hm1 := w.hminor
    rw [hnp, hj] at hm1
    have hm2 : (w.preMajor.map (den M σ ρ))[a.family.parameters.length + 1 + j.val]? = some (den M σ ρ w.minor) := by
      rw [List.getElem?_map, hm1]; rfl
    rw [← hms, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hjk, List.getElem?_drop,
      show a.family.parameters.length + 1 + j.val = a.family.parameters.length + 1 + j.val from rfl, hm2]
    rfl
  -- the constructor's stored type and the plain kinds
  have hst := (a.constructorViews j).storedType
  have hcpl := (a.constructorViews j).parameterCount
  have hctm : w.ctorMember.mtype = policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
          (a.constructorViews j).resultIndices)) := by rw [hcm]; exact hst
  have hfl : w.fields.length = (a.constructorViews j).fields.length := witness_fields_length a w hrec hm j hcm
  have hpeel := w.hpeel
  rw [hctm, show w.nparams + w.fields.length = ((a.constructorViews j).parameters ++
    (a.constructorViews j).fields).length by rw [List.length_append]; omega, peelPis_policyPi] at hpeel
  have hdoms : w.ctorDoms = (a.constructorViews j).parameters ++ (a.constructorViews j).fields :=
    (congrArg Prod.fst (Option.some.inj hpeel)).symm
  have hkinds := w.hkinds
  rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
  have hrhs : den M σ ρ (iotaRhsOf w) = fapps (den M σ ρ w.minor)
      ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams).map
        (den M σ ρ)) := by
    unfold iotaRhsOf
    rw [den_foldApps]
  rw [hrhs]
  have hfdl : (famDataOf a).ctors.length = a.constructors.length := famDataOf_ctors_length a
  have hnfj : nfOf (famDataOf a) j.val = (a.constructorViews j).fields.length := by
    unfold nfOf; rw [famDataOf_ctor a j]
  cases hd : M.dec (evalTotal (σOf (w.ls.map (evalTotal σ))) a.family.resultLevel = 0) with
  | isFalse h0 =>
      -- a Type family: the major premise is the constructor's data value
      have hff := fam_app_fits W _ (famDataOf a) hfamμ ps is (by simp [famDataOf, hpsl, hisl]) hmaj
      obtain ⟨j', xs', hcf', hzd⟩ := famEnd_type_mem W _ (famDataOf a) ps is (by simpa [famDataOf] using hisl) h0 hff.2
      have hmne : ¬ Equiv (den M σ ρ (ctorMajor w)) pempty := fun h => dataVal_ne_pempty j' xs' (hzd.symm.trans h)
      have hmajV : den M σ ρ (ctorMajor w) =
          fapps (M.μ w.ctorRef (w.lsC.map (evalTotal σ))) (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ)) := by
        unfold ctorMajor ctorSpine
        rw [den_foldApps, List.map_append]
        rfl
      rw [hst] at hctorμ
      have hlenC : (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ)).length =
          ((a.constructorViews j).parameters ++ (a.constructorViews j).fields).length := by
        simp [w.hctorParams, hnp, hcpl, hfl]
      have hneC : ¬ Equiv (fapps (piLam M (σOf (w.lsC.map (evalTotal σ))) (ctorEnd M (σOf (w.lsC.map (evalTotal σ)))
          (famDataOf a) j.val (a.constructorViews j).fields.length) (fun _ => pempty)
          (policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
            (foldApps (.const a.family.ref (policyFamilyLevels a.family))
              (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
                (a.constructorViews j).resultIndices))))
          (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ))) pempty := fun h =>
        hmne (by rw [hmajV]; exact (fapps_congr hctorμ _).trans h)
      have hfitC := fits_of_fapps_ne M _ (ctorEnd_resp M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
        (a.constructorViews j).fields.length) _ _ (fun _ => pempty) _ hlenC hneC
      have heqC := fapps_piLam M _ (ctorEnd_resp M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
        (a.constructorViews j).fields.length) (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
            (a.constructorViews j).resultIndices)) _ (fun _ => pempty) _ hfitC
      rw [piLam_foldApps_const] at heqC
      have h0C : ¬ evalTotal (σOf (w.lsC.map (evalTotal σ))) a.family.resultLevel = 0 := fun h => h0 (huni.mpr h)
      have hzv : Equiv (den M σ ρ (ctorMajor w)) (dataVal j.val (w.fields.map (den M σ ρ))) := by
        rw [hmajV]
        refine (fapps_congr hctorμ _).trans (heqC.trans ?_)
        unfold ctorEnd cond
        cases hd' : M.dec (evalTotal (σOf (w.lsC.map (evalTotal σ))) (famDataOf a).resLevel = 0) with
        | isTrue h => exact absurd h h0C
        | isFalse _ =>
            show Equiv (dataVal j.val (lastVals _ _)) _
            rw [push_append, show (a.constructorViews j).fields.length = (w.fields.map (den M σ ρ)).length by
              rw [List.length_map, hfl], lastVals_push]
            exact Equiv.rfl
      -- the left-hand side: the recursor's value at the data value
      have hR : Equiv (recEnd M (σOf (w.ls.map (evalTotal σ))) (famDataOf a)
          (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) (fun _ => pempty)))
          (fapps (ms.getD j.val pempty) (ihArgs a.family.ref (recCore M (famDataOf a) ms)
            (a.constructorViews j).fields (w.fields.map (den M σ ρ)))) := by
        unfold recEnd cond
        cases hd' : M.dec (evalTotal (σOf (w.ls.map (evalTotal σ))) (famDataOf a).resLevel = 0) with
        | isTrue h => exact absurd h h0
        | isFalse _ =>
            show Equiv (recCore M (famDataOf a) (minorsOf (famDataOf a).indices.length (famDataOf a).ctors.length
              (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) (fun _ => pempty)))
              (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) (fun _ => pempty) 0)) _
            rw [minorsOf_env ps mo ms is _ _ (by rw [hmsl, hfdl]) (by simpa [famDataOf] using hisl), push_cons_eq]
            have hchL : ihChildL (famDataOf a).fref (dataVal j.val (w.fields.map (den M σ ρ)))
                (ctorFieldsOf (famDataOf a) j.val) (w.fields.map (den M σ ρ)) := by
              rw [ctorFieldsOf_famDataOf a j]
              exact ihChildL_of_analyze _ _ _ _ hkinds
            refine (recCore_data M (famDataOf a) ms hzv (by rw [hfdl]; exact hjk)
              (by rw [List.length_map, hfl, hnfj]) (ihChildL_congr' hzv.symm _ _ hchL)).trans ?_
            rw [ctorFieldsOf_famDataOf a j]
            exact Equiv.rfl
      -- the constructor telescope after the recursor-side parameters, read semantically
      have hsem : SemTel M σ ρ w.ctorAfterParams (a.constructorViews j).fields
          (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
          (push ((w.preMajor.take w.nparams).map (den M σ ρ)) ρ) := by
        have h1 := w.hctorAfter
        rw [hctm] at h1
        have hpl : (w.preMajor.take w.nparams).length = (a.constructorViews j).parameters.length := by
          rw [List.length_take, w.hpre, hcpl, hnp]; omega
        exact SemTel.applyTel (w.preMajor.take w.nparams) (a.constructorViews j).parameters _ hpl _ _
          (semTel_instantiateLevels M σ ρ w.ls _ _) h1
      -- the redex's level valuation agrees with the model's below the family's arity
      have hLlen : a.family.member.arity ≤ (w.ls.map (evalTotal σ)).length := by
        rw [List.length_map, w.hlsLen, hm, a.recursorArity]
        generalize a.policy = p
        cases p with
        | anySort => exact Nat.le_succ _
        | propOnly => exact Nat.le_refl _
      have hσ : ∀ i, i < a.family.member.arity →
          (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i)) i = σOf (w.ls.map (evalTotal σ)) i := by
        intro i hi
        have hi' : i < (w.ls.map (evalTotal σ)).length := Nat.lt_of_lt_of_le hi hLlen
        show ((w.ls.map (evalTotal σ))[i]?).getD (σ i) = (w.ls.map (evalTotal σ)).getD i 0
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
        rfl
      have hpsT : (w.preMajor.take w.nparams).map (den M σ ρ) = ps := by
        rw [List.map_take, hnp, hps]
      -- the recursive calls
      have hcall : ∀ (k : Nat) (x A : Expr Nat) (idx : List (Expr Nat)), w.fields[k]? = some x →
          w.kinds[k]? = some .directRec →
          (a.constructorViews j).fields[k]? = some (foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals w.nparams (0 + k) ++ idx)) → idx.length = a.family.indices.length →
          (familyIdx w.nparams A).map (den M σ ρ) = idx.map (den M (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
            (push ((w.fields.take k).map (den M σ ρ)) (push ((w.preMajor.take w.nparams).map (den M σ ρ)) ρ))) →
          Equiv (den M σ ρ (recCallField (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors x A))
            (recCore M (famDataOf a) ms (den M σ ρ x)) := by
        intro k x A idx hx hkk hF hidxl hidxD
        rw [Nat.zero_add, hnp] at hF
        rw [hpsT] at hidxD
        obtain ⟨hFk, hFk'⟩ := List.getElem?_eq_some_iff.mp hF
        -- the field's value lies in the family at the recursor's parameters and the field's indices
        obtain ⟨c, hc, htel, _⟩ := hcf'
        have hjj : j' = j.val := by
          have h2 := ordPair_equiv (ordPair_equiv (hzd.symm.trans hzv)).2
          exact ord_inj h2.1
        subst hjj
        rw [famDataOf_ctor a j] at hc
        have hcc := Option.some.inj hc
        subst hcc
        have hxl : xs'.length = (w.fields.map (den M σ ρ)).length := by rw [htel.length, List.length_map, hfl]
        have hLx : LEq xs' (w.fields.map (den M σ ρ)) := (dataVal_inj hxl (hzd.symm.trans hzv)).2
        have hget := TelFits_get _ _ xs' htel k hFk
        have hkl : (xs'.take k).length = k := by
          rw [List.length_take, hxl, List.length_map, hfl]; exact Nat.min_eq_left (Nat.le_of_lt hFk)
        have hkl' : ((w.fields.take k).map (den M σ ρ)).length = k := by
          rw [List.length_map, List.length_take, hfl]; exact Nat.min_eq_left (Nat.le_of_lt hFk)
        have hpe : push (xs'.take k) (push ps (fun _ => pempty)) = push (ps ++ xs'.take k) (fun _ => pempty) :=
          (push_append ps _ _).symm
        have hdp : (policyParameterLocals a.family.parameters.length k).map
            (den M (σOf (w.ls.map (evalTotal σ))) (push (xs'.take k) (push ps (fun _ => pempty)))) = ps := by
          have h := den_paramLocals M (σOf (w.ls.map (evalTotal σ))) ps (xs'.take k) (fun _ => pempty)
          rw [hpsl, hkl, ← hpe] at h
          exact h
        have hFk2 : ((a.constructorViews j).fields)[k]'hFk = foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals a.family.parameters.length k ++ idx) := hFk'
        rw [hFk2, den_foldApps, List.map_append, hdp] at hget
        -- the call's indices are the field's, read below the fields before it
        have hbC : exprLevelsBounded a.family.member.arity w.ctorMember.mtype = true := by rw [hcm]; exact hlvC
        rw [hctm] at hbC
        have hbF := (levelsBounded_policyPi _ _ _ hbC).1 _ (List.mem_append_right _ (List.getElem_mem hFk))
        rw [hFk2] at hbF
        have hcl := w.hctorClosed
        rw [hctm] at hcl
        have hcF := lift_policyPi_append_fixed _ _ _ 0 hcl k hFk
        rw [hFk2, Nat.zero_add, hcpl] at hcF
        have hLe : ∀ e, e ∈ idx →
            Equiv (den M (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
              (push ((w.fields.take k).map (den M σ ρ)) (push ps ρ)) e)
              (den M (σOf (w.ls.map (evalTotal σ))) (push (xs'.take k) (push ps (fun _ => pempty))) e) := by
          intro e he
          have heF : e ∈ policyParameterLocals a.family.parameters.length k ++ idx := List.mem_append_right _ he
          rw [den_levels_agree M hσ e ((levelsBounded_foldApps _ _ _ hbF).2 e heF)]
          have hle := (lift_foldApps_fixed _ _ _ hcF).2 e heF
          rw [den_cutoff M _ e (a.family.parameters.length + k)
            (fun c' hc' => lift_closed_gen e _ hle c' 1 hc') _ (push ((w.fields.take k).map (den M σ ρ))
              (push ps (fun _ => pempty))) (fun i hi => push_push_agree _ _ _ _ i (by rw [hkl', hpsl]; exact hi))]
          refine den_congr M _ e (push_congr ?_ (fun _ => Equiv.rfl))
          rw [List.map_take]
          exact (LEq.take hLx k).symm
        have hLidx : LEq ((familyIdx w.nparams A).map (den M σ ρ))
            (idx.map (den M (σOf (w.ls.map (evalTotal σ))) (push (xs'.take k) (push ps (fun _ => pempty))))) := by
          rw [hidxD]; exact LEq_map_of idx hLe
        have hxk : Equiv (xs'.getD k pempty) (den M σ ρ x) := by
          have := LEq_getD hLx k
          refine this.trans ?_
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]
          exact Equiv.rfl
        obtain ⟨is', his'⟩ : ∃ is', (familyIdx w.nparams A).map (den M σ ρ) = is' := ⟨_, rfl⟩
        rw [his'] at hLidx
        have hisl' : is'.length = a.family.indices.length := by
          rw [hLidx.length, List.length_map, hidxl]
        have hxmem : den M σ ρ x ∈ Ed M (fapps (M.μ a.family.ref
            ((policyFamilyLevels a.family).map (evalTotal (σOf (w.ls.map (evalTotal σ)))))) (ps ++ is')) :=
          mem_congr_left hxk (mem_congr_right (ed_congr M (fapps_congr_args _ (LEq_append (LEq.refl ps)
            hLidx.symm))) hget)
        -- the call's arguments fit the recursor's telescope
        obtain ⟨hffit, _⟩ := fam_app_fits W _ (famDataOf a) hfamμ ps is'
          (by simp only [famDataOf, List.length_append, hpsl, hisl']) hxmem
        obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hffit
        have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl]; rfl)).1
        subst hxa
        have hxb : xb = is' := (List.append_cancel_left hxab).symm
        subst hxb
        have hfidx : TelFits M (σOf (w.ls.map (evalTotal σ))) (liftFields (a.minorTypes.length + 1) a.family.indices 0)
            (push (xa ++ mo :: ms) (fun _ => pempty)) xb := by
          have e1 : push (xa ++ mo :: ms) (fun _ => pempty) =
              push ([] : List PSet) (push (mo :: ms) (push xa (fun _ => pempty))) := by
            rw [push_append]; rfl
          have e2 : a.minorTypes.length + 1 = (mo :: ms).length := by
            rw [List.length_cons, hmsl, hk]
          rw [e1, e2, show (0 : Nat) = ([] : List PSet).length from rfl]
          exact (TelFits_liftFields M _ (mo :: ms) (push xa (fun _ => pempty)) a.family.indices [] xb).mpr hfb
        have hpd : recPreDomsOf a = (a.family.parameters ++ policyMotiveType a.family a.policy :: a.minorTypes) ++
            liftFields (a.minorTypes.length + 1) a.family.indices 0 := by
          unfold recPreDomsOf; simp only [List.append_assoc, List.cons_append]
        have hf1' := hf1
        rw [hpd, hsplit, show xa ++ mo :: (ms ++ is) = (xa ++ mo :: ms) ++ is by
          simp only [List.append_assoc, List.cons_append]] at hf1'
        obtain ⟨ya, yb, hyab, hya, _⟩ := TelFits_split _ _ _ _ hf1'
        have hya' : ya = xa ++ mo :: ms := (List.append_inj hyab.symm (by
          rw [hya.length]
          simp only [List.length_append, List.length_cons, hpsl, hmsl, hk])).1
        subst hya'
        have hmajx : den M σ ρ x ∈ Ed M (den M (σOf (w.ls.map (evalTotal σ)))
            (push ((xa ++ mo :: ms) ++ xb) (fun _ => pempty)) (recMajorOf a)) := by
          rw [show (xa ++ mo :: ms) ++ xb = xa ++ mo :: (ms ++ xb) by simp only [List.append_assoc, List.cons_append],
            den_recMajor M _ a xa mo ms xb _ hpsl (by rw [hmsl, hk]) hisl']
          exact hxmem
        have hfit2 : TelFits M (σOf (w.ls.map (evalTotal σ))) (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty)
            ((xa ++ mo :: ms) ++ xb ++ [den M σ ρ x]) := by
          rw [hpd]
          exact TelFits.append (TelFits.append hya hfidx) ⟨hmajx, trivial⟩
        -- the recursive call is the recursor's value at the field
        have hpre' : (recPrefix w.preMajor w.nparams w.nMinors).map (den M σ ρ) = xa ++ mo :: ms := by
          unfold recPrefix
          rw [List.map_take, hsplit, hnp, hnM, show xa ++ mo :: (ms ++ is) = (xa ++ mo :: ms) ++ is by
            simp only [List.append_assoc, List.cons_append]]
          exact List.take_left' (by simp only [List.length_append, List.length_cons, hpsl, hmsl]; omega)
        have hden : den M σ ρ (recCallField (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors x A) =
            fapps (M.μ r (w.ls.map (evalTotal σ))) ((xa ++ mo :: ms) ++ xb ++ [den M σ ρ x]) := by
          unfold recCallField
          rw [den_foldApps, List.map_append, List.map_append, hpre', his', hrec]
          rfl
        rw [hden]
        have heq2 := fapps_piLam M (σOf (w.ls.map (evalTotal σ))) (recEnd_resp M (σOf (w.ls.map (evalTotal σ)))
          (famDataOf a)) (recResultOf a) (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty) _ hfit2
        rw [show recResultOf a = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1)) _ from rfl,
          piLam_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h)] at heq2
        refine (fapps_congr hrecμ _).trans (heq2.trans ?_)
        have henv2 : (xa ++ mo :: ms) ++ xb ++ [den M σ ρ x] = xa ++ mo :: (ms ++ (xb ++ [den M σ ρ x])) := by
          simp only [List.append_assoc, List.cons_append]
        rw [henv2]
        unfold recEnd cond
        cases hd' : M.dec (evalTotal (σOf (w.ls.map (evalTotal σ))) (famDataOf a).resLevel = 0) with
        | isTrue h => exact absurd h h0
        | isFalse _ =>
            show Equiv (recCore M (famDataOf a) (minorsOf (famDataOf a).indices.length (famDataOf a).ctors.length
              (push (xa ++ mo :: (ms ++ (xb ++ [den M σ ρ x]))) (fun _ => pempty)))
              (push (xa ++ mo :: (ms ++ (xb ++ [den M σ ρ x]))) (fun _ => pempty) 0)) _
            rw [minorsOf_env xa mo ms xb _ _ (by rw [hmsl, hfdl]) (by simpa [famDataOf] using hisl'), push_cons_eq]
            exact Equiv.rfl
      have hRHS := rhsArgs_den M σ ρ (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors a.family.ref
        a.family.indices.length (policyFamilyLevels a.family) (recCore M (famDataOf a) ms)
        (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i)) w.fields w.kinds w.ctorAfterParams
        (a.constructorViews j).fields 0 _ hsem hkinds (by rw [hnp]; exact hrf) hfl hcall
      rw [hmin] at hR
      exact hL.trans (hR.trans (fapps_congr_args _ hRHS).symm)
  | isTrue h0 =>
      cases hpol : a.policy with
      | propOnly =>
          have := recEnd_propOnly M (σOf (w.ls.map (evalTotal σ))) (famDataOf a)
            (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) (fun _ => pempty)) h0 hpol
          rw [this] at hL
          exact absurd hL hne
      | anySort =>
          have hs : EliminationSelection a.family.resultLevel a.constructors.length
              (∀ i, (a.constructorViews i).AllFieldsSafe) .anySort := by
            rw [← hpol]; exact a.selected
          have hk1 : a.constructors.length = 1 := by
            rcases (EliminationSelection.anySort_iff _ _ _).mp hs with ht | ⟨_, hk0 | ⟨hk1, _⟩⟩
            · exact absurd h0 (Nat.pos_iff_ne_zero.mp (ht _))
            · omega
            · exact hk1
          have hj0 : j.val = 0 := by omega
          obtain ⟨hfree, hrest⟩ := (hpf h0 hpol).resolve_right fun hemp => by
            -- an empty family: the major premise cannot lie in it
            obtain ⟨⟨_, _, hcf⟩, _⟩ := famEnd_prop_mem W _ (famDataOf a) ps is (by simpa [famDataOf] using hisl) h0
              (fam_app_fits W _ (famDataOf a) hfamμ ps is (by simp [famDataOf, hpsl, hisl]) hmaj).2
            exact hemp _ _ _ _ hcf
          have hfd : (famDataOf a).ctors = [((a.constructorViews j).fields, (a.constructorViews j).resultIndices)] := by
            have hc := famDataOf_ctor a j
            have h2 : (famDataOf a).ctors[0]? =
                some ((a.constructorViews j).fields, (a.constructorViews j).resultIndices) := by
              have := hc; simp only [hj0] at this; exact this
            have hl := hfdl
            rw [hk1] at hl
            match hcs : (famDataOf a).ctors, hl with
            | [c], _ =>
                rw [hcs] at h2
                simp at h2
                rw [h2]
          have hR := recEnd_prop_single M (σOf (w.ls.map (evalTotal σ))) (famDataOf a) ps mo ms is
            (den M σ ρ (ctorMajor w)) (fun _ => pempty) (by rw [hmsl, hfdl]) (by simpa [famDataOf] using hisl)
            h0 hpol _ hfd
          -- the right-hand side's arguments are the fields
          have hplain : w.kinds = (a.constructorViews j).fields.map fun _ => RecKind.plain := by
            have := analyzeFields_plain a.family.ref _ hfree
            rw [hkinds] at this
            exact Option.some.inj this
          have hrw : rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors w.fields w.kinds
              w.ctorAfterParams = w.fields :=
            rhsArgs_plain _ _ _ _ _ _ (fun k hk => by
              rw [hplain] at hk; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hk; rfl) _
          rw [hrw]
          rw [hrw] at hspine
          rw [hj0] at hmin
          cases hrest with
          | inr hagree =>
              -- the field/index agreement is given
              rw [hmin] at hR
              exact hL.trans (hR.trans (hagree ps mo ms is hsplit hpsl hmsl hisl hf1 _ hfd))
          | inl hn =>
          obtain ⟨hnorev, ⟨b, hmt⟩, hprop⟩ := hn
          rw [recon_none _ is hnorev] at hR
          -- the minor lies in its type, a telescope of propositions
          have hf1' := hf1
          rw [hsplit] at hf1'
          unfold recPreDomsOf at hf1'
          obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hf1'
          have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl])).1
          subst hxa
          have hxb : xb = mo :: (ms ++ is) := (List.append_cancel_left hxab).symm
          subst hxb
          obtain ⟨ya, yb, hyab, hya, _⟩ := TelFits_split _ _ _ _ hfb.2
          have hya' : ya = ms := (List.append_inj hyab.symm (by rw [hya.length, hmsl, hk])).1
          subst hya'
          have hmt0 : a.minorTypes[0]'(by rw [hk, hk1]; exact Nat.zero_lt_one) =
              policyPi (liftFields 1 (a.constructorViews j).fields 0) b := by
            have e1 : a.minorTypes[j.val]? = a.minorTypes[0]? := by rw [hj0]
            have h1 := e1.symm.trans hmt
            have e2 : 1 + j.val = 1 := by omega
            rw [e2] at h1
            exact (List.getElem?_eq_some_iff.mp h1).2
          have hg := TelFits_get a.minorTypes _ ya hya 0 (by rw [hk, hk1]; exact Nat.zero_lt_one)
          rw [hmt0] at hg
          have hPT := propTel_liftFields M (σOf (w.ls.map (evalTotal σ))) [mo] (push xa (fun _ => pempty))
            (a.constructorViews j).fields [] (hprop xa hfa)
          rw [hmin] at hg hR
          have hlen : (w.fields.map (den M σ ρ)).length = (liftFields 1 (a.constructorViews j).fields 0).length := by
            rw [List.length_map, liftFields_length', hfl]
          have hsp := spine_proofs M (σOf (w.ls.map (evalTotal σ))) b _ _ _ _ hlen hg hPT hspine
          have e : (a.constructorViews j).fields.map (fun _ => pempty) = (w.fields.map (den M σ ρ)).map fun _ => pempty := by
            simp only [List.map_const', List.map_map, Function.comp_def, List.length_map, hfl]
          rw [e] at hR
          exact hL.trans (hR.trans hsp.symm)

end PSet

end Rcic.F3
