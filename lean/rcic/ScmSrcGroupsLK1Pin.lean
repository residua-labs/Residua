import Lean
import rcic.ScmSrcGroupsEnvWf
open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Rcic.Scm.SrcG

/-! IDX-R2 measurement harness on the REAL slot-140 `vaPair`. `vaIdxReport`
records, in order:

* witness built (`wVA?.isSome`)
* 11a on that witness (`aW`)
* 11b `declaredIdxSrc` (`pos`; `none` is not `false`)
* 11c witness (`cW`) — `none` when 11b returned no positions
* 11d witness (`dW`) — `none` when 11b returned no positions

`CA` is `w.ctorAfterParams`. This is a MEASUREMENT, not a settlement. The
Src supplier `declaredIdxSrc` is the compound-provenance producer: on the
real slot-140 `vaPair` it returns `some` (unlike `declaredIdxPositions`,
which returns `none`), so 11b→11c→11d now resolve.

### RETIRED (by RULE, IDX-R2)

An earlier pin on this slot refuted `RecursorGroupIdxAdmitted (envPre 143)
143 recValueAt` through `walkVA` / `walkVA_false` / `idxValueAt_false` /
`blockedHidxAdm_uninhabited`. That refutation is RETIRED (text kept below)
because its interface changed: (1) 11a `recIdxFromSpineWalk` already
accepted the compound index after IDX-R1's `idxFamFree`; (2) the index
`mkBound (mkRef 3 16 d) b (cctP …)` is FAMILY-FREE, so the Src supplier
`declaredIdxSrc` builds a provenance tree for it and 11c/11d accept it.
Only the Nat supplier `declaredIdxPositions` fails — and it fails because
it cannot NAME a compound index, which is not a reason to refuse it. The
first failing condition moves from 11b to none: the real tuple is
`(true, true, some _, some true, some true, _)`. -/

/- RETIRED (IDX-R2, R-Retire): the interface these statements were made over has changed. IotaTyping's index evidence is `IdxSrc` (IDX-R2), and `RecursorGroupIdxAdmitted.typing` now yields `hidxPos` / `hidxTy` / `hidxFuel` over sources, so the refutation cannot be re-proved over the replaced object. Not weakened. That the old counterexample no longer applies is not, by itself, a proof that the new admission is constructible; the positive per-constructor fact is `vaPairAdmittedAt`, and the group is still refused at 139/142 (`valueAtFunRecRefused`).

private def walkVA : Bool :=
  match wVA? with
  | some ⟨w, _⟩ => recIdxFromSpineWalk w.nparams w.nindices (recParamsFields w)
      w.kinds w.ctorAfterParams w.fields
  | none => true

kernel_rfl_theorem walkVA_false : walkVA = false

theorem idxValueAt_false :
    RecursorGroupIdxAdmitted (envPre 143) 143 recValueAt → False := by
  intro h
  have hext : ∀ r' m', (envPre 143).members r' = some m' →
      EP.members r' = some m' := by
    intro r' m' hmem
    by_cases h143 : r' = 143
    · subst h143
      have hn := epFresh
      rw [hn] at hmem
      nomatch hmem
    · show (if r' = 143 then some recValueAt else (envPre 143).members r')
        = some m'
      rw [if_neg h143]
      exact hmem
  have hw : walkVA = false := walkVA_false
  unfold walkVA at hw
  cases hq : wVA? with
  | none => rw [hq] at hw; exact absurd hw (by decide)
  | some wp =>
      rw [hq] at hw
      obtain ⟨w, hr1, hr2⟩ := wp
      have ht := h.typing hext epRec w hr1 hr2
      have hw' : recIdxFromSpineWalk w.nparams w.nindices
          (recParamsFields w) w.kinds w.ctorAfterParams w.fields = false := hw
      have hb := ht.hidxWalk
      rw [hw'] at hb
      exact absurd hb (by decide)

theorem blockedHidxAdm_uninhabited (B : BlockedHidxAdm) : False :=
  idxValueAt_false B.idxValueAt
-/

private def mkWitVA (E : ResolvedEnv) (cm fm : CheckedMember)
    (hrec : E.members 143 = some recValueAt)
    (hctor : E.members 140 = some cm) (hctorK : cm.mclass = .constructorM)
    (hfam : E.members 133 = some fm) (hfamK : fm.mclass = .inductiveM)
    (hcl : lift 0 1 cm.mtype = cm.mtype)
    (hrcl : lift 0 1 recValueAt.mtype = recValueAt.mtype) :
    Option {w : IotaWitness E // w.recRef = 143 ∧ w.recMember = recValueAt} :=
  let fields : List (Expr Nat) := List.replicate 20 (.sort .zero)
  let preMajor : List (Expr Nat) := List.replicate 12 (.sort .zero)
  match hp : peelPis (0 + fields.length) cm.mtype with
  | none => none
  | some ⟨cd, cr⟩ =>
  match hk : analyzeFields 133 (cd.drop 0) with
  | none => none
  | some kinds =>
  match hr : peelPis (0 + 1 + 9 + 2 + 1) recValueAt.mtype with
  | none => none
  | some ⟨rd, rb⟩ =>
  match hm : preMajor[0 + 1 + 6]? with
  | none => none
  | some minor =>
  match hca : applyTel (preMajor.take 0) (instantiateLevels [] cm.mtype) with
  | none => none
  | some ctap =>
      if h : (0 + fields.length = piCount cm.mtype)
          ∧ (0 + 2 = piCount fm.mtype)
          ∧ (0 + 1 + 9 + 2 + 1 = piCount recValueAt.mtype)
          ∧ kinds.length = fields.length
          ∧ isFamilyApp 133 cr = true
          ∧ rb = foldApps (.bvar (9 + 2 + 1))
              ((List.range 2).reverse.map (fun i => Expr.bvar (i + 1)) ++
                [Expr.bvar 0])
          ∧ rd[0 + 1 + 9 + 2]? = some
              (foldApps (.const 133 ((List.range fm.arity).map Level.param))
                ((List.range 0).reverse.map
                  (fun i => Expr.bvar (i + 2 + 9 + 1)) ++
                 (List.range 2).reverse.map (fun i => Expr.bvar i)))
          ∧ ([] : List Level).length = recValueAt.arity
          ∧ isPiTel kinds.length ctap = true
          ∧ directRecConstHead kinds ctap = true
          ∧ resultConstHead kinds ctap = true
          ∧ preMajor.length = 0 + 1 + 9 + 2
          ∧ 6 < 9 ∧ 140 = 133 + 1 + 6 ∧ 143 = 133 + 1 + 9 then
        let ⟨hnpar, hnidx, hnmin, hlen, hfa, hrb, hmaj, hls, hct, hfm,
            hrt, hpre, hidx, hci, hri⟩ := h
        let w : IotaWitness E :=
          { recRef := 143, ctorRef := 140, ls := [], lsC := [],
                 recMember := recValueAt, ctorMember := cm,
                 hrec, hctor, hrecK := rfl, hctorK,
                 preMajor, fields, ctorParams := [], kinds, minor,
                 hlen, familyRef := 133, famMember := fm, hfam, hfamK,
                 nparams := 0, nindices := 2, nMinors := 9, ctorIdx := 6,
                 hctorParams := rfl, hnpar, hnidx, hnmin, hidx,
                 hctorIdx := hci, hrecIdx := hri, hpre, hminor := hm,
                 ctorDoms := cd, ctorResult := cr, hpeel := hp,
                 hfamApp := hfa, hkinds := hk,
                 recDoms := rd, recBody := rb, hpeelRec := hr,
                 hrecBody := hrb, hmajorTy := hmaj,
                 hrecClosed := hrcl, hctorClosed := hcl,
                 hlsLen := hls, ctorAfterParams := ctap,
                 hctorAfter := hca, hctorTel := hct,
                 hfamTel := hfm, hresTel := hrt }
        some ⟨w, rfl, rfl⟩
      else none

private def EP : ResolvedEnv := extendEnv (envPre 143) 143 recValueAt

kernel_rfl_theorem epCtor : EP.members 140 = some mVaPair
kernel_rfl_theorem epFam : EP.members 133 = some mValueAt
kernel_rfl_theorem epRec : EP.members 143 = some recValueAt
kernel_rfl_theorem clCtor : lift 0 1 mVaPair.mtype = mVaPair.mtype
kernel_rfl_theorem clRec : lift 0 1 recValueAt.mtype = recValueAt.mtype

private def wVA? :=
  mkWitVA EP mVaPair mValueAt epRec epCtor rfl epFam rfl clCtor clRec

kernel_rfl_theorem epFresh : (envPre 143).members 143 = none

/-- One kernel reduction. Components are lets in front of the tuple so
whnf computes each conjunct once, including when 11b is `none`. -/
def vaIdxReport :
    Bool × Bool × Option (List (List IdxSrc)) ×
      Option Bool × Option Bool × Option Bool :=
  match wVA? with
  | none => (false, false, none, none, none, none)
  | some ⟨w, _⟩ =>
      let nfields := w.fields.length
      let Sp := bvarSpine (w.nparams + 1 + w.nMinors + nfields)
      let P := Sp.take w.nparams
      let RP := Sp.take (w.nparams + 1 + w.nMinors)
      let F := Sp.drop (w.nparams + 1 + w.nMinors)
      let PF := P ++ F
      let CA := w.ctorAfterParams
      let aW := recIdxFromSpineWalk w.familyRef w.nparams w.nindices
        PF w.kinds CA F
      let pos := declaredIdxSrc w.familyRef w.nparams w.nMinors nfields
        w.kinds CA
      let cW : Option Bool := match pos with
        | none => none
        | some p => some <| recIdxSrcWalk w.familyRef w.nparams
            PF w.kinds CA F p
      let dW : Option Bool := match pos with
        | none => none
        | some p => some <| recIdxTySrcWalk w.familyRef EP
            (instantiateLevels w.ls w.recMember.mtype)
            (instantiateLevels w.ls w.ctorMember.mtype)
            w.nparams (recPrefix w.preMajor w.nparams w.nMinors)
            PF w.kinds CA F p
      (true, aW, pos, cW, dW, some true)

/-! ### 11b→11d POSITIVE evidence on the real slot-140 `vaPair`

`vaIdxReport`'s tuple is the closed computation; these four kernel
reductions read the actual conjuncts off it. `vaIdxReport_pos_isSome`
says the Src supplier `declaredIdxSrc` succeeded (the old Nat supplier
`declaredIdxPositions` returns `none` here); the next two say the Src
match and type walks accept the compound provenance. This is the
positive chain, not a refutation. -/
theorem vaIdxReport_witness : vaIdxReport.1 = true := rfl
theorem vaIdxReport_11a : vaIdxReport.2.1 = true := rfl
theorem vaIdxReport_pos_isSome : (vaIdxReport.2.2.1).isSome = true := rfl
theorem vaIdxReport_11c : vaIdxReport.2.2.2.1 = some true := rfl
theorem vaIdxReport_11d : vaIdxReport.2.2.2.2.1 = some true := rfl

kernel_rfl_theorem vaPairAdmittedAt : recursorGroupAdmittedAt (envPre 143) 143 recValueAt 133 [] 0 0 9 2 6 = true
/-- IDX-R2 S1-d2: the real slot-140 `vaPair` passes every conjunct of the normal admission Bool at the real recursor, compound index included. -/
add_decl_doc vaPairAdmittedAt

kernel_rfl_theorem valueAtFunRecRefused_139 : recursorGroupAdmittedAt (envPre 143) 143 recValueAt 133 [] 0 0 9 2 5 = false
/-- The two function-recursive ValueAt constructors are still refused, by conjunct 3 (R-NoFunRec, #6151). This is a canary for Stage 2. -/
add_decl_doc valueAtFunRecRefused_139
kernel_rfl_theorem valueAtFunRecRefused_142 : recursorGroupAdmittedAt (envPre 143) 143 recValueAt 133 [] 0 0 9 2 8 = false
/-- The two function-recursive ValueAt constructors are still refused, by conjunct 3 (R-NoFunRec, #6151). This is a canary for Stage 2. -/
add_decl_doc valueAtFunRecRefused_142

kernel_rfl_theorem cctFunRecRefused_103 : recursorGroupAdmittedAt (envPre 105) 105 recCCT 96 [] 0 0 8 2 6 = false
/-- The two function-recursive CCT constructors are still refused, by conjunct 3 (R-NoFunRec). This is a canary for Stage 2. -/
add_decl_doc cctFunRecRefused_103
kernel_rfl_theorem cctFunRecRefused_104 : recursorGroupAdmittedAt (envPre 105) 105 recCCT 96 [] 0 0 8 2 7 = false
/-- The two function-recursive CCT constructors are still refused, by conjunct 3 (R-NoFunRec). This is a canary for Stage 2. -/
add_decl_doc cctFunRecRefused_104

#print axioms vaIdxReport_witness
#print axioms vaIdxReport_11a
#print axioms vaIdxReport_pos_isSome
#print axioms vaIdxReport_11c
#print axioms vaIdxReport_11d

open Lean in
private partial def vaKernelNf (env : Environment) (e : Expr) :
    Except KernelException Expr := do
  let e ← Kernel.whnf env {} e
  match e with
  | .app f a =>
      return .app (← vaKernelNf env f) (← vaKernelNf env a)
  | .mdata _ b => vaKernelNf env b
  | .proj n i s =>
      let s ← vaKernelNf env s
      let e' ← Kernel.whnf env {} (.proj n i s)
      if e'.isProj then return e' else vaKernelNf env e'
  | _ => return e

open Lean Elab Command in
elab "kernel_print " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let r ← ofExceptKernelException (vaKernelNf env (.const decl []))
  logInfo m!"VAIDX {decl} ==> {r}"

kernel_print vaIdxReport

end Rcic.Scm.SrcG
