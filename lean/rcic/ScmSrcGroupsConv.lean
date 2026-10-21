import rcic.ScmSrcGroupsWf
import rcic.ScmSrcGroupsKernelRfl

/-! Stage 2b-i: verified conversion. `convBy` is a fuel-bounded,
sound-by-construction converter for the small closed step theory
(δ-unfolding of transparent definitions, literal expansion, β, head
reduction inside an application spine). `inferConv` is `inferSpine2`
with a conversion fallback at `.app`; `checkConv` infers then
converts.  The generic converter uses no `Conv.irr`, no `Conv.eta`,
and no iota; slot 159 (`nthBNilVa`) is the only ι client — explicit
`IotaWitness`es via `iotaTry159` — and slot 160 (`vLBNil`) is the
only irr client — `Conv.irr` at `P = CCT lbRef bytesLB` with both
proofs honestly typed at `P` by `checkConv`. -/

open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-- One conversion step at `a`'s head: δ on a transparent `const`,
literal expansion, β on a redex, each lifted through application
spines by `Conv.app`-congruence against `refl` on the argument. -/
private def headStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (a : Expr Nat) → Option (Σ' a', Conv E n Γ a a')
  | .const r ls =>
      match hm : E.members r with
      | some m =>
          match hb : m.body with
          | some v =>
              if htr : transparent m.mclass = true then
                some ⟨_, .step Γ _ _ (.delta Γ r ls m v hm hb htr)⟩
              else none
          | none => none
      | none => none
  | .lit t => some ⟨_, .step Γ _ _ (.lit Γ t _ (.of t))⟩
  | .app (.lam A body) arg =>
      some ⟨_, .step Γ _ _ (.beta Γ A body arg)⟩
  | .app f x =>
      (headStep f).map fun ⟨f', hf⟩ =>
        ⟨.app f' x, .app Γ _ _ _ _ hf (.refl Γ x)⟩
  | _ => none

/-- Γ-generic iota step table: maps an expression to a one-step
`Conv` (empty by default; slot 159 registers the two `recBL`
witnesses). -/
abbrev IotaTable (E : ResolvedEnv) (n : Nat) :=
  {Γ' : LCtx} → (a : Expr Nat) → Option (Σ' a', Conv E n Γ' a a')

/-- Single-step reducer: head δ/lit/β plus the optional iota table. -/
private def stepAny {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (iot : IotaTable E n) (a : Expr Nat) :
    Option (Σ' a', Conv E n Γ a a') :=
  headStep a <|> iot a

private theorem eqN_of_eq {l₁ l₂ : Level} (h : l₁ = l₂) : eqN l₁ l₂ :=
  fun _ => h ▸ rfl

private theorem eqNList_of_eq {ls ls' : List Level} (h : ls = ls') :
    eqNList ls ls' := by
  subst h; induction ls with
  | nil => trivial
  | cons l t ih => exact ⟨fun _ => rfl, ih⟩

/-- Fuel-bounded conversion, sound by construction, with an optional
iota step-table. -/
def convByAux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (iot : IotaTable E n) :
    (fuel : Nat) → (a b : Expr Nat) → Option (Conv E n Γ a b)
  | 0, _, _ => none
  | fuel + 1, a, b =>
      if hab : a = b then
        some (Eq.ndrec (motive := fun x => Conv E n Γ a x)
          (.refl Γ a) hab)
      else
        (match a, b with
         | .app f₁ x₁, .app f₂ x₂ =>
             match convByAux iot fuel f₁ f₂, convByAux iot fuel x₁ x₂ with
             | some h1, some h2 => some (.app Γ _ _ _ _ h1 h2)
             | _, _ => none
         | .pi A₁ B₁, .pi A₂ B₂ =>
             match convByAux iot fuel A₁ A₂,
                   convByAux (Γ := LocalDecl.assumption A₁ :: Γ) iot
                     fuel B₁ B₂ with
             | some hA, some hB => some (.pi Γ _ _ _ _ hA hB)
             | _, _ => none
         | .lam A₁ B₁, .lam A₂ B₂ =>
             match convByAux iot fuel A₁ A₂,
                   convByAux (Γ := LocalDecl.assumption A₁ :: Γ) iot
                     fuel B₁ B₂ with
             | some hA, some hB => some (.lam Γ _ _ _ _ hA hB)
             | _, _ => none
         | .sort l₁, .sort l₂ =>
             if h : l₁ = l₂ then
               some (.sorts Γ _ _ (eqN_of_eq h)) else none
         | .const r ls, .const r' ls' =>
             if h : r = r' ∧ ls = ls' then
               some (Eq.ndrec
                 (motive := fun r' =>
                   Conv E n Γ (.const r ls) (.const r' ls'))
                 (.consts Γ r ls ls' (eqNList_of_eq h.2)) h.1)
             else none
         | _, _ => none)
        <|>
        (match stepAny iot a with
         | some ⟨a', ha⟩ =>
             (convByAux iot fuel a' b).map fun h =>
               .trans Γ _ _ _ ha h
         | none => none)
        <|>
        (match stepAny iot b with
         | some ⟨b', hb⟩ =>
             (convByAux iot fuel a b').map fun h =>
               .trans Γ _ _ _ h (.symm Γ _ _ hb)
         | none => none)

/-- The no-iota converter used for the ordinary slots. -/
def convBy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (fuel : Nat)
    (a b : Expr Nat) : Option (Conv E n Γ a b) :=
  convByAux (fun _ => none) fuel a b

/-- Head-normalize `a` by iterated single steps (`fuel`-bounded);
returns the reached term and the conversion chain. -/
def whnfConvAux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (iot : IotaTable E n) :
    (fuel : Nat) → (a : Expr Nat) → Option (Σ' a', Conv E n Γ a a')
  | 0, a => some ⟨a, .refl Γ a⟩
  | fuel + 1, a =>
      match stepAny iot a with
      | some ⟨a', hs⟩ =>
          match whnfConvAux iot fuel a' with
          | some ⟨a'', hrec⟩ => some ⟨a'', .trans Γ _ _ _ hs hrec⟩
          | none => some ⟨a', hs⟩
      | none => some ⟨a, .refl Γ a⟩

/-- `inferSpine2` plus conversion: whnf-normalizes inferred types when
a `.sort`/`.pi` head is required, and falls back to `convByAux` at
`.app`. -/
def inferConvAux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (iot : IotaTable E n) (fuel : Nat)
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc) :
    (e : Expr Nat) → Option (Σ' T, HasTy E n Γ e T)
  | .bvar i =>
      match h : lookupType Γ i with
      | some T => some ⟨T, .bvar Γ i T h⟩
      | none => none
  | .const r ls =>
      match hm : E.members r with
      | some m =>
          if hl : ls.length = m.arity then
            if hw : ls.all (fun l =>
                decide (eval (fun _ => none) l = none) ||
                  decide (0 < n)) then
              some ⟨instantiateLevels ls m.mtype,
                .const Γ r ls m hm hl (fun l hm' =>
                  levelWf_const_of ((List.all_eq_true.mp hw) l hm'))⟩
            else none
          else none
      | none => none
  | .lit t => some ⟨.const 0 [], hasTyLit h1 h2 t⟩
  | .sort l => some ⟨.sort (.succ l), .sort Γ l⟩
  | .pi A B =>
      match inferConvAux iot fuel h1 h2 A with
      | some ⟨T', hT⟩ =>
          match whnfConvAux iot fuel T' with
          | some ⟨.sort u, hc⟩ =>
              match inferConvAux (Γ := LocalDecl.assumption A :: Γ)
                  iot fuel h1 h2 B with
              | some ⟨V', hV⟩ =>
                  match whnfConvAux (Γ := LocalDecl.assumption A :: Γ)
                      iot fuel V' with
                  | some ⟨.sort v, hc'⟩ =>
                      some ⟨.sort (.imax u v), .pi Γ A u B v
                        (.conv Γ _ _ _ hT hc)
                        (.conv _ _ _ _ hV hc')⟩
                  | _ => none
              | none => none
          | _ => none
      | none => none
  | .lam A b =>
      match inferConvAux iot fuel h1 h2 A with
      | some ⟨T', hT⟩ =>
          match whnfConvAux iot fuel T' with
          | some ⟨.sort u, hc⟩ =>
              match inferConvAux (Γ := LocalDecl.assumption A :: Γ)
                  iot fuel h1 h2 b with
              | some ⟨B, hb⟩ =>
                  some ⟨.pi A B, .lam Γ A u b B
                    (.conv Γ _ _ _ hT hc) hb⟩
              | none => none
          | _ => none
      | none => none
  | .app f a =>
      match inferConvAux iot fuel h1 h2 f with
      | some ⟨Tf, hf⟩ =>
          match whnfConvAux iot fuel Tf with
          | some ⟨.pi A B, hc⟩ =>
              match inferConvAux iot fuel h1 h2 a with
              | some ⟨Ta, ha⟩ =>
                  if heq : Ta = A then
                    some ⟨instantiate0 a B,
                      .app Γ f a A B
                        (.conv Γ _ _ _ hf hc) (heq ▸ ha)⟩
                  else
                    (convByAux iot fuel Ta A).map fun hcv =>
                      ⟨instantiate0 a B,
                        .app Γ f a A B (.conv Γ _ _ _ hf hc)
                          (.conv Γ _ _ _ ha hcv)⟩
              | none => none
          | _ => none
      | none => none
  | _ => none

/-- `inferConvAux` without iota — the ordinary entry point. -/
def inferConv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (fuel : Nat)
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc) :
    (e : Expr Nat) → Option (Σ' T, HasTy E n Γ e T) :=
  inferConvAux (fun _ => none) fuel h1 h2

/-- Type check by inference plus conversion to the expected type. -/
def checkConvAux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (iot : IotaTable E n) (fuel : Nat)
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (e T : Expr Nat) : Option (HasTy E n Γ e T) :=
  match inferConvAux iot fuel h1 h2 e with
  | some ⟨T', hT⟩ =>
      if h : T' = T then
        some (h ▸ hT)
      else
        (convByAux iot fuel T' T).map fun hc => .conv Γ e T' T hT hc
  | none => none

/-- `checkConvAux` without iota. -/
def checkConv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (fuel : Nat)
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (e T : Expr Nat) : Option (HasTy E n Γ e T) :=
  checkConvAux (fun _ => none) fuel h1 h2 e T

/-! ### Slot 159 (`nthBNilVa`): `recBL` iota witnesses

The two ι-steps needed are `recBL` at `blNil` (the result) and at
`blCons` (inside the minor-premises' expected types). `mkWitBL`
constructs the `IotaWitness` generically from a redex's spine; every
proof field is discharged against the concrete members by the
single conjunctive `if`. -/

/-- App-spine head and argument list. -/
private def spineOf : Expr Nat → (Expr Nat × List (Expr Nat))
  | .app f a => let ⟨h, as⟩ := spineOf f; (h, as ++ [a])
  | e => (e, [])

/-- Witness-builder for `BL.rec` redexes in `envPre 159`:
`preMajor = [motive, minorNil, minorCons]` (nparams = nindices = 0),
`fields` = the major's constructor arguments. -/
private def mkWitBL (ctorIdx ctorRef : Nat) (cm : CheckedMember)
    (hctor : (envPre 159).members ctorRef = some cm)
    (hctorK : cm.mclass = .constructorM)
    (hcl : lift 0 1 cm.mtype = cm.mtype)
    (ls lsC : List Level) (preMajor fields : List (Expr Nat)) :
    Option (IotaWitness (envPre 159)) :=
  match hp : peelPis (0 + fields.length) cm.mtype with
  | none => none
  | some ⟨cd, cr⟩ =>
  match hk : analyzeFields 34 (cd.drop 0) with
  | none => none
  | some kinds =>
  match hr : peelPis (0 + 1 + 2 + 0 + 1) recBL.mtype with
  | none => none
  | some ⟨rd, rb⟩ =>
  match hm : preMajor[0 + 1 + ctorIdx]? with
  | none => none
  | some minor =>
  match hca : applyTel (preMajor.take 0)
      (instantiateLevels ls cm.mtype) with
  | none => none
  | some ctap =>
      if h : (fields.length = piCount cm.mtype)
          ∧ ctorIdx < 2 ∧ ctorRef = 34 + 1 + ctorIdx
          ∧ kinds.length = fields.length
          ∧ isFamilyApp 34 cr = true
          ∧ rb = .app (.bvar 3) (.bvar 0)
          ∧ rd[0 + 1 + 2 + 0]? = some (.const 34 [])
          ∧ ls.length = recBL.arity
          ∧ isPiTel kinds.length ctap = true
          ∧ directRecConstHead kinds ctap = true
          ∧ resultConstHead kinds ctap = true
          ∧ preMajor.length = 0 + 1 + 2 + 0 then
        let ⟨hpar, hidx, hci, hlen, hfa, hrb, hmaj, hls, hct, hfm,
            hrt, hpre⟩ := h
        some { recRef := 37, ctorRef, ls, lsC,
               recMember := recBL, ctorMember := cm,
               hrec := rfl, hctor, hrecK := rfl, hctorK,
               preMajor, fields, ctorParams := [], kinds, minor,
               hlen, familyRef := 34, famMember := mBL,
               hfam := rfl, hfamK := rfl,
               nparams := 0, nindices := 0, nMinors := 2,
               ctorIdx, hctorParams := rfl,
               hnpar := (Nat.zero_add _).trans hpar,
               hnidx := rfl, hnmin := rfl,
               hidx, hctorIdx := hci, hrecIdx := rfl,
               hpre, hminor := hm,
               ctorDoms := cd, ctorResult := cr, hpeel := hp,
               hfamApp := hfa, hkinds := hk,
               recDoms := rd, recBody := rb, hpeelRec := hr,
               hrecBody := hrb, hmajorTy := hmaj,
               hrecClosed := rfl, hctorClosed := hcl,
               hlsLen := hls, ctorAfterParams := ctap,
               hctorAfter := hca, hctorTel := hct,
               hfamTel := hfm, hresTel := hrt }
      else none

/-- The iota step-table for `envPre 159`: recognizes `BL.rec`
(`const 37`) applications whose major is a `blNil`/`blCons`
application, builds the witness, and emits the `Step.iota`
conversion. -/
private def iotaTry159 {Γ : LCtx} (a : Expr Nat) :
    Option (Σ' a', Conv (envPre 159) 1 Γ a a') :=
  let ⟨hd, args⟩ := spineOf a
  match hd, args.getLast? with
  | .const 37 ls, some major =>
      let pre := args.dropLast
      let ⟨mhd, margs⟩ := spineOf major
      match mhd with
      | .const 35 lsC =>
          (mkWitBL 0 35 mBlNil rfl rfl rfl ls lsC pre []).bind fun w =>
            if h : iotaLhsOf w = a then
              some ⟨_, Eq.ndrec
                (motive := fun x => Conv (envPre 159) 1 Γ x (iotaRhsOf w))
                (.step Γ _ _ (.iota Γ _ _ (.of w))) h⟩
            else none
      | .const 36 lsC =>
          match margs with
          | [x, t] =>
              (mkWitBL 1 36 mBlCons rfl rfl rfl ls lsC pre [x, t]).bind
                fun w =>
                if h : iotaLhsOf w = a then
                  some ⟨_, Eq.ndrec
                    (motive := fun x => Conv (envPre 159) 1 Γ x
                      (iotaRhsOf w))
                    (.step Γ _ _ (.iota Γ _ _ (.of w))) h⟩
                else none
          | _ => none
      | _ => none
  | _, _ => none

private def inf159 (e : Expr Nat) :=
  inferConvAux (n := 1) iotaTry159 (E := envPre 159) (Γ := ([] : LCtx))
    65536 rfl rfl e

private def cnv159 (a b : Expr Nat) :=
  convByAux (n := 1) iotaTry159 (E := envPre 159) (Γ := ([] : LCtx))
    65536 a b

kernel_rfl_theorem inf159ok : (inf159 (mNthBNilVa.body.getD
    (.sort .zero))).isSome = true

private def chk159 (e T : Expr Nat) :=
  checkConvAux (n := 1) iotaTry159 (E := envPre 159) (Γ := ([] : LCtx))
    65536 rfl rfl e T

kernel_rfl_theorem chkThm159 : (chk159 (mNthBNilVa.body.getD
    (.sort .zero)) mNthBNilVa.mtype).isSome = true

/-- The stored `nthBNilVa` theorem body, typed at `HasTy (envPre 159)
1 []` — `n = 1` because `recBL`'s `ls = [.succ .zero]` needs a
positive level bound in `HasTy.const`'s `hwf`. -/
def tyThm159 : HasTy (envPre 159) 1 []
    (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype :=
  Option.get
    (chk159 (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype)
    chkThm159

/-! ### Slot 160 (`vLBNil`): `Conv.irr` for the stored proof

The inferred `mkBound` argument carries `cctL … cctBoolPf` where the
stored type carries `cctLbPf` (a `theoremM` — not δ-transparent).
The two are convertible only by `Conv.irr`: both are honestly typed
at the Prop `CCT lbRef bytesLB`. Everything else is δ + congruence
through `convByAux`. -/

private def noIota160 : IotaTable (envPre 160) 1 := fun _ => none
private def inf160 (e : Expr Nat) :=
  inferConvAux (n := 1) noIota160 (E := envPre 160) (Γ := ([] : LCtx))
    65536 rfl rfl e
private def cnv160 (a b : Expr Nat) :=
  convByAux (n := 1) noIota160 (E := envPre 160) (Γ := ([] : LCtx))
    65536 a b
private def chk160 (e T : Expr Nat) :=
  checkConvAux (n := 1) noIota160 (E := envPre 160) (Γ := ([] : LCtx))
    65536 rfl rfl e T

/-- `lbRef = mkRef 3 16 digestLB`, as an expression. -/
private def mkRefE160 : Expr Nat :=
  mLbRef.body.getD (.sort .zero)
/-- The `cctL` application: `cctL boolRef bytesB bytesLB digestLB
bcLB daLB cctBoolPf`. -/
private def cctLapp160 : Expr Nat :=
  mCctLbPf.body.getD (.sort .zero)
/-- The irr Prop: `CCT lbRef bytesLB`. -/
private def p160 : Expr Nat :=
  .app (.app (.const 96 []) (.const 122 [])) (.const 21 [])

kernel_rfl_theorem chk160_ref :
    (cnv160 mkRefE160 (.const 122 [])).isSome = true
kernel_rfl_theorem chk160_p :
    (chk160 cctLapp160 p160).isSome = true
kernel_rfl_theorem chk160_P :
    (chk160 p160 (.sort .zero)).isSome = true
kernel_rfl_theorem chk160_q :
    (chk160 (.const 123 []) p160).isSome = true

/-- `cctL … cctBoolPf ≡ cctLbPf` by proof irrelevance. -/
private def convIrr160 :
    Conv (envPre 160) 1 [] cctLapp160 (.const 123 []) :=
  .irr _ p160 _ _
    (Option.get (chk160 p160 (.sort .zero)) chk160_P)
    (Option.get (chk160 cctLapp160 p160) chk160_p)
    (Option.get (chk160 (.const 123 []) p160) chk160_q)

/-- `mkBound`-unfold of `boundListBool`, moved to the right side. -/
private def convBlb160 :
    Conv (envPre 160) 1 []
      (instantiateLevels [] (mBoundListBool.body.getD (.sort .zero)))
      (.const 124 []) :=
  .symm _ _ _ (.step _ _ _
    (.delta _ _ _ _ _ rfl rfl rfl))

/-- The `mkBound` argument conversion: congruence on ref/bytes, `irr`
on the proof. -/
private def convX160 :
    Conv (envPre 160) 1 []
      (.app (.app (.app (.const 107 []) mkRefE160) (.const 21 []))
        cctLapp160)
      (.const 124 []) :=
  .trans _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.refl _ (.const 107 []))
          (Option.get (cnv160 mkRefE160 (.const 122 [])) chk160_ref))
        (.refl _ (.const 21 [])))
      convIrr160)
    convBlb160

kernel_rfl_theorem inf160ok : (inf160 (mVLBNil.body.getD
    (.sort .zero))).isSome = true

private def infVlb160 :=
  Option.get (inf160 (mVLBNil.body.getD (.sort .zero))) inf160ok

/-- The stored `vLBNil` theorem body, typed at `HasTy (envPre 160) 1
[]` — `n = 1` for consistency with the slot-159 convention (the
`hwf` level bound). -/
def tyThm160 : HasTy (envPre 160) 1 []
    (mVLBNil.body.getD (.sort .zero)) mVLBNil.mtype :=
  .conv _ _ _ _ infVlb160.2
    (.app _ _ _ _ _
      (.app _ _ _ _ _ (.refl _ (.const 133 [])) convX160)
      (.refl _ (.const 149 [])))

/-! slot 113: mCctI64Pf -/
kernel_rfl_theorem chkThm113 :
    (checkConv (E := envPre 113) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype).isSome = true

/-! slot 114: mCctBoolPf -/
kernel_rfl_theorem chkThm114 :
    (checkConv (E := envPre 114) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype).isSome = true

/-! slot 115: mCctStrPf -/
kernel_rfl_theorem chkThm115 :
    (checkConv (E := envPre 115) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype).isSome = true

/-! slot 116: mCctBytesPf -/
kernel_rfl_theorem chkThm116 :
    (checkConv (E := envPre 116) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype).isSome = true

/-! slot 121: mBcLB -/
kernel_rfl_theorem chkThm121 :
    (checkConv (E := envPre 121) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBcLB.body.getD (.sort .zero)) mBcLB.mtype).isSome = true

/-! slot 123: mCctLbPf -/
kernel_rfl_theorem chkThm123 :
    (checkConv (E := envPre 123) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype).isSome = true

/-! slot 144: mVb0 -/
kernel_rfl_theorem chkThm144 :
    (checkConv (E := envPre 144) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mVb0.body.getD (.sort .zero)) mVb0.mtype).isSome = true

/-! slot 145: mVb1 -/
kernel_rfl_theorem chkThm145 :
    (checkConv (E := envPre 145) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mVb1.body.getD (.sort .zero)) mVb1.mtype).isSome = true

/-! slot 153: mLt010 -/
kernel_rfl_theorem chkThm153 :
    (checkConv (E := envPre 153) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mLt010.body.getD (.sort .zero)) mLt010.mtype).isSome = true

/-! slot 154: mNd0 -/
kernel_rfl_theorem chkThm154 :
    (checkConv (E := envPre 154) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mNd0.body.getD (.sort .zero)) mNd0.mtype).isSome = true

/-! slot 155: mBc48S -/
kernel_rfl_theorem chkThm155 :
    (checkConv (E := envPre 155) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBc48S.body.getD (.sort .zero)) mBc48S.mtype).isSome = true

/-! slot 157: mBcLN0 -/
kernel_rfl_theorem chkThm157 :
    (checkConv (E := envPre 157) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBcLN0.body.getD (.sort .zero)) mBcLN0.mtype).isSome = true

/-! slot 158: mBcL0Nil -/
kernel_rfl_theorem chkThm158 :
    (checkConv (E := envPre 158) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBcL0Nil.body.getD (.sort .zero)) mBcL0Nil.mtype).isSome = true

/-! slot 161: mLt510 -/
kernel_rfl_theorem chkThm161 :
    (checkConv (E := envPre 161) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mLt510.body.getD (.sort .zero)) mLt510.mtype).isSome = true

/-! slot 162: mNd5 -/
kernel_rfl_theorem chkThm162 :
    (checkConv (E := envPre 162) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mNd5.body.getD (.sort .zero)) mNd5.mtype).isSome = true

/-! slot 163: mBc53S -/
kernel_rfl_theorem chkThm163 :
    (checkConv (E := envPre 163) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBc53S.body.getD (.sort .zero)) mBc53S.mtype).isSome = true

/-! slot 167: mVI5 -/
kernel_rfl_theorem chkThm167 :
    (checkConv (E := envPre 167) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mVI5.body.getD (.sort .zero)) mVI5.mtype).isSome = true

#print axioms Rcic.Scm.SrcG.convBy
#print axioms Rcic.Scm.SrcG.convByAux
#print axioms Rcic.Scm.SrcG.inferConv
#print axioms Rcic.Scm.SrcG.inferConvAux
#print axioms Rcic.Scm.SrcG.checkConv
#print axioms Rcic.Scm.SrcG.mkWitBL
#print axioms Rcic.Scm.SrcG.tyThm159
#print axioms Rcic.Scm.SrcG.tyThm160
#print axioms Rcic.Scm.SrcG.chkThm113
#print axioms Rcic.Scm.SrcG.chkThm167

end Rcic.Scm.SrcG
