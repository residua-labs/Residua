import NfCompose.Seq

/-!
A hop is an NF instance (NF-0, "A hop is an NF instance; its correctness
is exactness"). For a translation `T` from layer `M_A` to layer `M_B` and
an observation map `obs` (B outcomes to A outcomes), `hopModel` packages
the hop as an `ExecModel`:

  * `Raw` = A programs, `q = M_A.q`, `evalRaw`/`evalClass` = A's
    evaluation — the outcome a hop preserves is A's own;
  * `a` = exactness: B's evaluation of `T (sigma_A c)`, mapped by `obs`,
    equals A's evaluation of `c` (compared by `eqA`, the A-side value
    equality — executable models need a Bool where `DecidableEq` may not
    exist, e.g. scm's `Val`);
  * `sigma` = the canonical translated program, `M_B.q (T rep)`, emitted
    exactly on exact classes;
  * `rho` = the named failure: `translationRefused` when `sigma_A` gives
    no representative for `T`, `valueMismatch` carrying both outcomes.

`hopModel_profile` proves the four Tier-1 laws once, from the two layer
profiles. `hop_rho_none_iff_admissible` is the exactness reading: no
residue iff the hop's own admission holds — MST-NF's
exact_iff_empty_residues. `seq_residue_none_iff` /
`seq_residue_empty_iff` are the seq-of-hops residue lemma: under both
profiles a seq residue vanishes on a class iff stage 1 admits it and
stage 2 admits the class `feed` hands it, so a chain of hops has an
empty residue set on the admitted classes iff every hop's does
(stage-tagged by `SeqResidue`).

Prior art for the shape: CompCert's `forward_simulation` record and its
composition lemma; CakeML's per-phase semantics preservation.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

/-- the named failure of a hop: the translation could not be made (no
    representative of the A-class), or the two evaluations differed —
    carrying both outcomes. -/
inductive HopResidue (O_A O_B : Type) where
  | translationRefused
  | valueMismatch (a : O_A) (b : O_B)

/-- the generic hop model. `eqA` is the A-side outcome equality the
    admission compares with; callers supply it (for `DecidableEq`
    outcomes, `(· == ·)`). -/
def hopModel (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) : ExecModel where
  Raw := M_A.Raw
  Class := M_A.Class
  Rep := M_B.Class
  Residue := HopResidue M_A.Outcome M_B.Outcome
  Outcome := M_A.Outcome
  q := M_A.q
  evalRaw := M_A.evalRaw
  evalClass := M_A.evalClass
  admissible := fun c => match M_A.sigma c with
    | none => false
    | some rep => eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c)
  rho := fun c => match M_A.sigma c with
    | none => some .translationRefused
    | some rep =>
        if eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c) then none
        else some (.valueMismatch (M_A.evalClass c) (M_B.evalRaw (T rep)))
  sigma := fun c => match M_A.sigma c with
    | none => none
    | some rep =>
        if eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c)
        then some (M_B.q (T rep)) else none

/-- the four Tier-1 laws of a hop, proved once from the two layer
    profiles (only `M_A`'s quotient factorization is needed; the rest
    follows from the model's own shape). -/
theorem hopModel_profile (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (hA : hasMSTNFProfile M_A) (_hB : hasMSTNFProfile M_B) :
    hasMSTNFProfile (hopModel M_A M_B T obs eqA) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; exact hA.1 r
  · intro c rep selected
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig] at selected
    | some repA =>
        simp only [hopModel, hsig] at selected ⊢
        cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
          simp_all
  · intro c _ refused
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig]
    | some repA =>
        simp only [hopModel, hsig] at refused ⊢
        cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
          simp_all
  · intro c _ admitted
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig] at admitted
    | some repA =>
        simp only [hopModel, hsig] at admitted ⊢
        cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
          simp_all

/-- exactness as residue emptiness: a hop class has no residue iff the
    hop's own admission holds on it (`rho` is `some` exactly where `a` is
    `false`). -/
theorem hop_rho_none_iff_admissible (M_A M_B : ExecModel)
    (T : M_A.Rep → M_B.Raw) (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) (c : M_A.Class) :
    (hopModel M_A M_B T obs eqA).rho c = none ↔
      (hopModel M_A M_B T obs eqA).admissible c = true := by
  cases hsig : M_A.sigma c with
  | none => simp [hopModel, hsig]
  | some repA =>
      simp only [hopModel, hsig]
      cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
        simp [heq]

/-- "no residue on the admissible classes": the correctness statement of
    a hop (and of any model against a predicate on its classes). -/
def noResidueOn (M : ExecModel) (P : M.Class → Prop) : Prop :=
  ∀ c, activeClass M c → P c → M.rho c = none

/-- a hop's correctness theorem: no residue on the A-admissible classes —
    by `hop_rho_none_iff_admissible`, equivalently every A-admissible
    class is exact. -/
def hopCorrect (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) : Prop :=
  noResidueOn (hopModel M_A M_B T obs eqA)
    (fun c => M_A.admissible c = true)

theorem hopCorrect_iff_exact (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) :
    hopCorrect M_A M_B T obs eqA ↔
      ∀ c, activeClass M_A c → M_A.admissible c = true →
        (hopModel M_A M_B T obs eqA).admissible c = true := by
  unfold hopCorrect noResidueOn
  constructor
  · intro h c hc ha
    exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mp (h c hc ha)
  · intro h c hc ha
    exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mpr (h c hc ha)

/-- the seq-of-hops residue lemma, pointwise: under both profiles a seq
    residue vanishes on an active class iff stage 1 admits the class and
    stage 2 admits the class `feed` hands it (refusals stay tagged by
    stage: `SeqResidue.stage1` / `.stage2`). -/
theorem seq_residue_none_iff (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)
    (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2)
    (c : M1.Class) (hc : activeClass M1 c) :
    (seqModel M1 M2 feed).rho c = none ↔
      M1.admissible c = true ∧
      (∀ rep, M1.sigma c = some rep →
        M2.admissible (M2.q (feed rep)) = true) := by
  constructor
  · intro h
    cases ha : M1.admissible c with
    | false =>
        have hrho := h1.2.2.1 c hc ha
        cases hr : M1.rho c with
        | none => exact absurd hr hrho
        | some _ => simp [seqModel, seqRhoOf, ha, hr] at h
    | true =>
        have hsig := h1.2.2.2 c hc ha
        cases hs : M1.sigma c with
        | none => exact absurd hs hsig
        | some rep =>
            refine ⟨rfl, ?_⟩
            intro rep' hs'
            have hrr : rep = rep' := Option.some.inj hs'
            cases hrr
            cases hb : M2.admissible (M2.q (feed rep)) with
            | true => rfl
            | false =>
                have hrho2 := h2.2.2.1 _ ⟨feed rep, rfl⟩ hb
                cases hr2 : M2.rho (M2.q (feed rep)) with
                | none => exact absurd hr2 hrho2
                | some _ => simp [seqModel, seqRhoOf, ha, hs, hb, hr2] at h
  · intro ⟨ha, hrep⟩
    cases hs : M1.sigma c with
    | none => simp [seqModel, seqRhoOf, ha, hs]
    | some rep =>
        have hb := hrep rep hs
        simp [seqModel, seqRhoOf, ha, hs, hb]

/-- the seq-of-hops residue lemma, set form: a seq of two models has an
    empty residue set on `P` iff stage 1 admits every `P` class and
    stage 2 admits every class `feed` reaches from them. For two hops
    chained on sigma this is "the chain is correct iff every hop's
    residue set is empty". -/
theorem seq_residue_empty_iff (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)
    (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2)
    (P : M1.Class → Prop) :
    (∀ c, activeClass M1 c → P c →
      (seqModel M1 M2 feed).rho c = none) ↔
    (∀ c, activeClass M1 c → P c → M1.admissible c = true) ∧
    (∀ c rep, activeClass M1 c → P c → M1.sigma c = some rep →
      M2.admissible (M2.q (feed rep)) = true) := by
  constructor
  · intro h
    refine ⟨fun c hc hp => ?_, fun c rep hc hp hs => ?_⟩
    · exact ((seq_residue_none_iff M1 M2 feed h1 h2 c hc).mp (h c hc hp)).1
    · exact ((seq_residue_none_iff M1 M2 feed h1 h2 c hc).mp
        (h c hc hp)).2 rep hs
  · intro ⟨h1a, h2a⟩ c hc hp
    exact (seq_residue_none_iff M1 M2 feed h1 h2 c hc).mpr
      ⟨h1a c hc hp, fun rep hs => h2a c rep hc hp hs⟩

/-! ## seq associativity, model equivalence congruence, the hop as `obs ∘ seq` -/

/-- reassociate a left-nested sequential outcome rightward. -/
def seqAssocOut {O1 O2 O3 : Type} :
    SeqOutcome (SeqOutcome O1 O2) O3 → SeqOutcome O1 (SeqOutcome O2 O3)
  | .stage1 (.stage1 a) => .stage1 a
  | .stage1 (.stage2 b) => .stage2 (.stage1 b)
  | .stage2 c => .stage2 (.stage2 c)

/-- reassociate a left-nested sequential residue rightward. -/
def seqAssocRes {R1 R2 R3 : Type} :
    SeqResidue (SeqResidue R1 R2) R3 → SeqResidue R1 (SeqResidue R2 R3)
  | .stage1 (.stage1 a) => .stage1 a
  | .stage1 (.stage2 b) => .stage2 (.stage1 b)
  | .stage2 c => .stage2 (.stage2 c)

/-- reassociate a left-nested sequential representative rightward. -/
def seqAssocRep {P1 P2 P3 : Type} :
    SeqRep (SeqRep P1 P2) P3 → SeqRep P1 (SeqRep P2 P3)
  | .both (.both a b) c => .both a (.both b c)

/-- the left-associated feed into stage 3: it reads the second
    component's representative. -/
def seqAssocPairFeed {P1 P2 R3 : Type} (f23 : P2 → R3) :
    SeqRep P1 P2 → R3
  | .both _ r2 => f23 r2

/-- reassociation on the stage-nested residue tags, as function equalities
    (the `Option.map` compositions `seq` produces). -/
theorem seqAssocRes_s1s1 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘
        SeqResidue.stage1 ∘ SeqResidue.stage1) =
      (SeqResidue.stage1 : R1 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl

theorem seqAssocRes_s1s2 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘
        SeqResidue.stage1 ∘ SeqResidue.stage2) =
      (SeqResidue.stage2 ∘ SeqResidue.stage1 :
        R2 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl

theorem seqAssocRes_s2 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘ SeqResidue.stage2) =
      (SeqResidue.stage2 ∘ SeqResidue.stage2 :
        R3 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl

/-- `seq` is associative up to the reassociation maps: the left-nested
    and right-nested composites admit the same classes, evaluate each
    class to the same outcome, and produce the same residue and
    representative modulo `seqAssocRes`/`seqAssocRep`/`seqAssocOut`.
    `h1`'s admissibility soundness removes the case the left nesting
    could refuse where the right cannot (`sigma` present on a
    non-admissible class). -/
theorem seq_assoc (M1 M2 M3 : ExecModel) (f12 : M1.Rep → M2.Raw)
    (f23 : M2.Rep → M3.Raw) (h1 : hasMSTNFProfile M1) :
    ∀ c : M1.Class,
      (seqModel (seqModel M1 M2 f12) M3 (seqAssocPairFeed f23)).admissible c =
        (seqModel M1 (seqModel M2 M3 f23) f12).admissible c ∧
      seqAssocOut ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).evalClass c) =
        (seqModel M1 (seqModel M2 M3 f23) f12).evalClass c ∧
      ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).rho c).map seqAssocRes =
        (seqModel M1 (seqModel M2 M3 f23) f12).rho c ∧
      ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).sigma c).map seqAssocRep =
        (seqModel M1 (seqModel M2 M3 f23) f12).sigma c := by
  intro c
  cases ha : M1.admissible c with
  | false =>
      cases hs1 : M1.sigma c with
      | some r1 =>
          simp [h1.2.1 c r1 hs1] at ha
      | none =>
          simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
            seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
            seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
            ha, hs1]
  | true =>
      cases hs1 : M1.sigma c with
      | none =>
          simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
            seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
            seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
            ha, hs1]
      | some r1 =>
          cases ha2 : M2.admissible (M2.q (f12 r1)) with
          | false =>
              cases hs2 : M2.sigma (M2.q (f12 r1)) <;>
                simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                  seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                  seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                  ha, hs1, ha2, hs2]
          | true =>
              cases hs2 : M2.sigma (M2.q (f12 r1)) with
              | none =>
                  simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                    seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                    seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                    ha, hs1, ha2, hs2]
              | some r2 =>
                  cases ha3 : M3.admissible (M3.q (f23 r2)) <;>
                  cases hs3 : M3.sigma (M3.q (f23 r2)) <;>
                  simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                    seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                    seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                    ha, hs1, ha2, hs2, ha3, hs3]

/-- a homomorphism of models: every field is transported. `modelEquiv`
    is the symmetric closure of this simulation; the seq congruence
    below needs only the forward maps, so that is what is packaged. -/
structure ModelEquiv (M N : ExecModel) where
  toR : M.Raw → N.Raw
  toC : M.Class → N.Class
  toP : M.Rep → N.Rep
  toE : M.Residue → N.Residue
  toO : M.Outcome → N.Outcome
  q_map : ∀ r, toC (M.q r) = N.q (toR r)
  evalR_map : ∀ r, toO (M.evalRaw r) = N.evalRaw (toR r)
  evalC_map : ∀ c, toO (M.evalClass c) = N.evalClass (toC c)
  adm_map : ∀ c, M.admissible c = N.admissible (toC c)
  rho_map : ∀ c, (M.rho c).map toE = N.rho (toC c)
  sig_map : ∀ c, (M.sigma c).map toP = N.sigma (toC c)

/-- a model morphism componentwise through the seq tags. -/
def seqRepMap {P1 P2 P1' P2' : Type} (t1 : P1 → P1') (t2 : P2 → P2') :
    SeqRep P1 P2 → SeqRep P1' P2'
  | .both p1 p2 => .both (t1 p1) (t2 p2)

def seqResMap {R1 R2 R1' R2' : Type} (t1 : R1 → R1') (t2 : R2 → R2') :
    SeqResidue R1 R2 → SeqResidue R1' R2'
  | .stage1 r => .stage1 (t1 r)
  | .stage2 r => .stage2 (t2 r)

def seqOutMap {O1 O2 O1' O2' : Type} (t1 : O1 → O1') (t2 : O2 → O2') :
    SeqOutcome O1 O2 → SeqOutcome O1' O2'
  | .stage1 o => .stage1 (t1 o)
  | .stage2 o => .stage2 (t2 o)

/-- the tag maps commute with the stage tags, as function equalities
    (the `Option.map` compositions `seq` produces). -/
theorem seqResMap_s1 {R1 R2 R1' R2' : Type} (t1 : R1 → R1')
    (t2 : R2 → R2') :
    (seqResMap t1 t2 ∘ SeqResidue.stage1 :
        R1 → SeqResidue R1' R2') = SeqResidue.stage1 ∘ t1 :=
  funext fun _ => rfl

theorem seqResMap_s2 {R1 R2 R1' R2' : Type} (t1 : R1 → R1')
    (t2 : R2 → R2') :
    (seqResMap t1 t2 ∘ SeqResidue.stage2 :
        R2 → SeqResidue R1' R2') = SeqResidue.stage2 ∘ t2 :=
  funext fun _ => rfl

theorem seqRepMap_both {P1 P2 P1' P2' : Type} (t1 : P1 → P1')
    (t2 : P2 → P2') (p1 : P1) :
    (seqRepMap t1 t2 ∘ SeqRep.both p1 :
        P2 → SeqRep P1' P2') = SeqRep.both (t1 p1) ∘ t2 :=
  funext fun _ => rfl

/-- the fed class's stage-2 image, translated: `q` then `admissible`
    and `rho` commute through `feed` and the two maps. -/
theorem seqCong_feed_q (M1 M1' M2 M2' : ExecModel) (e1 : ModelEquiv M1 M1')
    (e2 : ModelEquiv M2 M2') (feed : M1.Rep → M2.Raw)
    (feed' : M1'.Rep → M2'.Raw)
    (feedC : ∀ r, feed' (e1.toP r) = e2.toR (feed r)) (rep : M1.Rep) :
    M2'.q (feed' (e1.toP rep)) = e2.toC (M2.q (feed rep)) :=
  (congrArg M2'.q (feedC rep)).trans (e2.q_map (feed rep)).symm

/-- `seq` is a congruence for model equivalence: compatible translations
    of the two stages (the feed commutes with the representative maps)
    transport to a translation of the composite. `ModelEquiv` is data —
    the congruence is a definition, not a theorem. -/
def seq_congr (M1 M2 M1' M2' : ExecModel) (feed : M1.Rep → M2.Raw)
    (feed' : M1'.Rep → M2'.Raw)
    (e1 : ModelEquiv M1 M1') (e2 : ModelEquiv M2 M2')
    (feedC : ∀ r, feed' (e1.toP r) = e2.toR (feed r)) :
    ModelEquiv (seqModel M1 M2 feed) (seqModel M1' M2' feed') where
  toR := e1.toR
  toC := e1.toC
  toP := seqRepMap e1.toP e2.toP
  toE := seqResMap e1.toE e2.toE
  toO := seqOutMap e1.toO e2.toO
  q_map := e1.q_map
  evalR_map := by
    intro r
    have hq : M1'.q (e1.toR r) = e1.toC (M1.q r) := (e1.q_map r).symm
    have hs' : M1'.sigma (e1.toC (M1.q r)) =
        (M1.sigma (M1.q r)).map e1.toP := (e1.sig_map (M1.q r)).symm
    cases hs : M1.sigma (M1.q r) <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs', hq,
        e1.evalR_map r, feedC, e2.evalR_map]
  evalC_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    cases hs : M1.sigma c <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs',
        e1.evalC_map c, feedC, e2.evalR_map]
  adm_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqAdmOf, ha, hs, hs', ha',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.adm_map]
  rho_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    have hr' : M1'.rho (e1.toC c) = (M1.rho c).map e1.toE :=
      (e1.rho_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqRhoOf, ha, hs, hs', ha', hr',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.adm_map,
        e2.rho_map, seqResMap_s1, seqResMap_s2]
    · rename_i rep
      cases hb : M2'.admissible (e2.toC (M2.q (feed rep))) <;>
        simp [hb, seqResMap_s1, seqResMap_s2]
      rw [← Option.map_map, e2.rho_map]
  sig_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqSigmaOf, ha, hs, hs', ha',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.sig_map,
        seqRepMap_both]
    · rename_i rep
      cases hsi : M2.sigma (M2.q (feed rep)) <;>
        simp [hsi, ← e2.sig_map, seqRepMap]

/-- the observation of a sequential outcome: the B-side value mapped
    back into A's outcome space. -/
def hopSeqObs {A B : Type} (obs : B → A) : SeqOutcome A B → A
  | .stage1 a => a
  | .stage2 b => obs b

/-- on a hop-admissible class the observed sequential outcome is the
    hop's own outcome: `M_A ~ obs ∘ seq(T, M_B)` on the class. -/
theorem hop_eval_eq_obs_seq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) (c : M_A.Class)
    (hadm : (hopModel M_A M_B T obs eqA).admissible c = true) :
    eqA (hopSeqObs obs ((seqModel M_A M_B T).evalClass c))
        ((hopModel M_A M_B T obs eqA).evalClass c) = true := by
  cases hsig : M_A.sigma c with
  | none => simp [hopModel, hsig] at hadm
  | some rep =>
      simp only [hopModel, hsig] at hadm
      simpa [seqModel, seqEvalOf, hsig, hopSeqObs, hopModel] using hadm

/-- a hop stated on canonical representatives:
    `M_A ~ obs ∘ seq(T, M_B)` — on every active A-admissible class the
    sequential composite's outcome, observed back into A's outcome
    space, is A's own outcome. -/
def hopObsSeq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) : Prop :=
  ∀ c, activeClass M_A c → M_A.admissible c = true →
    eqA (hopSeqObs obs ((seqModel M_A M_B T).evalClass c))
        (M_A.evalClass c) = true

/-- the two forms of a hop theorem coincide: no residue on the
    A-admissible classes iff the observed `seq(T, M_B)` agrees with
    `M_A` on the A-admissible classes. -/
theorem hopCorrect_iff_obsSeq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (hA : hasMSTNFProfile M_A) :
    hopCorrect M_A M_B T obs eqA ↔ hopObsSeq M_A M_B T obs eqA := by
  constructor
  · intro h c hact ha
    have hadm : (hopModel M_A M_B T obs eqA).admissible c = true :=
      (hopCorrect_iff_exact M_A M_B T obs eqA).mp h c hact ha
    exact hop_eval_eq_obs_seq M_A M_B T obs eqA c hadm
  · intro h
    unfold hopCorrect noResidueOn
    intro c hact ha
    cases hsig : M_A.sigma c with
    | none => exact absurd hsig (hA.2.2.2 c hact ha)
    | some rep =>
        have hobs := h c hact ha
        have hadm : (hopModel M_A M_B T obs eqA).admissible c = true := by
          simp only [hopModel, hsig]
          simpa [seqModel, seqEvalOf, hsig, hopSeqObs] using hobs
        exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mpr hadm

end NfCompose

#print axioms NfCompose.hopModel_profile
#print axioms NfCompose.hop_rho_none_iff_admissible
#print axioms NfCompose.hopCorrect_iff_exact
#print axioms NfCompose.seq_residue_none_iff
#print axioms NfCompose.seq_residue_empty_iff
#print axioms NfCompose.seq_assoc
#print axioms NfCompose.seq_congr
#print axioms NfCompose.hop_eval_eq_obs_seq
#print axioms NfCompose.hopCorrect_iff_obsSeq
