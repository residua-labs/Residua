/-
RCIC 07 §23 CT-021 (policy half) — the semantic decision boundary of the
AllowedAxioms(policy) subset check: `assumptionClosure ⊆
AllowedAxioms(policy)` with the policy as a SEPARATE presented set, not a
field of the closure.

Owner text and the carrier this models:
  `docs/rcic/04_ENVIRONMENT_AND_GROUPS.md:318` — the closure is the
    canonical set of reachable axiom members.
  `docs/rcic/04_ENVIRONMENT_AND_GROUPS.md:323` —
    `assumptionClosure(proof) ⊆ AllowedAxioms(policy)`.
  `docs/rcic/00_ANNEX_25_OBJECT_DECISIONS.md` (Annex 25.9, cc ruling
    R-OBJ, #6358) — `AllowedAxioms(policy)` is an `AllowedAssumptionSet`
    object; `policy` is that object's ref and is an argument; there is no
    `MasterProfile` field to read; the set is not copied into group
    identity.
  grok C's carrier (data lane, not duplicated): `apps/rcic-ct-allow`
    `(call rcic.allowed_axioms form closure_bytes policy_bytes policy_ref)`
    → `group_codec_ok digest | group_codec_refuse code`, on #6374
    `grok/ct-allowed-axioms` `d5127b5759`. Its form-0 cascade:
      1. `form = 0`, else `[rcic_allowed_axioms_form]`.
      2. `allowed_axioms_spell policy_bytes`, then the same for
         `closure_bytes`: split by `rcic.replay_order_csv` (empty bytes
         are the empty list), `dep_closure_bad` refuses an empty token or
         one longer than 2048 codepoints (name 12), and the surviving
         list must already be the canonical join
         `dep_closure_join (dep_closure_union xs [])` — sorted-unique —
         else name 9.
      3. `(rcic.derive 3 0 policy_bytes)` must yield a digest equal to
         the presented `policy_ref`, else `[rcic_allowed_axioms_ref]`
         (a derive refusal propagates under its own code). The ref is
         checked BEFORE the subset.
      4. `rcic.genesis_floor_subset` of the closure tokens in the policy
         tokens must hold, else `[rcic_allowed_axioms_subset]`.

TRANSCRIPTION TABLE (carrier → Lean; the Lean side is the semantic
reading of the decision boundary, not a reimplementation):
  `rcic.replay_order_csv`            → `csvTokens` (bytes → token list)
  `rcic.dep_closure_bad`             → `badTok` (empty / > 2048 chars)
  `dep_closure_union · []` + join    → `Rows.rowCanon` + `canonJoin`
  `rcic.derive 3 0 · .digest/.code`  → `AllowParams.derive` (a `Sum`)
  `rcic.genesis_floor_subset`        → `subsetAll` / `List.Subset`
  `rcic.group_codec_ok/refuse`       → `AllowOut` (`ok`, `canon`, `code`)
  name-12 / name-9 spell refusals    → `AllowParams.badTokCode`, `.nonCanonCode`

The theorems: `allowCheck` is the staged cascade; `allowCheck_ok_iff`
gives the accept boundary as the exact conjunction;
`allowCheck_subset_decides` is CT-021's "policy separate": once
form/spelling/ref hold, the subset of the presented token sets is the
ONLY remaining question — the closure's own derivation is never
consulted. `mutantCheck` is the LANDED corpus mutant (form, ref AND
subset all omitted); `mutantCheck_ok_iff` gives its accept boundary and
`mutant_diverges_on_{form,ref,subset_escape}` pin each dropped clause.
Teeth (concrete, in `ScmAllowPins`): the carrier's 17-row corpus
verbatim, the six corpus divergences, and the policy-gating lemma.

`closure_claim` stays 0.
-/
import rcic.ScmRows

namespace Rcic.Scm.Allow
open Rcic.Scm

/-- `rcic.replay_order_csv`: comma-split; EMPTY BYTES ARE THE EMPTY LIST. -/
def csvTokens (text : String) : List String :=
  if text.isEmpty then [] else text.splitOn ","

/-- `rcic.dep_closure_bad`: a token is bad if empty or longer than 2048
    codepoints (a 2048-codepoint token is inside the bound). -/
def badTok (t : String) : Bool := decide (t = "" ∨ 2048 < t.length)

/-- `rcic.dep_closure_join`: the comma-join of an already-canonical list. -/
def canonJoin (xs : List String) : String := ",".intercalate xs

/-- The carrier's output record `group_codec_{ok,refuse}`:
    `{ok, canon, code}`; on success `canon` is the policy ref. -/
structure AllowOut where
  ok : Int
  canon : String
  code : String
  deriving BEq, Repr

def okOut (canon : String) : AllowOut := ⟨1, canon, ""⟩
def noOut (code : String) : AllowOut := ⟨0, "", code⟩

/-- Everything outside the model that the carrier consults: the
    class-3-kind-0 `derive` for the policy bytes (`.inl` digest /
    `.inr` refusal code — a derive refusal propagates under its own
    code), and the two spell-refusal names (`dep_closure_name` 12 and
    9) — opaque vocabulary the carrier supplies. -/
structure AllowParams where
  derive : String → Sum String String
  badTokCode : String
  nonCanonCode : String

/-- `allowed_axioms_spell`: no bad token, and the text IS already the
    canonical join of its sorted-unique token list. This leg is the
    exactness half of CT-021's closure presentation: a spelled text is
    the canonical set spelled. -/
def spellCheck (ps : AllowParams) (text : String) : AllowOut :=
  if (csvTokens text).any badTok then noOut ps.badTokCode
  else if canonJoin (Rows.rowCanon (csvTokens text)) = text then okOut text
  else noOut ps.nonCanonCode

/-- `rcic.genesis_floor_subset`: every closure token is a policy token. -/
def subsetAll (xs ys : List String) : Bool := xs.all (ys.contains ·)

/-- The post-spelling stage of `rcic.allowed_axioms`: derive → ref →
    subset. A derive refusal propagates under its own code; the ref is
    checked BEFORE the subset. -/
def allowRest (ps : AllowParams) (policyBytes policyRef : String)
    (closureTokens policyTokens : List String) : AllowOut :=
  match ps.derive policyBytes with
  | .inl d => if policyRef = d then
      if subsetAll closureTokens policyTokens
      then okOut d else noOut "[rcic_allowed_axioms_subset]"
    else noOut "[rcic_allowed_axioms_ref]"
  | .inr code => noOut code

/-- The LANDED corpus mutant's post-spelling stage
    (`apps/rcic-ct-allow/rcic_ct_allow_mutant.scm` on origin/main): derive,
    then admit the digest — the ref comparison is dropped and the subset
    test was never reached. A derive refusal still propagates. -/
def mutantRest (ps : AllowParams) (policyBytes : String) : AllowOut :=
  match ps.derive policyBytes with
  | .inl d => okOut d
  | .inr code => noOut code

/-- `rcic.allowed_axioms` form 0, staged exactly as the carrier: form →
    policy spelling → closure spelling → derive → ref → subset. -/
def allowCheck (ps : AllowParams) (form : Int) (closureBytes policyBytes : String)
    (policyRef : String) : AllowOut :=
  if form ≠ 0 then noOut "[rcic_allowed_axioms_form]"
  else if (spellCheck ps policyBytes).ok = 0 then spellCheck ps policyBytes
  else if (spellCheck ps closureBytes).ok = 0 then spellCheck ps closureBytes
  else allowRest ps policyBytes policyRef
    (csvTokens closureBytes) (csvTokens policyBytes)

/-- The LANDED corpus mutant (`rcic_ct_allow_mutant.scm` on origin/main):
    form is not consulted, the presented ref is not compared with the
    derive digest, and the closure tokens are not tested against the
    policy — policy spelling → closure spelling → derive → ok. Spelling
    refusals and a derive refusal still pass through, so it is not a
    constant; it diverges on exactly the three omitted clauses. -/
def mutantCheck (ps : AllowParams) (_form : Int) (closureBytes policyBytes : String)
    (_policyRef : String) : AllowOut :=
  if (spellCheck ps policyBytes).ok = 0 then spellCheck ps policyBytes
  else if (spellCheck ps closureBytes).ok = 0 then spellCheck ps closureBytes
  else mutantRest ps policyBytes

/-- `okOut` never equals `noOut`. -/
theorem okOut_ne_noOut (c c' : String) : okOut c ≠ noOut c' := by
  simp [okOut, noOut]

/-- `noOut` never equals `okOut`. -/
theorem noOut_ne_okOut (c c' : String) : noOut c ≠ okOut c' :=
  fun h => okOut_ne_noOut c' c h.symm

/-- `allowRest` on a successful derive. -/
theorem allowRest_inl (ps : AllowParams) (policyBytes policyRef : String)
    (closureTokens policyTokens : List String) (d : String)
    (hd : ps.derive policyBytes = .inl d) :
    allowRest ps policyBytes policyRef closureTokens policyTokens =
      (if policyRef = d then
        (if subsetAll closureTokens policyTokens
         then okOut d else noOut "[rcic_allowed_axioms_subset]")
       else noOut "[rcic_allowed_axioms_ref]") := by
  unfold allowRest; rw [hd]

/-- `allowRest` on a derive refusal: the code propagates. -/
theorem allowRest_inr (ps : AllowParams) (policyBytes policyRef : String)
    (closureTokens policyTokens : List String) (code : String)
    (hd : ps.derive policyBytes = .inr code) :
    allowRest ps policyBytes policyRef closureTokens policyTokens = noOut code := by
  unfold allowRest; rw [hd]

/-- `mutantRest` on a successful derive: admit unconditionally. -/
theorem mutantRest_inl (ps : AllowParams) (policyBytes : String) (d : String)
    (hd : ps.derive policyBytes = .inl d) :
    mutantRest ps policyBytes = okOut d := by
  unfold mutantRest; rw [hd]

/-- `mutantRest` on a derive refusal: the code propagates. -/
theorem mutantRest_inr (ps : AllowParams) (policyBytes code : String)
    (hd : ps.derive policyBytes = .inr code) :
    mutantRest ps policyBytes = noOut code := by
  unfold mutantRest; rw [hd]

/-! ### Semantic lemmas -/

/-- `spellCheck`'s only success shape: on `ok ≠ 0` it returned
    `okOut` of its own text. -/
theorem spellCheck_ok_shape (ps : AllowParams) (text : String)
    (h : (spellCheck ps text).ok ≠ 0) :
    spellCheck ps text = okOut text := by
  unfold spellCheck at h ⊢
  split at h
  · exact absurd rfl h
  · rename_i hc
    rw [if_neg hc]
    split at h
    · rename_i hc2
      rw [if_pos hc2]
    · rename_i hc2
      rw [if_neg hc2]
      exact absurd rfl h

/-- `spellCheck` accepts iff no token is bad AND the text is already the
    canonical join of its own sorted-unique tokens — the presentation
    IS the canonical set spelled (the exactness leg's spelling side). -/
theorem spellCheck_ok_iff (ps : AllowParams) (text : String) :
    spellCheck ps text = okOut text ↔
      ((∀ t ∈ csvTokens text, t ≠ "" ∧ t.length ≤ 2048) ∧
        canonJoin (Rows.rowCanon (csvTokens text)) = text) := by
  unfold spellCheck
  split
  · rename_i hb
    constructor
    · intro h; exact absurd h (noOut_ne_okOut _ _)
    · rintro ⟨hno, _⟩
      rw [List.any_eq_true] at hb
      obtain ⟨t, ht, hbad⟩ := hb
      have hok := hno t ht
      rcases of_decide_eq_true hbad with he | hl
      · exact absurd he hok.1
      · exact absurd hok.2 (by omega)
  · rename_i hb
    have hb' : (csvTokens text).any badTok = false := Bool.not_eq_true _ ▸ hb
    rw [List.any_eq_false] at hb'
    split
    · rename_i hc
      constructor
      · intro _
        refine ⟨fun t ht => ?_, hc⟩
        have hbt := hb' t ht
        have hdec : ¬ (t = "" ∨ 2048 < t.length) := fun hd => hbt (decide_eq_true hd)
        have hnor := not_or.mp hdec
        exact ⟨hnor.1, by omega⟩
      · intro _; rfl
    · rename_i hc
      constructor
      · intro h; exact absurd h (noOut_ne_okOut _ _)
      · rintro ⟨_, h2⟩; exact absurd h2 hc

/-- `subsetAll` is exactly `List.Subset` of the presented token lists. -/
theorem subsetAll_iff (xs ys : List String) :
    subsetAll xs ys = true ↔ ∀ t ∈ xs, t ∈ ys := by
  unfold subsetAll
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    have := h t ht
    rwa [List.elem_iff] at this
  · intro h t ht
    rw [List.elem_iff]
    exact h t ht

/-- The accept boundary: `allowCheck` returns `ok d` iff form is 0, both
    texts are spelled, the derive yields `d` and the presented ref is
    `d`, and the closure's presented tokens are a subset of the
    policy's. Nothing else is consulted. -/
theorem allowCheck_ok_iff (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String) :
    allowCheck ps form closureBytes policyBytes policyRef = okOut d ↔
      (form = 0 ∧ spellCheck ps policyBytes = okOut policyBytes ∧
        spellCheck ps closureBytes = okOut closureBytes ∧
        ps.derive policyBytes = .inl d ∧ policyRef = d ∧
        ∀ t ∈ csvTokens closureBytes, t ∈ csvTokens policyBytes) := by
  unfold allowCheck
  split
  · rename_i hf
    constructor
    · intro h; exact absurd h (noOut_ne_okOut _ _)
    · rintro ⟨h0, _⟩; exact absurd h0 hf
  · rename_i hf
    have hf' : form = 0 := by
      by_cases h0 : form = 0
      · exact h0
      · exact absurd h0 hf
    split
    · rename_i hsp
      constructor
      · intro h; rw [h] at hsp; simp [okOut] at hsp
      · rintro ⟨_, hsp2, _⟩; rw [hsp2] at hsp; simp [okOut] at hsp
    · rename_i hsp
      have hsp' := spellCheck_ok_shape ps policyBytes hsp
      split
      · rename_i hsc
        constructor
        · intro h; rw [h] at hsc; simp [okOut] at hsc
        · rintro ⟨_, _, hsc2, _⟩; rw [hsc2] at hsc; simp [okOut] at hsc
      · rename_i hsc
        have hsc' := spellCheck_ok_shape ps closureBytes hsc
        cases hdv : ps.derive policyBytes with
        | inl dv =>
          rw [allowRest_inl (hd := hdv)]
          split
          · rename_i href
            split
            · rename_i hsub
              constructor
              · intro h
                have hdd : dv = d := congrArg AllowOut.canon h
                subst hdd
                exact ⟨hf', hsp', hsc', rfl, href, (subsetAll_iff _ _).mp hsub⟩
              · rintro ⟨_, _, _, hd2, _, _⟩
                injection hd2 with e; subst e; rfl
            · rename_i hsub
              constructor
              · intro h; exact absurd h (noOut_ne_okOut _ _)
              · rintro ⟨_, _, _, _, _, hsub2⟩
                exact absurd ((subsetAll_iff _ _).mpr hsub2) hsub
          · rename_i href
            constructor
            · intro h; exact absurd h (noOut_ne_okOut _ _)
            · rintro ⟨_, _, _, hd2, href2, _⟩
              injection hd2 with e; subst e
              exact absurd href2 href
        | inr code =>
          rw [allowRest_inr (hd := hdv)]
          constructor
          · intro h; exact absurd h (noOut_ne_okOut _ _)
          · rintro ⟨_, _, _, hd2, _⟩
            cases hd2

/-- CT-021 "policy separate": once the presentation holds (form 0, both
    spelled, ref = derive-digest), the verdict is decided ENTIRELY by
    the subset of the presented token sets. The check reads no field of
    any closure object and consults no derivation of the closure — the
    policy is a separate subset test on presented sets, not a field of
    the closure set (Annex 25.9; `04_ENVIRONMENT_AND_GROUPS.md:323`). -/
theorem allowCheck_subset_decides (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String)
    (hf : form = 0) (hsp : spellCheck ps policyBytes = okOut policyBytes)
    (hsc : spellCheck ps closureBytes = okOut closureBytes)
    (hd : ps.derive policyBytes = .inl d) (href : policyRef = d) :
    allowCheck ps form closureBytes policyBytes policyRef = okOut d ↔
      ∀ t ∈ csvTokens closureBytes, t ∈ csvTokens policyBytes := by
  rw [allowCheck_ok_iff]
  exact ⟨fun ⟨_, _, _, _, _, hsub⟩ => hsub,
    fun hsub => ⟨hf, hsp, hsc, hd, href, hsub⟩⟩

/-- Separation, second leg: the closure enters the verdict ONLY through
    its presented token list — two spelled closure texts with the same
    token membership give the same accept/refuse verdict. The closure's
    derivation history is invisible to the check; the policy bytes enter
    additionally through their derive-digest (the policy is the object
    whose ref is presented — Annex 25.9). -/
theorem allowCheck_closure_via_tokens (ps : AllowParams) {c₁ c₂ : String}
    (hsp₁ : spellCheck ps c₁ = okOut c₁) (hsp₂ : spellCheck ps c₂ = okOut c₂)
    (hmem : ∀ t, t ∈ csvTokens c₁ ↔ t ∈ csvTokens c₂)
    (form : Int) (policyBytes policyRef : String) (d : String) :
    allowCheck ps form c₁ policyBytes policyRef = okOut d ↔
      allowCheck ps form c₂ policyBytes policyRef = okOut d := by
  rw [allowCheck_ok_iff, allowCheck_ok_iff]
  constructor
  · rintro ⟨hf, hsp, _, hd, href, hsub⟩
    exact ⟨hf, hsp, hsp₂, hd, href, fun t ht => hsub t ((hmem t).mpr ht)⟩
  · rintro ⟨hf, hsp, _, hd, href, hsub⟩
    exact ⟨hf, hsp, hsp₁, hd, href, fun t ht => hsub t ((hmem t).mp ht)⟩

/-- The mutant's accept boundary: it admits iff BOTH spellings hold and
    the derive succeeds — form, the presented ref and the subset law are
    all invisible to it. -/
theorem mutantCheck_ok_iff (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String) :
    mutantCheck ps form closureBytes policyBytes policyRef = okOut d ↔
      (spellCheck ps policyBytes = okOut policyBytes ∧
        spellCheck ps closureBytes = okOut closureBytes ∧
        ps.derive policyBytes = .inl d) := by
  unfold mutantCheck
  split
  · rename_i hsp
    constructor
    · intro h; rw [h] at hsp; simp [okOut] at hsp
    · rintro ⟨hsp2, _⟩; rw [hsp2] at hsp; simp [okOut] at hsp
  · rename_i hsp
    have hsp' := spellCheck_ok_shape ps policyBytes hsp
    split
    · rename_i hsc
      constructor
      · intro h; rw [h] at hsc; simp [okOut] at hsc
      · rintro ⟨_, hsc2, _⟩; rw [hsc2] at hsc; simp [okOut] at hsc
    · rename_i hsc
      have hsc' := spellCheck_ok_shape ps closureBytes hsc
      cases hdv : ps.derive policyBytes with
      | inl dv =>
        rw [mutantRest_inl (hd := hdv)]
        constructor
        · intro h
          have e : dv = d := congrArg AllowOut.canon h
          subst e; exact ⟨hsp', hsc', rfl⟩
        · rintro ⟨_, _, hd2⟩; injection hd2 with e; subst e; rfl
      | inr code =>
        rw [mutantRest_inr (hd := hdv)]
        constructor
        · intro h; exact absurd h (noOut_ne_okOut _ _)
        · rintro ⟨_, _, hd2⟩; cases hd2

/-- Divergence 1 of 3 (the dropped form test): with both spellings and a
    successful derive, a nonzero form is admitted by the mutant and
    refused `[rcic_allowed_axioms_form]` by the check. -/
theorem mutant_diverges_on_form (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String)
    (hf : form ≠ 0) (hsp : spellCheck ps policyBytes = okOut policyBytes)
    (hsc : spellCheck ps closureBytes = okOut closureBytes)
    (hd : ps.derive policyBytes = .inl d) :
    mutantCheck ps form closureBytes policyBytes policyRef = okOut d ∧
      allowCheck ps form closureBytes policyBytes policyRef =
        noOut "[rcic_allowed_axioms_form]" := by
  constructor
  · exact (mutantCheck_ok_iff _ _ _ _ _ _).mpr ⟨hsp, hsc, hd⟩
  · unfold allowCheck; rw [if_pos hf]

/-- Divergence 2 of 3 (the dropped ref test): with form 0, both spellings
    and derive `d`, a presented ref `≠ d` is admitted by the mutant and
    refused `[rcic_allowed_axioms_ref]` by the check — ref before subset,
    so the subset is never even consulted. -/
theorem mutant_diverges_on_ref (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String)
    (hf : form = 0) (hsp : spellCheck ps policyBytes = okOut policyBytes)
    (hsc : spellCheck ps closureBytes = okOut closureBytes)
    (hd : ps.derive policyBytes = .inl d) (href : policyRef ≠ d) :
    mutantCheck ps form closureBytes policyBytes policyRef = okOut d ∧
      allowCheck ps form closureBytes policyBytes policyRef =
        noOut "[rcic_allowed_axioms_ref]" := by
  constructor
  · exact (mutantCheck_ok_iff _ _ _ _ _ _).mpr ⟨hsp, hsc, hd⟩
  · unfold allowCheck
    rw [if_neg (fun h => h hf)]
    split
    · rename_i hs; rw [hsp] at hs; simp [okOut] at hs
    · split
      · rename_i hs; rw [hsc] at hs; simp [okOut] at hs
      · rw [allowRest_inl (hd := hd)]
        split
        · rename_i hr; exact absurd hr href
        · rfl

/-- Divergence 3 of 3 (the dropped subset test): with form 0, both
    spellings, derive `d` and the right ref, a closure escaping the
    policy is admitted by the mutant and refused
    `[rcic_allowed_axioms_subset]` by the check. -/
theorem mutant_diverges_on_subset_escape (ps : AllowParams) (form : Int)
    (closureBytes policyBytes : String) (policyRef : String) (d : String)
    (hf : form = 0) (hsp : spellCheck ps policyBytes = okOut policyBytes)
    (hsc : spellCheck ps closureBytes = okOut closureBytes)
    (hd : ps.derive policyBytes = .inl d) (href : policyRef = d)
    (hescape : ¬ ∀ t ∈ csvTokens closureBytes, t ∈ csvTokens policyBytes) :
    mutantCheck ps form closureBytes policyBytes policyRef = okOut d ∧
      allowCheck ps form closureBytes policyBytes policyRef =
        noOut "[rcic_allowed_axioms_subset]" := by
  have hsub' : subsetAll (csvTokens closureBytes) (csvTokens policyBytes) = false := by
    cases hsubv : subsetAll (csvTokens closureBytes) (csvTokens policyBytes)
    · rfl
    · exact absurd ((subsetAll_iff _ _).mp hsubv) hescape
  constructor
  · exact (mutantCheck_ok_iff _ _ _ _ _ _).mpr ⟨hsp, hsc, hd⟩
  · unfold allowCheck
    rw [if_neg (fun h => h hf)]
    split
    · rename_i hs; rw [hsp] at hs; simp [okOut] at hs
    · split
      · rename_i hs; rw [hsc] at hs; simp [okOut] at hs
      · rw [allowRest_inl (hd := hd)]
        split
        · rename_i hr
          split
          · rename_i hs2; rw [hs2] at hsub'; cases hsub'
          · rfl
        · rename_i hr; exact absurd href hr

/-! ### The `AllowedAssumptionSet` denotation (Annex 25.9 / 26.20)

`AllowedAxioms(policy)` is an `AllowedAssumptionSet` object whose codec is
the same canonical csv spelling `spellCheck` checks (04:318; Annex 25.9).
The decode below is the object's denotation: bytes → member list, `none`
when the bytes are not an accepted spelling. `acceptedAllowedSet` is Annex
26.20's "an accepted `AllowedAssumptionSet`" at a ref — the two stages
`allowRest` runs before the subset law, minus the subset itself (the set's
own acceptance, not the closure's containment). -/

/-- The `AllowedAssumptionSet` decode (Annex 25.9): the set IS its
    canonical spelling — its members are the spelled tokens. `none` when
    the bytes are not an accepted spelling: the decode refuses nothing the
    spell stage accepts and accepts nothing it refuses. -/
def decodeAllowedAssumptionSet (ps : AllowParams) (bytes : String) :
    Option (List String) :=
  if (spellCheck ps bytes).ok = 0 then none else some (csvTokens bytes)

/-- The decode is exactly the spelled text's token list. -/
theorem decodeAllowedAssumptionSet_iff (ps : AllowParams) (bytes : String)
    (xs : List String) :
    decodeAllowedAssumptionSet ps bytes = some xs ↔
      spellCheck ps bytes = okOut bytes ∧ xs = csvTokens bytes := by
  unfold decodeAllowedAssumptionSet
  split
  · rename_i h
    constructor
    · intro h'; cases h'
    · rintro ⟨hs, _⟩
      rw [hs] at h
      simp [okOut] at h
  · rename_i h
    constructor
    · intro h'
      exact ⟨spellCheck_ok_shape ps bytes h, (Option.some.inj h').symm⟩
    · rintro ⟨_, e⟩; subst e; rfl

/-- Annex 26.20's "an accepted `AllowedAssumptionSet`" at ref `s`: the
    bytes spell and their class-3-kind-0 derive digest is `s`. -/
def acceptedAllowedSet (ps : AllowParams) (setRef bytes : String) : Prop :=
  spellCheck ps bytes = okOut bytes ∧ ps.derive bytes = .inl setRef

/-- An accepted set always decodes to its spelled member list: a consumer
    resolving `allowed_assumption_set_ref` never reads `none` off an
    accepted object. -/
theorem acceptedAllowedSet_decode (ps : AllowParams) (s b : String)
    (h : acceptedAllowedSet ps s b) :
    decodeAllowedAssumptionSet ps b = some (csvTokens b) :=
  (decodeAllowedAssumptionSet_iff ps b _).mpr ⟨h.1, rfl⟩

/-- Fail closed: bytes that do not spell decode to `none` — there is no
    default member list. -/
theorem decodeAllowedAssumptionSet_none_of_unspelled (ps : AllowParams)
    (b : String) (h : (spellCheck ps b).ok = 0) :
    decodeAllowedAssumptionSet ps b = none := by
  unfold decodeAllowedAssumptionSet; rw [if_pos h]

end Rcic.Scm.Allow
