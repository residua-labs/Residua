/-
CT-021 policy-half pins — `ScmAllow.allowCheck`/`mutantCheck` evaluated
at grok C's `apps/rcic-ct-allow/rcic_ct_allow_corpus.json` VERBATIM: the
same 17 rows, the same presented bytes, the same expected `AllowOut`
(`{ok, canon, code}` — `group_codec_ok digest | group_codec_refuse code`).
One corpus shared by Lean and scm; if the carrier's corpus changes, this
file is regenerated, not edited.

Corpus facts baked in:
  - spell refusals carry the closure carrier's names:
    `[rcic_dep_closure_parse]` (empty token / token > 2048 codepoints —
    name 12) and `[rcic_dep_closure_canon]` (unsorted or duplicate join —
    name 9). `AllowParams` is instantiated with those real codes.
  - `corpusParams.derive` is the corpus's derive table: the four spelled
    policies that reach `rcic.derive 3 0` map to their real digests; any
    other bytes refuse (no corpus row exercises that arm — every policy
    that reaches derive is spelled).
  - the landed mutant omits form, ref AND subset: it diverges on exactly
    the six corpus rows below (subset ×3, ref ×2, form ×1) and agrees on
    the other eleven.

Byte-level pins are `#guard`s: `String.splitOn`/`intercalate`/`decEq`
are extern-backed, so they run under compiled evaluation, not kernel
reduction — same convention as `ScmRows`' pins. Theorem-level pins are
kept to the parts that reduce kernel-side (the form arm; empty bytes).
The soundness/separation content lives in `ScmAllow`'s sealed theorems.
-/
import rcic.ScmAllow

namespace Rcic.Scm.Allow

/-- A token of `n` `Z`s — the corpus's length-boundary token
    (rows 12/14 are spelled with 2049 and exactly 2048 codepoints). -/
def zTok (n : Nat) : String := String.mk (List.replicate n 'Z')

/-- The four real policy digests the corpus presents. -/
def digEmpty : String :=
  "69e864cdae72390a21426e4ab96f10788672c3b356cb81b4131ac475749eca42"
def digAB : String :=
  "7cdf61f44c002811e09e49ccae338b7e95270a58eec54199d7136ac58792d25b"
def digA : String :=
  "96f37262cbb4f8dcab7dd94b2be5f66d187a73b77e47916a9982bd314e52748e"
def digZ : String :=
  "839a70698542a4605b8383525aef51f9aa0ffc4eb47e76672f75b663c1ec27db"

/-- Corpus parameters: `rcic.derive 3 0` read off the corpus — the four
    spelled policies map to their real digests; any other bytes refuse
    (unreached in the corpus: an unspelled policy never reaches derive).
    The two spell codes are the closure carrier's real names. -/
def corpusParams : AllowParams where
  derive := fun b =>
    if b = "" then .inl digEmpty
    else if b = "A,B" then .inl digAB
    else if b = "A" then .inl digA
    else if b = zTok 2048 then .inl digZ
    else .inr "[rcic_derive_refused]"
  badTokCode := "[rcic_dep_closure_parse]"
  nonCanonCode := "[rcic_dep_closure_canon]"

/-- Empty bytes are the empty token list — the carrier's codec rule. -/
theorem csvTokens_empty : csvTokens "" = [] := rfl

/-- form ≠ 0 is refused before any bytes are read — for ANY presented
    bytes and params. -/
theorem allowCheck_form_refused (ps : AllowParams) (c p r : String) :
    allowCheck ps 1 c p r = noOut "[rcic_allowed_axioms_form]" := rfl

/-- The policy gate is not vacuous — abstract level: a spelled policy
    whose tokens miss a spelled closure's token refuses the subset. This
    is `allowCheck_subset_decides`'s refuse direction read off. -/
theorem allowCheck_refuses_when_not_subset (ps : AllowParams) (form : Int)
    (cb pb r : String) (d : String)
    (hf : form = 0) (hsp : spellCheck ps pb = okOut pb)
    (hsc : spellCheck ps cb = okOut cb)
    (hd : ps.derive pb = .inl d) (href : r = d)
    (hescape : ¬ ∀ t ∈ csvTokens cb, t ∈ csvTokens pb) :
    allowCheck ps form cb pb r = noOut "[rcic_allowed_axioms_subset]" := by
  have hsub : subsetAll (csvTokens cb) (csvTokens pb) = false := by
    cases hv : subsetAll (csvTokens cb) (csvTokens pb)
    · rfl
    · exact absurd ((subsetAll_iff _ _).mp hv) hescape
  unfold allowCheck
  rw [if_neg (fun h => h hf)]
  split
  · rename_i hs; rw [hsp] at hs; simp [okOut] at hs
  · split
    · rename_i hs; rw [hsc] at hs; simp [okOut] at hs
    · rw [allowRest_inl (hd := hd)]
      split
      · rename_i hr
        split
        · rename_i hs2; rw [hs2] at hsub; cases hsub
        · rfl
      · rename_i hr; exact absurd href hr

-- ### The carrier's corpus, verbatim (apps/rcic-ct-allow corpus, 17 rows)

-- row 0: empty closure and empty policy, ref is that digest
#guard allowCheck corpusParams 0 "" "" digEmpty == okOut digEmpty
-- row 1: closure A is a subset of policy A,B
#guard allowCheck corpusParams 0 "A" "A,B" digAB == okOut digAB
-- row 2: closure A,B equals policy A,B
#guard allowCheck corpusParams 0 "A,B" "A,B" digAB == okOut digAB
-- row 3: empty closure is a subset of policy A
#guard allowCheck corpusParams 0 "" "A" digA == okOut digA
-- row 4: closure B is not a subset of policy A
#guard allowCheck corpusParams 0 "B" "A" digA == noOut "[rcic_allowed_axioms_subset]"
-- row 5: closure A,B is not a subset of policy A
#guard allowCheck corpusParams 0 "A,B" "A" digA == noOut "[rcic_allowed_axioms_subset]"
-- row 6: closure A is not a subset of the empty policy
#guard allowCheck corpusParams 0 "A" "" digEmpty == noOut "[rcic_allowed_axioms_subset]"
-- row 7: presented ref is not the digest of the empty policy
#guard allowCheck corpusParams 0 "" "" "not-the-ref" == noOut "[rcic_allowed_axioms_ref]"
-- row 8: policy B,A is not the sorted join
#guard allowCheck corpusParams 0 "" "B,A" "" == noOut "[rcic_dep_closure_canon]"
-- row 9: closure B,A is not the sorted join
#guard allowCheck corpusParams 0 "B,A" "A,B" digAB == noOut "[rcic_dep_closure_canon]"
-- row 10: policy A,A is not duplicate-free
#guard allowCheck corpusParams 0 "A" "A,A" "" == noOut "[rcic_dep_closure_canon]"
-- row 11: policy A, has an empty token
#guard allowCheck corpusParams 0 "" "A," "" == noOut "[rcic_dep_closure_parse]"
-- row 12: closure token longer than 2048
#guard allowCheck corpusParams 0 (zTok 2049) "A" digA == noOut "[rcic_dep_closure_parse]"
-- row 13: form 1 is not this check
#guard allowCheck corpusParams 1 "" "" digEmpty == noOut "[rcic_allowed_axioms_form]"
-- row 14: a 2048-codepoint token is inside the length bound
#guard allowCheck corpusParams 0 (zTok 2048) (zTok 2048) digZ == okOut digZ
-- row 15: closure A,,B has an empty token
#guard allowCheck corpusParams 0 "A,,B" "A,B" digAB == noOut "[rcic_dep_closure_parse]"
-- row 16: a wrong ref is refused before the subset law
#guard allowCheck corpusParams 0 "B" "A" "not-the-ref" == noOut "[rcic_allowed_axioms_ref]"

-- ### The landed mutant on the same corpus: agrees on 11, diverges on 6

-- agreement: the five ok rows — spelling+derive suffice for the mutant too
#guard mutantCheck corpusParams 0 "" "" digEmpty == okOut digEmpty
#guard mutantCheck corpusParams 0 "A" "A,B" digAB == okOut digAB
#guard mutantCheck corpusParams 0 "A,B" "A,B" digAB == okOut digAB
#guard mutantCheck corpusParams 0 "" "A" digA == okOut digA
#guard mutantCheck corpusParams 0 (zTok 2048) (zTok 2048) digZ == okOut digZ
-- agreement: spelling refusals still propagate (not a constant)
#guard mutantCheck corpusParams 0 "" "B,A" "" == noOut "[rcic_dep_closure_canon]"
#guard mutantCheck corpusParams 0 "B,A" "A,B" digAB == noOut "[rcic_dep_closure_canon]"
#guard mutantCheck corpusParams 0 "A" "A,A" "" == noOut "[rcic_dep_closure_canon]"
#guard mutantCheck corpusParams 0 "" "A," "" == noOut "[rcic_dep_closure_parse]"
#guard mutantCheck corpusParams 0 (zTok 2049) "A" digA == noOut "[rcic_dep_closure_parse]"
#guard mutantCheck corpusParams 0 "A,,B" "A,B" digAB == noOut "[rcic_dep_closure_parse]"

-- divergence: the dropped SUBSET clause (corpus rows 4, 5, 6)
#guard mutantCheck corpusParams 0 "B" "A" digA == okOut digA
#guard mutantCheck corpusParams 0 "A,B" "A" digA == okOut digA
#guard mutantCheck corpusParams 0 "A" "" digEmpty == okOut digEmpty
-- divergence: the dropped REF clause (corpus rows 7, 16)
#guard mutantCheck corpusParams 0 "" "" "not-the-ref" == okOut digEmpty
#guard mutantCheck corpusParams 0 "B" "A" "not-the-ref" == okOut digA
-- divergence: the dropped FORM clause (corpus row 13)
#guard mutantCheck corpusParams 1 "" "" digEmpty == okOut digEmpty

end Rcic.Scm.Allow
