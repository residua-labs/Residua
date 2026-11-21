# Release note — syntax engine, closed over its grammar class

English | [中文](syntax-engine.zh-CN.md)

Status: **shipped in release 0.2**; the summary also appears in
`docs/RELEASE-NOTES.md`. `closure_claim = 0`.

## What it provides

The parser is one function: (a grammar of the class given as data, an
input) -> a tree or a named, located refusal. The class is
`semantics/Syntax/Class.rsd`: `SynSpec.Grammar`, the `Parses` relation
and the reference decider `refParses` with its soundness proof
(axioms `propext`, `Quot.sound`). Engine sources are `rsdc/syntax/`; a
surface is data in `rsdc/profiles/*.syn` — a new profile is added with
an empty diff under `rsdc/syntax/`. The shipped compiler's accepted
surface is unchanged (the `.rsd` bootstrap subset of
`docs/LANGUAGE.md`).

## Acceptance evidence

- Source revision: `28b9ff89f10514b93de92b8c0f60a109660ffa49` (on the
  development `main` branch).
- Independent audit: verdict **SIGN** at that sha; transcript
  `reports/release-02/evidence/AUDIT-SYNTAX-ENGINE.28b9ff89f1.md`
  (copied into the packet from the development contracts repository).
- Agreement with the class (E2): `rsdc/syntax/ClassGate.rsd` over 240
  generated grammars and 4,334 generated inputs —
  `disagreements=0`; each grammar carries a mutant that changes a
  `refParses` verdict (240/240 armed), and coverage is checked: rhs
  lengths 0..3, precedence −1..2, associativity 0..3, disambiguation
  0..3, choice sizes 1..3, layout ops 12/12, scoped ops 12/12,
  boundary ops 7/7.
- Tier equality (E3): on the fast tier's subclass, Earley and Pratt
  tiers give the same tree or both refuse — 224 grammars, 5,679
  checks, `disagreements=0`; the armed control `mkA1 16` separates the
  tiers (`err=72` vs `err=90`).
- Engine-ness (E4): the `rse.syn` profile was added with an empty diff
  under `rsdc/syntax/`.
- Totality and determinism (E5): 1,122 rule-reversal stress checks;
  equal (grammar q, input) gives equal tree q on two hosts.
- Cost bound (E6): growth measured on generated inputs — Earley adds
  ratio ≈2.00 and Pratt steps ratio ≈2.00 at doubling sizes; the
  guarded column cache ratio 1.999 vs its uncached control 3.97
  (armed), per the published bound (Leo 1991 for the Earley tier).

## Limits

- Profiles outside the class are named in
  `reports/synspec/OUTSIDE-CLASS.tsv` (repository-side); a
  language needing a construct outside the class is a class revision,
  not an engine edit.
- Per-language corpus acceptance is a property of each profile, not of
  the engine.
