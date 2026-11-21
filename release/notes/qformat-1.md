# Release note — typed content address (q format v1)

English | [中文](qformat-1.zh-CN.md)

Status: **shipped in release 0.2**; the summary also appears in
`docs/RELEASE-NOTES.md`. `closure_claim = 0`.

## What it provides

Every content identity in the tree now carries its kind inside the hashed
bytes: `q(kind, c) = SHA-256("<kind> <len>\0" ++ c)`, the git object-header
convention with a versioned kind registry, printed as
`sha256:<hex>` (multihash `0x12 0x20` in self-describing binary). Raw
SHA-256 remains, renamed `digest`, for file integrity and interop only.
Two different kinds of content can no longer share one address; the seven
measured cross-kind collisions of the untagged format cannot recur.

The published form is `docs/QFORMAT.md` (specification, kind
registry v1, comparison rule, limits). The conformance check is
`release/checks/qformat/` (six vectors and two planted controls,
recomputable with `sha256sum` alone).

## Acceptance evidence

- Source revision: `6d700789ebbf04825ab7d1c3f1baa715a124a051`
  (on the development `main` branch).
- Independent audit: verdict **SIGN** at that sha, 8 attacks tried, no
  counterexample; transcript `reports/release-02/evidence/
  AUDIT-QFORMAT-1.6d700789eb.md` (copied into the packet from the
  development contracts repository).
- Controls at the landed head (all negative controls armed):
  349 hashing sites inventoried, 0 untagged identities after the batch;
  separation vectors pairwise distinct; interop control (`digest` ==
  `sha256sum`) unchanged; a crafted-preimage mutant refused by typed
  comparison; per-kind store round trips at the landed head; the seed
  light sample 8/8 `MODULE_EQUAL_NATIVE` — the batch does not change
  emitted bytes, so no performance rows are owed.

## Limits

- The `scc` kind is reserved; mutually recursive groups get one q per
  component only after the canonical member order is published.
- The registry is version 1 and append-only; kind canonical forms do
  not change under a kind.
- A printed `sha256:` field is typed by its schema, not self-describing
  as digest vs q.
- Third-party verification task for this goal (the release's stranger
  check): recompute a published q from kind and bytes, per
  `release/checks/qformat/README.md`.
