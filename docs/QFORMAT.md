# QFORMAT — the typed content address, version 1

English | [中文](QFORMAT.zh-CN.md)

## Purpose and scope

Residua names immutable content by *q*, a typed content address. This
document is the specification of version 1 of that address: the two
addresses in use (`digest` and `q`), the hashed preimage grammar, the
printed and binary representations, the registry of kinds, and the rule
every comparison site follows. It governs every `sha256:`-printed field
in the release — artifact tables, store keys, receipts, manifests — and
the conformance vectors in `release/checks/qformat/`. The working
documents the batch was designed and measured under remain
repository-side (`reports/qformat/`); this file is the published form.

## Motivation

A content address lets a party reuse a result without trusting its
producer, because the name is recomputed from the content. The scheme
only works if two different kinds of content can never share one name.
Before this specification, every identity in the tree was the raw
SHA-256 digest of its bytes. A measured inventory (349 hashing sites,
213 of them identities) found seven concrete collisions in which bytes
of one meaning hashed to the same value as bytes of another — for
example a seven-byte file `5:hello` and the S-expression atom `hello`
shared one address. An address that two kinds can share is not an
address. The fix is not a new hash function but a typed preimage: the
kind is written into the hashed bytes, so equal bytes under two kinds
produce different addresses by construction.

## Two addresses

**digest** — `digest(b) = SHA-256(b)`, the raw bytes, no header.
Role: file integrity and interop; it is exactly what `sha256sum`
prints. A digest is never an identity and never appears where a `q` is
expected.

**q** — `q(kind, c) = SHA-256(header ++ c)`, where `header` is the
preimage grammar below and `c` is the kind's canonical byte string.
Role: typed identity. "Equal meaning gives equal q" holds *within* a
kind. Equal bytes under two kinds give different q's, always, by
construction — the header differs — not by luck.

## The preimage grammar

    preimage := kind SP len NUL canonical
    kind     := [a-z][a-z0-9-]*          (at most 32 bytes, from the registry)
    len      := decimal byte length of canonical, no leading zeros;
                "0" for the empty canonical
    NUL      := 0x00

The header is exactly the git object-header convention
`<type> <len>\0` [1], with the type drawn from a registry rather than a
fixed set. `len` makes the header self-terminating; neither byte of
`kind` can be `SP` or `NUL`.

For every version-1 kind, `canonical` is the byte string the producing
site already hashed — encodings, length prefixes and container tags
stay inside the canonical bytes, unchanged. The batch changed only the
preimage: `SHA-256(b)` became `SHA-256(header ++ b)`. No codec, record
layout or serialization changed.

## Representation

| context | form |
|---|---|
| printed text fields (manifest values, receipt bindings, tables, logs) | `sha256:` + 64 lowercase hex, for both digest and q |
| path segments and file names | `sha256-` + 64 hex |
| self-describing binary (a q stored with no schema around it) | multihash `0x12 0x20` + 32 bytes (34 bytes total) [2] |
| inside a schema-typed record | 32 raw bytes; the schema carries algorithm and kind |

A printed `sha256:<hex>` does not by itself say `digest` or `q:<kind>` —
the field it sits in does. Every field, record slot, path namespace and
store that carries a content address is typed: `digest`, or `q:<kind>`
with the kind from the registry.

## Kind registry, version 1

The registry is append-only: a kind string, once used in a published
preimage, is never repurposed; a changed canonical form is a new kind.
The *exclusions* column is what the canonical form omits (the
peer-design rule of publishing each kind's hash-input exclusion list);
version-1 kinds exclude nothing — their bytes are already canonical
serializations.

| kind | canonical form | exclusions |
|---|---|---|
| `blob` | the raw content bytes | none — bytes are the content |
| `rsx-atom` | `itoa len ++ ":" ++ atom` | none |
| `rsx-list` | `"(" ++ "32:q₁" … ++ ")"` | none |
| `nf-key` | `NF1 ++ stage ++ node-q ++ sigQ ++ ctx ++ compiler ++ profile` | none |
| `nf-ctx` | encLL context bytes | none |
| `nf-profile` | encList layI ++ profile scalars | none |
| `nf-sig` | encList signature | none |
| `nf-node` | encList node bytes | none |
| `rval` | encodeRVal output (keeps `RVAL\x01` inside) | none |
| `receipt` | canonOpen / canonStep bytes | none |
| `verdict` | the RVAL record of the ten verdict fields: subject kind+q, statement q, axiom-set q, theory-profile q, observation q, instance-context q, environment q, checker q, policy q, trust-cut q | none — all ten fields hash |
| `decl-line` | one declaration line's bytes | none |
| `decl-bundle` | concatenated line bytes | none |
| `text` | fixed UTF-8 text bytes | none |
| `gate` | the syntax-gate byte stream | none |
| `cwasm-key` | `wasmQ ++ 0 ++ hostQ` | none |
| `scc` | RESERVED: `"(" ++ n ++ (":" ++ i ++ ":" ++ len(cᵢ) ++ ":" ++ cᵢ)* ++ ")"` — member count, then per member its decimal index, byte length and canonical bytes, in the group's published canonical order | member kinds' exclusions apply to each `cᵢ` |

An identity of raw byte content is `blob` wherever the bytes live — a
kind says how to interpret bytes, not which program wrote them. A kind
other than `blob` exists only where the hashed bytes are constructed at
hash time as a canonical serialization.

## The comparison rule

Every verifier that recomputes a q carries the expected kind:
`hashOk kind`, `verifyObject kind`, `cacheHit kind`. A store's kind is
declared per namespace of each deployment, and entries are addressed by
the namespace-kind q. Two consequences a reader should know:

- A file whose bytes happen to equal a valid tagged preimage (for
  example the 18 bytes `"rsx-atom 7\x005:hello"`) digests to the same
  value as `q(rsx-atom, "5:hello")`. That is unavoidable and harmless:
  the digest is byte-exact by interop, and a comparison site refuses a
  digest field where a `q:rsx-atom` is expected. The shipped vectors in
  `release/checks/qformat/` demonstrate exactly this pair.
- Two `blob` stores holding the same bytes answer the same q. That is
  by design: a q names content, not which store holds it.

Interning rule (unchanged): in memory a hash is a lookup key, and a hit
is confirmed by structural equality of the preimage before use — typed
preimages make the confirmation include the header.

## Mutually recursive groups (reserved)

A strongly connected component is hashed and checked as one unit: one
`q(scc, …)` per group, member canonicals in published canonical order
with member indexes — never per-member q's that let members certify
each other. `scc` is reserved in the registry; the member order is
published when the canonical SCC encoding lands. Until then no producer
may emit `scc` preimages.

## Three identities stay distinct

`q` (typed content identity), a snapshot cut, and durable handles
across edits are three different names. Fields and protocols never
substitute one for another. This specification governs only `q`.

## Checking a published q

Any `q:<kind>` printed in this release can be recomputed with only
`sha256sum`, `printf` and `cat`:

```sh
{ printf '%s %d\0' "<kind>" "$(wc -c < bytes | tr -d ' ')"; cat bytes; } \
  | sha256sum
```

`release/checks/qformat/` contains pinned vectors for five kinds plus
the planted controls (kind separation, the digest–q boundary, and the
crafted-preimage case above), each with the command that produced it
and the expected output.

## Trust assumptions and limitations

- Collision resistance of SHA-256 is assumed [FIPS 180-4]; typing is by
  the preimage and the field schema, not by the printed form.
- The registry is version 1 and append-only; a kind whose canonical
  form needs to change is a new kind, so published q's never move.
- `scc` is reserved but has no producer yet (member order unpublished).
- A `sha256:` field is self-describing only as an algorithm-tagged
  digest or q; the kind is carried by the field's declared type, so two
  fields printing the same hex under different declared kinds are
  different addresses, never one.
- Digest fields remain raw SHA-256 for interop; only identity fields
  carry the header.

## References

1. Git object format (`<type> <len>\0`): S. Chacon, B. Straub,
   *Pro Git*, 2nd ed., ch. 10.2; `gitrepository-layout(5)`.
2. Multihash (algorithm and length prefix; sha2-256 = `0x12`, length
   `0x20`): multiformats/multihash specification.
3. E. Dolstra. *The Purely Functional Software Deployment Model*.
   PhD thesis, Utrecht University, 2006 — Nix store paths hash a typed
   fingerprint; `narHash` carries an algorithm prefix.
4. P. Chiusano, R. Bjarnason et al. Unison: content-addressed
   definitions with SCCs hashed as one unit — unisonweb/unison.
5. Vercel Labs, zerolang (v0.3.4): kind-prefixed printed hashes and a
   published hash-input exclusion list — peer design study.
6. J.-C. Filliâtre, S. Conchon. Type-safe modular hash-consing.
   *ACM SIGPLAN Workshop on ML*, 2006 — a hash is a lookup key; a hit
   is confirmed by structural equality before use.
7. H. Barendregt, F. Wiedijk. The challenge of computer mathematics.
   *Phil. Trans. R. Soc. A* 363, 2005 (the de Bruijn criterion).
