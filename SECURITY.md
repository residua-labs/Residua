# Security Policy

## Reporting a vulnerability

Please report security vulnerabilities through GitHub's private
vulnerability reporting on this repository (**Security → Advisories →
Report a vulnerability**). Do not open a public issue.

If private reporting is unavailable, open an issue that only asks for
a private contact — do not include details.

We aim to acknowledge a report within 7 days and to answer with an
assessment or questions within 30.

## Scope

In scope:

- The bootstrap recipe (`bootstrap/seed/`) — for example a path that
  lets a poisoned download pass its checks, or a recipe step whose
  output is not the documented fixed point.
- The source-archive verification documents (`docs/VERIFY-RELEASE.md`)
  — a check that accepts what it claims to reject.
- The `rsd` build tool's content store — a payload stored or served
  under an address that does not match its inputs.
- The shipped formal-semantics texts insofar as a checker accepts a
  statement they claim to refuse.

Out of scope: denial of service against the GitHub infrastructure,
and anything requiring modification of a published tag or archive —
published tags are immutable by policy.

## Supported versions

The latest published release only. Fixes ship in the next release;
there is no back-port line yet.
