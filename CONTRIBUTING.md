# Contributing

English | [中文](CONTRIBUTING.zh-CN.md)

Thank you for your interest in Residua.

## How development works

Residua is developed in a private workspace by the project team; this
public repository is the published source of each release. Day-to-day
development, code review and the audit trail do not happen here, so
pull requests cannot be merged directly.

## What you can do

- **Open an issue** for bugs, unclear documentation, wrong claims in
  the verification documents, or feature requests. Reproductions of the
  seed recipe on machines we have not tried are especially welcome —
  post your host (`uname -a`, compiler version) and the outcome.
- **Propose a change in an issue.** Describe the change and the reason;
  the maintainers take it from there. Small fixes (typos, dead links,
  a wrong digest) are often taken verbatim in the next release.
- **Report a vulnerability privately** — never in a public issue. See
  [SECURITY.md](SECURITY.md).

## Building and testing

- Rebuild the compiler from the committed seed: the recipe in
  `bootstrap/seed/*/README.md`, on Linux x86-64.
- Verify a whole release: `docs/VERIFY-RELEASE.md`.
- Run the shipped test and benchmark suites: `TESTING.md`.

## Style

The `.rsd` sources are written in the language's bootstrap subset
(`docs/LANGUAGE.md`). Public prose follows `release/TERMS.tsv` —
internal names stay out of public documents; real technical terms are
defined once in `docs/GLOSSARY.md`.

## Conduct

Participation is covered by the [Code of Conduct](CODE_OF_CONDUCT.md).
