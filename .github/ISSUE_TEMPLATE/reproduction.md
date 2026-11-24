---
name: Seed-recipe reproduction
about: Report a run of the bootstrap recipe on your machine
title: "Reproduction: <os> <arch>"
labels: reproduction
---

**Host** — `uname -a`, C compiler (`cc --version` first line), RAM.

**Steps** — the exact commands you ran (from
`bootstrap/seed/*/README.md`).

**Result** — did the rebuilt compilers match the committed seed byte
for byte? Attach the recipe's `seed_roundtrip`/`images` line and your
`run.log` tail if it failed.
