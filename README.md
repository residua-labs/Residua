# Residua

<!-- BEGIN RCIC -->
## RCIC

`lean/rcic/` is the Lean 4 formalization of **R-CIC-0**, the dependent type theory that the Residua proof kernel targets. Build it with `lake build RCIC`. Its seal is `lean/rcic/RcicKernelSeal.lean`.

`closure_claim = 0`. The three kernel rows are proved within a scope check and open beyond it. See [`lean/rcic/README.md`](lean/rcic/README.md) for what is included, what is not claimed, the trust base and how to build.
<!-- END RCIC -->
