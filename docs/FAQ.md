# FAQ

English | [中文](FAQ.zh-CN.md)

- **Why a Lean subset?** It is the bootstrap surface: the compiler's
  own sources are written in it, and Lean's parser and kernel serve as
  oracles. It is not the final language design.
- **Does Residua depend on Lean?** Building and running 0.3 needs no
  Lean. Lean checks the formal semantics and is the reference for
  kernel rules and the parser.
- **Why not just use Lean?** For compiling and proving in one tool
  today, Lean is more complete. Residua's aims are different: results
  identified by content across tools and versions, admitted by
  mechanical checking, and a compiler you can reproduce from a small
  [seed](GLOSSARY.md).
- **Who is it for, and who builds it?** Residua is for agents, by
  agents: it is built by AI agents, and every change is accepted by
  mechanical checks (differential gates, planted mutants, fixpoints)
  and reviews by independent model families, never by trusting the
  agent that made it.
