import Effect.Device

namespace Effect.ABI

open Format

def abiId : String := "residua.effect.9p2000.v1"

def version9P : Bytes := ascii "9P2000"

def noTag : Nat := 65535

def noFid : Nat := 4294967295

def maxSigned : Nat := 2^63 - 1

structure Profile where
  revision : I64
  offer : I64
  maxSteps : I64
  maxData : I64
  timeout : I64
  deriving DecidableEq, Repr

def Profile.schema : Schema := record
  [("revision", .i64), ("msize_offer", .i64), ("max_steps", .i64), ("max_data", .i64),
    ("step_timeout_ms", .i64)]

def Profile.q (p : Profile) : Bytes := Format.q Profile.schema
  (p.revision, p.offer, p.maxSteps, p.maxData, p.timeout, ())

def Profile.valid (p : Profile) : Bool :=
  p.revision == 1 && 256 ≤ p.offer.toNat && p.offer.toNat < 2^32 &&
  p.maxSteps.toNat ≤ maxSigned && p.maxData.toNat < 2^32 &&
  1 ≤ p.timeout.toNat && p.timeout.toNat ≤ maxSigned

structure Invocation where
  argv : List Bytes
  stdin : Bytes
  cwd : Bytes
  manifestQ : Bytes
  envQ : Bytes
  fuel : I64

def Invocation.schema : Schema := record
  [("argv", .list .bytes), ("stdin", .bytes), ("cwd", .bytes), ("manifest_q", .bytes),
    ("env_q", .bytes), ("fuel", .i64)]

def Invocation.value (i : Invocation) : Invocation.schema.Value :=
  (i.argv, i.stdin, i.cwd, i.manifestQ, i.envQ, i.fuel, ())

inductive ProgramResult (result : Schema) where
  | value (v : result.Value)
  | residue (code : I64)
  | fuel
  | stuck (code : I64)
  | refused (code : I64)

def ProgramResult.schema (result : Schema) : Schema := .sum (.cons result
  (.cons .i64 (.cons (.record .nil) (.cons .i64 (.cons .i64 .nil)))))

def ProgramResult.encoded {t : Schema} : ProgramResult t → (ProgramResult.schema t).Value
  | .value v => .inl v
  | .residue code => .inr (.inl code)
  | .fuel => .inr (.inr (.inl ()))
  | .stuck code => .inr (.inr (.inr (.inl code)))
  | .refused code => .inr (.inr (.inr (.inr code)))

/-- The plan declares the complete Results type. Cores with several kinds
of terminal outcome can use the sum encoded by `ProgramResult`. -/
abbrev Result (declared : Schema) := declared.Value

inductive Step (state result : Schema) where
  | send (continuation : state.Value) (raw : Bytes)
  | done (outcome : Result result)

/-- A verifier fixes the pure invocation semantics and codecs before resolving
an input context. The selected module and all its values are typed data. -/
structure Core where
  modelQ : Bytes
  invocationCodecQ : Bytes
  programType : Schema
  inputType : Schema
  stateType : Schema
  resultType : Schema
  validates : programType.Value → inputType.Value → Invocation → Bool
  invoke : programType.Value → inputType.Value → Invocation →
    Option (stateType.Value × Bytes) → Step stateType resultType

structure Manifest where
  revision : I64
  moduleQ : Bytes
  invocationCodecQ : Bytes
  maxFuel : I64
  maxInputBytes : I64

def Manifest.schema : Schema := record
  [("revision", .i64), ("module_q", .bytes), ("invocation_codec_q", .bytes), ("max_fuel", .i64),
    ("max_input_bytes", .i64)]

def Manifest.q (m : Manifest) : Bytes := Format.q Manifest.schema
  (m.revision, m.moduleQ, m.invocationCodecQ, m.maxFuel, m.maxInputBytes, ())

structure Plan (core : Core) where
  program : core.programType.Value
  inputs : core.inputType.Value
  manifest : Manifest
  invocation : Invocation

def typeQ (type : Schema) : Bytes := Format.q .bytes type.typeBytes

def Plan.schema (core : Core) : Schema := record
  [("core_q", .bytes), ("program", core.programType), ("inputs", core.inputType),
    ("manifest_q", .bytes), ("invocation", Invocation.schema),
    ("state_type_q", .bytes), ("results_type_q", .bytes)]

def Plan.q {core : Core} (p : Plan core) : Bytes := Format.q (Plan.schema core)
  (core.modelQ, p.program, p.inputs, p.manifest.q, p.invocation.value,
    typeQ core.stateType, typeQ core.resultType, ())

def Plan.valid {core : Core} (p : Plan core) : Bool :=
  let m := p.manifest
  let i := p.invocation
  core.modelQ.length == 32 && core.invocationCodecQ.length == 32 &&
  m.revision == 1 && m.moduleQ == Format.q core.programType p.program &&
  m.invocationCodecQ == core.invocationCodecQ && i.manifestQ == m.q && i.envQ.length == 32 &&
  m.maxFuel.toNat ≤ maxSigned && i.fuel.toNat ≤ m.maxFuel.toNat &&
  m.maxInputBytes.toNat ≤ maxSigned &&
  (canonical Invocation.schema i.value).length + (canonical core.inputType p.inputs).length ≤
    m.maxInputBytes.toNat && core.validates p.program p.inputs i

def Plan.invoke {core : Core} (p : Plan core) (resume : Option (core.stateType.Value × Bytes)) :
    Step core.stateType core.resultType := core.invoke p.program p.inputs p.invocation resume

structure Context (core : Core) where
  abi : String
  nsQ : Bytes
  profileQ : Bytes
  planQ : Bytes
  ns : Option Namespace
  profile : Profile
  plan : Option (Plan core)

def Context.value {core : Core} (c : Context core) : contextSchema.Value :=
  (c.abi, c.nsQ, c.profileQ, c.planQ, ())

def Context.q {core : Core} (c : Context core) : Bytes := Format.q contextSchema c.value

def Context.digestsValid {core : Core} (c : Context core) : Bool :=
  c.abi == abiId && [c.nsQ, c.profileQ, c.planQ].all (fun q => q.length == 32) &&
  c.ns.all (fun ns => ns.q == c.nsQ) && c.profile.q == c.profileQ &&
  c.plan.all (fun p => p.q == c.planQ)

def Context.openingQ {core : Core} (c : Context core) : Bytes :=
  opening c.abi c.nsQ c.profileQ c.profile.offer c.planQ

def Context.authority {core : Core} (c : Context core) (registry : Registry)
    (path : Path) : Option PathAuthority :=
  c.ns.bind fun ns => ns.authority registry path

def Context.declares {core : Core} (c : Context core) (registry : Registry) (path : Path) : Bool :=
  (c.authority registry path).isSome

def Context.policy {core : Core} (c : Context core) (registry : Registry) (path : Path) : Option Rule :=
  (c.authority registry path).bind PathAuthority.policy

theorem Context.policy_declared {core : Core} (c : Context core) (registry : Registry)
    (path : Path) (h : (c.policy registry path).isSome = true) :
    c.declares registry path = true := by
  cases e : c.authority registry path <;> simp_all [Context.declares, Context.policy]

end Effect.ABI
