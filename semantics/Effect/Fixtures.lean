import Effect.Judgment
import Effect.WireBuild

/-! A finite model and declared fixture devices for protocol experiments.
The model reads a program consisting of exact request instructions. -/
namespace Effect.ABI.Fixtures

open Wire Format

def request (t : Wire.Request) (tag : Nat := 0) : Bytes :=
  (Build.request t tag).getD []

def reply (r : Wire.Reply) (tag : Nat := 0) : Bytes :=
  (Build.reply r tag).getD []

def fixtureCore : Core where
  modelQ := Format.q .str "residua.effect.fixture.literal-request-program.r1"
  invocationCodecQ := Format.q .str "residua.effect.fixture.i64-results.r1"
  programType := .list .bytes
  inputType := .record .nil
  stateType := .list .bytes
  resultType := .i64
  validates := fun _ _ invocation => invocation.fuel == 1
  invoke := fun program _ _ continuation =>
    match (continuation.map Prod.fst).getD program with
    | [] => .done (42 : Format.I64)
    | t :: ts => .send ts t

def makePlan (program : List Bytes) : Plan fixtureCore :=
  let manifest : Manifest := ⟨1, Format.q (.list .bytes) program, fixtureCore.invocationCodecQ,
    1, 8192⟩
  ⟨program, (), manifest, ⟨[], [], [], manifest.q, Format.q .bytes [], 1⟩⟩

def fsPath : Path := [ascii "fs", ascii "root"]

def cmdPath : Path := [ascii "cmd", ascii "echo", ascii "ctl"]

def execLine : Bytes := ascii "exec\n"

private def registration (item : String) (paths : List Path) (rules : List Rule)
    (edges : List Transition := []) : Registration :=
  { contract := ⟨1, item, rules, 0, edges, Format.q .str (item ++ "-effect-r1"),
      Format.q .str (item ++ "-cases-r1")⟩
    config := ⟨1, Format.q .str (item ++ "-authority-r1"), paths⟩ }

def fs : Registration :=
  registration "fixture-fs" [[ascii "root"]]
    [⟨[], true, [.walk, .read, .write, .create, .clunk, .remove, .stat, .wstat, .trunc, .rclose],
      {limit := 256}, {limit := 256}⟩]

def cmd : Registration :=
  let path := cmdPath.drop 1
  registration "fixture-cmd-ctl" [[ascii "echo"]]
    [⟨[], false, [.walk, .stat, .clunk], {limit := 0}, {limit := 0}⟩,
     ⟨[ascii "echo"], false, [.walk, .stat, .clunk], {limit := 0}, {limit := 0}⟩,
     ⟨path, false, [.walk, .write, .stat, .clunk], {limit := 0},
      {limit := 16, atomic := true, recordLimit := 16, grammar := .exact [execLine]}⟩]
    [⟨0, .write, path, 1, false⟩]

def registry : Registry := [cmd, fs]

def fixtureNS : Namespace :=
  ⟨1, [⟨ascii "cmd", cmd.contract.q, cmd.config.q⟩, ⟨ascii "fs", fs.contract.q, fs.config.q⟩]⟩

def profile : Profile := ⟨1, 256, 32, 128, 1000⟩

def context (program : List Bytes) (usage : Profile := profile)
    (ns : Namespace := fixtureNS) : Context fixtureCore :=
  let plan := makePlan program
  ⟨abiId, ns.q, usage.q, plan.q, some ns, usage, some plan⟩

def rootQid : Wire.Qid := ⟨128, 0, 1⟩

def fsQid : Wire.Qid := ⟨128, 0, 2⟩

def dirQid : Wire.Qid := ⟨128, 0, 3⟩

def fileQid : Wire.Qid := ⟨0, 0, 4⟩

def versionPair (offer server : Nat := 256) : RawPair :=
  ⟨request (.version offer version9P) noTag, reply (.version server version9P) noTag⟩

def attachPair (ns : Namespace := fixtureNS) : RawPair :=
  ⟨request (.attach 0 noFid [] (lowerHex ns.q)), reply (.attach rootQid)⟩

def walkPair : RawPair :=
  ⟨request (.walk 0 1 fsPath), reply (.walk [fsQid, dirQid])⟩

def filePair : RawPair :=
  ⟨request (.walk 1 1 [ascii "file"]), reply (.walk [fileQid])⟩

def openPair (mode : Nat) (iounit : Nat := 0) : RawPair :=
  ⟨request (.openFile 1 mode), reply (.openFile fileQid iounit)⟩

def cmdPair : RawPair :=
  ⟨request (.walk 0 1 cmdPath), reply (.walk [fsQid, dirQid, fileQid])⟩

def prefixPairs : List RawPair := [versionPair, attachPair]

def exactContext (rows : List RawPair) (usage : Profile := profile) : Context fixtureCore :=
  context (rows.map RawPair.t) usage

def exampleContext : Context fixtureCore := exactContext (prefixPairs ++ [walkPair])

def statOf (qid : Wire.Qid) (name : Bytes := ascii "file") : Wire.Stat :=
  ⟨0, 0, qid, if qid.directory then 0x800001ff else 0x1ff, 0, 0, 0,
    name, ascii "owner", [], []⟩

def noStatChange : Wire.Stat :=
  ⟨65535, noFid, ⟨255, noFid, noLengthChange⟩, noFid, noFid, noFid,
    noLengthChange, [], [], [], []⟩

def emptyStore : ObjectStore := fun _ => none

end Effect.ABI.Fixtures
