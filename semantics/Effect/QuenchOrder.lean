import Lean
import Lean.Util.FoldConsts
import Lean.Util.SCC

/-! Causal ordering for Quench V1, which admits declarations in file order. -/
open Lean

private def dependencies (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo theoremInfo => theoremInfo.type.getUsedConstants ++ theoremInfo.value.getUsedConstants
  | _ => #[]

def main : List String → IO Unit
  | [source, destination] => do
    let (data, _) ← readModuleData source
    let index := data.constants.foldl (fun table ci => table.insert ci.name ci)
      ({} : Std.HashMap Name ConstantInfo)
    let successors := fun name =>
      ((index[name]?.map dependencies).getD #[]).toList.filter index.contains
    let groups := SCC.scc (data.constants.toList.map ConstantInfo.name) successors
    let names := groups.flatten
    if groups.any (fun group => group.length != 1) || names.length != data.constants.size then
      throw (IO.userError "cycle or duplicate in theorem declarations")
    let ordered ← names.toArray.mapM fun name =>
      match index[name]? with
      | some ci => pure ci
      | none => throw (IO.userError s!"missing declaration {name}")
    saveModuleData destination `Effect.MonitorLaws { data with
      constants := ordered, constNames := ordered.map ConstantInfo.name }
  | _ => throw (IO.userError "expected source and destination olean paths")
