import BANANA
import Lean

/-!
Audit-only entry point: apply Lean's own collectAxioms (the implementation
used by #print axioms) separately to every visible project-owned constant
in the compiled BANANA import closure. This is not imported into BANANA.
The archived inventory is also the coverage oracle for manuscript links.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name :=
    #[.str .anonymous "BANANA"]
  let allowed : List String := ["propext", "Classical.choice", "Quot.sound"]
  let modules := env.header.moduleNames
  for modName in modules do
    if (Name.str .anonymous "SuccessorTree").isPrefixOf modName ||
        (Name.str .anonymous "RamseySpace").isPrefixOf modName then
      throwError "Unexpected external project module {modName}"
  let entries := env.const2ModIdx.toList.filterMap fun (decl, idx) =>
    let modName := modules[idx.toNat]!
    if roots.any (fun root => root.isPrefixOf modName) then
      some (modName, decl)
    else none
  let mut checked := 0
  let mut unavailable := 0
  for (modName, decl) in entries do
    if (env.find? decl).isNone then
      -- Some module-system private constants need not be imported.
      -- Do not claim a direct audit of these unavailable names.
      unavailable := unavailable + 1
    else
      let axioms ← Lean.collectAxioms decl
      for ax in axioms do
        unless allowed.contains ax.toString do
          throwError "Forbidden axiom {ax} in {modName}: {decl}"
      let deps := String.intercalate "," (axioms.toList.map fun a => a.toString)
      liftIO <| IO.println s!"PROJECT_AXIOMS\t{modName}\t{decl}\t{deps}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations audited"
  liftIO <| IO.println s!"PROJECT_AXIOMS_DONE\t{checked}\t{unavailable}\t{entries.length}"
