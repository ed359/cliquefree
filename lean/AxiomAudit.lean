module

import Cliquefree.Blueprint
import Solution
import Lean.Util.CollectAxioms

/-!
Fail if a project declaration depends on an admitted proof or a nonstandard axiom,
or if the blueprint or a mathematical module is outside the existence proof.
This audits the `Cliquefree` development and the `CliquefreeResults` Comparator solution.
-/

open Lean in
run_cmd do
  -- The audit needs transitive theorem bodies, which ordinary module imports omit.
  enableInitializersExecution
  let env ← importModules #[{ module := `Cliquefree.Blueprint }, { module := `Solution }]
    {} (loadExts := true) (level := .private)
  let isProject := fun name : Name =>
    (`Cliquefree).isPrefixOf name || name.toString.startsWith "_private.Cliquefree."
  let mut dependencies : NameSet := {}
  let mut modules : NameSet := {}
  let mut pending := #[``Cliquefree.existenceTheorem]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if dependencies.contains name then continue
    dependencies := dependencies.insert name
    let some info := env.find? name
      | throwError "Missing existence dependency: {name}"
    if let some index := env.getModuleIdxFor? name then
      modules := modules.insert env.allImportedModuleNames[index]!
    pending := pending ++ info.getUsedConstantsAsSet.toArray.filter isProject
  for name in env.allImportedModuleNames do
    if (`Cliquefree).isPrefixOf name && name != `Cliquefree &&
        name != `Cliquefree.Blueprint && !modules.contains name then
      throwError "Module {name} contributes no declaration to existenceTheorem"
  let some blueprintIndex := env.getModuleIdx? `Cliquefree.Blueprint
    | throwError "Blueprint metadata is missing"
  let nodes := Architect.blueprintExt.getModuleEntries env blueprintIndex
  for (_, node) in nodes do
    unless dependencies.contains node.name do
      throwError "Blueprint node {node.latexLabel} is outside the existence proof: {node.name}"
  logInfo m!"Existence scope audit passed: {modules.size} mathematical modules, \
    {nodes.size} blueprint nodes."
  let entries := (dependencies.toArray.qsort Name.lt).map fun name =>
    Json.mkObj [("name", toJson name.toString)]
  IO.FS.writeFile ".lake/build/existence-dependencies.json" (Json.arr entries).pretty

  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Cliquefree).isPrefixOf name || (`CliquefreeResults).isPrefixOf name then
      let axioms ← withEnv env (collectAxioms name)
      let unexpected := axioms.filter fun ax ↦ !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "{name} depends on forbidden axioms: {unexpected}"
      count := count + 1
  logInfo m!"Axiom audit passed for {count} project declarations."
