import ComplexityOfGenerators.Foundations
import ComplexityOfGenerators.MainTheorems
import Lean.Util.CollectAxioms

/-!
Checks every declaration imported by the project, including all current
expected-time results, the native guessed-index recognizer, concrete example
semantics, resource bridges, and historical results still retained by the API.
No declaration is excluded. Only the standard logical axioms listed below
are permitted; `sorryAx`, custom axioms, and unchecked evaluation are rejected.

Run after `lake build`: `lake env lean scripts/AuditFoundations.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if (`ComplexityOfGenerators).isPrefixOf moduleName then
      let data := env.header.moduleData[moduleIdx]
      for declaration in data.constNames do
        let dependencies ← liftCoreM (collectAxioms declaration)
        let unexpected := dependencies.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          throwError "Foundations audit: {declaration} depends on {unexpected}"
        checked := checked + 1
  logInfo m!"Foundations audit passed: {checked} local declarations; only propext, Classical.choice and Quot.sound are allowed."
