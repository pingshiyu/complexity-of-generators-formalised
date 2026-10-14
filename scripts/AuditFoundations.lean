import ComplexityOfGenerators.Foundations
import ComplexityOfGenerators.MainTheorems
import Lean.Util.CollectAxioms

/-!
Checks every declaration in the local supporting modules, including transitive
dependencies of imported Cook–Levin, Savitch and cryptographic proofs. Also
checks the completed main Theorems 3.1, 5.1, 7.1 and 7.2. Only unfinished
Theorem 6.1 is excluded explicitly.

Run after `lake build`: `lake env lean scripts/AuditFoundations.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unfinished : List Name := [
    ``ComplexityOfGenerators.theorem_6_1_polynomial_space_generation]
  let mut checked : Nat := 0
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if (`ComplexityOfGenerators).isPrefixOf moduleName then
      let data := env.header.moduleData[moduleIdx]
      for declaration in data.constNames do
        if unfinished.contains declaration then
          continue
        let dependencies ← liftCoreM (collectAxioms declaration)
        let unexpected := dependencies.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          throwError "Foundations audit: {declaration} depends on {unexpected}"
        checked := checked + 1
  logInfo m!"Foundations audit passed: {checked} local declarations; only propext, Classical.choice and Quot.sound are allowed."
