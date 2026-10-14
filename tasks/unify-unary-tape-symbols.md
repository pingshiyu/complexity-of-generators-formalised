# Plan: unify unary tape symbols

## Scope

Standardize the native unary tape interfaces on `Unit`, while retaining separate ordinary-input and index tapes. This is an implementation plan only. Coordinate with the contributor currently changing the codebase before starting implementation.

The ordinary unary input already uses `List Unit`. The dedicated index tape currently exposes `Option Bool`, although execution supplies only `some true` or `none`. Change the index interface to `Option Unit`, where `some ()` is a unary mark and `none` is blank.

Keep `InputData.index : ℕ` as the compact representation of the index tape's length. Preserve head movements, `generatorData`, random-bit and certificate semantics, resource accounting, and the statements of complexity-class results.

## Implementation steps

1. **Establish the implementation baseline.**

   Start from the other contributor's completed changes and recheck the affected definitions. The file references below reflect the checkout inspected when this plan was written. Preserve unrelated work.

2. **Change the native machine interface.**

   In [Machine.lean](../ComplexityOfGenerators/Machine.lean):

   - Change the index argument of `Machine.transition` from `Option Bool` to `Option Unit`.
   - In `observe` and `next`, supply `some ()` when `indexHead < data.index`, and `none` otherwise.
   - Update the index-tape documentation to describe a tape containing `n` unit symbols.
   - Retain the existing index length representation, head movement rules, and resource accounting.

3. **Simplify the unary tape adapter.**

   In [UnaryInput.lean](../ComplexityOfGenerators/Simulation/UnaryInput.lean), the ordinary unary input and index observations will both have type `Option Unit`.

   - Remove the symbol conversions in `unarySwapMachine` and pass the swapped symbols directly.
   - Retain the swaps of input data, head positions, and head movements.
   - Update the proofs of execution, output, determinism, and runtime preservation, including `unarySwap_run` and `unarySwap_decisionData`.

4. **Propagate the type through machine constructors and evaluators.**

   Inspect and update the index-symbol interfaces in the polynomial clock, transcript replay, sampler composition, transducer-bank compiler, virtual-index simulator, and computable evaluator. Relevant starting points include:

   - `ComplexityOfGenerators/Simulation/PolynomialClock.lean`
   - `ComplexityOfGenerators/Simulation/TranscriptReplay.lean`
   - `ComplexityOfGenerators/Simulation/SamplerComposition.lean`
   - `ComplexityOfGenerators/Simulation/TransducerBank/Basic.lean`
   - `ComplexityOfGenerators/Simulation/TransducerBank/Compiler.lean`
   - `ComplexityOfGenerators/Simulation/VirtualIndex.lean`
   - `ComplexityOfGenerators/Simulation/ComputableEvaluator.lean`

   Split grouped declarations such as:

   ```lean
   (auxiliary index : Option Bool)
   ```

   into:

   ```lean
   (auxiliary : Option Bool) (index : Option Unit)
   ```

   Update foundational and simulation proofs that explicitly reconstruct index reads, and any finite-evaluator definitions or encodings that expose the index-symbol type. Use compiler errors and targeted searches to locate dependent changes.

5. **Handle encoded simulation tapes explicitly.**

   Some simulators store a virtual unary tape inside a shared binary tape representation. For example, [CollisionBank.lean](../ComplexityOfGenerators/Simulation/CollisionBank.lean) currently passes `cell.bit` directly into the simulated machine's index argument.

   - Keep the internal storage format and decode a present mark to `some ()` at the simulated machine boundary.
   - Update the collision simulation proofs to establish that the stored tape produces the same index observations.
   - Document this as an internal encoding of the unified unary alphabet.
   - Retain Boolean flags used to record whether a virtual index cell is occupied, translating those flags into `Option Unit` when invoking a source machine.

   Avoid global replacements of `Bool` or `some true`. Random bits, certificates, ordinary binary inputs, and Boolean bookkeeping still need them. Binary encodings of virtual tapes are distinct from the native index-symbol interface being standardized.

6. **Validate the implementation.**

   Build affected modules incrementally, then run the repository checks:

   ```bash
   lake build
   lake env lean scripts/AuditFoundations.lean
   ```

   Check the empty index, reads inside the unary tape, and reads at its ending blank. Use the existing execution and simulation proofs to verify behavior and preserve exact runtime bounds. Do not weaken theorem statements or introduce proof placeholders to complete the migration.

7. **Update documentation and review the diff.**

   Explain that both native unary interfaces use `Unit`, while the two tapes retain distinct roles. Update relevant comments and README descriptions. Confirm that every native index-symbol interface uses `Option Unit` and that remaining binary representations have a documented purpose. Review for unrelated changes before handing off.

## Acceptance criteria

- `Machine.transition` takes `Option Unit` for its index symbol.
- Native index reads produce exactly `some ()` or `none`.
- The unary swap adapter exchanges symbols directly, without Boolean-to-unit conversions.
- Simulators decode their internal index representations explicitly and retain their correctness and resource-bound proofs.
- Randomness, certificates, ordinary input alphabets, tape roles, and complexity-class definitions retain their intended semantics.
- The complete build and foundations audit pass without new proof placeholders or axioms.
- Documentation distinguishes the native unary interface from internal simulation encodings.

## Main risk

Many proofs spell out index reads directly, so a small interface change has a broad proof migration. Special care is needed at simulator boundaries that currently pass binary tape cells directly to a source machine. The intended execution behavior remains unchanged.
