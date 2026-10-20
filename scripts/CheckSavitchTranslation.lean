import ComplexityOfGenerators.MainTheorems
import ComplexityOfGenerators.Proofs.ElementaryGenerators

/-! Kernel-checked regressions for the replacement Savitch route. The binary
return compiler has executable checks in `CheckLibraryTM.lean`.
Run: `lake env lean scripts/CheckSavitchTranslation.lean` after `lake build`. -/

namespace ComplexityOfGenerators.SavitchTranslationChecks
open Simulation NativeNTM Complexity

/-- Two random outcomes, with distinct accepting and rejecting successors. -/
abbrev branch (α : Type) [Fintype α] : Machine α Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 3
  symbols := 0
  initial := 0
  transition := fun q _ _ _ _ =>
    if q = 0 then .readRandom 1 2 else if q = 1 then .accept else .reject

-- Random choice changes only the simulated state, retaining the work sign.
example : (core (branch Bool) false (.simulate 0 true) .blank (fun _ => .blank)).state =
    .simulate 1 true := rfl
example : (core (branch Bool) true (.simulate 0 true) .blank (fun _ => .blank)).state =
    .simulate 2 true := rfl
example (choice : Bool) :
    (core (branch Bool) choice (.simulate 1 false) .blank (fun _ => .blank)).output = .one := rfl
example (choice : Bool) :
    (core (branch Bool) choice (.simulate 2 false) .blank (fun _ => .blank)).output = .zero := rfl

-- An empty alphabet accepts only the empty *encoding* into the simulator.
example : (core (branch (Fin 0)) false (.load 0) .blank (fun _ => .blank)).state =
    .rewind := rfl
example : (core (branch (Fin 0)) false (.load 0) .zero (fun _ => .blank)).output = .zero := rfl
example : (core (branch (Fin 0)) false (.load 0) .one (fun _ => .blank)).output = .zero := rfl

-- Reject an unterminated unary code and an out-of-range letter ordinal.
example : (core (branch (Fin 3)) false (.load 1) .blank (fun _ => .blank)).output = .zero := rfl
example : (core (branch (Fin 3)) false (.load 3) .one (fun _ => .blank)).output = .zero := rfl
example : (core (branch (Fin 3)) false (.load 3) .zero (fun _ => .blank)).output = .zero := rfl

-- Empty input, the right sentinel, and crossing the shared work-tape origin.
#guard boundedDir true true .left == .stay
#guard boundedDir true true .right == .stay
#guard boundedDir false true .right == .stay
#guard coordinate (foldedSign false true .left) (foldedHead false 0 .left) == -1
#guard coordinate (foldedSign true false .right) (foldedHead true 1 .right) == 0
#guard coordinate (foldedSign true true .right) (foldedHead true 0 .right) == 1

/-- Write at the shared origin, then move onto the negative half. -/
abbrev writer : Machine Bool Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 1
  initial := 0
  transition := fun _ _ _ _ _ => .step 0 (some 0) .left .stay .stay .stay none

def originRead : Tracks writer → Γ
  | .work none => .one
  | _ => .blank

-- Both half-tapes receive an origin write; an off-origin write affects one.
example : (core writer false (.simulate 0 false) .blank originRead).write
    (.work (some (true, 0))) = .one := rfl
example : (core writer false (.simulate 0 false) .blank originRead).write
    (.work (some (false, 0))) = .one := rfl
example : (core writer false (.simulate 0 false) .blank (fun _ => .blank)).write
    (.work (some (true, 0))) = .blank := rfl
example : (core writer false (.simulate 0 false) .blank (fun _ => .blank)).write
    (.work (some (false, 0))) = .one := rfl

-- Preserve the feasibility counterexample: finite-seed halting does not give
-- uniform termination of the translated nondeterministic machine.
theorem finite_tapes_do_not_give_uniform_time :
    (emptyGenerator Bool).IsGenerator (generatorData 0) ∧
      ¬ ∃ t, (emptyGenerator Bool).TimeBound (generatorData 0) t := by
  refine ⟨emptyGenerator_isGenerator, ?_⟩
  rintro ⟨t, bound⟩
  obtain ⟨result, halted⟩ := bound (List.replicate (t + 1) false)
  simp [emptyGenerator_run] at halted

theorem erased_empty_generator_loops (choice : Bool) :
    ((emptyGenerator Bool).decisionView (emptyGenerator Bool).initialConfiguration).advance
      (emptyGenerator Bool) (generatorData 0) choice =
        some ((emptyGenerator Bool).decisionView (emptyGenerator Bool).initialConfiguration) := by
  cases choice <;> rfl

-- The production bridge must continue to require only space, allowing loops.
example {α : Type} [Fintype α] (M : Machine α Bool Unit) (p : PolynomialBound)
    (space : ∀ word, M.SpaceBound (sourceData word) (p word.length)) :
    language M ∈ Standard.PSPACE := language_mem_PSPACE M p space

-- Both degenerate and nonbinary alphabets retain the unconditional theorem.
example : PSPACEG (Fin 0) = PSPACE (Fin 0) := theorem_6_1_polynomial_space_generation (Fin 0)
example : PSPACEG (Fin 3) = PSPACE (Fin 3) := theorem_6_1_polynomial_space_generation (Fin 3)

end ComplexityOfGenerators.SavitchTranslationChecks
