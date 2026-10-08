import ComplexityOfGenerators.Proofs.BinaryInputComposition
import ComplexityOfGenerators.Proofs.BinaryInputExhaustion
import ComplexityOfGenerators.Simulation.FiniteRecursiveResults

/-!
# Total recursive programs as native generators

The machine samples a candidate and a clock, executes Mathlib's verified
compiler with finite control, and prints the returned word. The totality
hypothesis below is about a concrete recursive program, not an assumed native
simulation. Every finite random tape either supplies both samples or exhausts.
-/

namespace ComplexityOfGenerators

open Simulation Turing ToPartrec Encodable MeasureTheory

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] [Encodable α]

/-- A concrete finite transition table, with random-input and output routines
attached to the established library compiler. -/
def recursiveGenerator (code : Code) : Machine Unit Bool α := by
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  let impl := recursivePostImplementation code
  letI := impl.finiteControl
  letI := impl.initialControl
  exact postOutputMachine (binaryInputSimulator impl.machine (Fintype.equivFin impl.Control)
    (Fintype.equivFin RecursiveAlphabet))

theorem recursiveGenerator_produces (code : Code) (data : InputData Unit Bool)
    (candidate clock : ℕ) (extra : BitString) (word : List α)
    (computed : code.eval [clock, candidate] = Part.some (word.reverse.map encode)) :
    (recursiveGenerator (α := α) code).Produces data
      (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) word := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  let impl := recursivePostImplementation code
  let := impl.finiteControl
  let := impl.initialControl
  obtain ⟨last, evaluated, decoded⟩ := recursivePostImplementation_result code [clock, candidate] word computed
  obtain ⟨path, halt⟩ := StateTransition.mem_eval.mp evaluated
  have halted : impl.machine last.q last.Tape.head = none := by
    simpa only [TM0.step, Option.map_eq_none_iff] using halt
  exact binary_post_output_produces impl.machine (Fintype.equivFin impl.Control)
    (Fintype.equivFin RecursiveAlphabet) data candidate clock extra word last path halted decoded

/-- The complete machine has a finite outcome for every tape: either exhaustion,
or the specified value of the total recursive program on its two samples. -/
theorem recursiveGenerator_outcomes (code : Code) (f : ℕ → ℕ → List α)
    (computes : ∀ clock candidate, code.eval [clock, candidate] = Part.some ((f clock candidate).reverse.map encode))
    (data : InputData Unit Bool) (bits : BitString) :
    (∃ t, (recursiveGenerator (α := α) code).run data bits t = .halted .exhausted) ∨
    (∃ clock candidate, (recursiveGenerator (α := α) code).Produces data bits (f clock candidate)) := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  let impl := recursivePostImplementation code
  let := impl.finiteControl
  let := impl.initialControl
  let control := Fintype.equivFin impl.Control
  let alphabet := Fintype.equivFin RecursiveAlphabet
  let sim := binaryInputSimulator impl.machine control alphabet
  rcases binary_input_seed_cases impl.machine control alphabet data bits with complete | exhausted
  · obtain ⟨candidate, clock, extra, rfl⟩ := complete
    exact Or.inr ⟨clock, candidate, recursiveGenerator_produces code data candidate clock extra _ (computes clock candidate)⟩
  · obtain ⟨t, execution⟩ := exhausted
    refine Or.inl ⟨t, ?_⟩
    have lifted := sequence_left_exhausted sim.machine (postOutputRoutine (α := α) sim) data bits
      sim.machine.initialConfiguration [] t (by rw [Machine.runFrom_initial]; exact execution)
    have initial : sequenceLeftConfiguration sim.machine (postOutputRoutine (α := α) sim)
        sim.machine.initialConfiguration [] = (recursiveGenerator (α := α) code).initialConfiguration := rfl
    rw [initial] at lifted
    change (recursiveGenerator (α := α) code).runFrom data bits
      (recursiveGenerator (α := α) code).initialConfiguration t = .halted .exhausted at lifted
    simpa only [Machine.runFrom_initial] using lifted

/-- Almost-sure acceptance follows from the proved measure-one binary sampling
event. Short finite tapes are still covered by the separate halting proof. -/
theorem recursiveGenerator_isGenerator (code : Code) (f : ℕ → ℕ → List α)
    (computes : ∀ clock candidate, code.eval [clock, candidate] = Part.some ((f clock candidate).reverse.map encode))
    (data : InputData Unit Bool) : (recursiveGenerator (α := α) code).IsGenerator data := by
  let M := recursiveGenerator (α := α) code
  have outcomes := recursiveGenerator_outcomes code f computes data
  refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
  · intro bits
    rcases outcomes bits with ⟨t, exhausted⟩ | ⟨clock, candidate, t, produced⟩
    · exact ⟨t, .exhausted, exhausted⟩
    · exact ⟨t, .accepted (f clock candidate), produced⟩
  · intro bits t rejected
    rcases outcomes bits with ⟨s, exhausted⟩ | ⟨clock, candidate, s, produced⟩
    · have impossible := M.halted_outcome_unique data bits t s .rejected .exhausted rejected exhausted
      cases impossible
    · have impossible := M.halted_outcome_unique data bits t s .rejected (.accepted (f clock candidate)) rejected produced
      cases impossible
  · have subset : binarySamplingEvent ⊆ M.acceptedStreams data := by
      rintro stream ⟨candidate, clock, cylinderMember⟩
      refine ⟨binaryNumberSeed candidate ++ binaryNumberSeed clock, cylinderMember, f clock candidate, ?_⟩
      simpa using recursiveGenerator_produces code data candidate clock [] _ (computes clock candidate)
    exact le_antisymm (by simpa using (measure_mono (μ := fairCoinMeasure) (Set.subset_univ (M.acceptedStreams data)))) (by
      rw [← fairCoinMeasure_binarySamplingEvent]
      exact measure_mono subset)

/-- The generated language is exactly the range of the total program. The
nonempty-seed condition in the paper is respected even for the empty word. -/
theorem recursiveGenerator_language (code : Code) (f : ℕ → ℕ → List α)
    (computes : ∀ clock candidate, code.eval [clock, candidate] = Part.some ((f clock candidate).reverse.map encode))
    (data : InputData Unit Bool) :
    (recursiveGenerator (α := α) code).generatedLanguage data = {word | ∃ clock candidate, f clock candidate = word} := by
  let M := recursiveGenerator (α := α) code
  ext word
  constructor
  · rintro ⟨bits, nonempty, t, produced⟩
    rcases recursiveGenerator_outcomes code f computes data bits with ⟨s, exhausted⟩ | ⟨clock, candidate, s, computed⟩
    · have impossible := M.halted_outcome_unique data bits t s (.accepted word) .exhausted produced exhausted
      cases impossible
    · have equal := M.halted_outcome_unique data bits s t (.accepted (f clock candidate)) (.accepted word) computed produced
      exact ⟨clock, candidate, Outcome.accepted.inj equal⟩
  · rintro ⟨clock, candidate, rfl⟩
    refine ⟨binaryNumberSeed candidate ++ binaryNumberSeed clock, ?_, ?_⟩
    · have nonempty : binaryNumberSeed candidate ≠ [] := by
        unfold binaryNumberSeed
        cases (candidate : Num) <;> simp [numSeed]
      intro empty
      exact nonempty (List.append_eq_nil_iff.mp empty).1
    · simpa using recursiveGenerator_produces code data candidate clock [] _ (computes clock candidate)

end

end ComplexityOfGenerators
