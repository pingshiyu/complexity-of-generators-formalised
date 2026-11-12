import ComplexityOfGenerators.Simulation.FixedBlockRetry.Execution
import ComplexityOfGenerators.Simulation.FixedBlockRetry.ValueProperties

/-! Native retry machine, exact support, polynomial short paths, and fair-stream
expected runtime. The only execution hypotheses concern a concrete finite phase. -/
namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O : Type} [Fintype S] [Fintype O]
    (unitSymbol : S) (bitSymbol : Bool → S) (decode : S → Option O)
    (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (f : ℕ → BitString → Option (List O))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)

noncomputable def coefficient : PolynomialBound := PolynomialBound.ofPolynomial
  (17 * Polynomial.X + 56 + 88 * cap.asPolynomial + 24 * width.asPolynomial +
    time.asPolynomial + 2 * (Command.counterBudget width).asPolynomial)

theorem coefficient_lower (n : ℕ) :
    17*n+16+24*cap n+2*collectBudget width n (cap n)+time n ≤ coefficient width cap time n := by
  have upper := PolynomialBound.eval_le_ofPolynomial
    (17 * Polynomial.X + 56 + 88 * cap.asPolynomial + 24 * width.asPolynomial +
      time.asPolynomial + 2 * (Command.counterBudget width).asPolynomial) n
  change _ ≤ coefficient width cap time n at upper
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, PolynomialBound.asPolynomial_eval] at upper
  unfold collectBudget
  omega

def program : Program (command unitSymbol bitSymbol decode width phase).Control S O 35 :=
  (command unitSymbol bitSymbol decode width phase).program 0

noncomputable def machine : Machine Unit Bool O := (program unitSymbol bitSymbol decode width phase).machine

include correct bounded frame in
theorem machine_produces_iff (n : ℕ) (bits : BitString) (word : List O)
    (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n) :
    (machine unitSymbol bitSymbol decode width phase).Produces (generatorData n) bits word ↔
      value width f n bits = some word := by
  obtain ⟨ticks, _, result, run, answer⟩ := command_runs unitSymbol bitSymbol decode width cap time phase f
    correct bounded frame n bits indexBudget widthBudget
  obtain ⟨nativeTicks, _, native⟩ := (program unitSymbol bitSymbol decode width phase).run_compiled (run.executes 0)
  constructor
  · rintro ⟨t, accepted⟩
    have same := (machine unitSymbol bitSymbol decode width phase).halted_outcome_unique
      (generatorData n) bits nativeTicks t _ _ native accepted
    rw [same] at answer
    exact answer.symm
  · intro output
    have accepted : result.outcome = .accepted word := by
      have equal := answer.trans output
      cases result with
      | exhausted => simp [Result.outcome, Outcome.acceptedWord] at equal
      | done last => simpa [Result.outcome, Outcome.acceptedWord] using equal
    exact ⟨nativeTicks, accepted ▸ native⟩

include correct bounded frame in
theorem machine_language (n : ℕ) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n) :
    (machine unitSymbol bitSymbol decode width phase).generatedLanguage (generatorData n) =
      {word | ∃ block : BitString, block.length = width n ∧ f n block = some word} := by
  ext word
  rw [Machine.mem_generatedLanguage_iff_produces]
  constructor
  · rintro ⟨bits, produced⟩
    exact value_sound width f n bits word
      ((machine_produces_iff unitSymbol bitSymbol decode width cap time phase f correct bounded frame n bits word indexBudget widthBudget).mp produced)
  · rintro ⟨block, length, output⟩
    exact ⟨block, (machine_produces_iff unitSymbol bitSymbol decode width cap time phase f correct bounded frame n block word indexBudget widthBudget).mpr
      ((value_single_block width f n block length).trans output)⟩

include correct bounded frame in
theorem machine_halting (n : ℕ) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n) :
    (machine unitSymbol bitSymbol decode width phase).HaltingTransducer (generatorData n) := by
  apply (program unitSymbol bitSymbol decode width phase).haltingTransducer n
  intro bits
  obtain ⟨ticks, _, result, run, _⟩ := command_runs unitSymbol bitSymbol decode width cap time phase f
    correct bounded frame n bits indexBudget widthBudget
  exact ⟨ticks, result.outcome, run.executes 0, by cases result <;> simp [Result.outcome]⟩

include correct bounded frame in
theorem machine_accepting_run (n : ℕ) (bits : BitString) (word : List O)
    (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (output : value width f n bits = some word) :
    ∃ nativeTicks ≤ 25*(coefficient width cap time n)^2*(bits.length/width n)^2,
      (machine unitSymbol bitSymbol decode width phase).run (generatorData n) bits nativeTicks = .halted (.accepted word) := by
  let count := bits.length / width n
  have countPositive : 0 < count := by
    by_contra notPositive
    have zero : count = 0 := Nat.eq_zero_of_not_pos notPositive
    change scan (width n) (f n) count bits = some word at output
    simp [zero, scan] at output
  obtain ⟨ticks, cost, result, run, answer⟩ := command_runs unitSymbol bitSymbol decode width cap time phase f
    correct bounded frame n bits indexBudget widthBudget
  have accepted : result.outcome = .accepted word := by
    have equal := answer.trans output
    cases result with
    | exhausted => simp [Result.outcome, Outcome.acceptedWord] at equal
    | done last => simpa [Result.outcome, Outcome.acceptedWord] using equal
  have primitive : ticks ≤ coefficient width cap time n * count := by
    have coefficientBound := coefficient_lower width cap time n
    have combined : 17*n+8+loopBudget width cap time n count+4*cap n ≤
        (17*n+16+24*cap n+2*collectBudget width n (cap n)+time n)*count := by
      unfold loopBudget attemptBudget
      nlinarith
    exact (cost.trans combined).trans (Nat.mul_le_mul_right _ coefficientBound)
  obtain ⟨nativeTicks, nativeCost, native⟩ := (program unitSymbol bitSymbol decode width phase).run_compiled
    (accepted ▸ run.executes 0)
  have bound : 1+(2*ticks+1)*(4*ticks+4) ≤ 25*(coefficient width cap time n)^2*count^2 := by
    have standard := Machine.retry_compiler_cost_le ticks (coefficient width cap time n) (count-1)
      ((coefficient width cap time).positive n) (by simpa [Nat.sub_add_cancel countPositive] using primitive)
    simpa only [Nat.sub_add_cancel countPositive] using standard
  exact ⟨nativeTicks, nativeCost.trans bound, native⟩

include correct bounded frame in
theorem first_success_acceptsBy (n : ℕ) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (stream : BitStream)
    (hit : fixedBlock (width n) stream (firstSuccessIndex (width n) (successSet width f n) stream) ∈ successSet width f n) :
    (machine unitSymbol bitSymbol decode width phase).streamAcceptsBy (generatorData n) stream
      (25 * (coefficient width cap time n)^2 *
        (firstSuccessIndex (width n) (successSet width f n) stream+1)^2) := by
  let N := firstSuccessIndex (width n) (successSet width f n) stream
  let bits := streamPrefix stream ((N+1)*width n)
  obtain ⟨word, output, _⟩ := value_first_success_prefix width f n stream hit
  obtain ⟨nativeTicks, bound, native⟩ := machine_accepting_run unitSymbol bitSymbol decode width cap time phase f
    correct bounded frame n bits word indexBudget widthBudget output
  have count : bits.length / width n = N+1 := by
    simp only [bits, streamPrefix_length, Nat.mul_div_cancel _ (width.positive n)]
  rw [count] at bound
  refine ⟨bits, word, stream_mem_prefix_cylinder stream _, ?_⟩
  have timeEqual : nativeTicks+(25*(coefficient width cap time n)^2*(N+1)^2-nativeTicks) =
      25*(coefficient width cap time n)^2*(N+1)^2 := by omega
  have padded :=
    (machine unitSymbol bitSymbol decode width phase).run_halted_add (generatorData n) bits nativeTicks
      (.accepted word) native (25*(coefficient width cap time n)^2*(N+1)^2-nativeTicks)
  rw [timeEqual] at padded
  exact padded

include correct bounded frame in
theorem machine_short_path (n : ℕ) (block : BitString) (word : List O)
    (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (length : block.length = width n) (output : f n block = some word) :
    (machine unitSymbol bitSymbol decode width phase).run (generatorData n) block
      (25*(coefficient width cap time n)^2) = .halted (.accepted word) := by
  obtain ⟨nativeTicks, bound, native⟩ := machine_accepting_run unitSymbol bitSymbol decode width cap time phase f
    correct bounded frame n block word indexBudget widthBudget ((value_single_block width f n block length).trans output)
  simp only [length, Nat.div_self (width.positive n), one_pow, mul_one] at bound
  have timeEqual : nativeTicks+(25*(coefficient width cap time n)^2-nativeTicks) = 25*(coefficient width cap time n)^2 := by omega
  have padded :=
    (machine unitSymbol bitSymbol decode width phase).run_halted_add (generatorData n) block nativeTicks
      (.accepted word) native (25*(coefficient width cap time n)^2-nativeTicks)
  rw [timeEqual] at padded
  exact padded

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
