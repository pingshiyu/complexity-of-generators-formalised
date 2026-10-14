import ComplexityOfGenerators.Foundations.ExecutionBounds
import ComplexityOfGenerators.Foundations.RandomTapeShift
import Mathlib.Data.Fintype.EquivFin
import ComplexityOfGenerators.Generators

/-! A uniform finite-control sampler of all binary words at the requested length.
The empty word is sampled at index zero. Each output bit costs two transitions. -/

namespace ComplexityOfGenerators.Simulation

set_option backward.isDefEq.respectTransparency false

def wordSampler : Machine Unit Bool Bool where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 3
  symbols := 0
  initial := 0
  transition := fun q _ _ index _ =>
    if q = 0 then
      if index.isSome then .readRandom 1 2 else .accept
    else .step 0 none .stay .stay .stay .right (some (q = 2))

def wordSamplerConfiguration (bits : BitString) (k : ℕ) : Configuration wordSampler :=
  {wordSampler.initialConfiguration with
    indexHead := k
    randomHead := k
    output := bits.take k}

theorem wordSampler_prefix (n : ℕ) (bits : BitString) (k : ℕ)
    (index : k ≤ n) (available : k ≤ bits.length) :
    wordSampler.run (generatorData n) bits (2 * k) =
      wordSampler.observe (generatorData n) bits (wordSamplerConfiguration bits k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have index' : k < n := by omega
      have available' : k < bits.length := by omega
      have previous :=  ih (by omega) (by omega)
      have lookup := List.getElem?_eq_getElem available'
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Machine.run, Machine.run, previous]
      simp only [Machine.observe, wordSampler, wordSamplerConfiguration, Machine.initialConfiguration,
        generatorData, index', ↓reduceIte, Option.isSome_some, Bool.true_eq, available']
      simp only [Machine.next, wordSampler, lookup]
      cases bit : bits[k] <;>
        simp [Machine.observe, Machine.next, wordSampler, wordSamplerConfiguration,
          Machine.initialConfiguration, generatorData, Move.onInput, Move.onInt,
          Nat.min_eq_left (show k + 1 ≤ n by omega), List.take_add_one, lookup, bit, index', available']

def wordSamplerOutcome (n : ℕ) (bits : BitString) : Outcome Bool :=
  if bits.length < n then .exhausted else .accepted (bits.take n)

theorem wordSampler_run (n : ℕ) (bits : BitString) :
    wordSampler.run (generatorData n) bits (2 * n) = .halted (wordSamplerOutcome n bits) := by
  by_cases short : bits.length < n
  · have stopped := wordSampler_prefix n bits bits.length (by omega) le_rfl
    have halt : wordSampler.run (generatorData n) bits (2 * bits.length) = .halted .exhausted := by
      simpa [Machine.observe, wordSampler, wordSamplerConfiguration, Machine.initialConfiguration,
        generatorData, short] using stopped
    have padded := wordSampler.run_halted_add (generatorData n) bits (2 * bits.length) .exhausted halt (2 * n - 2 * bits.length)
    simpa [wordSamplerOutcome, short, Nat.add_sub_of_le (by omega : 2 * bits.length ≤ 2 * n)] using padded
  · have stopped := wordSampler_prefix n bits n le_rfl (by omega)
    simpa [Machine.observe, wordSampler, wordSamplerConfiguration, Machine.initialConfiguration,
      generatorData, wordSamplerOutcome, short] using stopped

theorem wordSampler_timeBound (n : ℕ) : wordSampler.TimeBound (generatorData n) (2 * n) :=
  fun bits => ⟨wordSamplerOutcome n bits, wordSampler_run n bits⟩

theorem wordSampler_language (n : ℕ) :
    wordSampler.generatedLanguage (generatorData n) = {word | word.length = n} := by
  ext word
  constructor
  · rintro ⟨bits, _, t, produced⟩
    have same := wordSampler.halted_outcome_unique (generatorData n) bits t (2 * n) _ _ produced (wordSampler_run n bits)
    by_cases short : bits.length < n
    · simp [wordSamplerOutcome, short] at same
    · simp only [wordSamplerOutcome, short, ↓reduceIte, Outcome.accepted.injEq] at same
      simp [same, List.length_take, Nat.min_eq_left (by omega : n ≤ bits.length)]
  · intro length
    change word.length = n at length
    subst n
    refine ⟨word ++ [false], by simp, 2 * word.length, ?_⟩
    rw [wordSampler_run]
    simp [wordSamplerOutcome, List.take_append]

end ComplexityOfGenerators.Simulation
