import ComplexityOfGenerators.Simulation.ExpectedCollisionSearchExecution
import ComplexityOfGenerators.Foundations.Cryptography

/-!
# Uniform collision finding from bounded expected-length trials

The finite attacker searches all source indices up to twice the target length,
using the same random block throughout. The simulation is native, uniformly
polynomial, and permits ordinary attack failure on unsuccessful random blocks.
-/

namespace ComplexityOfGenerators.Simulation.ExpectedCollisionSearch

open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Unit Bool Bool)

def capPolynomial (p : PolynomialBound) : Polynomial ℕ :=
  100 * (Polynomial.X + p.asPolynomial + 1)

def trialPolynomial (p : PolynomialBound) : Polynomial ℕ :=
  Polynomial.C ((Source.body M Symbol.source (sourceDecode M) (Source.bank sourceSlots)).bound + 500) *
    (capPolynomial p + 1) + (Command.counterBudget p).asPolynomial

def stackTimePolynomial (p : PolynomialBound) : Polynomial ℕ :=
  let four : PolynomialBound := ⟨4, 1, by decide⟩
  let eight : PolynomialBound := ⟨8, 1, by decide⟩
  let prepare := 29 * Polynomial.X + 12 * (p.asPolynomial + 1) + (Command.counterBudget p).asPolynomial + 20
  let setup := 60 * capPolynomial p + (Command.counterBudget four).asPolynomial +
    (Command.counterBudget eight).asPolynomial + 100
  let search := (8 * (Polynomial.X + 1) + 5) * (trialPolynomial M p + 4)
  prepare + setup + search + 4 * capPolynomial p + 10

def stackTime (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (stackTimePolynomial M p)

def finderTime (p : PolynomialBound) : PolynomialBound := Program.compiledTime (stackTime M p)

@[simp] theorem capPolynomial_eval (p : PolynomialBound) (n : ℕ) :
    (capPolynomial p).eval n = cap p n := by
  simp [capPolynomial, cap, Polynomial.eval_add, Polynomial.eval_mul, PolynomialBound.asPolynomial_eval]

@[simp] theorem trialPolynomial_eval (p : PolynomialBound) (n : ℕ) :
    (trialPolynomial M p).eval n = trialBudget M p n := by
  simp [trialPolynomial, trialBudget, Polynomial.eval_add, Polynomial.eval_mul, PolynomialBound.asPolynomial_eval]

theorem stackTime_bound (p : PolynomialBound) (n : ℕ) :
    (29 * n + 12 * (p n + 1) + Command.counterBudget p n + 20) +
      (60 * cap p n + Command.counterBudget ⟨4, 1, by decide⟩ n +
        Command.counterBudget ⟨8, 1, by decide⟩ n + 100) +
      searchBudget M p n + 4 * cap p n + 10 ≤ stackTime M p n := by
  have bound := PolynomialBound.eval_le_ofPolynomial (stackTimePolynomial M p) n
  change _ ≤ PolynomialBound.ofPolynomial (stackTimePolynomial M p) n
  convert bound using 1
  simp only [stackTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat,
    PolynomialBound.asPolynomial_eval, capPolynomial_eval, trialPolynomial_eval,
    searchBudget, trials, target]
  ring

theorem machine_timeBound (p : PolynomialBound) (n : ℕ) :
    (machine M p).TimeBound (generatorData n) (finderTime M p n) := by
  intro bits
  obtain ⟨t, cost, result, run, _⟩ := command_runs M p n bits
  have stackBound : commandBudget M p n ≤ stackTime M p n := by
    simpa only [commandBudget, prepareBudget, setupBudget] using stackTime_bound M p n
  obtain ⟨ticks, nativeCost, native⟩ := ((command M p).program 32).run_compiled (run.executes 32)
  exact (machine M p).haltsWithin_mono _ bits
    (nativeCost.trans (WordStack.Program.compiledTime_bound (stackTime M p) n t
      (cost.trans stackBound))) ⟨result.outcome, native⟩

/-- An actual finite native attacker, uniformly polynomial on every random tape. -/
def finder (p : PolynomialBound) : CollisionFinder where
  machine := binaryOutputDecoder (machine M p)
  time := finderTime M p
  bounded n := binaryOutputDecoder_timeBound (machine M p) _ _ (machine_timeBound M p n)

theorem machine_produces (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (length : bits.length = p n + 1) :
    (machine M p).Produces (generatorData n) bits (foldAnswer M p n bits 0 (trials n) []) := by
  obtain ⟨_, _, result, run, output⟩ := command_runs M p n bits
  have enough : p n + 1 ≤ bits.length := length.ge
  have take : bits.take (p n + 1) = bits := by rw [← length, List.take_length]
  have resultEq : result.outcome = .accepted (foldAnswer M p n bits 0 (trials n) []) := by
    simpa only [enough, ite_true, take] using output
  obtain ⟨ticks, _, native⟩ := ((command M p).program 32).run_compiled (run.executes 32)
  exact ⟨ticks, resultEq ▸ native⟩

/-- Any qualifying bounded source run makes the same-seed native search output
some genuine collision at the requested security parameter. Other source indices
need only be sound; the search need not reproduce the same qualifying word. -/
theorem finder_success_of_run (h : HashFunction) (G : UniformGenerators Bool) (p : PolynomialBound)
    (sound : ∀ j word, word ∈ G.layer j → word = [] ∨ word ∈ h.binaryCollisionLanguage)
    (n i : ℕ) (bits word : BitString) (bits_length : bits.length = p n + 1)
    (index : i ≤ 2 * target n)
    (run : G.machine.run (generatorData i) bits (p n) = .halted (.accepted word))
    (length : word.length = target n) :
    ∃ x y, (finder G.machine p).machine.Produces (generatorData n) bits (encodePair x y) ∧
      h.IsCollision n x y := by
  have seedNonempty : bits ≠ [] := by
    intro empty
    simp only [empty, List.length_nil] at bits_length
    omega
  let answer := foldAnswer G.machine p n bits 0 (trials n) []
  obtain ⟨j, _, output, answerLength⟩ := foldAnswer_collision_witness G.machine p n i bits word index run length
  have member : answer ∈ G.layer j := ⟨bits, seedNonempty, p n, output⟩
  have collisionMember : answer ∈ h.binaryCollisionLanguage := by
    rcases sound j answer member with empty | member
    · have positive : 0 < target n := by simp [target]
      change answer.length = target n at answerLength
      rw [empty] at answerLength
      simp only [List.length_nil] at answerLength
      omega
    · exact member
  obtain ⟨x, y, collision, encoded⟩ := h.binary_collision_member_parameter n answer collisionMember answerLength
  have produced := machine_produces G.machine p n bits bits_length
  change (machine G.machine p).Produces (generatorData n) bits answer at produced
  rw [encoded] at produced
  exact ⟨x, y, binaryOutputDecoder_produces (machine G.machine p) _ bits (encodePair x y) produced, collision⟩

end
end ComplexityOfGenerators.Simulation.ExpectedCollisionSearch
