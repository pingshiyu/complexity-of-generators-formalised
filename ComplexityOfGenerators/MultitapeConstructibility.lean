import ComplexityOfGenerators.MultitapeComplexityClasses

/-!
# Charged finite-machine witnesses for time constructibility

A witness really computes the unary value on a finite deterministic tape bank.
The host function specifies the required output and bound; it is never an
instruction available to the program. Converting the emitted clock to marks
on a work tape and resetting the ordinary input are separate simulations and
must be charged when proving a resource characterisation.
-/

namespace ComplexityOfGenerators.Multitape

/-- A finite deterministic algorithm computing unary t(n) in O(t(n)) time.
The harmless +1 covers t(n)=0; under the paper's t(n)≥n premise this is the
usual eventual O(t(n)) bound. No clean-head or preloaded-clock interface is
assumed as an extra constructibility hypothesis. -/
structure TimeConstructor (time : ℕ → ℕ) where
  machine : MultitapeMachine Unit Bool Unit
  deterministic : machine.Deterministic
  constant : ℕ
  constant_pos : 0 < constant
  computes : ∀ n, ∃ ticks,
    ticks ≤ constant * (time n + 1) ∧
    machine.Executes (decisionData (List.replicate n ())) [] machine.initialConfiguration
      ticks (.accepted (List.replicate (time n) ()))

def TimeConstructible (time : ℕ → ℕ) : Prop := Nonempty (TimeConstructor time)

namespace TimeConstructor

variable {time : ℕ → ℕ} (constructor : TimeConstructor time)

/-- Determinism turns the one recorded computation into an all-choice-tape
bound, by replaying actual transitions rather than invoking an evaluator oracle. -/
theorem timeBound (n : ℕ) :
    constructor.machine.TimeBound (decisionData (List.replicate n ()))
      (constructor.constant * (time n + 1)) := by
  intro bits
  obtain ⟨ticks, cost, execution⟩ := constructor.computes n
  exact ⟨ticks, .accepted (List.replicate (time n) ()), cost,
    Simulation.TransducerBank.TapeBank.Executes.change_bits
      constructor.machine.program constructor.deterministic execution bits⟩

/-- Under the paper's linear lower bound, the charged constructor really has
O(t(n)) cost in the shared asymptotic convention. -/
theorem resourceOrder (dominates : ∀ n, n ≤ time n) :
    ResourceOrder (fun n => constructor.constant * (time n + 1)) time := by
  refine ⟨2 * constructor.constant, 1,
    Nat.mul_pos (by decide) constructor.constant_pos, ?_⟩
  intro n positive
  have large : 1 ≤ time n := positive.trans (dominates n)
  calc
    constructor.constant * (time n + 1) ≤ constructor.constant * (2 * time n) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = (2 * constructor.constant) * time n := by ac_rfl

end TimeConstructor
end ComplexityOfGenerators.Multitape
