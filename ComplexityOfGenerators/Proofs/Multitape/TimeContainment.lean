import ComplexityOfGenerators.Proofs.Multitape.IndexedRecognition
import ComplexityOfGenerators.Proofs.Multitape.NativeGeneration
import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

/-!
# The general-time generator-to-decider containments

These are genuine finite multitape simulations. The deterministic constructor
computes the unary time value, its output is captured as real clock marks, and
the source is run through a finite fuel controller. Streaming output comparison
and actual unary-length preparation then give an ordinary-input decider.
Every setup, clock, random-read, and source transition is charged.

The lower bound n≤t(n) suffices here, and therefore covers the paper's strict
n<t(n) assumption in Proposition 4.1. Monotonicity is needed for the converse
up-to construction, rather than for either containment proved in this module.
-/

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Simulation.TransducerBank

variable {α : Type} [Fintype α]

/-- The TIME half of Proposition 4.1 for the general finite multitape class. -/
theorem gtime_subset_ntime (time : ℕ → ℕ) (constructible : TimeConstructible time)
    (dominates : ∀ n, n ≤ time n) : GTIME α time ⊆ NTIME α time := by
  obtain ⟨constructor⟩ := constructible
  rintro language ⟨G, generated, bounded⟩
  have clockBound : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (1 * (time n + 1)) := by
    intro n bits ticks word execution
    simpa only [Nat.one_mul] using
      (bounded n bits ticks word execution).trans (Nat.le_succ (time n))
  apply indexed_output_mem_ntime language (ClockCapture.machine constructor G.machine 1)
    (ClockCapture.runtime constructor 1) time
    (ClockCapture.resourceOrder constructor 1 dominates) dominates
    (ClockCapture.timeBound constructor G.machine 1 (by decide) dominates)
  intro word
  have correspondence :
      (∃ bits, (ClockCapture.machine constructor G.machine 1).Produces
        (generatorData word.length) bits word) ↔
      (∃ bits, G.machine.Produces (generatorData word.length) bits word) :=
    exists_congr fun bits => ClockCapture.produces_iff_of_accepting_bound constructor G.machine
      1 (by decide) dominates clockBound word.length bits word
  rw [correspondence, ← G.machine.generatedLanguage_iff_produces (generatorData word.length) word]
  change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ language
  rw [G.input_length_layer, generated]

/-- The forward TIME half of Proposition 4.2, with its actual O(t) convention. -/
theorem gtimeUpTo_subset_ntime (time : ℕ → ℕ) (constructible : TimeConstructible time)
    (dominates : ∀ n, n ≤ time n) : GTIMEUpTo α time ⊆ NTIME α time := by
  obtain ⟨constructor⟩ := constructible
  rintro language ⟨G, runtime, generated, order, bounded⟩
  obtain ⟨copies, positive, covers⟩ := ResourceOrder.global_affine order
  have clockPositive : 1 ≤ copies := by omega
  have clockBound : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (copies * (time n + 1)) := by
    intro n bits ticks word execution
    exact (bounded n bits ticks word execution).trans (covers n)
  apply indexed_output_mem_ntime language (ClockCapture.machine constructor G.machine copies)
    (ClockCapture.runtime constructor copies) time
    (ClockCapture.resourceOrder constructor copies dominates) dominates
    (ClockCapture.timeBound constructor G.machine copies clockPositive dominates)
  intro word
  have correspondence :
      (∃ bits, (ClockCapture.machine constructor G.machine copies).Produces
        (generatorData word.length) bits word) ↔
      (∃ bits, G.machine.Produces (generatorData word.length) bits word) :=
    exists_congr fun bits => ClockCapture.produces_iff_of_accepting_bound constructor G.machine
      copies clockPositive dominates clockBound word.length bits word
  rw [correspondence, ← G.machine.generatedLanguage_iff_produces (generatorData word.length) word]
  change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ language
  rw [G.input_length_layer, generated]

/-- Existing native exact generators are a checked special case of the paper's
finite multitape containment, through a transition-preserving one-bank embedding. -/
theorem native_gtime_subset_ntime (time : ℕ → ℕ) (constructible : TimeConstructible time)
    (dominates : ∀ n, n ≤ time n) : ComplexityOfGenerators.GTIME α time ⊆ NTIME α time :=
  (Native.gtime_subset_multitape_gtime time).trans (gtime_subset_ntime time constructible dominates)

end
end ComplexityOfGenerators.Multitape
