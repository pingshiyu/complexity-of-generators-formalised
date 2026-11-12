import ComplexityOfGenerators.Simulation.SymbolRelabel
import ComplexityOfGenerators.Proofs.ResourceGeneration

namespace ComplexityOfGenerators.Simulation.SymbolRelabel
set_option backward.isDefEq.respectTransparency false
variable {I A O J B P : Type} [Fintype J] [Fintype B] [Fintype P]
variable (M : Machine I A O) (input : J→I) (auxiliary : B→A) (output : O→P)

theorem deterministic (source : M.Deterministic) : (machine M input auxiliary output).Deterministic := by
  intro q i a n w
  have bound := source q (i.map input) (a.map auxiliary) n w
  dsimp only [machine]
  cases h : M.transition q (i.map input) (a.map auxiliary) n w <;>
    simp_all [instruction]

theorem acceptingTimeBound (d : InputData J B) (ticks : ℕ)
    (bound : M.AcceptingTimeBound (data input auxiliary d) ticks) :
    (machine M input auxiliary output).AcceptingTimeBound d ticks := by
  intro bits word accepted
  obtain ⟨source,accepted,equal⟩ := (produces M input auxiliary output d bits word).mp accepted
  rw [run,bound bits source accepted]
  simpa only [state,outcome,equal]

theorem trialBound (d : InputData J B) (seed ticks : ℕ)
    (bound : M.GeneratorTimeBound (data input auxiliary d) seed ticks) :
    (machine M input auxiliary output).GeneratorTimeBound d seed ticks := by
  constructor
  · intro bits short
    obtain ⟨result,terminal⟩ := bound.1 bits short
    exact ⟨outcome output result,by rw [run,terminal];rfl⟩
  · intro bits length
    rw [accepts,language]
    simpa only [Set.image_nonempty] using bound.2 bits length

end ComplexityOfGenerators.Simulation.SymbolRelabel
