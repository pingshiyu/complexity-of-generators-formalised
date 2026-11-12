import ComplexityOfGenerators.Proofs.Multitape.GeneratorCompatibility
import ComplexityOfGenerators.Proofs.UpToElementaryGenerators

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

private theorem of_native_zero_upTo (language : Language α)
    (G : ComplexityOfGenerators.UpToGeneratorFamily α language)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) 0) (time : ℕ → ℕ) :
    language ∈ GTIMEUpTo α time := by
  refine ⟨ofNativeUpTo language G, (fun _ => 0), ?_, ?_, ?_⟩
  · rw [show (ofNativeUpTo language G).toUniformGenerators =
      ofNativeUniform G.toUniformGenerators from rfl, ofNativeUniform_language,
      nativeUpTo_language language G]
  · exact ⟨1, 0, by decide, fun _ _ => Nat.zero_le _⟩
  · intro n
    exact Simulation.TransducerBank.Native.acceptingTimeBound G.machine (generatorData n)
      (G.isGenerator n).1.1 0 (bounded n)

/-- A genuine random-bit drain, with no accepting executions to bound. -/
theorem empty_mem_gtimeUpTo (time : ℕ → ℕ) : (∅ : Language α) ∈ GTIMEUpTo α time := by
  apply of_native_zero_upTo ∅ (ComplexityOfGenerators.emptyUpToFamily α) ?_ time
  intro n bits word ⟨ticks, accepted⟩
  change (ComplexityOfGenerators.emptyGenerator α).run (generatorData n) bits ticks = _ at accepted
  rw [ComplexityOfGenerators.emptyGenerator_run] at accepted
  split_ifs at accepted <;> cases accepted

/-- Empty output is accepted in the initial finite control state at every index. -/
theorem empty_word_mem_gtimeUpTo (time : ℕ → ℕ) : ({[]} : Language α) ∈ GTIMEUpTo α time := by
  apply of_native_zero_upTo {[]} (ComplexityOfGenerators.emptyWordUpToFamily α) ?_ time
  intro n
  apply Machine.TimeBound.acceptingTimeBound
  intro bits
  exact ⟨.accepted [], rfl⟩

end
end ComplexityOfGenerators.Multitape
