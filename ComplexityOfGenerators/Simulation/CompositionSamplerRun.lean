import ComplexityOfGenerators.Simulation.CompositionSamplerSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

theorem composition_sampler_runFrom (n : ℕ) (bits : BitString) (c : Configuration S)
    (t : ℕ) (result : Outcome Bool) (source : S.runFrom (generatorData n) bits c t = .halted result)
    (indexBound : c.indexHead ≤ n) :
    ∃ terminal ticks, ticks ≤ 4 * t + 1 ∧
      (samplerCompositionBank S R).Steps (generatorData n) bits (samplerBankConfiguration S R n c) ticks
        {samplerBankConfiguration S R n terminal with
          state := .sampleWork terminal.state (decide (terminal.indexHead < n))} ∧
      S.observe (generatorData n) bits terminal = .halted result ∧ terminal.indexHead ≤ n := by
  induction t generalizing c with
  | zero => exact ⟨c, 1, by omega, composition_sampler_fetch S R n bits c, source, indexBound⟩
  | succ t ih =>
      cases observation : S.observe (generatorData n) bits c with
      | halted out =>
          have same := S.runFrom_halted (generatorData n) bits c out observation (t + 1)
          rw [source] at same
          cases same
          exact ⟨c, 1, by omega, composition_sampler_fetch S R n bits c, observation, indexBound⟩
      | running d =>
          have same := S.observe_running_eq _ bits c d observation
          subst d
          obtain ⟨d, next⟩ := S.next_running_of_observe_running _ bits c observation
          rw [S.runFrom_shift _ bits c d observation next t] at source
          cases action : S.transition c.state none none (if c.indexHead < n then some () else none) (c.work c.workHead) with
          | accept => simp [Machine.observe, generatorData, action] at observation
          | reject => simp [Machine.observe, generatorData, action] at observation
          | step state write work input auxiliary index emit =>
              rw [S.next_step _ bits c state write work input auxiliary index emit
                (by simpa [generatorData] using action)] at next
              cases next
              obtain ⟨terminal, ticks, bound, path, halted, finalBound⟩ := ih _ source (index.onInput_le _ _ indexBound)
              have step := (composition_sampler_fetch S R n bits c).trans (samplerCompositionBank S R)
                (composition_sampler_step S R n bits c indexBound state write work input auxiliary index emit action)
              exact ⟨terminal, 4 + ticks, by omega, step.trans _ path, halted, finalBound⟩
          | readRandom no yes =>
              cases lookup : bits[c.randomHead]? with
              | none => simp [Machine.next, generatorData, action, lookup] at next
              | some bit =>
                  simp only [Machine.next, generatorData, List.getElem?_nil, action, lookup, RunState.running.injEq] at next
                  subst d
                  obtain ⟨terminal, ticks, bound, path, halted, finalBound⟩ := ih _ source indexBound
                  have step := (composition_sampler_fetch S R n bits c).trans (samplerCompositionBank S R)
                    (composition_sampler_random S R n bits c no yes bit action lookup)
                  exact ⟨terminal, 2 + ticks, by omega, step.trans _ path, halted, finalBound⟩

end
end ComplexityOfGenerators.Simulation
