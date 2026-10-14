import ComplexityOfGenerators.Simulation.CompositionRecovererSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

theorem composition_recoverer_runFrom (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R)
    (t : ℕ) (result : Outcome α) (source : R.runFrom (generatorData n certificate) bits c t = .halted result)
    (indexBound : c.indexHead ≤ n) (auxiliaryBound : c.auxiliaryHead ≤ certificate.length) :
    ∃ terminal ticks, ticks ≤ 5 * t + 2 ∧
      (samplerCompositionBank S R).Steps (generatorData n) bits (recovererBankConfiguration S R n certificate samplerWork samplerHead c) ticks
        {recovererBankConfiguration S R n certificate samplerWork samplerHead terminal with
          state := .recoverWork terminal.state (decide (terminal.indexHead < n)) certificate[terminal.auxiliaryHead]?} ∧
      R.observe (generatorData n certificate) bits terminal = .halted result ∧ terminal.indexHead ≤ n ∧ terminal.auxiliaryHead ≤ certificate.length := by
  induction t generalizing c with
  | zero => exact ⟨c, 2, by omega, composition_recoverer_fetch S R n certificate bits samplerWork samplerHead c, source, indexBound, auxiliaryBound⟩
  | succ t ih =>
      cases observation : R.observe (generatorData n certificate) bits c with
      | halted out =>
          have same := R.runFrom_halted (generatorData n certificate) bits c out observation (t + 1)
          rw [source] at same
          cases same
          exact ⟨c, 2, by omega, composition_recoverer_fetch S R n certificate bits samplerWork samplerHead c, observation, indexBound, auxiliaryBound⟩
      | running d =>
          have same := R.observe_running_eq _ bits c d observation
          subst d
          obtain ⟨d, next⟩ := R.next_running_of_observe_running _ bits c observation
          rw [R.runFrom_shift _ bits c d observation next t] at source
          cases action : R.transition c.state none certificate[c.auxiliaryHead]? (if c.indexHead < n then some () else none) (c.work c.workHead) with
          | accept => simp [Machine.observe, generatorData, action] at observation
          | reject => simp [Machine.observe, generatorData, action] at observation
          | step state write work input auxiliary index emit =>
              rw [R.next_step _ bits c state write work input auxiliary index emit
                (by simpa [generatorData] using action)] at next
              cases next
              obtain ⟨terminal, ticks, bound, path, halted, finalBound, finalAuxiliary⟩ := ih _ source (index.onInput_le _ _ indexBound) (auxiliary.onInput_le _ _ auxiliaryBound)
              have step := (composition_recoverer_fetch S R n certificate bits samplerWork samplerHead c).trans (samplerCompositionBank S R)
                (composition_recoverer_step S R n certificate bits samplerWork samplerHead c indexBound auxiliaryBound state write work input auxiliary index emit action)
              exact ⟨terminal, 5 + ticks, by omega, step.trans _ path, halted, finalBound, finalAuxiliary⟩
          | readRandom no yes =>
              cases lookup : bits[c.randomHead]? with
              | none => simp [Machine.next, generatorData, action, lookup] at next
              | some bit =>
                  simp only [Machine.next, generatorData, List.getElem?_nil, action, lookup, RunState.running.injEq] at next
                  subst d
                  obtain ⟨terminal, ticks, bound, path, halted, finalBound, finalAuxiliary⟩ := ih _ source indexBound auxiliaryBound
                  have step := (composition_recoverer_fetch S R n certificate bits samplerWork samplerHead c).trans (samplerCompositionBank S R)
                    (composition_recoverer_random S R n certificate bits samplerWork samplerHead c no yes bit action lookup)
                  exact ⟨terminal, 3 + ticks, by omega, step.trans _ path, halted, finalBound, finalAuxiliary⟩

end
end ComplexityOfGenerators.Simulation
