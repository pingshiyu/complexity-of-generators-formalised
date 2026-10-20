import ComplexityOfGenerators.Simulation.ExactRecursive.BasicBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.TrialBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.SearchStep

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem coin_offer_bound (s : Store B V) (cap words : ℕ)
    (sizes : StoreBound s cap) (positive : 1 ≤ cap)
    (candidate : (s 25).length ≤ words) (output : (s 10).length ≤ words) :
    StoreBound ((coin B V (offer B V false) (offer B V true)).eval s) cap ∧
      ((coin B V (offer B V false) (offer B V true)).eval s 25).length ≤ words ∧
      (coin B V (offer B V false) (offer B V true)).cost s ≤ 20 * cap + 23 := by
  let popped := Function.update s 17 (s 17).tail
  have size : StoreBound popped cap := sizes.update 17 _ (by have := sizes 17; simp only [List.length_tail]; omega)
  have no := offer_bound B V false popped cap words size positive (by simpa [popped] using candidate)
    (by simpa [popped] using output)
  have yes := offer_bound B V true popped cap words size positive (by simpa [popped] using candidate)
    (by simpa [popped] using output)
  simp only [coin, WordStack.Routine.branch, WordStack.Routine.seq, WordStack.Routine.ofLocal,
    Local.eval_pop, Local.pop, Local.ticks, Local.eval, Action.apply]
  dsimp only [popped] at no yes
  split
  · exact ⟨yes.1, yes.2.1, by have := yes.2.2; omega⟩
  · exact ⟨no.1, no.2.1, by have := no.2.2; omega⟩

noncomputable def searchStepBudget (seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  ((Source.body V (Symbol.inverse : Source.Symbol V → Cell B V) (inverseDecode B V)
    (Source.bank sourceSlots)).bound + 250) * (cap + 1) +
      Command.counterBudget seed n + Command.counterBudget time n

theorem searchStep_bound (first : α) (seed time : PolynomialBound) (n : ℕ)
    (y label : List α) (bits : BitString) (selection : BoundedTrialChoice.Selection (List α))
    (s : Store B V) (stored : SearchStored B V n y label bits selection s)
    (cap words : ℕ) (sizes : StoreBound s cap) (base : n + 1 ≤ cap)
    (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap) (outputBound : time n + 1 ≤ words)
    (candidate : (s 25).length ≤ words) (nextSize : (Shortlex.next first label).length ≤ cap)
    (space : 1 + y.length + label.length + n + seed n + 3 * (time n + 1) ≤ cap) :
    StoreBound ((searchStep B V first seed time).eval s) cap ∧
      ((searchStep B V first seed time).eval s 25).length ≤ words ∧
      (searchStep B V first seed time).cost s ≤ searchStepBudget B V seed time n cap := by
  obtain ⟨trialSize, trialOutput, trialCost⟩ := sourceTrial_bound B V V Symbol.inverse (inverseDecode B V)
    (fun _ => rfl) (inverseInput B V) (inverseAuxiliary B V) (inverseBit B V) (fun _ => rfl)
    seed time s {input := y, auxiliary := label, index := n} bits
    (by simp [stored.input, letters, List.map_map, Function.comp_def, inverseInput])
    (by simp [stored.label, letters, List.map_map, Function.comp_def, inverseAuxiliary])
    stored.index stored.random stored.empty cap sizes base seedBound timeBound space
  let trial := (inverseTrial B V seed time).eval s
  have trialCandidate : (trial 25).length ≤ words := by
    rw [show trial 25 = s 25 from sourceTrial_fixes B V V _ _ _ _ _ seed time 25 (by decide) s]
    exact candidate
  obtain ⟨chosenSize, chosenCandidate, chosenCost⟩ := coin_offer_bound B V trial cap words trialSize
    (by omega) trialCandidate (trialOutput.trans outputBound)
  let chosen := (coin B V (offer B V false) (offer B V true)).eval trial
  have chosenLabel : chosen 12 = letters B V label := by
    have coinFrame := coin_fixes B V (offer B V false) (offer B V true) 12 (by decide)
      (offer_fixes B V false 12 (by decide) (by decide) (by decide) (by decide))
      (offer_fixes B V true 12 (by decide) (by decide) (by decide) (by decide)) trial
    have trialFrame := sourceTrial_outside B V V Symbol.inverse (inverseDecode B V)
      (inverseInput B V) (inverseAuxiliary B V) (inverseBit B V) seed time s 12 (by decide) (by decide)
    exact coinFrame.trans (by simpa [trial, inverseTrial, trialPrepared] using trialFrame.trans stored.label)
  obtain ⟨incrementSize, incrementCost⟩ := increment_bound B V first chosen label cap chosenSize chosenLabel nextSize
  refine ⟨incrementSize, ?_, ?_⟩
  · change ((increment B V first).eval chosen 25).length ≤ words
    rw [increment_fixes B V first 25 (by decide) (by decide)]
    exact chosenCandidate
  · change (inverseTrial B V seed time).cost s + 1 +
      ((coin B V (offer B V false) (offer B V true)).cost trial + 1 +
        (increment B V first).cost chosen) ≤ _
    change (inverseTrial B V seed time).cost s ≤ _ at trialCost
    dsimp only [searchStepBudget]
    nlinarith

end ComplexityOfGenerators.Simulation.ExactRecursive
