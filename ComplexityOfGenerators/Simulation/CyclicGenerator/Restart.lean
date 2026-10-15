import ComplexityOfGenerators.Simulation.CyclicGenerator.Erasure
import ComplexityOfGenerators.Simulation.CyclicGenerator.Entry
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! Returning from a decision to the word counter, with clean work memory.
Only the visited interval is erased; neither the word nor random cursor changes. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem decision_work_interval (word : List α) (seen : Bool) (random : ℕ)
    (source : Configuration D) (geometry : D.TapeGeometry source) (lo hi : ℤ)
    (interval : source.visited = Finset.Icc lo hi) :
    (decisionConfig D word seen random source).tape 1 = intervalTape D lo hi source.work := by
  funext i
  by_cases inside : lo ≤ i ∧ i ≤ hi
  · simp [decisionConfig, intervalTape, interval, inside]
  · have blank := geometry.blank i (by simpa [interval] using inside)
    simp [decisionConfig, intervalTape, interval, inside, blank]; omega

/-- Erasure and both rewinds take linear time in the source's space and the
word length. This cost bound is local to cleanup and does not bound a decision's
running time. -/
theorem restart_steps (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (source : Configuration D) (geometry : D.TapeGeometry source)
    (inputBound : source.inputHead ≤ word.length) (space : source.visited.card ≤ s) :
    ∃ ticks, ticks ≤ 3 * s + word.length + 3 ∧
      (bank D).Steps (generatorData word.length) bits
        {decisionConfig D word seen random source with state := .eraseLeft seen} ticks
        {candidateConfig D word seen random 0 with state := .increment seen} := by
  obtain ⟨lo, hi, lower, upper, interval⟩ := geometry.interval
  have head : lo ≤ source.workHead ∧ source.workHead ≤ hi := by
    simpa [interval] using geometry.head
  have size : (source.visited.card : ℤ) = hi + 1 - lo := by
    rw [interval]
    exact Int.card_Icc_of_le lo hi (by omega)
  let c : Config D := {decisionConfig D word seen random source with state := .eraseLeft seen}
  let d : Config D := {c with state := .eraseRight seen, head := Function.update c.head 1 lo}
  let e : Config D := {d with
    state := .workOrigin seen
    head := Function.update d.head 1 hi
    tape := Function.update d.tape 1 (fun _ => {})}
  let f : Config D := {e with state := .counterOrigin seen, head := Function.update e.head 1 0}
  let g : Config D := {f with state := .increment seen, head := Function.update f.head 0 0}
  have left : (bank D).Steps (generatorData word.length) bits c
      ((source.workHead - lo).toNat + 2) d :=
    eraseLeft_steps D word.length bits seen lo hi source.work _ c rfl
      (by simp [c, decisionConfig]; omega) (by omega)
      (decision_work_interval D word seen random source geometry lo hi interval) rfl rfl le_rfl
  have right : (bank D).Steps (generatorData word.length) bits d (source.visited.card + 1) e :=
    eraseRight_steps D word.length bits seen hi source.work _ lo d rfl (by simp [d]) (by omega)
      (decision_work_interval D word seen random source geometry lo hi interval) rfl rfl le_rfl
  have workRewind : (bank D).Steps (generatorData word.length) bits e (hi.toNat + 1) f :=
    TransducerBank.TapeBank.rewind_steps (bank D) _ bits (.workOrigin seen) (.counterOrigin seen)
      1 rfl (by intros; rfl) hi.toNat e rfl (by simp [e]; omega)
      (by simp [e, d, c, decisionConfig, generatorData])
      (by simp [e, d, c, decisionConfig, generatorData]) le_rfl
  have wordRewind : (bank D).Steps (generatorData word.length) bits f (source.inputHead + 1) g :=
    TransducerBank.TapeBank.rewind_steps (bank D) _ bits (.counterOrigin seen) (.increment seen)
      0 rfl (by intros; rfl) source.inputHead f rfl (by simp [f, e, d, c, decisionConfig])
      (by simp [f, e, d, c, decisionConfig, generatorData])
      (by simp [f, e, d, c, decisionConfig, generatorData]) le_rfl
  have final : g = {candidateConfig D word seen random 0 with state := .increment seen} := by
    apply TransducerBank.BankConfiguration.ext
    all_goals simp [g, f, e, d, c, decisionConfig, candidateConfig, Function.update_idem]
    · funext j
      fin_cases j <;> simp
    · funext j i
      fin_cases j <;> simp
  refine ⟨(source.workHead - lo).toNat + 2 + (source.visited.card + 1) +
    (hi.toNat + 1) + (source.inputHead + 1), ?_, ?_⟩
  · omega
  · rw [← final]
    exact ((left.trans (bank D) right).trans (bank D) workRewind).trans (bank D) wordRewind

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
