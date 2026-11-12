import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Witness
import ComplexityOfGenerators.Proofs.OriginalBinaryFastRecords
import ComplexityOfGenerators.Proofs.OriginalSourceLuckyClock

/-! Global lucky native paths for union and concatenation. Source indices and
source runtimes are bounded using final word length, rather than layer-local
short paths. All calls run on the actual native direct-call backend. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
include expected

theorem records_word_path (operation : Operation) (index work : PolynomialBound) (word : List α)
    (n : ℕ) (requests : List Request) (records : List OriginalSourceFamilySampler.Record)
    (available : Available families operation n requests)
    (labels : records.map OriginalSourceFamilySampler.request=requests)
    (minimal : ∀ record∈records,OriginalSourceFamilySampler.MinimalRecord families record)
    (outputs : OriginalSourceFamilySampler.words families records=word)
    (small : n ≤ index word.length)
    (budget : OriginalSourceFamilySampler.totalTime families records+records.length≤work word.length) :
    ∃ bits : BitString,bits≠[] ∧
      (machine families p operation).run (generatorData n) bits
        (OriginalSourceClosure.luckyClock (coefficient families p operation) index work word.length)=.halted (.accepted word) := by
  obtain ⟨bits,ticks,nonempty,time,run⟩ := runs_records families p expected operation n requests records available labels minimal
  have within := time.trans (OriginalSourceClosure.luckyClock_bound (coefficient families p operation) index work n word.length _ small budget)
  rw [outputs] at run
  have padded := (machine families p operation).run_halted_add (generatorData n) bits ticks (.accepted word) run
    (OriginalSourceClosure.luckyClock (coefficient families p operation) index work word.length-ticks)
  exact ⟨bits,nonempty,by simpa only [Nat.add_sub_of_le within] using padded⟩

theorem union_word_fast (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ clock : PolynomialBound,∀ word∈(families false).language∪(families true).language,
      ∃ index : ℕ,∃ bits : BitString,bits≠[] ∧
        (machine families p .union).run (generatorData index) bits (clock word.length)=.halted (.accepted word) := by
  obtain ⟨q,paths⟩ := OriginalSourceClosure.union_fast_records families fast
  refine ⟨OriginalSourceClosure.luckyClock (coefficient families p .union) q (OriginalSourceClosure.binaryWork q),?_⟩
  intro word member
  obtain ⟨tag,index,records,small,active,labels,minimal,outputs,budget⟩ := paths word member
  have available : Available families .union index [(tag,index)] := ⟨tag,rfl,active⟩
  obtain ⟨bits,nonempty,run⟩ := records_word_path families p expected .union q (OriginalSourceClosure.binaryWork q)
    word index [(tag,index)] records available labels minimal outputs small budget
  exact ⟨index,bits,nonempty,run⟩

theorem concat_word_fast (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ clock : PolynomialBound,∀ word∈IndexedSupport.concat (families false).language (families true).language,
      ∃ index : ℕ,∃ bits : BitString,bits≠[] ∧
        (machine families p .concatenation).run (generatorData index) bits (clock word.length)=.halted (.accepted word) := by
  obtain ⟨q,paths⟩ := OriginalSourceClosure.concat_fast_records families fast
  refine ⟨OriginalSourceClosure.luckyClock (coefficient families p .concatenation) (q.add q) (OriginalSourceClosure.binaryWork q),?_⟩
  intro word member
  obtain ⟨left,right,records,small,activeLeft,activeRight,labels,minimal,outputs,budget⟩ := paths word member
  have available : Available families .concatenation (left+right) [(false,left),(true,right)] := by
    refine ⟨left,by omega,?_,activeLeft,?_⟩
    · simp
    · simpa using activeRight
  obtain ⟨bits,nonempty,run⟩ := records_word_path families p expected .concatenation (q.add q) (OriginalSourceClosure.binaryWork q)
    word (left+right) [(false,left),(true,right)] records available labels minimal outputs small budget
  exact ⟨left+right,bits,nonempty,run⟩

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
