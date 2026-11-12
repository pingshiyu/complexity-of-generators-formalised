import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

theorem source_advance (data : InputData I A) (length index : ℕ) (current : BankConfiguration O Q S k)
    (next write work input auxiliary sourceIndex emit) (live : Bool) :
    (bank source).advance data (configuration source length index current (.execute current.state live))
        (afterStep next live sourceIndex) (encodeSource write) work input auxiliary .stay emit =
      configuration source length index (source.advance (sourceData data) current next write work input auxiliary sourceIndex emit)
        (afterStep next live sourceIndex) := by
  apply BankConfiguration.ext <;> try rfl
  · simp only [TapeBank.advance,bank,selected,configuration,Fin.addCases_right,BankEmbedding.update_right]
  · simp only [TapeBank.advance,bank,selected,configuration,Fin.addCases_right,BankEmbedding.update_right]
    congr 1
    funext j position
    by_cases same : j=source.select current.state
    · subst j
      by_cases location : position=current.head (source.select current.state)
      · subst position
        simp [encodeSource]
      · simp [Function.update_of_ne location,encodeSource]
    · simp [Function.update_of_ne same,encodeSource]

theorem source_choose (length index : ℕ) (current : BankConfiguration O Q S k) (live : Bool) (next : Q) :
    TapeBank.choose (configuration source length index current (.execute current.state live)) (.probe next (.scan false)) =
      configuration source length index (TapeBank.choose current next) (.probe next (.scan false)) := rfl

theorem configuration_bounded (data : InputData I A) (length index : ℕ) (current : BankConfiguration O Q S k)
    (state : Control Q) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current) :
    (bank source).Bounded data radius (configuration source length index current state) := by
  refine ⟨bounded.input,bounded.auxiliary,Nat.zero_le _,?_⟩
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [configuration]
  · simpa [configuration] using bounded.head j

theorem source_step (data : InputData I A) (choices : BitString) (current : BankConfiguration O Q S k)
    (live : Bool) (availability : live=decide (current.indexHead<data.input.length))
    (next write work input auxiliary sourceIndex emit)
    (table : source.instruction (sourceData data) current=.step next write work input auxiliary sourceIndex emit) :
    (bank source).Steps data choices (configuration source data.input.length current.indexHead current (.execute current.state live)) 1
      (configuration source data.input.length current.indexHead
        (source.advance (sourceData data) current next write work input auxiliary sourceIndex emit) (afterStep next live sourceIndex)) := by
  have nativeTable : (bank source).instruction data
      (configuration source data.input.length current.indexHead current (.execute current.state live))=
      .step (afterStep next live sourceIndex) (encodeSource write) work input auxiliary .stay emit := by
    rw [source_instruction source data current live availability,table]
    rfl
  have path := TapeBank.Steps.single (bank source) data choices _ _ _ _ _ _ _ _ nativeTable
  rw [source_advance] at path
  exact path

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
