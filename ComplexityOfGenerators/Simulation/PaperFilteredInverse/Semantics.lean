import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Execution
import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Eval
import ComplexityOfGenerators.Proofs.PaperExactRecursiveTrials

/-! The concrete controller's accepted output is exactly one bounded inverse
call satisfying the candidate-length and certificate-width filters. -/
namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

theorem body_accept_iff (seed time q : PolynomialBound) (width : Word α→ℕ)
    (correct : ∀ x,W.Produces {input:=x} [] (List.replicate (width x) ()))
    (bounded : ∀ x,W.TimeBound {input:=x} (q x.length))
    (data : InputData α α) (bits : BitString) (word : Word α) :
    finishValue M W (bodyMemory M W seed time q data bits)=some word↔
      M.run data (bits.take (seed data.index)) (time data.index)=.halted (.accepted word) ∧
      word.length≤data.index ∧ data.auxiliary.length=width word := by
  let s := initialStore M W seed data.index data.input data.auxiliary bits
  have input : (s 11).map (inverseInput M W)=data.input.map (fun a=>Symbol.inverse (.input a)) := by
    simp [s,initialStore,BoundedSource.preparedMemory,letters,inverseInput]
  have aux : (s 12).map (inverseAuxiliary M W)=data.auxiliary.map (fun a=>Symbol.inverse (.auxiliary a)) := by
    simp [s,initialStore,BoundedSource.preparedMemory,letters,inverseAuxiliary]
  have idx : (s 13).length=data.index := by simp [s,initialStore,BoundedSource.preparedMemory]
  have random : s 17=(bits.take (seed data.index)).map Symbol.bit := by
    simp [s,initialStore,BoundedSource.preparedMemory]
  have empty : s 14=[] := by simp [s,initialStore,BoundedSource.preparedMemory]
  obtain ⟨status,out,state,output,character⟩ := BoundedSource.sourceTrial_result
    (O:=α) (Symbol.unit : Cell M W) Symbol.bit M Symbol.inverse (inverseDecode M W)
      (inverseDecode_encode M W) (inverseInput M W) (inverseAuxiliary M W) (inverseBit M W)
      (by intro bit;rfl) seed time s data (bits.take (seed data.index)) input aux idx random empty
  change (firstCall M W seed time).eval s 0=[Symbol.inverse (.state status)] at state
  change (firstCall M W seed time).eval s 10=out.map (fun a=>Symbol.inverse (.output a)) at output
  have char (x : Word α) : (status=.accepted ∧ out.reverse=x)↔
      M.run data (bits.take (seed data.index)) (time data.index)=.halted (.accepted x) := by
    simpa only [List.take_take,Nat.min_self] using character x
  let called := (firstCall M W seed time).eval s
  have called25 : called 25=s 25 := firstCall_frame M W seed time s 25 (Or.inr (Or.inr (Or.inr rfl)))
  have called13 : called 13=s 13 := firstCall_frame M W seed time s 13 (Or.inr (Or.inr (Or.inl rfl)))
  have called12 : called 12=s 12 := firstCall_frame M W seed time s 12 (Or.inr (Or.inl rfl))
  have calledEmpty : called 25=[] := by
    rw [called25]
    simp [s,initialStore,BoundedSource.preparedMemory]
  have captureEq := capture_eval M W called status out state output calledEmpty
  let captured := (capture M W).eval called
  have candidate : captured 25=letters M W out.reverse := by simp [captured,captureEq]
  have index : (captured 13).length=data.index := by
    simpa [captured,captureEq,called13] using idx
  have label : (captured 23).length=data.auxiliary.length := by
    simp [captured,captureEq,called12,s,initialStore,BoundedSource.preparedMemory,letters]
  have active : (captured 26).head?.isSome=decide (status=.accepted) := by
    by_cases accepted : status=.accepted <;> simp [captured,captureEq,accepted]
  obtain ⟨c25,c26,c27,c28⟩ := checks_fields M W q width correct bounded captured out.reverse data.index
    data.auxiliary.length candidate index label
  change (bodyStore M W seed time q data bits) 25=letters M W out.reverse at c25
  change ((bodyStore M W seed time q data bits) 26).head?.isSome=(captured 26).head?.isSome at c26
  change ((bodyStore M W seed time q data bits) 27).head?.isSome=decide (out.reverse.length≤data.index) at c27
  change ((bodyStore M W seed time q data bits) 28).head?.isSome=
    (if (captured 26).head?.isSome then decide (out.reverse.length≤data.index ∧ data.auxiliary.length=width out.reverse) else false) at c28
  rw [active] at c26 c28
  have value : finishValue M W (bodyMemory M W seed time q data bits)=
      if status=.accepted ∧ out.reverse.length≤data.index ∧ data.auxiliary.length=width out.reverse
      then some out.reverse else none := by
    change (if ((bodyStore M W seed time q data bits) 26).head?.isSome then
      if ((bodyStore M W seed time q data bits) 27).head?.isSome then
        if ((bodyStore M W seed time q data bits) 28).head?.isSome then
          some ([]++((bodyStore M W seed time q data bits) 25).filterMap (decodeOutput M W)) else none
      else none else none)=_
    rw [c26,c27,c28,c25,decodeOutput_letters]
    by_cases accepted : status=.accepted <;> by_cases small : out.reverse.length≤data.index <;>
      by_cases equal : data.auxiliary.length=width out.reverse <;> simp [accepted,small,equal]
  rw [value]
  constructor
  · intro accepted
    split_ifs at accepted with valid
    · have same := Option.some.inj accepted
      subst word
      exact ⟨(char out.reverse).mp ⟨valid.1,rfl⟩,valid.2⟩
  · rintro ⟨accepted,size,widthEq⟩
    have source := (char word).mpr accepted
    rcases source with ⟨acceptedStatus,rfl⟩
    exact if_pos ⟨acceptedStatus,size,widthEq⟩

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
