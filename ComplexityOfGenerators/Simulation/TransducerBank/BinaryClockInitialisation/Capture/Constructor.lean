import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Zeros

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

 theorem output_length_mono {data : InputData Unit Bool} {bits : BitString} {radius ticks : ℕ}
    {start finish : BankConfiguration Unit Q S k} (path : C.RegionSteps data bits radius start ticks finish) :
    start.output.length≤finish.output.length := by
  induction path with
  | refl => exact le_rfl
  | random start no yes bit ticks finish bounded table lookup rest ih => simpa only [TapeBank.choose] using ih
  | step start next write work input auxiliary index emit ticks finish bounded table rest ih =>
      simp only [TapeBank.advance,List.length_append] at ih
      omega

/-- Constructor output is stored as physical zero digits. The intermediate
clock cursor stays below the final width, independently of constructor time. -/
 theorem constructor_region (copies seed limit radius : ℕ) (data : InputData I A) (bits : BitString)
    (length temporary : List Bool) (deterministic : C.Deterministic)
    {start finish : BankConfiguration Unit Q S k} {ticks : ℕ}
    (path : C.RegionSteps (decisionData (List.replicate data.input.length ())) [] radius start ticks finish)
    (outputLimit : finish.output.length≤limit) :
    ∃ actual, (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits (radius+seed+copies*limit+3)
      (configuration C copies (.construct start.state) length temporary
        (List.replicate (seed+copies*start.output.length) false) start.inputHead 0 (seed+copies*start.output.length) start)
      actual
      (configuration C copies (.construct finish.state) length temporary
        (List.replicate (seed+copies*finish.output.length) false) finish.inputHead 0 (seed+copies*finish.output.length) finish) := by
  induction path with
  | refl start bounded =>
      refine ⟨0,.refl _ ?_⟩
      apply configuration_bounded (O:=O) C copies _ data _ length temporary _ start.inputHead 0 _ start
      · simpa [decisionData] using bounded.input
      · intro j; exact (bounded.head j).trans (by omega)
      · simp
      · simp only [←Nat.cast_add,←Nat.cast_mul,Int.natAbs_natCast]
        exact (Nat.add_le_add_left (Nat.mul_le_mul_left copies outputLimit) seed).trans (by omega)
  | random start no yes bit ticks finish bounded table lookup rest ih =>
      have never := deterministic start.state
        (List.replicate data.input.length ())[start.inputHead]? ([]:List Bool)[start.auxiliaryHead]?
        (if start.indexHead<0 then some () else none)
        (decide (start.head (C.select start.state)=0)) (start.tape (C.select start.state) (start.head (C.select start.state)))
      simp only [TapeBank.instruction,decisionData] at table
      rw [table] at never
      exact False.elim never
  | step start next write work input auxiliary index emit ticks finish bounded table rest ih =>
      obtain ⟨actual,tail⟩ := ih outputLimit
      have small := output_length_mono C rest
      have sourceInput : start.inputHead≤data.input.length := by simpa [decisionData] using bounded.input
      have sourceLength : start.output.length≤limit := by
        simp only [TapeBank.advance,List.length_append] at small
        omega
      have startBound := configuration_bounded (O:=O) C copies (radius+seed+copies*limit+3) data (.construct start.state)
        length temporary (List.replicate (seed+copies*start.output.length) false) start.inputHead 0
        (seed+copies*start.output.length) start sourceInput
        (fun j=>(bounded.head j).trans (by omega)) (by simp)
        (by simpa only [←Nat.cast_add,←Nat.cast_mul,Int.natAbs_natCast] using
          (Nat.add_le_add_left (Nat.mul_le_mul_left copies sourceLength) seed).trans (by omega))
      have stepTable := constructor_instruction (O:=O) C copies data length temporary (List.replicate (seed+copies*start.output.length) false) start
        next write work input auxiliary index emit table
      have advanced := configuration_constructorStep (O:=O) C copies data length temporary
        (List.replicate (seed+copies*start.output.length) false) start next write work input auxiliary index emit
      simp only [List.length_replicate,Nat.cast_add,Nat.cast_mul] at stepTable advanced
      cases emit with
      | none =>
          refine ⟨actual+1,?_⟩
          apply TapeBank.RegionSteps.step _ _ _ work input .stay .stay none actual _ startBound stepTable
          rw [advanced]
          simpa [TapeBank.advance] using tail
      | some unit =>
          cases unit
          have nextBound := rest.start_bound C
          have nextInput : (C.advance (decisionData (List.replicate data.input.length ())) start next write work input auxiliary index (some ())).inputHead≤data.input.length := by
            simpa [decisionData] using nextBound.input
          have nextLength : start.output.length+1≤limit := by
            simpa [TapeBank.advance] using small.trans outputLimit
          have adding := zeros_region (O:=O) C copies copies (seed+copies*start.output.length) (radius+seed+copies*limit+3) next
            data bits length temporary
            ((C.advance (decisionData (List.replicate data.input.length ())) start next write work input auxiliary index (some ())).inputHead)
            (C.advance (decisionData (List.replicate data.input.length ())) start next write work input auxiliary index (some ()))
            (by omega) nextInput (fun j=>(nextBound.head j).trans (by omega)) (by
              have upper := Nat.mul_le_mul_left copies nextLength
              simp only [Nat.mul_add,Nat.mul_one] at upper
              omega)
          simp only [Nat.cast_add,Nat.cast_mul] at adding
          refine ⟨(copies+1+actual)+1,?_⟩
          apply TapeBank.RegionSteps.step _ _ _ work input .stay .stay none (copies+1+actual) _ startBound stepTable
          rw [advanced]
          simpa only [Option.isSome_some,ite_true] using adding.trans (bank (I:=I) (A:=A) (O:=O) C copies) (by
            simpa [TapeBank.advance,mul_add,Nat.cast_add,Nat.cast_mul,add_assoc] using tail)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
