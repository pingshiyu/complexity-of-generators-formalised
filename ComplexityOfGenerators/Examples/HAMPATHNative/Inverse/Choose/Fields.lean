import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Label

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem candidate_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (chosen : j≠40) (source : j≠42) (counter : j≠46) (buffer : j≠47) (scratch : j≠48) :
    candidate.eval s j=s j := by
  have low (i : Fin 64) (inside : i.val<32) : j≠i := by intro e; have := congrArg Fin.val e; omega
  simp [candidate,Routine.seq,Routine.assign_eval,Function.update_apply,
    Classify.call32_frame _ _ j outside,TakeWord.routine_eval,candidateSlots,
    chosen,source,counter,buffer,scratch,low]

theorem candidate_values (s : Store) (enough : (s 38).length ≤ (s 42).length) :
    candidate.eval s 40 = List.replicate
        (FixedBitBlocks.decode (((s 42).take (s 38).length).map readBit)) (.bit true) ∧
      candidate.eval s 42 = (s 42).drop (s 38).length := by
  let a := (TakeWord.routine (O := Symbol) candidateSlots).eval s
  let b := (Routine.assign (O := Symbol) 38 19 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval a
  let c := ((LabelBits.routine (O := Symbol)).rename Output.low32).eval b
  have aLabel : a 25 = (s 42).take (s 38).length := by simp [a,TakeWord.routine_eval,candidateSlots]
  have aWidth : a 38=s 38 := by simp [a,TakeWord.routine_eval,candidateSlots]
  have bLabel : b 25 = a 25 := by simp [b,Routine.assign_eval]
  have bWidth : (b 19).length=(s 38).length := by simp [b,Routine.assign_eval,aWidth]
  have prefixLength : ((a 25).map readBit).length=(s 38).length := by simp [aLabel,Nat.min_eq_left enough]
  have padded : ((b 25).map readBit ++ List.replicate (b 19).length false).take (b 19).length =
      ((s 42).take (s 38).length).map readBit := by
    rw [bLabel,bWidth,List.take_left' prefixLength,aLabel]
  have numeric : c 28 = List.replicate
      (FixedBitBlocks.decode (((s 42).take (s 38).length).map readBit)) (.bit true) := by
    have value := Classify.labelBits_value b
    rw [padded] at value
    exact value
  have cRest : c 42 = (s 42).drop (s 38).length := by
    dsimp only [c]
    rw [Classify.call32_frame _ _ 42 (by decide)]
    simp [b,Routine.assign_eval,a,TakeWord.routine_eval,candidateSlots]
  change (Routine.assign (O := Symbol) 28 40 48 (by decide) (by decide) (by decide)
    (fun _ => Symbol.bit true)).eval c 40 = _ ∧ _
  constructor
  · simp [Routine.assign_eval,numeric]
  · change (Routine.assign (O := Symbol) 28 40 48 (by decide) (by decide) (by decide)
      (fun _ => Symbol.bit true)).eval c 42 = _
    simp [Routine.assign_eval,cRest]

theorem incidents_values (s : Store) :
    incidents.eval s 44 = (s 42).take (s 35).length ∧
      incidents.eval s 45 = ((s 42).drop (s 35).length).take (s 35).length ∧
      incidents.eval s 42 = (s 42).drop (2*(s 35).length) := by
  simp [incidents,Routine.seq,TakeWord.routine_eval,incomingSlots,outgoingSlots,List.drop_drop]
  omega

theorem incidents_frame (s : Store) (j : Fin 64) (source : j≠42) (incoming : j≠44)
    (outgoing : j≠45) (counter : j≠46) (buffer : j≠47) (scratch : j≠48) :
    incidents.eval s j=s j := by
  simp [incidents,Routine.seq,TakeWord.routine_eval,incomingSlots,outgoingSlots,
    Function.update_apply,source,incoming,outgoing,counter,buffer,scratch]

theorem positionPrepare_frame (s : Store) (j : Fin 64) (outside : 4 ≤ j.val) (scratch : j≠48) :
    positionPrepare.eval s j=s j := by
  have low (i : Fin 64) (inside : i.val<4) : j≠i := by intro e; have := congrArg Fin.val e; omega
  simp [positionPrepare,Routine.seq,Routine.assign_eval,Function.update_apply,scratch,low]

theorem position_values (s : Store) :
    position.eval s 40 = List.replicate
        ((Position.value (s 35).length (s 36).length (s 39).length (s 40).length).getD 0) (.bit true) ∧
      position.eval s 41 =
        if (Position.value (s 35).length (s 36).length (s 39).length (s 40).length).isSome then s 41 else [] := by
  let a := positionPrepare.eval s
  let b := ((Position.routine (O := Symbol)).rename low12).eval a
  let c := (Routine.assign (O := Symbol) 4 40 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval b
  have inputs (i : Fin 4) : (a (low12 ⟨i.val,by omega⟩)).length =
      (s (![35,36,39,40] i)).length := by
    fin_cases i <;> simp [a,positionPrepare,Routine.seq,Routine.assign_eval,low12]
  have chosen := Position.routine_values (O := Symbol) (a ∘ low12)
  have input0 : (a (low12 0)).length=(s 35).length := by simpa using inputs 0
  have input1 : (a (low12 1)).length=(s 36).length := by simpa using inputs 1
  have input2 : (a (low12 2)).length=(s 39).length := by simpa using inputs 2
  have input3 : (a (low12 3)).length=(s 40).length := by simpa using inputs 3
  simp only [Function.comp_apply,input0,input1,input2,input3] at chosen
  have bValue : b 4 = List.replicate
      ((Position.value (s 35).length (s 36).length (s 39).length (s 40).length).getD 0) (.bit true) := by
    change ((Position.routine (O := Symbol)).rename low12).eval a (low12 4)=_
    rw [Routine.rename_eval_here]
    exact chosen.1
  have bFound : (b 5).head?.isSome =
      (Position.value (s 35).length (s 36).length (s 39).length (s 40).length).isSome := by
    change (((Position.routine (O := Symbol)).rename low12).eval a (low12 5)).head?.isSome=_
    rw [Routine.rename_eval_here]
    exact chosen.2
  have bHigh : b 41=s 41 := by
    dsimp only [b]
    rw [Routine.rename_eval_frame]
    · exact positionPrepare_frame s 41 (by decide) (by decide)
    · intro i equal
      have := congrArg Fin.val equal
      dsimp [low12] at this
      omega
  change (Classify.require 5 true).eval c 40=_ ∧ (Classify.require 5 true).eval c 41=_
  simp only [Classify.require_eval]
  constructor
  · simp [c,Routine.assign_eval,bValue]
  · have cFound : (c 5).head?.isSome=(b 5).head?.isSome := by simp [c,Routine.assign_eval]
    have cHigh : c 41=b 41 := by simp [c,Routine.assign_eval]
    rw [Function.update_self,cFound,cHigh,bHigh,bFound]

theorem position_frame (s : Store) (j : Fin 64) (outside : 32≤j.val)
    (chosen : j≠40) (valid : j≠41) (scratch : j≠48) : position.eval s j=s j := by
  have sourceFrame (t : Store) : ((Position.routine (O := Symbol)).rename low12).eval t j=t j := by
    apply Routine.rename_eval_frame
    intro i equal
    have := congrArg Fin.val equal
    dsimp [low12] at this
    omega
  simp [position,Routine.seq,Classify.require_eval,Routine.assign_eval,
    Function.update_apply,chosen,valid,scratch,sourceFrame,
    positionPrepare_frame s j (by omega) scratch]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
