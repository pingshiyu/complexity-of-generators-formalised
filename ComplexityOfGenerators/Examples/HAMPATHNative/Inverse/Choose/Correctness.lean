import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Fields
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Force

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

def protectedRegisters : Fin 8 → Fin 64 := ![32,33,34,35,36,37,38,39]

theorem routine_frame (s : Store) (i : Fin 8) : routine.eval s (protectedRegisters i)=s (protectedRegisters i) := by
  simp only [routine,Routine.seq]
  rw [forceEdge_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    position_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    incidents_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    candidate_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]

structure Result (out source : Store) (size start next blockWidth : ℕ) (bits : List Bool) : Prop where
  chosen : out 40=List.replicate
    ((Position.value size start next (FixedBitBlocks.decode (bits.take blockWidth))).getD 0) (.bit true)
  live : out 41=if (Position.value size start next (FixedBitBlocks.decode (bits.take blockWidth))).isSome then source 41 else []
  incoming : out 44=((bits.drop blockWidth).take size).map Symbol.bit
  outgoing : out 45=(List.range size).map
    (fun vertex => Symbol.bit (forcedRow ((bits.drop (blockWidth+size)).take size) start vertex))

theorem routine_values (s : Store) (size start next blockWidth : ℕ) (bits : List Bool)
    (sourceSize : (s 35).length=size) (sourceStart : (s 36).length=start)
    (sourceNext : (s 39).length=next) (sourceWidth : (s 38).length=blockWidth)
    (sourceBits : s 42=bits.map Symbol.bit) (inside : start<size)
    (enough : blockWidth+2*size≤bits.length) :
    Result (routine.eval s) s size start next blockWidth bits := by
  let a := candidate.eval s
  let b := incidents.eval a
  let c := position.eval b
  let d := forceEdge.eval c
  have aProtected (i : Fin 5) : a (![35,36,38,39,41] i)=s (![35,36,38,39,41] i) := by
    fin_cases i <;> exact candidate_frame s _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have aSize : (a 35).length=size := (congrArg List.length (aProtected 0)).trans sourceSize
  have aStart : (a 36).length=start := (congrArg List.length (aProtected 1)).trans sourceStart
  have aNext : (a 39).length=next := (congrArg List.length (aProtected 3)).trans sourceNext
  have aLive : a 41=s 41 := aProtected 4
  have aCandidate : a 40=List.replicate (FixedBitBlocks.decode (bits.take blockWidth)) (.bit true) := by
    have value := (candidate_values s (by rw [sourceWidth,sourceBits,List.length_map]; omega)).1
    simpa [sourceBits,sourceWidth,← List.map_take,List.map_map,Function.comp_def,readBit] using value
  have aBits : a 42=(bits.drop blockWidth).map Symbol.bit := by
    simpa [sourceBits,sourceWidth,← List.map_drop] using (candidate_values s (by rw [sourceWidth,sourceBits,List.length_map]; omega)).2
  have bProtected (i : Fin 6) : b (![35,36,38,39,40,41] i)=a (![35,36,38,39,40,41] i) := by
    fin_cases i <;> exact incidents_frame a _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have bSize : (b 35).length=size := (congrArg List.length (bProtected 0)).trans aSize
  have bStart : (b 36).length=start := (congrArg List.length (bProtected 1)).trans aStart
  have bNext : (b 39).length=next := (congrArg List.length (bProtected 3)).trans aNext
  have bCandidate : (b 40).length=FixedBitBlocks.decode (bits.take blockWidth) := by
    have same : b 40=a 40 := bProtected 4
    rw [same,aCandidate,List.length_replicate]
  have bLive : b 41=s 41 := (bProtected 5).trans aLive
  have bIncoming : b 44=((bits.drop blockWidth).take size).map Symbol.bit := by
    have value : b 44=(a 42).take (a 35).length := (incidents_values a).1
    simpa only [aBits,aSize,← List.map_take] using value
  have bOutgoing : b 45=((bits.drop (blockWidth+size)).take size).map Symbol.bit := by
    have value : b 45=((a 42).drop (a 35).length).take (a 35).length := (incidents_values a).2.1
    simpa only [aBits,aSize,← List.map_drop,← List.map_take,List.drop_drop] using value
  have cStart : (c 36).length=start := by
    exact (congrArg List.length (position_frame b 36 (by decide) (by decide) (by decide) (by decide))).trans bStart
  have cChosen : c 40=List.replicate
      ((Position.value size start next (FixedBitBlocks.decode (bits.take blockWidth))).getD 0) (.bit true) := by
    have value := (position_values b).1
    simpa only [bSize,bStart,bNext,bCandidate] using value
  have cLive : c 41=if (Position.value size start next (FixedBitBlocks.decode (bits.take blockWidth))).isSome then s 41 else [] := by
    have value := (position_values b).2
    simpa only [bSize,bStart,bNext,bCandidate,bLive] using value
  have cIncoming : c 44=b 44 := position_frame b 44 (by decide) (by decide) (by decide) (by decide)
  have cOutgoing : c 45=b 45 := position_frame b 45 (by decide) (by decide) (by decide) (by decide)
  have result : Result d s size start next blockWidth bits := by
    constructor
    · exact (forceEdge_frame c 40 (by decide) (by decide) (by decide) (by decide)).trans cChosen
    · exact (forceEdge_frame c 41 (by decide) (by decide) (by decide) (by decide)).trans cLive
    · exact (forceEdge_frame c 44 (by decide) (by decide) (by decide) (by decide)).trans (cIncoming.trans bIncoming)
    · have windowLength : ((bits.drop (blockWidth+size)).take size).length=size := by
        simp only [List.length_take,List.length_drop]
        omega
      have value := forceEdge_word c ((bits.drop (blockWidth+size)).take size) start
        (cOutgoing.trans bOutgoing) cStart (by omega)
      rw [windowLength] at value
      exact value
  simpa only [routine_eval,d,c,b,a] using result

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
