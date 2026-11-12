import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Fields

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def labelStore (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s 25 (s 33)) 19 (List.replicate (s 38).length (.bit true)))
    27 (List.replicate (s 37).length (.bit true)))
    26 (List.replicate (s 37).length (.bit true))) 16 [.bit true]) 48 []

theorem labelPrepare_eval (s : Store) : labelPrepare.eval s = labelStore s := by
  funext j
  by_cases a : j=25 <;> by_cases b : j=19 <;> by_cases c : j=27 <;>
    by_cases d : j=26 <;> by_cases e : j=16 <;> by_cases f : j=48 <;>
    simp [labelPrepare,labelStore,Routine.seq,Routine.assign_eval,Routine.clear,
      Routine.ofLocal,Local.eval_push,Function.update_apply,List.map_const',a,b,c,d,e,f]

theorem labelBits_value (s : Store) :
    ((LabelBits.routine (O := Symbol)).rename Output.low32).eval s 28 =
      List.replicate (FixedBitBlocks.decode (((s 25).map readBit ++
        List.replicate (s 19).length false).take (s 19).length)) (.bit true) := by
  change ((LabelBits.routine (O := Symbol)).rename Output.low32).eval s (Output.low32 28) = _
  rw [Routine.rename_eval_here,LabelBits.routine_value]
  rfl

theorem labelBits_input (s : Store) (j : Fin 32) (outside : 16 ≤ j.val)
    (scratch : j ≠ 18) (result : j ≠ 28) :
    ((LabelBits.routine (O := Symbol)).rename Output.low32).eval s (Output.low32 j) = s (Output.low32 j) := by
  rw [Routine.rename_eval_here,LabelBits.routine_frame _ j outside scratch result]
  rfl

theorem labelChecks_input (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (flag : j ≠ 20) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    ((LabelChecks.routine (O := Symbol)).rename Output.low32).eval s (Output.low32 j) = s (Output.low32 j) := by
  rw [Routine.rename_eval_here,LabelChecks.routine_frame _ j valid flag copy counter scratch]
  rfl

theorem label_values (s : Store) (labelWidth : (s 38).length = width (s 37).length) :
    label.eval s 39 = List.replicate (nextValue (s 37).length (s 33)) (.bit true) ∧
      label.eval s 41 = if validCandidate (s 37).length (s 37).length (s 33) then s 41 else [] := by
  let a := labelStore s
  let b := ((LabelBits.routine (O := Symbol)).rename Output.low32).eval a
  let c := ((LabelChecks.routine (O := Symbol)).rename Output.low32).eval b
  let d := (Routine.assign (O := Symbol) 28 39 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval c
  let inputs : Fin 4 → Fin 32 := ![25,19,27,26]
  have bInputs (j : Fin 4) :
      b (Output.low32 (inputs j)) = a (Output.low32 (inputs j)) := by
    fin_cases j <;> exact labelBits_input a _ (by decide) (by decide) (by decide)
  have bValid : b 16 = [.bit true] := by
    change ((LabelBits.routine (O := Symbol)).rename Output.low32).eval a (Output.low32 16) = _
    rw [labelBits_input a 16 (by decide) (by decide) (by decide)]
    simp [a,labelStore,show Output.low32 16 = 16 from rfl]
  have bNext : b 28 = List.replicate (nextValue (s 37).length (s 33)) (.bit true) := by
    change ((LabelBits.routine (O := Symbol)).rename Output.low32).eval a 28 = _
    rw [labelBits_value]
    simp [a,labelStore,labelWidth,nextValue]
  have cNext : c 28 = b 28 := labelChecks_input b 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have cHigh : c 41 = s 41 := by
    dsimp only [c,b]
    rw [call32_frame _ _ 41 (by decide),call32_frame _ _ 41 (by decide)]
    simp [a,labelStore]
  have correct : LabelChecks.correct (b ∘ Output.low32) =
      validCandidate (s 37).length (s 37).length (s 33) := by
    have word := bInputs 0
    have count := bInputs 1
    have parent := bInputs 2
    have forbidden := bInputs 3
    change b 25 = a 25 at word
    change b 19 = a 19 at count
    change b 27 = a 27 at parent
    change b 26 = a 26 at forbidden
    simp only [LabelChecks.correct,Function.comp_apply,show Output.low32 25 = 25 from rfl,
      show Output.low32 19 = 19 from rfl,show Output.low32 28 = 28 from rfl,
      show Output.low32 27 = 27 from rfl,show Output.low32 26 = 26 from rfl,
      word,count,parent,forbidden,bNext]
    simp [a,labelStore,labelWidth,validCandidate]
  have cValid : c 16 = if validCandidate (s 37).length (s 37).length (s 33) then [.bit true] else [] := by
    change ((LabelChecks.routine (O := Symbol)).rename Output.low32).eval b (Output.low32 16) = _
    rw [Routine.rename_eval_here,LabelChecks.routine_flag,correct]
    exact congrArg (fun word => if validCandidate (s 37).length (s 37).length (s 33) then word else []) bValid
  simp only [label,Routine.seq,labelPrepare_eval]
  change (require 16 true).eval d 39 = _ ∧ (require 16 true).eval d 41 = _
  simp only [require_eval]
  constructor
  · simp [d,Routine.assign_eval,cNext,bNext,List.map_const']
  · have dValid : d 16 = c 16 := by simp [d,Routine.assign_eval]
    have dFlag : d 41 = c 41 := by simp [d,Routine.assign_eval]
    rw [Function.update_self,dValid,dFlag,cHigh,cValid]
    cases good : validCandidate (s 37).length (s 37).length (s 33) <;> simp [good]

theorem candidate_self_valid (size : ℕ) (label : List Symbol) :
    validCandidate size size label = (decodeLabel size label).isSome := by
  have same := candidate_eq_decodeLabel size size label
  cases decoded : decodeLabel size label with
  | none =>
      simp only [decoded] at same
      by_cases valid : validCandidate size size label <;> simp_all [candidate]

  | some next =>
      have bound := (decodeLabel_sound size label next decoded).1
      have different : next ≠ size := by omega
      simp only [decoded,ite_eq_right different] at same
      by_cases valid : validCandidate size size label <;> simp_all [candidate]

theorem label_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (next : j ≠ 39) (valid : j ≠ 41) (scratch : j ≠ 48) : label.eval s j = s j := by
  have low (i : Fin 64) (inside : i.val < 32) : j ≠ i := by
    intro equal
    have := congrArg Fin.val equal
    omega
  simp [label,Routine.seq,require_eval,Routine.assign_eval,Function.update_apply,
    next,valid,scratch,call32_frame _ _ j outside,labelPrepare_eval,labelStore,low]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
