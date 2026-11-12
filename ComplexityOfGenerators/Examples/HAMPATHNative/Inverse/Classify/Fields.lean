import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem call32_frame (source : Routine Symbol Symbol 32) (s : Store) (j : Fin 64)
    (outside : 32 ≤ j.val) : (source.rename Output.low32).eval s j = s j := by
  apply Routine.rename_eval_frame
  intro i equal
  have := congrArg Fin.val equal
  dsimp [Output.low32] at this
  omega

theorem call16_frame (source : Routine Symbol Symbol 16) (s : Store) (j : Fin 64)
    (outside : 16 ≤ j.val) : (source.rename Output.low16).eval s j = s j := by
  apply Routine.rename_eval_frame
  intro i equal
  have := congrArg Fin.val equal
  dsimp [Output.low16] at this
  omega

theorem parser_size (s : Store) :
    ((parser (O := Symbol)).rename Output.low32).eval s 4 =
      List.replicate (headerSize (s 2)) (.bit true) := by
  change ((parser (O := Symbol)).rename Output.low32).eval s (Output.low32 4) = _
  rw [Routine.rename_eval_here,parser_eval]
  simp [startEncoded,rowEncoded,cellEncoded,Function.comp_def,show Output.low32 2 = 2 from rfl]

theorem parser_start (s : Store) :
    ((parser (O := Symbol)).rename Output.low32).eval s 13 =
      List.replicate (parsedState (s 2)).start (.bit true) := by
  change ((parser (O := Symbol)).rename Output.low32).eval s (Output.low32 13) = _
  rw [Routine.rename_eval_here,parser_eval]
  simp [startEncoded,Function.comp_def,show Output.low32 2 = 2 from rfl]

theorem parse_values (s : Store) :
    parse.eval s 35 = List.replicate (headerSize (s 32)) (.bit true) ∧
      parse.eval s 36 = List.replicate (parsedState (s 32)).start (.bit true) := by
  simp [parse,Routine.seq,Routine.assign_eval,parser_size,parser_start,List.map_const']

theorem parse_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (size : j ≠ 35) (start : j ≠ 36) (scratch : j ≠ 48) : parse.eval s j = s j := by
  have low : j ≠ 2 := by intro e; have := congrArg Fin.val e; omega
  simp [parse,Routine.seq,Routine.assign_eval,Function.update_apply,size,start,scratch,low,
    call32_frame _ _ j outside]

theorem productive_value (s : Store) :
    (productive.eval s 41).head?.isSome = decide (BaseSearch.Productive (s 34).length) := by
  let a := (Routine.assign (O := Symbol) 34 12 48 (by decide) (by decide) (by decide)
    (fun _ => Symbol.bit true)).eval s
  have found := Productive.routine_found (a ∘ Output.low16)
  have atFound : (Productive.routine.rename Output.low16).eval a 11 =
      Productive.routine.eval (a ∘ Output.low16) 11 := by
    exact Routine.rename_eval_here _ _ _ 11
  change ((Routine.assign (O := Symbol) 11 41 48 (by decide) (by decide) (by decide)
    (fun _ => Symbol.bit true)).eval ((Productive.routine.rename Output.low16).eval a) 41).head?.isSome = _
  simp only [Routine.assign_eval,Function.update_self,List.head?_map,Option.isSome_map]
  rw [atFound,found]
  simp [a,Routine.assign_eval,Function.comp_def,show Output.low16 12 = 12 from rfl]

theorem productive_frame (s : Store) (j : Fin 64) (outside : 16 ≤ j.val)
    (flag : j ≠ 41) (scratch : j ≠ 48) : productive.eval s j = s j := by
  have input : j ≠ 12 := by intro e; have := congrArg Fin.val e; omega
  simp [productive,Routine.seq,Routine.assign_eval,Function.update_apply,flag,scratch,input,
    call16_frame _ _ j outside]

theorem logarithm_value (s : Store) :
    ((Logarithm.routine (O := Symbol)).rename Output.low32).eval s 19 =
      List.replicate (Nat.clog 2 (s 17).length) (.bit true) := by
  change ((Logarithm.routine (O := Symbol)).rename Output.low32).eval s (Output.low32 19) = _
  rw [Routine.rename_eval_here,Logarithm.routine_value]
  rfl

theorem logarithm_source (s : Store) :
    ((Logarithm.routine (O := Symbol)).rename Output.low32).eval s 17 = s 17 := by
  change ((Logarithm.routine (O := Symbol)).rename Output.low32).eval s (Output.low32 17) = _
  rw [Routine.rename_eval_here,Logarithm.routine_frame _ 17 (by decide) (by decide) (by decide)]
  rfl

theorem parent_values (s : Store) :
    parent.eval s 37 = List.replicate ((s 35).length+1) (.bit true) ∧
      parent.eval s 38 = List.replicate (Nat.clog 2 ((s 35).length+1)) (.bit true) := by
  simp [parent,Routine.seq,Routine.assign_eval,Routine.ofLocal,Local.eval_push,
    logarithm_value,logarithm_source,List.map_const']

theorem parent_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (size : j ≠ 37) (labelWidth : j ≠ 38) (scratch : j ≠ 48) : parent.eval s j = s j := by
  have seventeen : j ≠ 17 := by intro e; have := congrArg Fin.val e; omega
  simp [parent,Routine.seq,Routine.assign_eval,Routine.ofLocal,Local.eval_push,
    Function.update_apply,size,labelWidth,scratch,seventeen,call32_frame _ _ j outside]

theorem capacity_flag (s : Store) :
    capacity.eval s 41 = if encodingLength (s 37).length ≤ (s 34).length then s 41 else [] := by
  have polynomial : BaseSearch.square (s 37).length+1 = encodingLength (s 37).length := by
    simp only [BaseSearch.square,PolynomialBound.eval,encodingLength]
    ring
  by_cases fits : encodingLength (s 37).length ≤ (s 34).length
  · have above : ¬ (s 34).length < encodingLength (s 37).length := by omega
    have test : ¬ (s 34).length ≤ BaseSearch.square (s 37).length := by omega
    simp [capacity,Routine.seq,CounterRoutine.routine_eval,Routine.ofLocal,Local.eval_push,
      RationalSelection.Compare.routine_eval,require_eval,counterSlots,capacitySlots,polynomial,fits,above,test]
  · have above : (s 34).length < encodingLength (s 37).length := by omega
    have test : ¬ BaseSearch.square (s 37).length < (s 34).length := by omega
    simp [capacity,Routine.seq,CounterRoutine.routine_eval,Routine.ofLocal,Local.eval_push,
      RationalSelection.Compare.routine_eval,require_eval,counterSlots,capacitySlots,polynomial,fits,above,test]

theorem singleton_flag (s : Store) :
    singleton.eval s 41 = if (s 35).length = 1 then s 41 else [] := by
  by_cases one : (s 35).length = 1 <;>
    simp [singleton,Routine.seq,Routine.clear,Routine.ofLocal,Local.eval_push,
      LengthTest.routine_eval,require_eval,singletonSlots,one]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
