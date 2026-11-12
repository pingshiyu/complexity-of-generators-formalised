import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Basic

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

@[simp] theorem letters_length (word : List α) : (letters M W word).length=word.length := by simp [letters]

@[simp] theorem inverseDecode_encode (cell : Source.Symbol M) : inverseDecode M W (.inverse cell)=cell := rfl
@[simp] theorem widthDecode_encode (cell : Source.Symbol W) : widthDecode M W (.width cell)=cell := rfl

@[simp] theorem inverseInput_letters (word : List α) :
    (letters M W word).map (inverseInput M W)=word.map (fun a=>Symbol.inverse (.input a)) := by simp [letters,inverseInput]

@[simp] theorem inverseAuxiliary_letters (word : List α) :
    (letters M W word).map (inverseAuxiliary M W)=word.map (fun a=>Symbol.inverse (.auxiliary a)) := by simp [letters,inverseAuxiliary]

@[simp] theorem widthInput_letters (word : List α) :
    (letters M W word).map (widthInput M W)=word.map (fun a=>Symbol.width (.input a)) := by simp [letters,widthInput]

@[simp] theorem inverseOutput_map (word : List α) :
    (word.map (fun a=>Symbol.inverse (.output a))).map (inverseOutput M W)=letters M W word := by simp [letters,inverseOutput]

@[simp] theorem decodeOutput_letters (word : List α) :
    (letters M W word).filterMap (decodeOutput M W)=word := by simp [letters,decodeOutput]

theorem atMost_eval (s : Store M W) :
    (atMost M W).eval s=
      Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update s 33 []) 30 []) 29 ((s 25).drop (s 13).length)) 31 [])
        27 (if (s 25).length≤(s 13).length then [Symbol.unit] else []) := by
  have test : ((s 25).drop (s 13).length).head?.isNone=decide ((s 25).length≤(s 13).length) := by
    by_cases short : (s 25).length≤(s 13).length
    · simp [List.drop_eq_nil_iff.mpr short,short]
    · have nonempty : (s 25).drop (s 13).length≠[] := by intro empty;exact short (List.drop_eq_nil_iff.mp empty)
      cases rest : (s 25).drop (s 13).length with
      | nil => exact False.elim (nonempty rest)
      | cons a tail => simp [rest,short]
  simp only [atMost,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clear,
    DrainPair.routine_eval (30 : Fin 35) 29 31 (by decide) (by decide) (by decide),
    WordStack.Routine.branch,flag_eval]
  funext j
  fin_cases j <;> simp [Function.update_apply,test]

theorem sourceFlag_eval (s : Store M W) (status : Source.Status (Fin M.states))
    (state : s 0=[Symbol.inverse (.state status)]) :
    (sourceFlag M W).eval s=Function.update s 26 (if status=.accepted then [Symbol.unit] else []) := by
  cases status <;> simp [sourceFlag,WordStack.Routine.branch,state,flag_eval]

theorem capture_eval (s : Store M W) (status : Source.Status (Fin M.states)) (out : List α)
    (state : s 0=[Symbol.inverse (.state status)])
    (output : s 10=out.map (fun a=>Symbol.inverse (.output a))) (empty : s 25=[]) :
    (capture M W).eval s=
      Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update s 26 (if status=.accepted then [Symbol.unit] else [])) 33 [])
        23 (List.replicate (s 12).length Symbol.unit)) 10 []) 25 (letters M W out.reverse) := by
  simp only [capture,WordStack.Routine.seq,sourceFlag_eval M W s status state,
    WordStack.Routine.assign_eval,WordStack.Routine.transfer]
  funext j
  fin_cases j <;> simp [Function.update_apply,empty,output,letters,inverseOutput,List.map_reverse]

theorem widthSetup_eval (q : PolynomialBound) (s : Store M W) :
    (widthSetup M W q).eval s=
      Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update s 33 []) 11 (s 25)) 12 []) 21 [])
        19 (List.replicate ((s 13).length+1) Symbol.unit)) 20 [])
        16 (List.replicate (q (s 13).length+1) Symbol.unit)) 13 []) 14 [] := by
  simp only [widthSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,counter,BoundedSource.counter,
    CounterRoutine.routine_eval,BoundedSource.counterSlots_apply,WordStack.Routine.ofLocal,Local.eval_push,
    WordStack.Routine.clear]
  funext j
  fin_cases j <;> simp [Function.update_apply,List.replicate_succ]

theorem widthCall_output (s : Store M W) (word : List α) (ticks : ℕ)
    (input : s 11=letters M W word) (aux : s 12=[]) (index : s 13=[])
    (random : s 14=[]) (clock : (s 16).length=ticks+1)
    (value : List Unit) (accepted : W.run {input:=word} [] ticks=.halted (.accepted value)) :
    (widthCall M W).eval s 10=value.reverse.map (fun a=>Symbol.width (.output a)) := by
  have projection := Source.call_bank (Output := α) W BoundedSource.sourceSlots Symbol.width (widthDecode M W)
    (widthDecode_encode M W) (widthInput M W) (fun _=>.width .unit) (fun _=>.width (.bit false))
    s ({input:=word} : InputData α Unit) []
    (by simpa [input] using widthInput_letters M W word)
    (by simp [aux]) (by simp [index]) (by simp [random])
  have out := congrFun projection (10 : Fin 11)
  obtain ⟨state,output⟩ := Source.iterate_accept W ({input:=word} : InputData α Unit) [] ticks value accepted
  change ((Source.Snapshot.step W)^[ticks+1] (Source.initial W {input:=word} [])).output=value.reverse at output
  change (widthCall M W).eval s 10=
    (((Source.Snapshot.step W)^[(s 16).length]
      (Source.initial W {input:=word} [])).output.map Source.Cell.output).map Symbol.width at out
  rw [clock,output] at out
  simpa only [List.map_map,Function.comp_def] using out

theorem widthCall_frame (s : Store M W) (j : Fin 35) (outside : 11≤j.val) (clock : j≠16) :
    (widthCall M W).eval s j=if j=14 ∨ j=15 then [] else s j := by
  apply Source.call_frame
  · intro i eq
    have same := congrArg Fin.val eq
    change j.val=i.val at same
    omega
  · exact clock

theorem widthCheck_flag (q : PolynomialBound) (s : Store M W) (word : List α) (value : List Unit)
    (candidate : s 25=letters M W word)
    (accepted : W.run {input:=word} [] (q (s 13).length)=.halted (.accepted value)) :
    (widthCheck M W q).eval s 28=
      if value.length=(s 23).length then [Symbol.unit] else [] := by
  let prepared := (widthSetup M W q).eval s
  have output := widthCall_output M W prepared word (q (s 13).length)
    (by simp [prepared,widthSetup_eval,candidate])
    (by simp [prepared,widthSetup_eval]) (by simp [prepared,widthSetup_eval])
    (by simp [prepared,widthSetup_eval]) (by simp [prepared,widthSetup_eval]) value accepted
  have label := widthCall_frame M W prepared 23 (by decide) (by decide)
  simp only [widthCheck,WordStack.Routine.seq,LengthTest.routine_eval]
  change (if ((widthCall M W).eval prepared 10).length=((widthCall M W).eval prepared 23).length
    then [Symbol.unit] else [])=_
  rw [output,label]
  simp [prepared,widthSetup_eval]

theorem widthCheck_frame (q : PolynomialBound) (s : Store M W) (j : Fin 35)
    (allowed : j=25 ∨ j=26 ∨ j=27) : (widthCheck M W q).eval s j=s j := by
  rcases allowed with rfl|rfl|rfl <;>
    simp [widthCheck,WordStack.Routine.seq,LengthTest.routine_eval,widthCall_frame,
      widthSetup_eval,equalitySlots]

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
