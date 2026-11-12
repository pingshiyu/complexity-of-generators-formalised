import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Label

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def enabled (n size : ℕ) (word : List Symbol) : Bool :=
  decide (BaseSearch.Productive n) &&
    if word.isEmpty then decide (size=1) else
      decide (encodingLength (size+1) ≤ n) && (decodeLabel (size+1) word).isSome

theorem capacity_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (valid : j ≠ 41) (output : j ≠ 46) (base : j ≠ 47) (temporary : j ≠ 48) (scratch : j ≠ 49) :
    capacity.eval s j = s j := by
  have low (i : Fin 64) (inside : i.val < 32) : j ≠ i := by
    intro equal
    have := congrArg Fin.val equal
    omega
  simp [capacity,Routine.seq,CounterRoutine.routine_eval,Routine.ofLocal,Local.eval_push,
    RationalSelection.Compare.routine_eval,require_eval,counterSlots,capacitySlots,
    Function.update_apply,valid,output,base,temporary,scratch,low]

theorem singleton_frame (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (valid : j ≠ 41) (scratch : j ≠ 49) : singleton.eval s j = s j := by
  have low (i : Fin 64) (inside : i.val < 32) : j ≠ i := by
    intro equal
    have := congrArg Fin.val equal
    omega
  simp [singleton,Routine.seq,Routine.clear,Routine.ofLocal,Local.eval_push,
    LengthTest.routine_eval,require_eval,singletonSlots,Function.update_apply,valid,scratch,low]

def protectedRegisters : Fin 7 → Fin 64 := ![32,33,34,35,36,37,38]

theorem tail_frame (s : Store) (i : Fin 7) :
    (Routine.branch 33 (fun word => if word.isNone then singleton else capacity.seq label)).eval s
        (protectedRegisters i) = s (protectedRegisters i) := by
  simp only [Routine.branch]
  split
  · fin_cases i <;> exact singleton_frame s _ (by decide) (by decide) (by decide)
  · simp only [Routine.seq]
    rw [label_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    fin_cases i <;> exact capacity_frame s _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

structure Result (out : Store) (graph : Graph) (start n : ℕ) (word : List Symbol) : Prop where
  raw : out 32 = graph.encode start
  labelWord : out 33 = word
  index : (out 34).length = n
  childSize : out 35 = List.replicate graph.size (.bit true)
  childStart : out 36 = List.replicate start (.bit true)
  parentSize : out 37 = List.replicate (graph.size+1) (.bit true)
  labelWidth : out 38 = List.replicate (width (graph.size+1)) (.bit true)
  next : word ≠ [] → out 39 = List.replicate (nextValue (graph.size+1) word) (.bit true)
  live : (out 41).head?.isSome = enabled n graph.size word

def resultRegisters : Fin 9 → Fin 64 := ![32,33,34,35,36,37,38,39,41]

theorem Result.of_frame {source out : Store} {graph : Graph} {start n : ℕ} {word : List Symbol}
    (result : Result source graph start n word)
    (frame : ∀ i, out (resultRegisters i)=source (resultRegisters i)) : Result out graph start n word where
  raw := (frame 0).trans result.raw
  labelWord := (frame 1).trans result.labelWord
  index := (congrArg List.length (frame 2)).trans result.index
  childSize := (frame 3).trans result.childSize
  childStart := (frame 4).trans result.childStart
  parentSize := (frame 5).trans result.parentSize
  labelWidth := (frame 6).trans result.labelWidth
  next nonempty := (frame 7).trans (result.next nonempty)
  live := (congrArg (fun value => value.head?.isSome) (frame 8)).trans result.live

theorem routine_graph (s : Store) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (inside : start < graph.size) (target : s 32 = graph.encode start)
    (index : (s 34).length = n) (labelWord : s 33 = word) :
    Result (routine.eval s) graph start n word := by
  let a := parse.eval s
  let b := productive.eval a
  let c := parent.eval b
  let tail := Routine.branch 33 fun word => if word.isNone then singleton else capacity.seq label
  have aSize : a 35 = List.replicate graph.size (.bit true) := by
    have value := (parse_values s).1
    simpa [a,target,headerSize_encode] using value
  have aStart : a 36 = List.replicate start (.bit true) := by
    have value := (parse_values s).2
    simpa [a,target,parsedState_encode graph start inside] using value
  have bSize : b 35 = a 35 := productive_frame a 35 (by decide) (by decide) (by decide)
  have bStart : b 36 = a 36 := productive_frame a 36 (by decide) (by decide) (by decide)
  have cSize : c 35 = a 35 := (parent_frame b 35 (by decide) (by decide) (by decide) (by decide)).trans bSize
  have cStart : c 36 = a 36 := (parent_frame b 36 (by decide) (by decide) (by decide) (by decide)).trans bStart
  have cParent : c 37 = List.replicate (graph.size+1) (.bit true) := by
    have value := (parent_values b).1
    simpa only [bSize,aSize,List.length_replicate] using value
  have cWidth : c 38 = List.replicate (width (graph.size+1)) (.bit true) := by
    have value := (parent_values b).2
    simpa only [bSize,aSize,List.length_replicate,width] using value
  have prefixFrame (j : Fin 3) : c (![32,33,34] j) = s (![32,33,34] j) := by
    dsimp only [c,b,a]
    rw [parent_frame _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)
        (by fin_cases j <;> decide) (by fin_cases j <;> decide),
      productive_frame _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide),
      parse_frame _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)
        (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
  have cLabel : c 33 = word := (prefixFrame 1).trans labelWord
  have cIndex : (c 34).length = n := (congrArg List.length (prefixFrame 2)).trans index
  have cLive : (c 41).head?.isSome = decide (BaseSearch.Productive n) := by
    rw [show c 41 = b 41 from parent_frame b 41 (by decide) (by decide) (by decide) (by decide),productive_value]
    have same : (a 34).length = n := by
      dsimp only [a]
      rw [parse_frame s 34 (by decide) (by decide) (by decide) (by decide)]
      exact index
    rw [same]
  change Result (tail.eval c) graph start n word
  constructor
  · exact (tail_frame c 0).trans ((prefixFrame 0).trans target)
  · exact (tail_frame c 1).trans cLabel
  · exact (congrArg List.length (tail_frame c 2)).trans cIndex
  · exact (tail_frame c 3).trans (cSize.trans aSize)
  · exact (tail_frame c 4).trans (cStart.trans aStart)
  · exact (tail_frame c 5).trans cParent
  · exact (tail_frame c 6).trans cWidth
  · intro nonempty
    have present : (c 33).head?.isNone = false := by cases word <;> simp_all
    change (if (c 33).head?.isNone then singleton else capacity.seq label).eval c 39 = _
    rw [present]
    simp only [Bool.false_eq_true,ite_false,Routine.seq]
    have sizeFrame := capacity_frame c 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have widthFrame := capacity_frame c 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have wordFrame := capacity_frame c 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have widths : ((capacity.eval c) 38).length = width ((capacity.eval c) 37).length := by rw [sizeFrame,widthFrame,cParent,cWidth]; simp
    rw [(label_values (capacity.eval c) widths).1,sizeFrame,wordFrame,cParent,cLabel]
    simp
  · by_cases empty : word = []
    · have absent : (c 33).head?.isNone = true := by simp [cLabel,empty]
      change ((if (c 33).head?.isNone then singleton else capacity.seq label).eval c 41).head?.isSome = _
      rw [absent]
      simp only [ite_true,singleton_flag,cSize,aSize,List.length_replicate]
      cases one : decide (graph.size=1) <;> simp_all [enabled]
    · have present : (c 33).head?.isNone = false := by cases word <;> simp_all
      change ((if (c 33).head?.isNone then singleton else capacity.seq label).eval c 41).head?.isSome = _
      rw [present]
      simp only [Bool.false_eq_true,ite_false,Routine.seq]
      have sizeFrame := capacity_frame c 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have widthFrame := capacity_frame c 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have wordFrame := capacity_frame c 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have widths : ((capacity.eval c) 38).length = width ((capacity.eval c) 37).length := by rw [sizeFrame,widthFrame,cParent,cWidth]; simp
      rw [(label_values (capacity.eval c) widths).2,sizeFrame,wordFrame,cParent,cLabel]
      simp only [List.length_replicate,candidate_self_valid,capacity_flag,cParent,cIndex,List.length_replicate]
      by_cases fits : encodingLength (graph.size+1) ≤ n <;>
        cases decoded : (decodeLabel (graph.size+1) word).isSome <;>
        simp_all [enabled,List.isEmpty_iff]
      split_ifs <;> simp_all <;> omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
