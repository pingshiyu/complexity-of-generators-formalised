import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Fields
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.ProductiveBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.LogarithmBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
open Simulation.WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] parse productive parent Logarithm.routine

theorem call32_bound (source : Routine Symbol Symbol 32) (s : Store) (initial final : ℕ)
    (sizes : StoreBound s initial) (grows : initial ≤ final)
    (result : StoreBound (source.eval (s ∘ Output.low32)) final) :
    StoreBound ((source.rename Output.low32).eval s) final := by
  intro j
  by_cases inside : j.val < 32
  · let i : Fin 32 := ⟨j.val,inside⟩
    have same : Output.low32 i = j := Fin.ext rfl
    rw [← same,Routine.rename_eval_here]
    exact result i
  · rw [call32_frame _ _ j (by omega)]
    exact (sizes j).trans grows

theorem call16_bound (source : Routine Symbol Symbol 16) (s : Store) (initial final : ℕ)
    (sizes : StoreBound s initial) (grows : initial ≤ final)
    (result : StoreBound (source.eval (s ∘ Output.low16)) final) :
    StoreBound ((source.rename Output.low16).eval s) final := by
  intro j
  by_cases inside : j.val < 16
  · let i : Fin 16 := ⟨j.val,inside⟩
    have same : Output.low16 i = j := Fin.ext rfl
    rw [← same,Routine.rename_eval_here]
    exact result i
  · rw [call16_frame _ _ j (by omega)]
    exact (sizes j).trans grows

theorem assign_cost (source target scratch : Fin 64) (a : source ≠ target) (b : source ≠ scratch) (c : target ≠ scratch)
    (map : Symbol → Symbol) (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (Routine.assign (O := Symbol) source target scratch a b c map).cost s ≤ 20*(budget+1) := by
  have x := sizes source
  have y := sizes target
  have z := sizes scratch
  rw [Routine.assign_cost]
  omega

theorem require_bound (source : Fin 64) (expected : Bool) (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((require source expected).eval s) budget ∧ (require source expected).cost s ≤ 3*budget+1 := by
  constructor
  · rw [require_eval]
    apply sizes.update 41
    split_ifs
    · exact sizes 41
    · simp
  · have size := sizes 41
    simp only [require,Routine.branch]
    split_ifs <;> simp [Routine.skip,Routine.clear,Routine.ofLocal,Local.ticks] <;> omega

theorem parse_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (parse.eval s) (budget+1) ∧ parse.cost s ≤ 600*(budget+2)^2 := by
  let copied := (Routine.assign (O := Symbol) 32 2 48 (by decide) (by decide) (by decide) id).eval s
  let parsed := ((Native.parser (O := Symbol)).rename Output.low32).eval copied
  let counted := (Routine.assign (O := Symbol) 4 35 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval parsed
  have copiedSize : StoreBound copied budget := sizes.assign _ _ _ _ _ _ _
  have copiedCost := assign_cost 32 2 48 (by decide) (by decide) (by decide) id s budget sizes
  have lowSize : StoreBound (copied ∘ Output.low32) budget := fun j => copiedSize _
  have parsedSize : StoreBound parsed (budget+1) := call32_bound _ copied budget (budget+1) copiedSize (by omega)
    (Native.parser_bound (O := Symbol) _ budget lowSize)
  have parsedCost : ((Native.parser (O := Symbol)).rename Output.low32).cost copied ≤ 500*(budget+1)^2 := by
    simpa only [Routine.rename_cost] using Native.parser_cost (O := Symbol) (copied ∘ Output.low32) budget lowSize
  have countedSize : StoreBound counted (budget+1) := parsedSize.assign _ _ _ _ _ _ _
  have countedCost := assign_cost 4 35 48 (by decide) (by decide) (by decide) (fun _ => .bit true) parsed (budget+1) parsedSize
  have finalCost := assign_cost 13 36 48 (by decide) (by decide) (by decide) (fun _ => .bit true) counted (budget+1) countedSize
  constructor
  · unfold parse
    exact countedSize.assign 13 36 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)
  · unfold parse
    change (Routine.assign (O := Symbol) 32 2 48 _ _ _ id).cost s+1+
      (((Native.parser (O := Symbol)).rename Output.low32).cost copied+1+
        ((Routine.assign (O := Symbol) 4 35 48 _ _ _ (fun _ => .bit true)).cost parsed+1+
          (Routine.assign (O := Symbol) 13 36 48 _ _ _ (fun _ => .bit true)).cost counted)) ≤ _
    nlinarith

theorem productive_bound (s : Store) (budget n : ℕ) (sizes : StoreBound s budget) (index : (s 34).length = n) :
    StoreBound (productive.eval s) (max budget (BaseSearch.storeBudget n)) ∧
      productive.cost s ≤ 200*(max budget (BaseSearch.storeBudget n)+1)+n*(BaseSearch.bodyBudget n+4) := by
  let copied := (Routine.assign (O := Symbol) 34 12 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval s
  let tested := (Productive.routine.rename Output.low16).eval copied
  let bound := max budget (BaseSearch.storeBudget n)
  have copiedSize : StoreBound copied budget := sizes.assign _ _ _ _ _ _ _
  have copiedCost := assign_cost 34 12 48 (by decide) (by decide) (by decide) (fun _ => .bit true) s budget sizes
  have lowSize : StoreBound (copied ∘ Output.low16) budget := fun j => copiedSize _
  have input : ((copied ∘ Output.low16) 12).length = n := by
    change (copied 12).length = n
    simp [copied,Routine.assign_eval,index]
  have native := Productive.routine_bound (copied ∘ Output.low16) budget lowSize
  rw [input] at native
  have testedSize : StoreBound tested bound := call16_bound _ copied budget bound copiedSize (le_max_left _ _) native.1
  have testedCost : (Productive.routine.rename Output.low16).cost copied ≤
      120*(budget+1)+1+n*(BaseSearch.bodyBudget n+4) := by
    simpa only [Routine.rename_cost] using native.2
  have copiedResultCost := assign_cost 11 41 48 (by decide) (by decide) (by decide) (fun _ => .bit true) tested bound testedSize
  constructor
  · unfold productive
    exact testedSize.assign 11 41 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)
  · unfold productive
    change (Routine.assign (O := Symbol) 34 12 48 _ _ _ (fun _ => .bit true)).cost s+1+
      ((Productive.routine.rename Output.low16).cost copied+1+
        (Routine.assign (O := Symbol) 11 41 48 _ _ _ (fun _ => .bit true)).cost tested) ≤ _
    have grows : budget ≤ bound := le_max_left _ _
    change _ ≤ 200*(bound+1)+_ 
    omega

theorem parent_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (parent.eval s) (4*(budget+2)) ∧ parent.cost s ≤ 2000*(4*(budget+2)+1)^2 := by
  let copied := (Routine.assign (O := Symbol) 35 17 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval s
  let pushed := Function.update copied 17 (Symbol.bit true::copied 17)
  let logarithm := ((Logarithm.routine (O := Symbol)).rename Output.low32).eval pushed
  let counted := (Routine.assign (O := Symbol) 17 37 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval logarithm
  have copiedSize : StoreBound copied budget := sizes.assign _ _ _ _ _ _ _
  have copiedCost := assign_cost 35 17 48 (by decide) (by decide) (by decide) (fun _ => .bit true) s budget sizes
  have pushedSize : StoreBound pushed (budget+1) := (copiedSize.mono (by omega)).update 17 _ (by have := copiedSize 17; simp only [List.length_cons]; omega)
  have lowSize : StoreBound (pushed ∘ Output.low32) (budget+1) := fun j => pushedSize _
  have native := Logarithm.routine_bound (O := Symbol) (pushed ∘ Output.low32) (budget+1) lowSize
  have logarithmSize : StoreBound logarithm (4*(budget+2)) := call32_bound _ pushed (budget+1) _ pushedSize (by omega) native.1
  have logarithmCost : ((Logarithm.routine (O := Symbol)).rename Output.low32).cost pushed ≤ 1000*(budget+2)^2 := by
    simpa only [Routine.rename_cost,Nat.add_assoc] using native.2
  have countedSize : StoreBound counted (4*(budget+2)) := logarithmSize.assign _ _ _ _ _ _ _
  have countedCost := assign_cost 17 37 48 (by decide) (by decide) (by decide) (fun _ => .bit true) logarithm (4*(budget+2)) logarithmSize
  have finalCost := assign_cost 19 38 48 (by decide) (by decide) (by decide) (fun _ => .bit true) counted (4*(budget+2)) countedSize
  constructor
  · unfold parent
    exact countedSize.assign 19 38 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)
  · unfold parent
    change (Routine.assign (O := Symbol) 35 17 48 _ _ _ (fun _ => .bit true)).cost s+1+
      (1+1+(((Logarithm.routine (O := Symbol)).rename Output.low32).cost pushed+1+
        ((Routine.assign (O := Symbol) 17 37 48 _ _ _ (fun _ => .bit true)).cost logarithm+1+
          (Routine.assign (O := Symbol) 19 38 48 _ _ _ (fun _ => .bit true)).cost counted))) ≤ _
    nlinarith

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
