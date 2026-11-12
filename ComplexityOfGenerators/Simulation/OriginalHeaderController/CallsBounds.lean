import ComplexityOfGenerators.Simulation.OriginalHeaderController.Views
import ComplexityOfGenerators.Simulation.WordStack.TransferWhileBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool)

theorem parse_bound (tag : Bool) (s : Store selector) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((parse selector tag).eval s) cap ∧ (parse selector tag).cost s≤10*cap+5 := by
  let clear := (Routine.clear (O:=Event) (23 : Fin 35)).eval s
  let transfer := Routine.transferWhile (O:=Event) (31 : Fin 35) 23 (by decide)
    (fun cell => headerBit selector cell==some tag) (fun _=>unitSymbol selector)
  have cleared : StoreBound clear cap := sizes.clear 23
  have moved := cleared.transferWhile (O:=Event) 31 23 (by decide)
    (fun cell => headerBit selector cell==some tag) (fun _=>unitSymbol selector) (by simp [clear,Routine.clear])
  constructor
  · change StoreBound ((Routine.ofLocal (O:=Event) (Local.pop 23)).eval (transfer.eval clear)) cap
    change StoreBound (Function.update (transfer.eval clear) 23 ((transfer.eval clear 23).tail)) cap
    exact moved.update 23 _ ((List.tail_sublist _).length_le.trans (moved 23))
  · have copyCost := Routine.transferWhile_cost (O:=Event) 31 23 (by decide)
      (fun cell => headerBit selector cell==some tag) (fun _=>unitSymbol selector) cleared
    have clearedSize := sizes 23
    change 3*(s 23).length+1+(transfer.cost clear+1+1)≤_
    change transfer.cost clear≤6*cap at copyCost
    omega

theorem assign_index_bound (map : Cell selector → Cell selector) (s : Store selector) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((Routine.assign (O:=Event) 13 23 33 (by decide) (by decide) (by decide) map).eval s) cap ∧
      (Routine.assign (O:=Event) 13 23 33 (by decide) (by decide) (by decide) map).cost s≤20*cap+3 := by
  refine ⟨sizes.assign 13 23 33 (by decide) (by decide) (by decide) map,?_⟩
  have a:=sizes 13
  have b:=sizes 23
  have c:=sizes 33
  rw [Routine.assign_cost]
  omega

theorem afterEvent_bound (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35)
    (cap : ℕ) (sizes : StoreBound m.store cap)
    (parameter : m.store 23=List.replicate index (unitSymbol selector)) :
    StoreBound (afterEvent selector tag index m).store cap := by
  change StoreBound (Function.update m.store 23 (List.replicate (index-1) (unitSymbol selector))) cap
  apply sizes.update 23
  simp only [List.length_replicate]
  have bound := sizes 23
  rw [parameter,List.length_replicate] at bound
  omega

@[simp] theorem event_randomFree (tag zero : Bool) : (event selector tag zero).RandomFree := .act _ _ _ _
@[simp] theorem emitIndex_randomFree (tag : Bool) : (emitIndex selector tag).RandomFree := by
  unfold emitIndex
  apply Command.RandomFree.branch
  intro observation
  split <;> simp
@[simp] theorem parse_randomFree (tag : Bool) : (parse selector tag).command.RandomFree := by simp [parse]
@[simp] theorem unionCalls_randomFree : (unionCalls selector).RandomFree := by simp [unionCalls]
@[simp] theorem factorCall_randomFree (tag : Bool) : (factorCall selector tag).RandomFree := by simp [factorCall]
@[simp] theorem calls_randomFree (operation : Operation) : (calls selector operation).RandomFree := by
  cases operation <;> simp [calls]

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
