import ComplexityOfGenerators.Simulation.PaperFilteredInverse.BoundsBasic

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

theorem widthSetup_bound (q : PolynomialBound) (s : Store M W) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length=n) (base : n+1≤cap) (width : q n+1≤cap) :
    StoreBound ((widthSetup M W q).eval s) cap ∧
      (widthSetup M W q).cost s≤70*(cap+1)+Command.counterBudget q n := by
  constructor
  · rw [widthSetup_eval]
    have input:=sizes 25
    apply (((((((((sizes.clear 33).update 11 _ input).clear 12).clear 21).update 19 _ ?_).clear 20).update 16 _ ?_).clear 13).clear 14)
    · simpa [index] using base
    · simpa [index] using width
  · let a := (WordStack.Routine.assign (O:=α) 25 11 33 (by decide) (by decide) (by decide) id).eval s
    let b := Function.update a 12 []
    let c := (counter M W 16 (by decide) q).eval b
    let d := Function.update c 16 (Symbol.unit::c 16)
    let e := Function.update d 13 []
    have aBound : StoreBound a cap := sizes.assign (O:=α) 25 11 33 (by decide) (by decide) (by decide) id
    have bBound : StoreBound b cap := aBound.clear 12
    have bIndex : (b 13).length=n := by simp [b,a,WordStack.Routine.assign_eval,index]
    obtain ⟨cBound,cCost⟩ := BoundedSource.counter_bound (O:=α) (Symbol.unit : Cell M W) Symbol.bit
      16 (by decide) q b n cap bBound bIndex base (by omega)
    have cClock : (c 16).length=q n := by simp [c,counter,BoundedSource.counter,CounterRoutine.routine_eval,bIndex]
    have dBound : StoreBound d cap := cBound.update 16 _ (by simpa [cClock] using width)
    have eBound : StoreBound e cap := dBound.clear 13
    have aCost := assign_cost_bound M W 25 11 33 (by decide) (by decide) (by decide) id s cap sizes
    have aux:=aBound 12
    have idx:=dBound 13
    have random:=eBound 14
    change (counter M W 16 (by decide) q).cost b≤_ at cCost
    change (WordStack.Routine.assign (O:=α) 25 11 33 (by decide) (by decide) (by decide) id).cost s+1+
      (3*(a 12).length+1+((counter M W 16 (by decide) q).cost b+1+
      (1+1+(3*(d 13).length+1+3*(e 14).length))))≤_
    omega

def widthBodyConstant : ℕ := (Source.body W Symbol.width (widthDecode M W) (Source.bank BoundedSource.sourceSlots)).bound

theorem widthCheck_bound (q : PolynomialBound) (s : Store M W) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length=n) (base : n+1≤cap) (width : q n+1≤cap)
    (word : List α) (candidate : s 25=letters M W word) :
    StoreBound ((widthCheck M W q).eval s) (7*cap+1) ∧
      (widthCheck M W q).cost s≤(widthBodyConstant M W+900)*(cap+1)+Command.counterBudget q n := by
  let a := (widthSetup M W q).eval s
  let b := (widthCall M W).eval a
  obtain ⟨aBound,aCost⟩ := widthSetup_bound M W q s n cap sizes index base width
  have input : (a (BoundedSource.sourceSlots 11)).map (widthInput M W)=
      word.map (fun a=>Symbol.width (.input a)) := by
    simp [a,widthSetup_eval,candidate,widthInput,letters]
  have auxiliary : (a (BoundedSource.sourceSlots 12)).map (fun _ : Cell M W=>(Symbol.width Source.Cell.unit : Cell M W))=
      ([] : List Unit).map (fun a=>(Symbol.width (.auxiliary a) : Cell M W)) := by simp [a,widthSetup_eval]
  have idx : (a (BoundedSource.sourceSlots 13)).length=0 := by simp [a,widthSetup_eval]
  have random : (a (BoundedSource.sourceSlots 14)).reverse.map (fun _ : Cell M W=>(Symbol.width (.bit false) : Cell M W))=
      ([] : BitString).map (fun b=>(Symbol.width (.bit b) : Cell M W)) := by simp [a,widthSetup_eval]
  have bBound : StoreBound b (7*cap+1) := by
    intro j
    exact Source.call_size (Output:=α) W BoundedSource.sourceSlots Symbol.width (widthDecode M W)
      (widthDecode_encode M W) (widthInput M W) (fun _=>.width .unit) (fun _=>.width (.bit false))
      a ({input:=word} : InputData α Unit) [] input auxiliary idx random cap aBound j
  have checked := bBound.lengthTest (O:=α) equalitySlots Symbol.unit (by omega)
  constructor
  · exact checked
  · have callCost := Source.call_cost (Output:=α) W BoundedSource.sourceSlots Symbol.width (widthDecode M W)
      (widthInput M W) (fun _=>.width .unit) (fun _=>.width (.bit false)) a cap aBound
    change (widthCall M W).cost a≤(widthBodyConstant M W+105)*(cap+1) at callCost
    have checkCost := LengthTest.routine_cost (O:=α) equalitySlots (Symbol.unit : Cell M W) b (7*cap+1) bBound
    change (widthSetup M W q).cost s+1+((widthCall M W).cost a+1+
      (LengthTest.routine (O:=α) equalitySlots (Symbol.unit : Cell M W)).cost b)≤_
    nlinarith

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
