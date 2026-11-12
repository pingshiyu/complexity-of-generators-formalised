import ComplexityOfGenerators.Simulation.PaperFilteredInverse.BoundsWidth
import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Eval

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

theorem checks_bound (q : PolynomialBound) (s : Store M W) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length=n) (base : n+1≤cap) (width : q n+1≤cap)
    (word : List α) (candidate : s 25=letters M W word) :
    StoreBound ((checks M W q).eval s) (7*cap+1) ∧
      (checks M W q).cost s≤(widthBodyConstant M W+1000)*(cap+1)+Command.counterBudget q n := by
  let a := (atMost M W).eval s
  let tail : Controller M W := WordStack.Routine.branch 26 fun accepted=>if accepted.isSome then
    WordStack.Routine.branch 27 (fun short=>if short.isSome then widthCheck M W q else flag M W 28 false)
    else flag M W 28 false
  obtain ⟨aBound,aCost⟩ := atMost_bound M W s cap sizes (by omega)
  have aIndex : (a 13).length=n := by simp [a,atMost_eval,index]
  have aCandidate : a 25=letters M W word := by simp [a,atMost_eval,candidate]
  obtain ⟨widthBound,widthCost⟩ := widthCheck_bound M W q a n cap aBound aIndex base width word aCandidate
  obtain ⟨flagBound,flagCost⟩ := flag_bound M W 28 false a cap aBound (by omega)
  have tailBound : StoreBound (tail.eval a) (7*cap+1) ∧
      tail.cost a≤(widthBodyConstant M W+900)*(cap+1)+Command.counterBudget q n+2 := by
    cases h26 : (a 26).head? with
    | none=>
        simp only [tail,WordStack.Routine.branch,h26,Option.isSome_none,Bool.false_eq_true,ite_false]
        exact ⟨flagBound.mono (by omega),by nlinarith⟩
    | some accepted=>
        cases h27 : (a 27).head? with
        | none=>
            simp only [tail,WordStack.Routine.branch,h26,h27,Option.isSome_some,Option.isSome_none,
              Bool.true_eq,ite_true,Bool.false_eq_true,ite_false]
            exact ⟨flagBound.mono (by omega),by nlinarith⟩
        | some short=>
            simp only [tail,WordStack.Routine.branch,h26,h27,Option.isSome_some,Bool.true_eq,ite_true]
            exact ⟨widthBound,by omega⟩
  constructor
  · exact tailBound.1
  · change (atMost M W).cost s+1+tail.cost a≤_
    have tailCost:=tailBound.2
    nlinarith

theorem checks_candidate_frame (q : PolynomialBound) (s : Store M W) :
    (checks M W q).eval s 25=s 25 := by
  let a := (atMost M W).eval s
  change (WordStack.Routine.branch 26 (fun accepted=>if accepted.isSome then
    WordStack.Routine.branch 27 (fun short=>if short.isSome then widthCheck M W q else flag M W 28 false)
    else flag M W 28 false)).eval a 25=s 25
  cases h26 : (a 26).head? with
  | none=>
      simp only [WordStack.Routine.branch,h26,Option.isSome_none,Bool.false_eq_true,ite_false]
      simp [flag_eval,a,atMost_eval]
  | some accepted=>
      cases h27 : (a 27).head? with
      | none=>
          simp only [WordStack.Routine.branch,h26,h27,Option.isSome_some,Option.isSome_none,ite_true,Bool.false_eq_true,ite_false]
          simp [flag_eval,a,atMost_eval]
      | some short=>
          simp only [WordStack.Routine.branch,h26,h27,Option.isSome_some,Bool.true_eq,ite_true]
          rw [widthCheck_frame M W q a 25 (Or.inl rfl)]
          simp [a,atMost_eval]

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
