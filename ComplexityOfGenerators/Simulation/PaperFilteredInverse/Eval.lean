import ComplexityOfGenerators.Simulation.PaperFilteredInverse.EvalBasic
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

theorem firstCall_frame (seed time : PolynomialBound) (s : Store M W) (j : Fin 35)
    (keep : j=11 ∨ j=12 ∨ j=13 ∨ j=25) : (firstCall M W seed time).eval s j=s j := by
  have frame (j : Fin 35) (out : 11≤j.val) (clock : j≠16) :=
    BoundedSource.sourceTrial_outside (O := α) (Symbol.unit : Cell M W) Symbol.bit M
      Symbol.inverse (inverseDecode M W) (inverseInput M W) (inverseAuxiliary M W) (inverseBit M W)
      seed time s j out clock
  have outside : 11≤j.val := by rcases keep with rfl|rfl|rfl|rfl <;> decide
  have notClock : j≠16 := by rcases keep with rfl|rfl|rfl|rfl <;> decide
  have h := frame j outside notClock
  dsimp only [firstCall]
  rw [h]
  rcases keep with rfl|rfl|rfl|rfl <;>
    norm_num [BoundedSource.trialPrepared,Function.update_apply]

theorem width_run (q : PolynomialBound) (width : List α→ℕ)
    (correct : ∀ x,W.Produces {input:=x} [] (List.replicate (width x) ()))
    (bounded : ∀ x,W.TimeBound {input:=x} (q x.length))
    (n : ℕ) (x : List α) (small : x.length≤n) :
    W.run {input:=x} [] (q n)=.halted (.accepted (List.replicate (width x) ())) := by
  exact W.produces_at_bound _ [] _ _
    (W.haltsWithin_mono _ [] (q.monotone small) (bounded x [])) (correct x)

theorem checks_fields (q : PolynomialBound) (width : List α→ℕ)
    (correct : ∀ x,W.Produces {input:=x} [] (List.replicate (width x) ()))
    (bounded : ∀ x,W.TimeBound {input:=x} (q x.length))
    (s : Store M W) (x : List α) (n label : ℕ)
    (candidate : s 25=letters M W x) (index : (s 13).length=n) (labelLength : (s 23).length=label) :
    let result := (checks M W q).eval s
    result 25=letters M W x ∧
      (result 26).head?.isSome=(s 26).head?.isSome ∧
      (result 27).head?.isSome=decide (x.length≤n) ∧
      (result 28).head?.isSome=
        (if (s 26).head?.isSome then decide (x.length≤n ∧ label=width x) else false) := by
  let a := (atMost M W).eval s
  have a25 : a 25=letters M W x := by simp [a,atMost_eval,candidate]
  have a26 : a 26=s 26 := by simp [a,atMost_eval]
  have a13 : (a 13).length=n := by simp [a,atMost_eval,index]
  have a23 : (a 23).length=label := by simp [a,atMost_eval,labelLength]
  have a27 : a 27=if x.length≤n then [Symbol.unit] else [] := by simp [a,atMost_eval,candidate,index]
  let result := (WordStack.Routine.branch 26 fun accepted=>if accepted.isSome then
    WordStack.Routine.branch 27 fun short=>if short.isSome then widthCheck M W q else flag M W 28 false
    else flag M W 28 false).eval a
  change result 25=letters M W x ∧
      (result 26).head?.isSome=(s 26).head?.isSome ∧
      (result 27).head?.isSome=decide (x.length≤n) ∧
      (result 28).head?.isSome=
        (if (s 26).head?.isSome then decide (x.length≤n ∧ label=width x) else false)
  by_cases active : (s 26).head?.isSome=true
  · by_cases small : x.length≤n
    · have run := width_run W q width correct bounded n x small
      have flagWidth := widthCheck_flag M W q a x (List.replicate (width x) ()) a25 (by simpa [a13] using run)
      have c25 := widthCheck_frame M W q a 25 (Or.inl rfl)
      have c26 := widthCheck_frame M W q a 26 (Or.inr (Or.inl rfl))
      have c27 := widthCheck_frame M W q a 27 (Or.inr (Or.inr rfl))
      have result_eq : result=(widthCheck M W q).eval a := by
        simp only [result,WordStack.Routine.branch,a26,active,ite_true,a27,if_pos small,
          List.head?_cons,Option.isSome_some]
      rw [result_eq]
      refine ⟨c25.trans a25,?_,?_,?_⟩
      · rw [c26,a26]
      · rw [c27,a27]
        simp [small]
      · rw [flagWidth,a23]
        by_cases equal : label=width x <;> simp [active,small,equal,eq_comm]
    · have result_eq : result=Function.update a 28 [] := by
        simp only [result,WordStack.Routine.branch,a26,active,ite_true,a27,if_neg small,
          List.head?_nil,Option.isSome_none,Bool.false_eq_true,ite_false,flag_eval] <;> simp
      rw [result_eq]
      simp [Function.update_apply,a25,a26,a27,active,small]
  · have result_eq : result=Function.update a 28 [] := by
      simp only [result,WordStack.Routine.branch,a26,if_neg active,flag_eval,Bool.false_eq_true,ite_false]
    rw [result_eq]
    by_cases small : x.length≤n <;> simp [Function.update_apply,a25,a26,a27,active,small]

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
