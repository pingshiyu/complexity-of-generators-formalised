import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

/-! Generic storage and cost bounds for counted finite routines. Every bound
is about an explicit primitive routine and its proved evaluator; no native
machine or compiler is assumed by this interface. -/
namespace ComplexityOfGenerators.Simulation.WordStack.Routine
variable {S O : Type} {k : ℕ}
set_option backward.isDefEq.respectTransparency false

variable (clock : Fin k) (body : Routine S O k) (I : Local.Store S k → Prop)
    (base growth constant : ℕ)
    (pop_preserves : ∀ s, I s → I (Function.update s clock (s clock).tail))
    (body_preserves : ∀ s, I s → I (body.eval s))
    (body_bound : ∀ s budget, base ≤ budget → I s → StoreBound s budget →
      StoreBound (body.eval s) (budget+growth))
    (body_cost : ∀ s budget, base ≤ budget → I s → StoreBound s budget → body.cost s ≤ constant*(budget+1))

include pop_preserves body_preserves body_bound in
/-- A counted prefix grows the store budget by at most one fixed increment
per iteration, and preserves the caller's semantic invariant. -/
theorem counted_iterate_growing_bound (s : Local.Store S k) (budget count : ℕ)
    (large : base ≤ budget) (valid : I s) (sizes : StoreBound s budget) :
    I ((counted clock body).eval^[count] s) ∧
      StoreBound ((counted clock body).eval^[count] s) (budget+count*growth) := by
  induction count with
  | zero => simpa using And.intro valid sizes
  | succ count ih =>
    let current := (counted clock body).eval^[count] s
    let popped := Function.update current clock (current clock).tail
    have poppedValid : I popped := pop_preserves current ih.1
    have poppedBound : StoreBound popped (budget+count*growth) :=
      ih.2.update clock _ (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (ih.2 clock))
    have nextValid := body_preserves popped poppedValid
    have nextBound := body_bound popped (budget+count*growth) (by omega) poppedValid poppedBound
    rw [Function.iterate_succ_apply']
    refine ⟨nextValid, ?_⟩
    convert nextBound using 1 <;> simp [counted, seq, ofLocal, Local.eval_pop, current, popped, Nat.add_mul, Nat.add_assoc]

include pop_preserves body_preserves body_bound in
theorem iterate_growing_bound (frame : body.Fixes clock) (s : Local.Store S k) (budget : ℕ)
    (large : base ≤ budget) (valid : I s) (sizes : StoreBound s budget) :
    I ((iterate clock body frame).eval s) ∧
      StoreBound ((iterate clock body frame).eval s) (budget+(s clock).length*growth) :=
  counted_iterate_growing_bound clock body I base growth pop_preserves body_preserves body_bound s budget (s clock).length large valid sizes

include pop_preserves body_preserves body_bound body_cost in
/-- A single ceiling for the growing intermediate stores gives a cost linear
in the iteration count and in the ceiling, including all loop control. -/
theorem iterate_growing_cost (frame : body.Fixes clock) (s : Local.Store S k) (budget ceiling : ℕ)
    (large : base ≤ budget) (valid : I s) (sizes : StoreBound s budget)
    (fits : budget+(s clock).length*growth ≤ ceiling) :
    (iterate clock body frame).cost s ≤ (s clock).length*(constant+4)*(ceiling+1) := by
  change loopCost (counted clock body).cost (counted clock body).eval (s clock).length s ≤ _
  apply (loopCost_bound _ _ (s clock).length (constant*(ceiling+1)+2) s ?_).trans
  · nlinarith
  · intro i within
    have current := counted_iterate_growing_bound clock body I base growth pop_preserves body_preserves body_bound
      s budget i large valid sizes
    have upper : budget+i*growth ≤ ceiling :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt within)) _).trans fits
    let popped := Function.update ((counted clock body).eval^[i] s) clock
      (((counted clock body).eval^[i] s) clock).tail
    have poppedValid : I popped := pop_preserves _ current.1
    have poppedBound : StoreBound popped ceiling :=
      (current.2.mono upper).update clock _ (by
        simp only [List.length_tail]
        exact (Nat.sub_le _ _).trans ((current.2 _).trans upper))
    have cost := body_cost popped ceiling (large.trans (by omega)) poppedValid poppedBound
    change 1+1+body.cost popped ≤ _
    omega

end ComplexityOfGenerators.Simulation.WordStack.Routine
