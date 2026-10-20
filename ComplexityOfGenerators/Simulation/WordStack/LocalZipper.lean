import ComplexityOfGenerators.Simulation.WordStack.Local
import ComplexityOfGenerators.Simulation.WordStack.Zipper

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Zipper

variable {A B : Type}

def map (f : A → B) (z : Zipper A) : Zipper B := ⟨z.left.map f, z.right.map f⟩

@[simp] theorem map_clampedMove (f : A → B) (z : Zipper A) (dir : Move) :
    (z.map f).clampedMove dir = (z.clampedMove dir).map f := by
  cases dir <;> cases z with
  | mk left right => cases left <;> cases right <;> rfl

@[simp] theorem map_workMove (f : A → B) (blank : A) (z : Zipper A) (dir : Move) :
    (z.map f).workMove (f blank) dir = (z.workMove blank dir).map f := by
  cases dir <;> cases z with
  | mk left right => cases left <;> cases right <;> rfl

@[simp] theorem map_write (f : A → B) (a : A) (z : Zipper A) :
    (z.map f).write (f a) = (z.write a).map f := by
  cases z with | mk left right => cases right <;> rfl

end Zipper

namespace Local

variable {S : Type} {k : ℕ}

theorem eval_moveRead (left right : Fin k) (different : left ≠ right) (dir : Move) (s : Store S k) :
    let z : Zipper S := ⟨s left, s right⟩
    (moveRead left right dir).eval s =
      Function.update (Function.update s left (z.clampedMove dir).left) right (z.clampedMove dir).right := by
  cases dir <;> cases hl : s left <;> cases hr : s right <;>
    funext j <;> by_cases hjl : j = left <;> by_cases hjr : j = right <;>
      simp_all [eval, moveRead, moveOne, Zipper.clampedMove, push, pop, Action.apply, Function.update_apply]

theorem eval_moveWork (left right : Fin k) (different : left ≠ right) (blank : S) (dir : Move) (s : Store S k) :
    let z : Zipper S := ⟨s left, s right⟩
    (moveWork left right blank dir).eval s =
      Function.update (Function.update s left (z.workMove blank dir).left) right (z.workMove blank dir).right := by
  cases dir <;> cases hl : s left <;> cases hr : s right <;>
    funext j <;> by_cases hjl : j = left <;> by_cases hjr : j = right <;>
      simp_all [eval, moveWork, moveOne, Zipper.workMove, push, pop, Action.apply, Function.update_apply]

end Local
end ComplexityOfGenerators.Simulation.WordStack
