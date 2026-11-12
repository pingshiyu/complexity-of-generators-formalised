import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Components
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Views

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem reset_eval (s : Store G) :
    (reset G).eval s = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update s 11 []) 12 []) 14 []) 25 []) 26 []) 27 []) 28 []) 31 []) 32 [] := by
  simp [reset, WordStack.Routine.seq, WordStack.Routine.clear, UnionGenerator.flag_eval, UnionGenerator.flagWord]

theorem calls_stored (seed time : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store G)
    (index : (s 13).length = n) (random : s 17 = bits.map Symbol.bit) :
    UnionGenerator.Stored G G n (bits.drop (2 * seed n))
      (UnionGenerator.sourceValue G time n (bits.take (seed n)))
      (UnionGenerator.sourceValue G time n ((bits.drop (seed n)).take (seed n)))
      ((calls G seed time).eval s) := by
  let r := (reset G).eval s
  have initial : UnionGenerator.Stored G G n bits none none r := by
    constructor <;> simp [r, reset_eval, index, random, UnionGenerator.held, UnionGenerator.flagWord]
  have left := UnionGenerator.leftStep_stored G G seed time n bits none none r initial
  have right := UnionGenerator.rightStep_stored G G seed time n (bits.drop (seed n))
    (UnionGenerator.sourceValue G time n (bits.take (seed n))) none _ left
  simpa only [calls, WordStack.Routine.seq, List.drop_drop, two_mul] using right

theorem calls_outer (seed time : PolynomialBound) (s : Store G) (q : Fin 35)
    (allowed : q = 22 ∨ q = 31 ∨ q = 32) :
    (calls G seed time).eval s q = if q = 22 then s q else [] := by
  let r := (reset G).eval s
  let a := (UnionGenerator.leftFinish G G).eval ((UnionGenerator.leftTrial G G seed time).eval r)
  have large : 22 ≤ q.val := by rcases allowed with rfl | rfl | rfl <;> decide
  have left := ConcatenationGenerator.leftStep_frame G G seed time r q large
    (by rcases allowed with rfl | rfl | rfl <;> decide)
    (by rcases allowed with rfl | rfl | rfl <;> decide)
  have right := ConcatenationGenerator.rightStep_frame G G seed time a q large
    (by rcases allowed with rfl | rfl | rfl <;> decide)
    (by rcases allowed with rfl | rfl | rfl <;> decide)
  change (UnionGenerator.rightFinish G G).eval ((UnionGenerator.rightTrial G G seed time).eval a) q = _
  exact right.trans (left.trans (by
    rcases allowed with rfl | rfl | rfl <;> simp [r, reset_eval]))

theorem calls_fixes22 (seed time : PolynomialBound) : (calls G seed time).Fixes 22 := by
  intro s
  simpa using calls_outer G seed time s 22 (Or.inl rfl)

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
