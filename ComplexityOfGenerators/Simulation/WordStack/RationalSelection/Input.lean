import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Bounds

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

def inputStore (denominator numerator : ℕ) (block : List Bool) : Store :=
  Function.update (Function.update (Function.update (fun _ => [])
    0 (List.replicate denominator true)) 1 (List.replicate numerator true)) 2 block

def result (s : Store) : Option Bool :=
  if (s 12).head?.isSome then some (s 13).head?.isSome else none

/-- The finite map whose uniform-block probabilities are a/d, (d-a)/d,
and rejection. Its numerical operations are realized by `selector`. -/
def choose (denominator numerator : ℕ) (block : List Bool) : Option Bool :=
  let value := FixedBitBlocks.decode (block.take (Nat.clog 2 denominator))
  if value < denominator then some (decide (value < numerator)) else none

theorem selector_input_result {O : Type} (denominator numerator : ℕ) (block : List Bool)
    (enough : Nat.clog 2 denominator ≤ block.length) :
    result ((selector (O := O)).eval (inputStore denominator numerator block)) =
      choose denominator numerator block := by
  have spec := selector_spec (O := O) (inputStore denominator numerator block) (by simpa [inputStore] using enough)
  have success := spec.2.1
  have truth := spec.2.2.1
  simp only [inputStore, Function.update_self, Function.update_of_ne (by decide : (0 : Fin 16) ≠ 2),
    Function.update_of_ne (by decide : (0 : Fin 16) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 16) ≠ 2), List.length_replicate] at success truth
  unfold result choose
  simp only [inputStore]
  rw [success, truth]
  split_ifs <;> simp_all

theorem inputStore_sizes (denominator numerator : ℕ) (block : List Bool) (bound : numerator ≤ denominator) :
    ∀ j, (inputStore denominator numerator block j).length ≤ denominator + block.length := by
  intro j
  by_cases d : j = 0 <;> by_cases a : j = 1 <;> by_cases b : j = 2 <;>
    simp [inputStore, d, a, b] <;> omega

theorem selector_input_cost {O : Type} (denominator numerator : ℕ) (block : List Bool)
    (positive : 0 < denominator) (bound : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ block.length) :
    (selector (O := O)).cost (inputStore denominator numerator block) ≤
      20000 * (denominator + block.length + 1) ^ 2 := by
  apply selector_cost _ _ (inputStore_sizes denominator numerator block bound)
  · simpa [inputStore] using positive
  · simpa [inputStore] using enough

theorem selector_input_bound {O : Type} (denominator numerator : ℕ) (block : List Bool)
    (positive : 0 < denominator) (bound : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ block.length) :
    ∀ j, ((selector (O := O)).eval (inputStore denominator numerator block) j).length ≤
      20 * (denominator + block.length + 1) := by
  apply selector_bound _ _ (inputStore_sizes denominator numerator block bound)
  · simpa [inputStore] using positive
  · simpa [inputStore] using enough

theorem choose_encode (denominator numerator value : ℕ)
    (fits : value < 2 ^ Nat.clog 2 denominator) :
    choose denominator numerator (FixedBitBlocks.encode (Nat.clog 2 denominator) value) =
      if value < denominator then some (decide (value < numerator)) else none := by
  have full : (FixedBitBlocks.encode (Nat.clog 2 denominator) value).take (Nat.clog 2 denominator) =
      FixedBitBlocks.encode (Nat.clog 2 denominator) value := by
    exact List.take_of_length_le (by simp)
  simp only [choose, full, FixedBitBlocks.decode_encode _ _ fits]

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
