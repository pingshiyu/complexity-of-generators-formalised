import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Tests

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem weighted_value (low high : Fin 35) (lowSafe : PreparedRationalSelection.Safe low)
    (highSafe : PreparedRationalSelection.Safe high) (lowDifferent : low ≠ 31 ∧ low ≠ 33)
    (highDifferent : high ≠ 31 ∧ high ≠ 33) (lower upper : List α) (i : ℕ) (bits : BitString) (s : Store G)
    (lowWord : s low = UnionGenerator.letters G G lower)
    (highWord : s high = UnionGenerator.letters G G upper) (target : (s 22).length = i)
    (random : s 17 = bits.map Symbol.bit) (empty : s 31 = []) (failed : s 32 = [])
    (enough : Nat.clog 2 (upper.length - lower.length) ≤ bits.length) :
    Chosen G ((RationalSelection.choose (upper.length - lower.length) (upper.length - i) bits).map
        (fun choice => if choice then lower else upper))
      (((select G low high lowSafe highSafe).seq
        (selectionFinish G low high lowDifferent highDifferent)).eval s) := by
  let t := (select G low high lowSafe highSafe).eval s
  have frame (j : Fin 35) (large : 16 ≤ j.val) (scratch : j ≠ 33) : t j = s j :=
    PreparedRationalSelection.routine_frame (O := α) Symbol.bit (decodeBit G) (fun _ => rfl)
      low high lowSafe highSafe s j large scratch
  have native := PreparedRationalSelection.result_eq_choose (O := α) Symbol.bit (decodeBit G) (fun _ => rfl)
    low high lowSafe highSafe s (by simpa [lowWord, highWord, random, UnionGenerator.letters] using enough)
  have choice : PreparedRationalSelection.result t =
      RationalSelection.choose (upper.length - lower.length) (upper.length - i) bits := by
    simpa [t, select, lowWord, highWord, target, random, UnionGenerator.letters,
      List.map_map, Function.comp_def, decodeBit] using native
  have answer := selectionFinish_value G low high lowDifferent highDifferent lower upper t
    ((frame low lowSafe.1 lowSafe.2).trans lowWord)
    ((frame high highSafe.1 highSafe.2).trans highWord)
    ((frame 31 (by decide) (by decide)).trans empty)
    ((frame 32 (by decide) (by decide)).trans failed)
  rw [choice] at answer
  exact answer

theorem weightedLeft_value (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s)
    (enough : Nat.clog 2 (right.length - left.length) ≤ bits.length) :
    Chosen G ((RationalSelection.choose (right.length - left.length) (right.length - i) bits).map
      (fun choice => if choice then left else right)) ((weightedLeft G).eval s) :=
  weighted_value G 25 26 (by decide) (by decide) (by decide) (by decide) left right i bits s
    stored.leftWord stored.rightWord stored.target stored.random stored.word stored.found enough

theorem weightedRight_value (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s)
    (enough : Nat.clog 2 (left.length - right.length) ≤ bits.length) :
    Chosen G ((RationalSelection.choose (left.length - right.length) (left.length - i) bits).map
      (fun choice => if choice then right else left)) ((weightedRight G).eval s) :=
  weighted_value G 26 25 (by decide) (by decide) (by decide) (by decide) right left i bits s
    stored.rightWord stored.leftWord stored.target stored.random stored.word stored.found enough

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
