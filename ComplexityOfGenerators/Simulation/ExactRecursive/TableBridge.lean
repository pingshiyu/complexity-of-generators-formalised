import ComplexityOfGenerators.Simulation.ExactRecursive.Body
import ComplexityOfGenerators.Proofs.ExactRecursiveTableSampling

namespace ComplexityOfGenerators.ExactRecursiveGenerators

open Simulation.ExactRecursive Simulation.WordStack

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)
variable (alphabet : List α) (card : alphabet.length = Fintype.card α)
    (first : α) (least : Simulation.CyclicGenerator.firstLetter = some first)

noncomputable abbrev nativeTable : LabelEnumeration R := LabelEnumeration.shortlex R alphabet card first least

theorem native_search_eq (n : ℕ) (y : List α) (bits : BitString) :
    searchValue G.inverse first (R.labelCountBound alphabet) G.inverseSeed G.inverseTime n y bits =
      G.tableSearch (nativeTable (R := R) alphabet card first least) n y bits := by
  unfold searchValue tableSearch tableEntries
  rw [entriesFrom_eq]
  simp only [nativeTable, LabelEnumeration.shortlex, Shortlex.labels, List.map_map, Function.comp_def]
  have entries (label : List α) : positiveValue G.inverse G.inverseTime n y label = G.positiveTrial n y label := by
    funext seed
    by_cases empty : label = []
    · simp [positiveValue, positiveTrial, empty]
    · simp only [positiveValue, positiveTrial, empty, ↓reduceIte]
      apply Option.ext
      intro word
      rw [inverseValue_eq_some, G.inverseTrial_eq_some]
  simp only [entries]

theorem native_walk_eq (n fuel : ℕ) (y : List α) (bits : BitString) :
    walkResult G.inverse first (R.labelCountBound alphabet) G.inverseSeed G.inverseTime n fuel y bits =
      G.tableWalk (nativeTable (R := R) alphabet card first least) n fuel y bits := by
  induction fuel generalizing y bits with
  | zero => rfl
  | succ fuel ih =>
    rw [walkResult, tableWalk]
    have size : G.tableSeed (nativeTable (R := R) alphabet card first least) n =
        R.labelCountBound alphabet n * (G.inverseSeed n + 1) := by
      simp [tableSeed, nativeTable, LabelEnumeration.shortlex]
    rw [size, G.native_search_eq alphabet card first least]
    by_cases stop : y.length = n ∧ bits.head? = some true
    · simp [stop]
    · simp only [ite_eq_right stop]
      cases result : G.tableSearch (nativeTable (R := R) alphabet card first least) n y
          ((bits.drop 1).take (R.labelCountBound alphabet n * (G.inverseSeed n + 1))) <;>
        simp only [result, ih]

theorem native_algorithm_eq (seed time : PolynomialBound) (n : ℕ) (bits : BitString) :
    Simulation.ExactRecursive.algorithm G.base.machine G.inverse first seed time G.inverseSeed G.inverseTime
      (R.labelCountBound alphabet) R.rankBound n bits =
        G.tableAlgorithm seed time (nativeTable (R := R) alphabet card first least) n bits := by
  unfold Simulation.ExactRecursive.algorithm tableAlgorithm
  have value : baseValue G.base.machine time n (bits.take (seed n)) =
      G.baseTrial time n (bits.take (seed n)) := by
    apply Option.ext
    intro word
    rw [baseValue_eq_some, G.baseTrial_eq_some]
  rw [value]
  congr 1
  funext word
  exact G.native_walk_eq alphabet card first least n (R.rankBound n) word _

end ComplexityOfGenerators.ExactRecursiveGenerators
