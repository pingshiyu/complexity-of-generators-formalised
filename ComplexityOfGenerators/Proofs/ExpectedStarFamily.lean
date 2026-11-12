import ComplexityOfGenerators.Proofs.ExpectedStarNativeProperties
import ComplexityOfGenerators.Foundations.IndexedStarLanguage

/-! Package the implemented certified star machine as a uniform expected-time
family. Empty members use the empty-generator case; all moment requirements
are proved only at productive indices. -/
namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ExpectedStarGenerator.machine
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))
    (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

include layers in
theorem native_available_of_member (n : ℕ) (word : List α)
    (member : word ∈ (ExpectedStarGenerator.machine G.machine p P).generatedLanguage (generatorData n)) :
    Available G n := by
  have generated := ExpectedStarGenerator.machine_language_subset G.machine p P n member
  obtain ⟨parts,total,active⟩ := IndexedSupport.starLayers_available P.layer n word generated
  refine ⟨parts,total,?_⟩
  intro j belongs
  have source := active j belongs
  rw [layers j] at source
  exact source

include expected layers in
theorem native_isGenerator (n : ℕ) :
    (ExpectedStarGenerator.machine G.machine p P).IsGenerator (generatorData n) := by
  refine ⟨ExpectedStarGenerator.machine_halting G.machine p P n,?_⟩
  by_cases active : ((ExpectedStarGenerator.machine G.machine p P).generatedLanguage (generatorData n)).Nonempty
  · obtain ⟨word,member⟩ := active
    exact Or.inl (native_productive G p expected P layers n
      (native_available_of_member G p P layers n word member))
  · apply Or.inr
    rw [((ExpectedStarGenerator.machine G.machine p P).acceptedStreams_eq_empty_iff
      (generatorData n)).mpr (Set.not_nonempty_iff_eq_empty.mp active),measure_empty]

def family : UniformGenerators α where
  machine := ExpectedStarGenerator.machine G.machine p P
  isGenerator := native_isGenerator G p expected P layers

theorem family_layer (n : ℕ) :
    (family G p expected P layers).layer n = IndexedSupport.starLayers G.layer n := by
  change (ExpectedStarGenerator.machine G.machine p P).generatedLanguage (generatorData n) = _
  rw [ExpectedStarGenerator.machine_language p P G layers expected n,show P.layer = G.layer from funext layers]

theorem family_expectedLength : (family G p expected P layers).ExpectedLength := by
  intro n active
  obtain ⟨word,member⟩ := active
  exact native_expectedLength G p expected P layers n
    (native_available_of_member G p P layers n word member)

theorem family_expectedPolynomialTime : (family G p expected P layers).ExpectedPolynomialTime := by
  let clock := (expectedClock G p P).add (ExpectedStarGenerator.shortClock p P G)
  have expectedBound (n : ℕ) : expectedClock G p P n ≤ clock n :=
    (Nat.le_add_right _ _).trans (PolynomialBound.add_le _ _ n)
  have shortBound (n : ℕ) : ExpectedStarGenerator.shortClock p P G n ≤ clock n :=
    (Nat.le_add_left _ _).trans (PolynomialBound.add_le _ _ n)
  refine ⟨clock,?_,?_⟩
  · intro n active
    obtain ⟨word,member⟩ := active
    exact (native_expectedRuntime G p expected P layers n
      (native_available_of_member G p P layers n word member)).trans (Nat.cast_le.mpr (expectedBound n))
  · intro n word member
    have source := ExpectedStarGenerator.machine_language_subset G.machine p P n member
    obtain ⟨bits,nonempty,run⟩ := ExpectedStarGenerator.machine_short_path p P G layers expected n word source
    refine ⟨bits,nonempty,?_⟩
    have padded := (ExpectedStarGenerator.machine G.machine p P).run_halted_add (generatorData n) bits
      (ExpectedStarGenerator.shortClock p P G n) (.accepted word) run (clock n-ExpectedStarGenerator.shortClock p P G n)
    rw [Nat.add_sub_of_le (shortBound n)] at padded
    exact padded

end
end ComplexityOfGenerators.ExpectedStarSampling
