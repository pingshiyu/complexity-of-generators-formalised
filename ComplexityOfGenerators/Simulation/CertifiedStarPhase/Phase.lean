import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Mapped
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Components

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section

def pathChoice (p : PolynomialBound) (n : ℕ) (bits : BitString) : Option StarPaths.Parts :=
  let inspected := StarCertification.walk M p 0 n bits
  StarPaths.selected inspected.1 n inspected.2

def value (p : PolynomialBound) (n : ℕ) (bits : BitString) : Option (List StarPaths.Symbol) :=
  (pathChoice M p n bits).map StarPaths.payload

noncomputable def routine (p : PolynomialBound) : Step M := (StarCertification.routine M p).seq (pathStage M)

attribute [local irreducible] StarCertification.routine StarPaths.pathRoutine pathStage routine value pathChoice

private theorem decode_mapped (word : List StarPaths.Symbol) :
    (word.map (encodePath M)).filterMap (decodePath M) = word := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

/-- Exact payload/flag semantics of the actual certification-plus-selection
controller; it does not emit a physical source word. -/
theorem routine_value (p : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store M)
    (coins : s 17 = bits.map (bitSymbol M)) (master : (s 22).length = n) :
    (routine M p).eval s 32 = FixedBlockRetry.flagWord (unitSymbol M) (value M p n bits).isSome ∧
      ∀ word, value M p n bits = some word → ((routine M p).eval s 31).filterMap (decodePath M) = word := by
  let tested := (StarCertification.routine M p).eval s
  let inspected := StarCertification.walk M p 0 n bits
  have bitCode : bitSymbol M = StarCertification.bitSymbol M := rfl
  have certificationCoins : s 17 = bits.map (StarCertification.bitSymbol M) := by rw [← bitCode]; exact coins
  have inspectedResult := StarCertification.routine_value M p s bits certificationCoins
  have testedCache : tested 25 = StarCertification.cacheWord M inspected.1 := by simpa only [master] using inspectedResult.1
  have testedCoinsRaw : tested 17 = inspected.2.map (StarCertification.bitSymbol M) := by
    simpa only [master] using inspectedResult.2
  have testedCoins : tested 17 = inspected.2.map (bitSymbol M) := by rw [bitCode]; exact testedCoinsRaw
  have testedMaster : (tested 22).length = n :=
    (congrArg List.length (StarCertification.routine_frame M p 22 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)).trans master
  have selectedResult := pathStage_value M inspected.1 inspected.2 tested n testedCache testedCoins testedMaster
  have pureValue : value M p n bits = (StarPaths.selected inspected.1 n inspected.2).map StarPaths.payload := by
    unfold value pathChoice
    rfl
  have actual : (routine M p).eval s = (pathStage M).eval tested := by unfold routine; rfl
  rw [actual]
  constructor
  · rw [selectedResult.2,pureValue]
    cases StarPaths.selected inspected.1 n inspected.2 <;> rfl
  · intro word output
    rw [pureValue] at output
    cases chosen : StarPaths.selected inspected.1 n inspected.2 with
    | none => simp [chosen] at output
    | some parts =>
        have same : StarPaths.payload parts = word := by simpa [chosen] using output
        rw [selectedResult.1,chosen]
        simpa only [StarPaths.held,decode_mapped] using same

/-- Successful and failed phases retain an exactly encoded path bank,
not only its filtered projection. This invariant is preserved by the outer
native retry loop before source-factor calls begin. -/
theorem routine_output (p : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store M)
    (coins : s 17 = bits.map (bitSymbol M)) (master : (s 22).length = n) :
    (routine M p).eval s 31 = ((value M p n bits).getD []).map (encodePath M) := by
  let tested := (StarCertification.routine M p).eval s
  let inspected := StarCertification.walk M p 0 n bits
  have bitCode : bitSymbol M = StarCertification.bitSymbol M := rfl
  have certificationCoins : s 17 = bits.map (StarCertification.bitSymbol M) := by rw [← bitCode]; exact coins
  have inspectedResult := StarCertification.routine_value M p s bits certificationCoins
  have testedCache : tested 25 = StarCertification.cacheWord M inspected.1 := by simpa only [master] using inspectedResult.1
  have testedCoinsRaw : tested 17 = inspected.2.map (StarCertification.bitSymbol M) := by
    simpa only [master] using inspectedResult.2
  have testedCoins : tested 17 = inspected.2.map (bitSymbol M) := by rw [bitCode]; exact testedCoinsRaw
  have testedMaster : (tested 22).length = n :=
    (congrArg List.length (StarCertification.routine_frame M p 22 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)).trans master
  have selectedResult := pathStage_value M inspected.1 inspected.2 tested n testedCache testedCoins testedMaster
  have pureValue : value M p n bits = (StarPaths.selected inspected.1 n inspected.2).map StarPaths.payload := by
    unfold value pathChoice
    rfl
  have actual : (routine M p).eval s = (pathStage M).eval tested := by unfold routine; rfl
  rw [actual,selectedResult.1,pureValue]
  cases StarPaths.selected inspected.1 n inspected.2 <;> rfl

theorem phase_correct (p : PolynomialBound) : FixedBlockRetry.PhaseCorrect
    (unitSymbol M) (bitSymbol M) (decodePath M) (StarCertification.width p) (routine M p) (value M p) := by
  intro n block s _ _ master coins
  exact routine_value M p n block s coins master

/-- The master length required by the outer retry loop is preserved even
when arbitrary original symbols are normalized to the path alphabet. -/
theorem routine_frame (p : PolynomialBound) (s : Store M) : ((routine M p).eval s 22).length = (s 22).length := by
  let tested := (StarCertification.routine M p).eval s
  have head := pathStage_frame M tested
  have source := congrArg List.length (StarCertification.routine_frame M p 22 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s)
  have actual : (routine M p).eval s = (pathStage M).eval tested := by unfold routine; rfl
  rw [actual]
  exact head.trans source

theorem value_isSome (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    (value M p n bits).isSome = true ↔
      ∃ parts, StarPaths.Valid (StarCertification.walk M p 0 n bits).1 n parts := by
  unfold value pathChoice
  dsimp only
  simp only [Option.isSome_map]
  exact StarPaths.selected_isSome _ n _

theorem value_sound (p : PolynomialBound) (n : ℕ) (bits : BitString) (word : List StarPaths.Symbol)
    (result : value M p n bits = some word) :
    ∃ parts, StarPaths.Valid (StarCertification.walk M p 0 n bits).1 n parts ∧ word = StarPaths.payload parts := by
  unfold value at result
  obtain ⟨parts,chosen,equal⟩ := Option.map_eq_some_iff.mp result
  refine ⟨parts,?_,equal.symm⟩
  apply StarPaths.selected_sound _ n _ parts
  unfold pathChoice at chosen
  dsimp only at chosen
  exact chosen

end
end ComplexityOfGenerators.Simulation.CertifiedStarPhase
