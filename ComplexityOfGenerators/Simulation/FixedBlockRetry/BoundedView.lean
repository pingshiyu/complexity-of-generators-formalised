import ComplexityOfGenerators.Simulation.FixedBlockRetry.Native
import ComplexityOfGenerators.Proofs.PolynomialUnionSupport

/-! A single full block of the native retry generator is exactly one bounded
phase. Existing bounded union/concatenation/star controllers can reuse it. -/
namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O : Type} [Fintype S] [Fintype O]

def singleClock (width cap time : PolynomialBound) : PolynomialBound :=
  (⟨25, 0, by decide⟩ : PolynomialBound).mul
    ((coefficient width cap time).mul (coefficient width cap time))

theorem singleClock_eval (width cap time : PolynomialBound) (n : ℕ) :
    singleClock width cap time n = 25*(coefficient width cap time n)^2 := by
  unfold singleClock
  rw [PolynomialBound.mul_eval, PolynomialBound.mul_eval]
  change 25*(coefficient width cap time n * coefficient width cap time n) = _
  ring

variable (unitSymbol : S) (bitSymbol : Bool → S) (decode : S → Option O)
    (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (f : ℕ → BitString → Option (List O))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase)
    (frame : ∀ s, (phase.eval s 22).length = (s 22).length)

include correct bounded frame in
theorem sourceValue_full_block (n : ℕ) (block : BitString) (indexBudget : n+1 ≤ cap n)
    (widthBudget : width n ≤ cap n) (length : block.length = width n) :
    UnionGenerator.sourceValue (machine unitSymbol bitSymbol decode width phase) (singleClock width cap time) n block =
      f n block := by
  cases output : f n block with
  | none =>
    cases candidate : UnionGenerator.sourceValue (machine unitSymbol bitSymbol decode width phase)
        (singleClock width cap time) n block with
    | none => rfl
    | some word =>
      have produced : (machine unitSymbol bitSymbol decode width phase).Produces (generatorData n) block word :=
        ⟨_, (UnionGenerator.sourceValue_eq_some_iff _ _ _ _ _).mp candidate⟩
      have valueOutput := (machine_produces_iff unitSymbol bitSymbol decode width cap time phase f correct bounded frame
        n block word indexBudget widthBudget).mp produced
      rw [value_single_block width f n block length, output] at valueOutput
      cases valueOutput
  | some word =>
    unfold UnionGenerator.sourceValue
    rw [singleClock_eval, machine_short_path unitSymbol bitSymbol decode width cap time phase f correct bounded frame
      n block word indexBudget widthBudget length output]
    rfl

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
