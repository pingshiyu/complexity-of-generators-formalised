import ComplexityOfGenerators.Proofs.PaperExactRecursiveTrials
import ComplexityOfGenerators.Proofs.RandomMeter
import ComplexityOfGenerators.Proofs.ExactRecursiveGeneration

/-!
# Packaging the verified filtered inverse source

A raw filtered source only needs polynomial total time on productive fibres.
The native random-meter compiler supplies uniform finite trial budgets on
empty fibres as well. No such budgets are assumed by the paper's interface.
-/
namespace ComplexityOfGenerators.PaperExactRecursiveGenerators
noncomputable section
open Simulation
variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : PaperExactRecursiveGenerators R)
    (source : Machine α α α) (p : PolynomialBound)
    (support : ∀ n y w,y∈L →
      source.generatedLanguage { input:=y,auxiliary:=w,index:=n }=R.inverseFibre n y w)
    (noReject : ∀ n y w,y∈L → ∀ bits : BitString,∀ ticks,
      source.run { input:=y,auxiliary:=w,index:=n } bits ticks≠.halted .rejected)
    (activeTime : ∀ n y w,y∈L → (R.inverseFibre n y w).Nonempty →
      source.TimeBound { input:=y,auxiliary:=w,index:=n } (p n))

/-- The old controller's source budgets are derived by a genuine native
compiler, after validating source outputs against the current interface. -/
def normalized : ExactRecursiveGenerators R where
  base := G.normalizedBase
  baseTime := G.normalizedBase_polynomialTime
  base_language := G.normalizedBase_language
  inverse := RandomMeter.machine source
  inverseSeed := RandomMeter.seed p
  inverseTime := RandomMeter.time p
  inverse_generator n y w member := by
    apply RandomMeter.isGenerator source _ (p n) (RandomMeter.seed p n) (RandomMeter.seed_long p n)
      (noReject n y w member)
    intro active
    rw [support n y w member] at active
    exact activeTime n y w member active
  inverse_language n y w member := (RandomMeter.generatedLanguage source _).trans (support n y w member)
  inverse_time n y w member := by
    apply RandomMeter.polynomial_trialBound source p _ (noReject n y w member)
    intro active
    rw [support n y w member] at active
    exact activeTime n y w member active

include G source p support noReject activeTime in
/-- Final controller packaging, applied to the concrete native filtered source
in the current exact-recursive generation theorem. -/
theorem mem_pg_of_filtered_source : L∈PG α :=
  (normalized G source p support noReject activeTime).mem_pg

end
end ComplexityOfGenerators.PaperExactRecursiveGenerators
