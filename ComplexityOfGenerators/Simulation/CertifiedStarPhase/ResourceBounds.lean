import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Phase
import ComplexityOfGenerators.Simulation.CertifiedStarPhase.CanonicalBounds
import ComplexityOfGenerators.Simulation.StarPaths.FinalBounds

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section

/-- The mapped selector retains only the target, cache and unused block;
its input size is independent of discarded caller/source scratch data. -/
def inputBound (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  ((StarCertification.width p).asPolynomial+Polynomial.X+1)

def cap (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (1+Polynomial.X+(IndexwiseCertification.seed p).asPolynomial+
    3*((IndexwiseCertification.clock p).asPolynomial+1)+
    (StarPaths.workspace (inputBound p)).asPolynomial+(inputBound p).asPolynomial+10)

def time (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  ((StarCertification.primitiveTime M p (cap p)).asPolynomial+
    (StarPaths.primitiveTime (inputBound p)).asPolynomial+300*((cap p).asPolynomial+1)+10)

theorem inputBound_lower (p : PolynomialBound) (n : ℕ) :
    StarCertification.width p n+n+1 ≤ inputBound p n := by
  unfold inputBound
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,PolynomialBound.asPolynomial_eval]
  rfl

theorem cap_lower (p : PolynomialBound) (n : ℕ) :
    1+n+IndexwiseCertification.seed p n+3*(IndexwiseCertification.clock p n+1)+
      StarPaths.workspace (inputBound p) n+inputBound p n+10 ≤ cap p n := by
  unfold cap
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval]
  rfl

theorem time_lower (p : PolynomialBound) (n : ℕ) :
    StarCertification.primitiveTime M p (cap p) n+StarPaths.primitiveTime (inputBound p) n+
      300*(cap p n+1)+10 ≤ time M p n := by
  unfold time
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval]
  rfl

attribute [local irreducible] cap inputBound time pathStage routine StarCertification.routine StarPaths.pathRoutine

private theorem pathInput_bound (p : PolynomialBound) (flags bits : List Bool) (s : Store M) (n : ℕ)
    (source : s 25 = StarCertification.cacheWord M flags) (coins : s 17 = bits.map (bitSymbol M))
    (master : (s 22).length = n) (flagsSize : flags.length ≤ n) (bitsSize : bits.length ≤ StarCertification.width p n) :
    StoreBound (pathInput M s) (inputBound p n) := by
  have lower := inputBound_lower p n
  intro j
  by_cases a : j = 17 <;> by_cases b : j = 22 <;> by_cases c : j = 25 <;>
    simp [pathInput,a,b,c,source,coins,StarCertification.cacheWord,master] <;> omega

/-- The complete outer phase preserves one fixed polynomial cap even when
the incoming scratch bank contains arbitrary data up to that cap. -/
theorem routine_resources (p : PolynomialBound) (n : ℕ) (block : BitString) (s : Store M)
    (length : block.length = StarCertification.width p n) (master : (s 22).length = n)
    (coins : s 17 = block.map (bitSymbol M)) (sizes : StoreBound s (cap p n)) :
    StoreBound ((routine M p).eval s) (cap p n) ∧ (routine M p).cost s ≤ time M p n := by
  let tested := (StarCertification.routine M p).eval s
  let inspected := StarCertification.walk M p 0 n block
  have lower := cap_lower p n
  have bitCode : bitSymbol M = StarCertification.bitSymbol M := rfl
  have certificationCoins : s 17 = block.map (StarCertification.bitSymbol M) := by rw [← bitCode]; exact coins
  have certified := StarCertification.routine_bound M p s block n (cap p n) certificationCoins master sizes
    (by omega) (by omega) (by omega) (by omega)
  have testedSize : StoreBound tested (cap p n) := certified.1
  have certificationTime := (StarCertification.routine_resources M p (cap p) s block n certificationCoins master sizes).2
  have inspectedResult := StarCertification.routine_value M p s block certificationCoins
  have testedCache : tested 25 = StarCertification.cacheWord M inspected.1 := by simpa only [master] using inspectedResult.1
  have testedCoinsRaw : tested 17 = inspected.2.map (StarCertification.bitSymbol M) := by simpa only [master] using inspectedResult.2
  have testedCoins : tested 17 = inspected.2.map (bitSymbol M) := by rw [bitCode]; exact testedCoinsRaw
  have testedMaster : (tested 22).length = n :=
    (congrArg List.length (StarCertification.routine_frame M p 22 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)).trans master
  have flagsSize : inspected.1.length ≤ n := (StarCertification.walk_length M p 0 n block).le
  have bitsSize : inspected.2.length ≤ StarCertification.width p n := by
    change (StarCertification.walk M p 0 n block).2.length ≤ _
    rw [StarCertification.walk_remaining]
    simp only [List.length_drop]
    omega
  have inputSize := pathInput_bound M p inspected.1 inspected.2 tested n testedCache testedCoins testedMaster flagsSize bitsSize
  have sourceInput : pathInput M tested 25 = StarPaths.flagsWord inspected.1 := by
    simp [pathInput,testedCache,StarCertification.cacheWord,StarCertification.flagSymbol,StarPaths.flagsWord,
      List.map_map,Function.comp_def,projectPath]
  have inputMaster : (pathInput M tested 22).length = n := (pathInput_master M tested).trans testedMaster
  have path := StarPaths.pathRoutine_resources (O := α) (inputBound p) inspected.1 (pathInput M tested) n
    inputSize sourceInput inputMaster
  have prepared := canonicalPrepare_bound M tested (cap p n) testedSize
  have selectedSize : StoreBound ((pathStage M).eval tested) (cap p n) := by
    unfold pathStage
    intro j
    change (((StarPaths.pathRoutine (O := α)).eval (pathInput M tested) j).map (encodePath M)).length ≤ _
    rw [List.length_map]
    exact (path.1 j).trans (by omega)
  have selectedTime : (pathStage M).cost tested ≤ 250*(cap p n+1)+1+StarPaths.primitiveTime (inputBound p) n := by
    unfold pathStage
    change (canonicalPrepare M).cost tested+1+(StarPaths.pathRoutine (O := α)).cost (pathInput M tested) ≤ _
    omega
  constructor
  · unfold routine
    exact selectedSize
  · have final := time_lower M p n
    unfold routine
    change (StarCertification.routine M p).cost s+1+(pathStage M).cost tested ≤ _
    omega

theorem phase_bound (p : PolynomialBound) : FixedBlockRetry.PhaseBound
    (bitSymbol M) (StarCertification.width p) (cap p) (time M p) (routine M p) := by
  intro n block s length _ master coins sizes
  exact routine_resources M p n block s length master coins sizes

end
end ComplexityOfGenerators.Simulation.CertifiedStarPhase
