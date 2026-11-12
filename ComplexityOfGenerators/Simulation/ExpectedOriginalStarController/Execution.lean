import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Prefix

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CertifiedStarPhase.routine StarCertification.routine StarPaths.pathRoutine pathRetry
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

def primitiveCoefficient : PolynomialBound := PolynomialBound.ofPolynomial
  (100*(Polynomial.X+1)+
    (FixedBlockRetry.attemptClock (StarCertification.width p) (CertifiedStarPhase.cap p)
      (CertifiedStarPhase.time M p)).asPolynomial+
    20*((CertifiedStarPhase.cap p).asPolynomial+1)*(Polynomial.X+1)+2)

theorem primitiveCoefficient_lower (n : ℕ) :
    100*(n+1)+ExpectedStarGenerator.pathCallBudget M p n+
      20*(CertifiedStarPhase.cap p n+1)*(n+1)+2≤primitiveCoefficient M p n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval]
  have path := FixedBlockRetry.attemptBudget_add_two_le (StarCertification.width p)
    (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p) n
  change ExpectedStarGenerator.pathCallBudget M p n≤_ at path
  omega

theorem command_runs_success (n random failures : ℕ) (parts : List ℕ) (bits : BitString)
    (total : parts.sum=n) (positive : ∀ j∈parts,0<j)
    (enough : random+(failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures, CertifiedStarPhase.value M p n
      ((bits.drop (random+k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (random+failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts)) :
    ∃ ticks≤primitiveCoefficient M p n*(failures+1), ∃ next,
      (command M p).Runs n bits (initialMemory M random) ticks (.done next) ∧
      next.output=List.replicate parts.length () ∧ next.indexHead=0 ∧
      next.randomHead=random+(failures+1)*StarCertification.width p n ∧
      ∃ after : Memory (Cell M) Unit 80, after.indexHead=0 ∧ after.output=[] ∧ after.store 31=pathWord M parts ∧
        Trace M n bits parts (after.set 0 []) next := by
  unfold command
  obtain ⟨first,firstBound,firstRun⟩ := boot_runs M n random bits
  obtain ⟨second,secondBound,after,secondRun,afterOrigin,afterRandom,afterOutput,afterPath,afterBound⟩ :=
    pathRetry_runs_success M p n random failures parts bits enough failed success
  obtain ⟨last,lastBound,next,lastRun,nextOrigin,nextRandom,nextOutput,_,_,_,trace⟩ :=
    events_runs M n bits parts after (CertifiedStarPhase.cap p n) afterOrigin afterPath afterBound
  have count : parts.length≤n :=
    (ExpectedStarGenerator.positive_length_le_sum parts positive).trans_eq total
  have lastBudget : last≤20*(CertifiedStarPhase.cap p n+1)*(n+1) :=
    lastBound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right count 1))
  have fixedCharge : 100*(n+1)+20*(CertifiedStarPhase.cap p n+1)*(n+1)+2≤
      (failures+1)*(100*(n+1)+20*(CertifiedStarPhase.cap p n+1)*(n+1)+2) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right
      (100*(n+1)+20*(CertifiedStarPhase.cap p n+1)*(n+1)+2) (show 1≤failures+1 by omega)
  have timeBound : first+1+(second+1+last)≤(failures+1)*primitiveCoefficient M p n := by
    calc
      first+1+(second+1+last) ≤
          (failures+1)*ExpectedStarGenerator.pathCallBudget M p n+
          (100*(n+1)+20*(CertifiedStarPhase.cap p n+1)*(n+1)+2) := by omega
      _ ≤ (failures+1)*ExpectedStarGenerator.pathCallBudget M p n+
          (failures+1)*(100*(n+1)+20*(CertifiedStarPhase.cap p n+1)*(n+1)+2) :=
        Nat.add_le_add_left fixedCharge _
      _ = (failures+1)*(100*(n+1)+ExpectedStarGenerator.pathCallBudget M p n+
          20*(CertifiedStarPhase.cap p n+1)*(n+1)+2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (primitiveCoefficient_lower M p n)
  refine ⟨first+1+(second+1+last),by simpa [Nat.mul_comm] using timeBound,next,
    (by simpa only [Nat.add_assoc] using (Command.Runs.seq _ _ _ _ _ _ _
      (prelude_of_runs M p firstRun secondRun afterOutput) lastRun)),
    ?_,nextOrigin,nextRandom.trans afterRandom,after,afterOrigin,afterOutput,afterPath,trace⟩
  simpa only [afterOutput,List.nil_append] using nextOutput

def GeneratedResult (n : ℕ) : Result (Cell M) Unit 80 → Prop
  | .exhausted => True
  | .done next => ∃ parts : List ℕ, parts.sum=n ∧ (∀ j∈parts,0<j) ∧
      next.output=List.replicate parts.length () ∧ next.indexHead=0

theorem command_runs_total (n random : ℕ) (bits : BitString) :
    ∃ ticks result, (command M p).Runs n bits (initialMemory M random) ticks result ∧
      GeneratedResult M n result := by
  unfold command
  obtain ⟨first,_,firstRun⟩ := boot_runs M n random bits
  obtain ⟨second,result,secondRun,post⟩ := pathRetry_runs_total M p n random bits
  cases result with
  | exhausted =>
      exact ⟨first+1+second,.exhausted,Command.Runs.seq_absent _ _ _ _ (prelude_of_exhausted M p firstRun secondRun),trivial⟩
  | done after =>
      obtain ⟨origin,empty,sizes,parts,total,positive,path,_⟩ := post
      obtain ⟨last,_,next,lastRun,nextOrigin,_,nextOutput,_,_,_,_⟩ :=
        events_runs M n bits parts after (CertifiedStarPhase.cap p n) origin path sizes
      refine ⟨first+1+(second+1+last),.done next,(by simpa only [Nat.add_assoc] using (Command.Runs.seq _ _ _ _ _ _ _
        (prelude_of_runs M p firstRun secondRun empty) lastRun)),parts,total,positive,?_,nextOrigin⟩
      simpa only [empty,List.nil_append] using nextOutput

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
