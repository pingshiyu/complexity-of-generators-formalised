import ComplexityOfGenerators.Simulation.OriginalHeaderController.Prelude
import ComplexityOfGenerators.Simulation.OriginalHeaderController.Runs
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Clock
import ComplexityOfGenerators.Simulation.FixedBlockRetry.ValueProperties

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound)

def primitiveCoefficient : PolynomialBound := PolynomialBound.ofPolynomial
  (100*(Polynomial.X+1)+(FixedBlockRetry.attemptClock width (cap width clock)
    (phaseTime selector width clock)).asPolynomial+100*((cap width clock).asPolynomial+1)+2)

theorem primitiveCoefficient_lower (n : ℕ) :
    100*(n+1)+(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2)+
      100*(cap width clock n+1)+2≤primitiveCoefficient selector width clock n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval]
  have bound := FixedBlockRetry.attemptBudget_add_two_le width (cap width clock) (phaseTime selector width clock) n
  omega

theorem command_runs_success (operation : Operation) (n random failures : ℕ) (bits : BitString)
    (header : List Bool) (requests : List Request) (choice : Choice operation n header requests)
    (enough : random+(failures+1)*width n≤bits.length)
    (failed : ∀ k<failures,reference selector clock n ((bits.drop (random+k*width n)).take (width n))=none)
    (accepted : reference selector clock n ((bits.drop (random+failures*width n)).take (width n))=some header) :
    ∃ ticks≤primitiveCoefficient selector width clock n*(failures+1),∃next,
      (command selector width clock operation).Runs n bits (initialMemory selector random) ticks (.done next) ∧
      next.output=(eventList requests).map Prod.fst ∧ next.indexHead≤n ∧
      next.randomHead=random+(failures+1)*width n := by
  obtain ⟨first,firstBound,after,firstRun,state,cursor,payload⟩ :=
    prelude_success selector width clock n random failures bits enough failed header accepted
  obtain ⟨last,lastBound,next,lastRun,head,randomHead,output,_⟩ :=
    events_runs selector operation n bits header requests choice after state.head state.index payload (cap width clock n) state.sizes
  have small : 100*(n+1)+100*(cap width clock n+1)+2≤
      (failures+1)*(100*(n+1)+100*(cap width clock n+1)+2) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ (show 1≤failures+1 by omega)
  have total : first+1+last≤(failures+1)*primitiveCoefficient selector width clock n := by
    calc
      first+1+last≤(failures+1)*(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2)+
          (100*(n+1)+100*(cap width clock n+1)+2) := by omega
      _≤(failures+1)*(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2)+
          (failures+1)*(100*(n+1)+100*(cap width clock n+1)+2) := Nat.add_le_add_left small _
      _=(failures+1)*(100*(n+1)+(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2)+
          100*(cap width clock n+1)+2) := by ring
      _≤_ := Nat.mul_le_mul_left _ (primitiveCoefficient_lower selector width clock n)
  refine ⟨first+1+last,by simpa only [Nat.mul_comm] using total,next,?_,?_,head.trans_le state.head,randomHead.trans cursor⟩
  · unfold command
    exact Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun
  · simpa only [state.output,List.nil_append] using output

/-- Each accepted certificate encodes one valid request list. -/
def Shape (operation : Operation) (n : ℕ) : Prop :=
  ∀ block : BitString,block.length=width n→∀ header,
    reference selector clock n block=some header→∃requests,Choice operation n header requests

theorem prelude_shape (operation : Operation) (n random : ℕ) (bits : BitString)
    (shape : Shape selector width clock operation n) (finish : Memory (Cell selector) Event 35)
    (canonical : BoundedMachinePhase.Canonical selector finish.store)
    (selected : FixedBlockRetry.selected (headerBit selector) (.done finish)=
      FixedBlockRetry.scan (width n) (reference selector clock n) ((bits.length-random)/width n) (bits.drop random)) :
    ∃header requests, finish.store 31=header.map Symbol.letter ∧ Choice operation n header requests ∧
      ∃block,block.length=width n ∧ reference selector clock n block=some header := by
  obtain ⟨header,payload⟩ := canonical
  have decoded : (finish.store 31).filterMap (headerBit selector)=header := by
    rw [payload]
    simp [headerBit,UnionGenerator.outputLetter,List.filterMap_map ]
  have scan : FixedBlockRetry.value width (reference selector clock) n (bits.drop random)=some header := by
    rw [FixedBlockRetry.selected,decoded] at selected
    simpa only [FixedBlockRetry.value,List.length_drop] using selected.symm
  obtain ⟨block,length,hit⟩ := FixedBlockRetry.value_sound width (reference selector clock) n (bits.drop random) header scan
  obtain ⟨requests,choice⟩ := shape block length header hit
  exact ⟨header,requests,payload,choice,block,length,hit⟩

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
