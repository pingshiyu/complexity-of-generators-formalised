import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.AfterIndex

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

def region (data : InputData I A) (radius : ℕ) := max radius (2*Nat.clog 2 (data.input.length+1)+4)

theorem probe_from_bounded (data : InputData I A) (choices : BitString)
    (current : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current) :
    (bank source).RegionSteps data choices (region data radius)
      (configuration source data.input.length current.indexHead current (.probe current.state (.scan false)))
      (2*(max (increment^[current.indexHead] []).length (increment^[data.input.length] []).length+1)+1)
      (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length)))) := by
  exact probe_steps source data choices current.indexHead current (region data radius)
    (bounded.mono source (Nat.le_max_left _ _)) bounded.index (by dsimp [region];omega)

/-- Every actual source execution is implemented by the finite binary-index
controller. Counter operations reuse the same logarithmic region between
source instructions and consume no random bits. -/
theorem execution_inRegion (data : InputData I A) (choices : BitString)
    (current : BankConfiguration O Q S k) (ticks : ℕ) (result : Outcome O)
    (execution : source.Executes (sourceData data) choices current ticks result) (radius : ℕ)
    (allBound : ∀ time next,source.Steps (sourceData data) choices current time next →
      source.Bounded (sourceData data) radius next) :
    (bank source).RegionRun data choices (region data radius)
      (configuration source data.input.length current.indexHead current (.probe current.state (.scan false))) result := by
  revert allBound
  induction execution with
  | accept current table =>
      intro allBound
      have bounded := allBound 0 current (.refl _)
      have probing := probe_from_bounded source data choices current radius bounded
      refine ⟨_,configuration source data.input.length current.indexHead current
        (.execute current.state (decide (current.indexHead<data.input.length))),probing,?_⟩
      apply TapeBank.Executes.accept
      rw [source_instruction source data current _ rfl,table]
      rfl
  | reject current table =>
      intro allBound
      have bounded := allBound 0 current (.refl _)
      have probing := probe_from_bounded source data choices current radius bounded
      refine ⟨_,configuration source data.input.length current.indexHead current
        (.execute current.state (decide (current.indexHead<data.input.length))),probing,?_⟩
      apply TapeBank.Executes.reject
      rw [source_instruction source data current _ rfl,table]
      rfl
  | exhausted current no yes table absent =>
      intro allBound
      have bounded := allBound 0 current (.refl _)
      have probing := probe_from_bounded source data choices current radius bounded
      refine ⟨_,configuration source data.input.length current.indexHead current
        (.execute current.state (decide (current.indexHead<data.input.length))),probing,?_⟩
      apply TapeBank.Executes.exhausted _ (.probe no (.scan false)) (.probe yes (.scan false))
      · rw [source_instruction source data current _ rfl,table]
        rfl
      · exact absent
  | random current no yes bit ticks result table lookup rest ih =>
      intro allBound
      have bounded := allBound 0 current (.refl _)
      let next := TapeBank.choose current (if bit then yes else no)
      have after : ∀ time finish,source.Steps (sourceData data) choices next time finish →
          source.Bounded (sourceData data) radius finish := by
        intro time finish path
        exact allBound (time+1) finish (.random current no yes bit time finish table lookup path)
      have nextBound := after 0 next (.refl _)
      have nativeBound := configuration_bounded source data data.input.length current.indexHead current
        (.execute current.state (decide (current.indexHead<data.input.length))) (region data radius)
        (bounded.mono source (Nat.le_max_left _ _))
      have nativeTable : (bank source).instruction data
          (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length))))=
          .readRandom (.probe no (.scan false)) (.probe yes (.scan false)) := by
        rw [source_instruction source data current _ rfl,table]
        rfl
      have chosen : TapeBank.choose
          (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length))))
          (if bit then .probe yes (.scan false) else .probe no (.scan false))=
          configuration source data.input.length next.indexHead next (.probe next.state (.scan false)) := by
        cases bit <;> rfl
      have one : (bank source).RegionSteps data choices (region data radius)
          (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length)))) 1
          (configuration source data.input.length next.indexHead next (.probe next.state (.scan false))) := by
        apply TapeBank.RegionSteps.random _ (.probe no (.scan false)) (.probe yes (.scan false)) bit 0 _ nativeBound nativeTable lookup
        rw [chosen]
        exact .refl _ (configuration_bounded source data data.input.length next.indexHead next (.probe next.state (.scan false))
          (region data radius) (nextBound.mono source (Nat.le_max_left _ _)))
      exact ((ih after).prepend (bank source) one).prepend (bank source)
        (probe_from_bounded source data choices current radius bounded)
  | step current next write work input auxiliary index emit ticks result table rest ih =>
      intro allBound
      have bounded := allBound 0 current (.refl _)
      let following := source.advance (sourceData data) current next write work input auxiliary index emit
      have after : ∀ time finish,source.Steps (sourceData data) choices following time finish →
          source.Bounded (sourceData data) radius finish := by
        intro time finish path
        exact allBound (time+1) finish (.step current next write work input auxiliary index emit time finish table path)
      have nextBound := after 0 following (.refl _)
      have nativeTable : (bank source).instruction data
          (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length))))=
          .step (afterStep next (decide (current.indexHead<data.input.length)) index) (encodeSource write) work input auxiliary .stay emit := by
        rw [source_instruction source data current _ rfl,table]
        rfl
      have one : (bank source).RegionSteps data choices (region data radius)
          (configuration source data.input.length current.indexHead current (.execute current.state (decide (current.indexHead<data.input.length)))) 1
          (configuration source data.input.length current.indexHead following (afterStep next (decide (current.indexHead<data.input.length)) index)) := by
        apply TapeBank.RegionSteps.step _ _ _ work input auxiliary .stay emit 0 _
          (configuration_bounded source data data.input.length current.indexHead current
            (.execute current.state (decide (current.indexHead<data.input.length))) (region data radius)
            (bounded.mono source (Nat.le_max_left _ _))) nativeTable
        rw [source_advance]
        exact .refl _ (configuration_bounded source data data.input.length current.indexHead following
          (afterStep next (decide (current.indexHead<data.input.length)) index) (region data radius)
          (nextBound.mono source (Nat.le_max_left _ _)))
      obtain ⟨time,adjusted⟩ := after_index_steps source data choices current.indexHead following (region data radius)
        (nextBound.mono source (Nat.le_max_left _ _)) bounded.index (Nat.le_max_right _ _)
        (decide (current.indexHead<data.input.length)) rfl index
      have continuation : (bank source).RegionRun data choices (region data radius)
          (configuration source data.input.length current.indexHead following (afterStep next (decide (current.indexHead<data.input.length)) index)) result := by
        exact (ih after).prepend (bank source) adjusted
      exact (continuation.prepend (bank source) one).prepend (bank source)
        (probe_from_bounded source data choices current radius bounded)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
