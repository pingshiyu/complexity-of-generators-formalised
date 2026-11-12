import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
open BinaryCounter
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ}
variable (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (c : BankConfiguration O Q S k)
    (radius : ℕ)
    (allBound : ∀ ticks finish, source.Steps data choices c ticks finish → source.Bounded data radius finish)

include canonical allBound in
theorem accepted_iff (word : List O) :
    (∃ nativeTime, (bank source).Executes data choices (configuration source digits c .check) nativeTime (.accepted word)) ↔
      ∃ sourceTime, sourceTime<FixedBitBlocks.decode digits ∧ source.Executes data choices c sourceTime (.accepted word) := by
  obtain ⟨time,_,reference,_⟩ := execution source data choices digits canonical c radius allBound
  constructor
  · rintro ⟨otherTime,run⟩
    have same := TapeBank.Executes.result_unique (bank source) reference run
    exact boundedResult_accepts source data choices (FixedBitBlocks.decode digits) c word same
  · rintro ⟨sourceTime,small,run⟩
    have same := boundedResult_of_executes source run (FixedBitBlocks.decode digits) small
    exact ⟨time,by simpa only [same] using reference⟩

include canonical allBound in
theorem prefix_bounded {ticks : ℕ} {finish : BankConfiguration O (Control Q) (Symbol S) (k+1)}
    (path : (bank source).Steps data choices (configuration source digits c .check) ticks finish) :
    (bank source).Bounded data (radius+2*digits.length+4) finish := by
  obtain ⟨_,_,_,run⟩ := execution source data choices digits canonical c radius allBound
  exact run.bounds_prefix (bank source) path

/-- The physical little-endian digits of the exponential clock. -/
def powerDigits (width : ℕ) : List Bool := List.replicate width false++[true]

theorem powerDigits_canonical (width : ℕ) : Canonical (powerDigits width) := by
  induction width with
  | zero => simp [powerDigits,Canonical]
  | succ width ih =>
    change Canonical (false::powerDigits width)
    exact (canonical_cons (by simp [powerDigits])).mpr ih

@[simp] theorem powerDigits_length (width : ℕ) : (powerDigits width).length=width+1 := by
  simp [powerDigits]

@[simp] theorem powerDigits_value (width : ℕ) : FixedBitBlocks.decode (powerDigits width)=2^width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    change 0+2*FixedBitBlocks.decode (powerDigits width)=2^(width+1)
    rw [ih,pow_succ]
    omega

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
