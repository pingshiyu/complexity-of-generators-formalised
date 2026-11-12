import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped.Rewind

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k) (counter : Fin k)

theorem oversized_prefix (data : InputData I A) (bits : BitString)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    ∃ side ticks, ticks ≤ 3 * data.index + 3 ∧
      (bank B counter).Steps data bits (bank B counter).initialConfiguration ticks
        (state B counter .drain side data.index) := by
  by_cases first : data.index < data.input.length
  · have scan := scan_prefix B counter data bits false data.index (by exact Nat.le_of_lt first) le_rfl
    have reject := scan_oversize B counter data bits false first
    refine ⟨false, data.index + 1, by omega, ?_⟩
    simpa only [initial_state] using scan.trans _ reject
  · have short : data.input.length ≤ data.index := by omega
    have earlier := check_short B counter data bits false short
    have second : data.index < data.auxiliary.length := oversized.resolve_left first
    have scan := scan_prefix B counter data bits true data.index (by exact Nat.le_of_lt second) le_rfl
    have reject := scan_oversize B counter data bits true second
    have middle : state (O := O) B counter (.scan true) false 0 =
        state B counter (.scan true) true 0 := by simp [state]
    refine ⟨true, 2 * data.input.length + 2 + (data.index + 1), by omega, ?_⟩
    simpa only [wordLength, Bool.false_eq_true, ite_false, middle, initial_state] using
      earlier.trans _ (scan.trans _ reject)

theorem oversized_executes (data : InputData I A) (bits : BitString)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    ∃ ticks, ticks ≤ 3 * data.index + 3 + bits.length ∧
      (bank B counter).Executes data bits (bank B counter).initialConfiguration ticks .exhausted := by
  obtain ⟨side, ticks, prefixBound, path⟩ := oversized_prefix B counter data bits oversized
  obtain ⟨drainTicks, drainBound, drain⟩ := TapeBank.drain_executes (bank B counter) data bits .drain
    (by intros; rfl) bits.length (state B counter .drain side data.index) rfl (by simp [state])
  exact ⟨ticks + drainTicks, by omega, path.executes _ drain⟩

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
