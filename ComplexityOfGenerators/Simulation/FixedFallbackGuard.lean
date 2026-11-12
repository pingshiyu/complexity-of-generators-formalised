import ComplexityOfGenerators.Simulation.FixedFallbackBank
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

def fixedFallbackGuardConfiguration (q : FixedFallbackState S M fallback) (position : ℕ) :
    FixedFallbackConfiguration S M fallback :=
  {(fixedFallbackBank S M fallback).initialConfiguration with state := q, indexHead := position}

theorem fixedFallback_check_steps (n : ℕ) (bits : BitString) (steps remaining start : ℕ)
    (range : remaining ≤ fallback.length) (enough : steps ≤ remaining) (live : start + steps ≤ n) :
    (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (fixedFallbackGuardConfiguration S M fallback (.check ⟨remaining, by omega⟩) start) steps
      (fixedFallbackGuardConfiguration S M fallback (.check ⟨remaining - steps, by omega⟩) (start + steps)) := by
  induction steps generalizing remaining start with
  | zero =>
      simp only [Nat.sub_zero, Nat.add_zero]
      exact .refl _
  | succ steps ih =>
      have positive : remaining ≠ 0 := by omega
      have inside : start < n := by omega
      let c := fixedFallbackGuardConfiguration S M fallback (.check ⟨remaining, by omega⟩) start
      let d := fixedFallbackGuardConfiguration S M fallback (.check ⟨remaining - 1, by omega⟩) (start + 1)
      have table : (fixedFallbackBank S M fallback).instruction (generatorData n) c =
          .step (.check ⟨remaining - 1, by omega⟩) {} .stay .stay .stay .right none := by
        simp [c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.instruction,
          TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackTransition,
          fixedFallbackSelect, generatorData, positive, inside]
      have one := TransducerBank.TapeBank.Steps.single (fixedFallbackBank S M fallback)
        (generatorData n) bits c _ _ _ _ _ _ _ table
      have first : (fixedFallbackBank S M fallback).Steps (generatorData n) bits c 1 d := by
        simpa [c, d, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.advance,
          TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackSelect,
          Function.update_eq_self, Move.onInput, Move.onInt, generatorData,
          Nat.min_eq_left (show start + 1 ≤ n by omega)] using one
      have rest := ih (remaining - 1) (start + 1) (by omega) (by omega) (by omega)
      have path := first.trans (fixedFallbackBank S M fallback) rest
      have minus : remaining - 1 - steps = remaining - (steps + 1) := by omega
      have plus : start + 1 + steps = start + (steps + 1) := by omega
      simpa only [c, d, minus, plus, Nat.add_comm 1 steps] using path

theorem fixedFallback_rewind_steps (n : ℕ) (bits : BitString) (remaining start : ℕ)
    (range : remaining ≤ fallback.length) (inside : start + remaining ≤ n) :
    (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (fixedFallbackGuardConfiguration S M fallback (.rewind ⟨remaining, by omega⟩) (start + remaining))
      (remaining + 1)
      (fixedFallbackGuardConfiguration S M fallback (.source .load) start) := by
  induction remaining with
  | zero =>
      have table : (fixedFallbackBank S M fallback).instruction (generatorData n)
          (fixedFallbackGuardConfiguration S M fallback (.rewind 0) start) =
          .step (.source .load) {} .stay .stay .stay .stay none := by
        simp [fixedFallbackGuardConfiguration, TransducerBank.TapeBank.instruction,
          TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackTransition,
          fixedFallbackSelect]
      have one := TransducerBank.TapeBank.Steps.single (fixedFallbackBank S M fallback)
        (generatorData n) bits _ _ _ _ _ _ _ _ table
      simpa [fixedFallbackGuardConfiguration, TransducerBank.TapeBank.advance,
        TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackSelect,
        Function.update_eq_self, Move.onInput, Move.onInt, generatorData,
        Nat.min_eq_left (show start ≤ n by omega)] using one
  | succ remaining ih =>
      let c := fixedFallbackGuardConfiguration S M fallback (.rewind ⟨remaining + 1, by omega⟩) (start + (remaining + 1))
      let d := fixedFallbackGuardConfiguration S M fallback (.rewind ⟨remaining, by omega⟩) (start + remaining)
      have table : (fixedFallbackBank S M fallback).instruction (generatorData n) c =
          .step (.rewind ⟨remaining, by omega⟩) {} .stay .stay .stay .left none := by
        simp [c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.instruction,
          TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackTransition,
          fixedFallbackSelect]
      have one := TransducerBank.TapeBank.Steps.single (fixedFallbackBank S M fallback)
        (generatorData n) bits c _ _ _ _ _ _ _ table
      have first : (fixedFallbackBank S M fallback).Steps (generatorData n) bits c 1 d := by
        simpa [c, d, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.advance,
          TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackSelect,
          Function.update_eq_self, Move.onInput, Move.onInt, generatorData,
          Nat.min_eq_left (show start + remaining ≤ n by omega)] using one
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        first.trans (fixedFallbackBank S M fallback) (ih (by omega) (by omega))

theorem fixedFallback_boot (n : ℕ) (bits : BitString) (live : fallback.length ≤ n) :
    (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (fixedFallbackBank S M fallback).initialConfiguration (2 * fallback.length + 2)
      ((samplerCompositionBank S (auxiliaryDecision M)).initialConfiguration.mapState FixedFallbackPhase.source) := by
  have checked := fixedFallback_check_steps S M fallback n bits fallback.length fallback.length 0 le_rfl le_rfl (by simpa using live)
  let c := fixedFallbackGuardConfiguration S M fallback (.check 0) fallback.length
  let d := fixedFallbackGuardConfiguration S M fallback
    (.rewind ⟨fallback.length, Nat.lt_succ_self _⟩) fallback.length
  have table : (fixedFallbackBank S M fallback).instruction (generatorData n) c =
      .step (.rewind ⟨fallback.length, Nat.lt_succ_self _⟩) {} .stay .stay .stay .stay none := by
    simp [c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.instruction,
      TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackTransition,
      fixedFallbackSelect]
  have one := TransducerBank.TapeBank.Steps.single (fixedFallbackBank S M fallback)
    (generatorData n) bits c _ _ _ _ _ _ _ table
  have enter : (fixedFallbackBank S M fallback).Steps (generatorData n) bits c 1 d := by
    simpa [c, d, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.advance,
      TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackSelect,
      Function.update_eq_self, Move.onInput, Move.onInt, generatorData, Nat.min_eq_left live] using one
  have rewound := fixedFallback_rewind_steps S M fallback n bits fallback.length 0 le_rfl (by simpa using live)
  have checked' : (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (fixedFallbackBank S M fallback).initialConfiguration fallback.length c := by
    simpa [c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.initialConfiguration,
      fixedFallbackBank] using checked
  have rewound' : (fixedFallbackBank S M fallback).Steps (generatorData n) bits d
      (fallback.length + 1) (fixedFallbackGuardConfiguration S M fallback (.source .load) 0) := by
    simpa [d] using rewound
  have whole := (checked'.trans (fixedFallbackBank S M fallback) enter).trans (fixedFallbackBank S M fallback) rewound'
  simpa [fixedFallbackGuardConfiguration, TransducerBank.TapeBank.initialConfiguration,
    TransducerBank.BankConfiguration.mapState, fixedFallbackBank, samplerCompositionBank,
    Nat.mul_add, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using whole

theorem fixedFallback_below_steps (n : ℕ) (bits : BitString) (below : n < fallback.length) :
    (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (fixedFallbackBank S M fallback).initialConfiguration (n + 1)
      (fixedFallbackGuardConfiguration S M fallback .drain n) := by
  let B := fixedFallbackBank S M fallback
  let c := fixedFallbackGuardConfiguration S M fallback (.check ⟨fallback.length - n, by omega⟩) n
  let d := fixedFallbackGuardConfiguration S M fallback .drain n
  have checked := fixedFallback_check_steps S M fallback n bits n fallback.length 0 le_rfl (by omega) (by omega)
  have checked' : B.Steps (generatorData n) bits B.initialConfiguration n c := by
    simpa [B, c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.initialConfiguration,
      fixedFallbackBank] using checked
  have table : B.instruction (generatorData n) c = .step .drain {} .stay .stay .stay .stay none := by
    simp [B, c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.instruction,
      TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackTransition,
      fixedFallbackSelect, generatorData, Nat.ne_of_gt (show 0 < fallback.length - n by omega)]
  have one := TransducerBank.TapeBank.Steps.single B (generatorData n) bits c _ _ _ _ _ _ _ table
  have enter : B.Steps (generatorData n) bits c 1 d := by
    simpa [B, c, d, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.advance,
      TransducerBank.TapeBank.initialConfiguration, fixedFallbackBank, fixedFallbackSelect,
      Function.update_eq_self, Move.onInput, Move.onInt, generatorData] using one
  exact checked'.trans B enter

theorem fixedFallback_executes_below (n : ℕ) (bits : BitString) (below : n < fallback.length) :
    ∃ ticks, ticks ≤ n + bits.length + 1 ∧
      (fixedFallbackBank S M fallback).Executes (generatorData n) bits
        (fixedFallbackBank S M fallback).initialConfiguration ticks .exhausted := by
  let B := fixedFallbackBank S M fallback
  let d := fixedFallbackGuardConfiguration S M fallback .drain n
  obtain ⟨ticks, cost, drained⟩ := TransducerBank.TapeBank.drain_executes B (generatorData n) bits .drain
    (by intros; rfl) bits.length d rfl
    (by simp [d, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.initialConfiguration])
  exact ⟨n + 1 + ticks, by omega, (fixedFallback_below_steps S M fallback n bits below).executes B drained⟩

end
end ComplexityOfGenerators.Simulation
