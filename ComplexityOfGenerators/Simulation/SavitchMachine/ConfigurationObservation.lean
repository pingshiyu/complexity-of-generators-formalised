import ComplexityOfGenerators.Foundations.SpaceCodeFields
import ComplexityOfGenerators.Foundations.SpaceCodeLocal
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkObservation

/-! The finite observations needed to select a native transition. Separate
field queries validate the entire configuration encoding, including truncated
or malformed strings, before any transition is accepted. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationObservation

open Machine
set_option backward.isDefEq.respectTransparency false
variable {α A O : Type} (M : Machine α A O)

@[ext] structure Observation where
  state : Fin M.states
  input : Option α
  index : Bool
  work : Option (Fin M.symbols)
  deriving DecidableEq

instance [Fintype α] : Fintype (Observation M) :=
  Fintype.ofEquiv (Fin M.states × Option α × Bool × Option (Fin M.symbols))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun o => (o.state, o.input, o.index, o.work)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def instruction (o : Observation M) : Instruction O M.states M.symbols :=
  M.transition o.state o.input none (if o.index then some () else none) o.work

def observed (word : List α) (s : ℕ)
    (c : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s) : Observation M :=
  ⟨c.1, word[c.2.1.val]?, decide (c.2.2.2.1.val < word.length), c.2.2.2.2.2 c.2.2.2.2.1⟩

theorem observed_instruction (word : List α) (s : ℕ)
    (c : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s) :
    instruction M (observed M word s c) = M.spaceCodeInstruction ⟨word, [], word.length⟩ s c := by
  simp [instruction, observed, Machine.spaceCodeInstruction]

variable [DecidableEq α]

def stateTest (state : Fin M.states) (bits : List Bool) : Bool :=
  ((FixedWidthCodec.fin M.states).decode (bits.take M.states)).any (fun q => decide (q = state))

def auxiliaryTest (n : ℕ) (bits : List Bool) : Bool :=
  ((FixedWidthCodec.fin 1).decode ((bits.drop (n + (M.states + 1))).take 1)).isSome

def inputTest (word : List α) (expected : Option α) (bits : List Bool) : Bool :=
  ((FixedWidthCodec.fin (word.length + 1)).decode ((bits.drop M.states).take (word.length + 1))).any
    (fun head => decide ((word.drop head.val).head? = expected))

def indexTest (n : ℕ) (expected : Bool) (bits : List Bool) : Bool :=
  ((FixedWidthCodec.fin (n + 1)).decode ((bits.drop (n + (M.states + 2))).take (n + 1))).any
    (fun head => decide (decide (head.val < n) = expected))

def test (word : List α) (s : ℕ) (o : Observation M) (bits : List Bool) : Bool :=
  stateTest M o.state bits && inputTest M word o.input bits &&
    auxiliaryTest M word.length bits && indexTest M word.length o.index bits &&
    WorkObservation.test M.states M.symbols word.length (2 * s + 1) o.work bits

/-- The conjunction of the local queries is exactly a whole-code decode with
the specified finite observation. No well-formedness premise is imposed. -/
theorem test_correct (word : List α) (s : ℕ) (o : Observation M) (bits : List Bool) :
    test M word s o bits = true ↔
      ∃ c : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s,
        (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode bits = some c ∧ observed M word s c = o := by
  have offset : 2 * word.length + (M.states + 3) + (2 * s + 1) =
      M.states + 2 * word.length + 2 * s + 4 := by omega
  simp only [test, Bool.and_eq_true, stateTest, inputTest, auxiliaryTest, indexTest,
    Option.any_eq_true, decide_eq_true_eq, Option.isSome_iff_exists, WorkObservation.test_correct]
  constructor
  · rintro ⟨⟨⟨⟨⟨state, hs, hstate⟩, ⟨input, hi, hinput⟩⟩, ⟨aux, ha⟩⟩,
        ⟨index, hx, hindex⟩⟩, work, cells, hw, hc, hwork⟩
    let c : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s :=
      ⟨state, input, aux, index, work, cells⟩
    refine ⟨c, (M.spaceCodeCodec_decode_fields word s bits c).mpr ⟨?_, ?_⟩, ?_⟩
    · intro field; cases field <;>
        simpa [c, spaceCodeHeader, HeaderField.bits, HeaderField.offset,
          HeaderField.coefficient, HeaderField.constant, HeaderField.width] using
          (by assumption)
    · simpa only [offset] using hc
    · apply Observation.ext
      · exact hstate
      · simpa [observed, c] using hinput
      · exact hindex
      · exact hwork
  · rintro ⟨c, decoded, ho⟩
    subst o
    obtain ⟨headers, cells⟩ := (M.spaceCodeCodec_decode_fields word s bits c).mp decoded
    have hs := headers .state
    have hi := headers .input
    have ha := headers .auxiliary
    have hx := headers .index
    have hw := headers .work
    simp only [spaceCodeHeader, HeaderField.bits, HeaderField.offset,
      HeaderField.coefficient, HeaderField.constant, HeaderField.width,
      Nat.zero_mul, Nat.zero_add, Nat.one_mul, List.drop_zero] at hs hi ha hx hw
    refine ⟨⟨⟨⟨⟨c.1, hs, rfl⟩, ⟨c.2.1, hi, ?_⟩⟩, ⟨c.2.2.1, ha⟩⟩,
      ⟨c.2.2.2.1, hx, rfl⟩⟩, c.2.2.2.2.1, c.2.2.2.2.2, hw, ?_, rfl⟩
    · simp [observed]
    · simpa only [offset] using cells

/-- Finite enumeration of accepting observations suffices for the acceptance
leaf of the configuration search. -/
theorem accept_iff [Fintype α] (word : List α) (s : ℕ) (bits : List Bool) :
    M.spaceAcceptBase ⟨word, [], word.length⟩ s bits = true ↔
      ∃ o : Observation M, test M word s o bits = true ∧
        (match instruction M o with | .accept => true | _ => false) = true := by
  simp only [spaceAcceptBase, Option.any_eq_true, test_correct]
  constructor
  · rintro ⟨c, decoded, accepted⟩
    refine ⟨observed M word s c, ⟨c, decoded, rfl⟩, ?_⟩
    rw [observed_instruction]
    rw [M.spaceCodeAccepting_eq] at accepted
    cases action : M.spaceCodeInstruction ⟨word, [], word.length⟩ s c <;> simp_all
  · rintro ⟨o, ⟨c, decoded, rfl⟩, accepted⟩
    refine ⟨c, decoded, ?_⟩
    rw [observed_instruction] at accepted
    rw [M.spaceCodeAccepting_eq]
    cases action : M.spaceCodeInstruction ⟨word, [], word.length⟩ s c <;> simp_all

end ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationObservation
