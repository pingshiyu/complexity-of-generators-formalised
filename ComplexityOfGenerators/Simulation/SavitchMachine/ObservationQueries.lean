import ComplexityOfGenerators.Simulation.SavitchMachine.PrepareQuery
import ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.InputObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.IndexObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.HeadComparison

/-! A finite native program for the acceptance leaves. Each observation is
checked by five reusable, cache-restoring queries; candidate observations are
enumerated in finite control, independently of the input length. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ObservationQueries

open Turing StackSpace Frames BooleanTest Machine ConfigurationObservation
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α A O : Type} (M : Machine α A O) (space : PolynomialBound)

/-- An endpoint query may contain arbitrary, even malformed, configuration
bits. Its suspended parent column and input must fit the same radius. -/
structure Context where
  word : List α
  bits : List Bool
  parents : List (Alphabet α)
  radius : ℕ
  columnRoom : bits.length + 1 + parents.length ≤ radius
  rulerRoom : word.length + space word.length + 1 ≤ radius
  decoderRoom : ∀ f : HeaderField, 2 * f.width M.states word.length (space word.length) + 1 ≤ radius
  offsetRoom : ∀ f : HeaderField, f.offset M.states word.length ≤ radius

variable {M space}

def memory (x : Context M space) : Fin 8 → List (Alphabet α) :=
  Query.memory (Alphabet.input x.word)
    ((x.bits.map some).map Alphabet.write ++ Alphabet.write none :: x.parents)

theorem input_room (x : Context M space) : x.word.length ≤ x.radius := by
  have h := x.rulerRoom; omega

theorem bits_room (x : Context M space) : x.bits.length ≤ x.radius := by
  have h := x.columnRoom; omega

theorem work_room (x : Context M space) : 2 * space x.word.length + 1 ≤ x.radius := by
  have h := x.decoderRoom .work
  simp only [HeaderField.width] at h
  omega

theorem memory_bound (x : Context M space) (j : Fin 8) : (memory x j).length ≤ x.radius := by
  have hi := input_room x
  have hc := x.columnRoom
  fin_cases j <;> simp [memory, Query.memory, Alphabet.input] <;> omega

private theorem realize (P : Program (Alphabet α) 6) (value : Context M space → Bool)
    (executes : ∀ x answer, ∃ stk, Trace P.code x.radius
      (localConfig P.entry (carrying answer false) (Query.small x.bits (Alphabet.input x.word)))
      (localConfig P.exit (carrying answer (value x)) stk) ∧ stk 6 = Alphabet.input x.word) :
    Realizable Context.radius memory value := by
  refine ⟨Query.compile P, ?_⟩
  intro x answer
  exact Query.run P answer (value x) x.bits (Alphabet.input x.word) x.parents x.radius
    (by simpa [Alphabet.input] using input_room x) x.columnRoom (executes x answer)

private theorem prepared (mode : PrepareQuery.Mode) (P : Program (Alphabet α) 6)
    (value : Context M space → Bool)
    (hb : ∀ x : Context M space, mode.bound space x.word.length ≤ x.radius)
    (hf : ∀ x : Context M space, mode.first ≤ x.radius)
    (executes : ∀ x answer, ∃ stk, Trace P.code x.radius
      (localConfig P.entry (carrying answer false)
        (ReadCoordinateAt.before Alphabet.write x.bits
          ((BoundedDecode.unary mode.first).map Alphabet.write) (mode.bound space x.word.length) (Alphabet.input x.word)))
      (localConfig P.exit (carrying answer (value x)) stk) ∧ stk 6 = Alphabet.input x.word) :
    Realizable Context.radius memory value := by
  apply realize (PrepareQuery.compile space mode P) value
  intro x answer
  exact PrepareQuery.run space mode P x.bits (Alphabet.input x.word) answer (value x) x.radius
    (bits_room x) (by simpa [Alphabet.input] using input_room x)
    (by simpa [Alphabet.input] using x.rulerRoom) (by simpa [Alphabet.input] using work_room x)
    (by simpa [Alphabet.input] using hb x) (hf x) (by simpa only [Alphabet.input, List.length_map] using executes x answer)

variable (M space)

private def comparison (a b : ℕ) : Program (Alphabet α) 6 where
  Label := HeadComparison.Label
  finite := inferInstance
  entry := .read (.skip .copy)
  exit := .done
  code := HeadComparison.program Alphabet.write Alphabet.read a b .stay false
  exit_halts := rfl

theorem state_realizable (state : Fin M.states) :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => stateTest M state x.bits) := by
  apply prepared (.fixed M.states state.val) (comparison 0 0) _
  · intro x; have h := x.decoderRoom .state; simp only [HeaderField.width] at h; simp only [PrepareQuery.Mode.bound, PrepareQuery.Mode.first]; omega
  · intro x; have h := x.decoderRoom .state; have hs := state.isLt
    simp only [HeaderField.width] at h; simp only [PrepareQuery.Mode.bound, PrepareQuery.Mode.first]; omega
  · intro x answer
    have result := HeadComparison.run (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse
      0 0 .stay false answer x.bits (Alphabet.input x.word) state.val M.states x.radius state.isLt
      (bits_room x) (by simpa [Alphabet.input] using input_room x) (by simp)
      (by simpa [HeaderField.width] using x.decoderRoom .state)
    simpa [comparison, PrepareQuery.Mode.first, PrepareQuery.Mode.bound,
      stateTest, MoveCheck.destination, Fin.ext_iff, eq_comm] using result

theorem auxiliary_realizable :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => auxiliaryTest M x.word.length x.bits) := by
  apply prepared (.fixed 1 0) (comparison 1 (M.states + 1)) _
  · intro x; have h := x.decoderRoom .auxiliary; simp only [HeaderField.width] at h; simp only [PrepareQuery.Mode.bound, PrepareQuery.Mode.first]; omega
  · intro x; exact Nat.zero_le _
  · intro x answer
    have result := HeadComparison.run (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse
      1 (M.states + 1) .stay false answer x.bits (Alphabet.input x.word) 0 1 x.radius (by decide)
      (bits_room x) (by simpa [Alphabet.input] using input_room x)
      (by simpa [Alphabet.input, HeaderField.offset, HeaderField.coefficient, HeaderField.constant] using x.offsetRoom .auxiliary)
      (by simpa [HeaderField.width] using x.decoderRoom .auxiliary)
    have eq (v : Option (Fin 1)) : v.any (fun target => decide
        (MoveCheck.destination .stay false (1 - 1) 0 = some target.val)) = v.isSome := by
      cases v with
      | none => rfl
      | some f => simp [MoveCheck.destination, Fin.eq_zero f]
    simpa only [comparison, PrepareQuery.Mode.first, PrepareQuery.Mode.bound,
      Alphabet.input, List.length_map, Nat.one_mul, eq, auxiliaryTest] using result

variable [DecidableEq α]

private def inputQuery (expected : Option α) : Program (Alphabet α) 6 where
  Label := InputObservation.Label
  finite := inferInstance
  entry := .read (.skip .copy)
  exit := .done
  code := InputObservation.program M.states expected
  exit_halts := rfl

private def indexQuery (expected : Bool) : Program (Alphabet α) 6 where
  Label := IndexObservation.Label
  finite := inferInstance
  entry := .read (.skip .copy)
  exit := .done
  code := IndexObservation.program Alphabet.write Alphabet.read M.states expected
  exit_halts := rfl

private def workQuery (expected : Option (Fin M.symbols)) : Program (Alphabet α) 6 where
  Label := WorkObservation.Label M.symbols
  finite := inferInstance
  entry := .copyCode
  exit := .done
  code := WorkObservation.program Alphabet.write Alphabet.read M.states M.symbols expected
  exit_halts := rfl

theorem input_realizable (expected : Option α) :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => inputTest M x.word expected x.bits) := by
  apply prepared .input (inputQuery M expected) _
  · intro x; have h := x.decoderRoom .input; simp only [HeaderField.width] at h; simp only [PrepareQuery.Mode.bound, PrepareQuery.Mode.first]; omega
  · intro x; exact Nat.zero_le _
  · intro x answer
    exact InputObservation.run M.states expected answer x.bits x.word x.radius (bits_room x) (input_room x)
      (by simpa [HeaderField.offset, HeaderField.coefficient, HeaderField.constant] using x.offsetRoom .input)
      (x.decoderRoom .input)

theorem index_realizable (expected : Bool) :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => indexTest M x.word.length expected x.bits) := by
  apply prepared .input (indexQuery M expected) _
  · intro x; have h := x.decoderRoom .index; simp only [HeaderField.width] at h; simp only [PrepareQuery.Mode.bound, PrepareQuery.Mode.first]; omega
  · intro x; exact Nat.zero_le _
  · intro x answer
    have result := IndexObservation.run (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse M.states expected
        answer x.bits (Alphabet.input x.word) x.radius (bits_room x)
        (by simpa [Alphabet.input] using input_room x)
        (by simpa [Alphabet.input, HeaderField.offset, HeaderField.coefficient, HeaderField.constant] using x.offsetRoom .index)
        (by simpa [Alphabet.input, HeaderField.width] using x.decoderRoom .index)

    have inputLength : (Alphabet.input x.word).length = x.word.length := by simp [Alphabet.input]
    rw [inputLength] at result
    simpa only [indexQuery, PrepareQuery.Mode.first, PrepareQuery.Mode.bound, BoundedDecode.unary,
      List.replicate_zero, List.map_nil, indexTest] using result

theorem work_realizable (expected : Option (Fin M.symbols)) :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => WorkObservation.test M.states M.symbols x.word.length (2 * space x.word.length + 1) expected x.bits) := by
  apply prepared .work (workQuery M expected) _
  · exact work_room
  · intro x; exact Nat.zero_le _
  · intro x answer
    simpa only [Alphabet.input, List.length_map, workQuery, PrepareQuery.Mode.first, PrepareQuery.Mode.bound, BoundedDecode.unary, List.replicate_zero, List.map_nil] using
      WorkObservation.run (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse M.states M.symbols expected
        answer x.bits (Alphabet.input x.word) (2 * space x.word.length + 1) x.radius (bits_room x)
        (by simpa [Alphabet.input] using input_room x)
        (by simpa [Alphabet.input, HeaderField.offset, HeaderField.coefficient, HeaderField.constant] using x.offsetRoom .work)
        (x.decoderRoom .work)

theorem observation_realizable (o : Observation M) :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => test M x.word (space x.word.length) o x.bits) :=
  ((((state_realizable M space o.state).and (input_realizable M space o.input)).and
    (auxiliary_realizable M space)).and (index_realizable M space o.index)).and (work_realizable M space o.work)

/-- A completely finite acceptance-leaf program, with its original column and
input restored and every helper stack empty at return. -/
theorem accept_realizable [Fintype α] :
    Realizable (Context.radius (M := M) (space := space)) memory
      (fun x => M.spaceAcceptBase ⟨x.word, [], x.word.length⟩ (space x.word.length) x.bits) := by
  classical
  let accepts (o : Observation M) : Bool := match instruction M o with | .accept => true | _ => false
  have candidates := Realizable.exists (memory_bound (M := M) (space := space))
    (fun (o : Observation M) (x : Context M space) => test M x.word (space x.word.length) o x.bits && accepts o)
    (fun o => (observation_realizable M space o).and
      ⟨constant (accepts o), constant_correct _ _ _ memory_bound⟩)
  have eq : (fun x : Context M space => decide (∃ o : Observation M,
      (test M x.word (space x.word.length) o x.bits && accepts o) = true)) =
      (fun x => M.spaceAcceptBase ⟨x.word, [], x.word.length⟩ (space x.word.length) x.bits) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    exact (accept_iff M x.word (space x.word.length) x.bits).symm
  exact eq ▸ candidates

end
end ComplexityOfGenerators.Simulation.SavitchMachine.ObservationQueries
