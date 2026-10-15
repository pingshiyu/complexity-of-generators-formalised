import ComplexityOfGenerators.Simulation.SavitchMachine.ObservationQueries
import ComplexityOfGenerators.Simulation.SavitchMachine.PairQuery
import ComplexityOfGenerators.Simulation.SavitchMachine.HeadRelation
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkRelation

/-! Cache-restoring native predicates on two configuration endpoints. These
share the input and parent columns with the single-endpoint observation tests. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.PairQueries

open Turing StackSpace Frames BooleanTest Machine ConfigurationObservation
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α A O : Type} (M : Machine α A O) (space : PolynomialBound)

structure Context where
  source : ObservationQueries.Context M space
  target : List Bool
  parents : List (Alphabet α)
  targetRoom : target.length + 1 + parents.length ≤ source.radius

variable {M space}

def Context.column (x : Context M space) : List (Alphabet α) :=
  (x.target.map some).map Alphabet.write ++ Alphabet.write none :: x.parents

def Context.targetContext (x : Context M space) : ObservationQueries.Context M space :=
  { x.source with bits := x.target, parents := x.parents, columnRoom := x.targetRoom }

def memory (x : Context M space) : Fin 9 → List (Alphabet α) :=
  PairQuery.memory (Alphabet.input x.source.word)
    ((x.source.bits.map some).map Alphabet.write ++ Alphabet.write none :: x.source.parents) x.column

def radius (x : Context M space) : ℕ := x.source.radius

theorem column_room (x : Context M space) : x.column.length ≤ radius x := by
  have bound := x.targetRoom
  simp only [Context.column, List.length_append, List.length_map, List.length_cons]
  exact by dsimp [radius]; omega

theorem memory_bound (x : Context M space) (j : Fin 9) : (memory x j).length ≤ radius x := by
  have a := x.source.columnRoom
  have b := column_room x
  have c := ObservationQueries.input_room x.source
  fin_cases j <;> simp [memory, PairQuery.memory, Alphabet.input, radius] at * <;> omega

/-- Lift a single-endpoint predicate to the source or target of a pair. -/
theorem lift_source {value : ObservationQueries.Context M space → Bool}
    (h : Realizable ObservationQueries.Context.radius ObservationQueries.memory value) :
    Realizable radius memory (fun x : Context M space => value x.source) := by
  have selected := h.comap Context.source
  apply selected.embed ⟨Fin.castSucc, Fin.castSucc_injective 8⟩ memory
  · intro x j; fin_cases j <;> rfl
  · exact memory_bound

theorem lift_target {value : ObservationQueries.Context M space → Bool}
    (h : Realizable ObservationQueries.Context.radius ObservationQueries.memory value) :
    Realizable radius memory (fun x : Context M space => value x.targetContext) := by
  have selected := h.comap Context.targetContext
  apply selected.embed PairQuery.slots memory
  · intro x j; fin_cases j <;> rfl
  · exact memory_bound

private theorem prepared (mode : PrepareQuery.Mode) (P : Program (Alphabet α) 7)
    (value : Context M space → Bool) (zero : mode.first = 0)
    (cap : ∀ x : Context M space, mode.bound space x.source.word.length ≤ radius x)
    (executes : ∀ x answer, ∃ stk, Trace P.code (radius x)
      (localConfig P.entry (carrying answer false)
        (Fin.snoc (ReadCoordinateAt.before Alphabet.write x.source.bits []
          (mode.bound space x.source.word.length) (Alphabet.input x.source.word)) x.column))
      (localConfig P.exit (carrying answer (value x)) stk) ∧
        stk 6 = Alphabet.input x.source.word ∧ stk 7 = x.column) :
    Realizable radius memory value := by
  let prep := PrepareQuery.compile space mode (constant (S := Alphabet α) (k := 6) false)
  let body := chain (BooleanTest.extend prep) P
  refine ⟨PairQuery.compile body, ?_⟩
  intro x answer
  apply PairQuery.run body answer (value x) x.source.bits (Alphabet.input x.source.word)
    x.source.parents x.column (radius x)
    (by simpa [radius, Alphabet.input] using ObservationQueries.input_room x.source)
    x.source.columnRoom (column_room x)
  let ready := ReadCoordinateAt.before (Alphabet.write (α := α)) x.source.bits []
    (mode.bound space x.source.word.length) (Alphabet.input x.source.word)
  have readyBound : ∀ j, (ready j).length ≤ radius x := by
    have bitsRoom := ObservationQueries.bits_room x.source
    have inputRoom := ObservationQueries.input_room x.source
    have boundRoom := cap x
    intro j; fin_cases j <;> simp [ready, ReadCoordinateAt.before, Alphabet.input, radius] at * <;> omega
  have build := PrepareQuery.trace space mode (constant (S := Alphabet α) (k := 6) false)
    x.source.bits (Alphabet.input x.source.word) answer false (radius x)
    (ObservationQueries.bits_room x.source)
    (by simpa [radius, Alphabet.input] using ObservationQueries.input_room x.source)
    (by simpa [radius, Alphabet.input] using x.source.rulerRoom)
    (by simpa [radius, Alphabet.input] using ObservationQueries.work_room x.source)
    (by simpa [radius, Alphabet.input] using cap x) (by rw [zero]; omega) ready (by
      have len : (Alphabet.input x.source.word).length = x.source.word.length := by simp [Alphabet.input]
      rw [len, zero]
      change Trace (constant (S := Alphabet α) (k := 6) false).code (radius x)
        (localConfig false (carrying answer false) ready) (localConfig true (carrying answer false) ready)
      exact .step readyBound rfl (.refl _ readyBound))
  obtain ⟨stk, traced, inputPreserved, targetPreserved⟩ := executes x answer
  have first := build.extend x.column (column_room x)
  refine ⟨stk, ?_, inputPreserved, targetPreserved⟩
  exact chain_trace (BooleanTest.extend prep) P (radius x) (carrying answer false)
    (carrying answer false) (carrying answer (value x)) _ _ _ first traced

variable (M space)

private def headProgram (field : HeaderField) (direction : Move) (clamp : Bool) : Program (Alphabet α) 7 where
  Label := HeadRelation.Label
  finite := inferInstance
  entry := .read (.skip .copy)
  exit := .done
  code := HeadRelation.program field.coefficient (field.constant M.states) direction clamp
  exit_halts := rfl

private def mode : HeaderField → PrepareQuery.Mode
  | .state => .fixed M.states 0
  | .auxiliary => .fixed 1 0
  | .input | .index => .input
  | .work => .work

private theorem mode_bound (field : HeaderField) (n : ℕ) :
    (mode M field).bound space n = field.width M.states n (space n) := by cases field <;> rfl

/-- The exact native head relation, on arbitrary source and target encodings. -/
theorem head_realizable (field : HeaderField) (direction : Move) (clamp : Bool) :
    Realizable (radius (M := M) (space := space)) memory (fun x =>
      HeadRelation.test field.coefficient (field.constant M.states) x.source.word.length
        (field.width M.states x.source.word.length (space x.source.word.length)) direction clamp
        x.source.bits x.target) := by
  apply prepared (mode M field) (headProgram M field direction clamp) _
  · cases field <;> rfl
  · intro x
    rw [mode_bound]
    have h := x.source.decoderRoom field
    dsimp only [radius]
    omega
  · intro x answer
    have h := HeadRelation.run field.coefficient (field.constant M.states) direction clamp answer
      x.source.bits x.target (Alphabet.input x.source.word) x.parents
      (field.width M.states x.source.word.length (space x.source.word.length)) (radius x)
      (ObservationQueries.bits_room x.source)
      (by simpa [radius, Alphabet.input] using ObservationQueries.input_room x.source) x.targetRoom
      (by simpa [radius, Alphabet.input, HeaderField.offset] using x.source.offsetRoom field)
      (x.source.decoderRoom field)
    have len : (Alphabet.input x.source.word).length = x.source.word.length := by simp [Alphabet.input]
    rw [len] at h
    simpa only [headProgram, mode_bound, Context.column] using h

private def workProgram (observed write : Option (Fin M.symbols)) : Program (Alphabet α) 7 where
  Label := WorkRelation.Label M.symbols
  finite := inferInstance
  entry := .copyCode
  exit := .done
  code := WorkRelation.program M.states M.symbols observed write
  exit_halts := rfl

/-- The exact native single-cell write relation on the two work windows. -/
theorem work_realizable (observed write : Option (Fin M.symbols)) :
    Realizable (radius (M := M) (space := space)) memory (fun x =>
      WorkRelation.test M.states M.symbols x.source.word.length (2 * space x.source.word.length + 1)
        observed write x.source.bits x.target) := by
  apply prepared .work (workProgram M observed write) _ rfl
  · exact fun x => ObservationQueries.work_room x.source
  · intro x answer
    have h := WorkRelation.run M.states M.symbols observed write answer x.source.bits x.target
      (Alphabet.input x.source.word) x.parents (2 * space x.source.word.length + 1) (radius x)
      (ObservationQueries.bits_room x.source)
      (by simpa [radius, Alphabet.input] using ObservationQueries.input_room x.source) x.targetRoom
      (by simpa [radius, Alphabet.input, HeaderField.offset, HeaderField.coefficient, HeaderField.constant] using x.source.offsetRoom .work)
      (x.source.decoderRoom .work)
    have len : (Alphabet.input x.source.word).length = x.source.word.length := by simp [Alphabet.input]
    rw [len] at h
    simpa only [workProgram, PrepareQuery.Mode.bound, Context.column] using h

end
end ComplexityOfGenerators.Simulation.SavitchMachine.PairQueries
