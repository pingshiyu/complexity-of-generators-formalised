import ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.HeadRelation
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkRelation

/-! Fieldwise correctness of the native edge predicate. The auxiliary head is
always zero on the empty auxiliary tape. Read-only head moves clamp; work-head
moves must remain inside the encoded window. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationEdge

open Machine ConfigurationObservation
set_option backward.isDefEq.respectTransparency false
variable {α A O : Type} (M : Machine α A O)

structure Update where
  state : Fin M.states
  input : Move
  index : Move
  work : Move
  write : Option (Fin M.symbols)

variable {M}

def Update.Rel (action : Update M) (word : List α) (s : ℕ)
    (a b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s) : Prop :=
  b.1 = action.state ∧
  MoveCheck.destination action.input true word.length a.2.1.val = some b.2.1.val ∧
  MoveCheck.destination action.index true word.length a.2.2.2.1.val = some b.2.2.2.1.val ∧
  MoveCheck.destination action.work false (2 * s) a.2.2.2.2.1.val = some b.2.2.2.2.1.val ∧
  b.2.2.2.2.2 = Function.update a.2.2.2.2.2 a.2.2.2.2.1
    (WorkWindow.written M.symbols action.write (a.2.2.2.2.2 a.2.2.2.2.1))

variable (M)

def headTest (word : List α) (s : ℕ) (field : HeaderField) (direction : Move)
    (clamp : Bool) (u v : List Bool) : Bool :=
  HeadRelation.test field.coefficient (field.constant M.states) word.length
    (field.width M.states word.length s) direction clamp u v

theorem headTest_correct (word : List α) (s : ℕ) (field : HeaderField) (direction : Move)
    (clamp : Bool) (u v : List Bool) (a : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s)
    (source : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode u = some a) :
    headTest M word s field direction clamp u v = true ↔
      ∃ target : Fin (field.width M.states word.length s),
        (FixedWidthCodec.fin (field.width M.states word.length s)).decode
          (field.bits M.states word.length s v) = some target ∧
        MoveCheck.destination direction clamp (field.width M.states word.length s - 1)
          (M.spaceCodeHeader word s a field).val = some target.val := by
  have decoded := M.spaceCodeCodec_decode_header word s u a source field
  change (FixedWidthCodec.fin (field.width M.states word.length s)).decode
    ((u.drop (field.coefficient * word.length + field.constant M.states)).take
      (field.width M.states word.length s)) = some (M.spaceCodeHeader word s a field) at decoded
  simp only [headTest, HeadRelation.test, decoded, Option.any_some, Option.any_eq_true,
    decide_eq_true_eq, HeaderField.bits, HeaderField.offset]

theorem workTest_correct (word : List α) (s : ℕ) (old write : Option (Fin M.symbols))
    (u v : List Bool) (a : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s)
    (source : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode u = some a)
    (observed : a.2.2.2.2.2 a.2.2.2.2.1 = old) :
    WorkRelation.test M.states M.symbols word.length (2 * s + 1) old write u v = true ↔
      ∃ cells,
        ((FixedWidthCodec.optionFin M.symbols).vector (2 * s + 1)).decode
          (v.drop (M.states + 2 * word.length + 2 * s + 4)) = some cells ∧
        cells = Function.update a.2.2.2.2.2 a.2.2.2.2.1
          (WorkWindow.written M.symbols write (a.2.2.2.2.2 a.2.2.2.2.1)) := by
  obtain ⟨headers, window⟩ := (M.spaceCodeCodec_decode_fields word s u a).mp source
  have head := headers .work
  change (FixedWidthCodec.fin (2 * s + 1)).decode
    ((u.drop (2 * word.length + (M.states + 3))).take (2 * s + 1)) = some a.2.2.2.2.1 at head
  have offset : 2 * word.length + (M.states + 3) + (2 * s + 1) =
      M.states + 2 * word.length + 2 * s + 4 := by omega
  simp only [WorkRelation.test, head, Option.any_some, offset, WorkWindow.test_correct,
    window, Option.some.injEq]
  constructor
  · rintro ⟨a', b, rfl, hb, _, update⟩
    exact ⟨b, hb, update⟩
  · rintro ⟨b, hb, update⟩
    exact ⟨a.2.2.2.2.2, b, rfl, hb, observed, update⟩

/-- All target fields and the permitted single-cell update. The source's
finite observation is checked separately. -/
def targetTest (word : List α) (s : ℕ) (old : Option (Fin M.symbols))
    (action : Update M) (u v : List Bool) : Bool :=
  stateTest M action.state v && auxiliaryTest M word.length v &&
    headTest M word s .input action.input true u v &&
    headTest M word s .index action.index true u v &&
    headTest M word s .work action.work false u v &&
    WorkRelation.test M.states M.symbols word.length (2 * s + 1) old action.write u v

theorem targetTest_correct (word : List α) (s : ℕ) (old : Option (Fin M.symbols))
    (action : Update M) (u v : List Bool)
    (a : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s)
    (source : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode u = some a)
    (observed : a.2.2.2.2.2 a.2.2.2.2.1 = old) :
    targetTest M word s old action u v = true ↔
      ∃ b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s,
        (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode v = some b ∧ action.Rel word s a b := by
  simp only [targetTest, Bool.and_eq_true, stateTest, auxiliaryTest,
    Option.any_eq_true, decide_eq_true_eq, Option.isSome_iff_exists,
    headTest_correct M word s _ _ _ u v a source,
    workTest_correct M word s old action.write u v a source observed]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨state, hs, hstate⟩, ⟨aux, ha⟩⟩, ⟨input, hi, hinput⟩⟩,
      ⟨index, hx, hindex⟩⟩, ⟨work, hw, hwork⟩⟩, cells, hc, hcells⟩
    let b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s :=
      ⟨state, input, aux, index, work, cells⟩
    refine ⟨b, (M.spaceCodeCodec_decode_fields word s v b).mpr ⟨?_, hc⟩, ?_⟩
    · intro f
      cases f with
      | state => simpa [b, spaceCodeHeader, HeaderField.bits, HeaderField.offset,
          HeaderField.coefficient, HeaderField.constant, HeaderField.width] using hs
      | auxiliary => simpa [b, spaceCodeHeader, HeaderField.bits, HeaderField.offset,
          HeaderField.coefficient, HeaderField.constant, HeaderField.width] using ha
      | input => exact hi
      | index => exact hx
      | work => exact hw
    · exact ⟨hstate, by simpa [spaceCodeHeader, HeaderField.width] using hinput,
        by simpa [spaceCodeHeader, HeaderField.width] using hindex,
        by simpa [spaceCodeHeader, HeaderField.width] using hwork, hcells⟩
  · rintro ⟨b, decoded, hstate, hinput, hindex, hwork, hcells⟩
    obtain ⟨headers, cells⟩ := (M.spaceCodeCodec_decode_fields word s v b).mp decoded
    have hs := headers .state
    have ha := headers .auxiliary
    simp only [spaceCodeHeader, HeaderField.bits, HeaderField.offset, HeaderField.coefficient,
      HeaderField.constant, HeaderField.width, Nat.zero_mul, Nat.zero_add, Nat.one_mul, List.drop_zero] at hs ha
    refine ⟨⟨⟨⟨⟨⟨b.1, hs, hstate⟩, ⟨b.2.2.1, ha⟩⟩, ⟨b.2.1, headers .input, ?_⟩⟩,
      ⟨b.2.2.2.1, headers .index, ?_⟩⟩, ⟨b.2.2.2.2.1, headers .work, ?_⟩⟩,
      b.2.2.2.2.2, cells, hcells⟩
    · simpa [spaceCodeHeader, HeaderField.width] using hinput
    · simpa [spaceCodeHeader, HeaderField.width] using hindex
    · simpa [spaceCodeHeader, HeaderField.width] using hwork

/-- Equality and random steps keep all coordinates and work cells unchanged. -/
def stationary (state : Fin M.states) : Update M := ⟨state, .stay, .stay, .stay, none⟩

theorem stationary_rel (word : List α) (s : ℕ) (state : Fin M.states)
    (a b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s) :
    (stationary M state).Rel word s a b ↔ b.1 = state ∧ b.2 = a.2 := by
  have aux : b.2.2.1 = a.2.2.1 := by
    apply Fin.ext
    have ha := a.2.2.1.isLt
    have hb := b.2.2.1.isLt
    simp only [List.length_nil] at ha hb
    omega
  simp [stationary, Update.Rel, MoveCheck.destination, WorkWindow.written,
    Prod.ext_iff, aux, Fin.ext_iff, eq_comm]

theorem step_rel (word : List α) (s : ℕ) (choice : Bool)
    (a b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s)
    (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (action : M.spaceCodeInstruction ⟨word, [], word.length⟩ s a =
      .step state write work input auxiliary index emit) :
    (Update.mk state input index work write).Rel word s a b ↔
      M.spaceCodeAdvance ⟨word, [], word.length⟩ s choice a = some b := by
  rw [M.spaceCodeAdvance_step_iff _ s choice a b state write work input auxiliary index emit action]
  have inputBound : a.2.1.val ≤ word.length := Nat.le_of_lt_succ a.2.1.isLt
  have indexBound : a.2.2.2.1.val ≤ word.length := Nat.le_of_lt_succ a.2.2.2.1.isLt
  have sourceBound : a.2.2.2.2.1.val ≤ 2 * s := Nat.le_of_lt_succ a.2.2.2.2.1.isLt
  have targetBound : b.2.2.2.2.1.val ≤ 2 * s := Nat.le_of_lt_succ b.2.2.2.2.1.isLt
  have workEq : MoveCheck.destination work false (2 * s) a.2.2.2.2.1.val = some b.2.2.2.2.1.val ↔
      (b.2.2.2.2.1.val : ℤ) - s = work.onInt ((a.2.2.2.2.1.val : ℤ) - s) := by
    rw [MoveCheck.destination_strict work (2 * s) _ _ sourceBound targetBound]
    cases work <;> simp only [Move.onInt] <;> omega
  have aux : b.2.2.1.val = auxiliary.onInput 0 a.2.2.1.val := by
    have ah : a.2.2.1.val = 0 := by have h := a.2.2.1.isLt; simp only [List.length_nil] at h; omega
    have bh : b.2.2.1.val = 0 := by have h := b.2.2.1.isLt; simp only [List.length_nil] at h; omega
    rw [ah, bh]; cases auxiliary <;> rfl
  simp only [Update.Rel, MoveCheck.destination_clamped input _ _ inputBound,
    MoveCheck.destination_clamped index _ _ indexBound, Option.some.injEq, workEq,
    List.length_nil, aux, true_and, WorkWindow.written]
  cases write <;> simp_all [eq_comm]

/-- A finite choice selects equality or one of the two native successor edges.
Halting instructions have no successor candidate. -/
def candidate (o : Observation M) : Option Bool → Option (Update M)
  | none => some (stationary M o.state)
  | some choice => match instruction M o with
    | .accept | .reject => none
    | .readRandom no yes => some (stationary M (if choice then yes else no))
    | .step state write work input _ index _ => some ⟨state, input, index, work, write⟩

theorem candidate_rel (word : List α) (s : ℕ)
    (a b : M.SpaceCode (⟨word, [], word.length⟩ : InputData α A) s) (choice : Option Bool) :
    (∃ update, candidate M (observed M word s a) choice = some update ∧ update.Rel word s a b) ↔
      (match choice with | none => a = b | some bit => M.spaceCodeAdvance ⟨word, [], word.length⟩ s bit a = some b) := by
  cases choice with
  | none =>
      simp only [candidate, Option.some.injEq, exists_eq_left', observed, stationary_rel]
      simp [Prod.ext_iff, eq_comm]
  | some bit =>
      have action := observed_instruction M word s a
      cases instructionEq : instruction M (observed M word s a) with
      | accept =>
          have h := M.spaceCodeAdvance_halt ⟨word, [], word.length⟩ s bit a (Or.inl (action.symm.trans instructionEq))
          simp [candidate, instructionEq, h]
      | reject =>
          have h := M.spaceCodeAdvance_halt ⟨word, [], word.length⟩ s bit a (Or.inr (action.symm.trans instructionEq))
          simp [candidate, instructionEq, h]
      | readRandom no yes =>
          simp only [candidate, instructionEq, Option.some.injEq, exists_eq_left']
          rw [stationary_rel, M.spaceCodeAdvance_random_iff _ s bit a b no yes (action.symm.trans instructionEq)]
      | step state write work input auxiliary index emit =>
          simp only [candidate, instructionEq, Option.some.injEq, exists_eq_left']
          exact step_rel M word s bit a b state write work input auxiliary index emit (action.symm.trans instructionEq)

variable [DecidableEq α]

/-- The disjunction of finitely many observation/transition cases is exactly
zero-or-one-edge reachability, including rejection of invalid endpoint codes. -/
theorem reach_iff (word : List α) (s : ℕ) (u v : List Bool) :
    M.spaceReachBase ⟨word, [], word.length⟩ s u v = true ↔
      ∃ o : Observation M, ∃ choice : Option Bool,
        test M word s o u = true ∧
          (candidate M o choice).any (fun action => targetTest M word s o.work action u v) = true := by
  constructor
  · intro found
    obtain ⟨a, b, hu, hv, path⟩ := (M.spaceReachBase_correct ⟨word, [], word.length⟩ s u v).mp found
    have edge : a = b ∨ M.SpaceCodeEdge ⟨word, [], word.length⟩ s a b := by
      simpa [FiniteReachability.Within] using path
    obtain ⟨choice, chosen⟩ : ∃ choice : Option Bool,
        (match choice with | none => a = b | some bit => M.spaceCodeAdvance ⟨word, [], word.length⟩ s bit a = some b) := by
      rcases edge with same | ⟨bit, step⟩
      · exact ⟨none, same⟩
      · exact ⟨some bit, step⟩
    obtain ⟨update, hc, rel⟩ := (candidate_rel M word s a b choice).mpr chosen
    refine ⟨observed M word s a, choice, (test_correct M word s _ u).mpr ⟨a, hu, rfl⟩, ?_⟩
    rw [hc, Option.any_some]
    exact (targetTest_correct M word s _ update u v a hu rfl).mpr ⟨b, hv, rel⟩
  · rintro ⟨o, choice, valid, target⟩
    obtain ⟨a, hu, rfl⟩ := (test_correct M word s o u).mp valid
    simp only [Option.any_eq_true] at target
    obtain ⟨update, hc, passed⟩ := target
    obtain ⟨b, hv, rel⟩ := (targetTest_correct M word s _ update u v a hu rfl).mp passed
    have chosen := (candidate_rel M word s a b choice).mp ⟨update, hc, rel⟩
    apply (M.spaceReachBase_correct ⟨word, [], word.length⟩ s u v).mpr
    refine ⟨a, b, hu, hv, ?_⟩
    cases choice with
    | none => exact Or.inl chosen
    | some bit => exact Or.inr ⟨a, rfl, bit, chosen⟩

end ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationEdge
