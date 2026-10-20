import ComplexityOfGenerators.Simulation.WordStack.SourceCorrectness

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Zipper

variable {A : Type}

def size (z : Zipper A) : ℕ := z.left.length + z.right.length

theorem size_eq_word (z : Zipper A) : z.size = z.word.length := by simp [size, word]

@[simp] theorem clampedMove_size (z : Zipper A) (dir : Move) : (z.clampedMove dir).size = z.size := by
  simp only [size_eq_word, clampedMove_word]

theorem workMove_size (z : Zipper A) (blank : A) (dir : Move) :
    (z.workMove blank dir).size ≤ z.size + 1 := by
  cases dir <;> cases hl : z.left <;> cases hr : z.right <;> simp [workMove, size, hl, hr] <;> omega

theorem write_size (z : Zipper A) (a : A) : (z.write a).size ≤ z.size + 1 := by
  cases hr : z.right <;> simp [write, size, hr] <;> omega

end Zipper

namespace Source

variable {I A O : Type} (M : Machine I A O)

namespace Snapshot

def size (c : Snapshot M) : ℕ :=
  1 + c.input.size + c.auxiliary.size + c.index.size + c.work.size + c.random.length + c.output.length

theorem step_size (c : Snapshot M) : (c.step M).size ≤ c.size + 3 := by
  cases state : c.status with
  | accepted | rejected | exhausted => simp [step, state]
  | live q =>
    simp only [step, state]
    cases action : M.transition q c.input.read c.auxiliary.read c.index.read (c.work.read.getD none) with
    | accept | reject => simp [size]
    | readRandom no yes => cases random : c.random <;> simp [size, random] <;> omega
    | step q write wm im am nm emit =>
      have workbound : ((match write with | none => c.work | some a => c.work.write (some a)).workMove none wm).size ≤
          c.work.size + 2 := by
        cases write with
        | none => exact (c.work.workMove_size none wm).trans (by omega)
        | some a =>
          have h₁ := (c.work.write (some a)).workMove_size none wm
          have h₂ := c.work.write_size (some a)
          dsimp
          omega
      cases emit <;> cases write <;>
        simp only [size, Zipper.clampedMove_size, List.length_cons] at * <;> omega

theorem iterate_size (c : Snapshot M) (t : ℕ) : ((step M)^[t] c).size ≤ c.size + 3 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have bound := step_size M ((step M)^[t] c)
    rw [Function.iterate_succ_apply']
    omega

theorem step_output_length (c : Snapshot M) : (c.step M).output.length ≤ c.output.length + 1 := by
  cases state : c.status with
  | accepted | rejected | exhausted => simp [step, state]
  | live q =>
    simp only [step, state]
    cases action : M.transition q c.input.read c.auxiliary.read c.index.read (c.work.read.getD none) with
    | accept | reject => simp
    | readRandom no yes => cases c.random <;> simp
    | step q write wm im am nm emit => cases emit <;> simp

theorem iterate_output_length (c : Snapshot M) (t : ℕ) :
    ((step M)^[t] c).output.length ≤ c.output.length + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have bound := step_output_length M ((step M)^[t] c)
    omega

theorem store_length_le (c : Snapshot M) (j : Fin 11) : (c.store M j).length ≤ c.size := by
  fin_cases j <;> simp [store, size, Zipper.size] <;> omega

def acceptedOutput (c : Snapshot M) : Option (List O) :=
  match c.status with | .accepted => some c.output.reverse | _ => none

end Snapshot

theorem initial_size (data : InputData I A) (bits : BitString) :
    (initial M data bits).size = 1 + data.input.length + data.auxiliary.length + data.index + bits.length := by
  simp [initial, Snapshot.size, Zipper.size]

theorem iterate_accept_iff (data : InputData I A) (bits : BitString) (time : ℕ) (word : List O) :
    (((Snapshot.step M)^[time + 1] (initial M data bits)).acceptedOutput = some word) ↔
      M.run data bits time = .halted (.accepted word) := by
  constructor
  · intro accepted
    have h := iterate_related M data bits (time + 1)
    cases raw : M.rawRun data bits (.running M.initialConfiguration) (time + 1) with
    | running c =>
      rw [raw] at h
      have state := h.state
      simp only [Snapshot.acceptedOutput, state, reduceCtorEq] at accepted
    | halted outcome =>
      rw [raw] at h
      cases outcome with
      | rejected => simp only [Snapshot.acceptedOutput, show _ = Status.rejected from h, reduceCtorEq] at accepted
      | exhausted => simp only [Snapshot.acceptedOutput, show _ = Status.exhausted from h, reduceCtorEq] at accepted
      | accepted output =>
        have equal : output = word := by simpa only [Snapshot.acceptedOutput, h.1, h.2, List.reverse_reverse, Option.some.injEq] using accepted
        subst output
        simpa using (M.rawRun_correct data bits M.initialConfiguration time (.accepted word)).mp raw
  · intro run
    obtain ⟨state, output⟩ := iterate_accept M data bits time word run
    simp only [Snapshot.acceptedOutput, state, output, List.reverse_reverse]

end Source
end ComplexityOfGenerators.Simulation.WordStack
