import ComplexityOfGenerators.Simulation.StackSpace.Execution

/-! Loading the input, and iterating source steps in a fixed tape region. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Fintype Q]
variable (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
variable (word : List S) (bits : BitString)

local notation "B" => bank P entry initial answer
local notation "D" => decisionData word

/-- Reading left to right pushes the letters onto stack zero. -/
def inputStacks (word : List S) : Fin (k + 1) → List S :=
  Function.update (fun _ => []) 0 word.reverse

def sourceInitial (entry : Q) (initial : V) (word : List S) :
    TM2.Cfg (fun _ : Fin (k + 1) => S) Q V :=
  ⟨some entry, initial, inputStacks word⟩

def loading (P : Q → Stmt S Q V k) (front : List S) : Config P :=
  configuration P front.length .load (inputStacks front)

theorem load_letter (front : List S) (s : S) (rest : List S) :
    (B).Steps (decisionData (front ++ s :: rest)) bits (loading P front) 1 (loading P (front ++ [s])) := by
  classical
  have table : (B).instruction (decisionData (front ++ s :: rest)) (loading P front) =
      .step .load (some s) .right .right .stay .stay none := by
    simp [TransducerBank.TapeBank.instruction, bank, transition, loading, configuration, decisionData]
  have path := TransducerBank.TapeBank.Steps.single B _ bits _ _ _ _ _ _ _ _ table
  convert path using 1
  apply TransducerBank.BankConfiguration.ext
  all_goals simp [TransducerBank.TapeBank.advance, loading, configuration, bank, selected,
    Move.onInput, Move.onInt, decisionData, inputStacks, List.reverse_append]
  · funext j
    by_cases h : j = 0 <;> simp [h]
  · funext j
    by_cases h : j = 0 <;> simp [h, stackTape_cons]

theorem load_rest (front rest : List S) :
    (B).Steps (decisionData (front ++ rest)) bits (loading P front) (rest.length + 1)
      (ready P (front ++ rest).length (sourceInitial entry initial (front ++ rest))) := by
  induction rest generalizing front with
  | nil =>
      have h := TransducerBank.TapeBank.Steps.go B (decisionData front) bits (loading P front)
        (.exec (node P entry) initial) (by rfl) (by simp [loading, configuration, decisionData])
        (by simp [loading, configuration, decisionData]) (by
          simp [TransducerBank.TapeBank.instruction, bank, transition, loading, configuration, decisionData])
      simpa [loading, ready, sourceInitial, configuration] using h
  | cons s rest ih =>
      have first := load_letter P entry initial answer bits front s rest
      have tail := ih (front ++ [s])
      simp only [List.append_assoc, List.singleton_append] at tail
      simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using first.trans B tail

theorem load_initial :
    (B).Steps D bits (B).initialConfiguration (word.length + 1)
      (ready P word.length (sourceInitial entry initial word)) := by
  have h := load_rest P entry initial answer bits [] word
  have empty : loading P ([] : List S) = (B).initialConfiguration := by
    apply TransducerBank.BankConfiguration.ext
    all_goals simp [loading, configuration, inputStacks, TransducerBank.TapeBank.initialConfiguration, bank]
    funext j i
    simp
  simpa [empty] using h

/-- Arbitrarily many source steps reuse a single region. The space hypothesis
is on reachable source stack lengths, not on the number of steps. -/
theorem reaches_inRegion (s : ℕ) (start finish : TM2.Cfg (fun _ : Fin (k + 1) => S) Q V)
    (path : TM2.Reaches P start finish)
    (bounded : ∀ c, TM2.Reaches P start c → ∀ j, (c.stk j).length ≤ s) :
    ∃ ticks, (B).RegionSteps D bits (s + programCost P)
      (ready P word.length start) ticks (ready P word.length finish) := by
  induction path with
  | refl =>
      refine ⟨0, .refl _ ?_⟩
      exact (configuration_bounded P entry initial answer word _ _ s (bounded _ .refl)).mono B (by omega)
  | @tail c d path edge ih =>
      obtain ⟨ticks, first⟩ := ih
      obtain ⟨steps, last⟩ := step_inRegion P entry initial answer word bits s c d
        (by simpa only [Option.mem_def] using edge) (bounded c path)
      exact ⟨ticks + steps, first.trans B last⟩

/-- Complete execution, including input loading and the final verdict. -/
theorem run_inRegion (s : ℕ) (large : word.length + 1 ≤ s)
    (bounded : ∀ c, TM2.Reaches P (sourceInitial entry initial word) c → ∀ j, (c.stk j).length ≤ s)
    (finish : TM2.Cfg (fun _ : Fin (k + 1) => S) Q V)
    (path : TM2.Reaches P (sourceInitial entry initial word) finish) (halted : finish.l = none) :
    (B).RegionRun D bits (s + programCost P) (B).initialConfiguration
      (if answer finish.var then .accepted [] else .rejected) := by
  obtain ⟨ticks, run⟩ := reaches_inRegion P entry initial answer word bits s _ finish path bounded
  have load := (load_initial P entry initial answer word bits).inRegion B 0 ((B).initial_bounded D)
  have loaded := load.mono B (by omega : 0 + (word.length + 1) ≤ s + programCost P)
  refine ⟨word.length + 1 + ticks, ready P word.length finish, loaded.trans B run, ?_⟩
  cases h : answer finish.var with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply TransducerBank.TapeBank.Executes.reject
      simp [TransducerBank.TapeBank.instruction, ready, configuration, bank, transition, halted, h]
  | true =>
      simp only [↓reduceIte]
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, ready, configuration, bank, transition, halted, h]

end
end ComplexityOfGenerators.Simulation.StackSpace
