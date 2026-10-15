import ComplexityOfGenerators.Simulation.TransducerBank.SpaceRandom
import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-!
# Space preservation for the native tape-bank compiler

Every virtual head stays in a fixed interval. The compiler's physical scans
visit that same interval, independently of execution time and the number of
random bits. The theorem includes terminal successors and starts with the
native blank work tape. This applies to both simulations in Theorem 6.1.
-/

namespace ComplexityOfGenerators.Simulation.TransducerBank

namespace TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- A uniform radius for all configurations on all finite random tapes.
`Steps` includes a terminal configuration reached by the last transition. -/
def SpaceBound (data : InputData I A) (r : ℕ) : Prop :=
  ∀ bits t c, B.Steps data bits B.initialConfiguration t c → B.Bounded data r c

end TapeBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

/-- Compile a terminating execution while preserving a fixed work region.
The region does not grow with the number of simulated instructions. -/
theorem bank_simulates_inRegion (data : InputData I A) (bits : BitString)
    (source : BankConfiguration O Q S k) (t : ℕ) (result : Outcome O)
    (exec : B.Executes data bits source t result) (r : ℕ)
    (bounded : ∀ u c, B.Steps data bits source u c → B.Bounded data r c)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (related : BankReady B source negative start) (region : (bankMachine B).InRegion r start) :
    ∃ ticks finish, (bankMachine B).Steps data bits start ticks finish ∧
      (bankMachine B).observe data bits finish = .halted result ∧
      (bankMachine B).InRegion r finish := by
  induction exec generalizing negative start with
  | accept source table =>
      obtain ⟨finish, path, terminal, visited⟩ := bank_terminal_inRegion B data bits r source negative
        start related (bounded 0 source (.refl _)) region _ (Or.inl ⟨table, rfl⟩)
      exact ⟨_, finish, path, terminal, visited⟩
  | reject source table =>
      obtain ⟨finish, path, terminal, visited⟩ := bank_terminal_inRegion B data bits r source negative
        start related (bounded 0 source (.refl _)) region _ (Or.inr (Or.inl ⟨table, rfl⟩))
      exact ⟨_, finish, path, terminal, visited⟩
  | exhausted source no yes table absent =>
      obtain ⟨finish, path, terminal, visited⟩ := bank_terminal_inRegion B data bits r source negative
        start related (bounded 0 source (.refl _)) region _
          (Or.inr (Or.inr ⟨no, yes, table, absent, rfl⟩))
      exact ⟨_, finish, path, terminal, visited⟩
  | random source no yes bit t result table lookup rest ih =>
      have after : ∀ u c, B.Steps data bits (TapeBank.choose source (if bit then yes else no)) u c →
          B.Bounded data r c := by
        intro u c path
        exact bounded (u + 1) c (.random source no yes bit u c table lookup path)
      obtain ⟨ticks, ready, _, readyRelated, path, readyRegion⟩ :=
        bank_random_inRegion B data bits r source negative start related
          (bounded 0 source (.refl _)) no yes bit table lookup region
      obtain ⟨remaining, finish, tail, terminal, visited⟩ := ih after negative ready readyRelated readyRegion
      exact ⟨ticks + remaining, finish, path.trans _ tail, terminal, visited⟩
  | step source next write work input auxiliary index emit t result table rest ih =>
      have after : ∀ u c, B.Steps data bits
          (B.advance data source next write work input auxiliary index emit) u c → B.Bounded data r c := by
        intro u c path
        exact bounded (u + 1) c (.step source next write work input auxiliary index emit u c table path)
      obtain ⟨ticks, ready, sides, _, readyRelated, path, readyRegion⟩ :=
        bank_step_inRegion B data bits r source negative start related
          (bounded 0 source (.refl _)) next write work input auxiliary index emit table region
          (after 0 _ (.refl _))
      obtain ⟨remaining, finish, tail, terminal, visited⟩ := ih after sides ready readyRelated readyRegion
      exact ⟨ticks + remaining, finish, path.trans _ tail, terminal, visited⟩

/-- End-to-end space-preserving compilation, including initialization. -/
theorem bank_run_inRegion (data : InputData I A) (bits : BitString) (r t : ℕ)
    (result : Outcome O) (exec : B.Executes data bits B.initialConfiguration t result)
    (space : B.SpaceBound data r) :
    ∃ ticks finish,
      (bankMachine B).Steps data bits (bankMachine B).initialConfiguration ticks finish ∧
      (bankMachine B).observe data bits finish = .halted result ∧
      (bankMachine B).InRegion r finish := by
  obtain ⟨ready, related, boot, region⟩ := bank_loaded_inRegion B data bits r
  obtain ⟨ticks, finish, path, terminal, visited⟩ := bank_simulates_inRegion B data bits
    B.initialConfiguration t result exec r (space bits) (fun _ => false) ready related region
  exact ⟨1 + ticks, finish, boot.trans _ path, terminal, visited⟩

/-- A terminating bank with head radius `r` compiles to a native machine that
visits at most `2*r+1` cells. There is no time-bound or random-tape-length premise. -/
theorem bankMachine_spaceBound (data : InputData I A) (r : ℕ)
    (space : B.SpaceBound data r)
    (terminates : ∀ bits, ∃ t result, B.Executes data bits B.initialConfiguration t result) :
    (bankMachine B).SpaceBound data (2 * r + 1) := by
  apply Machine.spaceBound_of_terminal_paths
  intro bits
  obtain ⟨t, result, exec⟩ := terminates bits
  obtain ⟨ticks, finish, path, terminal, visited⟩ := bank_run_inRegion B data bits r t result exec space
  exact ⟨ticks, finish, result, path, terminal, visited.card_le _⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank
