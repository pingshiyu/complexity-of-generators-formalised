import ComplexityOfGenerators.Simulation.SavitchMachine.Initialize

/-! Keep language input letters distinct from the interpreter's binary fields
and delimiters. The original input is one symbol per cell, so its length and
read-only head coordinates are unchanged. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

abbrev Alphabet (α : Type) := Sum α Frames.Symbol

namespace Alphabet

open Turing StackSpace Frames Complexity
variable {α : Type}

instance : Inhabited (Alphabet α) := ⟨Sum.inr none⟩

def write : Symbol → Alphabet α := Sum.inr
def read : Alphabet α → Symbol := Sum.elim (fun _ => none) id

theorem inverse : Function.LeftInverse (read (α := α)) write := fun _ => rfl

def input (word : List α) : List (Alphabet α) := word.map Sum.inl

/-- A search configuration with native input letters on the persistent stack
and encoded binary symbols on all frame and cache stacks. -/
def encoded {Q : Type} (word : List α) (q : Q) (s : Sav.Sst) :
    Source (Alphabet α) Q (Status × Option (Alphabet α)) 12 :=
  extendConfig (input word) (localConfig q (status s)
    (fun j => (memory s.stk (fun _ => []) j).map write))

theorem encoded_bound {Q : Type} (word : List α) (q : Q) (s : Sav.Sst) (r : ℕ)
    (inputRoom : word.length ≤ r) (bound : ∀ j, (column s.stk j).length ≤ r) :
    Within r (encoded word q s) := by
  apply extend_bound
  · intro j
    simpa [localConfig] using memory_bound s.stk r bound j
  · simpa [input] using inputRoom

end Alphabet
end ComplexityOfGenerators.Simulation.SavitchMachine
