import ComplexityOfGenerators.Simulation.IndexInputReset
import ComplexityOfGenerators.Simulation.OutputMatcher
import ComplexityOfGenerators.Simulation.ClockLoader

/-! The native recognizer underlying `PG ⊆ NP`: load an exact unary virtual
index, restore the input head, simulate the generator, and compare its output
against the input word. Clocking is applied after this construction. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def wordIndexBlocks : InputBlocks α (IndexCell M.symbols) where
  leading := [indexInitialCell M]
  trailing := []
  block := fun _ => [indexLiveCell M]

omit [Fintype α] in
@[simp] theorem wordIndexBlocks_word (w : List α) :
    (wordIndexBlocks M).word w = indexInitialCell M :: List.replicate w.length (indexLiveCell M) := by
  have flat : w.flatMap (fun _ => [indexLiveCell M]) = List.replicate w.length (indexLiveCell M) := by
    induction w <;> simp_all [List.replicate_succ]
  simp [InputBlocks.word, wordIndexBlocks, flat]

def wordIndexLoader : Machine α Bool Unit :=
  blockMachine (indexLoaderProgram M) (Fintype.equivFin Unit) (indexAlphabet M) (wordIndexBlocks M)

def wordIndexPreparedLoader : Machine α Bool Unit :=
  sequenceMachine (wordIndexLoader M) (machineRoutine (indexInputReset M))

def generatorMatcherRoutine := machineRoutine (outputMatcher (virtualIndexCore M))

def generatorRecognizer : Machine α Bool Unit :=
  sequenceMachine (wordIndexPreparedLoader M) (generatorMatcherRoutine M)

end

end ComplexityOfGenerators.Simulation
