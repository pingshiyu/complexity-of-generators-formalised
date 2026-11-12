import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Basic

/-! Actual random-prefix collection and input-word loading for the filtered
inverse controller. The two extra input registers are outside the owned35
registers of the existing bounded-source preparation command. -/
namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

abbrev NativeMemory := Memory (Cell M W) α 37

def loadedMemory (data : InputData α α) : NativeMemory M W :=
  InputBank.loadedMemory 35 36 Symbol.letter Symbol.letter data

noncomputable def preparedMemory (seed : PolynomialBound) (data : InputData α α) (bits : BitString) : NativeMemory M W :=
  Memory.patch slots
    (BoundedSource.preparedMemory (O:=α) Symbol.unit Symbol.bit data.index (seed data.index) (bits.take (seed data.index)))
    (loadedMemory M W data)

def initialStore (seed : PolynomialBound) (n : ℕ) (input auxiliary : Word α) (bits : BitString) : Store M W :=
  Function.update
    (Function.update
      (BoundedSource.preparedMemory (O:=α) (Symbol.unit : Cell M W) Symbol.bit n (seed n) (bits.take (seed n))).store
      11 (letters M W input)) 12 (letters M W auxiliary)

def initialMemory (seed : PolynomialBound) (data : InputData α α) (bits : BitString) : Memory (Cell M W) α 35 :=
  ⟨(),data.index,seed data.index,[],initialStore M W seed data.index data.input data.auxiliary bits⟩

@[simp] theorem loaded_index (data : InputData α α) : (loadedMemory M W data).indexHead=0 := rfl

@[simp] theorem loaded_project (data : InputData α α) :
    (loadedMemory M W data).project slots=Command.emptyMemory := by
  apply Configuration.ext <;> try rfl
  funext j
  have h35 : slots j≠(35:Fin 37) := by intro eq;have h:=congrArg Fin.val eq;change j.val=35 at h;omega
  have h36 : slots j≠(36:Fin 37) := by intro eq;have h:=congrArg Fin.val eq;change j.val=36 at h;omega
  simp [loadedMemory,InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore,
    Memory.project,h35,h36]

@[simp] theorem prepared_low (seed : PolynomialBound) (data : InputData α α) (bits : BitString) (j : Fin 35) :
    (preparedMemory M W seed data bits).store (slots j)=
      (BoundedSource.preparedMemory (O:=α) Symbol.unit Symbol.bit data.index (seed data.index)
        (bits.take (seed data.index))).store j := by simp [preparedMemory,Memory.patch]

@[simp] theorem prepared_input (seed : PolynomialBound) (data : InputData α α) (bits : BitString) :
    (preparedMemory M W seed data bits).store 35=data.input.reverse.map Symbol.letter := by
  have outside : ∀ i : Fin 35,(35:Fin 37)≠slots i := by
    intro i eq;have h:=congrArg Fin.val eq;change 35=i.val at h;omega
  simp [preparedMemory,Memory.patch,Memory.patchStore_outside slots _ _ 35 outside,loadedMemory,
    InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore]

@[simp] theorem prepared_auxiliary (seed : PolynomialBound) (data : InputData α α) (bits : BitString) :
    (preparedMemory M W seed data bits).store 36=data.auxiliary.reverse.map Symbol.letter := by
  have outside : ∀ i : Fin 35,(36:Fin 37)≠slots i := by
    intro i eq;have h:=congrArg Fin.val eq;change 36=i.val at h;omega
  simp [preparedMemory,Memory.patch,Memory.patchStore_outside slots _ _ 36 outside,loadedMemory,
    InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore]

theorem prepare_runs (seed : PolynomialBound) (data : InputData α α) (bits : BitString) :
    ∃ ticks≤BoundedSource.prepareBudget seed data.index,
      ((BoundedSource.prepareCommand (O:=α) (Symbol.unit : Cell M W) Symbol.bit seed).rename slots).Runs
        data.index bits (loadedMemory M W data) ticks
        (if seed data.index≤bits.length then .done (preparedMemory M W seed data bits) else .exhausted) := by
  obtain ⟨ticks,bound,source⟩ := BoundedSource.prepare_runs (O:=α) (Symbol.unit : Cell M W) Symbol.bit seed data.index bits
  have renamed := source.rename slots (loadedMemory M W data)
  have same : Memory.patch slots Command.emptyMemory (loadedMemory M W data)=loadedMemory M W data :=
    Memory.patch_eq slots _ _ (loaded_project M W data)
  rw [same] at renamed
  refine ⟨ticks,bound,?_⟩
  split_ifs with enough
  · simpa [enough,Result.patch,preparedMemory] using renamed
  · simpa [enough,Result.patch] using renamed

def loadedWordsMemory (seed : PolynomialBound) (data : InputData α α) (bits : BitString) : NativeMemory M W :=
  {preparedMemory M W seed data bits with store:=(loadWords M W).eval (preparedMemory M W seed data bits).store}

theorem loadWords_cost (seed : PolynomialBound) (data : InputData α α) (bits : BitString) :
    (loadWords M W).cost (preparedMemory M W seed data bits).store=
      6*data.input.length+1+6*data.auxiliary.length := by
  simp [loadWords,Routine.seq,Routine.transfer,prepared_input,prepared_auxiliary]

theorem loadedWords_project (seed : PolynomialBound) (data : InputData α α) (bits : BitString) :
    (loadedWordsMemory M W seed data bits).project slots=initialMemory M W seed data bits := by
  apply Configuration.ext <;> try rfl
  funext j
  have h35 : slots j≠(35:Fin 37) := by intro eq;have h:=congrArg Fin.val eq;change j.val=35 at h;omega
  have h36 : slots j≠(36:Fin 37) := by intro eq;have h:=congrArg Fin.val eq;change j.val=36 at h;omega
  have eq11 : slots j=(11:Fin 37)↔j=11 := by
    constructor
    · intro eq;apply Fin.ext;exact congrArg (fun i : Fin 37=>i.val) eq
    · intro eq;subst j;rfl
  have eq12 : slots j=(12:Fin 37)↔j=12 := by
    constructor
    · intro eq;apply Fin.ext;exact congrArg (fun i : Fin 37=>i.val) eq
    · intro eq;subst j;rfl
  have low11 : (preparedMemory M W seed data bits).store (11:Fin 37)=[] := by
    change (preparedMemory M W seed data bits).store (slots 11)=[]
    rw [prepared_low]
    simp [BoundedSource.preparedMemory]
  have low12 : (preparedMemory M W seed data bits).store (12:Fin 37)=[] := by
    change (preparedMemory M W seed data bits).store (slots 12)=[]
    rw [prepared_low]
    simp [BoundedSource.preparedMemory]
  by_cases a : j=11
  · subst j
    simp [loadedWordsMemory,Memory.project,initialMemory,initialStore,loadWords,Routine.seq,Routine.transfer,
      slots,prepared_input,prepared_auxiliary,low11,low12,BoundedSource.preparedMemory,letters]
  · by_cases b : j=12
    · subst j
      simp [loadedWordsMemory,Memory.project,initialMemory,initialStore,loadWords,Routine.seq,Routine.transfer,
        slots,prepared_input,prepared_auxiliary,low11,low12,BoundedSource.preparedMemory,letters]
    · simp [loadedWordsMemory,Memory.project,initialMemory,initialStore,loadWords,Routine.seq,Routine.transfer,
        Function.update_apply,h35,h36,eq11,eq12,a,b,prepared_low]

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
