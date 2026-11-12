import ComplexityOfGenerators.Simulation.WordStack.EventReturns
import ComplexityOfGenerators.Simulation.WordStack.EventCompilation
import ComplexityOfGenerators.Simulation.NativeEventTraceAppend
import ComplexityOfGenerators.Simulation.TransducerBank.TerminalSnapshot

namespace ComplexityOfGenerators.Simulation.WordStack.Program
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Q S E : Type} {k : ℕ} [Fintype Q] [Fintype S] [Fintype E]
    {P : Program Q S E k} {slot exported : Fin k} {symbol : S} {Allowed : E→ℕ→Prop}
    {n : ℕ} {bits : BitString} {events : List (E×ℕ)} {source finish : Memory S E k}

theorem EventTrace.native_terminal
    (parameter : E→Option (Fin P.machine.symbols)→Bool)
    (correct : ∀ (e : E) (j : ℕ) (store : Fin k→List S) (heads : Fin k→Option ℤ) (memory),
      Allowed e j → store exported=List.replicate (j-1) symbol →
      BankMemory P.bank (fun i=>tape (store i)) heads memory →
      ∀ position : ℕ, parameter e (memory position)=decide (position<j))
    {first lastWord : Configuration Q S E k}
    (trace : P.EventTrace slot exported symbol Allowed n bits events first lastWord)
    (terminal : P.instruction n lastWord=.accept)
    (indexBound : first.indexHead≤n) (negative : Fin k→Bool)
    (start : ComplexityOfGenerators.Configuration P.machine)
    (ready : BankReady P.bank (P.encoded first) negative start) :
    ∃ last, P.machine.NativeEventTrace parameter Allowed (generatorData n) bits events start last ∧
      P.machine.observe (generatorData n) bits last=.halted (.accepted lastWord.output) ∧
      last.randomHead=lastWord.randomHead ∧ last.output=lastWord.output := by
  obtain ⟨next,sides,nextReady,instrumented⟩ := trace.native parameter correct indexBound negative start ready
  obtain ⟨t,wordPath⟩ := trace.steps
  have finishIndex : lastWord.indexHead≤n := wordPath.index_le P indexBound
  have bankTerminal := P.encoded_instruction n lastWord
  rw [terminal] at bankTerminal
  obtain ⟨last,tail,snapshot,accepted⟩ := bank_accepting_path P.bank (generatorData n) bits _
    (P.encoded lastWord) sides next nextReady (P.encoded_bounded n lastWord finishIndex) bankTerminal
  exact ⟨last,instrumented.append tail (snapshot.output.trans nextReady.output.symm),accepted,snapshot.random,snapshot.output⟩

theorem EventReturns.native
    (parameter : E→Option (Fin P.machine.symbols)→Bool)
    (correct : ∀ (e : E) (j : ℕ) (store : Fin k→List S) (heads : Fin k→Option ℤ) (memory),
      Allowed e j → store exported=List.replicate (j-1) symbol →
      BankMemory P.bank (fun i=>tape (store i)) heads memory →
      ∀ position : ℕ, parameter e (memory position)=decide (position<j))
    (run : P.EventReturns slot exported symbol Allowed n bits events source finish)
    (indexBound : source.indexHead≤n) (negative : Fin k→Bool)
    (start : ComplexityOfGenerators.Configuration P.machine)
    (ready : BankReady P.bank (P.encoded (source.at P.initial)) negative start) :
    ∃ last, P.machine.NativeEventTrace parameter Allowed (generatorData n) bits events start last ∧
      P.machine.observe (generatorData n) bits last=.halted (.accepted finish.output) ∧
      last.randomHead=finish.randomHead ∧ last.output=finish.output := by
  obtain ⟨q,trace,terminal⟩ := run
  exact trace.native_terminal parameter correct terminal indexBound negative start ready

def blankMemory : Memory S E k := ⟨(),0,0,[],fun _=>[]⟩

theorem EventReturns.native_initial
    (parameter : E→Option (Fin P.machine.symbols)→Bool)
    (correct : ∀ (e : E) (j : ℕ) (store : Fin k→List S) (heads : Fin k→Option ℤ) (memory),
      Allowed e j → store exported=List.replicate (j-1) symbol →
      BankMemory P.bank (fun i=>tape (store i)) heads memory →
      ∀ position : ℕ, parameter e (memory position)=decide (position<j))
    (run : P.EventReturns slot exported symbol Allowed n bits events blankMemory finish) :
    ∃ last, P.machine.NativeEventTrace parameter Allowed (generatorData n) bits events P.machine.initialConfiguration last ∧
      P.machine.observe (generatorData n) bits last=.halted (.accepted finish.output) ∧
      last.randomHead=finish.randomHead ∧ last.output=finish.output := by
  obtain ⟨loaded,loadedReady,loadPath,_⟩ := bank_loaded_inRegion P.bank (generatorData n) bits 0
  have initialReady : BankReady P.bank (P.encoded (blankMemory.at P.initial)) (fun _=>false) loaded := by
    change BankReady P.bank (P.encoded P.initialConfiguration) _ _
    rw [P.encoded_initial]
    exact loadedReady
  obtain ⟨last,trace,terminal,random,output⟩ := run.native parameter correct (Nat.zero_le _) _ loaded initialReady
  exact ⟨last,trace.prepend loadPath (by change loaded.output=[]; exact loadedReady.output),terminal,random,output⟩

end
end ComplexityOfGenerators.Simulation.WordStack.Program
