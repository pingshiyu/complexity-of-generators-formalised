import ComplexityOfGenerators.Simulation.WordStack.EventTrace
import ComplexityOfGenerators.Simulation.WordStack.EventSite
import ComplexityOfGenerators.Simulation.NativeEventTrace

/-! Event instrumentation survives both real compiler stages. Parameter
correctness is a finite-cell codec fact about the actual updated bank memory. -/
namespace ComplexityOfGenerators.Simulation.WordStack.Program
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Q S E : Type} {k : ℕ} [Fintype Q] [Fintype S] [Fintype E]
    (P : Program Q S E k)

def storeRadius (store : Fin k→List S) : ℕ := Finset.univ.sup (fun i=>(store i).length)

theorem encoded_bounded (n : ℕ) (c : Configuration Q S E k) (index : c.indexHead≤n) :
    P.bank.Bounded (generatorData n) (storeRadius c.store) (P.encoded c) := by
  refine ⟨by simp [encoded],by simp [encoded],index,?_⟩
  intro j
  simpa only [encoded,Int.natAbs_natCast,storeRadius] using
    (Finset.le_sup (f := fun i=>(c.store i).length) (Finset.mem_univ j))

variable {P} {slot exported : Fin k} {symbol : S} {Allowed : E→ℕ→Prop}
    {n : ℕ} {bits : BitString} {events : List (E×ℕ)}
    {source finish : Configuration Q S E k}

theorem EventTrace.native
    (parameter : E→Option (Fin P.machine.symbols)→Bool)
    (correct : ∀ (e : E) (j : ℕ) (store : Fin k→List S) (heads : Fin k→Option ℤ) (memory),
      Allowed e j → store exported=List.replicate (j-1) symbol →
      BankMemory P.bank (fun i=>tape (store i)) heads memory →
      ∀ position : ℕ, parameter e (memory position)=decide (position<j))
    (trace : P.EventTrace slot exported symbol Allowed n bits events source finish) :
    ∀ (indexBound : source.indexHead≤n) (negative : Fin k→Bool)
      (start : ComplexityOfGenerators.Configuration P.machine),
      BankReady P.bank (P.encoded source) negative start →
      ∃ next sides, BankReady P.bank (P.encoded finish) sides next ∧
        P.machine.NativeEventTrace parameter Allowed (generatorData n) bits events start next := by
  induction trace with
  | nil source finish ticks path silent =>
      intro indexBound negative start ready
      obtain ⟨nativeTicks,next,sides,nextReady,native⟩ :=
        P.steps_native path _ negative start ready (P.encoded_bounded n source indexBound)
      refine ⟨next,sides,nextReady,.nil _ _ nativeTicks native ?_⟩
      exact nextReady.output.trans (silent.trans ready.output.symm)
  | cons e j events source before next finish ticks segment silent allowed selected empty exportedWord event rest ih =>
      intro indexBound negative start ready
      have beforeIndex := segment.index_le P indexBound
      obtain ⟨prefixTicks,nativeBefore,beforeSides,beforeReady,prefixPath⟩ :=
        P.steps_native segment _ negative start ready (P.encoded_bounded n source indexBound)
      obtain ⟨q,write,action,memory,tailTicks,after,afterSides,afterReady,tailPath,tailOutput⟩ :=
        P.event_site n bits before next e _ beforeSides nativeBefore beforeReady
          (P.encoded_bounded n before beforeIndex) (by rw [selected];exact empty) event
      have advancedIndex : (P.advance n before next .stay .stay (some e)).indexHead≤n :=
        Move.stay.onInput_le n before.indexHead beforeIndex
      obtain ⟨nativeFinish,finishSides,finishReady,nativeRest⟩ := ih advancedIndex afterSides after afterReady
      have instrumentedRest := nativeRest.prepend tailPath tailOutput
      refine ⟨nativeFinish,finishSides,finishReady,
        .cons e j events start nativeBefore q write nativeFinish prefixTicks prefixPath ?_
          allowed beforeReady.head action ?_ instrumentedRest⟩
      · exact beforeReady.output.trans (silent.trans ready.output.symm)
      · exact correct e j before.store _ _ allowed exportedWord memory

end
end ComplexityOfGenerators.Simulation.WordStack.Program
