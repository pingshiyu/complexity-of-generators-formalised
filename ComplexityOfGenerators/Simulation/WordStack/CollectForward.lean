import ComplexityOfGenerators.Simulation.WordStack.RandomInput
import ComplexityOfGenerators.Simulation.WordStack.Routines

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def collectForward (counter dst temporary : Fin k) (different : temporary ≠ dst)
    (encode : Bool → S) : Command S O k :=
  (Routine.clear (O := O) dst).command.seq
    ((Routine.clear (O := O) temporary).command.seq
      ((collect counter temporary encode).seq (Routine.transfer temporary dst different id).command))

def forwardCollected (counter dst temporary : Fin k) (encode : Bool → S)
    (bits : BitString) (m : Memory S O k) : Memory S O k :=
  ⟨m.state,m.indexHead,m.randomHead+(m.store counter).length,m.output,
    Function.update (Function.update (Function.update m.store counter []) temporary []) dst
      (((bits.drop m.randomHead).take (m.store counter).length).map encode)⟩

theorem collectForward_full (counter dst temporary : Fin k)
    (cd : counter ≠ dst) (ct : counter ≠ temporary) (td : temporary ≠ dst)
    (encode : Bool → S) {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (available : m.randomHead+(m.store counter).length ≤ bits.length) :
    ∃ ticks ≤ 3*(m.store dst).length+3*(m.store temporary).length+12*(m.store counter).length+3,
      (collectForward counter dst temporary td encode).Runs n bits m ticks
        (.done (forwardCollected counter dst temporary encode bits m)) := by
  let a : Memory S O k := {m with store := (Routine.clear (O := O) dst).eval m.store}
  let b : Memory S O k := {a with store := (Routine.clear (O := O) temporary).eval a.store}
  let c := collected counter temporary encode bits b (m.store counter).length
  obtain ⟨first,firstCost,firstRun⟩ := (Routine.clear (O := O) dst).runs bits m bounded
  obtain ⟨second,secondCost,secondRun⟩ := (Routine.clear (O := O) temporary).runs bits a bounded
  have clock : b.store counter = m.store counter := by simp [b,a,Routine.clear,cd,ct]
  have collecting := collect_full counter temporary ct encode bits b bounded (by
    change m.randomHead+(b.store counter).length ≤ bits.length
    rw [clock]
    exact available)
  rw [clock] at collecting
  obtain ⟨last,lastCost,lastRun⟩ := (Routine.transfer (O := O) temporary dst td id).runs bits c bounded
  have exactWindow : ((bits.drop m.randomHead).take (m.store counter).length).length = (m.store counter).length := by
    simp only [List.length_take,List.length_drop]
    omega
  have temporarySize : (c.store temporary).length = (m.store counter).length := by
    simp [c,collected,b,a,Memory.set,Routine.clear]
    omega
  have final : {c with store := (Routine.transfer (O := O) temporary dst td id).eval c.store} =
      forwardCollected counter dst temporary encode bits m := by
    apply Configuration.ext <;> try rfl
    funext j
    by_cases atCounter : j=counter <;> by_cases atDst : j=dst <;> by_cases atTemporary : j=temporary <;>
      simp_all [c,collected,b,a,Routine.clear,Routine.transfer,forwardCollected,Memory.set,
        Function.update_apply,List.map_reverse]
  rw [final] at lastRun
  refine ⟨first+1+(second+1+(6*(m.store counter).length+1+last)), ?_, ?_⟩
  · change first ≤ 3*(m.store dst).length at firstCost
    have secondBound : second ≤ 3*(m.store temporary).length := by simpa [a,Routine.clear,td] using secondCost
    have lastBound : last ≤ 6*(m.store counter).length := by simpa [Routine.transfer,temporarySize] using lastCost
    omega
  · exact Runs.seq _ _ _ _ _ _ _ firstRun
      (Runs.seq _ _ _ _ _ _ _ secondRun (Runs.seq _ _ _ _ _ _ _ collecting lastRun))

theorem collectForward_short (counter dst temporary : Fin k)
    (cd : counter ≠ dst) (ct : counter ≠ temporary) (td : temporary ≠ dst)
    (encode : Bool → S) {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (short : bits.length-m.randomHead < (m.store counter).length) :
    ∃ ticks ≤ 3*(m.store dst).length+3*(m.store temporary).length+6*(m.store counter).length+3,
      (collectForward counter dst temporary td encode).Runs n bits m ticks .exhausted := by
  let a : Memory S O k := {m with store := (Routine.clear (O := O) dst).eval m.store}
  let b : Memory S O k := {a with store := (Routine.clear (O := O) temporary).eval a.store}
  obtain ⟨first,firstCost,firstRun⟩ := (Routine.clear (O := O) dst).runs bits m bounded
  obtain ⟨second,secondCost,secondRun⟩ := (Routine.clear (O := O) temporary).runs bits a bounded
  have clock : b.store counter = m.store counter := by simp [b,a,Routine.clear,cd,ct]
  obtain ⟨last,lastCost,lastRun⟩ := collect_short counter temporary ct encode bits b bounded (by
    change bits.length-m.randomHead < (b.store counter).length
    rw [clock]
    exact short)
  rw [clock] at lastCost
  refine ⟨first+1+(second+1+last), ?_, ?_⟩
  · change first ≤ 3*(m.store dst).length at firstCost
    have secondBound : second ≤ 3*(m.store temporary).length := by simpa [a,Routine.clear,td] using secondCost
    omega
  · exact Runs.seq _ _ _ _ _ _ _ firstRun
      (Runs.seq _ _ _ _ _ _ _ secondRun (Runs.seq_absent _ _ _ _ lastRun))

end ComplexityOfGenerators.Simulation.WordStack.Command
