import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Prepare

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

def masked (count : ℕ) (bits : BitString) (m : Memory) : Memory :=
  ⟨m.state,m.indexHead,m.randomHead+count,m.output,
    Function.update (Function.update (Function.update m.store 30 []) 33 []) 31
      (((bits.drop m.randomHead).take count).map bitSymbol)⟩

theorem prepareMask_full (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (counter : m.store 32 = List.replicate n .zero) (available : m.randomHead+n ≤ bits.length) :
    ∃ ticks ≤ 3*(m.store 31).length+3*(m.store 33).length+3*(m.store 30).length+26*n+6,
      prepareMask.Runs n bits m ticks (.done (masked n bits m)) := by
  let cleared : Memory := {m with store := (Routine.clear (O := Symbol) 31).eval m.store}
  let counted : Memory := {cleared with store := maskClock.eval cleared.store}
  let collected := Command.collected 33 30 bitSymbol bits counted n
  obtain ⟨clearTicks, clearBound, clearRun⟩ := (Routine.clear (S := Symbol) (O := Symbol) 31).runs bits m index
  obtain ⟨counterTicks, counterBound, counterRun⟩ := maskClock.runs bits cleared index
  have clock : counted.store 33 = List.replicate n .zero := by
    simp [counted, cleared, maskClock, Routine.assign_eval, Routine.clear, counter]
  have countCost : maskClock.cost cleared.store = 3*(m.store 33).length+3*(m.store 30).length+14*n+3 := by
    simp [maskClock, Routine.assign_cost, cleared, Routine.clear, counter]
  have collectRun := Command.collect_full 33 30 (by decide) bitSymbol bits counted index (by
    simpa only [clock, List.length_replicate] using available)
  rw [clock,List.length_replicate] at collectRun
  obtain ⟨orientTicks, orientBound, orientRun⟩ := orientMask.runs bits collected index
  have outputSize : (collected.store 30).length = n := by
    simp [collected, Command.collected, counted, cleared, maskClock, Routine.assign_eval,
      Routine.clear, Nat.min_eq_left (show n ≤ bits.length-m.randomHead by omega)]
  have orientCost : orientMask.cost collected.store = 6*n := by simp [orientMask,Routine.transfer,outputSize]
  have final : {collected with store := orientMask.eval collected.store} = masked n bits m := by
    apply Configuration.ext <;> try rfl
    funext j
    fin_cases j <;>
      simp [collected,Command.collected,counted,cleared,maskClock,orientMask,
        Routine.assign_eval,Routine.clear,Routine.transfer,masked,Memory.set,List.map_reverse]

  rw [final] at orientRun
  have run := Command.Runs.seq _ _ _ _ _ _ _ clearRun
    (Command.Runs.seq _ _ _ _ _ _ _ counterRun
      (Command.Runs.seq _ _ _ _ _ _ _ collectRun orientRun))
  refine ⟨clearTicks+1+(counterTicks+1+(6*n+1+orientTicks)), ?_, ?_⟩
  · change clearTicks ≤ 3*(m.store 31).length at clearBound
    omega
  · simpa only [prepareMask] using run

theorem prepareMask_short (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (counter : m.store 32 = List.replicate n .zero) (random : m.randomHead ≤ bits.length)
    (short : bits.length < m.randomHead+n) :
    ∃ ticks ≤ 3*(m.store 31).length+3*(m.store 33).length+3*(m.store 30).length+26*n+8,
      prepareMask.Runs n bits m ticks .exhausted := by
  let cleared : Memory := {m with store := (Routine.clear (O := Symbol) 31).eval m.store}
  let counted : Memory := {cleared with store := maskClock.eval cleared.store}
  obtain ⟨clearTicks, clearBound, clearRun⟩ := (Routine.clear (S := Symbol) (O := Symbol) 31).runs bits m index
  obtain ⟨counterTicks, counterBound, counterRun⟩ := maskClock.runs bits cleared index
  have clock : counted.store 33 = List.replicate n .zero := by
    simp [counted, cleared, maskClock, Routine.assign_eval, Routine.clear, counter]
  have countCost : maskClock.cost cleared.store = 3*(m.store 33).length+3*(m.store 30).length+14*n+3 := by
    simp [maskClock, Routine.assign_cost, cleared, Routine.clear, counter]
  obtain ⟨collectTicks, collectBound, collectRun⟩ := Command.collect_short 33 30 (by decide) bitSymbol bits counted index
    (by simp only [clock,List.length_replicate]; change bits.length-m.randomHead<n; omega)
  rw [clock,List.length_replicate] at collectBound
  have absent := Command.Runs.seq_absent counted (Command.collect 33 30 bitSymbol) orientMask.command collectTicks collectRun
  have run := Command.Runs.seq _ _ _ _ _ _ _ clearRun (Command.Runs.seq _ _ _ _ _ _ _ counterRun absent)
  refine ⟨clearTicks+1+(counterTicks+1+collectTicks), ?_, ?_⟩
  · change clearTicks ≤ 3*(m.store 31).length at clearBound
    omega
  · exact run

theorem masked_fields (n : ℕ) (bits : BitString) (m : Memory) :
    (masked n bits m).store 31 = (((bits.drop m.randomHead).take n).map bitSymbol) ∧
      ∀ j : Fin 35, j ≠ 30 → j ≠ 31 → j ≠ 33 → (masked n bits m).store j = m.store j := by
  constructor
  · simp [masked]
  · intro j a b c
    simp [masked,a,b,c]

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
