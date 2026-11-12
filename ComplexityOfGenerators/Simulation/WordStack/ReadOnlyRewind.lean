import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Rewind the physical read-only index head using an explicit stored unary
counter. Each left move and each loop transfer is charged. -/
namespace ComplexityOfGenerators.Simulation.WordStack.Command
variable {S O : Type} {k : ℕ}

def rewind (counter : Fin k) : Command S O k :=
  .loop counter (fun observed => observed.1.isSome) (.act counter .pop .left none)

def rewound (counter : Fin k) (m : Memory S O k) : Memory S O k :=
  {m.set counter [] with indexHead := m.indexHead-(m.store counter).length}

theorem rewind_runs (counter : Fin k) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (rewind counter).Runs n bits m (3*(m.store counter).length) (.done (rewound counter m)) := by
  generalize equation : m.store counter = clock
  induction clock generalizing m with
  | nil =>
      have stored : m.set counter [] = m := by simpa only [equation] using Memory.set_self m counter
      have same : rewound counter m = m := by simpa only [rewound, equation, List.length_nil, Nat.sub_zero, stored]
      rw [same]
      exact Runs.loop_stop m counter _ _ (by simp [observe, equation])
  | cons letter clock ih =>
      let middle := Program.changeMemory counter n .pop .left none m
      have nextClock : middle.store counter = clock := by simp [middle, Program.changeMemory, equation, Action.apply]
      have nextHead : middle.indexHead = m.indexHead-1 := by simp [middle, Program.changeMemory, Move.onInput]
      have rest := ih middle (by rw [nextHead]; omega) nextClock
      have final : rewound counter middle = rewound counter m := by
        apply Configuration.ext <;>
          simp only [rewound, Memory.set, middle, Program.changeMemory, Action.apply,
            Option.toList_none, List.append_nil, Function.update_idem, Function.update_self,
            equation, List.tail_cons, List.length_cons, Move.onInput] <;> omega
      rw [final] at rest
      have run := Runs.loop m middle counter (fun observed => observed.1.isSome) (.act counter .pop .left none)
        1 (3*clock.length) _ (by simp [observe, equation]) (Runs.act m counter .pop .left none) rest
      convert run using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

end ComplexityOfGenerators.Simulation.WordStack.Command
