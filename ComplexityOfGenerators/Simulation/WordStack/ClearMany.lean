import ComplexityOfGenerators.Simulation.WordStack.Words

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Memory

variable {S O : Type} {k : ℕ}

def erase (m : Memory S O k) (registers : List (Fin k)) : Memory S O k :=
  {m with store := fun j => if j ∈ registers then [] else m.store j}

@[simp] theorem erase_nil (m : Memory S O k) : m.erase [] = m := by simp [erase]

@[simp] theorem erase_cons (m : Memory S O k) (j : Fin k) (rest : List (Fin k)) :
    (m.set j []).erase rest = m.erase (j :: rest) := by
  apply Configuration.ext <;> try rfl
  funext i
  by_cases same : i = j <;> by_cases member : i ∈ rest <;> simp [erase, set, same, member]

@[simp] theorem erase_index (m : Memory S O k) (registers : List (Fin k)) :
    (m.erase registers).indexHead = m.indexHead := rfl

@[simp] theorem erase_random (m : Memory S O k) (registers : List (Fin k)) :
    (m.erase registers).randomHead = m.randomHead := rfl

@[simp] theorem erase_output (m : Memory S O k) (registers : List (Fin k)) :
    (m.erase registers).output = m.output := rfl

@[simp] theorem erase_here (m : Memory S O k) (registers : List (Fin k)) (j : Fin k)
    (member : j ∈ registers) : (m.erase registers).store j = [] := by simp [erase, member]

@[simp] theorem erase_there (m : Memory S O k) (registers : List (Fin k)) (j : Fin k)
    (outside : j ∉ registers) : (m.erase registers).store j = m.store j := by simp [erase, outside]

end Memory

namespace Command

variable {S O : Type} {k : ℕ}

def clearMany : List (Fin k) → Command S O k
  | [] => .skip
  | j :: rest => (clear j).seq (clearMany rest)

theorem clearMany_runs (registers : List (Fin k)) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) (budget : ℕ)
    (sizes : ∀ j ∈ registers, (m.store j).length ≤ budget) :
    ∃ t ≤ registers.length * (3 * budget + 1),
      (clearMany registers).Runs n bits m t (.done (m.erase registers)) := by
  induction registers generalizing m with
  | nil => exact ⟨0, by simp, by simpa [clearMany] using Runs.skip m⟩
  | cons j rest ih =>
    have first := clear_runs j bits m bounded
    have size : (m.store j).length ≤ budget := sizes j (by simp)
    obtain ⟨t, cost, last⟩ := ih (m.set j []) bounded (by
      intro i member
      by_cases equal : i = j
      · simp [equal]
      · simpa [equal] using sizes i (by simp [member]))
    refine ⟨3 * (m.store j).length + 1 + t, ?_, ?_⟩
    · simp only [List.length_cons]; nlinarith
    · simpa only [clearMany, Memory.erase_cons] using Runs.seq _ _ _ _ _ _ _ first last

end Command
end ComplexityOfGenerators.Simulation.WordStack
