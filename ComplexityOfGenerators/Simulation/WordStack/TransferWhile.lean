import ComplexityOfGenerators.Simulation.WordStack.Routines

/-! Transfer the longest stored prefix satisfying a decidable symbol test.
The first failing symbol remains available to the next bounded operation. -/
namespace ComplexityOfGenerators.Simulation.WordStack

namespace Command

variable {S O : Type} {k : ℕ}

def transferWhile (src dst : Fin k) (keep : S → Bool) (f : S → S) : Command S O k :=
  .loop src (fun o => o.1.any keep) (.branch src fun o => match o.1 with
    | none => .skip
    | some a => (pop src).seq (push dst (f a)))

def transferredWhile (src dst : Fin k) (keep : S → Bool) (f : S → S) (m : Memory S O k) : Memory S O k :=
  (m.set src ((m.store src).dropWhile keep)).set dst (((m.store src).takeWhile keep).reverse.map f ++ m.store dst)

theorem transferWhile_runs (src dst : Fin k) (different : src ≠ dst) (keep : S → Bool) (f : S → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (transferWhile src dst keep f).Runs n bits m (6 * ((m.store src).takeWhile keep).length)
      (.done (transferredWhile src dst keep f m)) := by
  generalize word_eq : m.store src = word
  induction word generalizing m with
  | nil =>
    have same : transferredWhile src dst keep f m = m := by
      simp only [transferredWhile, word_eq, List.dropWhile_nil, List.takeWhile_nil,
        List.reverse_nil, List.map_nil, List.nil_append]
      rw [← word_eq, Memory.set_self, Memory.set_self]
    rw [same]
    exact Runs.loop_stop m src _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    by_cases kept : keep a = true
    · let middle := (m.set src word).set dst (f a :: m.store dst)
      have popStep := pop_runs src bits m bounded
      simp only [word_eq, List.tail_cons] at popStep
      have pushStep := push_runs dst (f a) bits (m.set src word) bounded
      simp only [Memory.set_there _ _ different.symm] at pushStep
      have body : (Command.branch src fun o => match o.1 with
          | none => Command.skip
          | some a => (pop src).seq (push dst (f a))).Runs n bits m 4 (.done middle) := by
        apply Runs.branch m src _ 3 (.done middle)
        simpa only [observe, word_eq, List.head?_cons] using
          Runs.seq m (m.set src word) (pop src) (push dst (f a)) 1 1 (.done middle) popStep pushStep
      have rest := ih middle (by simpa [middle] using bounded) (by simp [middle, different])
      have final : transferredWhile src dst keep f middle = transferredWhile src dst keep f m := by
        apply Configuration.ext <;> try rfl
        funext j
        by_cases hs : j = src <;> by_cases hd : j = dst <;>
          simp_all [transferredWhile, middle, Memory.set, Function.update_apply,
            List.reverse_cons, List.map_append, List.append_assoc]
      rw [final] at rest
      have run := Runs.loop m middle src (fun o => o.1.any keep) _ 4
        (6 * (word.takeWhile keep).length) _ (by simp [observe, word_eq, kept]) body rest
      convert run using 1 <;>
        simp [transferWhile, word_eq, kept, middle, different]
      omega
    · have same : transferredWhile src dst keep f m = m := by
        simp only [transferredWhile, word_eq]
        simp only [List.dropWhile_cons, List.takeWhile_cons, kept, Bool.false_eq_true, ↓reduceIte,
          List.reverse_nil, List.map_nil, List.nil_append]
        rw [← word_eq, Memory.set_self, Memory.set_self]
      rw [same]
      simpa [transferWhile, word_eq, kept] using
        (Runs.loop_stop m src (fun o => o.1.any keep) _ (by simp [observe, word_eq, kept]))

end Command

namespace Routine

variable {S O : Type} {k : ℕ}

def transferWhile (src dst : Fin k) (different : src ≠ dst) (keep : S → Bool) (f : S → S) : Routine S O k where
  command := Command.transferWhile src dst keep f
  eval := fun s => Function.update (Function.update s src ((s src).dropWhile keep)) dst
    (((s src).takeWhile keep).reverse.map f ++ s dst)
  cost := fun s => 6 * ((s src).takeWhile keep).length
  runs bits m bounded := ⟨_, le_rfl, Command.transferWhile_runs src dst different keep f bits m bounded⟩

end Routine
end ComplexityOfGenerators.Simulation.WordStack
