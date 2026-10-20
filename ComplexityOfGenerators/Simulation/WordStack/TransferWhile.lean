import ComplexityOfGenerators.Simulation.WordStack.Routines

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def transferWhile (src dst : Fin k) (test : S → Bool) (f : S → S) : Command S O k :=
  .loop src (fun o => o.1.any test) (.branch src fun o => match o.1 with
    | none => .skip
    | some a => (pop src).seq (push dst (f a)))

theorem transferWhile_runs (src dst : Fin k) (different : src ≠ dst) (test : S → Bool) (f : S → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (transferWhile src dst test f).Runs n bits m (6 * ((m.store src).takeWhile test).length)
      (.done ((m.set src ((m.store src).dropWhile test)).set dst
        (((m.store src).takeWhile test).reverse.map f ++ m.store dst))) := by
  generalize word_eq : m.store src = word
  induction word generalizing m with
  | nil =>
    have final : (m.set src (([] : List S).dropWhile test)).set dst
        ((([] : List S).takeWhile test).reverse.map f ++ m.store dst) = m := by
      simp only [List.dropWhile_nil, List.takeWhile_nil, List.reverse_nil, List.map_nil, List.nil_append]
      rw [← word_eq, Memory.set_self, Memory.set_self]
    rw [final]
    exact Runs.loop_stop m src _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    cases check : test a with
    | false =>
      have final : (m.set src ((a :: word).dropWhile test)).set dst
          (((a :: word).takeWhile test).reverse.map f ++ m.store dst) = m := by
        simp only [List.dropWhile_cons, check, Bool.false_eq_true, ite_false,
          List.takeWhile_cons, List.reverse_nil, List.map_nil, List.nil_append]
        rw [← word_eq, Memory.set_self, Memory.set_self]
      rw [final]
      simpa [transferWhile, List.takeWhile_cons, check] using
        Runs.loop_stop m src (fun o => o.1.any test) _ (by simp [observe, word_eq, check])
    | true =>
      let middle := (m.set src word).set dst (f a :: m.store dst)
      have popStep := pop_runs src bits m bounded
      simp only [word_eq, List.tail_cons] at popStep
      have pushStep := push_runs dst (f a) bits (m.set src word) bounded
      simp only [Memory.set_there _ _ different.symm] at pushStep
      have body : (Command.branch src fun o => match o.1 with
          | none => Command.skip
          | some a => (pop src).seq (push dst (f a))).Runs n bits m 4 (.done middle) := by
        apply Runs.branch m src _ 3 (.done middle)
        simpa only [observe, word_eq, List.head?_cons] using Runs.seq _ _ _ _ _ _ _ popStep pushStep
      have rest := ih middle (by simpa [middle] using bounded) (by simp [middle, different])
      have final : (middle.set src (word.dropWhile test)).set dst
          ((word.takeWhile test).reverse.map f ++ middle.store dst) =
          (m.set src ((a :: word).dropWhile test)).set dst
            (((a :: word).takeWhile test).reverse.map f ++ m.store dst) := by
        apply Configuration.ext <;> try rfl
        funext j
        by_cases hs : j = src <;> by_cases hd : j = dst <;>
          simp_all [middle, Memory.set, Function.update_apply, List.takeWhile_cons,
            List.dropWhile_cons, List.reverse_cons, List.map_append, List.append_assoc]
      rw [final] at rest
      have run := Runs.loop m middle src (fun o => o.1.any test) _ 4
        (6 * (word.takeWhile test).length) _ (by simp [observe, word_eq, check]) body rest
      convert run using 1
      · rfl
      · simp [List.takeWhile_cons, check]; omega

end ComplexityOfGenerators.Simulation.WordStack.Command

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

variable {S O : Type} {k : ℕ}

def transferWhile (src dst : Fin k) (different : src ≠ dst) (test : S → Bool) (f : S → S) : Routine S O k where
  command := Command.transferWhile src dst test f
  eval := fun s => Function.update (Function.update s src ((s src).dropWhile test)) dst
    (((s src).takeWhile test).reverse.map f ++ s dst)
  cost := fun s => 6 * ((s src).takeWhile test).length
  runs bits m bounded := ⟨_, le_rfl, Command.transferWhile_runs src dst different test f bits m bounded⟩

end ComplexityOfGenerators.Simulation.WordStack.Routine
