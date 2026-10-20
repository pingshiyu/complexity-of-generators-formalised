import ComplexityOfGenerators.Simulation.WordStack.Commands

/-! Word operations implemented with single-symbol stack instructions. -/

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Memory

variable {S O : Type} {k : ℕ}

def set (m : Memory S O k) (j : Fin k) (word : List S) : Memory S O k :=
  {m with store := Function.update m.store j word}

@[simp] theorem set_index (m : Memory S O k) (j : Fin k) (word : List S) :
    (m.set j word).indexHead = m.indexHead := rfl

@[simp] theorem set_random (m : Memory S O k) (j : Fin k) (word : List S) :
    (m.set j word).randomHead = m.randomHead := rfl

@[simp] theorem set_output (m : Memory S O k) (j : Fin k) (word : List S) :
    (m.set j word).output = m.output := rfl

@[simp] theorem set_here (m : Memory S O k) (j : Fin k) (word : List S) :
    (m.set j word).store j = word := Function.update_self ..

@[simp] theorem set_there (m : Memory S O k) {i j : Fin k} (word : List S) (different : i ≠ j) :
    (m.set j word).store i = m.store i := Function.update_of_ne different ..

@[simp] theorem set_self (m : Memory S O k) (j : Fin k) : m.set j (m.store j) = m := by
  simp [set, Function.update_eq_self]

@[simp] theorem set_twice (m : Memory S O k) (j : Fin k) (x y : List S) :
    (m.set j x).set j y = m.set j y := by simp [set, Function.update_idem]

theorem set_comm (m : Memory S O k) {i j : Fin k} (different : i ≠ j) (x y : List S) :
    (m.set i x).set j y = (m.set j y).set i x := by
  simp only [set]
  congr 1
  exact Function.update_comm different x y m.store

end Memory

namespace Command

variable {S O : Type} {k : ℕ}

def push (j : Fin k) (a : S) : Command S O k := .act j (.push a) .stay none
def pop (j : Fin k) : Command S O k := .act j .pop .stay none

theorem act_stay (j : Fin k) (action : Action S) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (Command.act j action .stay none).Runs n bits m 1 (.done (m.set j (action.apply (m.store j)))) := by
  convert Runs.act m j action .stay none using 1
  simp [Program.changeMemory, Memory.set, Move.onInput, Nat.min_eq_left bounded]

theorem push_runs (j : Fin k) (a : S) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (push j a).Runs n bits m 1 (.done (m.set j (a :: m.store j))) :=
  act_stay j (.push a) bits m bounded

theorem pop_runs (j : Fin k) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (pop j).Runs n bits m 1 (.done (m.set j (m.store j).tail)) :=
  act_stay j .pop bits m bounded

def clear (j : Fin k) : Command S O k := .loop j (fun o => o.1.isSome) (pop j)

theorem clear_runs (j : Fin k) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (clear j).Runs n bits m (3 * (m.store j).length) (.done (m.set j [])) := by
  generalize word_eq : m.store j = word
  induction word generalizing m with
  | nil =>
    have same : m.set j [] = m := by rw [← word_eq, Memory.set_self]
    rw [same]
    exact Runs.loop_stop m j _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    have step := pop_runs j bits m bounded
    simp only [word_eq, List.tail_cons] at step
    have rest := ih (m.set j word) bounded (by simp)
    simp only [Memory.set_twice] at rest
    have run := Runs.loop m (m.set j word) j (fun o => o.1.isSome) (pop j) 1 (3 * word.length) _
      (by simp [observe, word_eq]) step rest
    convert run using 1 <;> simp only [clear, List.length_cons]
    omega

def transfer (src dst : Fin k) (f : S → S) : Command S O k :=
  .loop src (fun o => o.1.isSome) (.branch src fun o => match o.1 with
    | none => .skip
    | some a => (pop src).seq (push dst (f a)))

theorem transfer_runs (src dst : Fin k) (different : src ≠ dst) (f : S → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (transfer src dst f).Runs n bits m (6 * (m.store src).length)
      (.done ((m.set src []).set dst ((m.store src).reverse.map f ++ m.store dst))) := by
  generalize word_eq : m.store src = word
  induction word generalizing m with
  | nil =>
    have same : (m.set src []).set dst (([] : List S).reverse.map f ++ m.store dst) = m := by
      simp only [List.reverse_nil, List.map_nil, List.nil_append]
      rw [← word_eq, Memory.set_self, Memory.set_self]
    rw [same]
    exact Runs.loop_stop m src _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    let middle := (m.set src word).set dst (f a :: m.store dst)
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
    have final : (middle.set src []).set dst (word.reverse.map f ++ middle.store dst) =
        (m.set src []).set dst ((a :: word).reverse.map f ++ m.store dst) := by
      dsimp [middle]
      rw [Memory.set_comm _ different.symm, Memory.set_twice, Memory.set_twice]
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    rw [final] at rest
    have run := Runs.loop m middle src (fun o => o.1.isSome) _ 4 (6 * word.length) _
      (by simp [observe, word_eq]) body rest
    convert run using 1 <;> simp only [transfer, List.length_cons]
    omega

def duplicateTransfer (src first second : Fin k) (f g : S → S) : Command S O k :=
  .loop src (fun o => o.1.isSome) (.branch src fun o => match o.1 with
    | none => .skip
    | some a => (pop src).seq ((push first (f a)).seq (push second (g a))))

theorem duplicateTransfer_runs (src first second : Fin k)
    (srcFirst : src ≠ first) (srcSecond : src ≠ second) (firstSecond : first ≠ second)
    (f g : S → S) {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (duplicateTransfer src first second f g).Runs n bits m (8 * (m.store src).length)
      (.done (((m.set src []).set first ((m.store src).reverse.map f ++ m.store first)).set second
        ((m.store src).reverse.map g ++ m.store second))) := by
  generalize word_eq : m.store src = word
  induction word generalizing m with
  | nil =>
    have same : ((m.set src []).set first (([] : List S).reverse.map f ++ m.store first)).set second
        (([] : List S).reverse.map g ++ m.store second) = m := by
      simp only [List.reverse_nil, List.map_nil, List.nil_append]
      rw [← word_eq, Memory.set_self, Memory.set_self, Memory.set_self]
    rw [same]
    exact Runs.loop_stop m src _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    let middle := ((m.set src word).set first (f a :: m.store first)).set second (g a :: m.store second)
    have popStep := pop_runs src bits m bounded
    simp only [word_eq, List.tail_cons] at popStep
    have firstStep := push_runs first (f a) bits (m.set src word) bounded
    simp only [Memory.set_there _ _ srcFirst.symm] at firstStep
    have secondStep := push_runs second (g a) bits ((m.set src word).set first (f a :: m.store first)) bounded
    simp only [Memory.set_there _ _ firstSecond.symm, Memory.set_there _ _ srcSecond.symm] at secondStep
    have body : (Command.branch src fun o => match o.1 with
        | none => Command.skip
        | some a => (pop src).seq ((push first (f a)).seq (push second (g a)))).Runs
        n bits m 6 (.done middle) := by
      apply Runs.branch m src _ 5 (.done middle)
      simp only [observe, word_eq, List.head?_cons]
      exact Runs.seq _ _ _ _ 1 3 _ popStep (Runs.seq _ _ _ _ 1 1 _ firstStep secondStep)
    have rest := ih middle (by simpa [middle] using bounded) (by simp [middle, srcFirst, srcSecond])
    have final : ((middle.set src []).set first (word.reverse.map f ++ middle.store first)).set second
        (word.reverse.map g ++ middle.store second) =
        ((m.set src []).set first ((a :: word).reverse.map f ++ m.store first)).set second
          ((a :: word).reverse.map g ++ m.store second) := by
      apply Configuration.ext <;> try rfl
      funext j
      by_cases hs : j = src <;> by_cases hf : j = first <;> by_cases ht : j = second <;>
        simp_all [middle, Memory.set, Function.update_apply, List.reverse_cons, List.map_append,
          List.append_assoc]
    rw [final] at rest
    have run := Runs.loop m middle src (fun o => o.1.isSome) _ 6 (8 * word.length) _
      (by simp [observe, word_eq]) body rest
    convert run using 1 <;> simp only [duplicateTransfer, List.length_cons]
    omega

/-- Prepend a mapped copy of `src` to `dst`, restoring `src` and the empty
scratch stack. No whole-word copying instruction is assumed. -/
def copy (src dst scratch : Fin k) (f : S → S) : Command S O k :=
  (transfer src scratch id).seq (duplicateTransfer scratch src dst id f)

theorem copy_runs (src dst scratch : Fin k) (srcDst : src ≠ dst)
    (srcScratch : src ≠ scratch) (dstScratch : dst ≠ scratch) (f : S → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (empty : m.store scratch = []) :
    (copy src dst scratch f).Runs n bits m (14 * (m.store src).length + 1)
      (.done (m.set dst ((m.store src).map f ++ m.store dst))) := by
  let middle := (m.set src []).set scratch (m.store src).reverse
  have first := transfer_runs src scratch srcScratch id bits m bounded
  simp only [List.map_id, empty, List.append_nil] at first
  have last := duplicateTransfer_runs scratch src dst srcScratch.symm dstScratch.symm srcDst id f
    bits middle (by simpa [middle] using bounded)
  have final : ((middle.set scratch []).set src ((middle.store scratch).reverse.map id ++ middle.store src)).set dst
      ((middle.store scratch).reverse.map f ++ middle.store dst) =
        m.set dst ((m.store src).map f ++ m.store dst) := by
    apply Configuration.ext <;> try rfl
    funext j
    by_cases hs : j = src <;> by_cases hd : j = dst <;> by_cases ht : j = scratch <;>
      simp_all [middle, Memory.set, Function.update_apply]
  rw [final] at last
  have run := Runs.seq m middle _ _ (6 * (m.store src).length) (8 * (middle.store scratch).length) _ first last
  convert run using 1 <;> simp only [copy, middle, Memory.set_here, List.length_reverse]
  omega

def assign (src dst scratch : Fin k) (f : S → S) : Command S O k :=
  (clear dst).seq (copy src dst scratch f)

theorem assign_runs (src dst scratch : Fin k) (srcDst : src ≠ dst)
    (srcScratch : src ≠ scratch) (dstScratch : dst ≠ scratch) (f : S → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (empty : m.store scratch = []) :
    (assign src dst scratch f).Runs n bits m (3 * (m.store dst).length + 14 * (m.store src).length + 2)
      (.done (m.set dst ((m.store src).map f))) := by
  have first := clear_runs dst bits m bounded
  have last := copy_runs src dst scratch srcDst srcScratch dstScratch f bits (m.set dst []) bounded
    (by simp [dstScratch.symm, empty])
  simp only [Memory.set_there _ _ srcDst, Memory.set_here, List.append_nil, Memory.set_twice] at last
  have run := Runs.seq _ _ _ _ _ _ _ first last
  convert run using 1
  all_goals first | rfl | omega

end Command
end ComplexityOfGenerators.Simulation.WordStack
