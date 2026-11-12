import ComplexityOfGenerators.Simulation.WordStack.Routines
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

/-! A primitive two-symbol expansion of a reversed stored input word. -/
namespace ComplexityOfGenerators.Simulation.PairCollisionExpandTwo
open WordStack
variable {S O : Type} {k : ℕ}

def blocks (f g : S→S) (word : List S) : List S := word.flatMap (fun a=>[f a,g a])

def command (src dst : Fin k) (f g : S→S) : Command S O k :=
  .loop src (fun o=>o.1.isSome) (.branch src fun o=>match o.1 with
    | none => .skip
    | some a => (Command.pop src).seq ((Command.push dst (g a)).seq (Command.push dst (f a))))

def expanded (src dst : Fin k) (f g : S→S) (m : Memory S O k) : Memory S O k :=
  (m.set src []).set dst (blocks f g (m.store src).reverse++m.store dst)

theorem runs (src dst : Fin k) (different : src≠dst) (f g : S→S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead≤n) :
    (command src dst f g).Runs n bits m (8*(m.store src).length) (.done (expanded src dst f g m)) := by
  generalize wordEq : m.store src=word
  induction word generalizing m with
  | nil =>
      have same : expanded src dst f g m=m := by
        simp only [expanded,wordEq,List.reverse_nil,blocks,List.flatMap_nil,List.nil_append]
        rw [←wordEq,Memory.set_self,Memory.set_self]
      rw [same]
      exact Command.Runs.loop_stop m src _ _ (by simp [observe,wordEq])
  | cons a word ih =>
      let popped := m.set src word
      let once := popped.set dst (g a::m.store dst)
      let middle := once.set dst (f a::g a::m.store dst)
      have popStep := Command.pop_runs src bits m bounded
      simp only [wordEq,List.tail_cons] at popStep
      have first := Command.push_runs dst (g a) bits popped bounded
      simp only [popped,Memory.set_there _ _ different.symm] at first
      have second := Command.push_runs dst (f a) bits once bounded
      simp only [once,Memory.set_here] at second
      have pushes : ((Command.push dst (g a)).seq (Command.push dst (f a))).Runs n bits popped 3 (.done middle) :=
        Command.Runs.seq _ _ _ _ 1 1 _ first second
      have body : (Command.branch src fun o=>match o.1 with
          | none=>Command.skip
          | some a=>(Command.pop src).seq ((Command.push dst (g a)).seq (Command.push dst (f a)))).Runs
          n bits m 6 (.done middle) := by
        apply Command.Runs.branch m src _ 5 (.done middle)
        simpa only [observe,wordEq,List.head?_cons] using
          Command.Runs.seq m popped _ _ 1 3 (.done middle) popStep pushes
      have rest := ih middle (by simpa [middle,once,popped] using bounded)
        (by simp [middle,once,popped,different,Memory.set])
      have final : expanded src dst f g middle=expanded src dst f g m := by
        apply Configuration.ext <;> try rfl
        funext j
        by_cases hs : j=src <;> by_cases hd : j=dst <;>
          simp_all [expanded,middle,once,popped,Memory.set,Function.update_apply,
            List.reverse_cons,blocks,List.flatMap_append,List.append_assoc]
      rw [final] at rest
      have run := Command.Runs.loop m middle src (fun o=>o.1.isSome) _ 6 (8*word.length) _
        (by simp [observe,wordEq]) body rest
      convert run using 1 <;> simp [command,wordEq] <;> omega

def routine (src dst : Fin k) (different : src≠dst) (f g : S→S) : WordStack.Routine S O k where
  command := command src dst f g
  eval := fun s=>Function.update (Function.update s src []) dst (blocks f g (s src).reverse++s dst)
  cost := fun s=>8*(s src).length
  runs bits m bounded := ⟨_,le_rfl,runs src dst different f g bits m bounded⟩

theorem pure (src dst : Fin k) (f g : S→S) : Command.RandomFree (command (O:=O) src dst f g) := by
  apply Command.RandomFree.loop
  apply Command.RandomFree.branch
  intro observation
  cases observation.1 <;> simp

@[simp] theorem blocks_length (f g : S→S) (word : List S) : (blocks f g word).length=2*word.length := by
  induction word with
  | nil => rfl
  | cons a tail ih => simp [blocks] at ih ⊢;omega

end ComplexityOfGenerators.Simulation.PairCollisionExpandTwo
