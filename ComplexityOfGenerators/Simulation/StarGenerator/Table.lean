import ComplexityOfGenerators.Simulation.StarGenerator.Value
import ComplexityOfGenerators.Simulation.WordStack.TransferWhile

set_option maxHeartbeats 1200000

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

abbrev Cell := UnionGenerator.Cell G G
abbrev Store := Local.Store (Cell G) 35
abbrev Controller := WordStack.Routine (Cell G) α 35

def someMarker : Cell G := .right (.state .accepted)
def noneMarker : Cell G := .right (.state .rejected)

def isLetter : Cell G → Bool
  | .letter _ => true
  | _ => false

def entry : Option (List α) → List (Cell G)
  | none => [noneMarker G]
  | some word => someMarker G :: UnionGenerator.letters G G word

/-- Entries supplied here are in decreasing index order. -/
def encoded (entries : Table α) : List (Cell G) := entries.flatMap (entry G)

def archive (table : Table α) : List (Cell G) := encoded G table.reverse

def available : Option (Cell G) → Bool
  | some (.right (.state .accepted)) => true
  | _ => false

/-- Consume one table entry. The output word is stored in register 26 and its
availability in 28; register 25 is temporary storage and is cleared again. -/
def readEntry : Controller G :=
  (WordStack.Routine.clear 25).seq
  ((WordStack.Routine.clear 26).seq
  (WordStack.Routine.branch 34 fun head =>
  (UnionGenerator.flag G G 28 (available G head)).seq
  ((WordStack.Routine.ofLocal (Local.pop 34)).seq
  ((WordStack.Routine.transferWhile 34 25 (by decide) (isLetter G) id).seq
    (WordStack.Routine.transfer 25 26 (by decide) id)))))

/-- Preserve the sampled word and prepend its tagged entry to the archive. -/
def appendEntry : Controller G :=
  WordStack.Routine.branch 32 fun found => if found.isSome then
    (WordStack.Routine.copy 31 29 33 (by decide) (by decide) (by decide) id).seq
      (WordStack.Routine.ofLocal (Local.push 29 (someMarker G)))
  else WordStack.Routine.ofLocal (Local.push 29 (noneMarker G))

theorem encoded_stops (entries : Table α) :
    (encoded G entries).takeWhile (isLetter G) = [] ∧
      (encoded G entries).dropWhile (isLetter G) = encoded G entries := by
  cases entries with
  | nil => simp [encoded]
  | cons value rest => cases value <;> simp [encoded, entry, someMarker, noneMarker, isLetter]

theorem takeWhile_letters (word : List α) (rest : List (Cell G)) :
    (word.map (Symbol.letter : α → Cell G) ++ rest).takeWhile (isLetter G) =
      word.map (Symbol.letter : α → Cell G) ++ rest.takeWhile (isLetter G) := by
  induction word with
  | nil => simp [UnionGenerator.letters]
  | cons a word ih => simpa [UnionGenerator.letters, isLetter, List.takeWhile_cons, List.dropWhile_cons] using congrArg (List.cons (Symbol.letter a)) ih

theorem dropWhile_letters (word : List α) (rest : List (Cell G)) :
    (word.map (Symbol.letter : α → Cell G) ++ rest).dropWhile (isLetter G) = rest.dropWhile (isLetter G) := by
  induction word with
  | nil => simp [UnionGenerator.letters]
  | cons a word ih => simpa [UnionGenerator.letters, isLetter, List.takeWhile_cons, List.dropWhile_cons] using ih

theorem readEntry_eval (value : Option (List α)) (rest : Table α) (s : Store G)
    (cursor : s 34 = entry G value ++ encoded G rest) :
    (readEntry G).eval s = Function.update (Function.update (Function.update
      (Function.update s 25 []) 26 (UnionGenerator.held G G value))
        28 (UnionGenerator.flagWord G G value.isSome)) 34 (encoded G rest) := by
  have stop := encoded_stops G rest
  cases value <;> funext j <;> fin_cases j <;>
    simp [readEntry, WordStack.Routine.seq, WordStack.Routine.clear,
      WordStack.Routine.branch, UnionGenerator.flag_eval, WordStack.Routine.ofLocal,
      Local.eval_pop, WordStack.Routine.transferWhile, WordStack.Routine.transfer,
      entry, someMarker, noneMarker, available, UnionGenerator.held, UnionGenerator.flagWord,
      takeWhile_letters, dropWhile_letters, List.map_reverse, UnionGenerator.letters, cursor, stop.1, stop.2]

theorem readEntry_empty (s : Store G) (cursor : s 34 = []) :
    (readEntry G).eval s = Function.update (Function.update (Function.update
      (Function.update s 25 []) 26 []) 28 []) 34 [] := by
  funext j
  fin_cases j <;>
    simp [readEntry, WordStack.Routine.seq, WordStack.Routine.clear,
      WordStack.Routine.branch, UnionGenerator.flag_eval, WordStack.Routine.ofLocal,
      Local.eval_pop, WordStack.Routine.transferWhile, WordStack.Routine.transfer,
      available, UnionGenerator.flagWord, cursor]

theorem readEntry_summary (entries : Table α) (s : Store G) (cursor : s 34 = encoded G entries) :
    (readEntry G).eval s = Function.update (Function.update (Function.update
      (Function.update s 25 []) 26 (UnionGenerator.held G G (entries.head?.bind id)))
      28 (UnionGenerator.flagWord G G (entries.head?.bind id).isSome)) 34 (encoded G (entries.drop 1)) := by
  cases entries with
  | nil => simpa [encoded, UnionGenerator.held, UnionGenerator.flagWord] using readEntry_empty G s (by simpa [encoded] using cursor)
  | cons value rest =>
    simpa using readEntry_eval G value rest s (by simpa [encoded] using cursor)

theorem archive_append (table : Table α) (value : Option (List α)) :
    archive G (table ++ [value]) = entry G value ++ archive G table := by
  simp [archive, encoded, List.reverse_append, List.flatMap_append]

theorem appendEntry_archive (value : Option (List α)) (s : Store G)
    (word : s 31 = UnionGenerator.held G G value)
    (found : s 32 = UnionGenerator.flagWord G G value.isSome) :
    (appendEntry G).eval s 29 = entry G value ++ s 29 := by
  cases value <;>
    simp [appendEntry, WordStack.Routine.branch, found, WordStack.Routine.seq,
      WordStack.Routine.copy, WordStack.Routine.ofLocal, Local.eval_push, word,
      UnionGenerator.flagWord, UnionGenerator.held, entry]

theorem appendEntry_fixes (j : Fin 35) (word : j ≠ 29) (scratch : j ≠ 33) :
    (appendEntry G).Fixes j := by
  intro s
  simp only [appendEntry, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, WordStack.Routine.copy,
    WordStack.Routine.ofLocal, Local.eval_push, word, scratch]

end ComplexityOfGenerators.Simulation.StarGenerator
