import ComplexityOfGenerators.Simulation.WordStack.TransferWhile

namespace ComplexityOfGenerators.Simulation.WordStack.WordCounter

variable {S O : Type} {k : ℕ}

def successor (first : S) (next : S → Option S) : List S → List S
  | [] => [first]
  | a :: rest => match next a with | none => first :: successor first next rest | some b => b :: rest

def finish (first : S) (next : S → Option S) : List S → List S
  | [] => [first]
  | a :: rest => match next a with | none => a :: rest | some b => b :: rest

def finishCode (word : Fin k) (first : S) (next : S → Option S) : Local S k :=
  .read word fun head => match head with
    | none => Local.push word first
    | some a => match next a with | none => .skip | some b => Local.write word b

theorem finish_eval (word : Fin k) (first : S) (next : S → Option S) (s : Local.Store S k) :
    (finishCode word first next).eval s = Function.update s word (finish first next (s word)) := by
  cases h : s word with
  | nil => simp [finishCode, Local.eval_read, h, finish]
  | cons a rest =>
    cases found : next a <;> simp [finishCode, Local.eval_read, h, found, finish, Function.update_eq_self]

theorem finish_ticks (word : Fin k) (first : S) (next : S → Option S) (s : Local.Store S k) :
    (finishCode word first next).ticks s ≤ 4 := by
  cases h : s word with
  | nil => simp [finishCode, Local.ticks, h, Local.push]
  | cons a rest => cases found : next a <;> simp [finishCode, Local.ticks, h, found, Local.write, Local.pop, Local.push]

theorem successor_split (first : S) (next : S → Option S) (word : List S) :
    successor first next word =
      List.replicate (word.takeWhile (fun a => (next a).isNone)).length first ++
        finish first next (word.dropWhile (fun a => (next a).isNone)) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    cases found : next a <;>
      simp [successor, found, List.takeWhile_cons, List.dropWhile_cons, finish, ih, List.replicate_succ]

def routine (word scratch : Fin k) (different : word ≠ scratch) (first : S) (next : S → Option S) :
    Routine S O k :=
  (Routine.clear scratch).seq
  ((Routine.transferWhile word scratch different (fun a => (next a).isNone) (fun _ => first)).seq
  ((Routine.ofLocal (finishCode word first next)).seq
    (Routine.transfer scratch word different.symm id)))

theorem routine_eval (word scratch : Fin k) (different : word ≠ scratch) (first : S) (next : S → Option S)
    (s : Local.Store S k) :
    (routine (O := O) word scratch different first next).eval s =
      Function.update (Function.update s scratch []) word (successor first next (s word)) := by
  rw [successor_split]
  have reverseDifferent := different.symm
  funext j
  by_cases hw : j = word <;> by_cases hs : j = scratch <;>
    simp_all [routine, Routine.seq, Routine.clear, Routine.transferWhile, Routine.ofLocal,
      finish_eval, Routine.transfer, Function.update_apply]

theorem routine_cost (word scratch : Fin k) (different : word ≠ scratch) (first : S) (next : S → Option S)
    (s : Local.Store S k) :
    (routine (O := O) word scratch different first next).cost s ≤
      3 * (s scratch).length + 12 * (s word).length + 7 := by
  let middle := (Routine.transferWhile (O := O) word scratch different (fun a => (next a).isNone) (fun _ => first)).eval
    ((Routine.clear (O := O) scratch).eval s)
  have finishing := finish_ticks word first next middle
  have length := (List.takeWhile_sublist (l := s word) (fun a => (next a).isNone)).length_le
  simp only [routine, Routine.seq, Routine.clear, Routine.transferWhile, Routine.ofLocal,
    Routine.transfer, finish_eval, Function.update_of_ne different, Function.update_of_ne different.symm,
    Function.update_self, List.length_map, List.length_reverse, List.length_append, List.length_nil,
    Nat.add_zero]
  simp only [middle, Routine.transferWhile, Routine.clear, Function.update_of_ne different,
    Function.update_self] at finishing
  omega

theorem successor_map {A : Type} (encode : A → S) (first : A) (nextA : A → Option A)
    (nextS : S → Option S) (successors : ∀ a, nextS (encode a) = (nextA a).map encode) (word : List A) :
    successor (encode first) nextS (word.map encode) = (successor first nextA word).map encode := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    cases found : nextA a <;> simp [successor, successors, found, ih]

end ComplexityOfGenerators.Simulation.WordStack.WordCounter
