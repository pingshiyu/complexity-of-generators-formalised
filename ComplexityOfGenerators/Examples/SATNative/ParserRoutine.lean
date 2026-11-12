import ComplexityOfGenerators.Examples.SATNative.ParserModel

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

noncomputable def header {O : Type} : Routine Symbol O 32 := NativeHeader.headerRoutine.rename subslots

def bodySetup {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 5 10 9 (by decide) (by decide) (by decide) id).seq
    ((Routine.assign 2 16 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
      (Routine.clearMany [17, 18]))

noncomputable def parser {O : Type} : Routine Symbol O 32 :=
  header.seq (bodySetup.seq NativeBody.bodyRoutine)

theorem header_fields {O : Type} (s : Store) :
    let output := (header (O := O)).eval s
    output 2 = (NativeHeader.parsedState (s 2)).word ∧
    output 4 = List.replicate (readOnes (s 2)).1 .one ∧
    output 5 = List.replicate (NativeHeader.parsedState (s 2)).count .one ∧
    output 6 = (if (NativeHeader.parsedState (s 2)).valid then [.one] else []) := by
  dsimp only
  have here (j : Fin 16) : (header (O := O)).eval s (subslots j) =
      NativeHeader.headerRoutine.eval (O := O) (s ∘ subslots) j := Routine.rename_eval_here _ _ _ _
  have word := here 2
  have cap := here 4
  have count := here 5
  have valid := here 6
  rw [NativeHeader.headerRoutine_eval] at word cap count valid
  exact ⟨by simpa [subslots, Function.comp_def, NativeHeader.encoded] using word,
    by simpa [subslots, Function.comp_def, NativeHeader.encoded, NativeHeader.scaffold] using cap,
    by simpa [subslots, Function.comp_def, NativeHeader.encoded] using count,
    by simpa [subslots, Function.comp_def, NativeHeader.encoded] using valid⟩

theorem bodySetup_represents {O : Type} (s : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool)
    (source : s 2 = word) (cap : s 4 = List.replicate capacity .one)
    (count : s 5 = List.replicate active .one) (valid : s 6 = if enabled then [.one] else []) :
    Represents capacity active ⟨word, false, false, enabled⟩ ((bodySetup (O := O)).eval s) ∧
      ((bodySetup (O := O)).eval s 16).length = word.length := by
  simp [bodySetup, Routine.seq, Routine.assign_eval, Routine.clearMany_eval,
    Represents, source, cap, count, valid]

theorem parser_represents {O : Type} (s : Store) :
    Represents (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count
      (finalState (s 2)) ((parser (O := O)).eval s) := by
  have initial := header_fields (O := O) s
  dsimp only at initial
  obtain ⟨represented, clock⟩ := bodySetup_represents (O := O) ((header (O := O)).eval s)
    (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (NativeHeader.parsedState (s 2)).word
    (NativeHeader.parsedState (s 2)).valid initial.1 initial.2.1 initial.2.2.1 initial.2.2.2
  have body := NativeBody.bodyRoutine_represents (O := O) _ _ _ _ represented
  rw [clock] at body
  exact body

/-- The actual finite parser routine agrees with the checked decoder on every
word, including malformed headers, literals, clauses and trailing junk. -/
theorem parser_decides {O : Type} (s : Store) :
    let output := (parser (O := O)).eval s
    ((output 2).isEmpty && !(output 17).head?.isSome && (output 6).head?.isSome) = (decode (s 2)).isSome := by
  dsimp only
  have represented := parser_represents (O := O) s
  rcases represented with ⟨word, _, _, valid, inside, _⟩
  rw [word, valid, inside]
  rw [← accepted_eq_decode]
  cases insideFlag : (finalState (s 2)).inside <;> cases good : (finalState (s 2)).valid <;>
    simp [accepted, NativeBody.accepts, insideFlag, good]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
