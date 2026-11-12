import ComplexityOfGenerators.Simulation.WordStack.LocalEmbedding
import ComplexityOfGenerators.Simulation.WordStack.Commands

/-! Register and alphabet embeddings preserve actual primitive command runs.
Alphabet correctness is stated on encoded words; unrelated ambient registers
are preserved by register renaming. -/

namespace ComplexityOfGenerators.Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

namespace Memory

def mapSymbols {S T O : Type} {k : ℕ} (encode : S → T) (m : Memory S O k) : Memory T O k :=
  ⟨(), m.indexHead, m.randomHead, m.output, Local.mapStore encode m.store⟩

def project {S O : Type} {k l : ℕ} (slots : Fin k → Fin l) (m : Memory S O l) : Memory S O k :=
  ⟨(), m.indexHead, m.randomHead, m.output, m.store ∘ slots⟩

end Memory

namespace Result

def mapSymbols {S T O : Type} {k : ℕ} (encode : S → T) : Result S O k → Result T O k
  | .done memory => .done (memory.mapSymbols encode)
  | .exhausted => .exhausted

def project {S O : Type} {k l : ℕ} (slots : Fin k → Fin l) : Result S O l → Result S O k
  | .done memory => .done (memory.project slots)
  | .exhausted => .exhausted

end Result

namespace Command

variable {S T O : Type} {k l : ℕ}

def mapSymbols (encode : S → T) (decode : T → S) : Command S O k → Command T O k
  | .skip => .skip
  | .act j action move emit => .act j (Local.mapAction encode action) move emit
  | .branch j next => .branch j fun observation =>
      (next (observation.1.map decode, observation.2)).mapSymbols encode decode
  | .random no yes => .random (no.mapSymbols encode decode) (yes.mapSymbols encode decode)
  | .seq first second => .seq (first.mapSymbols encode decode) (second.mapSymbols encode decode)
  | .loop j test body => .loop j (fun o => test (o.1.map decode, o.2)) (body.mapSymbols encode decode)
  | .drain => .drain

theorem mapSymbols_observe (encode : S → T) (decode : T → S) (retract : Function.LeftInverse decode encode)
    (n : ℕ) (m : Memory S O k) (j : Fin k) :
    ((observe n (m.mapSymbols encode) j).1.map decode, (observe n (m.mapSymbols encode) j).2) =
      observe n m j := by
  simp only [observe, Memory.mapSymbols, Local.mapStore, List.head?_map, Option.map_map]
  congr 2
  cases word : m.store j with
  | nil => rfl
  | cons letter rest => simp [retract letter]

theorem mapSymbols_changeMemory (encode : S → T) (n : ℕ) (m : Memory S O k) (j : Fin k)
    (action : Action S) (move : Move) (emit : Option O) :
    Program.changeMemory j n (Local.mapAction encode action) move emit (m.mapSymbols encode) =
      (Program.changeMemory j n action move emit m).mapSymbols encode := by
  apply Configuration.ext <;> try rfl
  simp only [Program.changeMemory, Memory.mapSymbols, Local.mapStore, Local.mapStore_update,
    Local.mapAction_apply]

theorem mapSymbols_readBit (encode : S → T) (m : Memory S O k) :
    Program.readBit (m.mapSymbols encode) = (Program.readBit m).mapSymbols encode := rfl

theorem Runs.mapSymbols (encode : S → T) (decode : T → S) (retract : Function.LeftInverse decode encode)
    {n : ℕ} {bits : BitString} {command : Command S O k} {memory : Memory S O k} {ticks : ℕ}
    {result : Result S O k} (run : command.Runs n bits memory ticks result) :
    (command.mapSymbols encode decode).Runs n bits (memory.mapSymbols encode) ticks (result.mapSymbols encode) := by
  induction run with
  | skip m => exact .skip _
  | act m j action move emit =>
    simpa only [Command.mapSymbols, Result.mapSymbols, mapSymbols_changeMemory] using
      (Runs.act (m.mapSymbols encode) j (Local.mapAction encode action) move emit)
  | branch m j next t result run ih =>
    apply Runs.branch _ j _ t _
    simpa only [mapSymbols_observe encode decode retract] using ih
  | random_absent m no yes absent => exact .random_absent _ _ _ absent
  | random m no yes bit t result lookup run ih =>
    apply Runs.random (m.mapSymbols encode) (no.mapSymbols encode decode) (yes.mapSymbols encode decode)
      bit t (result.mapSymbols encode) lookup
    cases bit <;> simpa [Command.mapSymbols, mapSymbols_readBit] using ih
  | seq_absent m first second t run ih => exact .seq_absent _ _ _ t ih
  | seq m middle first second s t result left right ihLeft ihRight =>
    exact .seq _ _ _ _ s t _ ihLeft ihRight
  | loop_stop m j test body stop =>
    exact .loop_stop _ j _ _ (by simpa only [mapSymbols_observe encode decode retract] using stop)
  | loop_absent m j test body t again run ih =>
    exact .loop_absent _ j _ _ t (by simpa only [mapSymbols_observe encode decode retract] using again) ih
  | loop m middle j test body s t result again run rest ihBody ihRest =>
    exact .loop _ _ j _ _ s t _ (by simpa only [mapSymbols_observe encode decode retract] using again) ihBody ihRest
  | drain m => exact .drain _

def rename (slots : Fin k → Fin l) : Command S O k → Command S O l
  | .skip => .skip
  | .act j action move emit => .act (slots j) action move emit
  | .branch j next => .branch (slots j) fun observation => (next observation).rename slots
  | .random no yes => .random (no.rename slots) (yes.rename slots)
  | .seq first second => .seq (first.rename slots) (second.rename slots)
  | .loop j test body => .loop (slots j) test (body.rename slots)
  | .drain => .drain

theorem project_observe (slots : Fin k → Fin l) (n : ℕ) (memory : Memory S O l) (j : Fin k) :
    observe n memory (slots j) = observe n (memory.project slots) j := rfl

theorem project_changeMemory (slots : Fin k ↪ Fin l) (n : ℕ) (memory : Memory S O l)
    (j : Fin k) (action : Action S) (move : Move) (emit : Option O) :
    (Program.changeMemory (slots j) n action move emit memory).project slots =
      Program.changeMemory j n action move emit (memory.project slots) := by
  apply Configuration.ext <;> try rfl
  exact Function.update_comp_eq_of_injective memory.store slots.injective j _

theorem project_readBit (slots : Fin k → Fin l) (memory : Memory S O l) :
    (Program.readBit memory).project slots = Program.readBit (memory.project slots) := rfl

end Command
end ComplexityOfGenerators.Simulation.WordStack
