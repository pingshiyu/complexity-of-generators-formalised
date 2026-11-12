import ComplexityOfGenerators.Simulation.WordStack.CommandEmbedding
import ComplexityOfGenerators.Simulation.WordStack.Routines

namespace ComplexityOfGenerators.Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

namespace Memory

variable {S O : Type} {k l : ℕ}

noncomputable def patchStore (slots : Fin k ↪ Fin l) (source : Fin k → List S)
    (ambient : Fin l → List S) : Fin l → List S := by
  classical
  exact fun j => if member : ∃ i, slots i = j then source (Classical.choose member) else ambient j

@[simp] theorem patchStore_here (slots : Fin k ↪ Fin l) (source : Fin k → List S)
    (ambient : Fin l → List S) (i : Fin k) : patchStore slots source ambient (slots i) = source i := by
  classical
  unfold patchStore
  split_ifs with member
  · have same := slots.injective (Classical.choose_spec member)
    rw [same]
  · exact False.elim (member ⟨i, rfl⟩)

theorem patchStore_outside (slots : Fin k ↪ Fin l) (source : Fin k → List S)
    (ambient : Fin l → List S) (j : Fin l) (outside : ∀ i, j ≠ slots i) :
    patchStore slots source ambient j = ambient j := by
  classical
  have absent : ¬ ∃ i, slots i = j := by rintro ⟨i, equal⟩; exact outside i equal.symm
  simp [patchStore, absent]

theorem patchStore_update (slots : Fin k ↪ Fin l) (source : Fin k → List S)
    (ambient : Fin l → List S) (i : Fin k) (word : List S) :
    patchStore slots (Function.update source i word) ambient =
      Function.update (patchStore slots source ambient) (slots i) word := by
  classical
  funext j
  by_cases member : ∃ a, slots a = j
  · obtain ⟨a, rfl⟩ := member
    by_cases same : a = i
    · subst a; simp
    · have different : slots a ≠ slots i := fun equal => same (slots.injective equal)
      simp [same, different]
  · have outside : ∀ a, j ≠ slots a := by intro a equal; exact member ⟨a, equal.symm⟩
    have different := outside i
    rw [patchStore_outside slots _ _ j outside, Function.update_of_ne different,
      patchStore_outside slots _ _ j outside]

noncomputable def patch (slots : Fin k ↪ Fin l) (source : Memory S O k) (ambient : Memory S O l) : Memory S O l :=
  ⟨(), source.indexHead, source.randomHead, source.output, patchStore slots source.store ambient.store⟩

theorem patch_eq (slots : Fin k ↪ Fin l) (source : Memory S O k) (ambient : Memory S O l)
    (related : ambient.project slots = source) : patch slots source ambient = ambient := by
  subst source
  apply Configuration.ext <;> try rfl
  funext j
  by_cases member : ∃ i, slots i = j
  · obtain ⟨i, rfl⟩ := member
    simp [patch, project]
  · apply patchStore_outside
    intro i equal
    exact member ⟨i, equal.symm⟩

end Memory

namespace Result

noncomputable def patch {S O : Type} {k l : ℕ} (slots : Fin k ↪ Fin l) (ambient : Memory S O l) :
    Result S O k → Result S O l
  | .done source => .done (Memory.patch slots source ambient)
  | .exhausted => .exhausted

end Result

namespace Command

variable {S O : Type} {k l : ℕ}

theorem patch_observe (slots : Fin k ↪ Fin l) (n : ℕ) (source : Memory S O k)
    (ambient : Memory S O l) (j : Fin k) :
    observe n (Memory.patch slots source ambient) (slots j) = observe n source j := by
  simp [observe, Memory.patch]

theorem patch_changeMemory (slots : Fin k ↪ Fin l) (n : ℕ) (source : Memory S O k)
    (ambient : Memory S O l) (j : Fin k) (action : Action S) (move : Move) (emit : Option O) :
    Program.changeMemory (slots j) n action move emit (Memory.patch slots source ambient) =
      Memory.patch slots (Program.changeMemory j n action move emit source) ambient := by
  apply Configuration.ext <;> try rfl
  simp only [Program.changeMemory, Memory.patch, Memory.patchStore_here, Memory.patchStore_update]

theorem patch_readBit (slots : Fin k ↪ Fin l) (source : Memory S O k) (ambient : Memory S O l) :
    Program.readBit (Memory.patch slots source ambient) = Memory.patch slots (Program.readBit source) ambient := rfl

theorem Runs.rename (slots : Fin k ↪ Fin l) {n : ℕ} {bits : BitString}
    {command : Command S O k} {memory : Memory S O k} {ticks : ℕ} {result : Result S O k}
    (run : command.Runs n bits memory ticks result) (ambient : Memory S O l) :
    (command.rename slots).Runs n bits (Memory.patch slots memory ambient) ticks (result.patch slots ambient) := by
  induction run with
  | skip m => exact .skip _
  | act m j action move emit =>
    simpa only [Command.rename, Result.patch, patch_changeMemory] using
      (Runs.act (Memory.patch slots m ambient) (slots j) action move emit)
  | branch m j next t result run ih =>
    apply Runs.branch _ (slots j) _ t _
    simpa only [patch_observe] using ih
  | random_absent m no yes absent => exact .random_absent _ _ _ absent
  | random m no yes bit t result lookup run ih =>
    apply Runs.random (Memory.patch slots m ambient) (no.rename slots) (yes.rename slots)
      bit t (result.patch slots ambient) lookup
    cases bit <;> simpa [Command.rename, patch_readBit] using ih
  | seq_absent m first second t run ih => exact .seq_absent _ _ _ t ih
  | seq m middle first second s t result left right ihLeft ihRight =>
    exact .seq _ _ _ _ s t _ ihLeft ihRight
  | loop_stop m j test body stop =>
    exact .loop_stop _ (slots j) _ _ (by simpa only [patch_observe] using stop)
  | loop_absent m j test body t again run ih =>
    exact .loop_absent _ (slots j) _ _ t (by simpa only [patch_observe] using again) ih
  | loop m middle j test body s t result again run rest ihBody ihRest =>
    exact .loop _ _ (slots j) _ _ s t _ (by simpa only [patch_observe] using again) ihBody ihRest
  | drain m => exact .drain _

end Command

namespace Routine

variable {S T O : Type} {k l : ℕ}

/-- The embedded finite command. Its semantics below require that the caller
prepared the owned registers using the alphabet encoding. -/
def embeddedCommand (routine : Routine S O k) (slots : Fin k ↪ Fin l)
    (encode : S → T) (decode : T → S) : Command T O l :=
  (routine.command.mapSymbols encode decode).rename slots

theorem embedded_runs (routine : Routine S O k) (slots : Fin k ↪ Fin l)
    (encode : S → T) (decode : T → S) (retract : Function.LeftInverse decode encode)
    {n : ℕ} (bits : BitString) (ambient : Memory T O l) (source : Local.Store S k)
    (index : ambient.indexHead ≤ n)
    (prepared : ∀ j, ambient.store (slots j) = (source j).map encode) :
    ∃ ticks ≤ routine.cost source,
      (routine.embeddedCommand slots encode decode).Runs n bits ambient ticks
        (.done {ambient with store := (Memory.patchStore slots
          (Local.mapStore encode (routine.eval source)) ambient.store)}) := by
  let initial : Memory S O k := ⟨(), ambient.indexHead, ambient.randomHead, ambient.output, source⟩
  obtain ⟨ticks, cost, run⟩ := routine.runs (n := n) bits initial index
  have mapped := run.mapSymbols encode decode retract
  have renamed := mapped.rename slots ambient
  have initial_eq : Memory.patch slots (initial.mapSymbols encode) ambient = ambient := by
    apply Memory.patch_eq
    apply Configuration.ext <;> try rfl
    funext j; exact prepared j
  rw [initial_eq] at renamed
  exact ⟨ticks, cost, renamed⟩

/-- Pure register renaming is total on every ambient store; no alphabet
invariant is needed when the source and target alphabets coincide. -/
noncomputable def rename (routine : Routine S O k) (slots : Fin k ↪ Fin l) : Routine S O l where
  command := routine.embeddedCommand slots id id
  eval := fun ambient => Memory.patchStore slots (routine.eval (ambient ∘ slots)) ambient
  cost := fun ambient => routine.cost (ambient ∘ slots)
  runs bits ambient index := by
    obtain ⟨ticks, cost, run⟩ := routine.embedded_runs slots id id (by intro value; rfl)
      bits ambient (ambient.store ∘ slots) index (by intro j; simp)
    have mapped : Local.mapStore (id : S → S) (routine.eval (ambient.store ∘ slots)) =
        routine.eval (ambient.store ∘ slots) := by
      funext j
      simp [Local.mapStore]
    exact ⟨ticks, cost, by simpa only [mapped] using run⟩

@[simp] theorem rename_eval_here (routine : Routine S O k) (slots : Fin k ↪ Fin l)
    (ambient : Local.Store S l) (j : Fin k) :
    (routine.rename slots).eval ambient (slots j) = routine.eval (ambient ∘ slots) j := by
  simp [rename]

theorem rename_eval_frame (routine : Routine S O k) (slots : Fin k ↪ Fin l)
    (ambient : Local.Store S l) (j : Fin l) (outside : ∀ i, j ≠ slots i) :
    (routine.rename slots).eval ambient j = ambient j :=
  Memory.patchStore_outside slots _ _ j outside

@[simp] theorem rename_cost (routine : Routine S O k) (slots : Fin k ↪ Fin l) (ambient : Local.Store S l) :
    (routine.rename slots).cost ambient = routine.cost (ambient ∘ slots) := rfl

end Routine
end ComplexityOfGenerators.Simulation.WordStack
