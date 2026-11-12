import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native
import ComplexityOfGenerators.Simulation.WordStack.CommandEmbedding
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.LocalLoop
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops
import ComplexityOfGenerators.Simulation.WordStack.TransferWhile
import ComplexityOfGenerators.Simulation.WordStack.Unary
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput

/-! A structural certificate for deterministic finite controllers. It survives
register/alphabet embeddings and implies the actual compiled NoRandom property. -/
namespace ComplexityOfGenerators.Simulation.WordStack
set_option backward.isDefEq.respectTransparency false

namespace Command
variable {S T O : Type} {k l : ℕ}

inductive RandomFree : Command S O k → Prop
  | skip : RandomFree .skip
  | act (j action move output) : RandomFree (.act j action move output)
  | branch (j next) (pure : ∀ observation, RandomFree (next observation)) : RandomFree (.branch j next)
  | seq {first second} (left : RandomFree first) (right : RandomFree second) : RandomFree (.seq first second)
  | loop (j test) {body} (pure : RandomFree body) : RandomFree (.loop j test body)

@[simp] theorem randomFree_skip : RandomFree (.skip : Command S O k) := .skip
@[simp] theorem randomFree_act (j : Fin k) (action : Action S) (move : Move) (output : Option O) :
    RandomFree (.act j action move output) := .act _ _ _ _
@[simp] theorem randomFree_branch (j : Fin k) (next : Observation S → Command S O k) :
    RandomFree (.branch j next) ↔ ∀ observation, RandomFree (next observation) := by
  constructor
  · intro pure; cases pure with | branch _ _ pure => exact pure
  · exact .branch j next
@[simp] theorem randomFree_seq (first second : Command S O k) :
    RandomFree (.seq first second) ↔ RandomFree first ∧ RandomFree second := by
  constructor
  · intro pure; cases pure with | seq left right => exact ⟨left, right⟩
  · exact fun ⟨left, right⟩ => .seq left right
@[simp] theorem randomFree_loop (j : Fin k) (test : Observation S → Bool) (body : Command S O k) :
    RandomFree (.loop j test body) ↔ RandomFree body := by
  constructor
  · intro pure; cases pure with | loop _ _ pure => exact pure
  · exact .loop j test

private theorem redirect_not_random {Q Q' S O : Type} (rename : Q → Q')
    (exit : Instruction Q' S O) (instruction : Instruction Q S O)
    (source : match instruction with | .random _ _ => False | _ => True)
    (finish : match exit with | .random _ _ => False | _ => True) :
    match Instruction.redirect rename exit instruction with | .random _ _ => False | _ => True := by
  cases instruction <;> simp_all [Instruction.redirect]

theorem RandomFree.noRandom {c : Command S O k} (pure : RandomFree c) (idle : Fin k) :
    InputBank.NoRandom (c.program idle) := by
  induction pure with
  | skip => intro state cell index; trivial
  | act j action move output => intro state cell index; cases state <;> trivial
  | branch j next pure ih =>
    intro state cell index
    cases state with
    | none => trivial
    | some position =>
      obtain ⟨observation, state⟩ := position
      exact redirect_not_random _ _ _ (ih observation state cell index) trivial
  | seq left right ihLeft ihRight =>
    intro state cell index
    cases state with
    | inl state => exact redirect_not_random _ _ _ (ihLeft state cell index) trivial
    | inr state => exact redirect_not_random _ _ _ (ihRight state cell index) trivial
  | loop j test pure ih =>
    intro state cell index
    cases state with
    | none => cases guarded : test (cell, index) <;> simp [program, Program.loop, guarded]
    | some state => exact redirect_not_random _ _ _ (ih state cell index) trivial

theorem RandomFree.mapSymbols {c : Command S O k} (pure : RandomFree c) (encode : S → T) (decode : T → S) :
    RandomFree (c.mapSymbols encode decode) := by
  induction pure with
  | skip => exact .skip
  | act => exact .act _ _ _ _
  | branch j next pure ih => exact .branch _ _ (fun observation => ih (observation.1.map decode, observation.2))
  | seq left right ihLeft ihRight => exact .seq ihLeft ihRight
  | loop j test pure ih => exact .loop _ _ ih

theorem RandomFree.rename {c : Command S O k} (pure : RandomFree c) (slots : Fin k ↪ Fin l) :
    RandomFree (c.rename slots) := by
  induction pure with
  | skip => exact .skip
  | act => exact .act _ _ _ _
  | branch j next pure ih => exact .branch _ _ ih
  | seq left right ihLeft ihRight => exact .seq ihLeft ihRight
  | loop j test pure ih => exact .loop _ _ ih

end Command

namespace Local
variable {S O : Type} {k : ℕ}

@[simp] theorem command_randomFree (code : Local S k) : Command.RandomFree (code.command (O := O)) := by
  induction code with
  | skip => exact .skip
  | act => exact .act _ _ _ _
  | read j next ih => exact .branch _ _ (fun observation => ih observation.1)
  | seq first second ihFirst ihSecond => exact .seq ihFirst ihSecond

@[simp] theorem clocked_randomFree (counter : Fin k) (body : Local S k) :
    Command.RandomFree (clocked (O := O) counter body) := by
  apply Command.RandomFree.loop
  exact command_randomFree _

end Local

namespace Command
variable {S O : Type} {k : ℕ}

@[simp] theorem randomFree_push (j : Fin k) (symbol : S) : RandomFree (push (O := O) j symbol) := .act _ _ _ _
@[simp] theorem randomFree_pop (j : Fin k) : RandomFree (pop (S := S) (O := O) j) := .act _ _ _ _
@[simp] theorem randomFree_clear (j : Fin k) : RandomFree (clear (S := S) (O := O) j) := by simp [clear]
@[simp] theorem randomFree_transfer (src dst : Fin k) (map : S → S) : RandomFree (transfer (O := O) src dst map) := by
  simp only [transfer, randomFree_loop, randomFree_branch]
  intro observation
  cases observation.1 <;> simp
@[simp] theorem randomFree_duplicateTransfer (src first second : Fin k) (f g : S → S) :
    RandomFree (duplicateTransfer (O := O) src first second f g) := by
  simp only [duplicateTransfer, randomFree_loop, randomFree_branch]
  intro observation
  cases observation.1 <;> simp
@[simp] theorem randomFree_copy (src dst scratch : Fin k) (map : S → S) : RandomFree (copy (O := O) src dst scratch map) := by
  simp [copy]
@[simp] theorem randomFree_loadIndex (dst : Fin k) (unit : S) : RandomFree (loadIndex (O := O) dst unit) := by
  simp [loadIndex]
@[simp] theorem randomFree_transferWhile (src dst : Fin k) (keep : S → Bool) (map : S → S) :
    RandomFree (transferWhile (O := O) src dst keep map) := by
  simp only [transferWhile, randomFree_loop, randomFree_branch]
  intro observation
  cases observation.1 <;> simp
@[simp] theorem randomFree_emitWord (src : Fin k) (decode : S → Option O) : RandomFree (emitWord src decode) := by
  simp only [emitWord, randomFree_loop, randomFree_branch]
  intro observation
  cases observation.1 <;> simp
@[simp] theorem randomFree_emitFixed (register : Fin k) (word : List O) : RandomFree (emitFixed (S := S) register word) := by
  induction word with | nil => exact .skip | cons symbol rest ih => exact .seq (.act _ _ _ _) ih

end Command

namespace Routine
variable {S O : Type} {k : ℕ}

@[simp] theorem randomFree_ofLocal (code : Local S k) : Command.RandomFree (ofLocal (O := O) code).command :=
  Local.command_randomFree code
@[simp] theorem randomFree_skip : Command.RandomFree (skip (S := S) (O := O) (k := k)).command := .skip
@[simp] theorem randomFree_seq (a b : Routine S O k) :
    Command.RandomFree (a.seq b).command ↔ Command.RandomFree a.command ∧ Command.RandomFree b.command := by
  simp [Routine.seq]
@[simp] theorem randomFree_branch (j : Fin k) (next : Option S → Routine S O k) :
    Command.RandomFree (branch j next).command ↔ ∀ head, Command.RandomFree (next head).command := by
  simp only [branch, Command.randomFree_branch]
  exact ⟨fun pure head => pure (head, none), fun pure observation => pure observation.1⟩
@[simp] theorem randomFree_clear (j : Fin k) : Command.RandomFree (clear (S := S) (O := O) j).command :=
  Command.randomFree_clear j
@[simp] theorem randomFree_transfer (src dst : Fin k) (different : src ≠ dst) (map : S → S) :
    Command.RandomFree (transfer (O := O) src dst different map).command := Command.randomFree_transfer src dst map
@[simp] theorem randomFree_copy (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch) (map : S → S) :
    Command.RandomFree (copy (O := O) src dst scratch sd st dt map).command := by simp [copy]
@[simp] theorem randomFree_assign (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch) (map : S → S) :
    Command.RandomFree (assign (O := O) src dst scratch sd st dt map).command := by simp [assign]
@[simp] theorem randomFree_clearMany (registers : List (Fin k)) :
    Command.RandomFree (clearMany (S := S) (O := O) registers).command := by
  induction registers with
  | nil => exact .skip
  | cons j rest ih => simpa [clearMany] using And.intro (randomFree_clear (S := S) (O := O) j) ih
@[simp] theorem randomFree_transferWhile (src dst : Fin k) (different : src ≠ dst) (keep : S → Bool) (map : S → S) :
    Command.RandomFree (transferWhile (O := O) src dst different keep map).command := Command.randomFree_transferWhile src dst keep map
@[simp] theorem randomFree_clocked [Fintype S] (clock : Fin k) (body : Local S k) (frame) :
    Command.RandomFree (clocked (O := O) clock body frame).command := Local.clocked_randomFree clock body
@[simp] theorem randomFree_iterate (clock : Fin k) (body : Routine S O k) (frame)
    (pure : Command.RandomFree body.command) : Command.RandomFree (iterate clock body frame).command := by
  simpa [iterate, counted] using pure

@[simp] theorem randomFree_rename {l : ℕ} (routine : Routine S O k) (slots : Fin k ↪ Fin l)
    (pure : Command.RandomFree routine.command) : Command.RandomFree (routine.rename slots).command :=
  (pure.mapSymbols id id).rename slots

end Routine
end ComplexityOfGenerators.Simulation.WordStack
