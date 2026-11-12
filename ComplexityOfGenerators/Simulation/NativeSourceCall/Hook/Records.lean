import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Paths
import ComplexityOfGenerators.Proofs.GeneratorSupport

/-! Finite records of actual original-source calls. Every record contains a
native path, not an assumed sampler implementation. Sequential offsets are the
actual consumed random-bit counts. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook

structure CallRecord (O : Type) where
  word : List O
  time : ℕ
  coins : ℕ

def words {O : Type} (records : List (CallRecord O)) : List O := (records.map CallRecord.word).flatten
def totalTime {O : Type} (records : List (CallRecord O)) : ℕ := (records.map CallRecord.time).sum
def totalCoins {O : Type} (records : List (CallRecord O)) : ℕ := (records.map CallRecord.coins).sum

noncomputable section
variable {E O : Type} [Fintype E] [Fintype O] (M : Machine Unit Bool O) (start : E → Fin M.states)

def CallAt (bits : BitString) (offset : ℕ) (event : E) (index : ℕ) (record : CallRecord O) : Prop :=
  ∃ finish : Configuration (selectedSource M start event),
    (selectedSource M start event).Steps (generatorData index) (bits.drop offset)
      (selectedSource M start event).initialConfiguration record.time finish ∧
    (selectedSource M start event).observe (generatorData index) (bits.drop offset) finish=.halted (.accepted record.word) ∧
    finish.randomHead=record.coins

theorem CallAt.mem_language {bits : BitString} {offset : ℕ} {event : E} {index : ℕ} {record : CallRecord O}
    (call : CallAt M start bits offset event index record) :
    record.word∈(selectedSource M start event).generatedLanguage (generatorData index) := by
  obtain ⟨finish,path,accepted,cursor⟩ := call
  apply ((selectedSource M start event).mem_generatedLanguage_iff_produces (generatorData index) record.word).mpr
  refine ⟨bits.drop offset,record.time,?_⟩
  rw [←(selectedSource M start event).runFrom_initial]
  exact (path.runFrom (selectedSource M start event)).trans accepted

def SourceCalls (bits : BitString) (offset : ℕ) : List (E×ℕ) → List (CallRecord O) → Prop
  | [],[] => True
  | entry::events,record::records => CallAt M start bits offset entry.1 entry.2 record ∧
      SourceCalls bits (offset+record.coins) events records
  | _,_ => False

theorem SourceCalls.length_eq {bits : BitString} {offset : ℕ} {events : List (E×ℕ)} {records : List (CallRecord O)}
    (calls : SourceCalls M start bits offset events records) : records.length=events.length := by
  induction events generalizing offset records with
  | nil => cases records <;> simp_all [SourceCalls]
  | cons event events ih =>
      cases records with
      | nil => exact False.elim calls
      | cons record records =>
          simpa only [List.length_cons] using congrArg (·+1) (ih calls.2)

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
