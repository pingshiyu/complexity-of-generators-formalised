import ComplexityOfGenerators.Proofs.ExpectedSourceRecords
import ComplexityOfGenerators.Foundations.FreshStreamListSequence
import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Trace
import ComplexityOfGenerators.Foundations.BalancedPairProbability

/-! Concrete fresh word records are the successful native execution traces
used by the star controller. The conversion inspects only the consumed finite
prefix, whose length is determined by the actual number of attempted blocks. -/
namespace ComplexityOfGenerators.BoundedPhaseFamily
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

noncomputable def recordSamplers (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty) :
    List (FreshStreamSampler (ℕ × List α)) :=
  parts.attach.map (fun part => P.wordRecord part.1 (active part.1 part.2))

noncomputable def recordCalls (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty) :
    FreshStreamSampler (List (ℕ × List α)) := FreshStreamSampler.sequenceList (P.recordSamplers parts active)

def nativeRecords (records : List (ℕ × List α)) : List (ExpectedStarCalls.Record α) :=
  records.map (fun record => ⟨record.1,record.2⟩)

def StreamTrace (stream : BitStream) : List ℕ → List (ExpectedStarCalls.Record α) → Prop
  | [], [] => True
  | j::parts, record::records =>
      (∀ k < record.failures, (P.phase j).value (fixedBlock (P.seed j) stream k) = none) ∧
      (P.phase j).value (fixedBlock (P.seed j) stream record.failures) = some record.word ∧
      StreamTrace (fun i => stream (record.blocks*P.seed j+i)) parts records
  | _, _ => False

theorem recordCalls_cons (j : ℕ) (parts : List ℕ)
    (active : ∀ k ∈ j::parts, (P.layer k).Nonempty) (stream : BitStream) :
    (P.recordCalls (j::parts) active).run stream =
      (let first := (P.wordRecord j (active j (by simp))).run stream
       let remaining := (P.recordCalls parts (fun k member => active k (by simp [member]))).run first.2
       (first.1::remaining.1,remaining.2)) := by
  simp [recordCalls,recordSamplers,List.attach_cons,List.map_map,Function.comp_def,
    FreshStreamSampler.sequenceList_cons]

/-- Every finite sequence of productive calls has the precise first-success
trace required by the implemented nested retry controller, almost surely. -/
theorem recordCalls_trace_ae (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty) :
    ∀ᵐ stream ∂fairCoinMeasure,
      StreamTrace P stream parts (nativeRecords ((P.recordCalls parts active).run stream).1) := by
  induction parts with
  | nil => simp [recordCalls,recordSamplers,nativeRecords,StreamTrace]
  | cons j parts ih =>
    let nextActive : ∀ k ∈ parts, (P.layer k).Nonempty := fun k member => active k (by simp [member])
    have remaining := (P.wordRecord j (active j (by simp))).tail_ae (ih nextActive)
    filter_upwards [P.wordRecord_spec_ae j (active j (by simp)),remaining] with stream first rest
    rw [recordCalls_cons]
    change StreamTrace P stream (j::parts)
      (⟨((P.wordRecord j (active j (by simp))).run stream).1.1,
         ((P.wordRecord j (active j (by simp))).run stream).1.2⟩ ::
        nativeRecords ((P.recordCalls parts nextActive).run ((P.wordRecord j (active j (by simp))).run stream).2).1)
    refine ⟨first.1,first.2,?_⟩
    simpa only [ExpectedStarCalls.Record.blocks,P.wordRecord_tail] using rest

/-- Infinite-stream records give actual native finite-tape runs on every
prefix long enough to contain their consumed blocks. -/
theorem StreamTrace.native_prefix (stream : BitStream) (total offset : ℕ) (parts : List ℕ)
    (records : List (ExpectedStarCalls.Record α))
    (trace : StreamTrace P (fun i => stream (offset+i)) parts records)
    (enough : offset+ExpectedStarCalls.consumed P parts records ≤ total) :
    ExpectedStarCalls.Trace P (streamPrefix stream total) offset parts records := by
  induction parts generalizing records offset with
  | nil => cases records <;> exact trace
  | cons j parts ih =>
    cases records with
    | nil => exact False.elim trace
    | cons record records =>
      rcases trace with ⟨failed,accepted,rest⟩
      have leading : offset+record.blocks*P.seed j ≤ total := by
        change offset+(record.blocks*P.seed j+ExpectedStarCalls.consumed P parts records) ≤ total at enough
        omega
      refine ⟨by simpa only [streamPrefix_length] using leading,?_,?_,?_⟩
      · intro k earlier
        have fits : offset+k*P.seed j+P.seed j ≤ total := by
          have within := Nat.mul_le_mul_right (P.seed j) (show k+1 ≤ record.blocks by
            unfold ExpectedStarCalls.Record.blocks; omega)
          nlinarith
        rw [BalancedPairPhase.streamPrefix_drop_take stream total (offset+k*P.seed j) (P.seed j) fits]
        have known := failed k earlier
        change UnionGenerator.sourceValue P.machine P.clock j
          (List.ofFn (fun index : Fin (P.seed j) => stream (offset+(k*P.seed j+index.val)))) = none at known
        simpa only [Nat.add_assoc] using known
      · have fits : offset+record.failures*P.seed j+P.seed j ≤ total := by
          simpa only [ExpectedStarCalls.Record.blocks,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using leading
        rw [BalancedPairPhase.streamPrefix_drop_take stream total (offset+record.failures*P.seed j) (P.seed j) fits]
        change UnionGenerator.sourceValue P.machine P.clock j
          (List.ofFn (fun index : Fin (P.seed j) => stream (offset+(record.failures*P.seed j+index.val)))) = some record.word at accepted
        simpa only [Nat.add_assoc] using accepted
      · apply ih (offset+record.blocks*P.seed j) records
        · simpa only [Nat.add_assoc] using rest
        · simpa only [ExpectedStarCalls.consumed,Nat.add_assoc] using enough

end
end ComplexityOfGenerators.BoundedPhaseFamily
