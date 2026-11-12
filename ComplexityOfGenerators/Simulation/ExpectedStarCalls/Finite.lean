import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Call
import ComplexityOfGenerators.Simulation.FixedBlockRetry.ValueProperties

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

theorem scan_none (width count : ℕ) (phase : BitString → Option (List α)) (bits : BitString)
    (failed : ∀ k < count, phase ((bits.drop (k*width)).take width) = none) :
    FixedBlockRetry.scan width phase count bits = none := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih =>
      have first := failed 0 (by omega)
      simp only [Nat.zero_mul, List.drop_zero] at first
      simp only [FixedBlockRetry.scan, first, Option.or]
      apply ih
      intro k less
      have later := failed (k+1) (by omega)
      simpa only [List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm width] using later

theorem retry_runs_exhausted (inputIndex j : ℕ) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (owned : ∀ i, m.store (innerSlots i) = (initialStore P j i).map Sum.inr)
    (within : j ≤ inputIndex)
    (failed : ∀ k < (bits.length-m.randomHead)/P.seed j,
      UnionGenerator.sourceValue P.machine P.clock j
        ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none) :
    ∃ ticks, (retry P).Runs inputIndex bits m ticks .exhausted := by
  let start := startMemory P j m
  obtain ⟨ticks, _, result, run, selected, _, _⟩ :=
    FixedBlockRetry.loop_runs_at_index_preserves_head
      (UnionGenerator.Symbol.unit : InnerCell P) UnionGenerator.Symbol.bit P.seed
      (BoundedMachinePhase.cap P.seed P.clock) (BoundedMachinePhase.time P.machine P.seed P.clock)
      (BoundedMachinePhase.phase P.machine P.seed P.clock) (UnionGenerator.outputLetter P.machine P.machine)
      (fun n block => UnionGenerator.sourceValue P.machine P.clock n block)
      (BoundedMachinePhase.phase_correct P.machine P.seed P.clock)
      (BoundedMachinePhase.phase_bound P.machine P.seed P.clock)
      (fun s => congrArg List.length (BoundedMachinePhase.phase_fixes22 P.machine P.seed P.clock s))
      j ((bits.length-m.randomHead)/P.seed j) inputIndex bits start (startMemory_state P j m origin empty)
      (by simp [start, startMemory, initialStore]) within (BoundedMachinePhase.indexBudget P.seed P.clock j)
      (BoundedMachinePhase.widthBudget P.seed P.clock j) rfl
  have absent : FixedBlockRetry.scan (P.seed j) (fun block => UnionGenerator.sourceValue P.machine P.clock j block)
      ((bits.length-m.randomHead)/P.seed j) (bits.drop m.randomHead) = none := by
    apply scan_none
    intro k less
    simpa only [List.drop_drop] using failed k less
  change FixedBlockRetry.selected (UnionGenerator.outputLetter P.machine P.machine) result =
    FixedBlockRetry.scan (P.seed j) (fun block => UnionGenerator.sourceValue P.machine P.clock j block)
      ((bits.length-m.randomHead)/P.seed j) (bits.drop m.randomHead) at selected
  rw [absent] at selected
  cases result with
  | exhausted => exact ⟨ticks, retry_lift P owned run⟩
  | done next => simp [FixedBlockRetry.selected] at selected

theorem source_member (j offset failures : ℕ) (bits : BitString) (word : List α)
    (enough : offset+(failures+1)*P.seed j ≤ bits.length)
    (hit : UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (offset+failures*P.seed j)).take (P.seed j)) = some word) : word ∈ P.layer j := by
  let block := (bits.drop (offset+failures*P.seed j)).take (P.seed j)
  have length : block.length = P.seed j := by
    simp only [block, List.length_take, List.length_drop]
    apply Nat.min_eq_left
    have one : offset+failures*P.seed j+P.seed j ≤ bits.length := by nlinarith
    omega
  let vector := (blockListEquiv (P.seed j)).symm ⟨block, length⟩
  have recovered : List.ofFn vector = block :=
    congrArg Subtype.val ((blockListEquiv (P.seed j)).apply_symm_apply ⟨block, length⟩)
  rw [P.layer_iff]
  exact ⟨vector, by simpa only [recovered] using hit⟩

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

def FiniteCallPost (before : Memory (Cell (β := β) P) α 80) (j : ℕ) (parts : List ℕ) : Result (Cell (β := β) P) α 80 → Prop
  | .exhausted => True
  | .done next => ∃ failures word, CallPost P encode before next j failures parts word ∧ word ∈ P.layer j

include retract in
theorem call_runs_total (inputIndex j : ℕ) (parts : List ℕ) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode (j::parts)) (within : j ≤ inputIndex) :
    ∃ ticks result, (call P decode).Runs inputIndex bits m ticks result ∧ FiniteCallPost P encode m j parts result := by
  let count := (bits.length-m.randomHead)/P.seed j
  let good := fun k => k < count ∧ (UnionGenerator.sourceValue P.machine P.clock j
    ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j))).isSome = true
  by_cases existsHit : ∃ k, good k
  · let first := Nat.find existsHit
    have found : good first := Nat.find_spec existsHit
    change first < count ∧ (UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+first*P.seed j)).take (P.seed j))).isSome = true at found
    have fits : m.randomHead+(first+1)*P.seed j ≤ bits.length := by
      have available : first+1 ≤ count := by omega
      have bounded := (Nat.mul_le_mul_right (P.seed j) available).trans (Nat.div_mul_le_self (bits.length-m.randomHead) (P.seed j))
      have consumedPositive : 0 < (first+1)*P.seed j := Nat.mul_pos (by omega) (P.seed.positive j)
      omega
    have failed (k : ℕ) (less : k < first) : UnionGenerator.sourceValue P.machine P.clock j
        ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none := by
      cases output : UnionGenerator.sourceValue P.machine P.clock j
          ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) with
      | none => rfl
      | some word =>
          have earlier : good k := ⟨by omega, by simp [output]⟩
          have least : first ≤ k := Nat.find_min' existsHit earlier
          omega
    cases hit : UnionGenerator.sourceValue P.machine P.clock j
        ((bits.drop (m.randomHead+first*P.seed j)).take (P.seed j)) with
    | none => simp [good, hit] at found
    | some word =>
        obtain ⟨ticks, _, next, run, post⟩ := call_runs_success P encode decode retract inputIndex j first parts word bits m
          origin empty path within fits failed hit
        exact ⟨ticks, .done next, run, first, word, post, source_member P j m.randomHead first bits word fits hit⟩
  · have failed (k : ℕ) (less : k < count) : UnionGenerator.sourceValue P.machine P.clock j
        ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none := by
      cases output : UnionGenerator.sourceValue P.machine P.clock j
          ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) with
      | none => rfl
      | some word => exact False.elim (existsHit ⟨k, less, by simp [output]⟩)
    let a : Memory (Cell (β := β) P) α 80 := {m with store := (parseFactor P decode).eval m.store}
    let b : Memory (Cell (β := β) P) α 80 := {a with store := (setup P).eval a.store}
    have parsed := parseFactor_fields P encode decode retract m.store j parts path
    have owned (i : Fin 35) : b.store (innerSlots i) = (initialStore P j i).map Sum.inr := by
      rw [show b.store (innerSlots i) = (setup P).eval a.store (innerSlots i) from rfl, setup_owned]
      change (initialStore P (((parseFactor P decode).eval m.store) 71).length i).map Sum.inr = _
      rw [parsed.2, List.length_replicate]
    obtain ⟨first, _, firstRun⟩ := (parseFactor P decode).runs (n := inputIndex) bits m (by omega)
    obtain ⟨second, _, secondRun⟩ := (setup P).runs (n := inputIndex) bits a (by change m.indexHead ≤ inputIndex; omega)
    obtain ⟨last, lastRun⟩ := retry_runs_exhausted P inputIndex j bits b origin empty owned within failed
    exact ⟨first+1+(second+1+last), .exhausted,
      Command.Runs.seq _ _ _ _ _ _ _ firstRun (Command.Runs.seq _ _ _ _ _ _ _ secondRun
        (Command.Runs.seq_absent _ _ _ _ lastRun)), trivial⟩

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
