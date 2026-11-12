import ComplexityOfGenerators.Simulation.FixedBlockRetry.Components

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry

open WordStack

variable {S O : Type} [Fintype S] (unitSymbol : S) (bitSymbol : Bool → S)

structure State (n cap : ℕ) (m : Memory S O 35) : Prop where
  head : m.indexHead ≤ n
  index : (m.store 13).length = n
  master : (m.store 22).length = n
  output : m.output = []
  sizes : StoreBound m.store cap

theorem collected_state {n cap : ℕ} {m : Memory S O 35} (state : State n cap m)
    (count : ℕ) (block : BitString) (indexBudget : n + 1 ≤ cap) (blockBudget : block.length ≤ cap) :
    State n cap (collectedMemory unitSymbol bitSymbol n count block m) := by
  constructor
  · exact state.head
  · simpa [collectedMemory] using state.index
  · simpa [collectedMemory] using state.master
  · exact state.output
  · exact collectedMemory_bound unitSymbol bitSymbol n count block m cap state.sizes indexBudget blockBudget

theorem restored_state (n cap : ℕ) (m : Memory S O 35) (head : m.indexHead ≤ n)
    (master : (m.store 22).length = n) (output : m.output = []) (sizes : StoreBound m.store cap) :
    State n cap {m with store := (restoreIndex (O := O) unitSymbol).eval m.store} := by
  constructor
  · exact head
  · simpa [restoreIndex, WordStack.Routine.assign_eval] using master
  · simpa [restoreIndex, WordStack.Routine.assign_eval] using master
  · exact output
  · exact sizes.assign 22 13 33 (by decide) (by decide) (by decide) (fun _ => unitSymbol)

theorem restore_cost (s : Local.Store S 35) (cap : ℕ) (sizes : StoreBound s cap) :
    (restoreIndex (O := O) unitSymbol).cost s ≤ 20 * cap + 3 := by
  have h13 := sizes 13
  have h22 := sizes 22
  have h33 := sizes 33
  simp only [restoreIndex, WordStack.Routine.assign_cost]
  omega

noncomputable def attemptBudget (width cap time : PolynomialBound) (n : ℕ) : ℕ :=
  collectBudget width n (cap n) + time n + 20 * cap n + 5

theorem attempt_full_at_index_with_post {Payload : Type} (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)
    (Q : Local.Store S 35 → Prop)
    (post : ∀ (n : ℕ) (block : BitString) (s : Local.Store S 35), block.length = width n →
      (s 13).length = n → (s 22).length = n → s 17 = block.map bitSymbol → Q (phase.eval s))
    (restored : ∀ s, Q s → Q ((restoreIndex (O := O) unitSymbol).eval s))
    (n inputIndex : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n (cap n) m)
    (within : n ≤ inputIndex) (indexBudget : n + 1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : width n ≤ bits.length - m.randomHead) :
    let block := (bits.drop m.randomHead).take (width n)
    ∃ t ≤ attemptBudget width cap time n, ∃ next,
      (attempt unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.indexHead = m.indexHead ∧ next.randomHead = m.randomHead + width n ∧ Q next.store ∧
      next.store 32 = flagWord unitSymbol (f n block).isSome ∧
      ∀ word, f n block = some word → (next.store 31).filterMap decode = word := by
  let block := (bits.drop m.randomHead).take (width n)
  have length : block.length = width n := by simp [block, Nat.min_eq_left enough]
  let ready := collectedMemory unitSymbol bitSymbol n (width n) block m
  obtain ⟨collectTime, collectCost, collectRun⟩ := collect_runs_at_index unitSymbol bitSymbol width n (cap n) inputIndex bits m
    (state.head.trans within) state.index state.sizes
  rw [ite_eq_left enough] at collectRun
  have readyState : State n (cap n) ready := collected_state unitSymbol bitSymbol state (width n) block indexBudget (by omega)
  have random : ready.store 17 = block.map bitSymbol := by simp [ready, collectedMemory]
  obtain ⟨phaseSize, phaseCost⟩ := bounded n block ready.store length readyState.index readyState.master random readyState.sizes
  have phaseValue := correct n block ready.store length readyState.index readyState.master random
  obtain ⟨phaseTime, phaseTicks, phaseRun⟩ := phase.runs bits ready (readyState.head.trans within)
  let afterPhase : Memory S O 35 := {ready with store := phase.eval ready.store}
  have master : (afterPhase.store 22).length = n := by
    change (phase.eval ready.store 22).length = n
    exact (frame ready.store).trans readyState.master
  obtain ⟨restoreTime, restoreTicks, restoreRun⟩ := (restoreIndex (O := O) unitSymbol).runs bits afterPhase (readyState.head.trans within)
  let next : Memory S O 35 := {afterPhase with store := (restoreIndex (O := O) unitSymbol).eval afterPhase.store}
  have nextState : State n (cap n) next := restored_state unitSymbol n (cap n) afterPhase readyState.head master readyState.output phaseSize
  have restoreCost := restore_cost (O := O) unitSymbol afterPhase.store (cap n) phaseSize
  have run := Command.Runs.seq _ _ _ _ _ _ _ collectRun
    (Command.Runs.seq _ _ _ _ _ _ _ phaseRun restoreRun)
  refine ⟨collectTime + 1 + (phaseTime + 1 + restoreTime), ?_, next, run, nextState, rfl, rfl,
    restored afterPhase.store (post n block ready.store length readyState.index readyState.master random), ?_, ?_⟩
  · change phaseTime ≤ phase.cost ready.store at phaseTicks
    change restoreTime ≤ (restoreIndex (O := O) unitSymbol).cost afterPhase.store at restoreTicks
    dsimp only [attemptBudget]
    omega
  · simpa [next, afterPhase, restoreIndex, WordStack.Routine.assign_eval] using phaseValue.1
  · intro word output
    simpa [next, afterPhase, restoreIndex, WordStack.Routine.assign_eval] using phaseValue.2 word output

theorem attempt_full_at_index_preserves_head {Payload : Type} (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)
    (n inputIndex : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n (cap n) m)
    (within : n ≤ inputIndex) (indexBudget : n + 1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : width n ≤ bits.length - m.randomHead) :
    let block := (bits.drop m.randomHead).take (width n)
    ∃ t ≤ attemptBudget width cap time n, ∃ next,
      (attempt unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.indexHead = m.indexHead ∧ next.randomHead = m.randomHead + width n ∧
      next.store 32 = flagWord unitSymbol (f n block).isSome ∧
      ∀ word, f n block = some word → (next.store 31).filterMap decode = word := by
  obtain ⟨ticks, cost, next, run, state, origin, head, _, flag, payload⟩ :=
    attempt_full_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame
      (fun _ => True) (by intros; trivial) (by intros; trivial) n inputIndex bits m state within indexBudget widthBudget enough
  exact ⟨ticks, cost, next, run, state, origin, head, flag, payload⟩

theorem attempt_full_at_index {Payload : Type} (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)
    (n inputIndex : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n (cap n) m)
    (within : n ≤ inputIndex) (indexBudget : n + 1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : width n ≤ bits.length - m.randomHead) :
    let block := (bits.drop m.randomHead).take (width n)
    ∃ t ≤ attemptBudget width cap time n, ∃ next,
      (attempt unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.randomHead = m.randomHead + width n ∧
      next.store 32 = flagWord unitSymbol (f n block).isSome ∧
      ∀ word, f n block = some word → (next.store 31).filterMap decode = word := by
  obtain ⟨ticks, cost, next, run, state, origin, head, flag, payload⟩ :=
    attempt_full_at_index_preserves_head unitSymbol bitSymbol width cap time phase decode f correct bounded frame
      n inputIndex bits m state within indexBudget widthBudget enough
  exact ⟨ticks, cost, next, run, state, head, flag, payload⟩

theorem attempt_full {Payload : Type} (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)
    (n : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n (cap n) m)
    (indexBudget : n + 1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : width n ≤ bits.length - m.randomHead) :
    let block := (bits.drop m.randomHead).take (width n)
    ∃ t ≤ attemptBudget width cap time n, ∃ next,
      (attempt unitSymbol bitSymbol width phase).Runs n bits m t (.done next) ∧
      State n (cap n) next ∧ next.randomHead = m.randomHead + width n ∧
      next.store 32 = flagWord unitSymbol (f n block).isSome ∧
      ∀ word, f n block = some word → (next.store 31).filterMap decode = word :=
  attempt_full_at_index unitSymbol bitSymbol width cap time phase decode f correct bounded frame
    n n bits m state le_rfl indexBudget widthBudget enough

theorem attempt_short_at_index (width : PolynomialBound) (phase : WordStack.Routine S O 35)
    (n cap inputIndex : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n cap m)
    (within : n ≤ inputIndex) (short : bits.length - m.randomHead < width n) :
    ∃ t ≤ collectBudget width n cap, (attempt unitSymbol bitSymbol width phase).Runs inputIndex bits m t .exhausted := by
  obtain ⟨t, cost, run⟩ := collect_runs_at_index unitSymbol bitSymbol width n cap inputIndex bits m (state.head.trans within) state.index state.sizes
  rw [ite_eq_right (by omega : ¬width n ≤ bits.length - m.randomHead)] at run
  exact ⟨t, cost, Command.Runs.seq_absent m _ _ t run⟩

theorem attempt_short (width : PolynomialBound) (phase : WordStack.Routine S O 35)
    (n cap : ℕ) (bits : BitString) (m : Memory S O 35) (state : State n cap m)
    (short : bits.length - m.randomHead < width n) :
    ∃ t ≤ collectBudget width n cap, (attempt unitSymbol bitSymbol width phase).Runs n bits m t .exhausted :=
  attempt_short_at_index unitSymbol bitSymbol width phase n cap n bits m state le_rfl short

end ComplexityOfGenerators.Simulation.FixedBlockRetry
