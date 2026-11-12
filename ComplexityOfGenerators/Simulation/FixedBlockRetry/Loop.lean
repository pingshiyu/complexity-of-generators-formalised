import ComplexityOfGenerators.Simulation.FixedBlockRetry.State

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O Payload : Type} [Fintype S] (unitSymbol : S) (bitSymbol : Bool → S)
    (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)

def Finished (n cap : ℕ) : Result S O 35 → Prop
  | .exhausted => True
  | .done memory => State n cap memory ∧ memory.store 32 ≠ []

noncomputable def loopBudget (n count : ℕ) : ℕ :=
  count * (attemptBudget width cap time n + 2) + collectBudget width n (cap n) + 1

include correct bounded frame in
theorem loop_runs_at_index_with_post (Q : Local.Store S 35 → Prop)
    (post : ∀ (n : ℕ) (block : BitString) (s : Local.Store S 35), block.length = width n →
      (s 13).length = n → (s 22).length = n → s 17 = block.map bitSymbol → Q (phase.eval s))
    (restored : ∀ s, Q s → Q ((restoreIndex (O := O) unitSymbol).eval s))
    (n count inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (number : (bits.length-m.randomHead)/width n = count) :
    ∃ t ≤ loopBudget width cap time n count, ∃ result,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t result ∧
      selected decode result = scan (width n) (f n) count (bits.drop m.randomHead) ∧
      Finished n (cap n) result ∧ (match result with
        | .exhausted => True
        | .done finish => Q finish.store) ∧ (match result with
        | .exhausted => True
        | .done finish => finish.indexHead = m.indexHead) := by
  induction count generalizing m with
  | zero =>
    have short : bits.length-m.randomHead < width n := by
      by_contra notShort
      have enough : width n ≤ bits.length-m.randomHead := by omega
      have equation := Nat.div_eq_sub_div (width.positive n) enough
      have impossible := number.symm.trans equation
      exact Nat.noConfusion impossible
    obtain ⟨ticks, cost, run⟩ := attempt_short_at_index unitSymbol bitSymbol width phase n (cap n) inputIndex bits m state within short
    refine ⟨1+ticks, ?_, .exhausted, ?_, rfl, trivial, trivial, trivial⟩
    · unfold loopBudget
      omega
    · apply Command.Runs.loop_absent m 32 (fun observed => observed.1.isNone)
        (attempt unitSymbol bitSymbol width phase) ticks
      · simp [observe, waiting]
      · exact run
  | succ count ih =>
    have enough : width n ≤ bits.length-m.randomHead := by
      by_contra short
      have zero := Nat.div_eq_of_lt (show bits.length-m.randomHead < width n by omega)
      omega
    obtain ⟨ticks, cost, next, run, nextState, nextOrigin, nextHead, nextPost, flag, payload⟩ :=
      attempt_full_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame Q post restored
        n inputIndex bits m state within indexBudget widthBudget enough
    have remaining : (bits.length-next.randomHead)/width n = count := by
      rw [nextHead, Nat.sub_add_eq]
      have equation := Nat.div_eq_sub_div (width.positive n) enough
      omega
    have dropped : bits.drop next.randomHead = (bits.drop m.randomHead).drop (width n) := by
      simp only [nextHead, List.drop_drop, Nat.add_comm]
    cases output : f n ((bits.drop m.randomHead).take (width n)) with
    | none =>
      have nextWaiting : next.store 32 = [] := by simpa [output, flagWord] using flag
      obtain ⟨restTicks, restCost, result, restRun, answer, finished, resultPost, origin⟩ := ih next nextState nextWaiting remaining
      refine ⟨1+ticks+1+restTicks, ?_, result, ?_, ?_, finished, resultPost, ?_⟩
      · unfold loopBudget at *
        nlinarith
      · exact Command.Runs.loop m next 32 (fun observed => observed.1.isNone) _ ticks restTicks result
          (by simp [observe, waiting]) run restRun
      · simpa only [scan, output, Option.none_or, dropped] using answer
      · cases result with
        | exhausted => trivial
        | done finish => exact origin.trans nextOrigin
    | some word =>
      have nextFlag : next.store 32 = [unitSymbol] := by simpa [output, flagWord] using flag
      have stop : (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits next 0 (.done next) :=
        Command.Runs.loop_stop next 32 _ _ (by simp [observe, nextFlag])
      refine ⟨1+ticks+1+0, ?_, .done next, ?_, ?_, ⟨nextState, ?_⟩, nextPost, nextOrigin⟩
      · unfold loopBudget
        nlinarith
      · exact Command.Runs.loop m next 32 (fun observed => observed.1.isNone) _ ticks 0 _
          (by simp [observe, waiting]) run stop
      · simp only [selected, scan, output, Option.some_or]
        exact congrArg some (payload word output)
      · simp [nextFlag]

include correct bounded frame in
theorem loop_runs_at_index_preserves_head (n count inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (number : (bits.length-m.randomHead)/width n = count) :
    ∃ t ≤ loopBudget width cap time n count, ∃ result,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t result ∧
      selected decode result = scan (width n) (f n) count (bits.drop m.randomHead) ∧
      Finished n (cap n) result ∧ (match result with
        | .exhausted => True
        | .done finish => finish.indexHead = m.indexHead) := by
  obtain ⟨ticks, cost, result, run, value, finished, _, origin⟩ :=
    loop_runs_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame
      (fun _ => True) (by intros; trivial) (by intros; trivial) n count inputIndex bits m state waiting within indexBudget widthBudget number
  exact ⟨ticks, cost, result, run, value, finished, origin⟩

include correct bounded frame in
theorem loop_runs_at_index (n count inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (number : (bits.length-m.randomHead)/width n = count) :
    ∃ t ≤ loopBudget width cap time n count, ∃ result,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t result ∧
      selected decode result = scan (width n) (f n) count (bits.drop m.randomHead) ∧
      Finished n (cap n) result := by
  obtain ⟨ticks, cost, result, run, value, finished, origin⟩ :=
    loop_runs_at_index_preserves_head unitSymbol bitSymbol width cap time phase decode f correct bounded frame
      n count inputIndex bits m state waiting within indexBudget widthBudget number
  exact ⟨ticks, cost, result, run, value, finished⟩

include correct bounded frame in
theorem loop_runs (n count : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (number : (bits.length-m.randomHead)/width n = count) :
    ∃ t ≤ loopBudget width cap time n count, ∃ result,
      (retryLoop unitSymbol bitSymbol width phase).Runs n bits m t result ∧
      selected decode result = scan (width n) (f n) count (bits.drop m.randomHead) ∧
      Finished n (cap n) result :=
  loop_runs_at_index unitSymbol bitSymbol width cap time phase decode f correct bounded frame
    n count n bits m state waiting le_rfl indexBudget widthBudget number

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
