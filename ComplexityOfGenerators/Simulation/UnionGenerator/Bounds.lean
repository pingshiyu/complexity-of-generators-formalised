import ComplexityOfGenerators.Simulation.UnionGenerator.Views

namespace ComplexityOfGenerators.Simulation.UnionGenerator

open WordStack

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

theorem flag_bound (reg : Fin 35) (b : Bool) (s : Store G H) (cap : ℕ)
    (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((flag G H reg b).eval s) cap ∧ (flag G H reg b).cost s ≤ 3 * cap + 2 := by
  constructor
  · rw [flag_eval]
    apply sizes.update
    cases b <;> simp_all [flagWord]
  · have size := sizes reg
    cases b <;> simp [flag, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.skip,
      WordStack.Routine.ofLocal, Local.push, Local.ticks] <;> omega

theorem takeOutput_bound (dst : Fin 35) (different : (10 : Fin 35) ≠ dst)
    (f : Cell G H → Cell G H) (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((takeOutput G H dst different f).eval s) cap ∧
      (takeOutput G H dst different f).cost s ≤ 9 * cap + 1 := by
  constructor
  · rw [takeOutput_eval]
    exact (sizes.clear 10).update dst _ (by simpa using sizes 10)
  · have source := sizes 10
    have target := sizes dst
    simp only [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.transfer,
      Function.update_of_ne different]
    omega

theorem leftFinish_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap)
    (positive : 1 ≤ cap) :
    StoreBound ((leftFinish G H).eval s) cap ∧ (leftFinish G H).cost s ≤ 13 * cap + 5 := by
  unfold leftFinish
  simp only [WordStack.Routine.branch]
  split
  · obtain ⟨taken, takenCost⟩ := takeOutput_bound G H 25 (by decide) (leftOutput G H) s cap sizes
    obtain ⟨flagged, flagCost⟩ := flag_bound G H 27 true _ cap taken positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq]; omega⟩
  · obtain ⟨flagged, flagCost⟩ := flag_bound G H 27 false _ cap (sizes.clear 25) positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq, WordStack.Routine.clear]; have := sizes 25; omega⟩

theorem rightFinish_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap)
    (positive : 1 ≤ cap) :
    StoreBound ((rightFinish G H).eval s) cap ∧ (rightFinish G H).cost s ≤ 13 * cap + 5 := by
  unfold rightFinish
  simp only [WordStack.Routine.branch]
  split
  · obtain ⟨taken, takenCost⟩ := takeOutput_bound G H 26 (by decide) (rightOutput G H) s cap sizes
    obtain ⟨flagged, flagCost⟩ := flag_bound G H 28 true _ cap taken positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq]; omega⟩
  · obtain ⟨flagged, flagCost⟩ := flag_bound G H 28 false _ cap (sizes.clear 26) positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq, WordStack.Routine.clear]; have := sizes 26; omega⟩

theorem leftFinish_output_length (s : Store G H) :
    ((leftFinish G H).eval s 25).length ≤ (s 10).length := by
  simp only [leftFinish, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, takeOutput_eval, flag_eval, WordStack.Routine.clear]

theorem rightFinish_output_length (s : Store G H) :
    ((rightFinish G H).eval s 26).length ≤ (s 10).length := by
  simp only [rightFinish, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, takeOutput_eval, flag_eval, WordStack.Routine.clear]

theorem chooseFrom_bound (first second firstFlag secondFlag : Fin 35)
    (firstDifferent : first ≠ 11 ∧ first ≠ 33) (secondDifferent : second ≠ 11 ∧ second ≠ 33)
    (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((chooseFrom G H first second firstFlag secondFlag firstDifferent secondDifferent).eval s) cap ∧
      (chooseFrom G H first second firstFlag secondFlag firstDifferent secondDifferent).cost s ≤ 24 * cap + 10 := by
  have success (source : Fin 35) (different : source ≠ 11 ∧ source ≠ 33) :
      StoreBound (((WordStack.Routine.assign source 11 33 different.1 different.2 (by decide) id).seq
        (flag G H 29 true)).eval s) cap ∧
      ((WordStack.Routine.assign source 11 33 different.1 different.2 (by decide) id).seq
        (flag G H 29 true)).cost s ≤ 23 * cap + 6 := by
    have assigned := sizes.assign (O := α) source 11 33 different.1 different.2 (by decide) id
    obtain ⟨flagged, flagCost⟩ := flag_bound G H 29 true _ cap assigned positive
    refine ⟨flagged, ?_⟩
    have h₀ := sizes 11
    have h₁ := sizes 33
    have h₂ := sizes source
    simp only [WordStack.Routine.seq, WordStack.Routine.assign_cost]
    omega
  unfold chooseFrom
  simp only [WordStack.Routine.branch]
  split
  · obtain ⟨bounded, cost⟩ := success first firstDifferent
    exact ⟨bounded, by omega⟩
  · simp only [WordStack.Routine.branch]
    split
    · obtain ⟨bounded, cost⟩ := success second secondDifferent
      exact ⟨bounded, by omega⟩
    · obtain ⟨flagged, flagCost⟩ := flag_bound G H 29 false _ cap (sizes.clear 11) positive
      exact ⟨flagged, by simp only [WordStack.Routine.seq, WordStack.Routine.clear]; have := sizes 11; omega⟩

theorem choose_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((choose G H).eval s) cap ∧ (choose G H).cost s ≤ 24 * cap + 11 := by
  unfold choose
  simp only [WordStack.Routine.branch]
  split
  · obtain ⟨bounded, cost⟩ := chooseFrom_bound G H 26 25 28 27 (by decide) (by decide) s cap sizes positive
    exact ⟨bounded, by omega⟩
  · obtain ⟨bounded, cost⟩ := chooseFrom_bound G H 25 26 27 28 (by decide) (by decide) s cap sizes positive
    exact ⟨bounded, by omega⟩

noncomputable def bodyBudget (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n cap : ℕ) : ℕ :=
  ((Source.body G (Symbol.left : Source.Symbol G → Cell G H) (leftDecode G H)
      (Source.bank BoundedSource.sourceSlots)).bound +
    (Source.body H (Symbol.right : Source.Symbol H → Cell G H) (rightDecode G H)
      (Source.bank BoundedSource.sourceSlots)).bound + 500) * (cap + 1) +
    Command.counterBudget leftSeed n + Command.counterBudget leftTime n +
    Command.counterBudget rightSeed n + Command.counterBudget rightTime n

theorem body_bound (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n read cap : ℕ) (bits : BitString)
    (sizes : StoreBound (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store cap)
    (index : n + 1 ≤ cap)
    (leftSeedBound : leftSeed n ≤ cap) (leftTimeBound : leftTime n + 1 ≤ cap)
    (rightSeedBound : rightSeed n ≤ cap) (rightTimeBound : rightTime n + 1 ≤ cap)
    (leftSpace : 1 + n + leftSeed n + 3 * (leftTime n + 1) ≤ cap)
    (rightSpace : 1 + n + rightSeed n + 3 * (rightTime n + 1) ≤ cap) :
    StoreBound ((body G H leftSeed leftTime rightSeed rightTime).eval
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store) cap ∧
    (body G H leftSeed leftTime rightSeed rightTime).cost
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store ≤
      bodyBudget G H leftSeed leftTime rightSeed rightTime n cap := by
  let s := (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store
  have initial : Stored G H n bits none none s := by
    constructor <;> simp [s, BoundedSource.preparedMemory, held, flagWord]
  obtain ⟨leftBound, _, leftCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit G Symbol.left (leftDecode G H)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (leftBit G H) (fun _ => rfl)
      leftSeed leftTime s (generatorData n) bits
      (by simp [initial.input, generatorData]) (by simp [initial.auxiliary, generatorData])
      initial.index initial.random initial.empty cap sizes index leftSeedBound leftTimeBound
      (by simpa [generatorData] using leftSpace)
  obtain ⟨leftFinished, leftFinishCost⟩ := leftFinish_bound G H _ cap leftBound (by omega)
  have storedLeft := leftStep_stored G H leftSeed leftTime n bits none none s initial
  obtain ⟨rightBound, _, rightCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit H Symbol.right (rightDecode G H)
      (fun _ => rfl) (fun _ => .right .unit) (fun _ => .right .unit) (rightBit G H) (fun _ => rfl)
      rightSeed rightTime _ (generatorData n) (bits.drop (leftSeed n))
      (by simp [storedLeft.input, generatorData]) (by simp [storedLeft.auxiliary, generatorData])
      storedLeft.index storedLeft.random storedLeft.empty cap leftFinished index rightSeedBound rightTimeBound
      (by simpa [generatorData] using rightSpace)
  obtain ⟨rightFinished, rightFinishCost⟩ := rightFinish_bound G H _ cap rightBound (by omega)
  obtain ⟨chosen, chooseCost⟩ := choose_bound G H _ cap rightFinished (by omega)
  refine ⟨chosen, ?_⟩
  change (leftTrial G H leftSeed leftTime).cost s + 1 +
    ((leftFinish G H).cost _ + 1 + ((rightTrial G H rightSeed rightTime).cost _ + 1 +
    ((rightFinish G H).cost _ + 1 + (choose G H).cost _))) ≤ _
  change (leftTrial G H leftSeed leftTime).cost s ≤ _ at leftCost
  change (rightTrial G H rightSeed rightTime).cost _ ≤ _ at rightCost
  simp only [generatorData] at leftCost rightCost
  dsimp only [bodyBudget]
  simp only [s, leftTrial, rightTrial] at leftCost rightCost leftFinishCost rightFinishCost chooseCost ⊢
  nlinarith only [leftCost, rightCost, leftFinishCost, rightFinishCost, chooseCost]

end ComplexityOfGenerators.Simulation.UnionGenerator
