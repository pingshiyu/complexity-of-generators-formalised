import ComplexityOfGenerators.Foundations.RankedExecution
import ComplexityOfGenerators.Generators
import Mathlib.Data.Fintype.EquivFin

/-! A cumulative-word sampler over an arbitrary nonempty finite alphabet.
Each letter is selected by a bounded chain of coin flips in finite control;
the last alphabet symbol is chosen on either branch of the last flip. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive FiniteWordSamplerPhase (α : Type) [Fintype α]
  | test | halt
  | choose (position : Fin (Fintype.card α))
  | emit (letter : α)
  deriving Fintype

variable (α : Type) [Fintype α] [Nonempty α]

abbrev finiteWordSamplerCode := Fintype.equivFin (FiniteWordSamplerPhase α)

def finiteUpToWordSampler : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (FiniteWordSamplerPhase α)
  symbols := 0
  initial := finiteWordSamplerCode α .test
  transition := fun q _ _ index _ =>
    match (finiteWordSamplerCode α).symm q with
    | .test => if index.isSome then
        .readRandom (finiteWordSamplerCode α .halt)
          (finiteWordSamplerCode α (.choose ⟨0, Fintype.card_pos⟩))
      else .accept
    | .halt => .accept
    | .choose position =>
        let letter := (Fintype.equivFin α).symm position
        .readRandom (finiteWordSamplerCode α (.emit letter))
          (finiteWordSamplerCode α (if next : position.val + 1 < Fintype.card α then
            .choose ⟨position.val + 1, next⟩ else .emit letter))
    | .emit letter =>
        .step (finiteWordSamplerCode α .test) none .stay .stay .stay .right (some letter)

def finiteWordSamplerInvariant (n : ℕ) (c : Configuration (finiteUpToWordSampler α)) : Prop :=
  c.output.length = c.indexHead ∧ c.indexHead ≤ n ∧
    match (finiteWordSamplerCode α).symm c.state with
    | .test | .halt => True
    | .choose _ | .emit _ => c.indexHead < n

def finiteWordSamplerRank (n : ℕ) (c : Configuration (finiteUpToWordSampler α)) : ℕ :=
  let block := Fintype.card α + 2
  match (finiteWordSamplerCode α).symm c.state with
  | .test => block * (n - c.indexHead)
  | .halt => 0
  | .choose position => block * (n - c.indexHead - 1) + (Fintype.card α - position.val) + 1
  | .emit _ => block * (n - c.indexHead - 1) + 1

def finiteWordSamplerPost (n : ℕ) : Outcome α → Prop
  | .accepted word => word.length ≤ n
  | .rejected => False
  | .exhausted => True

theorem finiteWordSampler_terminal (n : ℕ) (bits : BitString)
    (c : Configuration (finiteUpToWordSampler α)) (result : Outcome α)
    (valid : finiteWordSamplerInvariant α n c)
    (terminal : (finiteUpToWordSampler α).observe (generatorData n) bits c = .halted result) :
    finiteWordSamplerPost α n result := by
  rcases valid with ⟨length, bound, live⟩
  cases result <;> cases phase : (finiteWordSamplerCode α).symm c.state <;>
    simp_all [Machine.observe, finiteUpToWordSampler, generatorData, finiteWordSamplerPost]
  all_goals split_ifs at terminal <;> simp_all

theorem finiteWordSampler_decreases (n : ℕ) (bits : BitString)
    (c d : Configuration (finiteUpToWordSampler α))
    (valid : finiteWordSamplerInvariant α n c)
    (observed : (finiteUpToWordSampler α).observe (generatorData n) bits c = .running c)
    (next : (finiteUpToWordSampler α).next (generatorData n) bits c = .running d) :
    finiteWordSamplerInvariant α n d ∧ finiteWordSamplerRank α n d < finiteWordSamplerRank α n c := by
  rcases valid with ⟨length, bound, live⟩
  have split (inside : c.indexHead < n) :
      (Fintype.card α + 2) * (n - c.indexHead) =
        (Fintype.card α + 2) * (n - c.indexHead - 1) + (Fintype.card α + 2) := by
    calc
      _ = (Fintype.card α + 2) * ((n - c.indexHead - 1) + 1) := by congr 1; omega
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  cases phase : (finiteWordSamplerCode α).symm c.state with
  | halt => simp [Machine.observe, finiteUpToWordSampler, phase] at observed
  | test =>
      have inside : c.indexHead < n := by
        by_contra outside
        simp [Machine.observe, finiteUpToWordSampler, phase, generatorData, outside] at observed
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next, finiteUpToWordSampler, phase, generatorData, inside, lookup] at next
      | some flag =>
          simp only [Machine.next, finiteUpToWordSampler, phase, generatorData, inside,
            ↓reduceIte, Option.isSome_some, lookup, RunState.running.injEq] at next
          subst d
          cases flag <;>
            simp [finiteWordSamplerInvariant, finiteWordSamplerRank, phase, length, bound,
              inside, split inside, Nat.add_assoc]
  | choose position =>
      have inside : c.indexHead < n := by simpa [phase] using live
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next, finiteUpToWordSampler, phase, lookup] at next
      | some flag =>
          simp only [Machine.next, finiteUpToWordSampler, phase, lookup, RunState.running.injEq] at next
          subst d
          cases flag
          · simp [finiteWordSamplerInvariant, finiteWordSamplerRank, phase, length, bound, inside]
            omega
          · by_cases more : position.val + 1 < Fintype.card α
            · simp [finiteWordSamplerInvariant, finiteWordSamplerRank, phase, length, bound, inside, more]
              omega
            · simp [finiteWordSamplerInvariant, finiteWordSamplerRank, phase, length, bound, inside, more]
              omega
  | emit letter =>
      have inside : c.indexHead < n := by simpa [phase] using live
      simp only [Machine.next, finiteUpToWordSampler, phase, RunState.running.injEq] at next
      subst d
      have plus : min (c.indexHead + 1) n = c.indexHead + 1 := Nat.min_eq_left (by omega)
      have minus : n - (c.indexHead + 1) = n - c.indexHead - 1 := by omega
      simp [finiteWordSamplerInvariant, finiteWordSamplerRank, phase,
        Move.onInput, generatorData, length, plus, minus]
      omega

theorem finiteUpToWordSampler_run (n : ℕ) (bits : BitString) :
    ∃ result, (finiteUpToWordSampler α).run (generatorData n) bits ((Fintype.card α + 2) * n) = .halted result ∧
      (match result with
        | .accepted word => word.length ≤ n
        | .rejected => False
        | .exhausted => True) := by
  have result := (finiteUpToWordSampler α).runFrom_of_rank (generatorData n) bits
    (finiteWordSamplerInvariant α n) (finiteWordSamplerRank α n)
    (finiteWordSamplerPost α n)
    (finiteWordSampler_terminal α n bits) (finiteWordSampler_decreases α n bits)
    (finiteUpToWordSampler α).initialConfiguration
    (by simp [finiteWordSamplerInvariant, Machine.initialConfiguration, finiteUpToWordSampler])
  rw [Machine.runFrom_initial] at result
  simpa [finiteWordSamplerRank, finiteWordSamplerPost, Machine.initialConfiguration, finiteUpToWordSampler] using result

theorem finiteUpToWordSampler_timeBound (n : ℕ) :
    (finiteUpToWordSampler α).TimeBound (generatorData n) ((Fintype.card α + 2) * n) := by
  intro bits
  obtain ⟨result, halted, _⟩ := finiteUpToWordSampler_run α n bits
  exact ⟨result, halted⟩

def finiteWordSamplerChoice (c : Configuration (finiteUpToWordSampler α))
    (letter : α) (consumed : ℕ) : Configuration (finiteUpToWordSampler α) :=
  {c with state := finiteWordSamplerCode α (.emit letter), randomHead := c.randomHead + consumed}

theorem finiteWordSampler_choose (n : ℕ) (bits tail : BitString)
    (steps : ℕ) (position target : Fin (Fintype.card α))
    (distance : position.val + steps = target.val)
    (c : Configuration (finiteUpToWordSampler α))
    (state : c.state = finiteWordSamplerCode α (.choose position))
    (choices : bits.drop c.randomHead = List.replicate steps true ++ false :: tail) :
    (finiteUpToWordSampler α).runFrom (generatorData n) bits c (steps + 1) =
      (finiteUpToWordSampler α).observe (generatorData n) bits
        (finiteWordSamplerChoice α c ((Fintype.equivFin α).symm target) (steps + 1)) := by
  induction steps generalizing c position with
  | zero =>
      have equal : position = target := Fin.ext (by omega)
      subst position
      have first : bits[c.randomHead]? = some false := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [List.getElem?_drop] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      have value : bits[c.randomHead] = false := List.getElem?_eq_some_iff.mp first |>.2
      simp [Machine.runFrom, Machine.observe, Machine.next, finiteUpToWordSampler,
        state, available, value, finiteWordSamplerChoice]
  | succ steps ih =>
      have more : position.val + 1 < Fintype.card α := by omega
      have first : bits[c.randomHead]? = some true := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [List.getElem?_drop, List.replicate_succ] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      let d : Configuration (finiteUpToWordSampler α) :=
        {c with
          state := finiteWordSamplerCode α (.choose ⟨position.val + 1, more⟩)
          randomHead := c.randomHead + 1}
      have observed : (finiteUpToWordSampler α).observe (generatorData n) bits c = .running c := by
        simp [Machine.observe, finiteUpToWordSampler, state, available]
      have next : (finiteUpToWordSampler α).next (generatorData n) bits c = .running d := by
        simp [Machine.next, finiteUpToWordSampler, state, first, more, d]
      have rest : bits.drop d.randomHead = List.replicate steps true ++ false :: tail := by
        change bits.drop (c.randomHead + 1) = _
        rw [← List.drop_drop, choices]
        simp [List.replicate_succ]
      have resumed := ih ⟨position.val + 1, more⟩
        (by change (position.val + 1) + steps = target.val; omega) d rfl rest
      have shifted := (finiteUpToWordSampler α).runFrom_shift (generatorData n) bits c d observed next (steps + 1)
      rw [resumed] at shifted
      simpa [d, finiteWordSamplerChoice, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shifted

def finiteWordSeed : List α → BitString
  | [] => [false]
  | letter :: word => true :: (List.replicate ((Fintype.equivFin α) letter).val true ++ false :: finiteWordSeed word)

theorem finiteWordSampler_word (n : ℕ) (bits : BitString) (word : List α)
    (c : Configuration (finiteUpToWordSampler α))
    (state : c.state = finiteWordSamplerCode α .test)
    (bound : c.indexHead + word.length ≤ n)
    (choices : bits.drop c.randomHead = finiteWordSeed α word) :
    ∃ ticks, (finiteUpToWordSampler α).runFrom (generatorData n) bits c ticks =
      .halted (.accepted (c.output ++ word)) := by
  induction word generalizing c with
  | nil =>
      by_cases inside : c.indexHead < n
      · have first : bits[c.randomHead]? = some false := by
          have eq := congrArg (fun w : BitString => w[0]?) choices
          simpa [finiteWordSeed, List.getElem?_drop] using eq
        have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
        have value : bits[c.randomHead] = false := List.getElem?_eq_some_iff.mp first |>.2
        exact ⟨1, by simp [Machine.runFrom, Machine.observe, Machine.next, finiteUpToWordSampler,
          state, generatorData, inside, available, value]⟩
      · exact ⟨0, by simp [Machine.runFrom, Machine.observe, finiteUpToWordSampler,
          state, generatorData, inside]⟩
  | cons letter word ih =>
      have inside : c.indexHead < n := by simp only [List.length_cons] at bound; omega
      let position := (Fintype.equivFin α) letter
      have first : bits[c.randomHead]? = some true := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [finiteWordSeed, List.getElem?_drop] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      let choosing : Configuration (finiteUpToWordSampler α) :=
        {c with state := finiteWordSamplerCode α (.choose ⟨0, Fintype.card_pos⟩), randomHead := c.randomHead + 1}
      have observed : (finiteUpToWordSampler α).observe (generatorData n) bits c = .running c := by
        simp [Machine.observe, finiteUpToWordSampler, state, generatorData, inside, available]
      have next : (finiteUpToWordSampler α).next (generatorData n) bits c = .running choosing := by
        simp [Machine.next, finiteUpToWordSampler, state, generatorData, inside, first, choosing]
      have decoderChoices : bits.drop choosing.randomHead = List.replicate position.val true ++ false :: finiteWordSeed α word := by
        change bits.drop (c.randomHead + 1) = _
        rw [← List.drop_drop, choices]
        rfl
      have decoded := finiteWordSampler_choose α n bits (finiteWordSeed α word) position.val
        ⟨0, Fintype.card_pos⟩ position (by simp) choosing rfl decoderChoices
      let emitting := finiteWordSamplerChoice α choosing letter (position.val + 1)
      have letterEq : (Fintype.equivFin α).symm position = letter := Equiv.symm_apply_apply _ _
      rw [letterEq] at decoded
      let d := (finiteUpToWordSampler α).stepConfiguration (generatorData n) emitting
        (finiteWordSamplerCode α .test) none .stay .stay .stay .right (some letter)
      have emitRun : (finiteUpToWordSampler α).runFrom (generatorData n) bits emitting 1 =
          (finiteUpToWordSampler α).observe (generatorData n) bits d := by
        simp [Machine.runFrom, Machine.observe, Machine.next, finiteUpToWordSampler,
          emitting, finiteWordSamplerChoice, d, Machine.stepConfiguration]
      have ds : d.state = finiteWordSamplerCode α .test := rfl
      have db : d.indexHead + word.length ≤ n := by
        simp [d, Machine.stepConfiguration, emitting, finiteWordSamplerChoice, choosing,
          Move.onInput, generatorData, Nat.min_eq_left (show c.indexHead + 1 ≤ n by omega)]
        simp only [List.length_cons] at bound
        omega
      have dc : bits.drop d.randomHead = finiteWordSeed α word := by
        change bits.drop (c.randomHead + 1 + (position.val + 1)) = _
        rw [show c.randomHead + 1 + (position.val + 1) = (c.randomHead + 1) + (position.val + 1) by omega,
          ← List.drop_drop, decoderChoices]
        simp [List.drop_append]
      obtain ⟨ticks, execution⟩ := ih d ds db dc
      have afterEmit := (finiteUpToWordSampler α).runFrom_add _ _ emitting d 1 emitRun ticks
      rw [execution] at afterEmit
      have afterChoice := (finiteUpToWordSampler α).runFrom_add _ _ choosing emitting (position.val + 1) decoded (1 + ticks)
      rw [afterEmit] at afterChoice
      have all := (finiteUpToWordSampler α).runFrom_shift _ _ c choosing observed next ((position.val + 1) + (1 + ticks))
      rw [afterChoice] at all
      refine ⟨position.val + 1 + (1 + ticks) + 1, ?_⟩
      simpa [d, Machine.stepConfiguration, emitting, finiteWordSamplerChoice, choosing, List.append_assoc] using all

theorem finiteUpToWordSampler_language (n : ℕ) :
    (finiteUpToWordSampler α).generatedLanguage (generatorData n) = {word | word.length ≤ n} := by
  ext word
  constructor
  · rintro ⟨bits, _, ticks, accepted⟩
    obtain ⟨result, execution, related⟩ := finiteUpToWordSampler_run α n bits
    have same := (finiteUpToWordSampler α).halted_outcome_unique _ bits ticks _ _ _ accepted execution
    subst result
    exact related
  · intro bound
    obtain ⟨ticks, accepted⟩ := finiteWordSampler_word α n (finiteWordSeed α word) word
      (finiteUpToWordSampler α).initialConfiguration rfl
      (by simpa [Machine.initialConfiguration] using bound) (by simp [Machine.initialConfiguration])
    rw [Machine.runFrom_initial] at accepted
    refine ⟨finiteWordSeed α word, ?_, ticks, ?_⟩
    · cases word <;> simp [finiteWordSeed]
    · simpa [Machine.initialConfiguration] using accepted

end
end ComplexityOfGenerators.Simulation
