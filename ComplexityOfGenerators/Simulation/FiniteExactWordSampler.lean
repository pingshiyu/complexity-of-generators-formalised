import ComplexityOfGenerators.Foundations.RankedExecution
import ComplexityOfGenerators.Generators
import Mathlib.Data.Fintype.EquivFin

/-! An exact-word sampler over an arbitrary nonempty finite alphabet.
Each letter is selected by a bounded chain of coin flips in finite control;
the last alphabet symbol is chosen on either branch of the last flip. -/

namespace ComplexityOfGenerators.Simulation.FiniteExactWordSampler

noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Phase (α : Type) [Fintype α]
  | test | halt
  | choose (position : Fin (Fintype.card α))
  | emit (letter : α)
  deriving Fintype

variable (α : Type) [Fintype α] [Nonempty α]

abbrev code := Fintype.equivFin (Phase α)

def sampler : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (Phase α)
  symbols := 0
  initial := code α .test
  transition := fun q _ _ index _ =>
    match (code α).symm q with
    | .test => if index.isSome then
        .readRandom (code α (.choose ⟨0, Fintype.card_pos⟩))
          (code α (.choose ⟨0, Fintype.card_pos⟩))
      else .accept
    | .halt => .accept
    | .choose position =>
        let letter := (Fintype.equivFin α).symm position
        .readRandom (code α (.emit letter))
          (code α (if next : position.val + 1 < Fintype.card α then
            .choose ⟨position.val + 1, next⟩ else .emit letter))
    | .emit letter =>
        .step (code α .test) none .stay .stay .stay .right (some letter)

def Invariant (n : ℕ) (c : Configuration (sampler α)) : Prop :=
  c.output.length = c.indexHead ∧ c.indexHead ≤ n ∧
    match (code α).symm c.state with
    | .test => True
    | .halt => False
    | .choose _ | .emit _ => c.indexHead < n

def rank (n : ℕ) (c : Configuration (sampler α)) : ℕ :=
  let block := Fintype.card α + 2
  match (code α).symm c.state with
  | .test => block * (n - c.indexHead)
  | .halt => 0
  | .choose position => block * (n - c.indexHead - 1) + (Fintype.card α - position.val) + 1
  | .emit _ => block * (n - c.indexHead - 1) + 1

def Post (n : ℕ) : Outcome α → Prop
  | .accepted word => word.length = n
  | .rejected => False
  | .exhausted => True

theorem terminal (n : ℕ) (bits : BitString)
    (c : Configuration (sampler α)) (result : Outcome α)
    (valid : Invariant α n c)
    (terminal : (sampler α).observe (generatorData n) bits c = .halted result) :
    Post α n result := by
  rcases valid with ⟨length, bound, live⟩
  cases result <;> cases phase : (code α).symm c.state <;>
    simp_all [Machine.observe, sampler, generatorData, Post]
  all_goals split_ifs at terminal <;> simp_all <;> omega

theorem decreases (n : ℕ) (bits : BitString)
    (c d : Configuration (sampler α))
    (valid : Invariant α n c)
    (observed : (sampler α).observe (generatorData n) bits c = .running c)
    (next : (sampler α).next (generatorData n) bits c = .running d) :
    Invariant α n d ∧ rank α n d < rank α n c := by
  rcases valid with ⟨length, bound, live⟩
  have split (inside : c.indexHead < n) :
      (Fintype.card α + 2) * (n - c.indexHead) =
        (Fintype.card α + 2) * (n - c.indexHead - 1) + (Fintype.card α + 2) := by
    calc
      _ = (Fintype.card α + 2) * ((n - c.indexHead - 1) + 1) := by congr 1; omega
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  cases phase : (code α).symm c.state with
  | halt => simp [Machine.observe, sampler, phase] at observed
  | test =>
      have inside : c.indexHead < n := by
        by_contra outside
        simp [Machine.observe, sampler, phase, generatorData, outside] at observed
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next, sampler, phase, generatorData, inside, lookup] at next
      | some flag =>
          simp only [Machine.next, sampler, phase, generatorData, inside,
            ↓reduceIte, Option.isSome_some, lookup, RunState.running.injEq] at next
          subst d
          cases flag <;>
            simp [Invariant, rank, phase, length, bound,
              inside, split inside, Nat.add_assoc]
  | choose position =>
      have inside : c.indexHead < n := by simpa [phase] using live
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next, sampler, phase, lookup] at next
      | some flag =>
          simp only [Machine.next, sampler, phase, lookup, RunState.running.injEq] at next
          subst d
          cases flag
          · simp [Invariant, rank, phase, length, bound, inside]
            omega
          · by_cases more : position.val + 1 < Fintype.card α
            · simp [Invariant, rank, phase, length, bound, inside, more]
              omega
            · simp [Invariant, rank, phase, length, bound, inside, more]
              omega
  | emit letter =>
      have inside : c.indexHead < n := by simpa [phase] using live
      simp only [Machine.next, sampler, phase, RunState.running.injEq] at next
      subst d
      have plus : min (c.indexHead + 1) n = c.indexHead + 1 := Nat.min_eq_left (by omega)
      have minus : n - (c.indexHead + 1) = n - c.indexHead - 1 := by omega
      simp [Invariant, rank, phase,
        Move.onInput, generatorData, length, plus, minus]
      omega

theorem sampler_run (n : ℕ) (bits : BitString) :
    ∃ result, (sampler α).run (generatorData n) bits ((Fintype.card α + 2) * n) = .halted result ∧
      (match result with
        | .accepted word => word.length = n
        | .rejected => False
        | .exhausted => True) := by
  have result := (sampler α).runFrom_of_rank (generatorData n) bits
    (Invariant α n) (rank α n)
    (Post α n)
    (terminal α n bits) (decreases α n bits)
    (sampler α).initialConfiguration
    (by simp [Invariant, Machine.initialConfiguration, sampler])
  rw [Machine.runFrom_initial] at result
  simpa [rank, Post, Machine.initialConfiguration, sampler] using result

theorem sampler_timeBound (n : ℕ) :
    (sampler α).TimeBound (generatorData n) ((Fintype.card α + 2) * n) := by
  intro bits
  obtain ⟨result, halted, _⟩ := sampler_run α n bits
  exact ⟨result, halted⟩

def choice (c : Configuration (sampler α))
    (letter : α) (consumed : ℕ) : Configuration (sampler α) :=
  {c with state := code α (.emit letter), randomHead := c.randomHead + consumed}

theorem choose (n : ℕ) (bits tail : BitString)
    (steps : ℕ) (position target : Fin (Fintype.card α))
    (distance : position.val + steps = target.val)
    (c : Configuration (sampler α))
    (state : c.state = code α (.choose position))
    (choices : bits.drop c.randomHead = List.replicate steps true ++ false :: tail) :
    (sampler α).runFrom (generatorData n) bits c (steps + 1) =
      (sampler α).observe (generatorData n) bits
        (choice α c ((Fintype.equivFin α).symm target) (steps + 1)) := by
  induction steps generalizing c position with
  | zero =>
      have equal : position = target := Fin.ext (by omega)
      subst position
      have first : bits[c.randomHead]? = some false := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [List.getElem?_drop] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      have value : bits[c.randomHead] = false := List.getElem?_eq_some_iff.mp first |>.2
      simp [Machine.runFrom, Machine.observe, Machine.next, sampler,
        state, available, value, choice]
  | succ steps ih =>
      have more : position.val + 1 < Fintype.card α := by omega
      have first : bits[c.randomHead]? = some true := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [List.getElem?_drop, List.replicate_succ] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      let d : Configuration (sampler α) :=
        {c with
          state := code α (.choose ⟨position.val + 1, more⟩)
          randomHead := c.randomHead + 1}
      have observed : (sampler α).observe (generatorData n) bits c = .running c := by
        simp [Machine.observe, sampler, state, available]
      have next : (sampler α).next (generatorData n) bits c = .running d := by
        simp [Machine.next, sampler, state, first, more, d]
      have rest : bits.drop d.randomHead = List.replicate steps true ++ false :: tail := by
        change bits.drop (c.randomHead + 1) = _
        rw [← List.drop_drop, choices]
        simp [List.replicate_succ]
      have resumed := ih ⟨position.val + 1, more⟩
        (by change (position.val + 1) + steps = target.val; omega) d rfl rest
      have shifted := (sampler α).runFrom_shift (generatorData n) bits c d observed next (steps + 1)
      rw [resumed] at shifted
      simpa [d, choice, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shifted

def seed : List α → BitString
  | [] => [false]
  | letter :: word => true :: (List.replicate ((Fintype.equivFin α) letter).val true ++ false :: seed word)

theorem generates_word (n : ℕ) (bits : BitString) (word : List α)
    (c : Configuration (sampler α))
    (state : c.state = code α .test)
    (bound : c.indexHead + word.length = n)
    (choices : bits.drop c.randomHead = seed α word) :
    ∃ ticks, (sampler α).runFrom (generatorData n) bits c ticks =
      .halted (.accepted (c.output ++ word)) := by
  induction word generalizing c with
  | nil =>
      have last : c.indexHead=n := by simpa using bound
      exact ⟨0,by simp [Machine.runFrom,Machine.observe,sampler,state,generatorData,last]⟩
  | cons letter word ih =>
      have inside : c.indexHead < n := by simp only [List.length_cons] at bound; omega
      let position := (Fintype.equivFin α) letter
      have first : bits[c.randomHead]? = some true := by
        have eq := congrArg (fun w : BitString => w[0]?) choices
        simpa [seed, List.getElem?_drop] using eq
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp first |>.1
      let choosing : Configuration (sampler α) :=
        {c with state := code α (.choose ⟨0, Fintype.card_pos⟩), randomHead := c.randomHead + 1}
      have observed : (sampler α).observe (generatorData n) bits c = .running c := by
        simp [Machine.observe, sampler, state, generatorData, inside, available]
      have next : (sampler α).next (generatorData n) bits c = .running choosing := by
        simp [Machine.next, sampler, state, generatorData, inside, first, choosing]
      have decoderChoices : bits.drop choosing.randomHead = List.replicate position.val true ++ false :: seed α word := by
        change bits.drop (c.randomHead + 1) = _
        rw [← List.drop_drop, choices]
        rfl
      have decoded := choose α n bits (seed α word) position.val
        ⟨0, Fintype.card_pos⟩ position (by simp) choosing rfl decoderChoices
      let emitting := choice α choosing letter (position.val + 1)
      have letterEq : (Fintype.equivFin α).symm position = letter := Equiv.symm_apply_apply _ _
      rw [letterEq] at decoded
      let d := (sampler α).stepConfiguration (generatorData n) emitting
        (code α .test) none .stay .stay .stay .right (some letter)
      have emitRun : (sampler α).runFrom (generatorData n) bits emitting 1 =
          (sampler α).observe (generatorData n) bits d := by
        simp [Machine.runFrom, Machine.observe, Machine.next, sampler,
          emitting, choice, d, Machine.stepConfiguration]
      have ds : d.state = code α .test := rfl
      have db : d.indexHead + word.length = n := by
        simp [d, Machine.stepConfiguration, emitting, choice, choosing,
          Move.onInput, generatorData, Nat.min_eq_left (show c.indexHead + 1 ≤ n by omega)]
        simp only [List.length_cons] at bound
        omega
      have dc : bits.drop d.randomHead = seed α word := by
        change bits.drop (c.randomHead + 1 + (position.val + 1)) = _
        rw [show c.randomHead + 1 + (position.val + 1) = (c.randomHead + 1) + (position.val + 1) by omega,
          ← List.drop_drop, decoderChoices]
        simp [List.drop_append]
      obtain ⟨ticks, execution⟩ := ih d ds db dc
      have afterEmit := (sampler α).runFrom_add _ _ emitting d 1 emitRun ticks
      rw [execution] at afterEmit
      have afterChoice := (sampler α).runFrom_add _ _ choosing emitting (position.val + 1) decoded (1 + ticks)
      rw [afterEmit] at afterChoice
      have all := (sampler α).runFrom_shift _ _ c choosing observed next ((position.val + 1) + (1 + ticks))
      rw [afterChoice] at all
      refine ⟨position.val + 1 + (1 + ticks) + 1, ?_⟩
      simpa [d, Machine.stepConfiguration, emitting, choice, choosing, List.append_assoc] using all

theorem sampler_language (n : ℕ) :
    (sampler α).generatedLanguage (generatorData n) = {word | word.length = n} := by
  ext word
  constructor
  · rintro ⟨bits, _, ticks, accepted⟩
    obtain ⟨result, execution, related⟩ := sampler_run α n bits
    have same := (sampler α).halted_outcome_unique _ bits ticks _ _ _ accepted execution
    subst result
    exact related
  · intro bound
    obtain ⟨ticks, accepted⟩ := generates_word α n (seed α word) word
      (sampler α).initialConfiguration rfl
      (by simpa [Machine.initialConfiguration] using bound) (by simp [Machine.initialConfiguration])
    rw [Machine.runFrom_initial] at accepted
    refine ⟨seed α word, ?_, ticks, ?_⟩
    · cases word <;> simp [seed]
    · simpa [Machine.initialConfiguration] using accepted

end
end ComplexityOfGenerators.Simulation.FiniteExactWordSampler
