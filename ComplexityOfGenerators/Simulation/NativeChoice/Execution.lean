import ComplexityOfGenerators.Simulation.NativeChoice.Basic
import ComplexityOfGenerators.Simulation.WorkSteps

namespace ComplexityOfGenerators.Simulation.NativeChoice
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] (family : E → Machine Unit Bool O)

private theorem map_update {A B : Type} (f : A → B) (memory : ℤ → Option A)
    (position : ℤ) (value : Option A) :
    (fun x => (Function.update memory position value x).map f)=
      Function.update (fun x => (memory x).map f) position (value.map f) := by
  funext x
  by_cases same : x=position <;> simp [same]

theorem observe (event : E) (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (family event)) :
    (machine family event).observe data bits (configuration family event c) =
      runState family event ((family event).observe data bits c) := by
  simp only [Machine.observe]
  dsimp only [configuration]
  rw [machine_transition,decode_encode]
  cases table : (family event).transition c.state data.input[c.inputHead]?
      data.auxiliary[c.auxiliaryHead]? (if c.indexHead<data.index then some () else none) (c.work c.workHead) <;>
    simp only [instruction,runState,configuration]
  split_ifs <;> rfl

theorem next (event : E) (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (family event)) :
    (machine family event).next data bits (configuration family event c) =
      runState family event ((family event).next data bits c) := by
  simp only [Machine.next]
  dsimp only [configuration]
  rw [machine_transition,decode_encode]
  cases table : (family event).transition c.state data.input[c.inputHead]?
      data.auxiliary[c.auxiliaryHead]? (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => rfl
      | some bit => cases bit <;> rfl
  | step state write work input auxiliary index emit =>
      cases write <;> cases emit <;>
        simp only [instruction,Option.map_none,Option.map_some,runState,configuration,map_update]

theorem run (event : E) (data : InputData Unit Bool) (bits : BitString) (ticks : ℕ) :
    (machine family event).run data bits ticks=runState family event ((family event).run data bits ticks) := by
  exact Machine.run_map (fun _ => rfl) (fun _ => rfl)
    (observe family event data bits) (next family event data bits) (configuration_initial family event) ticks

theorem steps (event : E) (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration (family event)} {ticks : ℕ} (path : (family event).Steps data bits c ticks d) :
    (machine family event).Steps data bits (configuration family event c) ticks (configuration family event d) := by
  induction path with
  | refl => exact .refl
  | @tail ticks c d path edge ih =>
      exact .tail ih (by rw [next family event data bits,edge]; rfl)

end
end ComplexityOfGenerators.Simulation.NativeChoice
