import ComplexityOfGenerators.Simulation.CollisionHashRun
import ComplexityOfGenerators.Simulation.CollisionParserData

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem hashBankConfiguration_initial (second : Bool) (frame)
    (input : frame.head (hashInputTape second) = 0) (index : frame.head 2 = 0)
    (work : frame.head (hashWorkTape second) = 0) (output : frame.head (hashOutputTape second) = 0)
    (blankWork : frame.tape (hashWorkTape second) = fun _ => collisionBlank M)
    (blankOutput : frame.tape (hashOutputTape second) = fun _ => collisionBlank M) :
    hashBankConfiguration M second frame M.initialConfiguration =
      {frame with state := .hashWork second M.initial} := by
  apply BankConfiguration.ext
  · rfl
  · rfl
  · funext j
    simp only [hashBankConfiguration, Machine.initialConfiguration, List.length_nil, Int.natCast_zero,
      Function.update_apply]
    split_ifs <;> simp_all
  · funext j i
    simp [hashBankConfiguration, Machine.initialConfiguration, Function.update_apply]
    split_ifs <;> simp_all [collisionBlank]

end
end ComplexityOfGenerators.Simulation
