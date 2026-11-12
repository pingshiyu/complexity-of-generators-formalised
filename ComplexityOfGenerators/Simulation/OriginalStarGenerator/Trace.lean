import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Basic
import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.NativeSplit
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Tail
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Terminal
import ComplexityOfGenerators.Proofs.OriginalSourceHookTrace
import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling.Basic

/-! One actual native star execution consumes the bounded certificate prefix,
then interleaves fresh original source paths with a deterministic controller
suffix. Its original-source contribution is linear. -/
namespace ComplexityOfGenerators.Simulation.OriginalStarGenerator
open NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)

theorem machine_runs_trace (n failures : ℕ) (parts : List ℕ)
    (records : List OriginalSourceFamilySampler.Record) (bits : BitString)
    (total : parts.sum=n) (positive : ∀ j∈parts,0 < j)
    (enough : (failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures,CertifiedStarPhase.value G.machine p n
      ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value G.machine p n
      ((bits.drop (failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts))
    (sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace (ExpectedOriginalStarSampling.families G)
      bits ((failures+1)*StarCertification.width p n) (parts.map (fun j=>(false,j))) records) :
    ∃ ticks,ticks≤25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2*(failures+1)^2+
      (6*n+20)*(OriginalSourceFamilySampler.totalTime (ExpectedOriginalStarSampling.families G) records+records.length) ∧
      (machine G.machine p).run (generatorData n) bits ticks=
        .halted (.accepted (OriginalSourceFamilySampler.words (ExpectedOriginalStarSampling.families G) records)) := by
  let C := ExpectedOriginalStarController.machine G.machine p
  let parameter := ExpectedOriginalStarController.parameter G.machine p
  let families := ExpectedOriginalStarSampling.families G
  let M := OriginalSourceFamilySampler.source families
  let start : Unit → Fin M.states := OriginalSourceFamilySampler.entry families (fun _=>false)
  obtain ⟨prefixTicks,tailTicks,tailStart,last,certPath,empty,cursor,trace,tail,stable,accepted,budget⟩ :=
    ExpectedOriginalStarController.machine_split_success G.machine p n failures parts bits total positive enough failed success
  have ready := Hook.initial_controllerReady C M parameter start (generatorData n)
  obtain ⟨target,targetReady,initialPath,initialOutput⟩ := Hook.controller_path C M parameter start
    (generatorData n) bits false C.initialConfiguration tailStart
    (Hook.machine C M parameter start).initialConfiguration ready prefixTicks certPath
    (by simpa only [Machine.initialConfiguration] using empty)
  have calls := OriginalSourceFamilySampler.finiteSequenceTrace_hook families (fun _ : Unit=>false)
    bits ((failures+1)*StarCertification.width p n) (parts.map (fun j=>(false,j))) records
    (parts.map (fun j=>((),j))) sourceTrace (by simp [List.map_map])
  rw [←cursor] at calls
  have indices : ∀ entry∈parts.map (fun j=>((),j)),entry.2≤n := by
    intro entry member
    obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
    exact (List.le_sum_of_mem inside).trans_eq total
  obtain ⟨controllerTicks,nativeTicks,origin,finish,controllerPath,time,finishReady,path,output⟩ :=
    Hook.execute_tail C M parameter start ExpectedOriginalStarController.allowed (generatorData n) bits n
      (parts.map (fun j=>((),j))) indices (records.map (OriginalSourceFamilySampler.hookRecord families))
      tailStart last target false targetReady trace stable calls
  have controllerBound := controllerPath.le_terminal C tail accepted
  have table := Hook.accepting_of_observe C (generatorData n) bits last _ accepted
  have terminal := Hook.controller_accept C M parameter start (generatorData n) bits origin
    (C.rebaseRandom last (tailStart.randomHead+Hook.totalCoins (records.map (OriginalSourceFamilySampler.hookRecord families))))
    finish finishReady table
  have finalPath := initialPath.trans (Hook.machine C M parameter start) path
  refine ⟨prefixTicks+nativeTicks,?_,?_⟩
  · simp only [OriginalSourceFamilySampler.hookRecord_time,List.length_map,families] at time
    omega
  · change (Hook.machine C M parameter start).run (generatorData n) bits (prefixTicks+nativeTicks)=_
    rw [←Machine.runFrom_initial,finalPath.runFrom,terminal,output,initialOutput]
    simp only [Machine.initialConfiguration,List.nil_append,OriginalSourceFamilySampler.hookRecord_words,families]

end
end ComplexityOfGenerators.Simulation.OriginalStarGenerator
