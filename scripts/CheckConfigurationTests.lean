import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinate
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindowCorrectness
import ComplexityOfGenerators.Simulation.SavitchMachine.MoveCheck
import ComplexityOfGenerators.Simulation.StackSpace.ReadAt
import ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationHeader
import ComplexityOfGenerators.Simulation.SavitchMachine.InputObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.IndexObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateBound
import ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint
import ComplexityOfGenerators.Simulation.SavitchMachine.HeadRelation
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkRelation
import ComplexityOfGenerators.Simulation.SavitchMachine.ClearCaches

/-! Execute the actual finite base-test component programs. The imported
proofs establish their universal semantics and space bounds; these guards
exercise malformed encodings, window endpoints and single-cell writes. -/

open ComplexityOfGenerators Simulation StackSpace SavitchMachine
namespace ConfigurationTestChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def execute {S Q V : Type} {k : ℕ} (P : Q → Stmt S Q V k) :
    ℕ → Source S Q V k → Option (Source S Q V k)
  | 0, _ => none
  | fuel + 1, c => match Turing.TM2.step P c with
      | none => some c
      | some next => execute P fuel next

def coordinate (bits : List Bool) (bound : ℕ) (valid : Bool) (value : ℕ) (rest : List Bool) : Bool :=
  let initial := localConfig ReadCoordinate.Label.scan (carrying false false)
    (ReadCoordinate.registers bits 0 bound)
  (execute ReadCoordinate.program 20000 initial).any fun final =>
    decide (final.var.1.returned = some valid ∧ final.var.2 = none) &&
    decide (final.stk 0 = rest.map some ∧ final.stk 1 = BoundedDecode.unary value ∧
      final.stk 2 = BoundedDecode.unary bound ∧ final.stk 3 = [] ∧ final.stk 4 = [] ∧ final.stk 5 = [])

#guard coordinate [false, true, false, true, true] 3 true 2 [true, true]
#guard coordinate [true, true, false, true] 3 false 3 [true]
#guard coordinate [true] 3 false 0 []
#guard coordinate [true, false] 0 false 0 [true, false]

def move (direction : Move) (clamp : Bool) (value bound target : ℕ) (expected : Bool) : Bool :=
  let initial := localConfig MoveCheck.Label.start (carrying false false)
    (MoveCheck.registers value bound target)
  (execute (MoveCheck.program direction clamp) 20000 initial).any fun final =>
    decide (final.var.1.returned = some expected ∧ final.var.2 = none)

#guard move .left true 0 3 0 true
#guard move .left false 0 3 0 false
#guard move .left false 1 3 0 true
#guard move .left true 2 3 2 false
#guard move .stay false 2 3 2 true
#guard move .stay true 2 3 1 false
#guard move .right true 3 3 3 true
#guard move .right false 3 3 3 false
#guard move .right false 2 3 3 true
#guard move .right true 1 3 3 false
#guard move .right true 0 0 0 true
#guard move .right false 0 0 0 false
#guard move .stay false 0 0 0 true

def cellBits (symbols : ℕ) (cells : List (Option (Fin symbols))) : List Bool :=
  cells.flatMap (FixedWidthCodec.optionFin symbols).encode

def window (symbols : ℕ) (observed write : Option (Fin symbols))
    (count head : ℕ) (u v : List Bool) (expected : Bool) : Bool :=
  let initial := localConfig (WorkWindow.Label.loop false) (carrying false false)
    (WorkWindow.registers u v count head)
  (execute (WorkWindow.program symbols observed write) 20000 initial).any fun final =>
    decide (final.var.1.returned = some expected ∧ final.var.2 = none)

def cells (observed write : Option (Fin 2)) (head : ℕ)
    (u v : List (Option (Fin 2))) (expected : Bool) : Bool :=
  window 2 observed write u.length head (cellBits 2 u) (cellBits 2 v) expected

#guard cells none none 0 [none] [none] true
#guard cells none (some 0) 0 [none] [some 0] true
#guard cells none (some 0) 0 [none] [none] false
#guard cells (some 1) none 1 [none, some 1, none] [none, some 1, none] true
#guard cells (some 0) none 1 [none, some 1, none] [none, some 1, none] false
#guard cells (some 1) (some 0) 1 [none, some 1, none] [none, some 0, none] true
#guard cells (some 1) (some 0) 1 [none, some 1, none] [some 0, some 0, none] false
#guard cells none (some 1) 2 [none, some 1, none] [none, some 1, some 1] true
#guard cells none none 3 [none, none, none] [none, none, none] false
#guard window 2 none none 1 0 [false] [false] false
#guard window 2 none none 1 0 [true, true, false] [true, true, false] false
#guard window 2 none none 1 0 [false, false, false, false] [false, false, false, false] false
#guard window 0 none none 1 0 [false] [false] true
#guard window 0 none none 0 0 [] [] false

inductive ReadLabel | loop | inspect | done deriving DecidableEq

def readProgram (expected : Option (Fin 5)) : ReadLabel → Stmt (Fin 5) ReadLabel (Bool × Option (Fin 5)) 1
  | .loop => readAtCode 0 1 .loop .inspect
  | .inspect => inspectCode 0 (fun s _ => decide (s = expected)) .done
  | .done => .halt

def read (word : List (Fin 5)) (position : ℕ) (expected : Option (Fin 5)) : Bool :=
  let initial := localConfig ReadLabel.loop false ![word, List.replicate position (0 : Fin 5)]
  (execute (readProgram expected) 1000 initial).any fun final =>
    final.var.1 && decide (final.var.2 = none ∧ final.stk 0 = word.drop position ∧ final.stk 1 = [])

#guard read [4, 2, 1] 0 (some 4)
#guard read [4, 2, 1] 1 (some 2)
#guard read [4, 2, 1] 2 (some 1)
#guard read [4, 2, 1] 3 none
#guard read [] 0 none
#guard read [] 2 none

abbrev Original := Fin 5

def headerCompare (a b bound source : ℕ) (bits : List Bool) (expected : Bool) : Bool :=
  let word : List (Alphabet Original) := Alphabet.input [4, 2, 1]
  let initial := localConfig (HeadComparison.Label.read (.skip .copy)) (carrying false false)
    (ReadCoordinateAt.before (Alphabet.write (α := Original)) bits
      ((BoundedDecode.unary source).map Alphabet.write) bound word)
  (execute (HeadComparison.program Alphabet.write Alphabet.read a b .right false) 50000 initial).any fun final =>
    decide (final.var.1.returned = some expected ∧ final.var.2 = none ∧ final.stk 6 = word)

#guard headerCompare 0 2 4 1 [true, false, false, true, false, false] true
#guard headerCompare 0 2 4 1 [true, false, true, true, false, false] false
#guard headerCompare 0 2 4 1 [true, false, true, true, true, true] false
#guard headerCompare 0 2 4 1 [true, false, false] false
#guard headerCompare 1 4 4 2 ([true, false, false, true, false, false, false] ++ [true, true, false, false]) true

def inputObserved (headBits : List Bool) (expected : Option Original) (result : Bool) : Bool :=
  let word : List Original := [4, 2, 1]
  let input := Alphabet.input word
  let initial := localConfig (InputObservation.Label.read (.skip .copy)) (carrying false false)
    (ReadCoordinateAt.before (Alphabet.write (α := Original)) ([true, false] ++ headBits) [] 4 input)
  (execute (InputObservation.program 2 expected) 50000 initial).any fun final =>
    decide (final.var.1.returned = some result ∧ final.var.2 = none ∧ final.stk 6 = input)

#guard inputObserved [false, true, false, false] (some 1) true
#guard inputObserved [false, true, false, false] (some 4) false
#guard inputObserved [true, true, false, false] none true
#guard inputObserved [true, true, true, true] none false
#guard inputObserved [false] none false

def indexObserved (headBits : List Bool) (expected result : Bool) : Bool :=
  let input : List (Alphabet Original) := Alphabet.input [4, 2, 1]
  let bits := [true, false, false, true, false, false, false] ++ headBits
  let initial := localConfig (IndexObservation.Label.read (.skip .copy)) (carrying false false)
    (ReadCoordinateAt.before (Alphabet.write (α := Original)) bits [] 4 input)
  (execute (IndexObservation.program Alphabet.write Alphabet.read 2 expected) 50000 initial).any fun final =>
    decide (final.var.1.returned = some result ∧ final.var.2 = none ∧ final.stk 6 = input)

#guard indexObserved [false, true, false, false] true true
#guard indexObserved [false, true, false, false] false false
#guard indexObserved [true, true, false, false] false true
#guard indexObserved [true, true, false, false] true false
#guard indexObserved [true, true, true, true] false false
#guard indexObserved [] false false

def workObserved (headBits windowBits : List Bool) (expected : Option (Fin 2)) (result : Bool) : Bool :=
  let input : List (Alphabet Original) := Alphabet.input [4, 2, 1]
  let header := [true, false, false, true, false, false, false, true, true, false, false]
  let bits := header ++ headBits ++ windowBits
  let initial := localConfig WorkObservation.Label.copyCode (carrying false false)
    (ReadCoordinateAt.before (Alphabet.write (α := Original)) bits [] 3 input)
  (execute (WorkObservation.program Alphabet.write Alphabet.read 2 2 expected) 50000 initial).any fun final =>
    decide (final.var.1.returned = some result ∧ final.var.2 = none ∧ final.stk 6 = input)

#guard workObserved [true, false, false] (cellBits 2 [none, some 1, none]) (some 1) true
#guard workObserved [true, false, false] (cellBits 2 [none, some 1, none]) (some 0) false
#guard workObserved [true, true, false] (cellBits 2 [none, some 1, none]) none false
#guard workObserved [true, false, false] (cellBits 2 [none, some 1]) (some 1) false
#guard workObserved [true, false, false] (cellBits 2 [none, some 1, none] ++ [false]) (some 1) false
#guard workObserved [true, false, false] ([false, false, false, true, true, false, false, false, false]) none false

def coordinateBound (work : Bool) (input : List (Alphabet Original)) (expected : ℕ) : Bool :=
  let symbol := Alphabet.write (α := Original) (some false)
  let source : List (Alphabet Original) := [Alphabet.write (some true), Alphabet.write (some false)]
  let space : PolynomialBound := ⟨1, 0, by decide⟩
  let initial := localConfig (CoordinateBound.Label.ruler .copyInput) false
    (CoordinateBound.registers symbol source input 0)
  (execute (CoordinateBound.program symbol space work) 50000 initial).any fun final =>
    decide (final.stk = CoordinateBound.registers symbol source input expected ∧ final.var = (false, none))

#guard coordinateBound false (Alphabet.input [4, 2, 1]) 4
#guard coordinateBound true (Alphabet.input [4, 2, 1]) 3
#guard coordinateBound false [] 1
#guard coordinateBound true [] 3

def endpoint (bits : List Bool) : Bool :=
  let encoded := (bits.map some).map (Alphabet.write (α := Original))
  let delimiter := Alphabet.write (α := Original) none
  let parent := [Alphabet.write (α := Original) (some true), delimiter]
  let stk : Fin 8 → List (Alphabet Original) :=
    ![[], [Alphabet.write (some false)], [Alphabet.write (some false)], [], [],
      [Sum.inl 4], Alphabet.input [4, 2, 1], encoded ++ delimiter :: parent]
  let initial := localConfig Endpoint.Label.load false stk
  (execute (Endpoint.program delimiter (fun x => (Alphabet.read x).isSome)) 1000 initial).any fun final =>
    decide (final.stk = Function.update stk 0 encoded ∧ final.var = (false, none))

#guard endpoint []
#guard endpoint [true, false, true]

def cleanup : Bool :=
  let stk : Fin 8 → List Bool := ![[true], [], [false, true], [true], [false], [true, true], [false, false], [true, false]]
  let initial := localConfig (0 : ClearCaches.Label) true stk
  (execute ClearCaches.program 1000 initial).any fun final =>
    decide (final.stk = ![[], [], [], [], [], [], stk 6, stk 7] ∧ final.var = (true, none))

#guard cleanup

def relatedHeads (u v : List Bool) (clamp : Bool) (result : Bool) : Bool :=
  let input := Alphabet.input (α := Original) [4, 2, 1]
  let column := (([false, false] ++ v).map some).map (Alphabet.write (α := Original)) ++
    [Alphabet.write none, Alphabet.write (some true), Alphabet.write none]
  let initial := localConfig (HeadRelation.Label.read (.skip .copy)) (carrying false false)
    (Fin.snoc (ReadCoordinateAt.before Alphabet.write ([false, false] ++ u) [] 4 input) column)
  (execute (HeadRelation.program 0 2 .right clamp) 50000 initial).any fun final =>
    decide (final.var = (carrying false result, none) ∧ final.stk 6 = input ∧ final.stk 7 = column)

#guard relatedHeads [true, false, false, false] [false, true, false, false] true true
#guard relatedHeads [true, true, false, false] [true, true, false, false] true true
#guard relatedHeads [true, true, false, false] [true, true, false, false] false false
#guard relatedHeads [true, true, true, true] [false, true, false, false] true false
#guard relatedHeads [true, false] [false, true, false, false] true false

def relatedWork (headBits sourceCells targetCells : List Bool)
    (write : Option (Fin 2)) (result : Bool) : Bool :=
  let input := Alphabet.input (α := Original) [4, 2, 1]
  let header := [true, false, false, true, false, false, false, true, true, false, false]
  let source := header ++ headBits ++ sourceCells
  let target := header ++ [false, false, false] ++ targetCells
  let column := (target.map some).map (Alphabet.write (α := Original)) ++
    [Alphabet.write none, Alphabet.write (some true), Alphabet.write none]
  let initial := localConfig WorkRelation.Label.copyCode (carrying false false)
    (Fin.snoc (ReadCoordinateAt.before Alphabet.write source [] 3 input) column)
  (execute (WorkRelation.program 2 2 (some 1) write) 50000 initial).any fun final =>
    decide (final.var = (carrying false result, none) ∧ final.stk 6 = input ∧ final.stk 7 = column)

#guard relatedWork [true, false, false] (cellBits 2 [none, some 1, none])
  (cellBits 2 [none, some 0, none]) (some 0) true
#guard relatedWork [true, false, false] (cellBits 2 [none, some 1, none])
  (cellBits 2 [none, some 1, none]) none true
#guard relatedWork [true, false, false] (cellBits 2 [none, some 1, none])
  (cellBits 2 [some 0, some 0, none]) (some 0) false
#guard relatedWork [true, false, false] (cellBits 2 [none, some 1, none])
  (cellBits 2 [none, some 0]) (some 0) false
#guard relatedWork [true, true, false] (cellBits 2 [none, some 1, none])
  (cellBits 2 [none, some 0, none]) (some 0) false

end ConfigurationTestChecks
