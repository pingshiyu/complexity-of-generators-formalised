import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.NP
import Complexitylib.Classes.L
import Complexitylib.Classes.NP.Reduction
import Complexitylib.Classes.NP.CoNP

/-!
# Imported classical complexity definitions

The definitions below are aliases, not a second implementation. Complexitylib
provides concrete deterministic/nondeterministic multi-tape machines, asymptotic
time and space bounds, polynomial-time functions, and Karp reductions. Languages
are binary words, with malformed encodings included in the universe.

The paper's generator machines have different tape conventions. The existing
local decision definitions have NOT yet been identified with these imported
classes; see `ModelBridge`. No equality of machine models is assumed implicitly.
-/

namespace ComplexityOfGenerators.Standard

abbrev P := Complexity.P
abbrev NP := Complexity.NP
abbrev coNP := Complexity.coNP
abbrev PSPACE := Complexity.PSPACE
abbrev NPSPACE := Complexity.NPSPACE
abbrev L := Complexity.L
abbrev NL := Complexity.NL
abbrev FP := Complexity.FP
abbrev DTIME := Complexity.DTIME
abbrev NTIME := Complexity.NTIME
abbrev DSPACE := Complexity.DSPACE
abbrev NSPACE := Complexity.NSPACE
abbrev KarpReduction := Complexity.MapReducesPoly
abbrev NPHard := Complexity.NPHard
abbrev NPComplete := Complexity.NPComplete
abbrev coNPHard := Complexity.coNPHard
abbrev coNPComplete := Complexity.coNPComplete

end ComplexityOfGenerators.Standard
