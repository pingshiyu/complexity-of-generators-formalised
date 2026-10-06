import Lake
open Lake DSL

package complexityOfGenerators where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require complexitylib from git
  "https://github.com/SamuelSchlesinger/complexitylib.git" @
  "d51bfbd39bea4d8a4a3282d4d4ddbb33709ea467"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio.git" @
  "9146f78c4f1bc2c9d8d92da686e9e375315ae5e7"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib ComplexityOfGenerators

-- Backport only the upstream cast-proof compatibility fix. See patches/README.md.
post_update pkg do
  let result ← IO.Process.output {
    cmd := "bash"
    args := #[(pkg.dir / "scripts" / "apply-compatibility-patches.sh").toString]
    cwd := some pkg.dir }
  if result.exitCode != 0 then
    error s!"Complexitylib compatibility patch failed:\n{result.stderr}"
