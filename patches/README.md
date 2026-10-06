# Complexitylib compatibility backport

`complexitylib-asymptotics.patch` is the change to
`Complexitylib/Asymptotics.lean` between pinned commit
`d51bfbd39bea4d8a4a3282d4d4ddbb33709ea467` and upstream commit
[`257ad90ec5f547894cc20f27bd828839b1bf7bbf`](https://github.com/SamuelSchlesinger/complexitylib/commit/257ad90ec5f547894cc20f27bd828839b1bf7bbf).

It adapts four proofs to changes in `convert`'s generated goals under the shared
Lean/Mathlib 4.34 toolchain. Statements and definitions are unchanged. This is a
verbatim upstream backport, not a substitute complexity library. All affected
proofs are recompiled and checked by Lean.

`lake update` applies it automatically through the root post-update hook.
The script also accepts an already applied patch and fails on unexpected source
changes. No other dependency sources are modified.
