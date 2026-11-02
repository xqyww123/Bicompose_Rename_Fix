# bicompose_rename_fix

In Isabelle2026, resolution with a rule, as in `rule`, `erule`, `drule`, `OF` or `RS`, can prove
`False`. In such a step the kernel gives some unknowns (schematic variables) of the rule the names
of the subgoal's bound variables, for readability: after `rule exI` on `∃y. Q y` the subgoal is
`Q ?y`. In some cases it renames an unknown in one place but not in another. This feature makes the
renaming reach every occurrence. Isabelle2025-2 behaves the same way; this package changes
Isabelle2026 only.

You need it if you rely on Isabelle to check proofs you did not write yourself, for example proofs
written by AI agents. The change leaves ordinary proofs alone: in every session of Isabelle's group
`main`, every new subgoal stays the same.

Kevin Kappelmann and Fabian Huch found the three cases in which this happens;
[`details.md`](https://github.com/xqyww123/Bicompose_Rename_Fix/blob/main/details.md) shows them
and explains the change.

## Sources

This repository holds the Isabelle sources the feature changes as git submodules:
`worktrees/Isabelle2026-bicompose_rename_fix` is Isabelle with this feature,
`worktrees/Isabelle2026-bicompose_rename_fix-stock` the same Isabelle without it. To get a release:

```
git clone --recurse-submodules -b Isabelle2026/bicompose_rename_fix/<m> https://github.com/xqyww123/Bicompose_Rename_Fix.git
```

In an existing clone, `git checkout Isabelle2026/bicompose_rename_fix/<m>` and then
`git submodule update --init`; a plain checkout leaves the submodules where they were. `<m>` is the
last number of the package version: `1` for `2026.0.1`.
