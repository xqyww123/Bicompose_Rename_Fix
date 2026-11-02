# bicompose_rename_fix: the three cases and the change

When Isabelle resolves a rule with a subgoal, as `rule`, `erule`, `drule`, `OF` and `RS` do, the
kernel function `Thm.bicompose_aux` (`src/Pure/thm.ML`) gives some unknowns (schematic variables)
of the rule the names of the subgoal's bound variables. Kevin Kappelmann and Fabian Huch found
three cases in which this renaming reaches only some occurrences of an unknown. The new proof state
then does not follow from the rule and the old state, and the three cases end in the theorems
`∀y. False`, `∀y. ¬ False ⟹ False` and `False`. This feature changes two arguments in
`bicompose_aux` so that the renaming reaches every occurrence.

## The renaming

To resolve a rule with the subgoal `Bi = ⋀a. H a ⟹ C a`, the kernel first *lifts* the rule: it
puts the parameters `a` and the assumptions `H a` in front of each premise and of the conclusion,
and it raises the indices of the rule's unknowns above those of the proof state. Then it unifies
the lifted conclusion with the subgoal. Before the unifier's assignments are applied to the new
subgoals, the local function `newAs` renames, for readability: `apply (rule exI)` on `∃y. Q y`
leaves the subgoal `Q ?y`, not `Q ?x`. An unknown that is renamed no longer receives the
assignment made to its old name.

- `rename_bvars` decides what to rename. It pairs the rule's bound variable names with the
  subgoal's: exI is `?P ?x ⟹ ∃x. ?P x`, so `x` is paired with `y`, and each unknown of the rule
  named `x` gets the name `y`. Only the name changes, never the index.
- It leaves a pair out when either name occurs in the part of the rule that was unified with the
  subgoal (the conclusion, and for `erule` also the premise that is eliminated) or in a flex-flex
  pair that this unification leaves unsolved. A flex-flex pair is a constraint such as
  `?f True =?= ?g True`, with an unknown at the head of both sides, which the kernel keeps
  unsolved. The flex-flex pairs that the rule itself carries are not looked at.
- `strip_apply` applies the renaming to each new subgoal. It first skips the parameters and
  assumptions that lifting put in front, because they come from the subgoal and can hold the proof
  state's own unknowns. To find where they end, it walks a guide term alongside the new subgoal:
  as long as both begin with `⋀`, or both with `⟹`, it skips one step. In Isabelle2026 the guide
  is the lifted conclusion of the rule, `B` in the code. `rename_bvars` skips in the same way when
  it collects the unknowns of the new subgoals.

Renaming an unknown everywhere in a rule, in its premises, its conclusion and its flex-flex pairs,
gives an instance of the rule, which is again a theorem. So the renaming in `newAs` does no harm as
long as its result is the same as renaming the whole rule before the step: every occurrence of a
renamed unknown must be renamed, or none.

## The three cases

**Case 1**, with `rule`:

```isabelle
lemma flex_rule1: "x True ⟹ x True" .
lemma flex_rule2: "P True ⟹ ∀x::bool. P True" by simp

lemma "∀y::bool. False"
  apply (rule flex_rule1[THEN flex_rule2])
  by (rule TrueI)
```

`THEN` unifies the conclusion `?x True` of `flex_rule1` with the premise `?P True` of
`flex_rule2`. Both sides begin with an unknown, so the kernel keeps the pair unsolved:
`flex_rule1[THEN flex_rule2]` is the rule `?x True ⟹ ∀x. ?P True` together with the flex-flex pair
`?x True =?= ?P True`. The bound `x` of `∀x` and the unknown `?x` have the same name.

Unification sets `?P := λ_. False`. Solving the flex-flex pair, now `?x True =?= False`, sets
`?x := λ_. False`, so the new subgoal `?x True` would become `False`. But before that, the renaming
pairs `x` with `y`, and since it does not look at the rule's own flex-flex pair, it renames `?x` to
`?y` in the new subgoal. The assignment to `?x` no longer reaches it: the new subgoal is `?y True`,
which `TrueI` closes.

**Case 2** is the same with `erule`:

```isabelle
lemma eres_rule: "P True ⟹ (∀x::bool. ¬ P True) ⟹ False" by simp

lemma "∀y::bool. ¬ False ⟹ False"
  apply (erule flex_rule1[THEN eres_rule, rotated])
  by (rule TrueI)
```

`flex_rule1[THEN eres_rule, rotated]` is the rule `(∀x. ¬ ?P True) ⟹ ?x True ⟹ False` with the
flex-flex pair `?x True =?= ?P True`. `erule` eliminates the assumption `∀y. ¬ False` with the
first premise. This pairs `x` with `y` and sets `?P := λ_. False`, and the new subgoal `?x True`
becomes `?y True`, which `TrueI` closes.

**Case 3**, with a rule whose conclusion begins with `⋀`:

```isabelle
definition X :: "prop" where "X ≡ (⋀w::bool. True ⟹ False)"
lemma split_rule: "(⋀z::bool. z = w ⟹ z ≠ w) ⟹ PROP X"
  unfolding X_def by auto
lemma split_aux: "z = True ⟹ z ≠ False" by simp

schematic_goal split_bad: "PROP ?G (λv::nat. v)"
  apply (rule split_rule[unfolded X_def])
  apply (rule split_aux)
  apply assumption
  done

lemma False by (rule split_bad) (rule TrueI)
```

After `unfolded`, the rule's conclusion is `⋀w. True ⟹ False`, that is,
`Pure.all (λw. True ⟹ False)`. Isabelle normally moves such a `⋀` in front of the premises;
`unfolded` does not. The pairing compares the conclusion with the subgoal `PROP ?G (λv. v)` position
by position, so the conclusion's `λw` meets the subgoal's `λv`, and `?w` is to become `?v`.

The subgoal has no parameters and no assumptions, so lifting puts nothing in front of the premise,
and nothing is to be skipped. But `strip_apply` follows the lifted conclusion `⋀w. True ⟹ False`,
and its `⋀w` and `⟹` line up with the `⋀z` and the `⟹` of the premise `⋀z. z = ?w ⟹ z ≠ ?w`. So
`strip_apply` skips `z = ?w` as if lifting had put it there, and renames only `z ≠ ?w`. In the new
subgoal `⋀z. z = ?w ⟹ z ≠ ?v`, the one unknown `?w` has become two. `split_aux` sets `?v := False`,
and `assumption` sets `?w := True`. So `split_bad` is the theorem `⋀w. True ⟹ False`, and the last
line derives `False` from it.

## The change

```diff
     fun newAs (As0, n, dpairs, tpairs) =
       let val (As1, rder') =
         if lifted then
-          (case rename_bvars dpairs tpairs B As0 of
+          (case rename_bvars dpairs (rtpairs @ tpairs) Bi As0 of
             SOME term =>
               let fun proof p = Same.commit (Proofterm.map_proof_terms_same term I) p;
-              in (map (strip_apply (Same.commit term) B) As0, deriv_rule1 I proof rder) end
+              in (map (strip_apply (Same.commit term) Bi) As0, deriv_rule1 I proof rder) end
```

- `rtpairs @ tpairs`: the rule's own flex-flex pairs (`rtpairs`) join the pairs whose names are
  never renamed (Cases 1 and 2). The change sits in `newAs`, which both `rule` and `erule` reach.
- `Bi` instead of `B`, in both calls: what `strip_apply` skips now follows the subgoal `Bi`, the
  same term that lifting followed (`Logic.lift_all`), so the skipping stops exactly where lifting
  stopped (Case 3). `rename_bvars` gets the same `Bi`, so the unknowns it collects from the new
  subgoals are the ones that `strip_apply` renames. The comment above `strip_apply` already says
  that it skips the "assumptions/parameters from A introduced by lifting".

With the change, Cases 1 and 2 leave the subgoal `False`, and Case 3 leaves
`⋀z. z = ?v ⟹ z ≠ ?v`; none of them proves `False` any more.

## What changes for you

A result can differ only when the rule carries flex-flex pairs, which arise from combinations such
as `[THEN]` that leave a pair unsolved, or when the rule's conclusion begins with `⋀`, as after
`unfolded` in Case 3. Both are rare. In each of two full builds of Isabelle's group `main` (HOL,
HOL-Library, HOL-Analysis, ZF and the others), the renaming acted in more than 640,000 resolution
steps, counting those inside automatic methods such as `auto`, and no new subgoal changed.

The session in [`tests/`](https://github.com/xqyww123/Bicompose_Rename_Fix/tree/main/tests) checks
that the three cases no longer prove `False`, that ordinary rule steps (`rule exI`, `erule allE`,
`rule allI`) still rename, and that the proof state's own unknowns keep their names. On Isabelle
without this feature, the session fails.
