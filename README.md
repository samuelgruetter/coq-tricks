# Collection of Useful Features of the Coq Proof Assistant

Goal of this document: Let's make every Coq user's "OMG I wish I had known this before" moments happen as early as possible :wink:

Pull requests are welcome!


## Ltac

### lazymatch

In an Ltac `match`, a branch is taken only if the pattern matches *and* the rhs tactic succeeds.
If we want the decision to depend only on the pattern, but not on whether the rhs tactic succeeds, we can use `lazymatch` instead.

An important advantage of `lazymatch` compared to `match` is that it doesn't swallow errors, turning them into a generic "No matching clauses for match.".
For instance, if `pat1` and `pat2` are disjoint, and `x` matches `pat1`, but `tac1` fails, the following code will fail with "No matching clauses for match."

```
match x with
| pat1 => tac1
| pat2 => tac2
end.
```

However, if we replace `match` by `lazymatch`, it will fail with the error message of `tac1`.


### control flow

```
tryif tac1 then tac2 else tac3
```

Runs `tac1`, if `tac1` succeeds, continues with `tac2`, else reverts the effects of `tac1` and continues with `tac3`.

*Note*: If the `else` branch is a sequence of several commands separated by a semicolon, they have to be wrapped in parentheses, to get the operator precedence right.


```
assert_fails tac1
```

Runs `tac1`, always reverts the effects of `tac1`, and succeeds if `tac1` failed, and fails if `tac1` succeeded.


```
assert_succeeds tac1
```

Runs `tac1`, always reverts the effects of `tac1`, and succeeds if `tac1` succeeded, and fails if `tac1` failed.


```
unify term1 term2
constr_eq term1 term2
```

`unify` checks that two terms are unifiable, potentially instantiating evars.

`constr_eq` only does a syntactic comparison (modulo alpha-conversion and casts).

However, we often want a side-effect free unification test, ie. unification which does not instantiate evars:

```
assert_fails (has_evar term1); assert_fails (has_evar term2); unify term1 term2.
```

```
is_var term1
is_evar term1
```

succeeds if `term1` is a variable or evar, respectively.


### Tactic redefinition with `::=`

```
Ltac tac_name ::= ...
```

Overrides a previously defined tactic `tac_name` with a new implementation.

Useful to make libraries user-configurable, and to debug libraries without recompiling them.


### Ltac Profiler

Coq has an Ltac profiler which shows for each Ltac function how much time it took.

It will be part of Coq 8.6. For earlier versions, you can get it by applying a patch to the Coq source code, as described on the [LtacProf website](http://www.ps.uni-saarland.de/~ttebbi/ltacprof/).


## Vernacular

### Search

`Search ident.` lists all lemmas mentioning `ident`.

But `Search` is much more powerful than just that:
* `Search ident1 ... identN.` lists all lemmas mentioning all of `ident1` ... `identN`.
* `Search pattern.` lists all lemmas in which `pattern` occurs. For instance, you can

    ```
    Search (length (skipn _ _)).
    ```


### Custom reduction strategies

```
Declare Reduction foo := cbv [length app].

Eval foo in (length (app (cons 1 nil) (cons 2 nil))).
```


## Tools

### coqwc

`coqwc` is a stand-alone command line tool to print line statistics about Coq files (how many lines are spec, proof, comments).
