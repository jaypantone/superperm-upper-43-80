# Reading the Lean formalization

Start with [Challenge.lean](Challenge.lean). It defines the mathematical
statements independently of the proof libraries, and
[Solution.lean](Solution.lean) proves them. A challenge file is a useful
convention for separating a problem statement from its solution; it is not a
special Lean file type. Here the statements are definitions of propositions,
with no admitted proofs or added axioms.

The alphabet `Fin K` consists of the integers from `0` through `K - 1`.
A word is a finite list of these symbols. `Covers w` quantifies over every
duplicate-free list `p` of length `K` and requires `w = u ++ p ++ v` for some
lists `u` and `v`. Thus every permutation must occur contiguously in one
linear word.

## Main finite upper theorem

Write

$$
F_3(K)=K!+(K-1)!+(K-2)!.
$$

For integers $m\ge9$ and $2\le a\le m$, put $h=m-1$ and
$H=h!$. The theorem gives a superpermutation on $K=m+2$ symbols
of length at most

$$
F_3(m+2)+\frac{43}{80}H
+(a-2)\frac{17H}{240h}
+(m-a)\min\left(\frac{17H}{240h},\frac{(m+1)!}{(a+1)!}\right).
$$

This is `Cost m a` in the challenge file. The two public proofs are
`SuperpermutationBounds.finite_bound`, with a natural-number parameter, and
`SuperpermutationBounds.finite_bound_integer`, with an integer parameter.
They express the same mathematical range. All divisions in the bound are
rational; the hypotheses ensure that factorial arguments and conversions
have their intended meaning.

For a particular alphabet size `K ≥ 11`, set `m = K - 2`, evaluate the
finite list of choices `a = 2, …, m`, and take the smallest bound. A word's
integer length is at most the floor of the chosen rational bound.
The coefficient `43/80` by itself is not the finite-size bound: the two
additional nonnegative terms must be included.

## Asymptotic consequence

`SuperpermutationBounds.eventual_bound` proves that, for every positive
rational $\varepsilon$, there is an $N\ge11$ such that every
$K\ge N$ has a superpermutation of length at most

$$
F_3(K)+\left(\frac{43}{80}+\varepsilon\right)(K-3)!.
$$

The threshold is uniform over all `K ≥ N`; it is not a separate assertion
for an unbounded sequence of sizes. The paper also proves the more explicit
coefficient error `O(log K / (K log log K))`. That error rate is not
formalized in this repository.

## Other public theorems

All names in this table have the prefix `SuperpermutationBounds.`.

| Lean theorem | Statement |
|---|---|
| `word_eight` | There exists a superpermutation on 8 symbols of length at most 46,181. |
| `word_nine` | There exists a superpermutation on 9 symbols of length at most 408,743. |
| `word_ten_structural` | There exists a superpermutation on 10 symbols of length at most 4,035,009. |
| `uniform_three_fifths` | For every `K ≥ 10`, length at most `F3(K) + (3/5)(K-3)!`. |
| `uniform_101_over_120` | For every `K ≥ 8`, length at most `F3(K) + (101/120)(K-3)!`. |

The uniform bounds come from an earlier construction and its finite base
cases. Their current Lean proofs are separate from the `43/80` proof.
The `101/120` result is included as a consequence already used by the
library; the eight- and nine-symbol theorems together with `3/5` give at
least as strong a bound throughout its range.

The smaller optimized words in [words/manifest.json](words/manifest.json)
are checked by a separate literal scanner. The general existence theorems
do not certify the bytes of those files, and the `word_nine` and
`word_ten_structural` bounds are larger than the corresponding optimized
literal words. No optimum or matching lower bound is asserted.

## How the proof is organized

The proof is in two libraries. `SuperpermutationUpperBound` contains the
general machinery and the earlier bounds. `SuperpermutationUpperBound43`
adds the certificate for 43/80 and the argument that turns it into the
main theorems, reusing that machinery.

| Source | Role |
|---|---|
| [Foundation/Words.lean](SuperpermutationUpperBound/Foundation/Words.lean) | Finite words, permutations, and contiguous coverage. |
| [Rows.lean](SuperpermutationUpperBound/Rows.lean) and [RowSpelling.lean](SuperpermutationUpperBound/RowSpelling.lean) | The local row construction and the words it spells. |
| [Partition/](SuperpermutationUpperBound/Partition/) and [Completion/](SuperpermutationUpperBound/Completion/) | Coverage under extension to a larger alphabet. |
| [Transport/](SuperpermutationUpperBound/Transport/) and [CircleTransport/](SuperpermutationUpperBound/CircleTransport/) | Closed trails, ports, and transport of connector circles. |
| [BalancedCuts/](SuperpermutationUpperBound/BalancedCuts/) and [Assembly/](SuperpermutationUpperBound/Assembly/) | Integral cuts, directed trails, joins, and their literal costs. |
| [Certificate/](SuperpermutationUpperBound43/Certificate/) | The explicit finite partition and connector data used for `43/80`, together with proofs of their properties. |
| [Family.lean](SuperpermutationUpperBound43/Family.lean) | Transport of that certified data to every required size. |
| [GenericBounds.lean](SuperpermutationUpperBound43/GenericBounds.lean) | Finite arithmetic bounds and the eventual epsilon argument. |
| [Main.lean](SuperpermutationUpperBound43/Main.lean) | Discharges the finite certificate and states unconditional construction theorems. |

The base data cover 40,320 cyclic blocks in 350 parents, with total charge
18,816 and 357 connector circles. The proof checks the actual partition and
the required contacts, then transports them. The principal coefficient is
`(18816 + 8 × 357) / 40320 = 43/80`. The word-existence conclusions retain
no assumption that these certificate checks succeed: their proofs establish
them.

## Checking the project

[lean-toolchain](lean-toolchain) pins Lean 4.31.0.
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json)
pin Mathlib and its transitive dependencies. With `elan` and Git installed,
run from the repository root:

```sh
lake exe cache get
lake build
```

The default targets compile `Solution` and `AxiomCheck`, including their
proof dependencies. To check only the independent statement file after
installing dependencies, use `lake build Challenge`.
The first construction build includes substantial finite certificate
checking; the Mathlib cache does not provide compiled copies of this
project's own proofs.

[AxiomCheck.lean](AxiomCheck.lean) prints each public theorem's transitive
axioms. The expected output contains only `propext`, `Classical.choice`,
and `Quot.sound`, the standard logical axioms used here. It contains no
`sorryAx` or project-specific axiom.
