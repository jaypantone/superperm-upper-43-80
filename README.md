# superperm-upper-43-80

A superpermutation on `K` symbols is a word containing every permutation of
those symbols as a contiguous substring. This repository contains Lean proofs
that there are superpermutations on `K` symbols of length

$$
K!+(K-1)!+(K-2)!+\left(\frac{43}{80}+o(1)\right)(K-3)!,
$$

together with explicit superpermutations on 8 through 13 symbols.

## Results

Write $F_3(K)=K!+(K-1)!+(K-2)!$. Egan's construction gives superpermutations
of length $F_3(K)+(K-3)!+K-3$, and Raudvere improved this by one for every
$K\ge8$. The main theorem proved here lowers the coefficient of $(K-3)!$
from $1$ to $43/80$:

> For every rational $\varepsilon>0$ there is an $N\ge11$ such that every
> $K\ge N$ has a superpermutation of length at most
> $F_3(K)+(43/80+\varepsilon)(K-3)!$.

This follows from an explicit bound at every size. For integers $m\ge9$ and
$2\le a\le m$, put $h=m-1$ and $H=h!$. Then there is a superpermutation on
$K=m+2$ symbols of length at most

$$
F_3(m+2)+\frac{43}{80}H+(a-2)\frac{17H}{240h}
+(m-a)\min\left(\frac{17H}{240h},\frac{(m+1)!}{(a+1)!}\right).
$$

For a given `K ≥ 11`, set `m = K - 2`, try every `a`, and take the floor
of the smallest value; `python3 tools/finite_bound.py` does this. Both
statements have complete Lean proofs, which have been independently
audited. The sharper error term `O(log K / (K log log K))` in the coefficient
has an [ordinary proof](docs/upper-error-term.md) and is not formalized.

The library also proves the earlier uniform bounds
$F_3(K)+\frac35(K-3)!$ for `K ≥ 10` and $F_3(K)+\frac{101}{120}(K-3)!$ for
`K ≥ 8`, and the existence of words of lengths 46,181, 408,743 and
4,035,009 on 8, 9 and 10 symbols. [THEOREMS.md](THEOREMS.md) states
exactly what is formalized.

## Explicit words

| Symbols | Egan | Egan − 1 | Proved in Lean | Word in this repository |
|---:|---:|---:|---:|---|
| 8 | 46,205 | 46,204 | 46,181 | [46,181](words/8/superpermutation-8-46181.txt) |
| 9 | 408,966 | 408,965 | 408,743 | [408,736](words/9/superpermutation-9-408736.txt) |
| 10 | 4,037,047 | 4,037,046 | 4,035,009 | [4,034,894](words/10/superpermutation-10-4034894.txt) |
| 11 | 43,948,808 | 43,948,807 | 43,932,117 | [43,930,689](words/11/superpermutation-11-43930689.txt.xz) (XZ) |
| 12 | 522,910,089 | 522,910,088 | 522,759,498 | [522,748,520](words/12/superpermutation-12-522748520.txt.xz) (XZ), see below |
| 13 | 6,749,568,010 | 6,749,568,009 | 6,748,047,864 | [6,747,987,126](words/13/superpermutation-13-6747987126.txt.xz) (XZ) |

The eight-symbol word is exactly the construction. For 9 through 13 symbols,
the cuts and order of the pieces were then optimized by computer search.
Those shorter words are not proved in Lean; they are checked by the
independent scanner described below. Each file is one line over the alphabet
`0123456789ABC`, truncated to the required size, followed by one newline
that is not counted in the length. The files marked XZ are compressed with
`xz`, since the words on 11, 12 and 13 symbols would otherwise take about
44 MB, 523 MB and 6.7 GB; `xz -dk FILE` restores the text file.
[words/manifest.json](words/manifest.json) records the lengths and hashes.

The twelve-symbol word of length 522,748,520 comes from a tighter
construction. The ten-symbol base is transported once, to eleven symbols,
and its connector cycles are then chosen again at twelve symbols: 2,843
cycles instead of the 2,856 obtained by transporting the cycles chosen at
eleven symbols. The same argument then gives the coefficient
21659/40320 = 0.53718 in place of 43/80 = 0.5375, which is checked by
computer but not proved in Lean. The word was assembled by
`tools/construct.cpp`, changed only to read an eleven-symbol base, with its
default piece order and no further optimization. The earlier twelve-symbol
word, of length 522,752,900, is kept because
`tools/generate_large_words.py` rebuilds it from the data in this
repository.

## Check the Lean proofs

| File | Purpose |
|---|---|
| [Challenge.lean](Challenge.lean) | The statements, including an independent definition of coverage, separate from the proofs. |
| [Solution.lean](Solution.lean) | Proofs of the statements in `Challenge.lean`. |
| [AxiomCheck.lean](AxiomCheck.lean) | Prints the axioms each public theorem depends on. |

The project pins Lean 4.31.0 and Mathlib. With `elan` and Git installed,
run from the repository root:

```sh
lake exe cache get
lake build
```

The default build compiles the proofs and prints the axiom report. Every
public theorem should depend only on `propext`, `Classical.choice` and
`Quot.sound`; nothing uses `native_decide`. The first build checks the
finite certificates behind the construction, which takes a while. To compile
only the statements, run `lake build Challenge`.

## Check the word files

The checker needs a C++17 compiler and Python's standard library. It scans
every window of the word, independently of the construction, and confirms
that all permutations occur:

```sh
python3 tools/verify_words.py               # 8 through 11 symbols
python3 tools/verify_words.py --deletions   # also try deleting each letter
python3 tools/verify_words.py --degrees 12 13 --deletions
```

The `--deletions` option confirms that no single letter can be removed while
keeping coverage; it does not rule out other local changes. Compressed files
are checked against their hashes, extracted one at a time to a temporary
directory and removed afterwards. The thirteen-symbol word expands to about
6.75 GB, and its check needs about 13 GB of memory.

To check another word directly:

```sh
c++ -O3 -std=c++17 tools/literal_check.cpp -o literal_check
./literal_check 8 01234567 words/8/superpermutation-8-46181.txt --deletions
```

## Reconstruct the largest words

The twelve- and thirteen-symbol words can be rebuilt without any solver from
the ten-symbol starting data and saved component orders:

```sh
python3 tools/generate_large_words.py 12 --output-dir generated
python3 tools/generate_large_words.py 13 --output-dir generated
python3 tools/verify_words.py --degrees 12 13 --large-dir generated --deletions
```

The rebuilt words are checked against the hashes in the manifest. At thirteen
symbols the constructor needs about 13.5 GB of disk space. The input data is
in `tools/construction-input.txt` and `tools/recipes/`.

## Credits

This project made heavy use of AI models, for the computer searches, for
parts of the construction, and for writing and auditing the Lean proofs.

## License

Apache License 2.0; see [LICENSE](LICENSE).
