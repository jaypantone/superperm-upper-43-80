# The finite upper bound and its logarithmic error term

The finite bound and its eventual positive-epsilon consequence are proved in
Lean. This supplement gives an **ordinary mathematical proof** of the sharper
error estimate

$$
S(K)\le F_3(K)+\left(\frac{43}{80}
+O\!\left(\frac{\log K}{K\log\log K}\right)\right)(K-3)!,
$$

where $F_3(K)=K!+(K-1)!+(K-2)!$. The logarithmic rate, and the direct
comparison with $3/5$ proved below, are not additional Lean theorems in
this repository. All logarithms here are natural logarithms.

## The exact finite expression

For $m\ge9$, $2\le a\le m$, $K=m+2$, and $H=(m-1)!$, the
[formalized finite theorem](../Challenge.lean) gives a covering word of
length at most $C(m,a)$, where

$$
\frac{C(m,a)-F_3(m+2)}{H}
=\frac{43}{80}+\Delta(m,a)
$$

and, with $\gamma=17/240$,

$$
\Delta(m,a)=
\gamma\frac{a-2}{m-1}
+(m-a)\min\left\{\frac{\gamma}{m-1},
                   \frac{m(m+1)}{(a+1)!}\right\}.
\tag{1}
$$

The factorial ratio in (1) follows from

$$
\frac{(m+1)!}{(m-1)!(a+1)!}=\frac{m(m+1)}{(a+1)!}.
$$

Both terms of $\Delta$ are nonnegative. The first grows with the chosen
cut parameter $a$; the second can be reduced rapidly by increasing
$(a+1)!$. The logarithmic error comes from choosing $a$ to control both
terms.

## A factorial estimate gives the rate

Choose the least integer $a\ge2$ such that

$$
(a+1)!\ge m^4.
\tag{2}
$$

We first show that, for all sufficiently large $m$, this choice is
admissible and satisfies

$$
a=O\!\left(\frac{\log m}{\log\log m}\right).
\tag{3}
$$

Put $L=\log m$, $\ell=\log L$, and

$$
b=\left\lceil\frac{5L}{\ell}\right\rceil.
$$

These quantities are positive for all sufficiently large $m$. For any
integer $t\ge2$, monotonicity of $\log$ gives the elementary bound

$$
\log(t!)=\sum_{j=2}^{t}\log j
\ge\int_1^t\log x\,dx
=t\log t-t+1.
$$

The function $x(\log x-1)$ is increasing for $x\ge1$. Since
$b+1\ge5L/\ell$, we obtain, eventually,

$$
\begin{aligned}
\log((b+1)!)
&\ge\frac{5L}{\ell}
   \left(\log\frac{5L}{\ell}-1\right)\\
&=5L\left(1-\frac{\log\ell-\log5+1}{\ell}\right).
\end{aligned}
$$

The expression in parentheses tends to 1, because
$(\log\ell)/\ell\to0$. It is therefore at least $4/5$ for all
sufficiently large $m$, proving $(b+1)!\ge m^4$. Thus the least choice
in (2) has $a\le b$, which proves (3). Also $b/m\to0$, so eventually
$2\le a\le m$, as required by the finite theorem.

For this admissible choice, the second term of (1) is at most

$$
\frac{m(m+1)(m-a)}{(a+1)!}
\le\frac{m^2(m+1)}{m^4}
=\frac{m+1}{m^2}
\le\frac2m.
$$

The first term is $O(a/m)$. Substituting (3) therefore gives

$$
0\le\Delta(m,a)
\le\gamma\frac{a-2}{m-1}+\frac2m
=O\!\left(\frac{\log m}{m\log\log m}\right).
\tag{4}
$$

A loose explicit constant is also available. The inequalities $a-2\le5L/\ell$,
$m-1\ge m/2$, and $L/\ell\ge1$ imply

$$
\Delta(m,a)\le
(10\gamma+2)\frac{L}{m\ell}
=\frac{65}{24}\frac{\log m}{m\log\log m}
$$

for all sufficiently large $m$. Since $K=m+2$, replacing $m$ by $K$ changes the scale in (4)
by a factor tending to 1. This proves the stated logarithmic rate.

In terms of added letters, the estimate is equivalently

$$
O\!\left(\frac{\log K}{\log\log K}(K-4)!\right),
$$

because $(K-3)!/K=((K-3)/K)(K-4)!$. This is an upper estimate for the
construction's error. It does not establish that the optimal error, or the
optimal superpermutation length, grows at this rate.

## A concrete bound for every finite size

No asymptotic cutoff or unknown constant is needed to evaluate the finite
theorem. For each $K\ge11$, define

$$
U(K)=\left\lfloor
\min_{a\in\{2,\ldots,K-2\}}C(K-2,a)
\right\rfloor.
$$

Then $S(K)\le U(K)$. The minimum has exactly $K-3$ choices. Every
quantity is an integer or a rational number, so it can be evaluated exactly.
The floor is valid because word lengths are integers. For example:

| $K$ | Minimizing $a$ | $U(K)$ |
|---:|---:|---:|
| 11 | 7 | 43,932,117 |
| 12 | 7 | 522,759,498 |
| 13 | 8 | 6,748,047,864 |
| 14 | 8 | 93,907,379,760 |
| 15 | 8 | 1,401,355,309,200 |

[tools/finite_bound.py](../tools/finite_bound.py) contains the exact rational
evaluation. The optimized literal words in the repository can be shorter
than $U(K)$: the formula bounds the costs of a valid assembly, and does
not claim those bounds are attained by the best ordering and joins.

## Relation to the uniform coefficient $3/5$

The repository also contains an earlier, separately formalized theorem

$$
S(K)\le F_3(K)+\frac35(K-3)!
\qquad(K\ge10).
$$

Its existing Lean proof uses the earlier construction and its finite base
cases. The eventual $43/80+\varepsilon$ theorem alone would imply a
$3/5$ coefficient only beyond an unspecified threshold. The **finite**
$43/80$ formula gives a stronger comparison: its minimized bound is
strictly smaller than the displayed $3/5$ bound for every $K\ge11$.
Here is a direct ordinary proof of that assertion.

For $m=9,\ldots,15$, substitute the following choices into (1). Each
listed coefficient is strictly less than $3/5$.

| $m$ | $a$ | $(C(m,a)-F_3(m+2))/(m-1)!$ |
|---:|---:|---:|
| 9 | 7 | $7879/13440$ |
| 10 | 7 | $35383/60480$ |
| 11 | 8 | $29287/50400$ |
| 12 | 8 | $96109/166320$ |
| 13 | 8 | $2983/5184$ |
| 14 | 8 | $10739/18720$ |
| 15 | 8 | $541/945$ |

For every $m\ge16$, choose $a=\lfloor m/2\rfloor$. Then
$(a-2)/(m-1)\le1/2$, and the last term of (1) is at most

$$
E(m)=\frac{m(m+1)(m-a)}{(a+1)!}.
$$

Both parity subsequences of $E(m)$ decrease on this range. Indeed, for
$r\ge8$,

$$
\begin{aligned}
E(2r)&=\frac{2r^2(2r+1)}{(r+1)!},&
\frac{E(2r+2)}{E(2r)}
&=\frac{(r+1)^2(2r+3)}{r^2(2r+1)(r+2)}<1,\\
E(2r+1)&=\frac{2(2r+1)(r+1)^2}{(r+1)!},&
\frac{E(2r+3)}{E(2r+1)}
&=\frac{(2r+3)(r+2)}{(2r+1)(r+1)^2}<1.
\end{aligned}
$$

For completeness, the first ratio is at most
$(9/8)^2(19/17)/10<1$, and the second is at most
$(19/17)(10/9)/9<1$. Comparing the two initial values gives

$$
E(m)\le\max\{E(16),E(17)\}=\frac{2754}{9!}.
$$

Consequently, for all $m\ge16$,

$$
\frac{C(m,a)-F_3(m+2)}{(m-1)!}
\le\frac{43}{80}+\frac{17}{480}+\frac{2754}{9!}
=\frac{3901}{6720}
<\frac35.
$$

Together with the seven finite substitutions, this covers every $K\ge11$.
It compares the two guaranteed length bounds; it does not compare every
possible word produced by the older and newer constructions.
The $K=10$ case remains supplied by the earlier theorem, since the finite
$43/80$ family stated here begins at $K=11$.

Finally, the earlier formalized $101/120$ coefficient holds for every
$K\ge8$. It is secondary: the explicit Lean bounds at eight and nine
symbols, together with $3/5$ from ten onward, give an equal or stronger
bound throughout that range. It remains in the proof library as an already
proved consequence, not as the main upper-bound result.
