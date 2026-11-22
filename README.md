# Sun's binomial-power $q$-log-convexity conjecture

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24437479.svg)](https://doi.org/10.5281/zenodo.24437479)

For integers $m \ge 2$, let

$$
R_n^{(m)}(q)=\sum_{k=0}^{n}\binom{n+k}{k}^{m}q^k,\qquad
\Delta_n^{(m)}(q)=R_{n-1}^{(m)}(q)R_{n+1}^{(m)}(q)-\bigl(R_n^{(m)}(q)\bigr)^2.
$$

The second part of Zhi-Wei Sun's Conjecture 1.1(i) in [arXiv:2505.02767](https://arxiv.org/abs/2505.02767) asserts that $(R_n^{(m)}(q))_{n\ge 0}$ is $q$-log-convex for every integer $m \ge 2$.

## Result

**The conjecture holds for $m = 2$ and $m = 3$, and fails for every $m \ge 4$.**

- For $m = 2$ and $m = 3$, every coefficient of $\Delta_n^{(m)}(q)$ is nonnegative for every $n \ge 1$ (strictly positive for $1 \le d \le 2n$, and zero for $d = 0$ and $d > 2n$). The proofs are computer-assisted and backed by exact rational certificates.
- For every $m \ge 4$ and every $n \ge 23$, the coefficient of $q^2$ in $\Delta_n^{(m)}(q)$ is strictly negative. For example,

$$
[q^2]\Delta_{23}^{(4)}(q)
=276^4+325^4-2\cdot 300^4+575^4-576^4=-2\,999\,950.
$$

Earlier counterexamples are credited below: Qiping Zhou gave $m = 5,\ n = 7$ with $[q^2]\Delta_7^{(5)}(q) = -499\,140$, and Shivam Patel gave the $m = 4,\ n = 23$ counterexample and proved eventual failure for each fixed $m \ge 4$. This archive proves the uniform threshold $n \ge 23$ for all $m \ge 4$, together with complete proofs for $m = 2$ and $m = 3$.

## 中文说明

本仓库研究孙智伟猜想 1.1(i) 后半部分中底数为 $\binom{n+k}{k}$ 的截断多项式族 $(R_n^{(m)}(q))_{n\ge 0}$。对整数幂次 $m \ge 2$，该多项式族**恰在 $m = 2, 3$ 时**具有 $q$-对数凸性；对所有 $m \ge 4$ 和 $n \ge 23$，差多项式 $\Delta_n^{(m)}(q)$ 的 $q^2$ 系数严格为负。

## Files

| File | Contents |
|---|---|
| [`binomial-square-proof-zh.tex`](binomial-square-proof-zh.tex) | $m = 2$ 中文证明源码（LaTeX） |
| [`sun-binomial-powers-proof-zh.tex`](sun-binomial-powers-proof-zh.tex) | $m = 3$ 证明与所有 $m \ge 4$ 统一反例中文源码（LaTeX） |
| [`paper/binomial-square-proof-zh.pdf`](paper/binomial-square-proof-zh.pdf) | $m = 2$ 证明编译版 PDF |
| [`paper/sun-binomial-powers-proof-zh.pdf`](paper/sun-binomial-powers-proof-zh.pdf) | $m = 3$ 证明与 $m \ge 4$ 反例编译版 PDF |
| [`verify_binomial_square_proof.py`](verify_binomial_square_proof.py) | $m = 2$ 证明的精确有理数证书核验脚本 |
| [`verify_sun_binomial_cubic.py`](verify_sun_binomial_cubic.py) | $m = 3$ 证明与 $m = 4$ 反例的精确有理数核验脚本 |
| [`SunBinomial.lean`](SunBinomial.lean) | Lean 4 / Mathlib 形式化证明（$m \ge 4$ 证伪与 $q^2$ 系数定理） |
| [`SunBinomial/CubicAlgebra.lean`](SunBinomial/CubicAlgebra.lean) | Lean 4 / Mathlib 对三次证明关键代数恒等式的核验 |

## Exact Python Verification

Both scripts use only the Python 3 standard library (`fractions.Fraction`) with exact rational arithmetic and no floating-point approximation:

```sh
python verify_binomial_square_proof.py
python verify_sun_binomial_cubic.py
```

The Chinese LaTeX sources can be compiled with XeLaTeX (run twice to resolve cross-references) or Tectonic:

```sh
xelatex binomial-square-proof-zh.tex
xelatex sun-binomial-powers-proof-zh.tex
```

## Lean 4 / Mathlib Verification

The project is pinned to Lean `4.19.0` and the matching Mathlib release. With Lean installed, run:

```sh
lake build
```

- [`SunBinomial.lean`](SunBinomial.lean) proves, directly from the definition of $R_n^{(m)}(q)$, $\Delta_n^{(m)}(q)$, and $q$-log-convexity (`QLogConvex`):
  - `coeff_two_negative`: for all $m \ge 4$ and $n \ge 23$, $[q^2]\Delta_n^{(m)}(q) < 0$;
  - `not_qLogConvex`: for all $m \ge 4$, $\neg\,\mathrm{QLogConvex}(m)$ (end-to-end formal disproof of the all-$m \ge 2$ conjecture);
  - `fourth_counterexample`: $[q^2]\Delta_{23}^{(4)}(q) = -2\,999\,950$;
  - `coeff_two_positive_square_or_cube`: for $m \in \{2, 3\}$ and all $n \ge 1$, $[q^2]\Delta_n^{(m)}(q) > 0$.
- [`SunBinomial/CubicAlgebra.lean`](SunBinomial/CubicAlgebra.lean) additionally checks the cubic cancellation identity (`residual_identity`), positivity of the scaling factor (`scaling_factor_positive`), and absorption of the three negative boundary terms (`boundary_negative_terms_absorbed`).

**Scope of the formalization:** The Lean development completely formalizes the disproof for all $m \ge 4$ (`not_qLogConvex`) together with the $q^2$ coefficient positivity and selected cubic algebraic identities. The full coefficientwise positivity proofs for $m = 2, 3$ are given in the LaTeX notes and checked by the exact Python rational scripts; they are not yet fully formalized in Lean.

## Citation

If you use this archive, please cite the Zenodo concept DOI (which always resolves to the latest version):

> janahesse580-star, *Sun's binomial-power $q$-log-convexity conjecture: $m=2,3$ proofs and $m\ge 4$ counterexamples*, Zenodo, [10.5281/zenodo.24437479](https://doi.org/10.5281/zenodo.24437479).

## Sources and Attribution

- Zhi-Wei Sun formulated the all-powers statement in Conjecture 1.1(i). [arXiv:2505.02767](https://arxiv.org/abs/2505.02767)
- William Y. C. Chen, Robert L. Tang, Larry X. W. Wang, and Arthur L. B. Yang proved the $q$-log-convexity of the ordinary binomial-square polynomials $\sum_{k=0}^n \binom{n}{k}^2 q^k$. The $m = 2$ proof uses their theorem for low-degree coefficients. [arXiv:0810.2247](https://arxiv.org/abs/0810.2247)
- Qiping Zhou gave the $m = 5,\ n = 7$ counterexample ($[q^2]\Delta_7^{(5)}(q) = -499\,140$). [MathOverflow discussion](https://mathoverflow.net/questions/479301/on-the-polynomials-sum-k-0n-binomnkkm-qk)
- Shivam Patel gave the $m = 4,\ n = 23$ counterexample and proved eventual failure for each fixed $m \ge 4$. [Public proof note](https://mathdb.com/p/368293/sun-s-q-log-convexity-conjecture-for-binomial-sums-and-the-p)

The proof notes and exact checks were developed through iterative, user-directed work with AI coding assistants. All mathematical claims and certificates are provided for independent verification. Priority is not asserted.
