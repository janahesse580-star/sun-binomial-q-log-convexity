# Sun's binomial-power q-log-convexity conjecture

For integers $m\ge 2$, let

$$
R_n^{(m)}(q)=\sum_{k=0}^{n}\binom{n+k}{k}^{m}q^k,\qquad
\Delta_n^{(m)}(q)=R_{n-1}^{(m)}(q)R_{n+1}^{(m)}(q)-\bigl(R_n^{(m)}(q)\bigr)^2.
$$

The notes prove that every coefficient of $\Delta_n^{(m)}$ is nonnegative for every $n\ge1$ when $m=2$ or $3$. For every $m\ge4$ and $n\ge23$, the coefficient of $q^2$ is negative. For example,

$$
[q^2]\Delta_{23}^{(4)}(q)
=276^4+325^4-2\cdot300^4+575^4-576^4=-2\,999\,950.
$$

## 中文说明

这个仓库研究孙智伟猜想 1.1(i) 中底数为 $\binom{n+k}{k}$ 的截断多项式。对整数幂次 $m\ge2$，这族多项式恰在 $m=2,3$ 时具有 $q$-对数凸性。四次及以上有统一反例，任取 $n\ge23$，差多项式的 $q^2$ 系数为负。

- [二次的中文证明（LaTeX）](binomial-square-proof-zh.tex)
- [三次的中文证明与高次反例（LaTeX）](sun-binomial-powers-proof-zh.tex)
- [二次证明的精确核验脚本](verify_binomial_square_proof.py)
- [三次证明与四次反例的精确核验脚本](verify_sun_binomial_cubic.py)

两个核验脚本只用 Python 3 标准库。程序检查有限个多项式展开和符号证书，这些证书覆盖证明中的无界参数范围。

~~~sh
python verify_binomial_square_proof.py
python verify_sun_binomial_cubic.py
~~~

中文源码可用 XeLaTeX 或 Tectonic 编译。使用 XeLaTeX 时运行两次以解析交叉引用。

~~~sh
xelatex binomial-square-proof-zh.tex
xelatex sun-binomial-powers-proof-zh.tex
~~~

## Lean verification

项目固定使用 Lean 4.19.0 和同版本的 Mathlib。安装 Lean 后，在仓库根目录运行：

~~~sh
lake build
~~~

[SunBinomial.lean](SunBinomial.lean) 从截断二项式多项式的定义出发，给出以下经 Lean 检查的定理：

- 对所有 $m\ge4,\ n\ge23$，差多项式的 $q^2$ 系数严格为负。
- 四次在 $n=23$ 的 $q^2$ 系数精确等于 $-2\,999\,950$。
- 对 $m=2,3$ 及所有 $n\ge1$，差多项式的 $q^2$ 系数严格为正。

二次和三次的全系数 $q$-对数凸性证明见上面的中文 LaTeX。它们的完整证明尚未在 Lean 中形式化。

## Sources and attribution

- Zhi-Wei Sun formulated the all-powers statement in Conjecture 1.1(i). [Paper](https://arxiv.org/abs/2505.02767)
- Chen, Tang, Wang, and Yang proved the $q$-log-convexity of the ordinary binomial-square polynomials $\sum_k\binom nk^2q^k$. The proof for $R_n^{(2)}$ uses their theorem for low-degree coefficients. [Paper](https://arxiv.org/abs/0810.2247)
- Qiping Zhou gave the $m=5,\ n=7$ counterexample. [MathOverflow answer and discussion](https://mathoverflow.net/questions/479301/on-the-polynomials-sum-k-0n-binomnkkm-qk)
- Shivam Patel recorded the fourth-power counterexample and eventual failure for each fixed exponent $m\ge4$. The note here gives a single bound, $n\ge23$, for all such exponents. [Public proof note](https://mathdb.com/p/368293/sun-s-q-log-convexity-conjecture-for-binomial-sums-and-the-p)

The square and cubic proof notes were developed through iterative, user-directed work with Codex. The accompanying exact checks are included for independent review. Priority is not asserted.
