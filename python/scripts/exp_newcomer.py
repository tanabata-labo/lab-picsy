"""新メンバーは、いつ普通のメンバー並みに買えるようになるか（D12 の予算の下限 ε の影響）。

共謀なしの経済を WARM エポック回したあと、(3.69) で1人加える。新メンバーは予算0・貢献度1で始まり、
以後は普通のメンバーと同じく買い手にも売り手にもなる。売り手としての人気は Zipf の順位で与える
（5位 = 人気、50位 = 中くらい、95位 = 不人気）。定価は既存メンバーの中央値。

測るもの（加入後の各エポック、自然回収の直後）:
  予算 E_nn、貢献度 c_n、使える購買力 (E_nn - ε) c_n、既存メンバーの使える購買力の中央値に対する比、
  新メンバーの成立した買い物の累計。

  uv run python scripts/exp_newcomer.py
"""
import copy
import warnings

import numpy as np

from picsy.core import State, contributions, initial, join, recover, transact

warnings.simplefilter("ignore", RuntimeWarning)
N, WARM, AFTER, TX, GAMMA, ZIPF, PMEAN, PSIG = 100, 100, 60, 100, 0.05, 1.0, 0.02, 0.5


def epoch(st, c, rng, pop, price, eps, watch=None):
    n = st.N
    p = pop / pop.sum()
    done = rej = 0
    for _ in range(TX):
        b = int(rng.integers(n))
        s = int(rng.choice(n, p=p))
        if b == s:
            continue
        alpha = price[s] / c[b] if c[b] > 0 else np.inf
        if not alpha <= st.E[b, b] - eps:
            rej += b == watch
            continue
        st = transact(st, b, s, alpha)
        c = contributions(st.E)
        done += b == watch
    st = recover(st, GAMMA)
    return st, contributions(st.E), done, rej


rng0 = np.random.default_rng(0)
pop0 = rng0.permutation(1.0 / np.arange(1, N + 1) ** ZIPF)
price0 = PMEAN * rng0.lognormal(-PSIG**2 / 2, PSIG, N)
st0: State = initial(N)
c0 = contributions(st0.E)
for _ in range(WARM):  # 共謀なしでは下限に当たらないので、ε によらず同じ状態になる
    st0, c0, _, _ = epoch(st0, c0, rng0, pop0, price0, 0.0)
print(f"加入前（{WARM}エポック後）: 予算の中央値 {np.median(np.diag(st0.E)):.3f}  "
      f"購買力 E_ii c_i の中央値 {np.median(np.diag(st0.E) * c0):.3f}  定価の中央値 {np.median(price0):.4f}")
print()
print("ε     人気  初回の買い物  中央値に追いつく  予算(1/2/3/10)            c(10/30/60)          使える購買力/中央値(10/30/60)  買い物の累計")

for eps in (0.0, 0.05, 0.1, 0.2):
    for rank in (5, 50, 95):
        rng = copy.deepcopy(rng0)
        st = join(st0, c0)
        c = contributions(st.E)
        pop = np.append(pop0, 1.0 / rank**ZIPF)
        price = np.append(price0, np.median(price0))
        k = N  # 新メンバーの番号
        budget, cs, ratio = [], [], []
        first = catch = None
        total = 0
        for t in range(1, AFTER + 1):
            st, c, done, rej = epoch(st, c, rng, pop, price, eps, watch=k)
            total += done
            usable = np.clip(np.diag(st.E) - eps, 0, None) * c
            r = usable[k] / np.median(usable[:k])
            budget.append(st.E[k, k]); cs.append(c[k]); ratio.append(r)
            if first is None and total > 0:
                first = t
            if catch is None and r >= 1:
                catch = t
        fmt = lambda x: "—" if x is None else f"{x}"
        print(f"{eps:<5} {rank:>3}位  {fmt(first):>6}エポック    {fmt(catch):>6}エポック     "
              f"{budget[0]:.3f}/{budget[1]:.3f}/{budget[2]:.3f}/{budget[9]:.3f}   "
              f"{cs[9]:.2f}/{cs[29]:.2f}/{cs[59]:.2f}       {ratio[9]:.2f}/{ratio[29]:.2f}/{ratio[59]:.2f}"
              f"                 {total}", flush=True)
