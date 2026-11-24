"""1回の支払いで貢献度 c を更新する計算コストを、参加者数 N を振って測る。

方式:
  dense  … 参照実装どおり、密な (I - E')^T の連立一次方程式を解く。O(N^3)・メモリ O(N^2)
  iter   … E' = E_off + diag(b)(11^T - I)/(N-1)（E_off は対角を除いた評価、b は予算）の構造を使い、
           c E' = c E_off + ((c·b) 1 - c∘b)/(N-1) を O(nnz + N) で計算するべき乗法。
           支払い直前の c から始める（warm start）。1回の支払いは E の1行の2成分しか変えない。

評価の相手は1人あたり K 人（疎）と仮定する。予算は
  normal … 一様乱数 0.2〜0.8（通常のシミュレーションの予算の平均は約0.57）
  floor  … 全員が下限 eps ちょうど（予算をぎりぎりまで使い切った最悪の場合）
dense は N=3000 まで測り、N=10000 は O(N^3) で外挿する（メモリ 800MB×数枚を避けるため）。

  uv run python scripts/bench_cost.py
"""
import time

import numpy as np
import scipy.sparse as sp

K, TOL, EPS = 50, 1e-12, 0.1
rng = np.random.default_rng(0)


def make(N, budget):
    k = min(K, N - 1)
    rows = np.repeat(np.arange(N), k)
    cols = np.empty(N * k, dtype=np.int64)
    for i in range(N):
        others = rng.choice(N - 1, size=k, replace=False)
        cols[i * k:(i + 1) * k] = others + (others >= i)
    w = rng.random(N * k)
    W = sp.csr_matrix((w, (rows, cols)), shape=(N, N))
    W = sp.diags(1 / np.asarray(W.sum(1)).ravel()) @ W  # 行和1
    b = budget(N)
    Eoff = sp.diags(1 - b) @ W  # 行和 1 - b
    return Eoff.tocsr(), b


def vcb_dense(Eoff, b):
    N = len(b)
    M = Eoff.toarray() + np.outer(b, np.ones(N)) / (N - 1)
    M[np.diag_indices(N)] = 0
    return M


def solve_dense(M):
    N = M.shape[0]
    A = (np.eye(N) - M).T
    A[-1, :] = 1
    rhs = np.zeros(N); rhs[-1] = N
    return np.linalg.solve(A, rhs)


def step(c, EoffT, b):
    N = len(b)
    return EoffT @ c + (c @ b - c * b) / (N - 1)


def solve_iter(EoffT, b, c0):
    c, it = c0.copy(), 0
    while True:
        it += 1
        c2 = step(c, EoffT, b)
        c2 *= len(b) / c2.sum()
        if np.abs(c2 - c).max() < TOL * len(b):
            return c2, it
        c = c2


def pay(Eoff, b, buyer, seller, alpha):
    """取引: 予算 b[buyer] から alpha を売り手への評価へ移す（疎行列の1成分を足す）。"""
    b = b.copy(); b[buyer] -= alpha
    Eoff = Eoff.tolil(); Eoff[buyer, seller] += alpha
    return Eoff.tocsr(), b


print(f"K={K}（1人あたりの評価相手）、収束判定 max|Δc| < {TOL}·N、floor は全員の予算 = ε = {EPS}")
print("N       方式            時間/支払い     反復   メモリ(概算)   検算 max|c_iter - c_dense|")
for N in (100, 300, 1000, 3000, 10000):
    for name, budget in (("normal", lambda n: rng.uniform(0.2, 0.8, n)), ("floor", lambda n: np.full(n, EPS + 0.01))):
        Eoff, b = make(N, budget)
        EoffT = Eoff.T.tocsr()
        c0, _ = solve_iter(EoffT, b, np.ones(N))  # 支払い前の c（定常）
        buyer, seller = 0, 1
        alpha = min(0.01, b[buyer] - EPS if name == "floor" else 0.01)
        Eoff2, b2 = pay(Eoff, b, buyer, seller, alpha)
        EoffT2 = Eoff2.T.tocsr()
        t = time.perf_counter(); c_it, it = solve_iter(EoffT2, b2, c0); t_it = time.perf_counter() - t
        mem_it = (Eoff2.data.nbytes + Eoff2.indices.nbytes + Eoff2.indptr.nbytes) * 2 / 1e6
        if N <= 3000:
            M = vcb_dense(Eoff2, b2)
            t = time.perf_counter(); c_d = solve_dense(M); t_d = time.perf_counter() - t
            err = f"{np.abs(c_it - c_d).max():.1e}"
            del M
            print(f"{N:<7} dense/{name:<9} {t_d*1e3:10.1f} ms        —   {N*N*8*2/1e6:8.0f} MB")
        else:
            err = "—"
            print(f"{N:<7} dense/{name:<9}   （外挿）{t_d*1e3*(N/3000)**3/1e3:6.1f} s         —   {N*N*8*2/1e6:8.0f} MB")
        print(f"{N:<7} iter/{name:<10} {t_it*1e3:10.2f} ms   {it:5d}   {mem_it:8.1f} MB   {err}", flush=True)
