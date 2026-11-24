"""PICSY 仮想中央銀行法の参照実装。

仕様は docs/spec.md。式番号は鈴木健の博士論文（2009）第3章のもの。

行列は numpy 配列で持つ。dtype は float64（シミュレーション用）か
object に Fraction を入れたもの（厳密な性質テスト用）のどちらでもよい。
貢献度の計算だけは数の型で実装を分ける（float は LAPACK、Fraction はガウスの消去法）。

状態は不変（演算は新しい State を返す）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np
from scipy.sparse.csgraph import connected_components


class PicsyError(Exception):
    """仕様に反する操作や、定義されない状態。"""


class InvalidOperation(PicsyError):
    """前提条件を満たさない演算（D5 ほか）。"""


class NotUnique(PicsyError):
    """貢献度が一意に決まらない（閉じたクラスが複数ある。D4）。"""

    def __init__(self, classes: list[list[int]]):
        self.classes = classes
        super().__init__(f"閉じたクラスが {len(classes)} 個ある: {classes}")


@dataclass(frozen=True)
class State:
    """状態は評価行列 E と、凍結（離脱手続き中）のメンバー集合だけ。"""

    E: np.ndarray
    frozen: frozenset[int] = field(default_factory=frozenset)

    @property
    def N(self) -> int:
        return self.E.shape[0]

    @property
    def exact(self) -> bool:
        return self.E.dtype == object


# ---------------------------------------------------------------- 生成


def initial(N: int, exact: bool = False) -> State:
    """全員が予算1（E = I）の初期状態。このとき E' = J で c は全員1。"""
    if N < 3:
        raise InvalidOperation("N >= 3 が必要（spec §1）")
    if exact:
        E = np.array([[Fraction(int(i == j)) for j in range(N)] for i in range(N)], dtype=object)
    else:
        E = np.eye(N)
    return State(E)


def _one(E: np.ndarray):
    return Fraction(1) if E.dtype == object else 1.0


# ---------------------------------------------------------------- 派生量


def vcb(E: np.ndarray) -> np.ndarray:
    """E' = E - B + BD/(N-1)（論文 (3.63)）。各人の予算を自分以外へ均等に配る。"""
    N = E.shape[0]
    d = np.diag(E).copy()
    Ep = E + d[:, None] / (N - 1)
    for i in range(N):
        Ep[i, i] = 0 * _one(E)
    return Ep


def uniform_J(N: int, exact: bool = False) -> np.ndarray:
    """J = D/(N-1)。全員が自分以外の全員を均等に評価する行列。"""
    if exact:
        v = Fraction(1, N - 1)
        return np.array([[v if i != j else Fraction(0) for j in range(N)] for i in range(N)], dtype=object)
    J = np.full((N, N), 1.0 / (N - 1))
    np.fill_diagonal(J, 0.0)
    return J


def chain_matrix(E: np.ndarray, eta=0) -> np.ndarray:
    """貢献度を取る行列。eta=0 なら論文どおり E'。

    eta>0 は D4 の比較実験用の正則化（PageRank の一様ジャンプに当たる）。
    (1-eta)E' + eta*J は、状態を変えずに回収率 eta の自然回収を
    E' にだけ1回かけたものと同じ形になる（spec 性質 P4）。
    """
    M = vcb(E)
    if eta:
        M = (1 - eta) * M + eta * uniform_J(E.shape[0], E.dtype == object)
    return M


def closed_classes(M: np.ndarray) -> list[list[int]]:
    """マルコフ連鎖 M の閉じた（再帰的な）通信クラス。"""
    adj = np.asarray(M > 0, dtype=bool)
    n, labels = connected_components(adj, directed=True, connection="strong")
    classes = []
    for k in range(n):
        members = np.flatnonzero(labels == k)
        outside = np.flatnonzero(labels != k)
        if outside.size == 0 or not adj[np.ix_(members, outside)].any():
            classes.append(members.tolist())
    return classes


def contributions(E: np.ndarray, eta=0) -> np.ndarray:
    """c M = c, sum(c) = N を解く（D3）。閉じたクラスが複数なら NotUnique（D4）。

    閉じたクラスが1つだけなら、可約でも c は一意（クラス外の人は c=0）。
    """
    M = chain_matrix(E, eta)
    classes = closed_classes(M)
    if len(classes) != 1:
        raise NotUnique(classes)
    N = E.shape[0]
    # (I - M)^T c^T = 0。M は行確率なので式の和は恒等的に0、どれか1本は冗長。
    # 最後の式を sum(c) = N に置き換える。
    A = (np.eye(N) if E.dtype != object else np.array(
        [[Fraction(int(i == j)) for j in range(N)] for i in range(N)], dtype=object)) - M
    A = A.T.copy()
    rhs = [0 * _one(E)] * N
    for j in range(N):
        A[N - 1, j] = _one(E)
    rhs[N - 1] = N * _one(E)
    if E.dtype == object:
        return np.array(_solve_exact(A, rhs), dtype=object)
    return np.linalg.solve(A.astype(float), np.array(rhs, dtype=float))


def _solve_exact(A: np.ndarray, b: list) -> list:
    """Fraction のガウス＝ジョルダン消去。"""
    n = len(b)
    m = [[Fraction(A[i, j]) for j in range(n)] + [Fraction(b[i])] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if m[r][col] != 0), None)
        if piv is None:
            raise PicsyError("特異な系（一意性の判定と矛盾）")
        m[col], m[piv] = m[piv], m[col]
        p = m[col][col]
        m[col] = [x / p for x in m[col]]
        for r in range(n):
            if r != col and m[r][col] != 0:
                f = m[r][col]
                m[r] = [x - f * y for x, y in zip(m[r], m[col])]
    return [m[i][n] for i in range(n)]


def purchasing_power(E: np.ndarray, c: np.ndarray) -> np.ndarray:
    """購買力 E_bb c_b（論文 3.5.2節）。"""
    return np.diag(E) * c


# ---------------------------------------------------------------- 演算


def transact(st: State, b: int, s: int, alpha) -> State:
    """取引（論文 (3.65)(3.66)）。前提は D5: b != s, 0 < alpha <= E_bb。"""
    if b == s:
        raise InvalidOperation("自分との取引はできない")
    if b in st.frozen or s in st.frozen:
        raise InvalidOperation("凍結中のメンバーは取引できない（D9）")
    if not (0 < alpha <= st.E[b, b]):
        raise InvalidOperation(f"alpha={alpha} が予算 E_bb={st.E[b, b]} の範囲外")
    E = st.E.copy()
    E[b, b] = E[b, b] - alpha
    E[b, s] = E[b, s] + alpha
    return State(E, st.frozen)


def remaining(alpha, gammas):
    """取引の量 alpha が、その後の自然回収（回収率の列 gammas）を経て残っている量（D13）。"""
    for g in gammas:
        alpha = (1 - g) * alpha
    return alpha


def cancel(st: State, b: int, s: int, amount) -> State:
    """取引の取り消し（D13）。amount は remaining(alpha, その後の回収率の列)。

    E_bb += amount、E_bs -= amount。あいだに取引と自然回収だけが挟まっていれば、
    結果はその取引をしなかった場合の状態に一致する（Lean の cancel_exact）。
    凍結中のメンバーが関わる取引も取り消せる。除去されたメンバーが関わる取引は取り消せない。
    """
    if b == s:
        raise InvalidOperation("自分との取引は無い")
    if not 0 <= b < st.N or not 0 <= s < st.N:
        raise InvalidOperation("存在しないメンバー")
    if not (0 < amount <= st.E[b, s]):
        raise InvalidOperation(f"amount={amount} が評価 E_bs={st.E[b, s]} の範囲外")
    E = st.E.copy()
    E[b, b] = E[b, b] + amount
    E[b, s] = E[b, s] - amount
    return State(E, st.frozen)


def recover(st: State, gamma) -> State:
    """自然回収 E <- (1-gamma)E + gamma I を全員に同時に（論文 (3.67)(3.68)、D7）。

    凍結中のメンバーにもかける（D9: 中央銀行法の死亡の扱い）。
    """
    if not (0 < gamma < 1):
        raise InvalidOperation("0 < gamma < 1 が必要")
    N = st.N
    one = _one(st.E)
    E = (one - gamma) * st.E
    for i in range(N):
        E[i, i] = E[i, i] + gamma
    return State(E, st.frozen)


def join(st: State, c: np.ndarray | None = None) -> State:
    """N+1 人目の加入（論文 (3.69)）。c は加入直前の貢献度（D8。省略時は厳密モードで計算）。"""
    E0 = st.E
    N = st.N
    if c is None:
        c = contributions(E0)
    one = _one(E0)
    E = np.empty((N + 1, N + 1), dtype=E0.dtype)
    for i in range(N):
        for j in range(N):
            E[i, j] = E0[i, i] if i == j else E0[i, j] * (N - 1) / N
        E[i, N] = (one - E0[i, i]) / N
    for j in range(N):
        E[N, j] = c[j] / N
    E[N, N] = 0 * one
    return State(E, st.frozen)


def freeze(st: State, d: int) -> State:
    """離脱の第1段（D9）。以後 d は取引できないが、自然回収は続く。"""
    if not 0 <= d < st.N:
        raise InvalidOperation("存在しないメンバー")
    return State(st.E, st.frozen | {d})


def remove(st: State, d: int) -> State:
    """離脱の第2段（D9）。E_id を i 自身の予算へ戻してから d の行と列を消す。"""
    if d not in st.frozen:
        raise InvalidOperation("凍結してから除去する（D9）")
    if st.N - 1 < 3:
        raise InvalidOperation("除去後も N >= 3 が必要")
    E = st.E.copy()
    for i in range(st.N):
        if i != d:
            E[i, i] = E[i, i] + E[i, d]
    keep = [i for i in range(st.N) if i != d]
    E = E[np.ix_(keep, keep)].copy()
    frozen = frozenset(i - (i > d) for i in st.frozen if i != d)
    return State(E, frozen)


# ---------------------------------------------------------------- 検査


def invariant_errors(E: np.ndarray) -> dict:
    """I1（非負）と I2（行和1）からのずれ。厳密モードでは両方0になるはず。"""
    rows = E.sum(axis=1)
    return {
        "min_entry": min(E.flat),
        "max_rowsum_err": max(abs(r - 1) for r in rows),
    }
