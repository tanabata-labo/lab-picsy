"""n=100 程度のシミュレーション（spec §7）。

1エポック = 取引 tx_per_epoch 回のあと自然回収1回（D7 のイベント列）。
買い手は予算のある人から一様に、売り手は人気（Zipf）に比例して選ぶ。
価格は売り手ごとの定価 delta（貢献度の単位）で、alpha = delta / c_b に換算する（D6）。
alpha が予算を超える取引は拒否して数える（D5）。

link_farm > 0 のとき、先頭の link_farm 人が共謀して、毎エポックの最初に予算を全額
仲間内に払う（論文 5.1節「budget constraints があるので link farm は難しい」の検証）。
farm_groups > 1 なら共謀者を複数の組に分け、組の間では払わない。

budget_floor = eps > 0 のとき、取引は予算を eps 未満まで使えない（E_bb - alpha >= eps）。
共謀者も eps を残して払う。link farm 対策の候補（η 正則化と比べる）。

out を渡すと、1エポックごとに CSV へ1行書いて flush する（途中で止まっても残る）。
"""

from __future__ import annotations

import csv
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np

from .core import (
    InvalidOperation,
    NotUnique,
    State,
    chain_matrix,
    closed_classes,
    contributions,
    initial,
    invariant_errors,
    recover,
    transact,
    uniform_J,
)


@dataclass
class Config:
    N: int = 100
    epochs: int = 200
    tx_per_epoch: int = 100
    gamma: float = 0.05
    eta: float = 0.0  # 0 = 論文どおり（D4 strict）
    zipf: float = 1.0  # 売り手の人気の偏り
    price_mean: float = 0.02  # 定価 delta の平均（貢献度の単位）
    price_sigma: float = 0.5  # 定価の対数正規の幅
    link_farm: int = 0
    farm_groups: int = 1
    farm_start: int = 0  # このエポックから共謀を始める（それまでは普通に取引する）
    seed: int = 0
    init_mix: float = 0.0  # 初期状態 E = (1-m)I + mJ（D11 の既定は m=0、つまり E=I）
    budget_floor: float = 0.0  # 予算の下限 eps（取引で E_bb を eps 未満にしない）


def gini(x: np.ndarray) -> float:
    x = np.sort(np.clip(x, 0, None))
    n = len(x)
    if x.sum() == 0:
        return 0.0
    return float((2 * np.arange(1, n + 1) - n - 1) @ x / (n * x.sum()))


def second_eigen(M: np.ndarray) -> float:
    w = np.sort(np.abs(np.linalg.eigvals(M)))
    return float(w[-2])


def run(cfg: Config, out: Path | None = None, return_state: bool = False):
    rng = np.random.default_rng(cfg.seed)
    N = cfg.N
    st: State = initial(N)
    if cfg.init_mix:
        st = State((1 - cfg.init_mix) * st.E + cfg.init_mix * uniform_J(N))
    pop = 1.0 / np.arange(1, N + 1) ** cfg.zipf
    pop = rng.permutation(pop)
    farm = list(range(cfg.link_farm))
    groups = [farm[k:: cfg.farm_groups] for k in range(cfg.farm_groups)] if farm else []
    honest = np.array([i for i in range(N) if i not in farm])
    pop_h = pop[honest] / pop[honest].sum()
    price = cfg.price_mean * rng.lognormal(-cfg.price_sigma**2 / 2, cfg.price_sigma, N)

    eps = cfg.budget_floor
    c = contributions(st.E, cfg.eta)
    records = []
    f = w = None
    if out:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.with_suffix(".config.txt").write_text(repr(asdict(cfg)), encoding="utf-8")
        f = out.open("w", newline="", encoding="utf-8")
    for ep in range(cfg.epochs):
        acc = dict(done=0, rejected=0, ratio=[], dcb=[], not_unique=0)
        # 共謀: 予算を全額、自分の組の次の人へ
        farming = ep >= cfg.farm_start
        pool = honest if farming else np.arange(N)
        ppool = pop_h if farming else pop / pop.sum()
        for g in (groups if farming else []):
            if len(g) < 2:
                continue
            for k, b in enumerate(g):
                s = g[(k + 1) % len(g)]
                if st.E[b, b] > eps:
                    st = transact(st, b, s, st.E[b, b] - eps)
        try:
            c = contributions(st.E, cfg.eta)
        except NotUnique:
            acc["not_unique"] += 1
        for _ in range(cfg.tx_per_epoch):
            b = int(rng.choice(pool))
            s = int(rng.choice(pool, p=ppool))
            if b == s:
                continue
            alpha = price[s] / c[b] if c[b] > 0 else np.inf
            if not alpha <= st.E[b, b] - eps:
                acc["rejected"] += 1
                continue
            st2 = transact(st, b, s, alpha)
            try:
                c2 = contributions(st2.E, cfg.eta)
            except NotUnique:
                acc["not_unique"] += 1
                continue
            acc["ratio"].append((c2[s] - c[s]) / price[s])
            acc["dcb"].append(c2[b] - c[b])
            st, c = st2, c2
            acc["done"] += 1
        # 自然回収の直前に測る（最も歪んだ時点）
        inv = invariant_errors(st.E)
        M = chain_matrix(st.E, cfg.eta)
        rec = dict(
            epoch=ep,
            done=acc["done"],
            rejected=acc["rejected"],
            not_unique=acc["not_unique"],
            closed_classes=len(closed_classes(M)),
            c_min=float(c.min()),
            c_max=float(c.max()),
            c_gini=gini(c),
            farm_share=float(c[farm].sum() / N) if farm else 0.0,
            total_pp=float(np.diag(st.E) @ c),
            budget_mean=float(np.diag(st.E).mean()),
            zero_budget=int((np.diag(st.E) <= 0).sum()),
            ratio_mean=float(np.mean(acc["ratio"])) if acc["ratio"] else np.nan,
            ratio_min=float(np.min(acc["ratio"])) if acc["ratio"] else np.nan,
            dcb_absmax=float(np.max(np.abs(acc["dcb"]))) if acc["dcb"] else np.nan,
            lambda2=second_eigen(M),
            min_entry=float(inv["min_entry"]),
            rowsum_err=float(inv["max_rowsum_err"]),
        )
        records.append(rec)
        if f:
            if w is None:
                w = csv.DictWriter(f, fieldnames=list(rec))
                w.writeheader()
            w.writerow(rec)
            f.flush()
        st = recover(st, cfg.gamma)
        try:
            c = contributions(st.E, cfg.eta)
        except NotUnique:
            pass
    if f:
        f.close()
    if return_state:
        return records, st
    return records
