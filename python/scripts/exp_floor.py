"""η 正則化と予算の下限 ε を、同じ共謀シナリオで比べる。

観点は3つ:
  1. 共謀者の占有（farm_share）と経済が回るか（成立取引・拒否）
  2. 加入のずれ（(3.69) の加入で既存メンバーの c がどれだけ動くか）
  3. 定価の近似（売り手の c の増分 / delta）

メモリと実行時間を抑えるため、1回の起動で1グループだけ回す:
  uv run python scripts/exp_floor.py farm   # 共謀5人・初日から
  uv run python scripts/exp_floor.py late   # 共謀5人・50エポック目から
  uv run python scripts/exp_floor.py two    # 共謀2組
  uv run python scripts/exp_floor.py base   # 共謀なし（ε の副作用）
  uv run python scripts/exp_floor.py join   # 加入のずれ
各エポックの記録は runs/floor/*.csv に逐次書き出す。
"""
import sys
import warnings
from pathlib import Path

import numpy as np

from picsy.core import contributions, join
from picsy.sim import Config, run

warnings.simplefilter("ignore", RuntimeWarning)
OUT = Path(__file__).resolve().parents[2] / "runs" / "floor"
group = sys.argv[1]
EPOCHS = int(sys.argv[2]) if len(sys.argv) > 2 else 150

# (eta, eps) の組
ARMS = [(0.0, 0.0), (0.05, 0.0), (0.0, 0.02), (0.0, 0.05), (0.0, 0.1), (0.0, 0.2)]


def summary(name, r):
    last = r[-10:]
    f = [x["farm_share"] for x in r]
    m = lambda k: np.nanmean([x[k] for x in last])
    print(f"{name:<22} 占有 {f[min(9, len(f)-1)]:.3f}/{f[min(49, len(f)-1)]:.3f}/{m('farm_share'):.3f}"
          f"  成立 {m('done'):5.1f}  拒否 {m('rejected'):5.1f}  一意性エラー {sum(x['not_unique'] for x in r):5d}"
          f"  c {m('c_min'):.2f}〜{m('c_max'):.2f}  ジニ {m('c_gini'):.2f}  購買力 {m('total_pp'):5.1f}"
          f"  Δc_s/δ {m('ratio_mean'):.3f}  予算平均 {m('budget_mean'):.3f}", flush=True)


def arm_name(eta, eps):
    return f"eta{eta}_eps{eps}"


if group in ("farm", "late", "two", "base"):
    kw = dict(farm=dict(link_farm=5), late=dict(link_farm=5, farm_start=50),
              two=dict(link_farm=10, farm_groups=2), base=dict())[group]
    print(f"== {group}: {kw}  {EPOCHS}エポック ==")
    for eta, eps in ARMS:
        r = run(Config(epochs=EPOCHS, eta=eta, budget_floor=eps, **kw), OUT / f"{group}_{arm_name(eta, eps)}.csv")
        summary(f"eta={eta} eps={eps}", r)

elif group == "join":
    print("== 加入のずれ: max|c'_i - c_i|（既存メンバー）と新メンバーの c'（厳密なら 0 と 1） ==")
    for eta, eps in [(0.0, 0.0), (0.01, 0.0), (0.05, 0.0), (0.1, 0.0), (0.0, 0.05), (0.0, 0.1)]:
        for ep in (1, 20, 100):
            _, st = run(Config(epochs=ep, eta=eta, budget_floor=eps, seed=1), return_state=True)
            c = contributions(st.E, eta)
            c2 = contributions(join(st, c).E, eta)
            print(f"eta={eta:<5} eps={eps:<5} {ep:>4}エポック後  {np.max(np.abs(c2[:-1] - c)):.3e}  {c2[-1]:.6f}", flush=True)
else:
    sys.exit(f"unknown group: {group}")
