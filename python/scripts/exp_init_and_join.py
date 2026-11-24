"""実験1: 初期状態を変えると初日からの link farm は効かなくなるか。
実験2: 正則化モード（eta>0）で、加入（3.69）が既存メンバーの貢献度をどれだけ動かすか。"""
import sys
import warnings
from pathlib import Path

import numpy as np

from picsy.core import State, contributions, join
from picsy.sim import Config, run

warnings.simplefilter("ignore", RuntimeWarning)
OUT = Path(__file__).resolve().parents[2] / "runs" / "init_join"
EPOCHS = int(sys.argv[1]) if len(sys.argv) > 1 else 150

print("== 実験1: 初期状態 E=(1-m)I+mJ と共謀5人（初日から） ==")
print("m     eta   farm占有(10/50/最後) 成立取引/ep(最後10) ジニ(最後10)")
for m in (0.0, 0.2, 0.5, 0.9):
    for eta in (0.0, 0.05):
        r = run(Config(epochs=EPOCHS, eta=eta, link_farm=5, init_mix=m), OUT / f"init_m{m}_eta{eta}.csv")
        f = [x["farm_share"] for x in r]
        last = r[-10:]
        print(f"{m:<5} {eta:<5} {f[9]:.3f}/{f[49]:.3f}/{f[-1]:.3f}        "
              f"{np.mean([x['done'] for x in last]):6.1f}            {np.mean([x['c_gini'] for x in last]):.3f}", flush=True)

print()
print("== 実験2: 加入の前後で既存メンバーの c はどれだけ動くか ==")
print("eta   状態(エポック) max|c'_i - c_i|  新メンバーの c'  (厳密なら 0 と 1)")
for eta in (0.0, 0.01, 0.05, 0.1):
    for ep in (1, 20, 100):
        _, st = run(Config(epochs=ep, eta=eta, seed=1), return_state=True)
        c = contributions(st.E, eta)
        st2 = join(st, c)
        c2 = contributions(st2.E, eta)
        print(f"{eta:<5} {ep:<13} {np.max(np.abs(c2[:-1] - c)):.3e}        {c2[-1]:.6f}", flush=True)
