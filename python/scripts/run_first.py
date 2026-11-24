"""最初の比較実験: 論文どおり（eta=0）と PageRank 型の正則化（eta>0）、通常取引と link farm。"""
import sys
import time
import warnings
warnings.simplefilter('ignore', RuntimeWarning)
from pathlib import Path

import numpy as np

from picsy.sim import Config, run

OUT = Path(__file__).resolve().parents[2] / "runs" / "first"
EPOCHS = int(sys.argv[1]) if len(sys.argv) > 1 else 150

scenarios = []
for eta in (0.0, 0.01, 0.05):
    scenarios.append((f"base_eta{eta}", Config(epochs=EPOCHS, eta=eta)))
for eta in (0.0, 0.01, 0.05):
    scenarios.append((f"farm1_eta{eta}", Config(epochs=EPOCHS, eta=eta, link_farm=5)))
for eta in (0.0, 0.05):
    scenarios.append((f"farm1late_eta{eta}", Config(epochs=EPOCHS, eta=eta, link_farm=5, farm_start=EPOCHS // 3)))
for eta in (0.0, 0.05):
    scenarios.append((f"farm2_eta{eta}", Config(epochs=EPOCHS, eta=eta, link_farm=10, farm_groups=2)))

def summary(name, r):
    last = r[-10:]
    g = lambda k, f=np.nanmean: f([x[k] for x in last])
    allr = lambda k, f: f([x[k] for x in r])
    print(f"{name:16s} done/ep={g('done'):6.1f} rej/ep={g('rejected'):5.1f} notuniq={allr('not_unique', sum):5d} "
          f"c=[{g('c_min'):.3f},{g('c_max'):.3f}] gini={g('c_gini'):.3f} farm={allr('farm_share', max):.3f}/{g('farm_share'):.3f} "
          f"pp={g('total_pp'):.3f} ratio={g('ratio_mean'):.3f}(min {allr('ratio_min', np.nanmin):.3f}) "
          f"|dcb|max={allr('dcb_absmax', np.nanmax):.2e} lam2={allr('lambda2', max):.4f} "
          f"rowerr={allr('rowsum_err', max):.1e} minE={allr('min_entry', min):.1e}", flush=True)

for name, cfg in scenarios:
    t = time.time()
    r = run(cfg, OUT / f"{name}.csv")
    summary(name, r)
print("done", file=sys.stderr)
