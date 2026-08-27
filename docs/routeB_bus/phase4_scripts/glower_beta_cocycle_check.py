"""Проверка source identity вердикта: tau(k,n) = (beta_k - beta_n)/(k-n)?

Если верно, то для любых трёх индексов выполняется коцикл:
   tau(k,n)(k-n) + tau(n,m)(n-m) = tau(k,m)(k-m)
поскольку (b_k-b_n)+(b_n-b_m) = b_k-b_m. Это проверяемо без знания beta.
"""
import importlib.util, sys
from pathlib import Path
REPO = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("p1", REPO/"docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py")
p1 = importlib.util.module_from_spec(spec); sys.modules["p1"]=p1; spec.loader.exec_module(p1)
p1.ctx.dps = 60; p1.N = 40
from flint import arb
b = p1.CCMArbBuilder()

def tau(k,n): return b.tau_entry(k,n)

print("КОЦИКЛ tau(k,n)(k-n) + tau(n,m)(n-m) - tau(k,m)(k-m)  =? 0")
print(f"  {'(k,n,m)':>14}   {'невязка коцикла':>22}   {'масштаб tau':>14}")
bad = 0
for (k,n,m) in [(5,3,1),(10,7,2),(20,11,4),(31,17,5),(37,23,13),(12,9,6)]:
    lhs = tau(k,n)*(k-n) + tau(n,m)*(n-m) - tau(k,m)*(k-m)
    sc = max(abs(float(tau(k,n).mid())), abs(float(tau(k,m).mid())))
    v = abs(float(lhs.mid()))
    flag = "OK" if v < 1e-40*max(sc,1) else "НЕ НОЛЬ"
    if flag != "OK": bad += 1
    print(f"  {str((k,n,m)):>14}   {v:>22.6e}   {sc:>14.4e}  {flag}")
print()
print("ВЫВОД:", "лёвнеровская структура ПОДТВЕРЖДЕНА" if bad==0 else f"структура НЕ подтверждена ({bad} нарушений)")
if bad == 0:
    print()
    print("Извлекаю beta по beta_k = beta_1 + (k-1)*tau(k,1) при beta_1 = 0:")
    for k in (2,3,5,10,20,37):
        bk = (k-1)*float(tau(k,1).mid())
        print(f"    beta_{k:>2} = {bk:>18.10f}")
