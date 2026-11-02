"""Three fixed-vector precision controls; no eigenproblem."""
from pathlib import Path
import sys
import rellich as r
r.IN=Path(sys.argv[1]);r.mp.mp.dps=140
for name in ['ledger_zeta_m55_q27.json','zeta_cell_m240_dps120_gl192.json','dh_cell_m240_native_dps120_gl192.json']:
 r.run(r.IN/name,256)
