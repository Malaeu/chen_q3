"""Record the inputs of the zero-height scan without modifying them."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
ROOT=P.parents[2]
paths=[ROOT/f'core_m{m}_dps100_gl128.json' for m in (16,20,24)]
paths += [ROOT/'core_m24_dps140_gl160.json',P.parent/'identify.py',P.parent/'fourier_maxima.csv',
          P.parent.parent/'shape.py',P.parent.parent/'shape_results.json']
r=dict(source_commit='167dff63a632f170fed2d01d88af61268ad0af7f',status='DIAGNOSTIC_NEVER_A_PROOF',
       inputs=[dict(path=str(x.relative_to(ROOT)),sha256=hashlib.sha256(x.read_bytes()).hexdigest()) for x in paths])
(P/'source_hashes.json').write_text(json.dumps(r,indent=2)+'\n')
