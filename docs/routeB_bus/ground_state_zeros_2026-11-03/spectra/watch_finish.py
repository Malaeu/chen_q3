from pathlib import Path
import time,subprocess,sys
P=Path(__file__).resolve().parent
if (P/'tail_schedule_manifest.json').exists():markers=[P/f'tail_{role}_complete.json' for role in ['even','odd','late']]
else:markers=[P/f'shard{i}_complete.json' for i in [0,1]]
while not all(p.exists() for p in markers):time.sleep(30)
r=subprocess.run([sys.executable,str(P/'finish.py')]);sys.exit(r.returncode)
