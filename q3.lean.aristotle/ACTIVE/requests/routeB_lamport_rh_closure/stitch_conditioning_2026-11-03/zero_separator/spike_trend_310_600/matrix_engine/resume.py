from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json
import trend
P=trend.O
def complete(m):
 for w in ['zeta','plant','dh']:
  try:
   a=json.loads((P/f'{w}_m{m}.json').read_text());assert (P/f'{w}_m{m}.npz').exists()
  except (OSError,ValueError,AssertionError):return False
 return True
if __name__=='__main__':
 todo=[m for m in range(310,601,10) if not complete(m)]
 print('MISSING',todo,flush=True)
 with ProcessPoolExecutor(max_workers=2) as pool:list(pool.map(trend.run,todo))
