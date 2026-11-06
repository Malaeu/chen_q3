# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Verify exact source objects and the inherited finite grid."""
import csv,hashlib,json,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[3]
def main():
    sources=json.loads((H/'SOURCES.json').read_text());loaded={}
    for row in sources:
        data=subprocess.check_output(['git','-C',str(ROOT),'show',row['commit']+':'+row['path']])
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==row['blob'];loaded[row['role']]=data
    grid=[int(r['N']) for r in csv.DictReader(loaded['core_grid'].decode().splitlines())]
    assert len(grid)==92 and grid==sorted(set(grid)) and grid[0]==3 and grid[-1]==10000
    opt=list(csv.DictReader(loaded['optimum'].decode().splitlines()))
    for N in [500,1000,2000,5000]:
        selected=[r for r in opt if int(r['N'])==N]
        assert [int(r['n']) for r in selected]==list(range(2,N+1))
        assert float(selected[0]['c_opt'])<0
    result={'source_blobs_verified':len(sources),'grid_count':len(grid),'grid_N':grid,'optimal_free_sign':'ec1e2e96 c_opt is already physical; do not negate it again','status':'PASS'}
    (H/'input_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('[##############################] 100% ETA 0s source and grid audit PASS')
if __name__=='__main__':main()
