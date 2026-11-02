#!/usr/bin/env python3
"""Verify committed bytes and all archived cells without a numerical rerun."""
from pathlib import Path
import csv,gzip,hashlib,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=140
checks=0
for line in (P/'SHA256SUMS').read_text().splitlines():
    wanted,name=line.split('  ',1)
    assert hashlib.sha256((P/name).read_bytes()).hexdigest()==wanted,name
    checks+=1
manifest=json.loads((P/'NATIVE_ARCHIVE.json').read_text());chunks=[]
for part in manifest['parts']:
    b=(P/part['name']).read_bytes()
    assert len(b)==part['bytes'] and hashlib.sha256(b).hexdigest()==part['sha256']
    chunks.append(b)
b=b''.join(chunks);assert hashlib.sha256(b).hexdigest()==manifest['sha256']
raw=gzip.decompress(b);assert hashlib.sha256(raw).hexdigest()==manifest['uncompressed_sha256']
expected={r['name']:r for r in manifest['cells']};seen=set();base={}
for line in raw.splitlines():
    item=json.loads(line);name=item['name'];assert name in expected and name not in seen;seen.add(name)
    payload=item['content'].encode();record=expected[name]
    assert len(payload)==record['bytes'] and hashlib.sha256(payload).hexdigest()==record['sha256']
    d=json.loads(payload)
    if name.endswith('_dps220_gl256.json'):
        base[d['world'],d['m']]=d
        assert d['positive_pivots']+d['negative_pivots']==d['q']<=d['m']+1
        assert len(d['K'])==4 and all(mp.mpf(x)>=0 for x in d['reciprocal_proxy_squared'])
assert seen==set(expected) and len(seen)==464
assert set(base)=={(w,m) for w in ['zeta','dh'] for m in range(20,241)}
assert all(base['zeta',m]['negative_pivots']==0 for m in range(20,241))
assert min(m for w,m in base if w=='dh' and base[w,m]['negative_pivots'])==52
assert base['dh',53]['negative_pivots']==0
for name in ['curve_zeta.json','curve_dh.json','curve_refined_dh.json']:
    d=json.loads((P/name).read_text());rows=d['prefixes']
    assert all(rows[i]['negative_inertia']<=rows[i+1]['negative_inertia'] for i in range(len(rows)-1))
    if d['world']=='zeta':assert all(mp.mpf(r['Schur_pivot'])>0 and mp.mpf(r['increment'])>=0 for r in rows)
    else:assert any(mp.mpf(r['Schur_pivot'])<0 for r in rows) and any(mp.mpf(r['increment'])<0 for r in rows)
    assert mp.mpf(d['final_linear_solve_residual'])<mp.mpf('1e-70')
assert len(list(csv.DictReader((P/'source_sections.csv').open())))==442
assert len(list(csv.DictReader((P/'raw_steps.csv').open())))==440
q=json.loads((P/'IMPEDANCE_CONTROL.json').read_text())['rows']
assert all(mp.mpf(r['Q_imag'])>0 for r in q if mp.mpf(r['z_real'])==0)
assert any(r['world']=='dh' and mp.mpf(r['Q_imag'])<0 for r in q)
overlap=json.loads((P/'CONCURRENT_NUMERIC_VALIDATION.json').read_text())
assert overlap['native_inertias_compared']==442 and overlap['native_queries_compared']==1768
assert mp.mpf(overlap['max_relative_K_error'])<mp.mpf('1e-55')
print(f'PASS: {checks} committed hashes, 464 archived cells, 442 native cases, geometry and global controls')
