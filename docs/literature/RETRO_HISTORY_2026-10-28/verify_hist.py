import csv,sys,glob,os,subprocess,sqlite3,collections,re
REPO='/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean'
DB=REPO+'/q3.lean.aristotle/aristotle_db/knowledge.db'
D=sys.argv[1]
con=sqlite3.connect(f'file:{DB}?mode=ro',uri=True)
def norm(s): return re.sub(r'\s+',' ',s).strip()
cache={}
def text_at(loc):
    loc=loc.strip()
    if loc in cache: return cache[loc]
    t=''
    try:
        if loc.startswith('knowledge.db:'):
            _,tab,i=loc.split(':',2)
            row=con.execute(f'select * from {tab} where id=?',(i,)).fetchone()
            t=' '.join(str(x) for x in row) if row else ''
        else:
            parts=loc.split(':')
            if re.fullmatch(r'[0-9a-f]{7,40}\^?',parts[0]) and len(parts)>=2 and parts[1]=='commit-message':
                t=subprocess.run(['git','-C',REPO,'log','-1','--format=%B',parts[0]],capture_output=True,text=True,errors='replace').stdout
            elif re.fullmatch(r'[0-9a-f]{7,40}\^?',parts[0]) and len(parts)>=2:
                t=subprocess.run(['git','-C',REPO,'show',f'{parts[0]}:{parts[1]}'],capture_output=True,text=True,errors='replace').stdout
            else:
                p=parts[0]; fp=p if p.startswith('/') else os.path.join(REPO,p)
                t=open(fp,encoding='utf-8',errors='replace').read() if os.path.isfile(fp) else ''
    except Exception as e: t=''
    cache[loc]=norm(t); return cache[loc]
rows=[];bad=[]
for f in sorted(glob.glob(f'{D}/*.tsv')):
    for r in csv.DictReader(open(f,encoding='utf-8'),delimiter='\t'):
        rows.append(r)
        q=norm(r.get('quote',''))
        ok = q and q in text_at(r.get('locator',''))
        zok = r.get('Z','').strip()!='YES' or norm(r.get('Z_quote',''))!=''
        if not ok or not zok: bad.append((r.get('id'),'quote' if not ok else 'zquote',r.get('locator','')[:80]))
print('rows',len(rows),'bad',len(bad))
for b in bad[:40]: print('  BAD',b)
c=collections.Counter(r.get('OUTCOME','').strip() for r in rows); print('OUTCOME',dict(c))
e=collections.Counter((r.get('exponent_moved','').strip(),r.get('Z','').strip()) for r in rows); print('exp x Z',dict(e))
print('\nexponent moved rows:')
for r in rows:
    if r.get('exponent_moved','').strip() in ('YES_UNCOND','YES_COND','LOG_ONLY'):
        print(f"{r['id']:16} {r['exponent_moved']:10} Z={r['Z']:7} {r['route'][:14]:14} {r['main_quantity'][:50]} | {r['summary'][:80]}")
