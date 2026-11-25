import sys, os, re
from collections import Counter
roots=[r for r in sys.argv[1].split(':')]
out=sys.argv[2]; start=sys.argv[3:]
imp=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)')
def header(text):
    res=[]; depth=0
    for s in text.split('\n'):
        r=''; j=0
        while j<len(s):
            if s.startswith('/-',j): depth+=1; j+=2; continue
            if s.startswith('-/',j) and depth>0: depth-=1; j+=2; continue
            if depth==0: r+=s[j]
            j+=1
        r=r.split('--')[0].strip()
        if not r or r in ('module','prelude'): continue
        m=imp.match(r)
        if m: res.append(m.group(1))
        else: break
    return res
def find(m):
    for r in roots:
        p=os.path.join(r,*m.split('.'))+'.lean'
        if os.path.exists(p): return r,p
    return None
seen={}; st=list(start)
while st:
    m=st.pop()
    if m in seen: continue
    f=find(m)
    if f is None or m.split('.')[0] in ('Mathlib','Lean','Std','Init','Batteries','Aesop'):
        seen[m]=None; continue
    deps=header(open(f[1],encoding='utf-8').read())
    seen[m]=f; st.extend(deps)
inn=sorted(k for k,v in seen.items() if v); ext=sorted(k for k,v in seen.items() if not v)
open(out+'_internal.txt','w').write('\n'.join(f'{seen[m][0]}\t{m}' for m in inn)+'\n')
open(out+'_external.txt','w').write('\n'.join(ext)+'\n')
print(len(inn),'internal', sum(os.path.getsize(seen[m][1]) for m in inn),'bytes')
print(Counter('.'.join(m.split('.')[:3]) if m.startswith('OAI') else m.split('.')[0] for m in inn).most_common(40))
print([m for m in ext if not m.startswith('Mathlib')])
