import sys, re, os
pats=[r'\brun_cmd\b',r'\brun_tac\b',r'\brun_meta\b',r'\brun_elab\b',r'#eval',r'#exit',r'\binitialize\b',r'\bbuiltin_init',r'\bIO\b',r'\bunsafe\b',r'\belab\b',r'\belab_rules\b',r'\bmacro\b',r'\bmacro_rules\b',r'\bsyntax\b',r'\bextern\b',r'implemented_by',r'\bcsimp\b',r'\baxiom\b',r'\bsorry\b',r'\badmit\b',r'native_decide',r'ofReduceBool',r'reduceBool',r'trustCompiler',r'\bopaque\b',r'debug\.',r'skipKernelTC',r'addDecl',r'evalConst',r'evalDecl',r'Lean\.Elab',r'Lean\.Meta',r'open Lean',r'\bsimproc\b',r'import Lean',r'by_elab',r'include_str',r'IO\.Process',r'FilePath',r'IO\.FS',r'getEnv',r'modifyEnv',r'setEnv',r'unsafeCast',r'compile_inductive',r'set_option(?!\s+(maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|linter\.|autoImplicit|relaxedAutoImplicit|pp\.|tactic\.))',r'import all',r'^\s*notation',r'^\s*infix',r'^\s*prefix\b',r'^\s*postfix']
def strip(t):
    # blank out comments, keep newlines
    out=[];depth=0;i=0;n=len(t);line=False
    while i<n:
        if line:
            if t[i]=='\n': line=False; out.append('\n')
            i+=1; continue
        if depth==0 and t.startswith('--',i): line=True; i+=2; continue
        if t.startswith('/-',i): depth+=1; i+=2; continue
        if depth>0:
            if t.startswith('-/',i): depth-=1; i+=2; continue
            if t[i]=='\n': out.append('\n')
            i+=1; continue
        out.append(t[i]); i+=1
    return ''.join(out)
bad=set(range(0x200b,0x2010))|set(range(0x202a,0x202f))|set(range(0x2060,0x2070))|{0xfeff}
hits={}
nf=0
for line in open(sys.argv[1]):
    r,m=line.rstrip('\n').split('\t')
    p=os.path.join(r,*m.split('.'))+'.lean'
    t=open(p,encoding='utf-8').read(); nf+=1
    if any(ord(c) in bad for c in t): hits.setdefault('UNICODE',[]).append((m,0,''))
    s=strip(t)
    for pat in pats:
        for mm in re.finditer(pat,s,re.M):
            ln=s.count('\n',0,mm.start())+1
            hits.setdefault(pat,[]).append((m,ln,s.split('\n')[ln-1].strip()[:140]))
print(nf,'files')
for k,v in hits.items():
    print(k,len(v),len({x[0] for x in v}))
    for x in v[:int(sys.argv[2]) if len(sys.argv)>2 else 4]: print('    ',x)
