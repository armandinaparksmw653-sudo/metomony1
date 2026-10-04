"""Logistic calibration of the LLM frame lexicon with statistics of the training partition; also on frames unseen in train. Prints a table."""
import json,math,sys
import numpy as np
from collections import Counter,defaultdict
from sklearn.linear_model import LogisticRegression
import os
KB=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','data','kb')+os.sep
MED=["LOCATION","INSTITUTE","TEAM","ARTIFACT","EVENT"]
idx=json.load(open(KB+'wimcor_frame_index.json',encoding='utf-8'))
llm={}
for l in open(os.path.join(KB,'..','..','results','colab_run3','frame_scores.jsonl'),encoding='utf-8'):
    j=json.loads(l); llm[(j['level'],j['frame'])]=j['lp']
st2=defaultdict(Counter);st1=defaultdict(Counter);glob=Counter()
for sid,(f2,f1,p,m,c) in idx.items():
    if p=='train': st2[f2][m]+=1; st1[f1][m]+=1; glob[m]+=1
gt=sum(glob.values()); prior=np.array([glob[m]/gt for m in MED])
def stat(f2,f1,loo=None):
    c=st2.get(f2)
    if c and sum(c.values())>=2: cc=Counter(c)
    elif f1 in st1: cc=Counter(st1[f1])
    else: return np.log(prior)
    if loo: cc[loo]-=1
    tot=sum(cc.values())
    return np.log(np.array([(cc[m]+0.5*prior[i])/(tot+0.5) for i,m in enumerate(MED)]))
def feats(f2,f1,loo=None):
    lp=llm.get((2,f2)) or llm.get((1,f1)) or [-1.79]*6
    return np.concatenate([lp,stat(f2,f1,loo)])
X={'train':[],'val':[],'test':[]};Y={'train':[],'val':[],'test':[]}
for sid,(f2,f1,p,m,c) in idx.items():
    if p=='train': X[p].append(feats(f2,f1,loo=m))   # leave-one-out statistics for train rows
    else: X[p].append(feats(f2,f1))
    Y[p].append(MED.index(m))
Xtr,Ytr=np.array(X['train']),np.array(Y['train'])
for name,cols in (('LLM only',slice(0,6)),('stat only',slice(6,11)),('LLM+stat',slice(0,11))):
    clf=LogisticRegression(max_iter=300,C=1.0).fit(Xtr[:,cols],Ytr)
    for p in ('val','test'):
        Xp=np.array(X[p])[:,cols];yp=np.array(Y[p]);pr=clf.predict(Xp)
        rec=[(pr[yp==k]==k).mean() for k in range(5)];pre=[(yp[pr==k]==k).mean() if (pr==k).any() else 0 for k in range(5)]
        tp=((yp!=0)&(pr!=0)).sum();fp=((yp==0)&(pr!=0)).sum();fn=((yp!=0)&(pr==0)).sum()
        print('%-10s %s acc %.3f macro-recall %.3f clash P %.3f R %.3f | recall %s'%(name,p,(pr==yp).mean(),np.mean(rec),tp/max(1,tp+fp),tp/max(1,tp+fn),' '.join('%.2f'%r for r in rec)))

print('--- frames unseen in train (L2 never seen in train, so statistics back off to one token or prior)')
seen=set(st2.keys())
sel={p:[i for i,(sid,(f2,f1,pp,m,c)) in enumerate([(s,v) for s,v in idx.items() if v[2]==p]) if f2 not in seen] for p in ('val','test')}
for name,cols in (('LLM only',slice(0,6)),('stat only',slice(6,11)),('LLM+stat',slice(0,11))):
    clf=LogisticRegression(max_iter=300,C=1.0).fit(Xtr[:,cols],Ytr)
    for p in ('test',):
        ii=sel[p];Xp=np.array(X[p])[ii][:,cols];yp=np.array(Y[p])[ii];pr=clf.predict(Xp)
        rec=[(pr[yp==k]==k).mean() if (yp==k).any() else float('nan') for k in range(5)]
        print('%-10s %s unseen-frame subset n=%d acc %.3f recall %s'%(name,p,len(ii),(pr==yp).mean(),' '.join('%.2f'%r for r in rec)))
