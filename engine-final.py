import json,os,sys,urllib.request

URL=os.environ.get("MAKEFUN_ENV_URL","")
VAL={"p":100,"n":320,"b":330,"r":500,"q":900,"k":0}
KN=(31,33,18,14,-31,-33,-18,-14)
KI=(-17,-16,-15,-1,1,15,16,17)
BI=(-17,-15,15,17)
RO=(-16,-1,1,16)
MAX=50000
INF=32000
MATE=30000
nodes=0
stopped=False
rep_hits=0
killers=[]
history=[]
PA=(0,4,9,16,27,43,68,0)
RR=(0,0,1,3,6,10,18,12)
KG=(20,16,10,4,-4,-12,-22,-32)
KE=(0,5,10,16,23,30,36,40)

def sq(s): return ord(s[0])-97+(int(s[1])-1)*16
def cs(i): return chr((i&7)+97)+str((i>>4)+1)
def pos(f):
 b=["."]*128
 for y,row in enumerate(f.split()[0].split("/")):
  x=0
  for c in row:
   if c.isdigit(): x+=int(c)
   else: b[x+(7-y)*16]=c; x+=1
 z=f.split()
 return b,1 if z[1]=="w" else -1,sum((1<<i) for i,c in enumerate("KQkq") if c in z[2]),sq(z[3]) if z[3]!="-" else -1,int(z[4]) if len(z)>4 else 0

def atk(b,t,s):
 for d in ((-15,-17) if s==1 else (15,17)):
  x=t+d
  if not x&0x88 and b[x]==("P" if s==1 else "p"): return 1
 for d in KN:
  x=t+d
  if not x&0x88 and b[x].upper()=="N" and (1 if b[x].isupper() else -1)==s: return 1
 for d in KI:
  x=t+d
  if not x&0x88 and b[x].upper()=="K" and (1 if b[x].isupper() else -1)==s: return 1
 for ds,pcs in ((BI,"BQ"),(RO,"RQ")):
  for d in ds:
   x=t+d
   while not x&0x88:
    c=b[x]
    if c!=".":
     if c.upper() in pcs and (1 if c.isupper() else -1)==s: return 1
     break
    x+=d
 return 0

def push(p,m):
 b,s,c,e,h=p
 i,j,r=m
 q=b.copy(); x=q[i]; v=q[j]; q[i]="."; q[j]=x
 ep=x.upper()=="P" and j==e and v=="." and (i&7)!=(j&7)
 if ep: q[j-16*s]="."
 if x.upper()=="K" and abs(j-i)==2:
  e=i+3 if j>i else i-4; k=i+1 if j>i else i-1
  q[k]=q[e]; q[e]="."
 if r: q[j]=r.upper() if s==1 else r
 if x.upper()=="K": c &= ~(3 if s==1 else 12)
 for home,bit in ((0,2),(7,1),(112,8),(119,4)):
  if i==home or j==home: c &= ~bit
 e=i+16*s if x.upper()=="P" and abs(j-i)==32 else -1
 h=0 if x.upper()=="P" or v!="." or ep else h+1
 return q,-s,c,e,h

def pseudo(p):
 b,s,c,e,h=p
 for i in range(128):
  if i&0x88: continue
  x=b[i]
  if x=="." or (1 if x.isupper() else -1)!=s: continue
  typ=x.upper()
  if typ=="P":
   d=16*s; j=i+d
   if not j&0x88 and b[j]==".":
    for r in ("qrbn" if j>>4 in (0,7) else ("",)):
     yield i,j,r
    if i>>4==(1 if s==1 else 6):
     k=j+d
     if b[k]==".": yield i,k,""
   for d in (d-1,d+1):
    j=i+d
    if not j&0x88 and ((b[j]!="." and b[j].upper()!="K" and (1 if b[j].isupper() else -1)==-s) or j==e):
     for r in ("qrbn" if j>>4 in (0,7) else ("",)):
      yield i,j,r
  else:
   ds=KN if typ=="N" else KI if typ=="K" else BI if typ=="B" else RO if typ=="R" else BI+RO
   for d in ds:
    j=i+d
    while not j&0x88:
     y=b[j]
     if y==".":
      yield i,j,""
     else:
      if y.upper()!="K" and (1 if y.isupper() else -1)==-s: yield i,j,""
      break
     if typ in "NK": break
     j+=d
 if s==1 and b[4]=="K" and not atk(b,4,-1):
  if c&1 and b[7]=="R" and b[5]==b[6]=="." and not atk(b,5,-1) and not atk(b,6,-1): yield 4,6,""
  if c&2 and b[0]=="R" and b[1]==b[2]==b[3]=="." and not atk(b,3,-1) and not atk(b,2,-1): yield 4,2,""
 if s==-1 and b[116]=="k" and not atk(b,116,1):
  if c&4 and b[119]=="r" and b[117]==b[118]=="." and not atk(b,117,1) and not atk(b,118,1): yield 116,118,""
  if c&8 and b[112]=="r" and b[113]==b[114]==b[115]=="." and not atk(b,115,1) and not atk(b,114,1): yield 116,114,""

def legal(p):
 b,s=p[:2]; out=[]; k="K" if s==1 else "k"; z=b.index(k)
 for m in pseudo(p):
  q=push(p,m)[0]
  if not atk(q,m[1] if b[m[0]]==k else z,-s): out.append(m)
 return out

def enc(m): return cs(m[0])+cs(m[1])+m[2]
def dec(x): return sq(x[:2]),sq(x[2:4]),x[4:].lower()
def order(p,ms,pv=None,ply=0):
 b,s,c,e=p[:4]
 def key(m):
  if m==pv: return -10000000,""
  x=b[m[0]]; y=b[m[1]]
  if y=="." and x.upper()=="P" and m[1]==e and (m[0]&7)!=(m[1]&7): y="p"
  if y!=".": v=10000+VAL[y.lower()]*10-VAL[x.lower()]+(VAL[m[2]]*8 if m[2] else 0)
  elif m[2]: v=9000+VAL[m[2]]*8
  else: v=(killers[ply].get(m,0) if ply<len(killers) else 0)+history[s== -1][m[0]*128+m[1]]
  return -v,enc(m)
 return sorted(ms,key=key)

def ev(p):
 b,s=p[:2]; score=0
 pawns=[[],[]]; files=[set(),set()];  bishops=[0,0]; knights=[0,0]; major=[0,0]
 for j,x in enumerate(b):
  if j&0x88 or x==".": continue
  c=0 if x.isupper() else 1
  if x.upper()=="P":
   files[c].add(j&7); pawns[c].append((j&7,j>>4))
  elif x.upper()=="B": bishops[c]+=1
  elif x.upper()=="N": knights[c]+=1
  elif x.upper() in "RQ": major[c]+=1
 phase=sum(4 if x.upper()=="Q" else 2 if x.upper()=="R" else 1 for i,x in enumerate(b) if not i&0x88 and x.upper() in "NBQR")
 for i in range(128):
  if i&0x88: continue
  x=b[i]
  if x==".": continue
  side=1 if x.isupper() else -1; ci=0 if side==1 else 1
  t=x.upper(); f=i&7; r=i>>4
  center=6-abs(3-f)-abs(3-r); adv=r if side==1 else 7-r
  v=VAL[t.lower()]
  if t=="P":
   v+=PA[adv]+center*2
   if sum(g==f for g,z in pawns[ci])>1 and not any(g==f and (z<r if side==1 else z>r) for g,z in pawns[ci]): v-=10
  elif t=="N": v+=center*10
  elif t=="B": v+=center*5
  elif t=="R":
   own=f in files[ci]; enemy=f in files[1-ci]
   v+=RR[adv]+(14 if not own else 0)+(8 if not enemy else 0)
   if adv==6: v+=16
  elif t=="Q": v+=center*3
  elif t=="K":
   v+=(KG[adv]*phase+KE[adv]*(24-phase))//24+center*(9 if phase<5 else -12)
   if phase>5:
    if f in (2,6): v+=18
    if r in (0,7): v+=12
  score+=side*v
 for ci in (0,1):
  if bishops[ci]>=2: score+=(30 if ci==0 else -30)
 for side,ps in ((1,pawns[0]),(-1,pawns[1])):
  ci=0 if side==1 else 1
  enemy=pawns[1-ci]
  for f,r in ps:
   if not any(abs(g-f)==1 for g,z in ps): score-=side*10
   blocker=any(abs(g-f)<=1 and (z>r if side==1 else z<r) for g,z in enemy)
   if not blocker:
    adv=r if side==1 else 7-r
    score+=side*(30+adv*adv*3)
 # Mobility and king shelter/attack pressure.
 for side in (1,-1):
  ci=0 if side==1 else 1
  moves=0
  for i,_,_ in pseudo((b,side,0,-1,0)):
   if i&128==128: continue
   if b[i]!="." and b[i].upper() in "NBRQ" and (1 if b[i].isupper() else -1)==side: moves+=1
  score+=side*min(moves,40)*2
  k=b.index("K" if side==1 else "k")
  kf=k&7; kr=k>>4
  shield=0
  for df in (-1,0,1):
   f=kf+df
   if 0<=f<8:
    for dr in (1,2) if side==1 else (-1,-2):
     j=f+(kr+dr)*16
     if not j&0x88 and b[j]==("P" if side==1 else "p"): shield+=1
  score+=side*shield*8
  danger=sum(not (j:=k+d)&0x88 and atk(b,j,-side) for d in KI)
  score-=side*danger*(8 if phase>=6 else 3)
 # Material-impoverished positions are terminal draws.
 if not any(pawns) and not sum(major) and sum(bishops+knights)<2: return 0
 return score*s

def qs(p,a,b,ply,left):
 global nodes,stopped
 nodes+=1
 if nodes>=MAX: stopped=True; return 0
 board,s,_,e,h=p; checked=atk(board,board.index("K" if s==1 else "k"),-s)
 if h>=100: return -MATE+ply if checked and not legal(p) else 0
 stand=ev(p)
 if not checked:
  if stand>=b: return b if legal(p) else 0
  a=max(a,stand)
  if left<=0: return stand if legal(p) else 0
 ms=legal(p)
 if not ms: return -MATE+ply if checked else 0
 if not checked:
  ms=[m for m in ms if board[m[1]]!="." or (board[m[0]].upper()=="P" and m[1]==e) or m[2]]
  if not ms: return a
 elif left < -3: return max(-ev(push(p,m)) for m in ms)
 for m in order(p,ms,None,ply):
  v=-qs(push(p,m),-b,-a,ply+1,left-1)
  if stopped: return 0
  if v>=b: return b
  a=max(a,v)
 return a

def ttscore(v,ply,load=0):
 if abs(v)>MATE-1000: v+=(1-2*load)*ply*(1 if v>0 else -1)
 return v

def search(p,d,a,b,ply,tt,path):
 global nodes,stopped,rep_hits
 nodes+=1
 if nodes>=MAX: stopped=True; return 0
 board,s,c,e,h=p; checked=atk(board,board.index("K" if s==1 else "k"),-s)
 if h>=100: return -MATE+ply if checked and not legal(p) else 0
 ms=legal(p)
 if not ms: return -MATE+ply if checked else 0
 rep=(tuple(board),s,c,e)
 if path.get(rep,0)>=2: rep_hits+=1; return 0
 path[rep]=path.get(rep,0)+1
 old_rep_hits=rep_hits
 try:
  if d<=0: return qs(p,a,b,ply,5)
  key=(rep,min(h,100)); oa=a; ent=tt.get(key); pv=None
  if ent:
   od,flag,v,pv=ent; v=ttscore(v,ply,1)
   if od>=d and (flag==0 or flag==1 and v>=b or flag==-1 and v<=a): return v
  if d>=3 and not checked and h<90 and b<MATE-1000 and any(x!="." and x.upper() in "RQ" and (1 if x.isupper() else -1)==s for x in board):
   v=-search((board,-s,c,-1,h+1),d-3,-b,-b+1,ply+1,tt,{})
   if stopped: return 0
   if v>=b: return v
  best=-INF; bm=None
  for n,m in enumerate(order(p,ms,pv,ply)):
   if n==0: v=-search(push(p,m),d-1,-b,-a,ply+1,tt,path)
   else:
    v=-search(push(p,m),d-1,-a-1,-a,ply+1,tt,path)
    if not stopped and a<v<b: v=-search(push(p,m),d-1,-b,-a,ply+1,tt,path)
   if stopped: return 0
   if v>best: best,bm=v,m
   a=max(a,v)
   if a>=b:
    if board[m[1]]=="." and not m[2] and not (board[m[0]].upper()=="P" and m[1]==e and (m[0]&7)!=(m[1]&7)):
     if ply<len(killers):
      if m not in killers[ply]: killers[ply]={m:9000,**killers[ply]}
      if len(killers[ply])>2: killers[ply].pop(next(reversed(killers[ply])))
     z=m[0]*128+m[1]; hst=history[s==-1]; hst[z]=min(20000,hst[z]+d*d)
    break
  flag=-1 if best<=oa else 1 if best>=b else 0
  if rep_hits==old_rep_hits and (len(tt)<16000 or key in tt): tt[key]=(d,flag,ttscore(best,ply),bm)
  return best
 finally:
  path[rep]-=1
  if not path[rep]: del path[rep]

def choose(fen,root):
 global nodes,stopped,rep_hits,killers,history
 p=pos(fen); ms=[dec(x) for x in root]
 if not ms: return ""
 if len(ms)==1: return enc(ms[0])
 best=ms[0]; nodes=0; stopped=False; rep_hits=0; tt={}; killers=[{} for _ in range(128)]; history=[[0]*16384 for _ in range(2)]
 board,s,c,e=p[:4]; path={(tuple(board),s,c,e):1}
 for d in range(1,32):
  a=-INF; pick=best; bv=-INF; complete=True
  for n,m in enumerate(order(p,ms,best,0)):
   if nodes>=MAX: complete=False; break
   child=push(p,m)
   if n==0: v=-search(child,d-1,-INF,-a,1,tt,path)
   else:
    v=-search(child,d-1,-a-1,-a,1,tt,path)
    if not stopped and a<v<INF: v=-search(child,d-1,-INF,-a,1,tt,path)
   if stopped: complete=False; break
   if v>bv: bv,pick=v,m
   a=max(a,v)
  if not complete: break
  best=pick
  if abs(bv)>=MATE-100: break
 return enc(best)

def post(path,body):
 req=urllib.request.Request(URL+path,data=json.dumps(body).encode(),headers={"content-type":"application/json"})
 with urllib.request.urlopen(req) as r: return json.load(r)

def main():
 if not URL: sys.exit("MAKEFUN_ENV_URL is not set")
 g=post("/game",{})
 while g["status"]!="done":
  while g["status"]=="your_move":
   g=post("/move",{"game":g["game"],"move":choose(g["fen"],g["legal_moves"])})
  if g["status"]!="done":
   g=post("/game",{})

if __name__=="__main__": main()
