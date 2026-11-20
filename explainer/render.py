"""Render verified coordinate witnesses with Pillow and FFmpeg. Run in this folder."""
from functools import lru_cache
from itertools import combinations
import json
import math
import subprocess
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

W,H,FPS = 1280,720,24
paper = "#F6F2E8"
ink = "#172F30"
teal = "#126D66"
orange = "#BC4C28"
muted = "#526864"
pale = "#DCEBE4"
gray = "#D5D7CA"
serif = "/System/Library/Fonts/Supplemental/Georgia.ttf"
sans = "/System/Library/Fonts/Avenir Next.ttc"
@lru_cache(None)
def font(size,face):
    return ImageFont.truetype(serif if face=="serif" else sans,size,index=0 if face=="serif" else {"bold":2,"regular":7}[face])

def text(d,x,y,s,size,face="regular",color=ink,anchor="la"):
    d.text((x,y),str(s),font=font(size,face),fill=color,anchor=anchor)

def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def hull(pts):
    def half(seq):
        out=[]
        for p in seq:
            while len(out)>1 and cross(out[-2],out[-1],p)<=0:
                out.pop()
            out.append(p)
        return out[:-1]
    a=sorted(pts)
    return half(a)+half(a[::-1])

def area(p):
    return abs(sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(p,p[1:]+p[:1])))

def catalogue(pts):
    assert all(cross(*s)!=0 for s in combinations(pts,3))
    shapes={}
    for k in range(3,len(pts)+1):
        shapes[k]=[h for s in combinations(pts,k) if len(h:=hull(s))==k]
    return shapes

p12=[tuple(map(int,line.split())) for line in Path("witness12.txt").read_text().splitlines()]
p13=[[tuple(p) for p in json.loads(line)[1]] for line in Path("real13.jsonl").read_text().splitlines()]
w12=catalogue(p12)
cats=[catalogue(P) for P in p13]
assert [len(w12[i]) for i in range(3,7)]==[220,165,22,1]
assert sum(map(len,w12.values()))==408
assert len(p13)==5 and all(sum(map(len,c.values()))==570 for c in cats)
assert sorted([len(c[i]) for i in range(3,7)] for c in cats)==[[286,241,41,2]]+[[286,247,35,2]]*4
tri=hull(p13[0])
assert len(tri)==3
interior=max((p for p in p13[0] if p not in tri),key=lambda p:min(abs(cross(a,b,p)) for a,b in zip(tri,tri[1:]+tri[:1])))
cues=json.loads(Path("build/cues.json").read_text())
duration=cues[-1][3]
def transform(P,box):
    x0,y0,x1,y1=box
    xmin,xmax=min(x for x,y in P),max(x for x,y in P)
    ymin,ymax=min(y for x,y in P),max(y for x,y in P)
    z=min((x1-x0)/(xmax-xmin),(y1-y0)/(ymax-ymin))
    return lambda p:((x0+x1)/2+z*(p[0]-(xmin+xmax)/2),(y0+y1)/2-z*(p[1]-(ymin+ymax)/2))
def draw_shape(d,P,S,box,f=1,r=6,other=True,inside=None):
    proj=transform(P,box)
    xy=[proj(p) for p in S]
    d.polygon(xy,fill=pale)
    for i,(a,b) in enumerate(zip(xy,xy[1:]+xy[:1])):
        w=max(0,min(1,len(xy)*f-i))
        if w:d.line([a,(a[0]+(b[0]-a[0])*w,a[1]+(b[1]-a[1])*w)],fill=teal,width=2 if r<=4 else 4)
    chosen=set(S)
    for p in P:
        if p not in chosen and not other and p!=inside:continue
        x,y=proj(p)
        q=r if p in chosen or p==inside else max(2,r-2)
        d.ellipse((x-q,y-q,x+q,y+q),fill=orange if p==inside else teal if p in chosen else muted)
        if p==inside:d.ellipse((x-q-6,y-q-6,x+q+6,y+q+6),outline=orange,width=2)

def label(d,x,y,s):
    text(d,x,y,s,18,"bold",teal)
def section(d,t):
    text(d,65,28,"ERDŐS PROBLEM 838",18,"bold",teal)
    text(d,1215,28,"Rohan Arun   /   Super Powers AI",18,"regular",muted,"ra")
    d.line((65,70,1215,70),fill=gray,width=2)
    d.line((0,716,round(W*t/duration),716),fill=orange,width=4)
def cap(d,s):
    d.rectangle((0,590,W,715),fill=ink)
    words=s.split()
    lines=[""]
    for word in words:
        if d.textlength((lines[-1]+" "+word).strip(),font=font(29,"regular"))>1120:
            lines.append(word)
        else:lines[-1]=(lines[-1]+" "+word).strip()
    for i,line in enumerate(lines):text(d,640,652+(i-(len(lines)-1)/2)*38,line,29,"regular",paper,"mm")
def frame(t):
    j=next((j for j,c in enumerate(cues) if t<c[3]),len(cues)-1)
    scene,s,a,b=cues[j]
    tau=t-a
    f=min(1,max(0,tau)/1.4)
    im=Image.new("RGB",(W,H),paper); d=ImageDraw.Draw(im)
    section(d,t)
    if scene in (0,1):
        text(d,65,139,"How few" if scene==0 else "The corner",66,"serif")
        text(d,65,220,"polygons?" if scene==0 else "test",66,"serif")
        sub=("13 points in the plane" if scene==0 else ("Four selected · three corners" if j==3 else "Three selected · three corners"))
        text(d,68,355,sub,25,"bold",orange)
        text(d,68,404,"No three points on a line.",24,"regular",muted)
        S=tri if scene==1 else max(cats[0][5],key=area)
        draw_shape(d,p13[0],S,(615,110,1170,541),f,8,scene==0,interior if j==3 else None)
    elif scene==2:
        text(d,65,97,"The earlier minima",55,"serif")
        for i,(n,total) in enumerate([(10,189),(11,283)]):
            x=74+590*i
            label(d,x,239,f"{n} POINTS")
            text(d,x,267,total,95,"serif")
            text(d,x,398,"convex polygons",25,"regular",muted)
        d.line((630,235,630,447),fill=gray,width=2)
        text(d,70,498,"Nikol Savova  ·  September 2026",23,"regular",teal)
    elif scene==3:
        text(d,65,94,"Twelve points",51,"serif")
        label(d,69,191,"MINIMUM NUMBER OF POLYGONS")
        text(d,61,209,"408",92,"serif")
        sizes=[("Triangles",220),("Quadrilaterals",165),("Pentagons",22),("Hexagons",1)]
        idx=min(3,int(4*tau/(b-a))) if j==6 else 2
        for i,(name,n) in enumerate(sizes):
            y=351+46*i
            if i==idx:d.rounded_rectangle((67,y-3,478,y+34),radius=4,fill=pale)
            text(d,79,y,name,24,"regular");text(d,464,y,n,24,"bold",teal,"ra")
        sh=max(w12[idx+3],key=area)
        draw_shape(d,p12,sh,(579,107,1190,540),f,7)
    elif scene==4:
        text(d,65,94,"Thirteen points",51,"serif")
        text(d,1215,107,"570 polygons",38,"serif",orange,"ra")
        for i,P in enumerate(p13):
            x=67+i*233
            d.line((x,208,x+210,208),fill=gray,width=2)
            draw_shape(d,P,hull(P),(x+8,250,x+198,452),max(0,min(1,(tau-i*.10)/.8)),4)
            text(d,x+102,482,f"Type {i+1}",21,"bold",teal,"ma")
        text(d,67,541,"Rotation, reflection and relabeling preserve the count.",22,"regular",muted)
    elif scene==5:
        text(d,65,91,"How the proof works",52,"serif")
        text(d,69,239,"Enumerate possible turns",32,"bold")
        text(d,69,298,"Exclude impossible patterns",32,"bold")
        text(d,69,357,"Check integer coordinates",32,"bold")
        P=p13[0];sh=tri
        draw_shape(d,P,sh,(735,172,1165,517),f,7,False)
        pr=transform(P,(735,172,1165,517))
        for name,point in zip("ABC",sh):
            x,y=pr(point)
            text(d,x+(12 if x<950 else -22),y+(7 if y<420 else -35),name,22,"bold",orange)
    else:
        text(d,65,102,"Exact today. Open at scale.",52,"serif")
        for i,(n,v) in enumerate([(10,189),(11,283),(12,408),(13,570)]):
            x=72+i*285
            label(d,x,244,f"{n} POINTS")
            text(d,x,287,str(v),78,"serif",teal if i<2 else ink)
        text(d,70,469,"Does log f(n) / (log n)² approach a constant?",32,"regular",orange)
        text(d,71,535,"Paper and reproduction files   ·   doi.org/10.5281/zenodo.24388070",21,"regular",muted)
    cap(d,s)
    return im

if __name__=="__main__":
    output="erdos-838-explained.mp4"
    command=["ffmpeg","-loglevel","error","-y","-f","rawvideo","-pix_fmt","rgb24","-s",f"{W}x{H}","-r",str(FPS),"-i","-","-i","build/narration.wav","-c:v","libx264","-preset","fast","-crf","17","-pix_fmt","yuv420p","-c:a","aac","-b:a","160k","-movflags","+faststart","-metadata","title=How few polygons? Erdős problem 838","-metadata","artist=Rohan Arun, Super Powers AI","-shortest",output]
    proc=subprocess.Popen(command,stdin=subprocess.PIPE)
    for k in range(math.ceil(duration*FPS)):
        proc.stdin.write(frame(k/FPS).tobytes())
    proc.stdin.close()
    if proc.wait():raise RuntimeError("ffmpeg encoding failed")
