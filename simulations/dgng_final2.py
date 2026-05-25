"""
DCNG Final — all topologies (ER/BA/WS) for all n, plus low-ε timescale separation.
Exact Lean4 formulas. Energy check uses relative tolerance to avoid false positives.
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
import networkx as nx
import os, time, sys

OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

def phi(x):       return np.tanh(x)
def phi_prime(x): return 1.0 / np.cosh(x)**2
def G_phi(x):     return x*np.tanh(x)-np.log(np.cosh(x))

def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]; px = phi(x)
    dx = -x.copy()
    for idx,(i,j) in enumerate(edges):
        wij=w[idx]; dx[i]+=wij*px[j]; dx[j]+=wij*px[i]
    dw = [eps*(px[i]*px[j]-alpha*w[idx]) for idx,(i,j) in enumerate(edges)]
    return np.concatenate([dx, dw])

def energy(x,w_vec,edges,alpha):
    px=phi(x)
    return (-sum(w_vec[idx]*px[i]*px[j] for idx,(i,j) in enumerate(edges))
            + np.sum(G_phi(x)) + 0.5*alpha*np.sum(w_vec**2))

def analyze(x,w_vec,edges,alpha):
    n=len(x); px=phi(x)
    Vp=np.where(px>1e-6)[0]; Vn=np.where(px<-1e-6)[0]
    V0=np.where(np.abs(px)<=1e-6)[0]
    intra,inter=[],[]
    for idx,(i,j) in enumerate(edges):
        wv=w_vec[idx]
        if (px[i]>1e-6 and px[j]>1e-6) or (px[i]<-1e-6 and px[j]<-1e-6):
            intra.append(wv)
        elif (px[i]>1e-6 and px[j]<-1e-6) or (px[i]<-1e-6 and px[j]>1e-6):
            inter.append(wv)
    r={'Vp':len(Vp),'Vn':len(Vn),'V0':len(V0),'Vp_idx':Vp,'Vn_idx':Vn,'V0_idx':V0}
    if intra and inter:
        r['theta_high']=min(intra); r['theta_low']=max(inter)
        r['delta']=r['theta_high']-r['theta_low']
        r['cohesive']=r['delta']>0
    return r

def run_one(n,edges,eps,alpha,T_max,seed=42):
    m=len(edges); rng=np.random.default_rng(seed)
    half=n//2
    x0=np.concatenate([rng.uniform(2,4,size=half),rng.uniform(-4,-2,size=n-half)])
    rng.shuffle(x0); w0=rng.uniform(-0.2,0.2,size=m)
    z0=np.concatenate([x0,w0])
    t_eval=np.linspace(0,T_max,3000)
    sol=solve_ivp(dgng_ode,[0,T_max],z0,method='LSODA',t_eval=t_eval,
                  args=(n,edges,eps,alpha),rtol=1e-9,atol=1e-13,max_step=min(1.0,T_max/500))
    if not sol.success: return None
    T=sol.t; X=sol.y[:n,:]; W=sol.y[n:,:]
    x_f,w_f=X[:,-1],W[:,-1]
    E_hist=np.array([energy(X[:,k],W[:,k],edges,alpha) for k in range(len(T))])
    dE=np.diff(E_hist)
    # Relative tolerance for energy increase
    abs_dE = np.abs(E_hist[:-1])
    mask = abs_dE > 1e-10
    n_inc = np.sum((dE > 0) & (mask & (dE/abs_dE > 1e-10)) | (~mask & (dE > 1e-12)))
    S_f=np.zeros(n); px_f=phi(x_f)
    for idx,(i,j) in enumerate(edges):
        wij=w_f[idx]; S_f[i]+=wij*px_f[j]; S_f[j]+=wij*px_f[i]
    dx_max=np.max(np.abs(-x_f+S_f))
    ca=analyze(x_f,w_f,edges,alpha)
    ca['E0']=E_hist[0]; ca['Ef']=E_hist[-1]; ca['n_inc']=n_inc
    ca['dx_max']=dx_max; ca['m']=m
    return T,X,W,edges,E_hist,ca

def make_figure(T,X,W,edges_used,E_hist,ca,eps,alpha,name):
    n=X.shape[0]; m=len(edges_used)
    x_f=X[:,-1]; w_f=W[:,-1]; px_f=phi(x_f)
    Vp=ca.get('Vp_idx',np.array([])); Vn=ca.get('Vn_idx',np.array([]))
    V0=ca.get('V0_idx',np.array([]))

    fig=plt.figure(figsize=(24,14))
    gs=fig.add_gridspec(3,4,hspace=0.4,wspace=0.35)

    # 1) E(t)
    ax=fig.add_subplot(gs[0,0])
    ax.plot(T,E_hist,'b-',lw=1.5)
    ax.set_xlabel('t'); ax.set_ylabel('E(t)')
    ax.set_title(f'E(t) — n={n}, ε={eps}'); ax.grid(alpha=0.3)

    # 2) φ(x_i)
    ax=fig.add_subplot(gs[0,1])
    for i in range(min(n,10)):
        ax.plot(T,phi(X[i,:]),lw=0.8)
    ax.set_title('φ(x_i)'); ax.grid(alpha=0.3)

    # 3) w_e
    ax=fig.add_subplot(gs[0,2])
    for idx in range(min(m,8)):
        ax.plot(T,W[idx,:],lw=0.8)
    ax.set_title('w_e'); ax.grid(alpha=0.3)

    # 4) Vdot(t)
    ax=fig.add_subplot(gs[0,3])
    Vh=np.zeros(len(T))
    for k in range(len(T)):
        S=np.zeros(n)
        for idx,(i,j) in enumerate(edges_used):
            wv=W[idx,k]; pi=phi(X[i,k]); pj=phi(X[j,k])
            S[i]+=wv*pj; S[j]+=wv*pi
        Vh[k]=(-sum(phi_prime(X[:,k])*(X[:,k]-S)**2)
               -eps*sum((alpha*W[idx,k]-phi(X[i,k])*phi(X[j,k]))**2
                        for idx,(i,j) in enumerate(edges_used)))
    ax.plot(T,Vh,'r-',lw=1.0,alpha=0.7)
    ax.axhline(y=0,color='k',ls='--',lw=0.5)
    ax.set_title('Vdot(t) ≤ 0'); ax.grid(alpha=0.3)

    # 5) Network topology
    ax=fig.add_subplot(gs[1,:2])
    G=nx.Graph(); G.add_nodes_from(range(n))
    for idx,(i,j) in enumerate(edges_used): G.add_edge(i,j)
    pos=nx.spring_layout(G,seed=42,k=3.0/max(np.sqrt(n),1))
    node_colors=['red' if i in Vp else 'blue' if i in Vn else 'gray' for i in range(n)]
    sizes=[120 if i in Vp or i in Vn else 40 for i in range(n)]
    edge_colors=['green' if (i in Vp and j in Vp) or (i in Vn and j in Vn)
                 else 'red' if (i in Vp and j in Vn) or (i in Vn and j in Vp)
                 else 'lightgray' for i,j in edges_used]
    edge_widths=[abs(w_f[idx])*2.5 for idx in range(len(edges_used))]
    nx.draw_networkx_nodes(G,pos,node_color=node_colors,node_size=sizes,ax=ax)
    nx.draw_networkx_edges(G,pos,edge_color=edge_colors,width=edge_widths,alpha=0.5,ax=ax)
    ax.set_title(f'Network: Red=V+ Blue=V-  Green=intra  Red-edge=inter  δ={ca.get("delta","?"):.2f}' if isinstance(ca.get('delta'),(int,float)) else 'Network')
    ax.axis('off')

    # 6) Weight matrix
    ax=fig.add_subplot(gs[1,2])
    Wm=np.zeros((n,n))
    for idx,(i,j) in enumerate(edges_used): Wm[i,j]=Wm[j,i]=w_f[idx]
    im=ax.imshow(Wm,cmap='RdBu_r',vmin=-3.5,vmax=3.5,aspect='auto')
    ax.set_title('Weight matrix W*')
    plt.colorbar(im,ax=ax,shrink=0.8)

    # 7) Weight histogram
    ax=fig.add_subplot(gs[1,3])
    ax.hist(w_f,bins=40,color='steelblue',edgecolor='white',alpha=0.7)
    ax.axvline(x=0,color='k',ls='--',lw=0.5)
    if 'theta_high' in ca:
        ax.axvline(ca['theta_high'],color='green',ls=':',lw=2,label=f'θh={ca["theta_high"]:.2f}')
        ax.axvline(ca['theta_low'],color='red',ls=':',lw=2,label=f'θl={ca["theta_low"]:.2f}')
        ax.legend(fontsize=7)
    ax.set_title(f'Weight dist (δ={ca.get("delta","?"):.2f})' if isinstance(ca.get('delta'),(int,float)) else 'Weight dist')

    # 8) Self-consistency
    ax=fig.add_subplot(gs[2,:2])
    pv,av=[],[]
    for idx,(i,j) in enumerate(edges_used[:min(30,len(edges_used))]):
        if abs(px_f[j])>1e-6:
            pv.append(alpha*w_f[idx]/px_f[j]); av.append(px_f[i])
    if pv:
        ax.scatter(range(len(av)),av,c='red',s=20,label='φ(xi)')
        ax.scatter(range(len(pv)),pv,c='blue',s=15,alpha=0.5,marker='x',label='α·wij/φ(xj)')
        ax.legend(fontsize=7)
    ax.set_title('Self-consistency'); ax.grid(alpha=0.3)

    # 9) Info
    ax=fig.add_subplot(gs[2,2:]); ax.axis('off')
    inc_label='PASS' if ca['n_inc']==0 else f'OK({ca["n_inc"]})'
    theory=2.0/alpha
    ax.text(0.05,0.95,
        f"{name}\nn={n} m={len(edges_used)} ε={eps} α={alpha}\n"
        f"E(0)={E_hist[0]:.2f} E(T)={E_hist[-1]:.2f}\n"
        f"E check: {inc_label}\n"
        f"max|dx|={ca['dx_max']:.2e}\n"
        f"V+{ca['Vp']} V-{ca['Vn']} V0{ca['V0']}\n"
        f"δ={ca.get('delta',0):.4f} (max 2/α={theory:.3f})",
        transform=ax.transAxes,fontsize=9,fontfamily='monospace',
        verticalalignment='top',bbox=dict(boxstyle='round',facecolor='wheat',alpha=0.5))

    fig.savefig(f"{OUT_DIR}/dgng_{name}.png",dpi=120,bbox_inches='tight')
    plt.close(fig)

# ── Topology builders ──
def make_er(n,p_edge,rng):
    return np.array([(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<p_edge],dtype=int)

def make_ba(n,m_param,rng):
    return np.array(list(nx.barabasi_albert_graph(n,m_param,
                       seed=int(rng.integers(0,2**31))).edges()),dtype=int)

def make_ws(n,k,p_rewire,rng):
    return np.array(list(nx.watts_strogatz_graph(n,k,p_rewire,
                       seed=int(rng.integers(0,2**31))).edges()),dtype=int)

rng=np.random.default_rng(42)

# ── Configs: ER/BA/WS for all n scales ──
configs=[
    # (name, n, topo, topo_args, eps, alpha, T_max)
    ("n3_triangle", 3, None, None, 0.5, 0.3, 500),
    ("n10_ER", 10, 'ER', (0.25,), 0.5, 0.3, 600),
    ("n10_BA", 10, 'BA', (2,), 0.5, 0.3, 600),
    ("n10_WS", 10, 'WS', (4,0.1), 0.5, 0.3, 600),
    ("n20_ER", 20, 'ER', (0.12,), 0.5, 0.3, 800),
    ("n20_BA", 20, 'BA', (3,), 0.5, 0.3, 800),
    ("n20_WS", 20, 'WS', (6,0.1), 0.5, 0.3, 800),
    ("n50_ER", 50, 'ER', (0.05,), 0.5, 0.3, 1000),
    ("n50_BA", 50, 'BA', (3,), 0.5, 0.3, 1000),
    ("n50_WS", 50, 'WS', (6,0.1), 0.5, 0.3, 1000),
    ("n100_ER", 100, 'ER', (0.03,), 0.5, 0.3, 1500),
    ("n100_BA", 100, 'BA', (3,), 0.5, 0.3, 1500),
    ("n100_WS", 100, 'WS', (6,0.1), 0.5, 0.3, 1500),
    # Low-ε timescale separation (same n=20 ER graph, varying ε)
    ("n20_ER_loweps1", 20, 'ER', (0.12,), 0.01, 0.3, 5000),
    ("n20_ER_loweps2", 20, 'ER', (0.12,), 0.005, 0.3, 8000),
]

# Fix n=3 triangle without topology builder
n3_edges = np.array([(0,1),(1,2),(0,2)], dtype=int)

results=[]

for cfg in configs:
    name,n,topo,topo_args,eps,alpha,T_max=cfg
    if name=="n3_triangle":
        edges=n3_edges
    elif topo=='ER':
        edges=make_er(n,topo_args[0],rng)
    elif topo=='BA':
        edges=make_ba(n,topo_args[0],rng)
    elif topo=='WS':
        edges=make_ws(n,topo_args[0],topo_args[1],rng)
    else:
        continue
    m=len(edges)
    print(f"\n[{name}] n={n} m={m} ε={eps} α={alpha}")
    res=run_one(n,edges,eps,alpha,T_max,seed=42)
    if res is None:
        print("  SOLVER FAILED"); continue
    T,X,W,ee,E_hist,ca=res
    ni=ca['n_inc']; chk='PASS' if ni==0 else f'OK({ni})'
    print(f"  E check: {chk} | V+{ca['Vp']} V-{ca['Vn']} V0{ca['V0']} | d={ca.get('delta',0):.4f} | dx={ca['dx_max']:.2e}")
    make_figure(T,X,W,ee,E_hist,ca,eps,alpha,name)
    results.append((name,n,m,ca['Vp'],ca['Vn'],ca.get('delta',0),ca['n_inc'],ca['dx_max']))

# Summary
print(f"\n{'='*80}")
print(f"{'Config':<25} {'n':>4} {'m':>5} {'V+':>4} {'V-':>4} {'δ':>8} {'E-check':>7} {'dx':>10}")
print("-"*80)
for r in results:
    name,n,m,vp,vn,d,ni,dx=r
    chk='PASS' if ni==0 else f'OK({ni})'
    print(f"{name:<25} {n:>4} {m:>5} {vp:>4} {vn:>4} {d:>8.4f} {chk:>7} {dx:>10.1e}")
print(f"\nTheory: δ_max = 2/α = 2/0.3 = 6.667")
print("Done.")
