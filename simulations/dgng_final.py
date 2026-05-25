"""
DCNG Final Simulation — uniform rich figures, all topologies.
Exact Lean4 formulas (LaSalle_n.lean:184-189).
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
import networkx as nx
import os, time

OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

# ── Exact Lean4 formulas ──
def phi(x):       return np.tanh(x)
def phi_prime(x): return 1.0 / np.cosh(x)**2
def G_phi(x):     return x * np.tanh(x) - np.log(np.cosh(x))

def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]; px = phi(x)
    dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]; dx[i] += wij * px[j]; dx[j] += wij * px[i]
    dw = np.array([eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)])
    return np.concatenate([dx, dw])

def energy(x, w_vec, edges, alpha):
    px = phi(x)
    E_int = -sum(w_vec[idx] * px[i] * px[j] for idx, (i, j) in enumerate(edges))
    return E_int + np.sum(G_phi(x)) + 0.5 * alpha * np.sum(w_vec**2)

def analyze(x, w_vec, edges, alpha):
    n = len(x); px = phi(x)
    Vp = np.where(px > 1e-6)[0]; Vn = np.where(px < -1e-6)[0]
    V0 = np.where(np.abs(px) <= 1e-6)[0]
    intra, inter = [], []
    for idx, (i, j) in enumerate(edges):
        wv = w_vec[idx]
        if (px[i] > 1e-6 and px[j] > 1e-6) or (px[i] < -1e-6 and px[j] < -1e-6):
            intra.append(wv)
        elif (px[i] > 1e-6 and px[j] < -1e-6) or (px[i] < -1e-6 and px[j] > 1e-6):
            inter.append(wv)
    r = {'Vp': len(Vp), 'Vn': len(Vn), 'V0': len(V0),
         'Vp_idx': Vp, 'Vn_idx': Vn, 'V0_idx': V0}
    if intra and inter:
        r['theta_high'] = min(intra); r['theta_low'] = max(inter)
        r['delta'] = r['theta_high'] - r['theta_low']
        r['cohesive'] = r['delta'] > 0
    return r

def run_one(n, edges, eps, alpha, T_max=500.0, seed=42):
    m = len(edges); rng = np.random.default_rng(seed)
    half = n // 2
    x0 = np.concatenate([rng.uniform(2.0, 4.0, size=half),
                          rng.uniform(-4.0, -2.0, size=n-half)])
    rng.shuffle(x0)
    w0 = rng.uniform(-0.2, 0.2, size=m)
    z0 = np.concatenate([x0, w0])

    t_eval = np.linspace(0, T_max, 2000)
    t0 = time.time()
    sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                    args=(n, edges, eps, alpha), rtol=1e-10, atol=1e-14, max_step=0.5)
    dt = time.time() - t0
    if not sol.success: return None

    T = sol.t; X = sol.y[:n, :]; W = sol.y[n:, :]
    x_f, w_f = X[:, -1], W[:, -1]

    # Energy history
    E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha) for k in range(len(T))])
    dE = np.diff(E_hist); n_inc = np.sum(dE > 1e-12)

    # Convergence check
    S_f = np.zeros(n); px_f = phi(x_f)
    for idx, (i, j) in enumerate(edges):
        wij = w_f[idx]; S_f[i] += wij * px_f[j]; S_f[j] += wij * px_f[i]
    dx_max = np.max(np.abs(-x_f + S_f))

    ca = analyze(x_f, w_f, edges, alpha)
    ca['E0'] = E_hist[0]; ca['Ef'] = E_hist[-1]; ca['n_inc'] = n_inc
    ca['dx_max'] = dx_max; ca['dt'] = dt; ca['m'] = m
    return T, X, W, edges, E_hist, ca

def make_figure(T, X, W, edges, E_hist, ca, eps, alpha, name):
    n = X.shape[0]; m = len(edges)
    x_f = X[:, -1]; w_f = W[:, -1]; px_f = phi(x_f)
    Vp = ca.get('Vp_idx', np.array([])); Vn = ca.get('Vn_idx', np.array([]))
    V0 = ca.get('V0_idx', np.array([]))

    fig = plt.figure(figsize=(24, 14))
    gs = fig.add_gridspec(3, 4, hspace=0.4, wspace=0.35)

    # 1) Energy E(t)
    ax1 = fig.add_subplot(gs[0, 0])
    ax1.plot(T, E_hist, 'b-', lw=1.5)
    ax1.set_xlabel('t'); ax1.set_ylabel('E(t)')
    inc_text = 'PASS' if ca['n_inc']==0 else f'FAIL({ca["n_inc"]})'
    ax1.set_title(f'E(t) — E non-inc: {inc_text}')
    ax1.grid(alpha=0.3)

    # 2) φ(x_i) — convergence
    ax2 = fig.add_subplot(gs[0, 1])
    for i in range(min(n, 10)):
        ax2.plot(T, phi(X[i,:]), lw=0.8)
    ax2.set_xlabel('t'); ax2.set_ylabel('φ(x_i)')
    ax2.set_title(f'φ(x_i) convergence'); ax2.grid(alpha=0.3)

    # 3) Weight trajectories
    ax3 = fig.add_subplot(gs[0, 2])
    for idx in range(min(m, 10)):
        ax3.plot(T, W[idx,:], lw=0.8)
    ax3.set_xlabel('t'); ax3.set_ylabel('w_e')
    ax3.set_title(f'w_e trajectories'); ax3.grid(alpha=0.3)

    # 4) Vdot(t)
    ax4 = fig.add_subplot(gs[0, 3])
    S_hist = np.zeros((len(T), n))
    for k in range(len(T)):
        for idx, (i, j) in enumerate(edges):
            wv = W[idx,k]; px_i = phi(X[i,k]); px_j = phi(X[j,k])
            S_hist[k,i] += wv*px_j; S_hist[k,j] += wv*px_i
    V_hist = np.array([-sum(phi_prime(X[:,k])*(X[:,k]-S_hist[k])**2)
                       -eps*sum((alpha*W[idx,k]-phi(X[i,k])*phi(X[j,k]))**2
                                for idx,(i,j) in enumerate(edges))
                       for k in range(len(T))])
    ax4.plot(T, V_hist, 'r-', lw=1.0, alpha=0.7)
    ax4.axhline(y=0, color='k', ls='--', lw=0.5)
    ax4.set_xlabel('t'); ax4.set_title('Vdot(t) ≤ 0'); ax4.grid(alpha=0.3)

    # 5) Network topology — cohesive structure
    ax5 = fig.add_subplot(gs[1, :2])
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for idx, (i, j) in enumerate(edges): G.add_edge(i, j)
    pos = nx.spring_layout(G, seed=42, k=3.0/max(np.sqrt(n), 1))
    node_colors = ['red' if i in Vp else 'blue' if i in Vn else 'gray' for i in range(n)]
    sizes = [120 if i in Vp or i in Vn else 40 for i in range(n)]
    edge_colors = ['green' if (i in Vp and j in Vp) or (i in Vn and j in Vn)
                   else 'red' if (i in Vp and j in Vn) or (i in Vn and j in Vp)
                   else 'lightgray' for i, j in edges]
    edge_widths = [abs(w_f[idx])*2.5 for idx in range(len(edges))]
    nx.draw_networkx_nodes(G, pos, node_color=node_colors, node_size=sizes, ax=ax5)
    nx.draw_networkx_edges(G, pos, edge_color=edge_colors, width=edge_widths, alpha=0.5, ax=ax5)
    ax5.set_title(f'Network at t=T  Red=V+  Blue=V-  Gray=V0\n'
                  f'δ={ca["delta"]:.2f}' if 'delta' in ca else 'δ=N/A')
    ax5.axis('off')

    # 6) Weight matrix heatmap
    ax6 = fig.add_subplot(gs[1, 2])
    W_mat = np.zeros((n, n))
    for idx, (i, j) in enumerate(edges): W_mat[i, j] = W_mat[j, i] = w_f[idx]
    im = ax6.imshow(W_mat, cmap='RdBu_r', vmin=-3.5, vmax=3.5, aspect='auto')
    ax6.set_title(f'Weight matrix W*')
    plt.colorbar(im, ax=ax6, shrink=0.8)

    # 7) Weight histogram
    ax7 = fig.add_subplot(gs[1, 3])
    ax7.hist(w_f, bins=40, color='steelblue', edgecolor='white', alpha=0.7)
    ax7.axvline(x=0, color='k', ls='--', lw=0.5)
    if 'theta_high' in ca:
        ax7.axvline(x=ca['theta_high'], color='green', ls=':', lw=2, label=f'θ_h={ca["theta_high"]:.2f}')
        ax7.axvline(x=ca['theta_low'], color='red', ls=':', lw=2, label=f'θ_l={ca["theta_low"]:.2f}')
        ax7.legend(fontsize=7)
    ax7.set_xlabel('w_e'); ax7.set_title(f'Weight distribution (δ={ca.get("delta","?"):.2f})')

    # 8) Self-consistency check
    ax8 = fig.add_subplot(gs[2, :2])
    pred_vals = []
    actual_vals = []
    for idx, (i, j) in enumerate(edges[:min(30, len(edges))]):
        if abs(px_f[j]) > 1e-6:
            pred_vals.append(alpha * w_f[idx] / px_f[j])
            actual_vals.append(px_f[i])
    if pred_vals:
        ax8.scatter(range(len(actual_vals)), actual_vals, c='red', s=20, label='actual φ(xᵢ)')
        ax8.scatter(range(len(pred_vals)), pred_vals, c='blue', s=15, alpha=0.5, marker='x', label='α·wᵢⱼ/φ(xⱼ)')
        ax8.legend(fontsize=7)
    ax8.set_title('Self-consistency: φ(xᵢ) vs α·wᵢⱼ/φ(xⱼ)')
    ax8.grid(alpha=0.3)

    # 9) Info panel
    ax9 = fig.add_subplot(gs[2, 2:])
    ax9.axis('off')
    theory_max = 2.0/alpha
    inc_label = 'PASS' if ca['n_inc']==0 else f'FAIL({ca["n_inc"]})'
    ax9.text(0.05, 0.95,
        f"{name}\n"
        f"n={n}, m={len(edges)}, ε={eps}, α={alpha}\n"
        f"E(0)={E_hist[0]:.2f}, E(T)={E_hist[-1]:.2f}\n"
        f"E non-inc: {inc_label}\n"
        f"max|dx(T)|={ca['dx_max']:.2e}\n"
        f"V+={ca['Vp']}, V-={ca['Vn']}, V0={ca['V0']}\n"
        f"θ_high={ca.get('theta_high','?'):.4f}, θ_low={ca.get('theta_low','?'):.4f}\n"
        f"δ={ca.get('delta','?'):.4f} (theory max 2/α={theory_max:.3f})\n"
        f"sim time: {ca['dt']:.0f}s",
        transform=ax9.transAxes, fontsize=9, fontfamily='monospace',
        verticalalignment='top',
        bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    fname = f"{OUT_DIR}/dgng_{name}.png"
    fig.savefig(fname, dpi=120, bbox_inches='tight')
    plt.close(fig)
    print(f"  Figure: dgng_{name}.png")

# ── Configs: small fast, large scalable ──
configs = [
    ("n3_triangle", 3, np.array([(0,1),(1,2),(0,2)], dtype=int), 0.5, 0.3, 500),
    ("n10_ER", 10, 'ER', 0.5, 0.3, 600),
    ("n15_ER", 15, 'ER', 0.5, 0.3, 700),
    ("n20_ER", 20, 'ER', 0.5, 0.3, 800),
    ("n50_ER", 50, 'ER', 0.5, 0.3, 1000),
    ("n100_ER", 100, 'ER', 0.5, 0.3, 1200),
    ("n100_BA", 100, 'BA', 0.5, 0.3, 1200),
    ("n100_WS", 100, 'WS', 0.5, 0.3, 1200),
]

rng = np.random.default_rng(42)
results = []

for cfg in configs:
    name, n, topo, eps, alpha, T_max = cfg
    TOPO_LUT = {
        'ER': lambda n, rng: np.array([(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<(2.0/n)], dtype=int),
        'BA': lambda n, rng: np.array(list(nx.barabasi_albert_graph(n, 3, seed=int(rng.integers(0,2**31))).edges()), dtype=int),
        'WS': lambda n, rng: np.array(list(nx.watts_strogatz_graph(n, 6, 0.1, seed=int(rng.integers(0,2**31))).edges()), dtype=int),
    }

    if isinstance(topo, np.ndarray):
        edges = topo
    else:
        edges = TOPO_LUT[topo](n, rng)

    m = len(edges)
    print(f"\n{'='*60}")
    print(f"[{name}] n={n}, m={m}, ε={eps}, α={alpha}")

    res = run_one(n, edges, eps, alpha, T_max, seed=42)
    if res is None:
        print(f"  SOLVER FAILED")
        continue
    T, X, W, edges_used, E_hist, ca = res
    n_inc = ca.get('n_inc', -1); d = ca.get('delta', 0)
    print(f"  E non-inc: {'PASS' if n_inc==0 else f'FAIL({n_inc})'} | "
          f"V+{ca['Vp']} V-{ca['Vn']} V0{ca['V0']} | "
          f"δ={d:.4f} | dx={ca['dx_max']:.2e} | dt={ca['dt']:.0f}s")
    results.append((name, n, m, ca['Vp'], ca['Vn'], d, n_inc, ca['dx_max'], ca['dt']))

    # Generate rich figure
    make_figure(T, X, W, edges_used, E_hist, ca, eps, alpha, name)

# ── Summary ──
print(f"\n{'='*80}")
print(f"{'Config':<20} {'n':>5} {'m':>5} {'V+':>5} {'V-':>5} {'δ':>8} {'E-inc':>7} {'dx_max':>10} {'dt':>6}")
print("-"*80)
for r in results:
    print(f"{r[0]:<20} {r[1]:>5} {r[2]:>5} {r[3]:>5} {r[4]:>5} {r[5]:>8.4f} {'OK' if r[6]==0 else 'FAIL':>7} {r[7]:>10.1e} {r[8]:>5.0f}s")
print(f"\nTheory: δ_max = 2/α = 2/0.3 = {2/0.3:.3f}")
print("Done.")
