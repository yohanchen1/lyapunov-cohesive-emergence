"""
DCNG Comprehensive Simulation — large networks, multiple topologies.
Exact Lean4 formulas (LaSalle_n.lean:184-189, GraphTheory.lean:35).
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
import networkx as nx
import os, time
from collections import defaultdict

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
        wij = w[idx]
        dx[i] += wij * px[j]; dx[j] += wij * px[i]
    dw = np.array([eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)])
    return np.concatenate([dx, dw])

def energy(x, w_vec, edges, alpha):
    px = phi(x)
    E_int = -sum(w_vec[idx] * px[i] * px[j] for idx, (i, j) in enumerate(edges))
    E_pot = np.sum(G_phi(x))
    E_reg = 0.5 * alpha * np.sum(w_vec**2)
    return E_int + E_pot + E_reg

def compute_vdot(x, w_vec, edges, eps, alpha):
    n = len(x); px = phi(x)
    S = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        wij = w_vec[idx]; S[i] += wij * px[j]; S[j] += wij * px[i]
    v1 = sum(phi_prime(x[k]) * (x[k] - S[k])**2 for k in range(n))
    v2 = sum((alpha * w_vec[idx] - px[i] * px[j])**2 for idx, (i, j) in enumerate(edges))
    return -v1 - eps * v2

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
    r = {'Vp': len(Vp), 'Vn': len(Vn), 'V0': len(V0)}
    if intra and inter:
        r['theta_high'] = min(intra); r['theta_low'] = max(inter)
        r['delta'] = r['theta_high'] - r['theta_low']
        r['cohesive'] = r['delta'] > 0
    return r

def make_er(n, p_edge, rng):
    edges = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < p_edge]
    return np.array(edges, dtype=int) if edges else np.zeros((0,2), dtype=int)

def make_ba(n, m, rng):
    G = nx.barabasi_albert_graph(n, m, seed=int(rng.integers(0, 2**31)))
    edges = np.array(list(G.edges()), dtype=int)
    return edges

def make_ws(n, k, p_rewire, rng):
    G = nx.watts_strogatz_graph(n, k, p_rewire, seed=int(rng.integers(0, 2**31)))
    edges = np.array(list(G.edges()), dtype=int)
    return edges

def run_one(n, edges, eps, alpha, T_max=1000.0, label=""):
    m = len(edges); rng = np.random.default_rng(42 + hash(label) % 1000)
    half = n // 2
    x0 = np.concatenate([rng.uniform(2.0, 4.0, size=half),
                          rng.uniform(-4.0, -2.0, size=n-half)])
    rng.shuffle(x0)
    w0 = rng.uniform(-0.2, 0.2, size=m)
    z0 = np.concatenate([x0, w0])

    t_eval = np.linspace(0, T_max, 3000)
    t0 = time.time()
    sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                    args=(n, edges, eps, alpha), rtol=1e-8, atol=1e-12, max_step=1.0)
    dt = time.time() - t0
    if not sol.success: return None

    T = sol.t; X = sol.y[:n, :]; W = sol.y[n:, :]
    x_f, w_f = X[:, -1], W[:, -1]

    # Checks
    E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha) for k in range(len(T))])
    dE = np.diff(E_hist); n_inc = np.sum(dE > 1e-12)
    S_f = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        wij = w_f[idx]; S_f[i] += wij * phi(x_f[j]); S_f[j] += wij * phi(x_f[i])
    dx_max = np.max(np.abs(-x_f + S_f))
    # Convergence time: first t where max|dx| < 1e-6
    conv_t = T_max
    for k in range(len(T)):
        S_k = np.zeros(n)
        for idx, (i, j) in enumerate(edges):
            wv = W[idx, k]; S_k[i] += wv * phi(X[j, k]); S_k[j] += wv * phi(X[i, k])
        if np.max(np.abs(-X[:, k] + S_k)) < 1e-6:
            conv_t = T[k]; break

    ca = analyze(x_f, w_f, edges, alpha)
    ca['E0'] = E_hist[0]; ca['Ef'] = E_hist[-1]
    ca['n_inc'] = n_inc; ca['conv_t'] = conv_t
    ca['dx_max'] = dx_max; ca['dt'] = dt; ca['m'] = m
    return T, X, W, edges, E_hist, ca

# ── Run suite ──
configs = [
    # (name, n, topo_fn, topo_args, eps, alpha, T_max)
    ("n3_triangle", 3, None, None, 0.5, 0.3, 500),
    ("n3_path", 3, None, None, 0.5, 0.3, 500),
    ("n50_ER", 50, 'ER', (0.12,), 0.5, 0.3, 1500),
    ("n100_ER", 100, 'ER', (0.06,), 0.5, 0.3, 2000),
    ("n200_ER", 200, 'ER', (0.03,), 0.5, 0.3, 3000),
    ("n100_BA", 100, 'BA', (3,), 0.5, 0.3, 2000),
    ("n200_BA", 200, 'BA', (4,), 0.5, 0.3, 3000),
    ("n100_WS", 100, 'WS', (6, 0.1), 0.5, 0.3, 2000),
    ("n200_WS", 200, 'WS', (6, 0.1), 0.5, 0.3, 3000),
]

results = []
rng = np.random.default_rng(42)

for cfg in configs:
    name = cfg[0]; n = cfg[1]; topo_fn = cfg[2]; topo_args = cfg[3]
    eps = cfg[4]; alpha = cfg[5]; T_max = cfg[6]

    # Build edges
    if name == "n3_triangle":
        edges = np.array([(0,1), (1,2), (0,2)], dtype=int)
    elif name == "n3_path":
        edges = np.array([(0,1), (1,2)], dtype=int)
    elif topo_fn == 'ER':
        edges = make_er(n, topo_args[0], rng)
    elif topo_fn == 'BA':
        edges = make_ba(n, topo_args[0], rng)
    elif topo_fn == 'WS':
        edges = make_ws(n, topo_args[0], topo_args[1], rng)
    else:
        continue

    print(f"\n{'='*60}")
    print(f"[{name}] n={n}, m={len(edges)}, ε={eps}, α={alpha}")

    res = run_one(n, edges, eps, alpha, T_max, label=name)
    if res is None:
        print(f"  FAILED")
        continue
    T, X, W, edges_used, E_hist, ca = res
    n_inc = ca.get('n_inc', -1); d = ca.get('delta', 0)
    print(f"  E non-inc: {'PASS' if n_inc==0 else 'FAIL'} ({n_inc} inc)")
    print(f"  V+{ca['Vp']} V-{ca['Vn']} V0{ca['V0']} | δ={d:.4f} | conv_t={ca['conv_t']:.1f}s | dx_max={ca['dx_max']:.2e} | dt={ca['dt']:.0f}s")
    results.append((name, n, ca['m'], ca['Vp'], ca['Vn'], ca.get('delta',0), n_inc, ca['conv_t'], ca['dx_max']))

    # Generate figure only for representative cases
    if name in ["n3_triangle", "n100_ER", "n100_BA"] and n_inc == 0:
        fig, axes = plt.subplots(2, 3, figsize=(20, 10))
        # E(t)
        axes[0,0].plot(T, E_hist, 'b-', lw=1.2); axes[0,0].set_title(f'E(t) — {name}'); axes[0,0].grid(alpha=0.3)
        # φ(x_i)
        for i in range(min(n, 8)):
            axes[0,1].plot(T, phi(X[i,:]), lw=0.8, label=f'x_{i}')
        axes[0,1].set_title(f'φ(x_i)'); axes[0,1].grid(alpha=0.3)
        # w_e trajectories
        for idx in range(min(len(edges_used), 8)):
            axes[0,2].plot(T, W[idx,:], lw=0.8)
        axes[0,2].set_title(f'w_e'); axes[0,2].grid(alpha=0.3)
        # Network topology
        x_f, w_f = X[:, -1], W[:, -1]; px_f = phi(x_f)
        Vp_set = set(np.where(px_f > 1e-6)[0]); Vn_set = set(np.where(px_f < -1e-6)[0])
        G = nx.Graph()
        for idx, (i, j) in enumerate(edges_used): G.add_edge(i, j)
        pos = nx.spring_layout(G, seed=42, k=3.0/np.sqrt(n))
        node_colors = ['red' if i in Vp_set else 'blue' if i in Vn_set else 'gray' for i in range(n)]
        sizes = [80 if i in Vp_set or i in Vn_set else 20 for i in range(n)]
        edge_colors = ['green' if (i in Vp_set and j in Vp_set) or (i in Vn_set and j in Vn_set)
                       else 'red' if (i in Vp_set and j in Vn_set) or (i in Vn_set and j in Vp_set)
                       else 'gray' for i, j in edges_used]
        nx.draw_networkx_nodes(G, pos, node_color=node_colors, node_size=sizes, ax=axes[1,0])
        nx.draw_networkx_edges(G, pos, edge_color=edge_colors, alpha=0.4, width=0.5, ax=axes[1,0])
        axes[1,0].set_title(f'Network topology (red=V+, blue=V-, green=intra, red-edge=inter)\nδ={ca.get("delta","?"):.2f}')
        axes[1,0].axis('off')
        # Weight distribution
        axes[1,1].hist(w_f, bins=50, color='steelblue', edgecolor='white', alpha=0.7)
        if 'theta_high' in ca:
            axes[1,1].axvline(ca['theta_high'], color='green', ls=':', lw=2, label=f'θ_h={ca["theta_high"]:.2f}')
            axes[1,1].axvline(ca['theta_low'], color='red', ls=':', lw=2, label=f'θ_l={ca["theta_low"]:.2f}')
            axes[1,1].legend(fontsize=7)
        axes[1,1].set_title(f'Weight distribution')
        # Info panel
        axes[1,2].axis('off')
        axes[1,2].text(0.05, 0.95,
            f"{name}\nn={n}, m={len(edges_used)}\nε={eps}, α={alpha}\n"
            f"E(0)={E_hist[0]:.2f}, E(T)={E_hist[-1]:.2f}\n"
            f"V+{ca['Vp']} V-{ca['Vn']} V0{ca['V0']}\n"
            f"δ={ca.get('delta',0):.4f} (theory max 2/α={2/alpha:.3f})\n"
            f"conv_t={ca['conv_t']:.1f}, dx_max={ca['dx_max']:.2e}",
            transform=axes[1,2].transAxes, fontsize=9, fontfamily='monospace',
            verticalalignment='top', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
        fig.savefig(f"{OUT_DIR}/dgng_{name}.png", dpi=120, bbox_inches='tight')
        plt.close(fig)
        print(f"  Figure saved: dgng_{name}.png")

# ── Summary table ──
print(f"\n{'='*80}")
print(f"{'Config':<20} {'n':>5} {'m':>5} {'V+':>5} {'V-':>5} {'δ':>8} {'E-inc':>7} {'conv_t':>8} {'dx_max':>10}")
print("-"*80)
for r in results:
    name, n, m, vp, vn, delta, ninc, ct, dx = r
    print(f"{name:<20} {n:>5} {m:>5} {vp:>5} {vn:>5} {delta:>8.4f} {'PASS' if ninc==0 else 'FAIL':>7} {ct:>8.1f} {dx:>10.2e}")
print(f"\nTheory: δ_max = 2/α = 2/0.3 = {2/0.3:.3f}")
print("All simulations complete.")
