"""
Graph-theoretic analysis of DCNG equilibrium: k-plex, structural balance, spectral comparison.
Generates analysis figures for Section 5 (Numerical Verification) additions.
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
import networkx as nx
import os

OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif", "font.serif": ["Times New Roman", "DejaVu Serif"],
    "font.size": 10, "axes.titlesize": 12, "axes.titleweight": "bold",
    "axes.labelsize": 10, "figure.dpi": 300, "savefig.dpi": 300,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.08,
})
C_TEAL = "#264653"; C_GREEN = "#2A9D8F"; C_ORANGE = "#F4A261"; C_CORAL = "#E76F51"
C_BLUE = "#2878B5"; C_RED = "#C82423"; C_GRAY = "#9E9E9E"

def phi(x): return np.tanh(x)

def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]; px = phi(x); dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]; dx[i] += wij * px[j]; dx[j] += wij * px[i]
    dw = [eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)]
    return np.concatenate([dx, dw])

def run_one(n, edges, eps, alpha, T_max, seed=42):
    m = len(edges); rng = np.random.default_rng(seed)
    half = n // 2
    x0 = np.concatenate([rng.uniform(2, 4, size=half), rng.uniform(-4, -2, size=n - half)])
    rng.shuffle(x0); w0 = rng.uniform(-0.2, 0.2, size=m)
    z0 = np.concatenate([x0, w0])
    sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA',
                    args=(n, edges, eps, alpha), rtol=1e-8, atol=1e-12)
    if not sol.success: return None
    return sol.y[:n, -1], sol.y[n:, -1]

rng_np = np.random.default_rng(42)

def make_er(n, p_edge):
    return np.array([(i, j) for i in range(n) for j in range(i + 1, n)
                     if rng_np.random() < p_edge], dtype=int)

def make_ba(n, m_param):
    return np.array(list(nx.barabasi_albert_graph(n, m_param,
        seed=int(rng_np.integers(0, 2**31))).edges()), dtype=int)

def make_ws(n, k, p_rewire):
    return np.array(list(nx.watts_strogatz_graph(n, k, p_rewire,
        seed=int(rng_np.integers(0, 2**31))).edges()), dtype=int)

# ====== k-plex parameter estimation ======
def compute_kplex_params(x_f, edges, ca):
    """Compute k-plex parameter k for V+ and V- subgraphs."""
    Vp = set(ca['Vp_idx']); Vn = set(ca['Vn_idx'])
    results = {}
    for label, Vset in [('V+', Vp), ('V-', Vn)]:
        if len(Vset) < 2:
            results[label] = None; continue
        sub_nodes = list(Vset)
        # Build induced subgraph and compute degrees
        sub_deg = {v: 0 for v in sub_nodes}
        for idx, (i, j) in enumerate(edges):
            if i in Vset and j in Vset:
                sub_deg[i] = sub_deg.get(i, 0) + 1
                sub_deg[j] = sub_deg.get(j, 0) + 1
        min_deg = min(sub_deg.values()) if sub_deg else 0
        k_val = len(Vset) - min_deg
        density = sum(sub_deg.values()) / (len(Vset) * (len(Vset) - 1)) if len(Vset) > 1 else 0
        results[label] = {'k': k_val, 'size': len(Vset), 'min_deg': min_deg, 'density': density}
    return results

# ====== Structural balance analysis ======
def compute_balance(G, edges_used, w_f):
    """Compute proportion of balanced triangles (product of 3 edge signs > 0)."""
    # Build edge sign dictionary
    edge_sign = {}
    for idx, (i, j) in enumerate(edges_used):
        edge_sign[(i, j)] = np.sign(w_f[idx])
        edge_sign[(j, i)] = np.sign(w_f[idx])

    # Find all triangles
    triangles = []
    for u, v in edges_used:
        common = set(G.neighbors(u)) & set(G.neighbors(v))
        for w in common:
            if w > u and w > v:  # ensure each triangle counted once
                triangles.append((u, v, w))

    if not triangles: return 0, 0
    balanced = 0
    for u, v, w_node in triangles:
        s1 = edge_sign.get((u, v), 0)
        s2 = edge_sign.get((v, w_node), 0)
        s3 = edge_sign.get((w_node, u), 0)
        if s1 * s2 * s3 > 0:  # balanced (positive product)
            balanced += 1
    return balanced, len(triangles)

# ====== Spectral comparison ======
def spectral_comparison(G, ca, w_f, edges_used):
    """Compare DCNG partition with spectral clustering eigenvector sign."""
    L = nx.laplacian_matrix(G).toarray()
    eigvals, eigvecs = np.linalg.eigh(L)
    fiedler = eigvecs[:, 1]  # second eigenvector (Fiedler vector)
    # DCNG partition signs
    dgng_sign = np.zeros(G.number_of_nodes())
    for i in ca['Vp_idx']: dgng_sign[i] = 1
    for i in ca['Vn_idx']: dgng_sign[i] = -1
    # Agreement
    mask = np.abs(dgng_sign) > 0  # exclude V0
    if mask.sum() < 2: return 0
    agreement = np.mean(np.sign(fiedler[mask]) == np.sign(dgng_sign[mask]))
    return max(agreement, 1 - agreement)  # sign flip invariant

# ====== Run analysis on all configurations ======
print("Running graph-theoretic analysis on all configurations...")
configs = [
    ("n3", 3, np.array([(0,1),(1,2),(0,2)]), 0.5, 0.3, 500),
    ("n10_ER", 10, make_er(10, 0.25), 0.5, 0.3, 600),
    ("n10_BA", 10, make_ba(10, 2), 0.5, 0.3, 600),
    ("n10_WS", 10, make_ws(10, 4, 0.1), 0.5, 0.3, 600),
    ("n20_ER", 20, make_er(20, 0.12), 0.5, 0.3, 800),
    ("n20_BA", 20, make_ba(20, 3), 0.5, 0.3, 800),
    ("n20_WS", 20, make_ws(20, 6, 0.1), 0.5, 0.3, 800),
    ("n50_ER", 50, make_er(50, 0.05), 0.5, 0.3, 1000),
    ("n50_BA", 50, make_ba(50, 3), 0.5, 0.3, 1000),
    ("n50_WS", 50, make_ws(50, 6, 0.1), 0.5, 0.3, 1000),
    ("n100_ER", 100, make_er(100, 0.03), 0.5, 0.3, 1500),
    ("n100_BA", 100, make_ba(100, 3), 0.5, 0.3, 1500),
    ("n100_WS", 100, make_ws(100, 6, 0.1), 0.5, 0.3, 1500),
]

results = []
for name, n, edges, eps, alpha, T_max in configs:
    print(f"  {name}...", end=" ")
    res = run_one(n, edges, eps, alpha, T_max, seed=42)
    if not res:
        print("FAIL"); continue
    x_f, w_f = res
    px_f = phi(x_f)
    Vp = np.where(px_f > 1e-6)[0]; Vn = np.where(px_f < -1e-6)[0]
    V0 = np.where(np.abs(px_f) <= 1e-6)[0]
    intra, inter = [], []
    for idx,(i,j) in enumerate(edges):
        wv = w_f[idx]
        if (px_f[i] > 1e-6 and px_f[j] > 1e-6) or (px_f[i] < -1e-6 and px_f[j] < -1e-6):
            intra.append(wv)
        elif (px_f[i] > 1e-6 and px_f[j] < -1e-6) or (px_f[i] < -1e-6 and px_f[j] > 1e-6):
            inter.append(wv)
    ca = {'Vp_idx': Vp, 'Vn_idx': Vn, 'V0_idx': V0, 'Vp': len(Vp), 'Vn': len(Vn), 'V0': len(V0)}
    if intra and inter:
        ca['theta_high'] = min(intra); ca['theta_low'] = max(inter)
        ca['delta'] = ca['theta_high'] - ca['theta_low']

    # Build graph
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for i,j in edges: G.add_edge(i,j)

    # k-plex
    kp = compute_kplex_params(x_f, edges, ca)

    # Structural balance
    bal, total = compute_balance(G, edges, w_f)

    # Spectral
    spec = spectral_comparison(G, ca, w_f, edges)

    results.append({
        'name': name, 'n': n, 'delta': ca.get('delta', 0),
        'Vp': ca['Vp'], 'Vn': ca['Vn'], 'V0': ca['V0'],
        'kplex_Vp': kp.get('V+'), 'kplex_Vn': kp.get('V-'),
        'balance_ratio': bal/total if total > 0 else 0,
        'n_triangles': total,
        'spectral_agreement': spec,
    })
    print(f"δ={ca.get('delta',0):.2f} kp_V+={kp.get('V+',{}).get('k','-') if kp.get('V+') else '-'} bal={bal}/{total} spec={spec:.3f}")

# ====== Generate figures ======
print("\nGenerating analysis figures...")

# Figure 1: k-plex parameter across topologies
fig, axes = plt.subplots(1, 2, figsize=(9, 3.5))

# k-plex k vs network size
for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
    pts = [(r['n'], r['kplex_Vp']['k']) for r in results
           if topo in r['name'] and r['kplex_Vp'] is not None and r['Vp'] >= 2]
    if pts:
        ns, ks = zip(*sorted(pts))
        axes[0].plot(ns, ks, color=color, marker=marker, lw=1.5, markersize=7, label=topo, markerfacecolor=color)
axes[0].set_xlabel('$n$'); axes[0].set_ylabel('$k$ (k-plex parameter)')
axes[0].set_title('$k$-plex of $V^+$ subgraph', fontweight='bold')
axes[0].legend(fontsize=8)

# Structural balance ratio vs network size
for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
    pts = [(r['n'], r['balance_ratio']) for r in results if topo in r['name']]
    if pts:
        ns, br = zip(*sorted(pts))
        axes[1].plot(ns, br, color=color, marker=marker, lw=1.5, markersize=7, label=topo, markerfacecolor=color)
axes[1].axhline(y=1.0, color=C_GRAY, ls=':', lw=1.5)
axes[1].set_xlabel('$n$'); axes[1].set_ylabel('Balanced triangle ratio')
axes[1].set_title('Structural balance', fontweight='bold')
axes[1].legend(fontsize=8)
axes[1].set_ylim(0, 1.1)

for ax in axes: ax.grid(alpha=0.10)
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, 'dgng_kplex_balance.png'), dpi=300, facecolor='white')
plt.close(fig)

# Figure 2: Spectral agreement
fig, ax = plt.subplots(figsize=(5, 3.5))
for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
    pts = [(r['n'], r['spectral_agreement']) for r in results if topo in r['name']]
    if pts:
        ns, sa = zip(*sorted(pts))
        ax.plot(ns, sa, color=color, marker=marker, lw=1.5, markersize=7, label=topo, markerfacecolor=color)
ax.axhline(y=1.0, color=C_GRAY, ls=':', lw=1.5)
ax.set_xlabel('$n$'); ax.set_ylabel('Agreement with Fiedler eigenvector')
ax.set_title('$\\delta$-cohesive vs. spectral partition', fontweight='bold')
ax.legend(fontsize=9); ax.set_ylim(0, 1.1); ax.grid(alpha=0.10)
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, 'dgng_spectral_comparison.png'), dpi=300, facecolor='white')
plt.close(fig)

# ====== Print table for paper ======
print("\n" + "="*80)
print("TABLE: Graph-theoretic analysis of equilibrium structures")
print("="*80)
print(f"{'Config':<12} {'n':>4} {'δ':>7} {'V+':>5} {'V-':>5} {'V0':>4} {'k+(k-plex)':>11} {'bal/tri':>10} {'spec':>6}")
print("-"*80)
for r in results:
    kp_vp = f"{r['kplex_Vp']['k']}" if r['kplex_Vp'] else "-"
    print(f"{r['name']:<12} {r['n']:>4} {r['delta']:>7.3f} {r['Vp']:>5} {r['Vn']:>5} {r['V0']:>4} {kp_vp:>11} {r['balance_ratio']:>10.3f} {r['spectral_agreement']:>6.3f}")
print("="*80)
print("\nDone. All graph-theoretic analysis figures saved.")
