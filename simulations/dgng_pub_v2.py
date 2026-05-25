"""
DCNG pub figures v2 — cleaner layout, no info box, bigger fonts, better topology.
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
    "font.size": 11, "axes.titlesize": 12, "axes.titleweight": "bold",
    "axes.labelsize": 11, "legend.fontsize": 9, "legend.frameon": True,
    "legend.edgecolor": "#DDD",
    "figure.dpi": 300, "savefig.dpi": 300, "savefig.bbox": "tight",
    "savefig.pad_inches": 0.08,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.linewidth": 0.6,
    "axes.grid": True, "grid.alpha": 0.10, "grid.linestyle": "-", "grid.linewidth": 0.4,
    "lines.linewidth": 1.6, "lines.markersize": 5,
    "xtick.labelsize": 10, "ytick.labelsize": 10,
    "xtick.major.width": 0.5, "ytick.major.width": 0.5,
    "axes.titlepad": 14,
})
C_TEAL = "#264653"; C_GREEN = "#2A9D8F"; C_ORANGE = "#F4A261"; C_CORAL = "#E76F51"
C_BLUE = "#2878B5"; C_RED = "#C82423"; C_GRAY = "#9E9E9E"

def phi(x): return np.tanh(x)
def phi_prime(x): return 1.0 / np.cosh(x) ** 2
def G_phi(x): return x * np.tanh(x) - np.log(np.cosh(x))

def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]; px = phi(x); dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]; dx[i] += wij * px[j]; dx[j] += wij * px[i]
    dw = [eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)]
    return np.concatenate([dx, dw])

def energy(x, w_vec, edges, alpha):
    px = phi(x)
    return (-sum(w_vec[k] * px[i] * px[j] for k, (i, j) in enumerate(edges))
            + np.sum(G_phi(x)) + 0.5 * alpha * np.sum(w_vec ** 2))

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
    return r

def run_one(n, edges, eps, alpha, T_max, seed=42):
    m = len(edges); rng = np.random.default_rng(seed)
    half = n // 2
    x0 = np.concatenate([rng.uniform(2, 4, size=half), rng.uniform(-4, -2, size=n - half)])
    rng.shuffle(x0); w0 = rng.uniform(-0.2, 0.2, size=m)
    z0 = np.concatenate([x0, w0])
    t_eval = np.linspace(0, T_max, 2000)
    sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                    args=(n, edges, eps, alpha), rtol=1e-9, atol=1e-13, max_step=min(1.0, T_max / 500))
    if not sol.success: return None
    T, X, W = sol.t, sol.y[:n, :], sol.y[n:, :]
    x_f, w_f = X[:, -1], W[:, -1]
    E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha) for k in range(len(T))])
    dE = np.diff(E_hist); abs_dE = np.abs(E_hist[:-1])
    n_inc = np.sum((dE > 1e-12) & ((abs_dE < 1e-10) | (dE / abs_dE < 1e-10)))
    S_f = np.zeros(n); px_f = phi(x_f)
    for idx, (i, j) in enumerate(edges):
        wij = w_f[idx]; S_f[i] += wij * px_f[j]; S_f[j] += wij * px_f[i]
    dx_max = np.max(np.abs(-x_f + S_f))
    ca = analyze(x_f, w_f, edges, alpha)
    ca['E0'] = E_hist[0]; ca['Ef'] = E_hist[-1]; ca['n_inc'] = n_inc; ca['dx_max'] = dx_max
    return T, X, W, edges, E_hist, ca

rng = np.random.default_rng(42)

def make_er(n, p_edge):
    return np.array([(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p_edge], dtype=int)

def make_ba(n, m_param):
    return np.array(list(nx.barabasi_albert_graph(n, m_param, seed=int(rng.integers(0, 2 ** 31))).edges()), dtype=int)

def make_ws(n, k, p_rewire):
    return np.array(list(nx.watts_strogatz_graph(n, k, p_rewire, seed=int(rng.integers(0, 2 ** 31))).edges()), dtype=int)

# ── Publication figure — 3x3 grid, no info box ──
def pub_figure(T, X, W, edges_used, E_hist, ca, eps, alpha, name, topo_label):
    n = X.shape[0]; m = len(edges_used)
    x_f = X[:, -1]; w_f = W[:, -1]; px_f = phi(x_f)
    Vp = ca.get('Vp_idx', np.array([])); Vn = ca.get('Vn_idx', np.array([]))
    d_ = ca.get('delta', 0)

    fig = plt.figure(figsize=(8.0, 6.8))
    gs = fig.add_gridspec(3, 3, hspace=0.60, wspace=0.45)

    # (0,0) Energy
    ax = fig.add_subplot(gs[0, 0])
    ax.plot(T, E_hist, color=C_TEAL, lw=1.8)
    ax.set_xlabel('$t$'); ax.set_ylabel('$E(t)$')
    ax.set_title('Energy', fontsize=12, fontweight='bold')
    ax.ticklabel_format(axis='y', style='scientific', scilimits=(-2, 2))

    # (0,1) phi(x_i)
    ax = fig.add_subplot(gs[0, 1])
    for i in range(min(n, 8)):
        ax.plot(T, phi(X[i, :]), lw=1.0, alpha=0.8)
    ax.set_xlabel('$t$'); ax.set_ylabel('$\\phi(x_i)$')
    ax.set_title('Activations', fontsize=12, fontweight='bold')

    # (0,2) Weight trajectories
    ax = fig.add_subplot(gs[0, 2])
    for idx in range(min(m, 8)):
        ax.plot(T, W[idx, :], lw=0.9, alpha=0.7)
    ax.set_xlabel('$t$'); ax.set_ylabel('$w_e$')
    ax.set_title('Weights', fontsize=12, fontweight='bold')

    # (1,0) Network topology
    ax = fig.add_subplot(gs[1, 0])
    G = nx.Graph(); G.add_nodes_from(range(n))
    for idx, (i, j) in enumerate(edges_used): G.add_edge(i, j)
    k_val = 7.0 / np.sqrt(n) if n > 20 else 4.0 / max(np.sqrt(n), 1)
    pos = nx.spring_layout(G, seed=42, k=k_val, iterations=120)
    node_colors = [C_RED if i in Vp else C_BLUE if i in Vn else C_GRAY for i in range(n)]
    base = max(4, 60.0 / (n ** 0.4))
    sizes = [base * 2.2 if i in Vp or i in Vn else base * 0.2 for i in range(n)]
    edge_colors = [C_GREEN if (i in Vp and j in Vp) or (i in Vn and j in Vn)
                   else C_CORAL if (i in Vp and j in Vn) or (i in Vn and j in Vp)
                   else '#E0E0E0' for i, j in edges_used]
    ew = 0.25 if n > 50 else 0.5
    nx.draw_networkx_edges(G, pos, edge_color=edge_colors, width=ew, alpha=0.55, ax=ax)
    nx.draw_networkx_nodes(G, pos, node_color=node_colors, node_size=sizes, linewidths=0, ax=ax)
    ax.set_title(f'{topo_label} ($n={n}$, $\\delta={d_:.2f}$)', fontsize=12, fontweight='bold')
    ax.axis('off')

    # (1,1) Weight matrix
    ax = fig.add_subplot(gs[1, 1])
    W_mat = np.zeros((n, n))
    for idx, (i, j) in enumerate(edges_used): W_mat[i, j] = W_mat[j, i] = w_f[idx]
    im = ax.imshow(W_mat, cmap='RdBu_r', vmin=-3.5, vmax=3.5, aspect='auto', interpolation='nearest')
    ax.set_title('Weight matrix $W^*$', fontsize=12, fontweight='bold')
    plt.colorbar(im, ax=ax, shrink=0.75)

    # (1,2) Weight histogram
    ax = fig.add_subplot(gs[1, 2])
    ax.hist(w_f, bins=min(40, max(15, m // 3)), color=C_ORANGE, edgecolor='white', alpha=0.8, lw=0.3)
    ax.axvline(x=0, color='#555', ls='--', lw=0.6)
    if 'theta_high' in ca:
        th = ca['theta_high']; tl = ca['theta_low']
        ax.axvline(th, color=C_GREEN, ls=':', lw=2, label='$\\theta_h$')
        ax.axvline(tl, color=C_RED, ls=':', lw=2, label='$\\theta_l$')
        ax.legend(fontsize=9, loc='upper left')
    ax.set_xlabel('$w_e$'); ax.set_ylabel('Count')
    ax.set_title('Weight distribution', fontsize=12, fontweight='bold')

    # (2,0) Vdot(t)
    ax = fig.add_subplot(gs[2, 0])
    Vh = np.zeros(len(T))
    for k in range(len(T)):
        S = np.zeros(n)
        for idx, (i, j) in enumerate(edges_used):
            wv = W[idx, k]; pi = phi(X[i, k]); pj = phi(X[j, k])
            S[i] += wv * pj; S[j] += wv * pi
        Vh[k] = (-sum(phi_prime(X[:, k]) * (X[:, k] - S) ** 2)
                 - eps * sum((alpha * W[idx, k] - phi(X[i, k]) * phi(X[j, k])) ** 2
                             for idx, (i, j) in enumerate(edges_used)))
    ax.plot(T, Vh, color=C_CORAL, lw=1.3, alpha=0.8)
    ax.axhline(y=0, color='k', ls='--', lw=0.5)
    ax.set_xlabel('$t$')
    ax.set_title('$\\dot E(t) \\leq 0$', fontsize=12, fontweight='bold')

    # (2,1)+(2,2) Self-consistency
    ax = fig.add_subplot(gs[2, 1:])
    pv, av = [], []
    for idx, (i, j) in enumerate(edges_used[:min(50, len(edges_used))]):
        if abs(px_f[j]) > 1e-6:
            pv.append(alpha * w_f[idx] / px_f[j]); av.append(px_f[i])
    if pv:
        ax.scatter(range(len(av)), av, c=C_RED, s=18, label='$\\phi(x_i)$ actual', zorder=3)
        ax.scatter(range(len(pv)), pv, c=C_BLUE, s=14, alpha=0.5, marker='x', label='$\\alpha w_{ij}/\\phi(x_j)$ pred')
        ax.legend(fontsize=9, loc='best')
    ax.set_title('Self-consistency verification', fontsize=12, fontweight='bold')
    ax.set_xlabel('Edge index'); ax.grid(alpha=0.10)

    fname = os.path.join(OUT_DIR, f"dgng_pub_{name}.png")
    fig.savefig(fname, dpi=300, facecolor='white')
    plt.close(fig)

# ── Phase transition figure ──
def pub_phase_transition():
    n = 20; p = 0.12; alpha = 0.3; T_max = 3000
    edges = make_er(n, p)
    half = n // 2
    x0_fixed = np.concatenate([rng.uniform(2, 4, size=half), rng.uniform(-4, -2, size=n - half)])
    rng.shuffle(x0_fixed); w0_fixed = rng.uniform(-0.2, 0.2, size=len(edges))

    def check_cohesive(eps):
        z0 = np.concatenate([x0_fixed.copy(), w0_fixed.copy()])
        t_eval = np.linspace(0, T_max, 2000)
        sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                        args=(n, edges, eps, alpha), rtol=1e-8, atol=1e-12, max_step=1.0)
        px_f = phi(sol.y[:n, -1]); w_f = sol.y[n:, -1]
        intra, inter = [], []
        for idx, (i, j) in enumerate(edges):
            wv = w_f[idx]
            if (px_f[i] > 1e-6 and px_f[j] > 1e-6) or (px_f[i] < -1e-6 and px_f[j] < -1e-6):
                intra.append(wv)
            elif (px_f[i] > 1e-6 and px_f[j] < -1e-6) or (px_f[i] < -1e-6 and px_f[j] > 1e-6):
                inter.append(wv)
        d_ = 0.0
        if intra and inter: d_ = min(intra) - max(inter)
        return d_

    lo, hi = 0.10, 0.16
    for _ in range(20):
        mid = (lo + hi) / 2; d_ = check_cohesive(mid)
        if d_ > 0: hi = mid
        else: lo = mid
    eps_c = (lo + hi) / 2

    eps_vals = np.linspace(0, 0.35, 250); deltas = []
    for eps in eps_vals: deltas.append(check_cohesive(eps))
    deltas = np.array(deltas)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.8))

    ax1.plot(eps_vals, deltas, color=C_TEAL, lw=2.0)
    ax1.axvline(x=eps_c, color=C_CORAL, ls='--', lw=2, label=f'$\\varepsilon_c = {eps_c:.4f}$')
    ax1.axhline(y=2 / alpha, color=C_GRAY, ls=':', lw=1.5, label=f'$\\delta_{{\\max}} = 2/\\alpha = {2 / alpha:.1f}$')
    ax1.axhline(y=0, color='#444', ls='-', lw=0.5)
    ax1.fill_between([0, eps_c], 0, 7.5, color=C_GRAY, alpha=0.06)
    ax1.fill_between([eps_c, 0.35], 0, 7.5, color=C_GREEN, alpha=0.06)
    ax1.set_xlabel('$\\varepsilon$', fontsize=11); ax1.set_ylabel('$\\delta$', fontsize=11)
    ax1.set_title('Phase transition: $\\delta$ vs $\\varepsilon$', fontsize=12, fontweight='bold')
    ax1.legend(fontsize=9, loc='lower right')
    ax1.set_xlim(0, 0.35); ax1.set_ylim(-0.5, 7.5)
    ax1.annotate('Trivial equilibrium', xy=(0.06, 0.5), fontsize=8, color=C_GRAY, ha='center')
    ax1.annotate(f'Cohesive ($\\delta \\approx 2/\\alpha$)', xy=(0.22, 6.2), fontsize=8, color=C_GREEN, ha='center')

    mask = (eps_vals >= eps_c - 0.015) & (eps_vals <= eps_c + 0.015)
    ax2.plot(eps_vals[mask], deltas[mask], color=C_TEAL, lw=2.0)
    ax2.axvline(x=eps_c, color=C_CORAL, ls='--', lw=2, label=f'$\\varepsilon_c = {eps_c:.4f}$')
    ax2.scatter([eps_c], [2 / alpha], color=C_CORAL, s=60, zorder=5)
    ax2.set_xlabel('$\\varepsilon$', fontsize=11); ax2.set_ylabel('$\\delta$', fontsize=11)
    ax2.set_title('Critical region', fontsize=12, fontweight='bold')
    ax2.legend(fontsize=9, loc='lower right')

    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, 'dgng_pub_phase_transition.png'), dpi=300, facecolor='white')
    plt.close(fig)

# ── Topology comparison figure ──
def pub_topology_summary():
    results = []
    for n, p_er in [(10, 0.25), (20, 0.12), (50, 0.05), (100, 0.03)]:
        for topo_name, make_fn, args in [('ER', make_er, (p_er,)), ('BA', make_ba, (3,)), ('WS', make_ws, (6, 0.1))]:
            try:
                edges = make_fn(n, *args)
            except:
                continue
            res = run_one(n, edges, 0.5, 0.3, 800 if n < 50 else 1500, seed=42)
            if res:
                _, _, _, _, _, ca = res
                results.append((topo_name, n, ca.get('delta', 0), ca['V0'] / n * 100, ca['dx_max'], ca['n_inc']))

    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.5))
    for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
        pts = [(n, d) for t, n, d, v0, dx, ni in results if t == topo]
        if pts:
            ns, ds = zip(*sorted(pts))
            axes[0].plot(ns, ds, color=color, marker=marker, lw=1.5, markersize=6, label=topo, markerfacecolor=color)
    axes[0].axhline(y=2 / 0.3, color=C_GRAY, ls=':', lw=1, label='$2/\\alpha = 6.67$')
    axes[0].set_xlabel('$n$'); axes[0].set_ylabel('$\\delta$')
    axes[0].set_title('Cohesive separation', fontweight='bold')
    axes[0].legend(fontsize=8, loc='lower right'); axes[0].set_ylim(0, 8)

    for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
        pts = [(n, v0) for t, n, d, v0, dx, ni in results if t == topo]
        if pts:
            ns, v0r = zip(*sorted(pts))
            axes[1].plot(ns, v0r, color=color, marker=marker, lw=1.5, markersize=6, label=topo, markerfacecolor=color)
    axes[1].set_xlabel('$n$'); axes[1].set_ylabel('$V^0$ ratio (%)')
    axes[1].set_title('Uncommitted nodes', fontweight='bold')
    axes[1].legend(fontsize=8, loc='upper right')

    for topo, color, marker in [('ER', C_TEAL, 'o'), ('BA', C_CORAL, 's'), ('WS', C_ORANGE, '^')]:
        pts = [(n, dx) for t, n, d, v0, dx, ni in results if t == topo]
        if pts:
            ns, dxs = zip(*sorted(pts))
            axes[2].semilogy(ns, dxs, color=color, marker=marker, lw=1.5, markersize=6, label=topo, markerfacecolor=color)
    axes[2].set_xlabel('$n$'); axes[2].set_ylabel('$\\max\\|\\dot x\\|(T)$')
    axes[2].set_title('Convergence error', fontweight='bold')
    axes[2].legend(fontsize=8, loc='lower right')

    for ax in axes: ax.grid(alpha=0.10, lw=0.4)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, 'dgng_pub_topology_summary.png'), dpi=300, facecolor='white')
    plt.close(fig)

if __name__ == '__main__':
    print("Phase transition...")
    pub_phase_transition()
    print("Topology comparison...")
    pub_topology_summary()

    configs = [
        ("n3_triangle", 3, np.array([(0, 1), (1, 2), (0, 2)], dtype=int), 0.5, 0.3, 500, 'Triangle'),
        ("n10_ER", 10, make_er(10, 0.25), 0.5, 0.3, 600, 'Erdos-Renyi'),
        ("n10_BA", 10, make_ba(10, 2), 0.5, 0.3, 600, 'Barabasi-Albert'),
        ("n10_WS", 10, make_ws(10, 4, 0.1), 0.5, 0.3, 600, 'Watts-Strogatz'),
        ("n20_ER", 20, make_er(20, 0.12), 0.5, 0.3, 800, 'Erdos-Renyi'),
        ("n20_BA", 20, make_ba(20, 3), 0.5, 0.3, 800, 'Barabasi-Albert'),
        ("n20_WS", 20, make_ws(20, 6, 0.1), 0.5, 0.3, 800, 'Watts-Strogatz'),
        ("n50_ER", 50, make_er(50, 0.05), 0.5, 0.3, 1000, 'Erdos-Renyi'),
        ("n50_BA", 50, make_ba(50, 3), 0.5, 0.3, 1000, 'Barabasi-Albert'),
        ("n50_WS", 50, make_ws(50, 6, 0.1), 0.5, 0.3, 1000, 'Watts-Strogatz'),
        ("n100_ER", 100, make_er(100, 0.03), 0.5, 0.3, 1500, 'Erdos-Renyi'),
        ("n100_BA", 100, make_ba(100, 3), 0.5, 0.3, 1500, 'Barabasi-Albert'),
        ("n100_WS", 100, make_ws(100, 6, 0.1), 0.5, 0.3, 1500, 'Watts-Strogatz'),
    ]

    for name, n, edges, eps, alpha, T_max, topo_label in configs:
        print(f"Generating {name}...")
        res = run_one(n, edges, eps, alpha, T_max, seed=42)
        if res:
            T, X, W, ee, Eh, ca = res
            pub_figure(T, X, W, ee, Eh, ca, eps, alpha, name, topo_label)

    print("All done.")
