"""
DCNG Large-Scale Simulation
============================
Extends dgng_simulation.py to n=50,100,200 with ER/BA/WS topologies.

Theoretical prediction:
  At equilibrium: w*_ij = phi(x_i)*phi(x_j)/alpha
  When |x_i| >> 1: tanh ≈ ±1
  => intra-group w* ≈ 1/alpha, inter-group w* ≈ -1/alpha
  => delta_max = theta_high - theta_low ≈ 1/alpha - (-1/alpha) = 2/alpha
  For alpha=0.3: delta_max ≈ 6.6667
"""

import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import networkx as nx
import os, time, sys, warnings
from dataclasses import dataclass, field
from typing import Optional

# ── Configuration ──────────────────────────────────────────────────────────────
OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

# Simulation combos
N_VALUES = [50, 100, 200]
TOPOLOGIES = ['er', 'ba', 'ws']
EPS = 0.5
ALPHA = 0.3
SEED = 42
THEORETICAL_DELTA_MAX = 2.0 / ALPHA  # ≈ 6.6667

# Per-n tuning
PARAMS = {
    50:  {'p_edge': 0.15, 'T_max': 200.0, 'eval_pts': 2000},
    100: {'p_edge': 0.10, 'T_max': 300.0, 'eval_pts': 2500},
    200: {'p_edge': 0.08, 'T_max': 500.0, 'eval_pts': 3000},
}

# ── Activation & helpers (exact Lean4 match) ─────────────────────────────────
def phi(x: np.ndarray) -> np.ndarray:
    return np.tanh(x)

def phi_prime(x: np.ndarray) -> np.ndarray:
    return 1.0 / np.cosh(x) ** 2

def G_phi(x: np.ndarray) -> np.ndarray:
    return x * np.tanh(x) - np.log(np.cosh(x))

# ── ODE right-hand side (dgngF_n, LaSalle_n.lean:174) ────────────────────────
def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]
    w = z[n:]
    px = phi(x)
    dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]
        dx[i] += wij * px[j]
        dx[j] += wij * px[i]
    dw = np.array([eps * (px[i] * px[j] - alpha * w[idx])
                   for idx, (i, j) in enumerate(edges)])
    return np.concatenate([dx, dw])

# ── Energy (dgngEnergy_n, LaSalle_n.lean:184) ─────────────────────────────────
def energy(x, w_vec, edges, alpha):
    px = phi(x)
    E_int = -sum(w_vec[idx] * px[i] * px[j] for idx, (i, j) in enumerate(edges))
    E_pot = np.sum(G_phi(x))
    E_reg = 0.5 * alpha * np.sum(w_vec ** 2)
    return E_int + E_pot + E_reg

# ── Gradient norm (required for convergence detection) ────────────────────────
def compute_max_dx(x, w_vec, edges):
    """Compute max |dx_i| for the x-subsystem."""
    n = len(x)
    px = phi(x)
    dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w_vec[idx]
        dx[i] += wij * px[j]
        dx[j] += wij * px[i]
    return np.max(np.abs(dx))

# ── Graph generators ──────────────────────────────────────────────────────────
def make_er(n: int, p_edge: float, seed: int):
    """Erdos-Renyi random graph."""
    rng = np.random.default_rng(seed)
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)
             if rng.random() < p_edge]
    return edges

def make_ba(n: int, m: int, seed: int):
    """Barabasi-Albert scale-free graph."""
    G = nx.barabasi_albert_graph(n, m, seed=seed)
    edges = sorted(G.edges())
    return [(int(u), int(v)) for u, v in edges]

def make_ws(n: int, k: int, p: float, seed: int):
    """Watts-Strogatz small-world graph."""
    G = nx.watts_strogatz_graph(n, k, p, seed=seed)
    edges = sorted(G.edges())
    return [(int(u), int(v)) for u, v in edges]

def get_graph(n: int, topology: str, seed: int):
    """Dispatch to the correct graph generator."""
    p = PARAMS[n]
    if topology == 'er':
        edges = make_er(n, p['p_edge'], seed)
    elif topology == 'ba':
        edges = make_ba(n, 3, seed)
    elif topology == 'ws':
        edges = make_ws(n, 6, 0.1, seed)
    else:
        raise ValueError(f"Unknown topology: {topology}")
    return edges

# ── State analysis ────────────────────────────────────────────────────────────
@dataclass
class StateAnalysis:
    n_pos: int
    n_neg: int
    n_zero: int
    Vp: np.ndarray
    Vn: np.ndarray
    V0: np.ndarray
    theta_high: Optional[float] = None
    theta_low: Optional[float] = None
    delta: Optional[float] = None
    max_intra: Optional[float] = None
    min_inter: Optional[float] = None
    cohesive_pct: Optional[float] = None

def analyze_state(x, w_vec, edges, alpha) -> StateAnalysis:
    """Compute δ-cohesive structure at a single time point."""
    n = len(x)
    px = phi(x)

    # Sign partition
    Vp = np.where(px > 1e-6)[0]
    Vn = np.where(px < -1e-6)[0]
    V0 = np.where(np.abs(px) <= 1e-6)[0]

    # Edge classification
    intra_pos_w = []
    intra_neg_w = []
    inter_pn_w = []
    total_edges = len(edges)
    cohesive_count = 0

    for idx, (i, j) in enumerate(edges):
        wv = w_vec[idx]
        pi, pj = px[i], px[j]

        if pi > 1e-6 and pj > 1e-6:
            intra_pos_w.append(wv)
            if wv > 0: cohesive_count += 1
        elif pi < -1e-6 and pj < -1e-6:
            intra_neg_w.append(wv)
            if wv > 0: cohesive_count += 1
        elif (pi > 1e-6 and pj < -1e-6) or (pi < -1e-6 and pj > 1e-6):
            inter_pn_w.append(wv)
            if wv < 0: cohesive_count += 1
        # Edges involving V0 are not classified (no cohesion constraint)

    result = StateAnalysis(
        n_pos=len(Vp), n_neg=len(Vn), n_zero=len(V0),
        Vp=Vp, Vn=Vn, V0=V0,
        cohesive_pct=100.0 * cohesive_count / total_edges if total_edges > 0 else 0.0,
    )

    all_intra = intra_pos_w + intra_neg_w
    if all_intra and inter_pn_w:
        result.theta_high = min(all_intra)
        result.theta_low = max(inter_pn_w)
        result.delta = result.theta_high - result.theta_low
        result.max_intra = max(all_intra)
        result.min_inter = min(inter_pn_w)

    return result

# ── δ trajectory (for the time-evolution subplot) ────────────────────────────
def compute_delta_trajectory(X, W, edges, alpha, stride=20):
    """Compute δ(t) at a subsampled set of time indices."""
    n_pts = X.shape[1]
    idxs = np.arange(0, n_pts, stride)
    delta_vals = []
    for k in idxs:
        state = analyze_state(X[:, k], W[:, k], edges, alpha)
        if state.delta is not None:
            delta_vals.append(state.delta)
        else:
            delta_vals.append(np.nan)
    return idxs, np.array(delta_vals)

# ── Initial conditions (bimodal) ──────────────────────────────────────────────
def make_initial_conditions(n, m, seed):
    """Bimodal initial conditions: half V+, half V-, weights near zero."""
    rng = np.random.default_rng(seed)
    half = n // 2
    x0 = np.concatenate([
        rng.uniform(2.0, 4.0, size=half),      # V+ group
        rng.uniform(-4.0, -2.0, size=n - half)  # V- group
    ])
    rng.shuffle(x0)
    w0 = rng.uniform(-0.2, 0.2, size=m)
    return np.concatenate([x0, w0]), x0, w0

# ── Results container ─────────────────────────────────────────────────────────
@dataclass
class SimResult:
    n: int
    topology: str
    m: int
    converge_t: float
    converged: bool
    n_pos: int
    n_neg: int
    n_zero: int
    delta: Optional[float]
    theta_high: Optional[float]
    theta_low: Optional[float]
    max_intra: Optional[float]
    min_inter: Optional[float]
    cohesive_pct: float
    energy_initial: float
    energy_final: float
    e_non_increasing: bool
    dx_final: float
    n_increase: int
    total_edges: int
    # Stored for figure generation
    T: np.ndarray
    E_hist: np.ndarray
    delta_idxs: np.ndarray
    delta_hist: np.ndarray
    X_final: np.ndarray
    W_final: np.ndarray
    edges: list = field(repr=False)

# ── Single simulation ─────────────────────────────────────────────────────────
def simulate_one(n, topology, eps, alpha, seed):
    """Run one (n, topology) simulation and return SimResult."""
    pset = PARAMS[n]
    edges = get_graph(n, topology, seed + hash(topology) % 1000)
    m = len(edges)
    if m == 0:
        return None

    T_max = pset['T_max']
    n_eval = pset['eval_pts']

    z0, x0, w0 = make_initial_conditions(n, m, seed)
    E0 = energy(x0, w0, edges, alpha)
    dx0 = compute_max_dx(x0, w0, edges)

    print(f"\n  [init] n={n}, {topology}, m={m}, E(0)={E0:.4f}, max|dx(0)|={dx0:.4f}")

    t_eval = np.linspace(0, T_max, n_eval)
    try:
        sol = solve_ivp(
            dgng_ode, [0, T_max], z0,
            method='LSODA', t_eval=t_eval,
            args=(n, edges, eps, alpha),
            rtol=1e-9, atol=1e-12, max_step=1.0,
        )
    except Exception as exc:
        print(f"  [FAIL] solver exception: {exc}")
        return None

    if not sol.success:
        print(f"  [FAIL] solver message: {sol.message}")
        # Try to salvage partial result
        if sol.y.shape[1] < 10:
            return None
        # Use whatever we have

    T = sol.t
    X = sol.y[:n, :]
    W = sol.y[n:, :]

    # Energy history
    E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha)
                       for k in range(len(T))])

    # Monotonicity check
    dE = np.diff(E_hist)
    n_increase = int(np.sum(dE > 1e-12))

    # Convergence time: first t where max|dx| < 1e-8
    converge_t = T_max
    converged = False
    for k in range(len(T)):
        dx_val = compute_max_dx(X[:, k], W[:, k], edges)
        if dx_val < 1e-8:
            converge_t = T[k]
            converged = True
            break

    # Final state analysis
    x_f = X[:, -1]
    w_f = W[:, -1]
    dx_f = compute_max_dx(x_f, w_f, edges)
    final_state = analyze_state(x_f, w_f, edges, alpha)
    E_f = E_hist[-1]

    print(f"  [done] E(T)={E_f:.6f}, dx_f={dx_f:.2e}, "
          f"converged={converged} at t={converge_t:.1f}")
    print(f"         V+={final_state.n_pos}, V-={final_state.n_neg}, V0={final_state.n_zero}, "
          f"delta={final_state.delta}")

    # δ trajectory
    delta_idxs, delta_hist = compute_delta_trajectory(X, W, edges, alpha, stride=20)

    return SimResult(
        n=n, topology=topology, m=m,
        converge_t=converge_t, converged=converged,
        n_pos=final_state.n_pos, n_neg=final_state.n_neg,
        n_zero=final_state.n_zero,
        delta=final_state.delta, theta_high=final_state.theta_high,
        theta_low=final_state.theta_low,
        max_intra=final_state.max_intra, min_inter=final_state.min_inter,
        cohesive_pct=final_state.cohesive_pct,
        energy_initial=E0, energy_final=E_f,
        e_non_increasing=(n_increase == 0),
        dx_final=dx_f, n_increase=n_increase,
        total_edges=m,
        T=T, E_hist=E_hist,
        delta_idxs=delta_idxs, delta_hist=delta_hist,
        X_final=x_f, W_final=w_f, edges=edges,
    )

# ── Figure generation (one per topology) ──────────────────────────────────────
def make_topology_figure(results, topo_name, out_dir):
    """Generate a summary figure for one topology with all three n values."""
    n_figs = len(results)
    fig, axes = plt.subplots(n_figs, 4, figsize=(22, 5 * n_figs))
    if n_figs == 1:
        axes = axes.reshape(1, -1)

    topo_label = {'er': 'Erdos-Renyi', 'ba': 'Barabasi-Albert', 'ws': 'Watts-Strogatz'}
    fig.suptitle(f'DCNG Summary — {topo_label.get(topo_name, topo_name.upper())} Topology\n'
                 f'epsilon={EPS}, alpha={ALPHA},  theoretical delta_max=2/alpha={THEORETICAL_DELTA_MAX:.4f}',
                 fontsize=14, fontweight='bold')

    for row, res in enumerate(results):
        # Panel 1: Energy E(t)
        ax = axes[row, 0]
        ax.plot(res.T, res.E_hist, 'b-', lw=1.0)
        ax.set_xlabel('t')
        ax.set_ylabel('E(t)')
        ax.set_title(f'n={res.n}, m={res.m}: E(t) (non-inc: {res.e_non_increasing})')
        ax.axhline(y=res.energy_final, color='gray', ls='--', lw=0.5)
        ax.grid(alpha=0.3)

        # Panel 2: delta(t) evolution
        ax = axes[row, 1]
        t_vals = res.T[res.delta_idxs]
        valid = ~np.isnan(res.delta_hist)
        ax.plot(t_vals[valid], res.delta_hist[valid], 'g-', lw=1.2)
        ax.axhline(y=THEORETICAL_DELTA_MAX, color='red', ls='--', lw=0.8,
                   label=f'2/alpha={THEORETICAL_DELTA_MAX:.2f}')
        if res.delta is not None:
            ax.axhline(y=res.delta, color='darkgreen', ls=':', lw=1.0,
                       label=f'final delta={res.delta:.3f}')
        ax.set_xlabel('t')
        ax.set_ylabel('delta(t)')
        ax.set_title(f'Delta(t): theta_high - theta_low')
        ax.legend(fontsize=7)
        ax.grid(alpha=0.3)

        # Panel 3: Final network (colored by V+/V-)
        ax = axes[row, 2]
        G = nx.Graph()
        for idx, (i, j) in enumerate(res.edges):
            G.add_edge(i, j, weight=abs(res.W_final[idx]))
        # Use a reliable layout
        pos = nx.spring_layout(G, seed=SEED, k=1.5 / np.sqrt(res.n))

        final_state = analyze_state(res.X_final, res.W_final, res.edges, ALPHA)
        colors = ['red' if i in final_state.Vp
                  else 'blue' if i in final_state.Vn
                  else 'gray' for i in range(res.n)]
        sizes = [80.0 if res.n <= 100 else 40.0 for _ in range(res.n)]
        edge_colors = []
        for idx, (i, j) in enumerate(res.edges):
            pi, pj = phi(res.X_final[i]), phi(res.X_final[j])
            if pi > 1e-6 and pj > 1e-6:
                edge_colors.append('green' if res.W_final[idx] > 0 else 'orange')
            elif pi < -1e-6 and pj < -1e-6:
                edge_colors.append('blue' if res.W_final[idx] > 0 else 'orange')
            elif (pi > 1e-6 and pj < -1e-6) or (pi < -1e-6 and pj > 1e-6):
                edge_colors.append('red' if res.W_final[idx] < 0 else 'orange')
            else:
                edge_colors.append('gray')
        edge_widths = [min(abs(res.W_final[idx]) * 1.5, 3.0) for idx in range(res.total_edges)]

        nx.draw_networkx_nodes(G, pos, node_color=colors, node_size=sizes, ax=ax)
        nx.draw_networkx_edges(G, pos, edge_color=edge_colors, width=edge_widths,
                               alpha=0.4, ax=ax)
        ax.set_title(f'Final network: red=V+, blue=V-, gray=V0\n'
                     f'Green=intra(+), Blue-edge=intra(-), Red-edge=inter')
        ax.axis('off')

        # Panel 4: Weight distribution histogram
        ax = axes[row, 3]
        # Separate weights by edge type
        intra_w = []
        inter_w = []
        zero_w = []
        for idx, (i, j) in enumerate(res.edges):
            pi, pj = phi(res.X_final[i]), phi(res.X_final[j])
            if abs(res.W_final[idx]) < 1e-8:
                zero_w.append(res.W_final[idx])
            elif (pi > 1e-6 and pj > 1e-6) or (pi < -1e-6 and pj < -1e-6):
                intra_w.append(res.W_final[idx])
            else:
                inter_w.append(res.W_final[idx])

        bins = 40
        if intra_w:
            ax.hist(intra_w, bins=bins, alpha=0.6, color='green', label=f'intra (n={len(intra_w)})')
        if inter_w:
            ax.hist(inter_w, bins=bins, alpha=0.6, color='red', label=f'inter (n={len(inter_w)})')
        ax.axvline(x=0, color='k', ls='--', lw=0.5)
        ax.axvline(x=1.0 / ALPHA, color='darkgreen', ls=':', lw=1.0, label=f'+1/alpha={1.0/ALPHA:.2f}')
        ax.axvline(x=-1.0 / ALPHA, color='darkred', ls=':', lw=1.0, label=f'-1/alpha={-1.0/ALPHA:.2f}')
        ax.set_xlabel('w_e')
        ax.set_ylabel('count')
        ax.set_title(f'Weight distribution (delta={res.delta:.3f})')
        ax.legend(fontsize=7)
        ax.grid(alpha=0.3)

    plt.tight_layout()
    fname = os.path.join(out_dir, f'dgng_summary_{topo_name}.png')
    fig.savefig(fname, dpi=120, bbox_inches='tight')
    plt.close(fig)
    print(f"Figure saved: {fname}")

# ── Results table ─────────────────────────────────────────────────────────────
def print_results_table(all_results):
    """Print a formatted ASCII results table."""
    print("\n" + "=" * 120)
    print("DCNG LARGE-SCALE SIMULATION RESULTS")
    print(f"epsilon={EPS}, alpha={ALPHA}, theoretical delta_max=2/alpha={THEORETICAL_DELTA_MAX:.4f}")
    print("=" * 120)

    header = (
        f"{'n':>4} {'topology':>10} {'m':>5} {'converge_t':>10} "
        f"{'V+':>4} {'V-':>4} {'V0':>3} "
        f"{'delta':>8} {'theta_h':>8} {'theta_l':>8} "
        f"{'max_intra':>10} {'min_inter':>10} {'%cohesive':>9} "
        f"{'E_final':>10} {'E non-inc':>10}"
    )
    print(header)
    print("-" * 120)

    for res in all_results:
        delta_str = f"{res.delta:.4f}" if res.delta is not None else "N/A"
        th_str = f"{res.theta_high:.4f}" if res.theta_high is not None else "N/A"
        tl_str = f"{res.theta_low:.4f}" if res.theta_low is not None else "N/A"
        mi_str = f"{res.max_intra:.4f}" if res.max_intra is not None else "N/A"
        mn_str = f"{res.min_inter:.4f}" if res.min_inter is not None else "N/A"
        ct_str = f"{res.converge_t:.1f}" if res.converged else f"{res.converge_t:.1f}*"
        ein_str = "PASS" if res.e_non_increasing else "FAIL"

        print(
            f"{res.n:>4} {res.topology:>10} {res.m:>5} {ct_str:>10} "
            f"{res.n_pos:>4} {res.n_neg:>4} {res.n_zero:>3} "
            f"{delta_str:>8} {th_str:>8} {tl_str:>8} "
            f"{mi_str:>10} {mn_str:>10} {res.cohesive_pct:>8.1f}% "
            f"{res.energy_final:>10.4f} {ein_str:>10}"
        )

    print("=" * 120)
    print("* = did not fully converge within T_max")
    print(f"Theoretical max delta = {THEORETICAL_DELTA_MAX:.4f}")
    print("=" * 120)

# ── Combined comparison figure ────────────────────────────────────────────────
def make_comparison_figure(all_results, out_dir):
    """Generate a combined comparison figure: delta per (n, topology)."""
    topo_labels = {'er': 'ER', 'ba': 'BA', 'ws': 'WS'}

    fig, axes = plt.subplots(1, 3, figsize=(18, 6))
    fig.suptitle(f'DCNG Comparison Across Topologies\n'
                 f'epsilon={EPS}, alpha={ALPHA}, theoretical delta_max={THEORETICAL_DELTA_MAX:.4f}',
                 fontsize=14, fontweight='bold')

    markers = {'er': 'o', 'ba': 's', 'ws': '^'}

    for idx, topo in enumerate(TOPOLOGIES):
        ax = axes[idx]
        subset = [r for r in all_results if r.topology == topo]
        ns = [r.n for r in subset]
        deltas = [r.delta if r.delta is not None else 0 for r in subset]
        cohesive = [r.cohesive_pct for r in subset]

        ax2 = ax.twinx()
        (line1,) = ax.plot(ns, deltas, 'bo-', ms=8, lw=1.5, label='delta')
        (line2,) = ax2.plot(ns, cohesive, 'rs--', ms=8, lw=1.5, label='% cohesive')

        ax.axhline(y=THEORETICAL_DELTA_MAX, color='gray', ls='--', lw=0.8,
                   label=f'theoretical max={THEORETICAL_DELTA_MAX:.2f}')

        ax.set_xlabel('n')
        ax.set_ylabel('delta', color='b')
        ax2.set_ylabel('% cohesive edges', color='r')
        ax.set_title(f'{topo_labels.get(topo, topo)} Topology')
        ax.grid(alpha=0.3)

        lines = [line1, line2]
        labels = [l.get_label() for l in lines]
        ax.legend(lines, labels, loc='best', fontsize=8)

    plt.tight_layout()
    fname = os.path.join(out_dir, 'dgng_comparison.png')
    fig.savefig(fname, dpi=120, bbox_inches='tight')
    plt.close(fig)
    print(f"Figure saved: {fname}")

# ── Wolfram verification (optional) ───────────────────────────────────────────
def wolfram_verify_delta():
    """Use WolframScript to verify the equilibrium formula."""
    import subprocess
    code = (
        'Print[StringForm["For alpha=``:  delta_max = 2/alpha = ``", '
        '0.3, N[2/0.3, 10]]];\n'
        'Print[StringForm["Intra-group w* = 1/alpha = ``", N[1/0.3, 10]]];\n'
        'Print[StringForm["Inter-group w* = -1/alpha = ``", N[-1/0.3, 10]]];'
    )
    try:
        result = subprocess.run(
            ['cmd', '/c', '"D:\\math\\Wolfram Engine 14.3\\WolframScript.exe"', '-code', code],
            capture_output=True, text=True, timeout=30
        )
        print("\n[Wolfram Verification]:")
        print(result.stdout)
        if result.stderr:
            print("stderr:", result.stderr[:200])
    except Exception as exc:
        print(f"[Wolfram] verification skipped: {exc}")

# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    print("=" * 70)
    print("DCNG LARGE-SCALE SIMULATION")
    print(f"n = {N_VALUES}")
    print(f"topologies = {TOPOLOGIES}")
    print(f"epsilon = {EPS}, alpha = {ALPHA}")
    print(f"theoretical delta_max = 2/alpha = {THEORETICAL_DELTA_MAX:.4f}")
    print("=" * 70)

    # Optional Wolfram verification
    wolfram_verify_delta()

    all_results = []
    total = len(N_VALUES) * len(TOPOLOGIES)
    count = 0

    for n in N_VALUES:
        for topo in TOPOLOGIES:
            count += 1
            print(f"\n{'─' * 60}")
            print(f"[{count}/{total}] n={n}, topology={topo}")
            print(f"{'─' * 60}")

            t_start = time.time()
            try:
                res = simulate_one(n, topo, EPS, ALPHA, SEED + count)
                elapsed = time.time() - t_start
                print(f"  [elapsed] {elapsed:.1f}s")
                if res is not None:
                    all_results.append(res)
                else:
                    print(f"  [SKIP] simulation returned None")
            except Exception as exc:
                elapsed = time.time() - t_start
                print(f"  [ERROR] after {elapsed:.1f}s: {exc}")

    # Print results table
    if all_results:
        print_results_table(all_results)

        # Generate per-topology figures
        print("\nGenerating per-topology summary figures...")
        for topo in TOPOLOGIES:
            subset = [r for r in all_results if r.topology == topo]
            if subset:
                make_topology_figure(subset, topo, OUT_DIR)
            else:
                print(f"  (no results for {topo})")

        # Generate comparison figure
        print("Generating comparison figure...")
        make_comparison_figure(all_results, OUT_DIR)

        # Save raw results as text
        results_path = os.path.join(OUT_DIR, 'dgng_large_scale_results.txt')
        with open(results_path, 'w') as f:
            f.write(f"DCNG Large-Scale Simulation Results\n")
            f.write(f"epsilon={EPS}, alpha={ALPHA}\n")
            f.write(f"theoretical delta_max=2/alpha={THEORETICAL_DELTA_MAX:.4f}\n\n")
            for res in all_results:
                f.write(str(res) + "\n")
        print(f"Results saved: {results_path}")

    print("\nAll simulations complete.")

if __name__ == '__main__':
    main()
