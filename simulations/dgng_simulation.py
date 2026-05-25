"""
DCNG Simulation — exact match with Lean4 LaSalle_n.lean definitions.

Lean4 refs:
  dgngF_n      (LaSalle_n.lean:174): ẋ_i = -x_i + S_i,  ẇ_e = ε(φ_i φ_j - α w_e)
  dgngEnergy_n (LaSalle_n.lean:184): E = -Σ w_e φ_i φ_j + Σ (x_i φ_i - log ch x_i) + (α/2) Σ w_e²
  dgngVdot_n   (LaSalle_n.lean:192): V̇ = -Σ φ'(x_i)(x_i-S_i)² - ε Σ (α w_e - φ_i φ_j)²
  neighborWeightSum (GraphTheory.lean:35): S_i = Σ_{j∈N(i)} w_ij φ(x_j)
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import networkx as nx
import os

OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

# ── Activation & helper functions ──
def phi(x):       return np.tanh(x)                     # Lean4: Real.tanh
def phi_prime(x): return 1.0 / np.cosh(x)**2             # Lean4: deriv Real.tanh
def G_phi(x):     return x * np.tanh(x) - np.log(np.cosh(x))  # Lean4: x·tanh(x)-log(cosh x)

# ── Dynamics: exact match with dgngF_n (LaSalle_n.lean:174-181) ──
def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]
    px = phi(x)
    # xdot_i = -x_i + neighborWeightSum (Lean4 line 177)
    dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]
        dx[i] += wij * px[j]
        dx[j] += wij * px[i]
    # wdot_ij = ε*(tanh(x_i)*tanh(x_j) - α*w_ij) for edges (Lean4 line 180)
    dw = np.array([eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)])
    return np.concatenate([dx, dw])

# ── Energy: exact match with dgngEnergy_n (LaSalle_n.lean:184-189) ──
def energy(x, w_vec, edges, alpha):
    n = len(x); m = len(edges)
    px = phi(x)
    # E_int = -Σ w_e * tanh(x_e1) * tanh(x_e2)  (NO 1/2)
    E_int = -sum(w_vec[idx] * px[i] * px[j] for idx, (i, j) in enumerate(edges))
    # E_pot = Σ (x_i * tanh(x_i) - log(cosh(x_i)))
    E_pot = np.sum(G_phi(x))
    # E_reg = (α/2) * Σ w_e²
    E_reg = 0.5 * alpha * np.sum(w_vec**2)
    return E_int + E_pot + E_reg

# ── Vdot: exact match with dgngVdot_n (LaSalle_n.lean:192-197) ──
def compute_vdot(x, w_vec, edges, eps, alpha):
    n = len(x); m = len(edges); px = phi(x)
    # neighborWeightSum S_i = Σ_{j∈N(i)} w_ij * tanh(x_j)  (GraphTheory.lean:35)
    S = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        wij = w_vec[idx]
        S[i] += wij * px[j]
        S[j] += wij * px[i]
    # Vdot = -Σ φ'(x_i)*(x_i - S_i)² - ε*Σ (α*w_e - φ_i φ_j)²
    v1 = sum(phi_prime(x[i]) * (x[i] - S[i])**2 for i in range(n))
    v2 = sum((alpha * w_vec[idx] - px[i] * px[j])**2 for idx, (i, j) in enumerate(edges))
    return -v1 - eps * v2

# ── δ-cohesive structure analysis (Theorem3_n.lean) ──
def analyze_cohesive(x, w_vec, edges, alpha):
    n = len(x); px = phi(x)
    # Sign partition (Theorem3 Part B)
    Vp = np.where(px > 1e-6)[0]; Vn = np.where(px < -1e-6)[0]; V0 = np.where(np.abs(px) <= 1e-6)[0]

    intra_pos, intra_neg, inter_pn = [], [], []
    for idx, (i, j) in enumerate(edges):
        wv = w_vec[idx]
        pi = px[i]; pj = px[j]
        if pi > 1e-6 and pj > 1e-6:      intra_pos.append(wv)
        elif pi < -1e-6 and pj < -1e-6:   intra_neg.append(wv)
        elif (pi > 1e-6 and pj < -1e-6) or (pi < -1e-6 and pj > 1e-6): inter_pn.append(wv)

    result = {'n_pos': len(Vp), 'n_neg': len(Vn), 'n_zero': len(V0),
              'Vp': Vp, 'Vn': Vn, 'V0': V0}
    if intra_pos and intra_neg and inter_pn:
        th = min(min(intra_pos), min(intra_neg))
        tl = max(inter_pn)
        result['theta_high'] = th
        result['theta_low'] = tl
        result['delta'] = th - tl
        result['cohesive'] = (th - tl) > 0
    return result

# ── Main simulation ──
def run_simulation(n=10, eps=0.5, alpha=0.5, p_edge=0.3, T_max=500.0, seed=42):
    rng = np.random.default_rng(seed)
    # Build random sparse graph
    edges = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < p_edge]
    m = len(edges)
    if m == 0: return None
    # Initial conditions — bimodal to produce non-trivial cohesive groups
    half = n // 2
    x0 = np.concatenate([rng.uniform(2.0, 4.0, size=half),   # V+ group
                          rng.uniform(-4.0, -2.0, size=n-half)]) # V- group
    rng.shuffle(x0)  # intermix node positions
    w0 = rng.uniform(-0.2, 0.2, size=m)
    z0 = np.concatenate([x0, w0])

    print(f"\n{'='*60}")
    print(f"n={n}, m={m}, eps={eps}, alpha={alpha}")
    print(f"E(0)={energy(x0, w0, edges, alpha):.4f}, Vdot(0)={compute_vdot(x0, w0, edges, eps, alpha):.4f}")

    # Solve ODE
    t_eval = np.linspace(0, T_max, 3000)
    sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                    args=(n, edges, eps, alpha), rtol=1e-9, atol=1e-12, max_step=1.0)
    if not sol.success:
        print(f"SOLVER FAILED: {sol.message}")
        return None

    T = sol.t; X = sol.y[:n, :]; W = sol.y[n:, :]
    # Energy history
    E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha) for k in range(len(T))])
    V_hist = np.array([compute_vdot(X[:, k], W[:, k], edges, eps, alpha) for k in range(len(T))])

    # Checks
    dE = np.diff(E_hist); n_increase = np.sum(dE > 1e-12)
    print(f"E({T[-1]:.0f})={E_hist[-1]:.6f}, E increases: {n_increase}/{len(dE)}")
    print(f"E non-increasing: {'PASS' if n_increase == 0 else 'FAIL'}")

    # Final state analysis
    x_f, w_f = X[:, -1], W[:, -1]; px_f = phi(x_f)
    # Vdot at final state
    v_f = compute_vdot(x_f, w_f, edges, eps, alpha)
    # Equilibrium check: max|dx|, max|dw|
    S_f = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        wij = w_f[idx]; S_f[i] += wij * px_f[j]; S_f[j] += wij * px_f[i]
    dx_max = np.max(np.abs(-x_f + S_f))
    dw_max = np.max([abs(eps * (px_f[i] * px_f[j] - alpha * w_f[idx])) for idx, (i, j) in enumerate(edges)])
    print(f"Convergence: max|dx|={dx_max:.2e}, max|dw|={dw_max:.2e}, Vdot_f={v_f:.2e}")

    # Cohesive analysis
    ca = analyze_cohesive(x_f, w_f, edges, alpha)
    print(f"Partition: V+={ca['n_pos']}, V-={ca['n_neg']}, V0={ca['n_zero']}")
    if 'cohesive' in ca:
        print(f"θ_high={ca['theta_high']:.4f}, θ_low={ca['theta_low']:.4f}, δ={ca['delta']:.4f}")
        print(f"δ-cohesive: {'YES' if ca['cohesive'] else 'DEGENERATE'}")

    # ── Visualization ──
    fig = plt.figure(figsize=(22, 12))
    gs = fig.add_gridspec(3, 4, hspace=0.35, wspace=0.3)

    # 1) Energy E(t) — Theorem 1 verification
    ax1 = fig.add_subplot(gs[0, 0])
    ax1.plot(T, E_hist, 'b-', lw=1.5)
    ax1.set_xlabel('t'); ax1.set_ylabel('E(t)')
    ax1.set_title(f'E(t) — Thm1 (E non-inc: {n_increase==0})')
    ax1.grid(alpha=0.3)

    # 2) Vdot(t) — negative sum of squares
    ax2 = fig.add_subplot(gs[0, 1])
    ax2.plot(T, V_hist, 'r-', lw=1.0, alpha=0.7)
    ax2.axhline(y=0, color='k', ls='--', lw=0.5)
    ax2.set_xlabel('t'); ax2.set_ylabel('Vdot(t)')
    ax2.set_title(f'Vdot(t) ≤ 0 (Thm1)')
    ax2.grid(alpha=0.3)

    # 3) φ(x_i) trajectories — convergence
    ax3 = fig.add_subplot(gs[0, 2])
    for i in range(min(n, 10)):
        ax3.plot(T, phi(X[i, :]), lw=0.8, label=f'x_{i}')
    ax3.set_xlabel('t'); ax3.set_ylabel('φ(x_i)')
    ax3.set_title(f'φ(x_i) convergence (Thm2)')
    ax3.grid(alpha=0.3)

    # 4) Weight trajectories
    ax4 = fig.add_subplot(gs[0, 3])
    for idx in range(min(m, 10)):
        ax4.plot(T, W[idx, :], lw=0.8)
    ax4.set_xlabel('t'); ax4.set_ylabel('w_e')
    ax4.set_title(f'w_e trajectories')
    ax4.grid(alpha=0.3)

    # 5) Network topology — cohesive structure (Theorem 3)
    ax5 = fig.add_subplot(gs[1, :2])
    G = nx.Graph()
    for idx, (i, j) in enumerate(edges): G.add_edge(i, j, weight=abs(w_f[idx]))
    pos = nx.spring_layout(G, seed=42, k=2.0)
    colors = ['red' if i in ca['Vp'] else 'blue' if i in ca['Vn'] else 'gray' for i in range(n)]
    sizes = [300.0 if i in ca['Vp'] or i in ca['Vn'] else 100.0 for i in range(n)]
    edge_colors = ['green' if w_f[idx] > 0.2 else 'red' if w_f[idx] < -0.1 else 'gray'
                   for idx, (i, j) in enumerate(edges)]
    edge_widths = [abs(w_f[idx]) * 3 for idx in range(len(edges))]
    nx.draw_networkx_nodes(G, pos, node_color=colors, node_size=sizes, ax=ax5)
    nx.draw_networkx_edges(G, pos, edge_color=edge_colors, width=edge_widths, alpha=0.5, ax=ax5)
    nx.draw_networkx_labels(G, pos, {i: str(i) for i in range(n)}, font_size=8, ax=ax5)
    ax5.set_title(f'Network at t=T — Green=intra(V+), Blue-edge=intra(V-), Red-edge=inter\n'
                  f'Red-node=V+, Blue-node=V-, Gray=V0, δ={ca.get("delta","N/A"):.2f}')
    ax5.axis('off')

    # 6) Weight matrix heatmap — block structure
    ax6 = fig.add_subplot(gs[1, 2])
    W_mat = np.zeros((n, n))
    for idx, (i, j) in enumerate(edges): W_mat[i, j] = W_mat[j, i] = w_f[idx]
    im = ax6.imshow(W_mat, cmap='RdBu_r', vmin=-1.0, vmax=1.0, aspect='auto')
    ax6.set_title(f'Weight matrix W* (t=T)')
    plt.colorbar(im, ax=ax6, shrink=0.8)

    # 7) Edge weight histogram — bimodal?
    ax7 = fig.add_subplot(gs[1, 3])
    ax7.hist(w_f, bins=30, color='steelblue', edgecolor='white', alpha=0.7)
    ax7.axvline(x=0, color='k', ls='--', lw=0.5)
    if 'theta_high' in ca:
        ax7.axvline(x=ca['theta_high'], color='green', ls=':', lw=1.5, label=f'θ_h={ca["theta_high"]:.2f}')
        ax7.axvline(x=ca['theta_low'], color='red', ls=':', lw=1.5, label=f'θ_l={ca["theta_low"]:.2f}')
        ax7.legend(fontsize=7)
    ax7.set_xlabel('w_e'); ax7.set_ylabel('count')
    ax7.set_title(f'Weight distribution (δ={ca.get("delta","N/A"):.2f})')

    # 8) Self-consistency check (Theorem 3 Part D)
    ax8 = fig.add_subplot(gs[2, :2])
    # φ(x_i) vs α*w_ij/(φ(x_j)) should be consistent
    for idx, (i, j) in enumerate(edges[:15]):
        if abs(px_f[j]) > 1e-6:
            pred = alpha * w_f[idx] / px_f[j]
            ax8.plot(i, px_f[i], 'ro', ms=6)
            ax8.plot(i, pred, 'bx', ms=4, alpha=0.5)
    ax8.set_xlabel('node index')
    ax8.set_ylabel('φ(x_i)')
    ax8.set_title('Self-consistency: φ(x_i) vs α·w_ij/φ(x_j) (red=actual, blue=predicted)')
    ax8.grid(alpha=0.3)

    # 9) Convergence metrics
    ax9 = fig.add_subplot(gs[2, 2:])
    ax9.axis('off')
    info_text = (
        f"Simulation Results\n{'='*40}\n"
        f"n={n}, m={m}, ε={eps}, α={alpha}\n"
        f"E(0)={E_hist[0]:.4f}, E(T)={E_hist[-1]:.6f}\n"
        f"E non-inc: {'PASS' if n_increase==0 else 'FAIL'}\n"
        f"max|dx(T)|={dx_max:.2e}, max|dw(T)|={dw_max:.2e}\n"
        f"Vdot(T)={v_f:.2e}\n"
        f"V+={ca['n_pos']}, V-={ca['n_neg']}, V0={ca['n_zero']}\n"
    )
    if 'cohesive' in ca:
        info_text += (f"θ_high={ca['theta_high']:.4f}\nθ_low={ca['theta_low']:.4f}\n"
                      f"δ={ca['delta']:.4f} → {'δ-COHESIVE' if ca['cohesive'] else 'degenerate'}")
    ax9.text(0.05, 0.95, info_text, transform=ax9.transAxes, fontsize=9,
             fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    fname = f"{OUT_DIR}/dgng_n{n}_e{eps}_a{alpha}_m{m}.png"
    fig.savefig(fname, dpi=120, bbox_inches='tight')
    plt.close(fig)
    print(f"Figure saved: {fname}")
    return {'E_hist': E_hist, 'V_hist': V_hist, 'cohesive': ca, 'converged': dx_max < 1e-6}

# ── Run suite ──
if __name__ == '__main__':
    configs = [
        (10, 0.5, 0.3, 0.35),    # stronger coupling (lower alpha → larger φ/α → stronger weights)
        (15, 0.5, 0.3, 0.3),
        (20, 0.8, 0.3, 0.25),
    ]
    for n, eps, alpha, p_edge in configs:
        run_simulation(n=n, eps=eps, alpha=alpha, p_edge=p_edge)
    print("\nAll simulations complete.")
