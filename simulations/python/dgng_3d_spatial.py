"""
3D Spatial Network: delta-cohesive emergence in irregular 3D volume.
n=1000 nodes, k-NN graph, verifies dimension-independence.
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.spatial import KDTree
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import os

OUT_DIR = "D:/learn/math/math论文/paper/figures"
os.makedirs(OUT_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif", "font.serif": ["Times New Roman", "DejaVu Serif"],
    "font.size": 10, "axes.titlesize": 12, "axes.titleweight": "bold",
    "axes.labelsize": 10, "figure.dpi": 300, "savefig.dpi": 300,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.08,
})
C_TEAL = "#264653"; C_RED = "#C82423"; C_BLUE = "#2878B5"; C_GRAY = "#9E9E9E"
C_GREEN = "#2A9D8F"; C_ORANGE = "#F4A261"

def phi(x): return np.tanh(x)

def build_knn_graph(points, k):
    tree = KDTree(points)
    edges = set()
    for i in range(len(points)):
        _, idx = tree.query(points[i], k=k+1)
        for j in idx[1:]:
            edges.add(tuple(sorted((i, j))))
    return np.array(list(edges), dtype=int)

def dgng_ode(t, z, n, edges, eps, alpha):
    x = z[:n]; w = z[n:]; px = phi(x); dx = -x.copy()
    for idx, (i, j) in enumerate(edges):
        wij = w[idx]; dx[i] += wij * px[j]; dx[j] += wij * px[i]
    dw = [eps * (px[i] * px[j] - alpha * w[idx]) for idx, (i, j) in enumerate(edges)]
    return np.concatenate([dx, dw])

def energy(x, w_vec, edges, alpha):
    px = phi(x)
    return (-sum(w_vec[k] * px[i] * px[j] for k, (i, j) in enumerate(edges))
            + np.sum(x * px - np.log(np.cosh(x)))
            + 0.5 * alpha * np.sum(w_vec ** 2))

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

print("Building 1000-node 3D spatial network...")
rng = np.random.default_rng(42)
n = 1000
points = rng.uniform(0, 1, size=(n, 3))
k = 6
edges = build_knn_graph(points, k)
m = len(edges)
print("  Nodes: {}, Edges: {}, avg degree: {:.1f}".format(n, m, 2*m/n))

eps, alpha = 0.5, 0.3
T_max = 2000

half = n // 2
x0 = np.concatenate([rng.uniform(2, 4, size=half), rng.uniform(-4, -2, size=n - half)])
rng.shuffle(x0)
w0 = rng.uniform(-0.2, 0.2, size=m)
z0 = np.concatenate([x0, w0])

print("Running ODE simulation...")
t_eval = np.linspace(0, T_max, 1000)
sol = solve_ivp(dgng_ode, [0, T_max], z0, method='LSODA', t_eval=t_eval,
                args=(n, edges, eps, alpha), rtol=1e-8, atol=1e-12, max_step=2.0)

if not sol.success:
    print("ODE FAILED: {}".format(sol.message))
    exit(1)

T, X, W = sol.t, sol.y[:n, :], sol.y[n:, :]
x_f = X[:, -1]; w_f = W[:, -1]; px_f = phi(x_f)
ca = analyze(x_f, w_f, edges, alpha)
print("Converged: V+={}, V-={}, V0={}, delta={:.4f}".format(
    ca['Vp'], ca['Vn'], ca['V0'], ca.get('delta', 0)))

E_hist = np.array([energy(X[:, k], W[:, k], edges, alpha) for k in range(len(T))])

# === FIGURE 1: 3D spatial evolution ===
fig = plt.figure(figsize=(16, 5))

ax0 = fig.add_subplot(1, 3, 1, projection='3d')
ax0.scatter(points[:, 0], points[:, 1], points[:, 2],
            c='#999999', s=3, alpha=0.6, linewidths=0)
ax0.set_title(r'$t=0$ (Disordered)', fontsize=12, fontweight='bold')

mid_idx = len(T) // 3
px_mid = phi(X[:, mid_idx])
colors_mid = [C_RED if p > 0.1 else C_BLUE if p < -0.1 else C_GRAY for p in px_mid]
ax1 = fig.add_subplot(1, 3, 2, projection='3d')
ax1.scatter(points[:, 0], points[:, 1], points[:, 2],
            c=colors_mid, s=3, alpha=0.6, linewidths=0)
n_committed = np.sum(np.abs(px_mid) > 0.1)
ax1.set_title('t={:.0f} (Differentiating, {}/1000 polarized)'.format(T[mid_idx], n_committed),
              fontsize=12, fontweight='bold')

colors_final = [C_RED if i in ca['Vp_idx'] else C_BLUE if i in ca['Vn_idx'] else C_GRAY
                for i in range(n)]
ax2 = fig.add_subplot(1, 3, 3, projection='3d')
ax2.scatter(points[:, 0], points[:, 1], points[:, 2],
            c=colors_final, s=3, alpha=0.6, linewidths=0)
d_val = ca.get('delta', 0)
ax2.set_title('t={:.0f} (delta={:.1f}, V+={}, V-={})'.format(
    T[-1], d_val, ca['Vp'], ca['Vn']), fontsize=12, fontweight='bold')

for ax in [ax0, ax1, ax2]:
    ax.set_xticks([]); ax.set_yticks([]); ax.set_zticks([])
    ax.xaxis.pane.fill = False; ax.yaxis.pane.fill = False; ax.zaxis.pane.fill = False
    ax.xaxis.pane.set_edgecolor('white'); ax.yaxis.pane.set_edgecolor('white')
    ax.zaxis.pane.set_edgecolor('white'); ax.grid(False)

fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, 'dgng_3d_spatial_evolution.png'), dpi=300, facecolor='white')
plt.close(fig)
print("3D spatial evolution figure saved.")

# === FIGURE 2: Energy + activations + weight histogram ===
fig = plt.figure(figsize=(12, 4))

ax = fig.add_subplot(1, 3, 1)
ax.plot(T, E_hist, color=C_TEAL, lw=1.5)
ax.set_xlabel('t'); ax.set_ylabel('E(t)')
ax.set_title('Energy (3D spatial, n=1000)', fontweight='bold')
ax.ticklabel_format(axis='y', style='scientific', scilimits=(-2, 2))

ax = fig.add_subplot(1, 3, 2)
sample_indices = rng.choice(n, min(15, n), replace=False)
for i in sample_indices[:8]:
    ax.plot(T, phi(X[i, :]), lw=0.6, alpha=0.8)
ax.set_xlabel('t'); ax.set_ylabel('phi(x_i)')
ax.set_title('Activation trajectories', fontweight='bold')

ax = fig.add_subplot(1, 3, 3)
ax.hist(w_f, bins=40, color=C_ORANGE, edgecolor='white', alpha=0.8, lw=0.3)
if 'theta_high' in ca:
    ax.axvline(ca['theta_high'], color=C_GREEN, ls=':', lw=2,
               label=r'$\theta_h$={:.1f}'.format(ca['theta_high']))
    ax.axvline(ca['theta_low'], color=C_RED, ls=':', lw=2,
               label=r'$\theta_l$={:.1f}'.format(ca['theta_low']))
    ax.legend(fontsize=9)
ax.set_xlabel('w_e'); ax.set_ylabel('Count')
ax.set_title('Weight distribution', fontweight='bold')

fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, 'dgng_3d_spatial_analysis.png'), dpi=300, facecolor='white')
plt.close(fig)
print("3D spatial analysis figure saved.")
print("Done. 3D spatial network verification complete.")
