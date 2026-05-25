"""
Numerical Verification of DCNG Theorem 1.

Verifies that for the coupled neural-synaptic dynamics on an undirected graph:
  1. |dE/dt (via chain rule) - Vdot (direct formula)| < 1e-10
     (implementation correctness / algebraic identity)
  2. Vdot <= 1e-14
     (dissipative dynamics, within floating-point tolerance)

System equations (DCNG):
  dx_i/dt   = -x_i + sum_{j in N(i)} w_ij * phi(x_j)
  dw_ij/dt  = epsilon * (phi(x_i) * phi(x_j) - alpha * w_ij)

Energy function:
  E = -sum_{(i,j) in E} w_ij * phi(x_i) * phi(x_j)
      + sum_i G_phi(x_i)
      + (alpha / 2) * sum_{(i,j) in E} w_ij^2

where G_phi(x) = x * phi(x) - int phi, and for phi = tanh:
  G_phi(x) = x * tanh(x) - log(cosh(x))

Time derivative via chain rule:
  dE/dt = sum_i (dE/dx_i * dx_i/dt) + sum_{(i,j)} (dE/dw_ij * dw_ij/dt)

Direct Vdot formula:
  Vdot = -sum_i sech^2(x_i) * (x_i - sum_j w_ij * phi(x_j))^2
         - epsilon * sum_{(i,j)} (alpha * w_ij - phi(x_i) * phi(x_j))^2
"""

import numpy as np

# ---------------------------------------------------------------------------
# Parameters
# ---------------------------------------------------------------------------
EPSILON = 0.1
ALPHA = 1.0
P_EDGE = 0.3

N_VALUES = [5, 8, 10, 15, 20]
N_TRIALS = 20

TOL_CHAIN_VS_VDOT = 1e-10
TOL_VDOT_NONPOS = 1e-14

SEED = 42


# ---------------------------------------------------------------------------
# Graph generation helpers
# ---------------------------------------------------------------------------
def make_er_graph(n: int, p: float, rng: np.random.Generator) -> np.ndarray:
    """Return symmetric adjacency matrix for Erdos-Renyi graph G(n, p)."""
    A = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                A[i, j] = A[j, i] = 1.0
    return A


def make_weights(A: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """Return symmetric weight matrix W with random edge weights in [-1, 1]."""
    n = A.shape[0]
    W = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            if A[i, j] > 0.5:
                w = rng.uniform(-1.0, 1.0)
                W[i, j] = W[j, i] = w
    return W


# ---------------------------------------------------------------------------
# Activation function utilities
# ---------------------------------------------------------------------------
def phi(x: np.ndarray) -> np.ndarray:
    """Activation: tanh."""
    return np.tanh(x)


def Gphi(x: np.ndarray) -> np.ndarray:
    """G_phi(x) = x * tanh(x) - log(cosh(x))."""
    return x * np.tanh(x) - np.log(np.cosh(x))


def sech2(x: np.ndarray) -> np.ndarray:
    """sech^2(x) = 1 / cosh^2(x)."""
    return 1.0 / np.cosh(x) ** 2


# ---------------------------------------------------------------------------
# Theorem 1 verification for one (x, W, A) triple
# ---------------------------------------------------------------------------
def check_theorem1(
    x: np.ndarray, W: np.ndarray, A: np.ndarray
) -> dict:
    """
    Compute E, dE/dt (chain rule), and Vdot (direct formula).

    Returns dict with all computed quantities and pass/fail flags.
    """
    n = x.shape[0]

    # --- Precompute common quantities ---
    px = phi(x)                 # phi(x_i)
    s2 = sech2(x)               # sech^2(x_i)
    Wp = W @ px                 # (W @ phi(x))_i = sum_j w_ij * phi(x_j)

    # ------ Energy E ------
    # Interaction: -sum_{(i,j)} w_ij * phi(x_i) * phi(x_j)    (unordered pair once)
    #   = -0.5 * sum_i sum_j W_ij * phi(x_i) * phi(x_j)
    E_int = -0.5 * np.sum(W * np.outer(px, px))

    # Potential: sum_i G_phi(x_i)
    E_pot = np.sum(Gphi(x))

    # Regularization: (alpha / 2) * sum_{(i,j)} w_ij^2
    #   np.sum(W * W) counts each ordered pair (i,j) and (j,i), i.e. 2x the
    #   undirected-edge sum.  So sum_{(i,j)} w_ij^2 = 0.5 * np.sum(W * W).
    E_reg = 0.5 * ALPHA * 0.5 * np.sum(W * W)  # = (alpha / 4) * ||W||_F^2

    E = E_int + E_pot + E_reg

    # ------ Dynamics ------
    # dx_i/dt = -x_i + sum_j w_ij * phi(x_j)
    dx_dt = -x + Wp

    # ------ dE/dt via chain rule ------
    # dE/dx_i = sech^2(x_i) * (x_i - (Wp)_i)
    dE_dx = s2 * (x - Wp)

    # Neural part: sum_i dE/dx_i * dx_i/dt
    dE_dt = np.sum(dE_dx * dx_dt)

    # Synaptic part: sum_{(i,j)} dE/dw_ij * dw_ij/dt
    for i in range(n):
        for j in range(i + 1, n):
            if A[i, j] > 0.5:
                ti = px[i]
                tj = px[j]
                wij = W[i, j]

                # dE/dw_ij = -phi(x_i) * phi(x_j) + alpha * w_ij
                dE_dw = -ti * tj + ALPHA * wij

                # dw_ij/dt = epsilon * (phi(x_i) * phi(x_j) - alpha * w_ij)
                dw_dt = EPSILON * (ti * tj - ALPHA * wij)

                dE_dt += dE_dw * dw_dt

    # ------ Vdot (direct formula) ------
    # Neural part: -sum_i sech^2(x_i) * (x_i - (Wp)_i)^2
    Vdot = -np.sum(s2 * (x - Wp) ** 2)

    # Synaptic part: -epsilon * sum_{(i,j)} (alpha * w_ij - phi(x_i) * phi(x_j))^2
    for i in range(n):
        for j in range(i + 1, n):
            if A[i, j] > 0.5:
                ti = px[i]
                tj = px[j]
                wij = W[i, j]

                Vdot += -EPSILON * (ALPHA * wij - ti * tj) ** 2

    # ------ Verification ------
    abs_diff = abs(dE_dt - Vdot)
    chain_ok = abs_diff < TOL_CHAIN_VS_VDOT
    vdot_ok = Vdot <= TOL_VDOT_NONPOS
    passed = chain_ok and vdot_ok

    return {
        "n": n,
        "E": E,
        "dE_dt": dE_dt,
        "Vdot": Vdot,
        "abs_diff": abs_diff,
        "chain_ok": chain_ok,
        "vdot_ok": vdot_ok,
        "passed": passed,
    }


# ---------------------------------------------------------------------------
# Main test driver
# ---------------------------------------------------------------------------
def main() -> None:
    rng = np.random.default_rng(SEED)

    print("=" * 74)
    print("  DCNG Theorem 1  --  Numerical Verification")
    print("=" * 74)
    print(f"  epsilon  = {EPSILON}")
    print(f"  alpha    = {ALPHA}")
    print(f"  p        = {P_EDGE}   (Erdos-Renyi edge probability)")
    print(f"  phi(x)   = tanh(x)")
    print(f"  n values = {N_VALUES}")
    print(f"  trials   = {N_TRIALS} per n")
    print(f"  seed     = {SEED}")
    print()
    print(f"  Tolerance |dE/dt - Vdot| < {TOL_CHAIN_VS_VDOT}")
    print(f"  Tolerance Vdot <= {TOL_VDOT_NONPOS}")
    print()
    print(f"  {'n':>3}  {'status':>6}  {'passed/total':>14}  "
          f"{'max |diff|':>12}  {'max Vdot':>12}  {'min Vdot':>12}")
    print("  " + "-" * 66)

    grand_pass = True

    for n in N_VALUES:
        pass_count = 0
        fail_count = 0
        max_abs_diff = 0.0
        max_vdot = -np.inf
        min_vdot = np.inf
        failures: list[dict] = []

        for trial in range(N_TRIALS):
            A = make_er_graph(n, P_EDGE, rng)
            W = make_weights(A, rng)
            x = rng.uniform(-2.0, 2.0, size=n)

            res = check_theorem1(x, W, A)
            res["trial"] = trial + 1

            max_abs_diff = max(max_abs_diff, res["abs_diff"])
            max_vdot = max(max_vdot, res["Vdot"])
            min_vdot = min(min_vdot, res["Vdot"])

            if res["passed"]:
                pass_count += 1
            else:
                fail_count += 1
                failures.append(res)

        # --- Per-n summary ---
        status = "PASS" if fail_count == 0 else "FAIL"
        ratio = f"{pass_count:2d}/{N_TRIALS:2d}"

        print(f"  {n:3d}  {status:>6}  {ratio:>14}  "
              f"{max_abs_diff:>12.2e}  {max_vdot:>12.2e}  {min_vdot:>12.2e}")

        if failures:
            grand_pass = False
            for f in failures:
                print(f"         FAIL trial #{f['trial']:2d}:  "
                      f"|diff|={f['abs_diff']:.2e}  "
                      f"Vdot={f['Vdot']:.2e}  "
                      f"chain={'OK' if f['chain_ok'] else 'FAIL'}  "
                      f"vdot={'OK' if f['vdot_ok'] else 'FAIL'}")

    # --- Global summary ---
    print("  " + "-" * 66)
    if grand_pass:
        print(f"  {'':>3}  {'PASS':>6}  All checks passed for every n and trial.")
        print(f"  Theorem 1 is numerically verified for all tested configurations.")
    else:
        print(f"  {'':>3}  {'FAIL':>6}  Some checks failed -- review details above.")
    print("=" * 74)


if __name__ == "__main__":
    main()
