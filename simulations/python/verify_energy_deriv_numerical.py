"""
数值验证 DCNG 系统的 dE/dt = Vdot 恒等式
============================================
对随机 Erdos-Renyi 图，验证通过链式法则计算的 dE/dt 
与 Lyapunov 函数导数 Vdot 公式在浮点精度内一致，
且 Vdot <= 0。
"""

import numpy as np
from itertools import combinations


def generate_random_graph(n, p=0.3, seed=None):
    """生成 Erdos-Renyi 随机图，返回边列表（无向，i<j）"""
    rng = np.random.default_rng(seed)
    edges = []
    for i, j in combinations(range(n), 2):
        if rng.random() < p:
            edges.append((i, j))
    return edges


def compute_energy(x, W, edges, alpha):
    """
    计算能量函数（无向边各计一次的等价形式）：
    E = -Σ_{(i,j)∈E_undirected} w_ij·tanh(x_i)·tanh(x_j)
        + Σ_i [x_i·tanh(x_i) - log(cosh(x_i))]
        + (α/2) Σ_{(i,j)∈E_undirected} w_ij²
    
    注：论文中写 -(1/2)Σ 是对有向边双重求和的convention，
    实现中对无向边各计一次等价于系数-1。
    """
    tanh_x = np.tanh(x)
    
    # 耦合项: -Σ w_ij·φ_i·φ_j (无向边各计一次)
    E_coupling = 0.0
    for idx, (i, j) in enumerate(edges):
        E_coupling += W[idx] * tanh_x[i] * tanh_x[j]
    E_coupling *= -1.0
    
    # 自连接项: Σ_i [x_i·tanh(x_i) - log(cosh(x_i))]
    E_self = np.sum(x * tanh_x - np.log(np.cosh(x)))
    
    # 正则化项: (α/2)·Σ w_ij²
    E_reg = (alpha / 2.0) * np.sum(W**2)
    
    return E_coupling + E_self + E_reg


def compute_dynamics(x, W, edges, n, epsilon, alpha):
    """
    计算 ODE 右端：
    dx_i/dt = -x_i + Σ_{j∈N(i)} w_ij·tanh(x_j)
    dw_ij/dt = ε·(tanh(x_i)·tanh(x_j) - α·w_ij)
    """
    tanh_x = np.tanh(x)
    
    # 计算 dx/dt
    dxdt = -x.copy()
    for idx, (i, j) in enumerate(edges):
        # 无向边：i->j 和 j->i 都贡献
        dxdt[i] += W[idx] * tanh_x[j]
        dxdt[j] += W[idx] * tanh_x[i]
    
    # 计算 dW/dt
    dWdt = np.zeros(len(edges))
    for idx, (i, j) in enumerate(edges):
        dWdt[idx] = epsilon * (tanh_x[i] * tanh_x[j] - alpha * W[idx])
    
    return dxdt, dWdt


def compute_dEdt_chain_rule(x, W, edges, epsilon, alpha):
    """
    通过链式法则精确计算 dE/dt：
    dE/dt = Σ_i ∂E/∂x_i · ẋ_i + Σ_{(i,j)∈E} ∂E/∂w_ij · ẇ_ij
    
    偏导数（无向边各计一次）：
    ∂E/∂x_k = -sech²(x_k)·Σ_{j∈N(k)} w_kj·tanh(x_j) + x_k·sech²(x_k)
             = sech²(x_k)·[x_k - Σ_{j∈N(k)} w_kj·tanh(x_j)]
             = -sech²(x_k)·ẋ_k
    
    ∂E/∂w_ij = -tanh(x_i)·tanh(x_j) + α·w_ij
    """
    n = len(x)
    tanh_x = np.tanh(x)
    sech2_x = 1.0 - tanh_x**2  # sech²(x) = 1 - tanh²(x)
    
    # 计算动力学
    dxdt, dWdt = compute_dynamics(x, W, edges, n, epsilon, alpha)
    
    # 计算 ∂E/∂x_i
    # 先计算 Σ_{j∈N(i)} w_ij·tanh(x_j) 对每个节点 i
    neighbor_sum = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        neighbor_sum[i] += W[idx] * tanh_x[j]
        neighbor_sum[j] += W[idx] * tanh_x[i]
    
    # ∂E/∂x_k = sech²(x_k)·[x_k - Σ w·φ] = -sech²(x_k)·ẋ_k
    dEdx = sech2_x * (x - neighbor_sum)
    
    # 计算 ∂E/∂w_ij = -φ_i·φ_j + α·w_ij
    dEdW = np.zeros(len(edges))
    for idx, (i, j) in enumerate(edges):
        dEdW[idx] = -tanh_x[i] * tanh_x[j] + alpha * W[idx]
    
    # dE/dt = Σ ∂E/∂x_i · ẋ_i + Σ ∂E/∂w_ij · ẇ_ij
    dEdt = np.dot(dEdx, dxdt) + np.dot(dEdW, dWdt)
    
    return dEdt


def compute_vdot(x, W, edges, epsilon, alpha):
    """
    计算 Vdot 公式：
    Vdot = -Σ_i (1-tanh²(x_i))·(x_i - Σ_{j∈N(i)} w_ij·tanh(x_j))²
           - ε·Σ_{(i,j)∈edges} (α·w_ij - tanh(x_i)·tanh(x_j))²
    """
    n = len(x)
    tanh_x = np.tanh(x)
    sech2_x = 1.0 - tanh_x**2
    
    # 计算 x_i - Σ_{j∈N(i)} w_ij·tanh(x_j)
    neighbor_sum = np.zeros(n)
    for idx, (i, j) in enumerate(edges):
        neighbor_sum[i] += W[idx] * tanh_x[j]
        neighbor_sum[j] += W[idx] * tanh_x[i]
    
    residual_x = x - neighbor_sum  # 注意：这里是完整的 neighbor_sum，不是 1/2
    
    # 状态项：-Σ_i sech²(x_i)·(x_i - Σ_{j∈N(i)} w_ij·tanh(x_j))²
    vdot_state = -np.sum(sech2_x * residual_x**2)
    
    # 权重项：-ε·Σ_{(i,j)} (α·w_ij - tanh(x_i)·tanh(x_j))²
    vdot_weight = 0.0
    for idx, (i, j) in enumerate(edges):
        term = alpha * W[idx] - tanh_x[i] * tanh_x[j]
        vdot_weight += term**2
    vdot_weight *= -epsilon
    
    return vdot_state + vdot_weight


def run_verification(n, num_trials, p=0.3, epsilon=0.1, alpha=1.0):
    """
    对给定节点数n运行num_trials次随机验证。
    返回 (最大误差, Vdot是否全≤0, 所有试验通过)
    """
    max_error = 0.0
    all_vdot_nonpositive = True
    all_pass = True
    
    for trial in range(num_trials):
        rng = np.random.default_rng(trial * 1000 + n)
        
        # 生成随机图
        edges = generate_random_graph(n, p=p, seed=trial * 100 + n)
        
        if len(edges) == 0:
            continue  # 跳过没有边的图
        
        # 随机初始化
        x = rng.uniform(-2.0, 2.0, size=n)
        W = rng.uniform(-1.0, 1.0, size=len(edges))
        
        # 链式法则计算 dE/dt
        dEdt = compute_dEdt_chain_rule(x, W, edges, epsilon, alpha)
        
        # Vdot 公式
        vdot = compute_vdot(x, W, edges, epsilon, alpha)
        
        # 验证恒等式
        error = abs(dEdt - vdot)
        max_error = max(max_error, error)
        
        if error > 1e-10:
            all_pass = False
            print(f"  [FAIL] n={n}, trial={trial}: |dE/dt - Vdot| = {error:.2e}")
            print(f"         dE/dt = {dEdt:.15e}")
            print(f"         Vdot  = {vdot:.15e}")
        
        # 验证 Vdot ≤ 0
        if vdot > 1e-14:
            all_vdot_nonpositive = False
            print(f"  [WARN] n={n}, trial={trial}: Vdot = {vdot:.2e} > 0")
    
    return max_error, all_vdot_nonpositive, all_pass


def main():
    print("=" * 70)
    print("  DCNG 系统数值验证: dE/dt = Vdot 恒等式")
    print("=" * 70)
    print()
    print("参数: ε=0.1, α=1.0, 图密度p=0.3")
    print("验证条件: |dE/dt - Vdot| < 1e-10 且 Vdot ≤ 0")
    print()
    
    test_configs = [
        (5, 100),
        (10, 100),
        (20, 100),
    ]
    
    overall_pass = True
    overall_max_error = 0.0
    
    for n, num_trials in test_configs:
        print(f"--- 测试 n={n}, {num_trials} 次随机试验 ---")
        max_error, vdot_ok, passed = run_verification(n, num_trials)
        overall_max_error = max(overall_max_error, max_error)
        
        status = "PASS" if (passed and vdot_ok) else "FAIL"
        print(f"  结果: [{status}]  最大误差 = {max_error:.2e}  Vdot≤0: {vdot_ok}")
        print()
        
        if not (passed and vdot_ok):
            overall_pass = False
    
    print("=" * 70)
    if overall_pass:
        print("  ✓ 所有测试通过！")
    else:
        print("  ✗ 部分测试失败！")
    print(f"  全局最大误差: {overall_max_error:.2e}")
    print("=" * 70)


if __name__ == "__main__":
    main()
