# Emergence of Stable Cohesive Structures in Sparse Dynamic Networks

**Lyapunov-based analysis and Lean 4 formalization** — proves that local Hebbian dynamics on sparse graphs necessarily self-organize into δ-cohesive equilibrium structures.

## Structure

### `lean4/` — Lean 4 Formal Verification
10 modules, 3,302 proof jobs, **zero `sorry`/`admit`**. All three theorems computer-verified at the highest standard of mathematical rigor.

```bash
cd lean4 && lake build DGNG
```

### `simulations/python/` — ODE Simulations
ER/BA/WS topologies, n=3–100. Phase transition at ε_c ≈ 0.138. δ ≈ 2/α = 6.67 across all topologies.

```bash
cd simulations && python python/dgng_pub_v2.py
```

### `simulations/wolfram/` — Symbolic Verification
Wolfram Engine 14.3: symbolic identity (n=3) + numerical sampling (n=4,5, 1000 configs each).

### `simulations/figures/` — 15 figures.

## Reference
*Emergence of Stable Cohesive Structures in Sparse Dynamic Networks: A Rigorous Lyapunov-Based Analysis* (2026)
