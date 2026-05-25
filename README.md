# DCNG: Emergence of Stable Cohesive Structures in Sparse Dynamic Networks

This repository contains the Lean4 formalization, simulation code, and verification scripts for the paper.

## Structure

### `lean4/` — Lean 4 Formal Verification
- 10 modules, 3,302 proof jobs, zero `sorry`/`admit`
- 4 axioms: LaSalle invariance principle (3) + energy chain rule (1)
- Build log: `build_full.log`

### `simulations/` — Numerical Verification  
- `dgng_pub_v2.py` — Publication-quality figure generation (15 figures)
- `dgng_final2.py` — Comprehensive ODE simulation (ER/BA/WS topologies, n=3-100)
- `verify_energy_deriv_numerical.py` — Python dE/dt identity verification (n=5,10,20)
- `verify_n3.wls`, `verify_n4.wls`, `verify_n5.wls` — Wolfram symbolic/numeric verification

## Build
```bash
cd lean4 && lake build DGNG
```

## License
MIT
