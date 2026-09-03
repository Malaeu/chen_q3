# Convention card — Goal 058 vectors, bases, pairings (2026-09-04)

Owner 2026-09-04: «столько нормировок; нужен быстрый доказанный переводчик». Converter with
self-checks: `docs/routeB_bus/phase5_codex/conventions.py` (all "must vanish" lines at 1e-60 on m=13).
Any report that uses a symbol below in another sense is wrong until it says so.

| symbol | basis / meaning | map to the others |
|---|---|---|
| `c_n`, n ∈ [−N, N] | FULL mode coefficients; `K(i,j) = τ(i,j)`, `τ(−i,−j) = τ(i,j)`, `τ(n,−n) = τ(n,0)` | — |
| `v = (v_0, v_n)` | EVEN orthonormal coordinates: `e_0 = mode_0`, `e_n = (mode_n + mode_{−n})/√2`; matrix `even_block()` | `v_0 = c_0`, `v_n = √2 c_n` (even c) |
| `w_n`, n ≥ 1 | ODD orthonormal coordinates: `o_n = (mode_n − mode_{−n})/√2`; matrix `odd_block = τ(i,j) − τ(i,−j)` | `w_n = √2 c_n` (odd c) |
| `R` | `(Rc)_n = c_n/n`, `(Rc)_0 = 0`, FULL; `1/n` is odd in `n`, so `R`: even → odd | in coordinates `w_n = v_n/n`; `diag(1/n)` on even coords IS `R` |
| `⟨Rc,(K−λ)Rc⟩_FULL` | quadratic form of the energy preflight (MAIN) | `= ⟨w,(K_odd − λ)w⟩`, `w_n = v_n/n` — the ODD block. NOT `⟨w,(K_even|_{n≥1} − λ)w⟩` (different form: residual 5e-2 on m=13) |
| `x_n = ξ_n/ξ_0` | FULL mode ratio; the P59 sample ratio `f_k(x_n) = (−1)^n x_n` carries NO √2 | `y_n = √2 x_n` |
| `y_n = v_n/v_0` | EVEN-coordinate ratio (`lattice_equation.py`, both preflights) | `x_n = y_n/√2` |
| `Δ_n` | `x_n − (Ξ-sample ratio)` in FULL ratios (verdicts f788d2fa, 99927f01: `Δ_n = f_k(x_n) − Ξ(x_n)/Ξ(0)` up to the sign `(−1)^n`) | energy preflight's `Δ` is in the same FULL ratio; blind re-derivation flags U1 = the √2 if `y` is mixed in |
| pairing | FULL Euclidean over `[−N,N]` = `c_0d_0 + 2Σ_{n≥1}c_nd_n` for equal parity = EVEN/ODD coordinate Euclidean | the "2Σ" of the energy preflight and the "plain Euclidean" of the blind re-derivation are the SAME number |
| odd diagonal | `τ(n,n) − τ(n,0)` (= `δ_n` of the energy preflight; = `D_n − P_n`, S7 is this definition) | even diagonal (n ≥ 1) is `τ(n,n) + τ(n,0)` |
| `λ₁, λ₂` | eigenvalues of the EVEN block (the builder never builds the odd block) | `λ_min(K_FULL)` = min over both blocks: OPEN whether it is the even `λ₁` (E7) |

Rule: a new report names its basis in the first line, or it is not read.
