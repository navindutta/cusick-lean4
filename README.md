# Cusick Conjecture — Lean 4 Formalization

A machine-checked formalization of **Cheng's 2026 proof** of Cusick's binary digit sum conjecture, in [Lean 4](https://leanprover.github.io/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## The theorem

For every integer $t \geq 1$, define

$$c_t := \lim_{N \to \infty} \frac{1}{N} \#\{0 \leq n < N : s_2(n + t) \geq s_2(n)\}$$

where $s_2(n)$ is the number of `1`-bits in the binary representation of $n$ (Hamming weight / popcount). **Cusick's conjecture** (2011) states $c_t > 1/2$ for all $t \geq 1$.

Cheng (2026) proved the stronger explicit bound:

$$c_t \geq \frac{1}{2} + 2^{-2s_2(t) - 1}$$

via an exact deconvolution of $s_2(n+t) - s_2(n)$ as a stopped random walk on the principal subsequence ideal of $t$.

## Status

| Component | File | Status |
|-----------|------|--------|
| `s₂` arithmetic foundations | `Cusick/SumOfDigits.lean` | ✅ **6 theorems, sorry-free** |
| Carry decomposition + subsequence ideals | `Cusick/BinaryStrings.lean` | 🔄 In progress |
| Density `cₜ` (Cesàro limit) | `Cusick/Density.lean` | 🔄 In progress |
| Main theorem | — | ⏳ Pending |

## What is proved so far

All proofs in `Cusick/SumOfDigits.lean` are **sorry-free** and verified by the Lean 4 kernel.

| Lean theorem | Mathematical statement |
|---|---|
| `Cusick.s2_zero` | $s_2(0) = 0$ |
| `Cusick.s2_one` | $s_2(1) = 1$ |
| `Cusick.s2_two` | $s_2(2) = 1$ |
| `Cusick.s2_odd` | $s_2(2n+1) = s_2(n) + 1$ (appending a 1-bit) |
| `Cusick.s2_even` | $s_2(2n) = s_2(n)$ for $n \neq 0$ (appending a 0-bit) |
| `Cusick.s2_succ_le` | $\forall n,\ s_2(n+1) \leq s_2(n) + 1$ (1-Lipschitz under increment) |

`s2_succ_le` captures the key carry propagation property: incrementing $n$ resets trailing 1-bits and sets one 0-bit, so the digit sum can only increase by at most 1. This is the foundational inequality the Cusick density bound rests on.

## Build

```bash
# Requires Lean 4 + Lake (install via elan: https://github.com/leanprover/elan)
git clone https://github.com/YOUR_HANDLE/cusick-lean4
cd cusick-lean4
lake build
```

**Axioms used** (same as all Mathlib proofs):
```
propext, Classical.choice, Quot.sound, funext
```
No sorry. No custom axioms.

## Project structure

```
cusick-lean4/
├── lakefile.lean              # Lake project (requires mathlib v4.14.0)
├── lean-toolchain             # leanprover/lean4:v4.14.0
├── Cusick/
│   ├── SumOfDigits.lean       # ✅ s₂ arithmetic (6 theorems)
│   ├── BinaryStrings.lean     # 🔄 carry decomposition, subsequence ideals
│   └── Density.lean           # 🔄 density cₜ and main theorem
└── README.md
```

## Reference

> Kaimin Cheng, *Proof of Cusick's Binary Digit Sum Conjecture*,  
> arXiv:**2606.23398** [math.NT], 22 June 2026.  
> https://arxiv.org/abs/2606.23398

Please also see Thomas W. Cusick's follow-up note confirming the proof and extending to the Tu–Deng conjecture (arXiv, 2026).

## Contributing

This is an active formalization project. If you want to contribute to `BinaryStrings.lean` (carry decomposition, Kummer's theorem in binary, subsequence ideals) or `Density.lean` (formalizing the Cesàro limit), open an issue or PR.

Proof discussion: [Lean Zulip](https://leanprover.zulipchat.com/) — see thread **"Cusick conjecture formalization"** in `#mathlib4`.

## License

Apache 2.0 (same as Mathlib).
