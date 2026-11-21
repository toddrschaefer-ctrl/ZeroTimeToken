# Zero-Time Token & Residual Multiplier Model (Lean 4)

A machine-verified formalization in **Lean 4** modeling settlement tokens, fractional-reserve ledger duplication, endogenous credit-cycle crashes (such as the 2018 policy-rate inversion), and price discovery under 100% reserve backing.

## Overview

Rather than treating macroeconomic cycles as driven purely by investor sentiment, this repository formalizes monetary plumbing as a conserved state machine across two ledger layers:

- **Layer 1 (`L1`):** Sovereign settlement tokens (base currency / T-bill-backed settlement instruments).
- **Layer 2 (`L2`):** Commercial bank deposit and credit claims issued against `L1` reserves.

### Core Theorems Proven

1. **Theorem 1 (`zero_time_token_loss`):** A zero-time settlement token held across time incurs an unmatched residual time cost $R$, reducing its intrinsic value to $V_{T_0} - R$.
2. **Theorem 2 (`ledger_duplication`):** Issuing a loan $Z$ against a deposit $X$ expands total nominal claims on `L2` to $X + Z$, exceeding actual `L1` settlement tokens by $Z$.
3. **Theorem 3 (`R_total` & `conserves_residual`):** Re-lending claims with reserve ratio $r$ across $n$ iterations multiplies the base residual into a system-wide overhang:
   $$R_{\text{total}} = R \sum_{k=0}^{n} (1 - r)^k$$
   By closed-system balance-sheet conservation, this residual must clear through currency inflation ($\pi$), credit defaults ($D$), or equity valuations ($E_{\text{prem}}$).
4. **Theorem 4 (`tightening_scales_crash` & `pivot_restores_support`):** When the central bank hikes the policy rate $P > R_{\text{total}}$ under price stability ($\pi = 0$), liquidity rotates into risk-free reserves, draining market support below legacy ZIRP overhang and mathematically forcing credit defaults ($D \ge \lambda(P - R_{\text{total}}) > 0$) until a policy pivot restores $P \le R_{\text{total}}$.
5. **Theorem 5 (`full_reserve_price_discovery` & `full_reserve_prevents_forced_crash`):** Setting the reserve requirement to 100% ($r = 1$) collapses the geometric multiplier ($R_{\text{total}} = R$) and eliminates synthetic price distortion ($R_{\text{total}} - R = 0$). Splitting the true underlying T-bill residual $R$ between token holders and banks preserves market price discovery and eliminates forced rate-hike defaults without requiring a central bank backstop.
6. - **Theorem 6 (`external_settlement_suppresses_inflation`):** Models open-economy settlement where scarce `L1` zero-time tokens force global trade to settle in short-term Treasury bills (`S_ext`), proving that offshore T-bill absorption (`S_ext > 0`) strictly suppresses domestic inflation (`π_open < π_closed`) rather than causing it.

## Repository Structure

```text
.
├── ZeroTimeToken.lean   # Complete Lean 4 definitions and machine-checked proofs
├── lakefile.toml        # Lake build configuration and Mathlib dependency
├── lean-toolchain       # Pinned Lean 4 compiler version
└── README.md            # Model overview and verification instructions
```

## How to Verify Locally

1. Install Lean 4 via [`elan`](https://github.com/leanprover/elan).
2. Clone this repository and fetch prebuilt Mathlib binaries:
   ```bash
   lake exe cache get
   lake build
   ```
3. A clean build with zero errors or `sorry` placeholders confirms that every theorem in `ZeroTimeToken.lean` is mathematically valid under the stated axioms.
