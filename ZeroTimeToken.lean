import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Zero-Time Token & Residual Multiplier Model
Formalizing endogenous credit distortion, the 2018 policy-rate inversion,
and price discovery under 100% reserve backing.
-/

-- ============================================================================
-- 1. CORE PRIMITIVES & THEOREMS 1–3 (Token Decay, Duplication, Multiplier)
-- ============================================================================

structure LedgerState where
  tokens : ℝ
  claims : ℝ

-- Theorem 1: Holding a Zero-Time Token across time incurs residual cost R
def intrinsic_value (v0 R : ℝ) : ℝ := v0 - R

theorem zero_time_token_loss (v0 R : ℝ) (hR : R > 0) :
    intrinsic_value v0 R < v0 := by
  unfold intrinsic_value
  linarith

-- Theorem 2: Fractional lending duplicates claims on L2 above L1 tokens
def issue_loan (L2 : LedgerState) (Z : ℝ) : LedgerState :=
  { tokens := L2.tokens, claims := L2.claims + Z }

theorem ledger_duplication (X Z : ℝ) :
    let L1 : LedgerState := ⟨X, 0⟩
    let L2 : LedgerState := issue_loan ⟨0, X⟩ Z
    L2.claims - L1.tokens = Z := by
  dsimp [issue_loan]
  ring

-- Theorem 3: Geometric Residual Multiplier across n re-uses
def R_total (R r : ℝ) (n : ℕ) : ℝ :=
  R * (Finset.range (n + 1)).sum (fun k => (1 - r) ^ k)

-- Synthetic price distortion above the base T-bill residual R
def price_distortion (R r : ℝ) (n : ℕ) : ℝ :=
  R_total R r n - R

-- ============================================================================
-- 2. MACRO ABSORPTION & THEOREM 4 (ZIRP -> 2018 Crash -> Fed Pivot)
-- ============================================================================

structure MacroAbsorption where
  inflation_tax : ℝ      -- π: Currency debasement
  credit_default : ℝ     -- D: Asset crash / L2 write-downs
  equity_premium : ℝ     -- E_prem: Residual absorbed by asset prices

structure MacroStep where
  P : ℝ                  -- Central Bank policy rate
  R_legacy : ℝ           -- Accumulated residual overhang entering the period
  state : MacroAbsorption

-- Closed-system conservation law: all residual overhang must be absorbed
def conserves_residual (s : MacroStep) : Prop :=
  s.state.inflation_tax + s.state.credit_default + s.state.equity_premium = s.R_legacy

-- Endogenous liquidity support: drains proportionally when P > R_total
def R_supported (P R_tot R_legacy lam : ℝ) : ℝ :=
  R_legacy - lam * max 0 (P - R_tot)

-- Theorem 4A: Hiking P > R_total under rigid prices (π = 0) forces a crash (D > 0)
theorem tightening_scales_crash
  (s : MacroStep) (R_tot lam : ℝ)
  (h_lam : lam > 0)
  (h_cons : conserves_residual s)
  (h_no_pi : s.state.inflation_tax = 0)
  (h_eq_cap : s.state.equity_premium ≤ R_supported s.P R_tot s.R_legacy lam)
  (h_hike : s.P > R_tot) :
  s.state.credit_default ≥ lam * (s.P - R_tot) := by
  unfold conserves_residual at h_cons
  unfold R_supported at h_eq_cap
  have h_spread_pos : 0 ≤ s.P - R_tot := by linarith
  rw [max_eq_right h_spread_pos] at h_eq_cap
  linarith

-- Theorem 4B: Cutting P ≤ R_total (The Fed Pivot) restores full liquidity support
theorem pivot_restores_support
  (P_pivot R_tot R_legacy lam : ℝ)
  (h_cut : P_pivot ≤ R_tot) :
  R_supported P_pivot R_tot R_legacy lam = R_legacy := by
  unfold R_supported
  have h_spread_nonpos : P_pivot - R_tot ≤ 0 := by linarith
  rw [max_eq_left h_spread_nonpos]
  ring

-- ============================================================================
-- 3. THE 100% RESERVE SOLUTION (Zero Distortion & Price Discovery)
-- ============================================================================

-- Theorem 5A: At 100% reserves (r = 1), the multiplier collapses to base R
theorem full_reserve_collapses_multiplier (R : ℝ) (n : ℕ) :
    R_total R 1 n = R := by
  unfold R_total
  rw [Finset.sum_range_succ']
  simp

-- Theorem 5B: At 100% reserves, synthetic price distortion is identically zero
theorem full_reserve_zero_distortion (R : ℝ) (n : ℕ) :
    price_distortion R 1 n = 0 := by
  unfold price_distortion
  rw [full_reserve_collapses_multiplier]
  ring

-- Theorem 5C: Any split of R between token holders and banks preserves efficiency
structure ResidualAllocation where
  R_holder : ℝ   -- Passed to holders as spending power
  R_bank : ℝ     -- Retained by banks as growth-seeking liquidity

def achieves_price_discovery (alloc : ResidualAllocation) (R r : ℝ) (n : ℕ) : Prop :=
  alloc.R_holder + alloc.R_bank = R_total R r n ∧ price_distortion R r n = 0

theorem full_reserve_price_discovery
  (alloc : ResidualAllocation) (R : ℝ) (n : ℕ)
  (h_split : alloc.R_holder + alloc.R_bank = R) :
  achieves_price_discovery alloc R 1 n := by
  unfold achieves_price_discovery
  exact ⟨by rw [full_reserve_collapses_multiplier]; exact h_split,
         full_reserve_zero_distortion R n⟩

-- Theorem 5D: Under 100% reserves, a policy rate anchored to the T-bill yield (P ≤ R)
-- eliminates forced credit defaults without needing a "Fed Put"
theorem full_reserve_prevents_forced_crash
  (s : MacroStep) (R lam : ℝ) (n : ℕ)
  (h_no_overhang : s.R_legacy = R_total R 1 n)
  (h_anchored_rate : s.P ≤ R)
  (h_cons : conserves_residual s)
  (h_no_pi : s.state.inflation_tax = 0)
  (h_full_eq : s.state.equity_premium = R_supported s.P (R_total R 1 n) s.R_legacy lam) :
  s.state.credit_default = 0 := by
  rw [full_reserve_collapses_multiplier] at h_no_overhang h_full_eq
  rw [pivot_restores_support s.P R s.R_legacy lam h_anchored_rate] at h_full_eq
  unfold conserves_residual at h_cons
  linarith
