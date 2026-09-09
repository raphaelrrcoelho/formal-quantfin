/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.DividendProblem

/-!
# Recovering a dividend-paying classical boundary from price/payoff contact

This is the dividend counterpart of the original zero-dividend contact
correspondence. It is a uniqueness statement for the boundary of a given
classical price, not existence or uniqueness of the PDE solution.

## Result

Public entry points include `contact_iff`, `contact_in_stock_units`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution

open Set

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem contact_iff (hp : DividendPutSolution k h p b) {x t : ℝ} (ht : 0 < t) :
    p x t = putPayoff x ↔ x ≤ b t := by
  constructor
  · intro he
    by_contra hx
    have hh := hp.continuation x t ht (lt_of_not_ge hx)
    rw [he] at hh
    exact (lt_irrefl _ hh)
  · intro hx
    rw [hp.exercise x t ht hx,putPayoff_of_nonpos (hx.trans (hp.boundary_nonpos ht))]

theorem contact_in_stock_units (hp : DividendPutSolution k h p b)
    {K S t : ℝ} (hK : 0 < K) (hS : 0 < S) (ht : 0 < t) :
    K*p (Real.log (S/K)) t = max (K-S) 0 ↔ S ≤ K*Real.exp (b t) := by
  rw [← putPayoff_in_stock_units hK hS,mul_right_inj' hK.ne',hp.contact_iff ht]
  rw [← Real.exp_le_exp,Real.exp_log (div_pos hS hK),div_le_iff₀ hK]
  rw [mul_comm K]

end MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution
