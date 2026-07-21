import Testlean.ExchangeableHoeffding.All

/-!
# Exchangeable Hoeffding formalization

This library is being developed as a Lean companion to the paper
`A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random Variables`.

The main import collects finite vector notation, the finite-population factor
`Gamma`, hypergeometric and Hamming-slice objects, and the high-level theorem
reductions.  Public results use descriptive names such as
`exchangeable_mgf_bound`, `exchangeable_tail_bound`, and
`admissible_constant_lower_bound`.
-/
