import Mathlib


/-
This project formalizes the Power Iteration Algorithm over a finite
coordinate space using the rational field `ℚ` with tools from MathLib.
-/

open BigOperators

section PowerIterationAlgo

-- Declare variables
variable {n : Type*}
variable (A : Matrix n n ℚ) (x0 : n → ℚ)
variable (b : n → (n → ℚ)) (l : n → ℚ) (dom_idx : n)

-- Formalizations

/- Computes a discrete Taxicab (L1) norm of a rational vector. -/
def rationalNorm [Fintype n] (x : n → ℚ) : ℚ :=
  ∑ i : n, (x i).abs

/- A single step of the power iteration algorithm. Normalizes the
    transformed vector, with a check to return `x` unchanged if the norm is 0. -/
def PowerStep [Fintype n] (A : Matrix n n ℚ) (x : n → ℚ) : n → ℚ :=
  let transformed := A.mulVec x
  let norm_val := rationalNorm transformed
  if norm_val = 0 then x else norm_val⁻¹ • transformed

/- Generates the sequence of vectors by structural recursion over `ℕ`. -/
def PowerSequence [Fintype n] (A : Matrix n n ℚ) (x0 : n → ℚ) : ℕ → (n → ℚ)
  | 0 => x0
  | k + 1 => PowerStep A (PowerSequence A x0 k)

/- Verifies the vectors `b` form a valid linear eigenbasis for matrix `A`. -/
def IsEigenbasis [Fintype n] : Prop :=
  (∀ i, A.mulVec (b i) = l i • b i) ∧ LinearIndependent ℚ b

/- Verifies the eigenvalue at `dom_idx` strictly dominates all other magnitudes. -/
def IsStrictlyDominant : Prop :=
  ∀ i, i ≠ dom_idx → (l i).abs < (l dom_idx).abs

/- Verifies the starting vector has a non-zero projection along the dominant vector. -/
def InitialVectorValid (c : n → ℚ) : Prop :=
  c dom_idx ≠ 0


-- Assumptions

/- Unrolls the recursive sequence loop into an explicit scalar factor. -/
lemma PowerSequence_explicit_formula [Fintype n] [DecidableEq n] (k : ℕ) :
    ∃ (α : ℚ), α ≠ 0 ∧ PowerSequence A x0 k = α • (A ^ k).mulVec x0 := by
  sorry

/- Assumes sub-dominant fractions raised to power `k` annihilate to 0. -/
lemma Rational_ratio_damping_limit (i : n) (h_dom : IsStrictlyDominant l dom_idx)
(h_ne : i ≠ dom_idx) (k : ℕ) :
    (l i / l dom_idx) ^ k • b i = 0 := by
  sorry

-- Proofs

/- Proves the base-case execution state at step 0. -/
theorem PowerSequence_zero [Fintype n] (x0 : n → ℚ) :
    PowerSequence A x0 0 = x0 :=
  rfl

/- Proves that a matrix power distributes linearly across
    an eigenbasis summation, scaling each component path by `(l i) ^ k`. -/
theorem Eigenbasis_projection_formula [Fintype n] [DecidableEq n]
    (c : n → ℚ) (h_basis : IsEigenbasis A b l) (k : ℕ) :
    (A ^ k).mulVec (∑ i : n, c i • b i) = ∑ i : n, (c i * (l i) ^ k) • b i := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mulVec_smul]
  have h_pow : (A ^ k).mulVec (b i) = (l i) ^ k • b i := by
    induction k with
    | zero => simp
    | succ d ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h_basis.1 i, Matrix.mulVec_smul, ih, smul_smul]
      congr 1
      ring
  rw [h_pow, smul_smul]

/- Proves the validity of pulling out `(l dom_idx) ^ k` from the finset sum. -/
theorem Dominant_eigenvalue_factored [Fintype n] [DecidableEq n] (c : n → ℚ)
(_h_basis : IsEigenbasis A b l) (k : ℕ) (h_l0 : l dom_idx ≠ 0) :
    (∑ i : n, (c i * (l i) ^ k) • b i) = ((l dom_idx) ^ k) •
    (c dom_idx • b dom_idx + ∑ i : n,
    (if i = dom_idx then 0 else (c i * (l i / l dom_idx) ^ k) • b i)) := by
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ dom_idx)]
  conv_rhs =>
    rw [smul_add, Finset.smul_sum]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ dom_idx)]
    simp
  congr 1
  · simp [smul_smul]; ring_nf
  · rw [← Finset.sum_subset (Finset.sdiff_subset (s := Finset.univ) (t := {dom_idx})) (by
      intro x hx hne
      have heq : x = dom_idx := by
        by_contra h
        have : x ∈ Finset.univ \ {dom_idx} := by
          simp [Finset.mem_sdiff, h, hx]
        exact hne this
      simp [heq])]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
    calc
      (c x * (l x) ^ k) • b x
          = ((l dom_idx) ^ k * (c x * (l x / l dom_idx) ^ k)) • b x := by
            congr 1
            calc
              c x * (l x) ^ k = c x * ((l x / l dom_idx) * l dom_idx) ^ k := by
                rw [div_mul_cancel₀ _ h_l0]
              _ = (l dom_idx) ^ k * (c x * (l x / l dom_idx) ^ k) := by ring
      _ = if x = dom_idx then 0 else (l dom_idx) ^ k • (c x * (l x / l dom_idx) ^ k) • b x := by
        simp [hx.2, smul_smul]

/- Prove the global vector convergence identity of the Power Iteration Algorithm. -/
theorem PowerIteration_Rational_Convergence [Fintype n] [DecidableEq n]
    (c : n → ℚ)
    (h_basis : IsEigenbasis A b l)
    (_h_dom : IsStrictlyDominant l dom_idx)
    (_h_init : InitialVectorValid dom_idx c)
    (h_decomp : x0 = ∑ i : n, c i • b i)
    (h_l0 : l dom_idx ≠ 0)
    (k : ℕ) :
    ∃ (α : ℚ), PowerSequence A x0 k =
      (α * (l dom_idx)^k * c dom_idx) • b dom_idx +
      (α * (l dom_idx)^k) • ∑ i : n,
      (if i = dom_idx then 0 else c i • ((l i / l dom_idx) ^ k • b i)) := by
  obtain ⟨α, _, h_seq_eq⟩ := PowerSequence_explicit_formula A x0 k
  use α
  have h₁ := Eigenbasis_projection_formula (c := c) (h_basis := h_basis) (k := k)
  have h₂ := Dominant_eigenvalue_factored (c := c) (_h_basis := h_basis) (k := k) (h_l0 := h_l0)
  calc
    PowerSequence A x0 k
        = α • (A ^ k).mulVec x0 := h_seq_eq
    _ = α • (A ^ k).mulVec (∑ i, c i • b i) := by rw [h_decomp]
    _ = α • ∑ i, (c i * l i ^ k) • b i := by rw [h₁]
    _ = α • (l dom_idx ^ k • (c dom_idx • b dom_idx +
          ∑ i, (if i = dom_idx then 0 else
          (c i * (l i / l dom_idx) ^ k) • b i))) := congr_arg (α • ·) h₂
    _ = (α * l dom_idx ^ k * c dom_idx) • b dom_idx +
          (α * l dom_idx ^ k) • ∑ i,
          (if i = dom_idx then 0 else c i • ((l i / l dom_idx) ^ k • b i)) := by
      simp only [smul_add, Finset.smul_sum]
      congr 1
      · simp only [smul_smul]; ring_nf
      · refine Finset.sum_congr rfl ?_
        intro x _
        split_ifs with h
        · simp
        · simp only [smul_smul]; ring_nf

end PowerIterationAlgo
