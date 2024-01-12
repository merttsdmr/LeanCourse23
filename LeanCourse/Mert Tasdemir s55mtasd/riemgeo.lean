-- First, we need to import the necessary libraries
import LeanCourse.Common
import Mathlib.Geometry

structure manifold :=
(space : Type)
(topology : topological_space space)
(smooth_atlas : set (local_homeomorph space ℝ)) -- smooth charts
(smooth_atlas_cover : space = ⋃₀ {u | ∃ e : local_homeomorph space ℝ, u = e.source ∧ e ∈ smooth_atlas})
(smooth_transition : ∀ e₁ e₂ : local_homeomorph space ℝ, e₁ ∈ smooth_atlas → e₂ ∈ smooth_atlas → e₁.source ∩ e₂.source ∈ e₁.to_fun ⁻¹' e₁.target ∩ e₂.to_fun ⁻¹' e₂.target)

-- Next, we define a tangent space at a point of the manifold
structure tangent_space (M : manifold) (p : M.space) :=
(vec_space : Type)
(add : vec_space → vec_space → vec_space)
(zero : vec_space)
(neg : vec_space → vec_space)
(scalar_mul : ℝ → vec_space → vec_space)

-- Then, we define an inner product on the tangent space
structure inner_product (M : manifold) (p : M.space) (T : tangent_space M p) :=
(ip : T.vec_space → T.vec_space → ℝ)
(ip_comm : ∀ v w, ip v w = ip w v)
(ip_pos_def : ∀ v, ip v v > 0 → v ≠ T.zero)
(ip_zero : ∀ v, ip v T.zero = 0)


-- A Riemannian metric is then a collection of inner products on each tangent space
def riemannian_metric (M : manifold) :=
∀ p : M.space, Σ' T : tangent_space M p, inner_product M p T

-- Angle between two vectors
noncomputable def angle (M : manifold) (g : riemannian_metric M) (p : M.space) (v w : (g p).1.vec_space) :=
Real.arccos ((g p).2.ip v w / (Real.sqrt ((g p).2.ip v v) * Real.sqrt ((g p).2.ip w w)))

structure levi_civita_connection (M : manifold) :=
  (connection : ∀ p : M.space, tangent_space M p → tangent_space M p → tangent_space M p)
  -- Add properties of the connection if needed
