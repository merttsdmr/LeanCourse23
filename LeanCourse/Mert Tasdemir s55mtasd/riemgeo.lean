-- First, we need to import the necessary libraries
import LeanCourse.Common
-- We can start by defining a manifold
structure manifold :=
(space : Type)
(is_open : Set space → Prop)
(open_univ : is_open Set.univ)
(open_inter : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(open_union : ∀s t, is_open s → is_open t → is_open (s ∪ t))

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

-- We first need to define a derivative on the tangent space
structure derivative (M : manifold) (p : M.space) (T : tangent_space M p) :=
(df : (ℝ → T.vec_space) → ℝ)
(linearity : ∀ v w, df (T.add v w) = df v + df w)
(leibniz : ∀ (f g : ℝ → T.vec_space), df (λ x↦ T.add (f x) (g x)) = λ x↦ T.add (df f) (df g))

-- The Levi-Civita connection is a derivative that satisfies the product rule
structure levi_civita_connection (M : manifold) (g : riemannian_metric M) :=
(conn : ∀ p : M.space, derivative M p (g p).1)
(product_rule : ∀ p (f g : ℝ → (g p).1.vec_space), conn p (λ x↦ T.scalar_mul (f x) (g x)) =
                 λ x↦ T.add (T.scalar_mul (f x) (conn p g)) (T.scalar_mul (g x) (conn p f)))

-- The Christoffel symbols are the coefficients of the Levi-Civita connection in a given coordinate system
def christoffel_symbols (M : manifold) (g : riemannian_metric M) (nabla : levi_civita_connection M g) (coords : M.space → ℝ) :
  M.space → (g p).1.vec_space → (g p).1.vec_space → ℝ :=
λ p v w ↦ let e := coords p in nabla.conn p (λ x↦ T.scalar_mul (e x) v) w
