import LeanCourse.Common
import LeanCourse.DiffGeom
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Basic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff
import Mathlib.LinearAlgebra.TensorProduct

/-First of all let us give the notions for manifolds in library.-/

#check LocalEquiv
#check SmoothManifoldWithCorners
#check ChartedSpace
#check TangentSpace



/-Manifold without boundary-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E E} [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]

theorem ModelWithCornerss.ext{𝕜 : Type u_1} :
∀ {inst : NontriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E} {inst_2 : NormedSpace 𝕜 E}
  {H : Type*} {inst_3 : TopologicalSpace H} (x y : ModelWithCorners 𝕜 E H),
  ↑x.toLocalEquiv = ↑y.toLocalEquiv → x.invFun = y.invFun → x.source = y.source → x.target = y.target → x = y := by
  exact fun {inst} {E} {inst_1} {inst_2} {H} {inst_3} x y a a_1 a_2 a_3 ↦
    ModelWithCorners.ext x y (congrArg LocalEquiv.toFun a) a_1 a_2 a_3


theorem ManifoldWithCorners.metrizableSpace{E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type u_2} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
TopologicalSpace.MetrizableSpace M := by
  haveI := I.locallyCompactSpace; haveI := ChartedSpace.locallyCompactSpace H M
  haveI := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigma_compact H M
  exact TopologicalSpace.metrizableSpace_of_t3_second_countable M

/- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
#check ModelWithCorners.Boundaryless

/- Let's define the Riemannian metric structure -/

variable (M I) in
structure RiemannianMetric  where
  (metric : M → (SmoothSection I E (TangentSpace I (M := M))) → (SmoothSection I E (TangentSpace I (M := M))) → ℝ)
  (symmetry : ∀ (x : M) (v w : SmoothSection I E (TangentSpace I (M := M))), metric x v w = metric x w v)
  (positive_definite : ∀ (x : M) (v : SmoothSection I E (TangentSpace I (M := M))), v ≠ 0 → metric x v v > 0)
  (zero_at_zero : ∀ (x : M) , metric x 0 0 = 0)
  (linearity : ∀ (x : M) (a : ℝ ) ( u w : SmoothSection I E (TangentSpace I (M := M))), metric x (a•u) w= a * metric x u w)
  (linearity2 : ∀ (x : M) ( u v w : SmoothSection I E (TangentSpace I (M := M))), metric x (u+v) w= metric x u w + metric x v w)

/-Pointwise Riemmannian metric-/
variable (g : RiemannianMetric I M) in
def PtWiseMetric (X Y : SmoothSection I E (TangentSpace I (M := M))) : M → ℝ :=
  fun x ↦ g.metric x X Y

/-We need to define multiplication of a smooth seciton and function as in lean it did not defined.-/
noncomputable section
open Manifold Bundle Filter
variable (f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯) (x : M)
instance : SMul (C^⊤⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (SmoothSection I E (TangentSpace I (M := M))) := by
  refine' ⟨fun f X ↦ ⟨fun x ↦ f x • X x, _⟩⟩
  intro x₀
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX ⊢
  set V := TangentSpace I (M := M)
  set e := trivializationAt E V x₀
  refine' ((f.2 x₀).smul hX).congr_of_eventuallyEq _
  refine' eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt E V x₀) _
  intro x hx
  apply (e.linear ℝ hx).2

/-This multiplication gives a smooth section-/
example (X : SmoothSection I E (TangentSpace I (M := M))) :
    SmoothSection I E (TangentSpace I (M := M)) := f • X

#check HSMul


/-Now let us define connection on a manifold-/
variable (M I) in
structure Connection where
  (conn : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) → SmoothSection I E (TangentSpace I (M := M)))
  (linear_first_arg : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M)))(a : ℝ), conn (a • X+Z) Y= a • conn X Y+conn Z Y )
  (linear_second_arg : ∀ (X Y Z: SmoothSection I E (TangentSpace I (M := M)))(a : ℝ), conn X (a• Y+Z)=a • (conn X Y)+conn X Z)
  (leibniz_rule : ∀ (x: M)(X Y : SmoothSection I E (TangentSpace I (M := M)) )(f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯), conn X (f • Y) = f • conn X Y + (mfderiv I 𝓘(ℝ, ℝ) f x (X x) • Y ) )


/-Lie bracket structure-/
variable (M I) in
structure LieBracket where
  (bracket : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) →  SmoothSection I E (TangentSpace I (M := M)))
  (antisymmetry : ∀ (X Y : SmoothSection I E (TangentSpace I (M := M))) , bracket X Y = -bracket Y X )
  (Jacobi_identity : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M))) , bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0)


#check Connection
#check LieBracket

/-Torsion tensor in order to define Levi Civita connection-/
variable (conn : Connection I M) (brack : LieBracket I M) in
def TorsionTensor (X Y : SmoothSection I E (TangentSpace I (M := M))) : SmoothSection I E (TangentSpace I (M := M)) :=
  conn.conn X Y - conn.conn Y X - brack.bracket X Y


variable (M I) in
structure LeviCivitaConnection (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) where
  (connection : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) → SmoothSection I E (TangentSpace I (M := M)))
  (linear_first_arg : ∀ (a : ℝ) (X Y : SmoothSection I E (TangentSpace I (M := M))), connection (a • X) Y= a • connection X Y)
  (linear_first_arg2 : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M))), connection (X+Z) Y= (connection X Y)+connection Z Y)
  (linear_second_arg : ∀ (X Y Z: SmoothSection I E (TangentSpace I (M := M))) (a : ℝ), connection X (a• Y+Z)=a • (connection X Y)+connection X Z)
  (leibniz_rule : ∀ (x: M)(X Y : SmoothSection I E (TangentSpace I (M := M)) )(f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯), connection X (f • Y) = f • connection X Y + (mfderiv I 𝓘(ℝ, ℝ) f x (X x) • Y ) )
  (metric_compatible : ∀ (x : M) (X Y Z : SmoothSection I E (TangentSpace I (M := M))),  (mfderiv I 𝓘(ℝ, ℝ) (PtWiseMetric g X Y) x (Z x))= g.metric x (conn.conn Z X) Y+ g.metric x X (conn.conn Z Y))
  (torsion_free : ∀ (X Y : SmoothSection I E (TangentSpace I (M := M))), TorsionTensor conn brack X Y = 0)


example (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) (nabla : LeviCivitaConnection I M g conn brack) (Y : SmoothSection I E (TangentSpace I (M := M))) :
 nabla.connection 0 Y = 0 := sorry






variable (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) (nabla : LeviCivitaConnection I M g conn brack) in
def CurvatureTensor31 (X Y Z: SmoothSection I E (TangentSpace I (M := M))) : SmoothSection I E (TangentSpace I (M := M)) :=
  nabla.connection X (nabla.connection Y Z) - nabla.connection Y (nabla.connection X Z) - nabla.connection (brack.bracket X Y) Z
variable (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) (nabla : LeviCivitaConnection I M g conn brack) in
def CurvatureTensor40 (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) : ℝ :=
  g.metric x (CurvatureTensor31 g conn brack nabla X Y Z) W





lemma ex1 (brack: LieBracket I M) (X Y : SmoothSection I E (TangentSpace I (M := M))) : brack.bracket X Y= -1 • brack.bracket Y X := by{
  rw[LieBracket.antisymmetry]
  simp
}

lemma ex2 (g : RiemannianMetric I M) (X Y : SmoothSection I E (TangentSpace I (M := M)) ) : g.metric x (-X) Y =-g.metric x X Y := by{
  have lem1 : -X=-1 • X := by exact (neg_one_zsmul X).symm
  calc g.metric x (-X) Y = g.metric x (-1 • X) Y := by rw [lem1]
                      _ = -1 * g.metric x X Y:= by{
                        rw [←@RiemannianMetric.linearity]
                        simp
                      }
                      _ = -g.metric x X Y := by simp

}


lemma ex3 (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) (nabla : LeviCivitaConnection I M g conn brack) (X Y Z : SmoothSection I E (TangentSpace I (M := M))) :
nabla.connection (-X) Y = - nabla.connection X Y := by{





  calc nabla.connection (-X) Y = nabla.connection (-1 • X) Y := by simp
                              _ = -1 • nabla.connection X Y := by{
                              rw [@neg_one_zsmul]
                              rw [@neg_one_zsmul]
                              rw [@eq_neg_iff_add_eq_zero]
                              rw [← @LeviCivitaConnection.linear_first_arg2]
                              simp
                              let P : SmoothSection I E (TangentSpace I (M := M)) := by exact X
                              have : nabla.connection 0 Y = nabla.connection (0 • P) Y := rfl
                              rw[this]
                              sorry

                              }
                              _ = - nabla.connection X Y := by simp
}



/- R(X,Y,Z,W)=-R(Y,X,Z,W)    -/
example (g : RiemannianMetric I M) (conn : Connection I M) (brack: LieBracket I M) (nabla : LeviCivitaConnection I M g conn brack) (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) : CurvatureTensor40 g conn brack nabla x X Y Z W = - CurvatureTensor40 g conn brack nabla x Y X Z W := by
{
  rw[CurvatureTensor40]
  rw[CurvatureTensor40]
  rw[CurvatureTensor31]
  have : nabla.connection (brack.bracket X Y) Z = - nabla.connection (brack.bracket Y X) Z :=by{
    rw[brack.antisymmetry]
    rw[ex3]
    exact X
  }
  rw[this]
  simp
  rw[←ex2]
  have : (LeviCivitaConnection.connection nabla X (LeviCivitaConnection.connection nabla Y Z) -
        LeviCivitaConnection.connection nabla Y (LeviCivitaConnection.connection nabla X Z) +
      LeviCivitaConnection.connection nabla (LieBracket.bracket brack Y X) Z) = -CurvatureTensor31 g conn brack nabla Y X Z := by{
        rw [@sub_add]
        rw[CurvatureTensor31]
        congr
        simp
        rw [@sub_eq_sub_iff_sub_eq_sub]
        simp
      }

  rw [this]
}



#check OrthonormalBasis


open BigOperators Finset

def myBasis := Basis.ofVectorSpace (SmoothSection I E (TangentSpace I (M := M)))

#check myBasis
