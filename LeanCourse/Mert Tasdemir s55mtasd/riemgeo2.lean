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

/-Manifolds are perfect objects because one can always equip them with a metric-/
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
class RiemannianMetric  where
  (metric : M → (SmoothSection I E (TangentSpace I (M := M))) → (SmoothSection I E (TangentSpace I (M := M))) → ℝ)
  (symmetry : ∀ (x : M) (v w : SmoothSection I E (TangentSpace I (M := M))), metric x v w = metric x w v)
  (positive_definite : ∀ (x : M) (v : SmoothSection I E (TangentSpace I (M := M))), v ≠ 0 → metric x v v > 0)
  (zero_at_zero : ∀ (x : M) , metric x 0 0 = 0)
  (linearity : ∀ (x : M) (a : ℝ ) ( u w : SmoothSection I E (TangentSpace I (M := M))), metric x (a•u) w= a * metric x u w)
  (linearity2 : ∀ (x : M) ( u v w : SmoothSection I E (TangentSpace I (M := M))), metric x (u+v) w= metric x u w + metric x v w)

open RiemannianMetric

/-Pointwise Riemmannian metric-/
variable [g : RiemannianMetric I M] in
def PtWiseMetric (X Y : SmoothSection I E (TangentSpace I (M := M))) : M → ℝ :=
  fun x ↦ metric x X Y

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
class Connection where
  (conn : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) → SmoothSection I E (TangentSpace I (M := M)))
  (linear_first_arg : ∀ (a : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯) (X Y : SmoothSection I E (TangentSpace I (M := M))), conn (a • X) Y= a • conn X Y )
  (linear_first_arg2 : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M))), conn (X+Y) Z= conn X Z + conn Y Z)
  (linear_second_arg : ∀ (X Y Z: SmoothSection I E (TangentSpace I (M := M)))(a : ℝ), conn X (a• Y+Z)=a • (conn X Y)+conn X Z)
  (leibniz_rule : ∀ (x: M)(X Y : SmoothSection I E (TangentSpace I (M := M)) )(f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯), conn X (f • Y) = f • conn X Y + (mfderiv I 𝓘(ℝ, ℝ) f x (X x) • Y ) )

notation "∇_" => Connection.conn

variable [Connection I M]
example (X Y : SmoothSection I E (TangentSpace I (M := M))) : SmoothSection I E (TangentSpace I (M := M)) :=
  ∇_ X Y - ∇_ Y X

/-Lie bracket structure-/
variable (M I) in
class LieBracket where
  (bracket : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) →  SmoothSection I E (TangentSpace I (M := M)))
  (antisymmetry : ∀ (X Y : SmoothSection I E (TangentSpace I (M := M))) ,bracket X Y = -bracket Y X )
  (Jacobi_identity : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M))) , bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0)
  (linearity : ∀ (a b : ℝ) (X Y Z : SmoothSection I E (TangentSpace I (M := M))), bracket (a•X+b•Y) Z =a • bracket X Z + b • bracket Y Z)
  (product : ∀ (x : M) (X Y : SmoothSection I E (TangentSpace I (M := M))) (f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯), bracket X (f • Y)= f • bracket X Y + (mfderiv I 𝓘(ℝ, ℝ) f x (X x) • Y ))

variable (M I) in
instance [brack : LieBracket I M] : Bracket ( SmoothSection I E (TangentSpace I (M := M))) ( SmoothSection I E (TangentSpace I (M := M))):= by {
  exact ⟨LieBracket.bracket⟩
}

#check Bracket
#check Connection
#check LieBracket

/-Torsion tensor in order to define Levi Civita connection-/
variable [conn : Connection I M] [brack : LieBracket I M]
def TorsionTensor (X Y : SmoothSection I E (TangentSpace I (M := M))) : SmoothSection I E (TangentSpace I (M := M)) :=
  ∇_ X Y - ∇_ Y X - ⁅ X, Y⁆

/-Levi Civita Connection as a definition-/
variable (M I)  in
class LeviCivitaConnection [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] where
  (connection : SmoothSection I E (TangentSpace I (M := M))→ SmoothSection I E (TangentSpace I (M := M)) → SmoothSection I E (TangentSpace I (M := M)))
  (linear_first_arg : ∀ (a : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯) (X Y : SmoothSection I E (TangentSpace I (M := M))), connection (a • X) Y= a • connection X Y)
  (linear_first_arg2 : ∀ (X Y Z : SmoothSection I E (TangentSpace I (M := M))), connection (X+Y) Z= (connection X Z)+connection Y Z)
  (linear_second_arg : ∀ (X Y Z: SmoothSection I E (TangentSpace I (M := M))) (a : ℝ), connection X (a• Y+Z)=a • (connection X Y)+connection X Z)
  (leibniz_rule : ∀ (x: M)(X Y : SmoothSection I E (TangentSpace I (M := M)) )(f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯), connection X (f • Y) = f • connection X Y + (mfderiv I 𝓘(ℝ, ℝ) f x (X x) • Y ) )
  (metric_compatible : ∀ (x : M) (X Y Z : SmoothSection I E (TangentSpace I (M := M))),  (mfderiv I 𝓘(ℝ, ℝ) (PtWiseMetric X Y) x (Z x))= metric x (conn.conn Z X) Y+ metric x X (conn.conn Z Y))
  (torsion_free : ∀ (X Y : SmoothSection I E (TangentSpace I (M := M))), TorsionTensor X Y = 0)


notation "∇_LC" => LeviCivitaConnection.connection

/-Showing Levi Civita connection is a connection-/
variable [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M]
instance (nabla : LeviCivitaConnection I M) : Connection I M where
conn := by exact ∇_LC
linear_first_arg := by exact nabla.linear_first_arg
linear_first_arg2 := by exact nabla.linear_first_arg2
linear_second_arg := by exact nabla.linear_second_arg
leibniz_rule := by exact nabla.leibniz_rule




/-In few examples and lemmas one can find some necessary basic properties for our future formalizations
Most of are direct conclusions of properties of concepts we gave so far.-/
example [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (Y : SmoothSection I E (TangentSpace I (M := M))) :
 ∇_LC 0 Y = 0 := by {
  have : ∇_LC 0 Y = ∇_LC (0 • Y) Y := by simp
  calc ∇_LC (0 • Y) Y = 0 • ∇_LC Y Y := by{
    rw [← @ofNat_zsmul]
    sorry
  }
                                _= 0 := rfl
 }
lemma ex1 [brack: LieBracket I M] (X Y : SmoothSection I E (TangentSpace I (M := M))) : ⁅ X,Y⁆= -1 • brack.bracket Y X := by{
  rw[LieBracket.antisymmetry]
  simp
  exact rfl
}

lemma ex2 [g : RiemannianMetric I M] (X Y : SmoothSection I E (TangentSpace I (M := M)) ) : metric x (-X) Y =-metric x X Y := by{
  have lem1 : -X=-1 • X := by exact (neg_one_zsmul X).symm
  calc metric x (-X) Y = metric x (-1 • X) Y := by rw [lem1]
                      _ = -1 * metric x X Y:= by{
                        rw [←@RiemannianMetric.linearity]
                        simp
                      }
                      _ = -metric x X Y := by simp

}


lemma ex3 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (X Y Z : SmoothSection I E (TangentSpace I (M := M))) :
∇_LC (-X) Y = - ∇_LC X Y := by{



  calc ∇_LC (-X) Y = ∇_LC (-1 • X) Y := by simp
                              _ = -1 • ∇_LC X Y := by{
                              rw [@neg_one_zsmul]
                              rw [@neg_one_zsmul]
                              rw [@eq_neg_iff_add_eq_zero]
                              rw [← @LeviCivitaConnection.linear_first_arg2]
                              simp
                              let P : SmoothSection I E (TangentSpace I (M := M)) := by exact X
                              have : ∇_LC 0 Y = ∇_LC (0 • P) Y := rfl
                              rw[this]
                              sorry

                              }
                              _ = - ∇_LC X Y := by simp
}

lemma ex4 (g : RiemannianMetric I M) (X : SmoothSection I E (TangentSpace I (M := M)) ) : metric x 0 X=0 := by{
  calc metric x 0 X = metric x (0 • X) X := by exact rfl
                      _= 0* metric x X X := by {
                        rw[←g.linearity]
                        simp
                      }
                      _=0 := by simp
}









/-Riemann curvature tensor of type (3,1)-/

variable [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] in
def CurvatureTensor31 (X Y Z: SmoothSection I E (TangentSpace I (M := M))) : SmoothSection I E (TangentSpace I (M := M)) :=
  ∇_LC X (∇_LC Y Z) - ∇_LC Y (∇_LC X Z) - ∇_LC (⁅ X,Y ⁆) Z





/-Some properties of Riemmann curvature tensor.-/
variable (x : M) [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] in
lemma prop1_R31 (X Y Z : SmoothSection I E (TangentSpace I (M := M))) (f : C^⊤⟮I, M; 𝓘(ℝ , ℝ ), ℝ⟯) : CurvatureTensor31 X (f • Y) Z=f • CurvatureTensor31 X Y Z := by{
  rw[CurvatureTensor31]
  sorry

}






/- Riemann curvature tensor of type (4,0) -/

variable [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] in
def CurvatureTensor40 (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) : ℝ :=
  metric x (CurvatureTensor31 X Y Z) W









/-Main Theorems we aim to prove-/

/- R(X,Y,Z,W)=-R(Y,X,Z,W)    -/
lemma SkewSymR401 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M)))
: CurvatureTensor40 x X Y Z W = - CurvatureTensor40 x Y X Z W := by
{
  rw[CurvatureTensor40]
  rw[CurvatureTensor40]
  rw[CurvatureTensor31]
  have : ∇_LC (⁅ X,Y⁆) Z = - ∇_LC (brack.bracket Y X) Z :=by{
    rw[brack.antisymmetry]
    rw[ex3]
    exact neg_eq_iff_eq_neg.mp rfl
    exact X
  }
  rw[this]
  simp
  rw[←ex2]
  have : (∇_LC X (∇_LC Y Z) -
        ∇_LC Y (∇_LC X Z) +
      ∇_LC (LieBracket.bracket Y X) Z) = -CurvatureTensor31 Y X Z := by{
        rw [@sub_add]
        rw[CurvatureTensor31]
        congr
        simp
        rw [@sub_eq_sub_iff_sub_eq_sub]
        simp
        exact rfl
      }

  rw [this]
}

lemma SkewSymR402 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) : CurvatureTensor40 x X Y Z W = - CurvatureTensor40 x X Y W Z := by sorry

lemma SymInR40 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) :
 CurvatureTensor40 x X Y Z W = CurvatureTensor40 x Y X W Z  := by {
  rw[SkewSymR401]
  rw[SkewSymR402]
  simp
 }


lemma BianchiR31 [g : RiemannianMetric I M]  [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z : SmoothSection I E (TangentSpace I (M := M))) : CurvatureTensor31 X Y Z + CurvatureTensor31 Y Z X + CurvatureTensor31 Z X Y = 0 := by{
  rw[CurvatureTensor31]
  rw[CurvatureTensor31]
  rw[CurvatureTensor31]
  have : TorsionTensor X Y = 0 := by {
      rw[nabla.torsion_free]
  }
  calc ∇_LC X (∇_LC Y Z) -
          ∇_LC Y (∇_LC X Z) -
        ∇_LC (LieBracket.bracket X Y) Z +
      (∇_LC Y (∇_LC Z X) -
          ∇_LC Z (∇_LC Y X) -
        ∇_LC (LieBracket.bracket Y Z) X) +
    (∇_LC Z (∇_LC X Y) -
        ∇_LC X (∇_LC Z Y) -
      ∇_LC (LieBracket.bracket Z X) Y) = ∇_LC X (∇_LC Y Z-∇_LC Z Y)+ ∇_LC Y (∇_LC X Z-∇_LC Z X)+ ∇_LC Z (∇_LC Y X-∇_LC X Y)-∇_LC (⁅ X,Y⁆) Z-∇_LC (brack.bracket Y Z) X-∇_LC (brack.bracket Z X) Y := sorry
      _=∇_LC X (brack.bracket Y Z)+ ∇_LC Y (brack.bracket X Z)+∇_LC Z (brack.bracket Y X)-∇_LC (⁅ X,Y⁆) Z-∇_LC (brack.bracket Y Z) X-∇_LC (brack.bracket Z X) Y := sorry
      _=0 := sorry
}

lemma BianchiR40 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) :
 CurvatureTensor40 x X Y Z W + CurvatureTensor40 x Y Z X W + CurvatureTensor40 x Z X Y W = 0 := by{
  rw[CurvatureTensor40]
  rw[CurvatureTensor40]
  rw[CurvatureTensor40]
  calc metric x (CurvatureTensor31 X Y Z) W +
      metric x (CurvatureTensor31 Y Z X) W +
    metric x (CurvatureTensor31 Z X Y) W = metric x ((CurvatureTensor31 X Y Z)+(CurvatureTensor31 Y Z X)+(CurvatureTensor31  Z X Y)) W := by {
      rw[←g.linearity2]
      rw[←g.linearity2]
    }
                                                                              _=metric x 0 W := by rw [BianchiR31 x X Y Z]
                                                                              _= 0 := by exact ex4 x g W
}


lemma MainSymR40 [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) :
 CurvatureTensor40 x X Y Z W =CurvatureTensor40 x  Z W X Y := by{
  have Bianchi1 :  CurvatureTensor40 x X Y Z W + CurvatureTensor40 x   Y Z X W + CurvatureTensor40 x  Z X Y W = 0 := by exact BianchiR40  x X Y Z W
  have Bianchi2 :  CurvatureTensor40 x Y Z W X+ CurvatureTensor40 x   Z W Y X + CurvatureTensor40 x  W Y Z X = 0 := by exact  BianchiR40  x Y Z W X
  have Bianchi3 :  CurvatureTensor40 x  Z W X Y + CurvatureTensor40 x  W X Z Y + CurvatureTensor40 x  X Z W Y = 0 := by exact  BianchiR40  x Z W X Y
  have Bianchi4 :  CurvatureTensor40 x  W X Y Z + CurvatureTensor40 x   X Y W Z + CurvatureTensor40 x  Y W X Z = 0 := by exact  BianchiR40  x W X Y Z
  have SummAllBianchi : CurvatureTensor40 x  X Y Z W + CurvatureTensor40 x   Y Z X W + CurvatureTensor40 x  Z X Y W + CurvatureTensor40 x  Y Z W X+ CurvatureTensor40 x   Z W Y X + CurvatureTensor40 x  W Y Z X+CurvatureTensor40 x  Z W X Y + CurvatureTensor40 x  W X Z Y + CurvatureTensor40 x  X Z W Y+CurvatureTensor40 x  W X Y Z + CurvatureTensor40 x   X Y W Z + CurvatureTensor40 x  Y W X Z=0 := by {
    rw[Bianchi1]
    simp
    rw[Bianchi2]
    simp
    rw[Bianchi3]
    simp
    rw[Bianchi4]
  }
  have OtherPerspectiveBianchi : CurvatureTensor40 x  X Y Z W + CurvatureTensor40 x   Y Z X W + CurvatureTensor40 x  Z X Y W + CurvatureTensor40 x  Y Z W X+ CurvatureTensor40 x   Z W Y X + CurvatureTensor40 x  W Y Z X+CurvatureTensor40 x  Z W X Y + CurvatureTensor40 x  W X Z Y + CurvatureTensor40 x  X Z W Y+CurvatureTensor40 x  W X Y Z + CurvatureTensor40 x   X Y W Z + CurvatureTensor40 x  Y W X Z= 2* CurvatureTensor40 x  X Y Z W- 2* CurvatureTensor40 x  Z W X Y := by{
   sorry
  }
  have MergeTogether : 2* CurvatureTensor40 x  X Y Z W- 2* CurvatureTensor40 x  Z W X Y =0 := by{
    rw[←OtherPerspectiveBianchi]
    rw[SummAllBianchi]
  }
  have : CurvatureTensor40 x  X Y Z W= CurvatureTensor40 x  Z W X Y  := sorry
  exact this
}



/-Definition of flat manifold.-/
variable [g : RiemannianMetric I M] [conn : Connection I M] [brack: LieBracket I M] [nabla : LeviCivitaConnection I M] in
structure FlatManifold where
(condition : ∀ (x : M) (X Y Z W : SmoothSection I E (TangentSpace I (M := M))) , CurvatureTensor40 x X Y Z W=0)
