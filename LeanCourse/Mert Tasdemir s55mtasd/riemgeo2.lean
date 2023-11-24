import LeanCourse.Common
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
