module

public import Cliquefree.TriangleReduction

/-!
# The triangle dichotomy used by the existence theorem

The triangle reduction gives the alternative needed at a positive maximizer.
-/

@[expose] public section

noncomputable section

universe u

namespace Cliquefree

/-- Every finite positively weighted graph satisfies the mathematical triangle alternative. -/
theorem triangle_dichotomy : TriangleDichotomy.{u} :=
  triangle_dichotomy_of_reduction triangle_reduction_step

end Cliquefree
