import Mathlib.Tactic

set_option autoImplicit false

/-! A common descendant ABI can be chosen *before* physical packing.
This does not identify any already serialized file with a wider one,
or assert that the separately pinned root page key has this width. -/
namespace J6R33GeneratedChildSite

def descendantWordWidth (base maxAxis axis : ℕ) : ℕ :=
  base + 12*(maxAxis-axis)

def descendantPageWidth (base maxAxis : ℕ) : ℕ :=
  base+12*maxAxis

theorem preselected_common_child_width {base maxAxis axis edges precision : ℕ}
    (a : axis≤maxAxis) (b : maxAxis≤base)
    (edgeFit : edges<2^base) (precFit : precision<2^(base+1)) :
    let q := descendantWordWidth base maxAxis axis
    let page := descendantPageWidth base maxAxis
    axis≤q ∧ base≤q ∧ q≤page ∧ (q-axis)+13*axis=page ∧
      edges<2^q ∧ precision<2^(q+1) := by
  let q := descendantWordWidth base maxAxis axis
  have qB : base≤q := by unfold q descendantWordWidth; omega
  have aq : axis≤q := a.trans (b.trans qB)
  have e : edges<2^q := edgeFit.trans_le (Nat.pow_le_pow_right (by decide) qB)
  have p : precision<2^(q+1) := precFit.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨aq,qB,?_,?_,e,p⟩ <;>
    dsimp only [q,descendantPageWidth,descendantWordWidth] <;> omega

#print axioms preselected_common_child_width
end J6R33GeneratedChildSite
