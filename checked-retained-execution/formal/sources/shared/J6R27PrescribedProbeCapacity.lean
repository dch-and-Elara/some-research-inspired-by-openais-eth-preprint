
import J6R26StablePreparedRootSite
import J6R14ZeroModePlanted

/-! The printed extension degree has room for one more word than the
root probe order: there is no need to include the zero binary word. -/
namespace J6R27PrescribedProbe
open scoped Polynomial
open Polynomial J6Mesh J6R12Repack J6R11Repack J6R14ZeroMode
open J6R26StablePreparedRoot J6OrientedHost
set_option maxHeartbeats 4500000
set_option linter.unusedSectionVars false

theorem mesh_length_le_edges (m : ℕ) : L m≤M m := by
  have p : 0<D m*K m := by unfold J6Mesh.D J6Mesh.K; positivity
  calc
    L m = 1*L m := (one_mul _).symm
    _ ≤ (D m*K m)*L m := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt p)
    _ = M m := by rw [Nat.mul_assoc,mesh_product]

theorem printed_nonzero_capacity (m native e : ℕ) (hn : native≤m)
    (he : e=4*Nat.clog 2 (physicalSize m native)) :
    literalDegree m native+1 < 2^e := by
  have hLam : 0<lambda m := by
    unfold lambda
    have hp := b_pos m
    omega
  have hM : 0<M m := by unfold M; positivity
  have hL : 0<L m := by unfold L; positivity
  have hL' := mesh_length_le_edges m
  have hMul : M m ≤ M m*(2*L m) := by
    calc
      M m = M m*1 := (mul_one _).symm
      _ ≤ M m*(2*L m) := Nat.mul_le_mul_left _ (by omega)
  rw [literal_degree_eq m native hn,he,(physicalSize_ceiling m native hn).2.2]
  calc
    M m*(2*L m-1)+1 ≤ M m*(2*L m) := by
      rw [Nat.mul_sub,Nat.mul_one]
      omega
    _ ≤ M m*(2*M m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hL')
    _ = 2^(lambda m+lambda m+1) := by rw [J6Mesh.M,pow_succ,pow_add]; ring
    _ < 2^(4*lambda m) := Nat.pow_lt_pow_right (by decide) (by omega)

theorem literal_external_spare {V : Type} [Fintype V] (f : ℤ[X])
    (ell m l q base native width : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (G : RootShape f m l base native width T w) :
    externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m l q T w)+1 < 2^f.natDegree := by
  change literalDegree m native+1 < 2^f.natDegree
  exact printed_nonzero_capacity m native f.natDegree G.nativeFits G.fieldDegree

#print axioms mesh_length_le_edges
#print axioms printed_nonzero_capacity
#print axioms literal_external_spare
end J6R27PrescribedProbe
