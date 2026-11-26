import SolverPacketCompatibility

noncomputable section
namespace RootSeparation.Solver
open S11 Classical
open scoped BigOperators

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c) (cap : probeCount c.edges (callL s c) ≤ 2^e)
variable (t : callCenters s c) (j : callProbes s c)

private theorem readExponent_transport {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A ≃ B) (xs : List B) (β : List ℕ) (a : A) :
    readExponent (xs.map e.symm) β a = readExponent xs β (e a) := by
  induction xs generalizing β with
  | nil => rfl
  | cons b xs ih =>
    cases β with
    | nil => rfl
    | cons n ns =>
      simp only [List.map_cons,readExponent,← e.apply_eq_iff_eq,e.apply_symm_apply,ih]

def packetExponent (β : List ℕ) : (nativeAffineData F G cap t j).affine.Z → ℕ :=
  fun z => actualExponent G t β (unpackActualMode F G t z)

theorem packetExponent_native (β : List ℕ) :
    packetExponent F G cap t j β =
      readExponent (nativeModeOrder (nativeAffineData F G cap t j).affine (level t.val)
        (callPrecision s c t.val) (unpackActualMode F G t)) β := by
  funext z
  unfold packetExponent actualExponent nativeModeOrder
  exact (readExponent_transport (unpackActualMode F G t) _ β z).symm

def packetSourceEquiv (g : Fin 64) (k : G.Packet) :
    (nativeAffineData F G cap t j).packetReads g k ≃ SourceAt F G t g k where
  toFun z := ⟨unpackActualMode F G t z.val, z.val.2.2.property.1.trans z.property.2, z.property.1⟩
  invFun z := ⟨(unpackActualMode F G t).symm z.val,z.property.2,z.property.1⟩
  left_inv := by
    rintro ⟨⟨a,b,z,hb,ha⟩,_,_⟩
    subst a
    subst b
    rfl
  right_inv := fun _ => rfl

set_option maxHeartbeats 1800000 in
theorem packetTile_native (β : List ℕ) (g : Fin 64) (k : G.Packet) (bits : GroupBits F G t g) :
    (nativeAffineData F G cap t j).packetTile (packetExponent F G cap t j β) g k bits =
      ∏ z : SourceAt F G t g k,
        (reduced F t (sourceTile G t (K := RationalCoefficients F) (packetBits F G t (k := k) bits) z.val)
          (sourceTile_integral G t (K := RationalCoefficients F) (rationalValuation F)
            (packetBits F G t (k := k) bits) z.val)) ^ actualExponent G t β z.val := by
  unfold PacketData.packetTile
  apply Fintype.prod_equiv (packetSourceEquiv F G cap t j g k)
  rintro ⟨⟨a,b,z,hb,ha⟩,hs,hp⟩
  subst a
  subst b
  subst g
  cases hp
  rfl

private theorem nativeChild_leafValue (β : List ℕ) (g : Fin 64) :
    leafValue (childCall F.monic F.degree G (nativeTables F G cap) t j β g) =
      ∑ bits : GroupBits F G t g, (nativeAffineData F G cap t j).old g bits *
        ∏ k, nativeTables F G cap t j β g k (packetBits F G t (k := k) bits) := by
  classical
  unfold leafValue Network.contract Network.rowProduct Network.colProduct
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro X _
  congr 1
  · apply Finset.prod_congr rfl
    rintro ⟨v|v,hv⟩ _
    · rfl
    · rfl
  · apply Finset.prod_congr rfl
    intro k _
    exact childCall_packet_at_creation F.monic F.degree G (nativeTables F G cap) t j β g k _

set_option maxHeartbeats 1200000 in
/-- The grouped sum in the S11 recurrence is the contraction of the
    physical child at its creation precision. No recursive return is
    assumed in this identity. -/
theorem affineChild_physical (β : List ℕ) (g : Fin 64) :
    (nativeAffineData F G cap t j).affine.child (packetExponent F G cap t j β) g =
      leafValue (childCall F.monic F.degree G (nativeTables F G cap) t j β g) := by
  rw [PacketData.affine_child_packets,nativeChild_leafValue]
  apply Finset.sum_congr rfl
  intro bits _
  apply congrArg ((nativeAffineData F G cap t j).old g bits * ·)
  apply Finset.prod_congr rfl
  intro k _
  rw [packetTile_native,nativeTables_as_packetValue,packetValue]
  rfl

end RootSeparation.Solver

#print axioms RootSeparation.Solver.packetExponent_native
#print axioms RootSeparation.Solver.affineChild_physical
