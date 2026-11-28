
import J9R17AllPinsDecode

/-!
A literal table evaluator for the J7 baseline/source and J8 marked children.
Each sum enumerates assignments to one original old column only. No row-
column joined cube or expectation oracle is part of the evaluator.
-/
namespace J9R18Compiled
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8J9Grouped J8EndToEnd LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

section OneColumn
variable {K V : Type*} [CommSemiring K] [Fintype V] [DecidableEq V]
variable {P : V → Type*} [∀ v, Fintype (P v)]

def oneColumn (w : (v : V) → P v → K) (v : V) (read : P v → K) : K :=
  (∑ z : P v, w v z * read z) * ∏ u ∈ Finset.univ.erase v, ∑ z : P u, w u z

set_option maxHeartbeats 1200000 in
theorem oneColumn_exact (w : (v : V) → P v → K) (v : V) (read : P v → K) :
    (∑ x : (u : V) → P u, (∏ u : V, w u (x u)) * read (x v)) =
      oneColumn w v read := by
  let lift : (u : V) → P u → K := fun u z => if h : u = v then read (h ▸ z) else 1
  have hlift (x : (u : V) → P u) : (∏ u : V, lift u (x u)) = read (x v) := by
    rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · simp [lift]
    · intro u _ h; simp [lift,h]
  calc
    _ = ∑ x : (u : V) → P u, ∏ u : V, w u (x u) * lift u (x u) := by
      simp only [Finset.prod_mul_distrib,hlift]
    _ = ∏ u : V, ∑ z : P u, w u z * lift u z := (Fintype.prod_sum (fun (u : V) (z : P u) => w u z * lift u z)).symm
    _ = oneColumn w v read := by
      unfold oneColumn
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
      congr 1
      · simp [lift]
      · apply Finset.prod_congr rfl
        intro u hu
        simp [lift,(Finset.mem_erase.mp hu).1]
end OneColumn

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def localWeight (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g) (z : LocalPort d v → Bool) : ℚ :=
  J8SourceMoment.localColumnWeight (groupWiring d e he g) (outerAmplitude L) (F g) mark v z

def massAt (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g) : ℚ :=
  ∑ z : LocalPort d v→Bool, localWeight d e he F g mark v z

def groupMass (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (mark : Option (LocalRow d g × Bool)) : ℚ :=
  J8SourceMoment.unmatchedMultiplier (groupWiring d e he g) mark *
    ∏ v : LocalColumn d g, massAt d e he F g mark v

theorem groupMass_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (mark : Option (LocalRow d g × Bool)) :
    groupMass d e he F g mark =
      ∑ x : LocalBits d g, J8SourceMoment.weighted
        (localChild d e he g (outerAmplitude L) (F g)) mark x :=
  (J8SourceMoment.marked_mass_local (groupWiring d e he g) (outerAmplitude L) (F g) mark).symm

def oldPortMoment (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (q : Sigma (LocalPort d (g:=g))) : ℚ :=
  oneColumn (localWeight d e he F g none) q.1
    (fun z => NativeChildRealization.bitValue ℚ (z q.2))

theorem oldPortMoment_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (q : Sigma (LocalPort d (g:=g))) :
    oldPortMoment d e he F g q =
      ∑ x : LocalBits d g, J8SourceMoment.weighted
        (localChild d e he g (outerAmplitude L) (F g)) none x *
          NativeChildRealization.bitValue ℚ (x q.1 q.2) := by
  unfold oldPortMoment
  simp_rw [localChild,J8SourceMoment.weighted_column_factor,
    J8SourceMoment.unmatchedMultiplier_baseline,one_mul]
  exact (oneColumn_exact (localWeight d e he F g none) q.1 _).symm

def backgroundNumber (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ℚ :=
  ∑ q : OldTile d a, (ordinal d (ordinaryWire d q.1) : ℚ)^b *
    oldPortMoment d e he F (d.pinLabel a) (tileOldInSource d q)

theorem backgroundNumber_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : ℕ) :
    backgroundNumber d e he F a b =
      ∑ x : LocalBits d (d.pinLabel a), J8SourceMoment.weighted
        (localChild d e he _ (outerAmplitude L) (F _)) none x * tileBackground d a b x := by
  simp only [backgroundNumber,oldPortMoment_exact,tileBackground,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro q _
  ring

def pinMoment (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) : ℚ :=
  ∑ i : Fin (Fintype.card (PinTile d a)),
    NativeMomentReconstruction.bitValue (sign (pinEnumeration d a i).1) * coordinates d a i^(b:ℕ)

def sourceMoment (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) : ℚ :=
  backgroundNumber d e he F a b +
    groupMass d e he F (d.pinLabel a) none * pinMoment d a b sign

theorem sourceMoment_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) (higher : RestArguments d) :
    sourceMoment d e he F a b sign =
      (J8SourceMoment.genuineChild (localChild d e he (d.pinLabel a) (outerAmplitude L) (F _))
        (fun i : LocalPin d (d.pinLabel a) => sign i.1) (higher _)
        none (J8SourceMoment.sourceFeature (fun i => tilePinInSource d (pinEnumeration d a i))
          (coordinates d a) (fun n => tileBackground d a n) b)).coeff 0 := by
  rw [J8SourceMoment.childConstant,sourceMoment,backgroundNumber_exact,groupMass_exact]
  simp only [J8SourceMoment.sourceFeature,mul_add,Finset.sum_add_distrib,Finset.sum_mul,pinMoment]
  rfl

#print axioms oneColumn_exact
#print axioms groupMass_exact
#print axioms oldPortMoment_exact
#print axioms backgroundNumber_exact
#print axioms sourceMoment_exact

end
end J9R18Compiled
