import SolverRowPartition
import S11ModeDFS
import RootExecution

noncomputable section
namespace RootSeparation.Solver
open S11 Classical
open scoped BigOperators
set_option linter.unusedSectionVars false

/-- Group-local bits with rows and target variables separated by the
packet of the physical row or variable. Source variables need not
have the same symbol as their targets. -/
structure PacketData (G R : Type*) (P : Type) where
  Bits : G → Type
  Rows : G → P → Type
  Modes : G → P → Type
  source : (Σ g, Σ p, Modes g p) → G
  weight : (Σ g, Σ p, Modes g p) → ℕ
  old : (g : G) → Bits g → R
  normalized : (g : G) → Bits g → (p : P) → Rows g p → Option (Modes g p) → R
  readTile : (z : Σ g, Σ p, Modes g p) → Bits (source z) → R

namespace PacketData

variable {G R : Type*} {P : Type} [Fintype G] [Fintype P] [CommSemiring R]
variable (D : PacketData G R P)
variable [∀ g, Fintype (D.Bits g)] [∀ g p, Fintype (D.Rows g p)]
variable [∀ g p, Fintype (D.Modes g p)]

abbrev affine : AffinePacket G R where
  Bits := D.Bits
  Rows g := Σ p, D.Rows g p
  TargetMode g := Σ p, D.Modes g p
  source := D.source
  weight := D.weight
  old := D.old
  normalized g bits := globalRow (D.normalized g bits)
  readTile := D.readTile

def localRow (g : G) (bits : D.Bits g) (k : P) (r : D.Rows g k) (o : Option (D.Modes g k)) : R :=
  (2:R) ^ o.elim' 0 (fun z => D.weight ⟨g,k,z⟩) * D.normalized g bits k r o

theorem affine_row (g : G) (bits : D.Bits g) (r : Σ p, D.Rows g p)
    (o : Option (Σ p, D.Modes g p)) :
    D.affine.row g bits r o = globalRow (D.localRow g bits) r o := by
  rcases r with ⟨k,r⟩
  cases o with
  | none => rfl
  | some z =>
    rcases z with ⟨k',z⟩
    by_cases h : k' = k
    · subst k'
      simp [AffinePacket.row,AffinePacket.weightOption,affine,globalRow,localRow]
    · simp [AffinePacket.row,affine,globalRow,h]

def packetReads (g : G) (k : P) := {z : D.affine.Z // D.source z = g ∧ z.2.1 = k}

noncomputable instance (g : G) (k : P) : Fintype (D.packetReads g k) := by
  unfold packetReads
  infer_instance

def packetTile (β : D.affine.Z → ℕ) (g : G) (k : P) (bits : D.Bits g) : R :=
  ∏ z : D.packetReads g k, D.readTile z.val (z.property.1.symm ▸ bits) ^ β z.val

theorem affine_tile (β : D.affine.Z → ℕ) (g : G) (bits : D.Bits g) :
    D.affine.tileProduct β g bits = ∏ k, D.packetTile β g k bits := by
  let f (z : {z : D.affine.Z // D.source z = g}) := z.val.2.1
  unfold AffinePacket.tileProduct
  rw [← Fintype.prod_fiberwise f]
  apply Finset.prod_congr rfl
  intro k _
  apply Fintype.prod_equiv (f := fun z : {z // f z = k} =>
    D.readTile z.val.val (z.val.property.symm ▸ bits) ^ β z.val.val)
    (g := fun z : D.packetReads g k => D.readTile z.val (z.property.1.symm ▸ bits) ^ β z.val)
    { toFun := fun z => ⟨z.val.val, z.val.property, z.property⟩
      invFun := fun z => ⟨⟨z.val,z.property.1⟩, z.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  intro _
  rfl

theorem affine_child_packets (β : D.affine.Z → ℕ) (g : G) :
    D.affine.child β g =
      ∑ bits : D.Bits g, D.old g bits *
        ∏ k, (packetCoeff (D.localRow g bits k) (fun z => β ⟨g,k,z⟩) *
          D.packetTile β g k bits) := by
  classical
  letI : DecidableEq (D.affine.Rows g) := fun a b => Classical.propDecidable (a = b)
  letI : DecidableEq (D.affine.TargetMode g) := fun a b => Classical.propDecidable (a = b)
  unfold AffinePacket.child
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro bits _
  rw [Finset.prod_mul_distrib, ← affine_tile]
  rw [← packetCoeff_split]
  unfold packetCoeff
  rw [← mul_assoc,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro choices _
  simp only [AffinePacket.accepts,AffinePacket.oldAndRows,AffinePacket.uses,affine_row]
  change (if (∀ z : Σ p, D.Modes g p,
      Fintype.card {r // choices r = some z} = β ⟨g,z⟩) then
      D.old g bits * (∏ r, globalRow (D.localRow g bits) r (choices r)) *
        D.affine.tileProduct β g bits else 0) = _
  split <;> simp_all only [mul_zero,zero_mul]

end PacketData

#print axioms PacketData.affine_row
#print axioms PacketData.affine_tile
#print axioms PacketData.affine_child_packets

theorem executeBatch_affine_value {R I B : Type*} [CommSemiring R] [DecidableEq I]
    [Fintype B] (A : AffinePacket (Fin 64) R)
    [∀ g, Fintype (A.Bits g)] [∀ g, Fintype (A.Rows g)] [∀ g, Fintype (A.TargetMode g)]
    (t : ℤ) (j p : ℕ) (e : A.Z ≃ Mode B (level t) p)
    (hw : ∀ z, A.weight z = (e z).2.2.val+1)
    (hp : (2:R)^p = 0) (codec : R ≃+ RootSeparation.Execution.Coords I p) (track : I) :
    let child (slot : Slot) (g : Fin 64) :=
      A.child (readExponent (nativeModeOrder A (level t) p e) slot.exponents) g
    codec.symm (RootSeparation.Execution.executeBatch p codec track child
      (modeWeights B (level t) p) t j).accumulator = A.sample := by
  dsimp only
  rw [RootSeparation.Execution.executeBatch_value]
  have h := native_batch_value A t j p e hw hp
  rw [runBatch_value,batch,List.map_map] at h
  exact h

#print axioms executeBatch_affine_value

end RootSeparation.Solver
