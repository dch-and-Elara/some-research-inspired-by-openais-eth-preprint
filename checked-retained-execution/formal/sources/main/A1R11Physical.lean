import A1R11Moment
import A1R11Machine

/-! Bridge the executable row compiler to the actual native physical
recipes. Same-packet/group scans and target/tile tests are derived from
the given port geometry. The normalized dyadic kernel and crossing bit
cells remain supplied; source quotient moments themselves are generated. -/

namespace A1R11
open A1R10 AOracleCoordinates AOracleMachineTime AOracleSuccinct
open AOracleSuccinctPacket AOracleSuccinctKernel AOracleSuccinctPhysical

def packScan {p c bc ell : ℕ} {f : List (A1R10.Word p)}
    (fit : c≤2^bc) (ok : Fin c → Bool) (v : Fin c → UVBlock f ell) : WireTape c bc f ell :=
  (scanRecipe ok v).map fun ⟨i,z⟩ => packWire fit i z

theorem packScan_exact {p c bc ell : ℕ} {f : List (A1R10.Word p)}
    (hp : 0<p) (fit : c≤2^bc) (ok : Fin c → Bool) (v : Fin c → UVBlock f ell) :
    linearDenote hp (packScan fit ok v)=scanRecipe ok (fun j => uvRead hp f ell (v j)) ∧
    (packScan fit ok v).length≤c := by
  constructor
  · simp [packScan,linearDenote,scanRecipe,List.map_map,Function.comp_def,packWire_position]
    intro j _
    rfl
  · simpa only [packScan,List.length_map] using scanRecipe_length ok v

def packedPhysical {p r c m packets G a i delta bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell) (fc : c≤2^bc)
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p)
    (lk : Fin r → Fin c → UVBlock f ell) (cr : Fin r → Fin m → UVBlock f ell)
    (slotQuot : Fin c → A1R10.Word p) : Packed r c m delta bc f ell where
  rows := rt
  cols := ct
  localRecipe j := packScan fc (sameGroup row col j) (lk j)
  cross := cr
  target j k := targets row j (modes k)
  moment k := packScan fc (fun j => inTile col j (modes k))
    (fun j => (momentCell hp he hv (slotQuot j) (modes k).exponent.val).result)

theorem packedPhysical_eq {p r c m packets G a i delta bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell) (fc : c≤2^bc)
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p)
    (lk : Fin r → Fin c → UVBlock f ell) (cr : Fin r → Fin m → UVBlock f ell)
    (slotQuot : Fin c → A1R10.Word p) (z : UVBlock f ell) (t : ℤ)
    (hslot : ∀ j,wordRead (slotQuot j)=(quotient i (col.slot j).val:ZMod (2^p)))
    (hlk : ∀ j k,uvRead hp f ell (lk j k)=modular p a t
          (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z))
    (hcr : ∀ j k,uvRead hp f ell (cr j k)=crossCell p a i (modes k).exponent.val t
          (row.slot j).val (modes k).tile.val (uvRead hp f ell z)) :
    (packedPhysical hp he hv fc rt ct row col modes lk cr slotQuot).denote hp =
      physical (Modulus p hp f) rt ct row col modes t (uvRead hp f ell z) := by
  have hk (j : Fin r) :
      (fun k => uvRead hp f ell (lk j k))=(fun k =>
        modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z)) :=
    funext (hlk j)
  have hm (k : Fin m) :
      (fun j => uvRead hp f ell (momentCell hp he hv (slotQuot j) (modes k).exponent.val).result) =
        (fun j => (quotient i (col.slot j).val:Truncated (Modulus p hp f) ell)^
          (modes k).exponent.val) := by
    funext j
    exact (momentCell_exact hp he hv (slotQuot j) i (col.slot j).val _ (hslot j)).1
  have hc : (fun j k => uvRead hp f ell (cr j k)) =
      fun j k => crossCell p a i (modes k).exponent.val t (row.slot j).val
        (modes k).tile.val (uvRead hp f ell z) := funext fun j => funext (hcr j)
  have Hk : (fun j => linearDenote hp (packScan fc (sameGroup row col j) (lk j))) =
      fun j => scanRecipe (sameGroup row col j) (fun k =>
        modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z)) := by
    funext j
    rw [(packScan_exact hp fc _ _).1,hk]
  have Hm :
      (fun k => linearDenote hp (packScan fc (fun j => inTile col j (modes k))
        (fun j => (momentCell hp he hv (slotQuot j) (modes k).exponent.val).result))) =
      fun k => momentRecipe col (modes k) := by
    funext k
    rw [(packScan_exact hp fc _ _).1,hm]
    rfl
  unfold Packed.denote packedPhysical physical compile
  dsimp only
  rw [Hk,hc,Hm]

theorem packedPhysical_width {p r c m packets G a i delta bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell) (fc : c≤2^bc)
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p)
    (lk : Fin r → Fin c → UVBlock f ell) (cr : Fin r → Fin m → UVBlock f ell)
    (slotQuot : Fin c → A1R10.Word p) :
    let P := packedPhysical hp he hv fc rt ct row col modes lk cr slotQuot
    (∀ j,(P.localRecipe j).length≤c) ∧ (∀ k,(P.moment k).length≤c) := by
  exact ⟨fun _ => (packScan_exact hp fc _ _).2,fun _ => (packScan_exact hp fc _ _).2⟩

#print axioms packScan_exact
#print axioms packedPhysical_eq
#print axioms packedPhysical_width
end A1R11

