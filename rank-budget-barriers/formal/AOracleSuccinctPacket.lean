import AOracleSuccinct
import Mathlib.Tactic

/-!
# Physical packet and tile recipes for A1

The input lists label/group and packet/slot coordinates for every
real port. A mode is given by its literal packet, tile, source/target
groups and exponent. These formulae do not enumerate all assignments.
Native coefficient evaluation comes from the separate dyadic code.
-/

open scoped BigOperators

namespace AOracleSuccinctPacket
open AOracleSuccinct AOracleWitness

structure Ports (n packets G L : ℕ) where
  packet : Fin n → Fin packets
  group : Fin n → Fin G
  slot : Fin n → Fin L

structure Mode (packets G i p : ℕ) where
  packet : Fin packets
  tile : Fin (2^(i+1))
  src : Fin G
  dst : Fin G
  exponent : Fin (p-1)

def Mode.weight {packets G i p : ℕ} (z : Mode packets G i p) : ℕ :=
  z.exponent.val+1

theorem Mode.weight_range {packets G i p : ℕ} (z : Mode packets G i p) :
    1 ≤ z.weight ∧ z.weight < p := by
  have h := z.exponent.isLt
  unfold Mode.weight
  omega

/-- Use the actual tile remainder and quotient of a nonnegative
physical column coordinate. -/
def tile (i y : ℕ) : ℕ := y % 2^(i+1)
def quotient (i y : ℕ) : ℕ := y / 2^(i+1)

theorem tile_ok (i y : ℕ) : tile i y < 2^(i+1) := by
  unfold tile
  exact Nat.mod_lt _ (by positivity)

theorem tile_decompose (i y : ℕ) : tile i y+2^(i+1)*quotient i y = y :=
  Nat.mod_add_div _ _

section
variable {r c packets G L i p m delta : ℕ}

def sameGroup (row : Ports r packets G L) (col : Ports c packets G L)
    (x : Fin r) (y : Fin c) : Bool :=
  decide (row.packet x = col.packet y ∧ row.group x = col.group y)

def targets (row : Ports r packets G L) (x : Fin r) (z : Mode packets G i p) : Bool :=
  decide (row.packet x = z.packet ∧ row.group x = z.dst)

def inTile (col : Ports c packets G L) (y : Fin c) (z : Mode packets G i p) : Bool :=
  decide (col.packet y = z.packet ∧ tile i (col.slot y).val = z.tile.val ∧ col.group y = z.src)

/-- At most c physical column records are scanned. The assignments
are never enumerated. Keep a copy of a repeated numerical value if it
occurs at a different physical column. -/
def scanRecipe {R : Type*} (ok : Fin c → Bool) (value : Fin c → R) : Linear c R :=
  ((List.finRange c).filter ok).map (fun y => (y,value y))

theorem scanRecipe_length {R : Type*} (ok : Fin c → Bool) (value : Fin c → R) :
    (scanRecipe ok value).length ≤ c := by
  rw [scanRecipe, List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

variable {R : Type*} [CommRing R]

theorem eval_filtered_positions (x : Cols c) (ok : Fin c → Bool) (value : Fin c → R)
    (addresses : List (Fin c)) :
    linearEval x ((addresses.filter ok).map (fun y => (y,value y))) =
      (addresses.map (fun y => if ok y && x y then value y else 0)).sum := by
  induction addresses with
  | nil => rfl
  | cons y ys ih =>
    cases hy : ok y <;> simp [hy, linearEval, ih]

theorem scanRecipe_eq (x : Cols c) (ok : Fin c → Bool) (value : Fin c → R) :
    linearEval x (scanRecipe ok value) =
      ∑ y : Fin c, if ok y && x y then value y else 0 := by
  rw [scanRecipe, eval_filtered_positions]
  rw [List.finRange, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The j^b factor is generated from its actual physical tile index.
In particular 0^0=1 is already represented correctly. -/
def momentRecipe (col : Ports c packets G L) (z : Mode packets G i p) : Linear c R :=
  scanRecipe (fun j => inTile col j z)
    (fun j => (quotient i (col.slot j).val:R)^z.exponent.val)

theorem momentRecipe_exact (col : Ports c packets G L) (z : Mode packets G i p) (x : Cols c) :
    linearEval x (momentRecipe (R:=R) col z) =
      ∑ j : Fin c, if inTile col j z && x j then
        (quotient i (col.slot j).val:R)^z.exponent.val else 0 :=
  scanRecipe_eq _ _ _

/-- Numeric kernel and cross values come from the native geometry
or the on-demand dyadic evaluator. No assignment-indexed input appears. -/
def compile (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G L) (col : Ports c packets G L)
    (modes : Fin m → Mode packets G i p)
    (kernel : Fin r → Fin c → R)
    (cross : Fin r → Mode packets G i p → R) : Recipes R r c m delta where
  rows := rt
  cols := ct
  localRecipe j := scanRecipe (sameGroup row col j) (kernel j)
  cross j k := cross j (modes k)
  target j k := targets row j (modes k)
  moment k := momentRecipe col (modes k)

theorem compile_read_bound (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G L) (col : Ports c packets G L)
    (modes : Fin m → Mode packets G i p)
    (kernel : Fin r → Fin c → R) (cross : Fin r → Mode packets G i p → R)
    (a : Allocation r m) :
    totalLinearReads (compile rt ct row col modes kernel cross) a ≤ r*c := by
  apply totalLinearReads_le
  · intro j
    apply scanRecipe_length
  · intro k
    apply scanRecipe_length

/-- The same source schedule may compute the fixed-node aggregate with
one full physical packet recipe per row (groups no longer filtered). -/
def fullRecipe (row : Ports r packets G L) (col : Ports c packets G L)
    (kernel : Fin r → Fin c → R) (j : Fin r) : Linear c R :=
  scanRecipe (fun k => decide (row.packet j = col.packet k)) (kernel j)

theorem fullRecipe_eq (row : Ports r packets G L) (col : Ports c packets G L)
    (kernel : Fin r → Fin c → R) (j : Fin r) (x : Cols c) :
    linearEval x (fullRecipe row col kernel j) =
      ∑ k : Fin c, if decide (row.packet j = col.packet k) && x k then kernel j k else 0 :=
  scanRecipe_eq _ _ _

end

#print axioms Mode.weight_range
#print axioms tile_decompose
#print axioms scanRecipe_length
#print axioms scanRecipe_eq
#print axioms momentRecipe_exact
#print axioms compile_read_bound
#print axioms fullRecipe_eq

end AOracleSuccinctPacket

