import P1DyadicGrid
import Mathlib.Tactic

/-! Literal tile moments in Appendix D's nonzero probe. The tile
and within-tile integer are obtained from the real column slots,
so the mode substitution does not read any target-group bit. -/
namespace J6R9PacketTiles
open scoped BigOperators
open P1DyadicGrid
def tile (i y : ℕ) : ℕ := y % 2^(i+1)
def coord (i y : ℕ) : ℕ := y / 2^(i+1)

theorem tile_coordinates (i y : ℕ) :
    tile i y < 2^(i+1) ∧ y=tile i y+2^(i+1)*coord i y := by
  unfold tile coord
  exact ⟨Nat.mod_lt _ (by positivity),(Nat.mod_add_div _ _).symm⟩

theorem bit_of_tile (i y : ℕ) :
    y.testBit i=(tile i y).testBit i := by
  obtain ⟨_,he⟩ := tile_coordinates i y
  conv_lhs => rw [he]
  exact tile_bit i (tile i y) (coord i y)

variable {P K R : Type*} [Fintype P] [DecidableEq K] [CommRing R]

def columns (page : P → K) (seat : P → ℕ) (i : ℕ) (k : K) (τ : ℕ) : Finset P :=
  Finset.univ.filter (fun p => page p=k ∧ tile i (seat p)=τ)

def bit (R : Type*) [Zero R] [One R] (x : Bool) : R := if x then 1 else 0

def L (page : P → K) (seat : P → ℕ) (i : ℕ) (k : K) (τ b : ℕ)
    (X : P → Bool) : R :=
  ∑ p ∈ columns page seat i k τ, ((coord i (seat p):ℕ):R)^b * bit R (X p)

theorem in_tile_exact (page : P → K) (seat : P → ℕ) (i : ℕ) (k : K) (τ : ℕ)
    (p : P) (hp : p ∈ columns page seat i k τ) :
    page p=k ∧ seat p=τ+2^(i+1)*coord i (seat p) ∧ (seat p).testBit i=τ.testBit i := by
  have he := (Finset.mem_filter.mp hp).2
  refine ⟨he.1,?_,?_⟩
  · have h := (tile_coordinates i (seat p)).2
    rwa [he.2] at h
  · rw [bit_of_tile,he.2]

theorem moment_local (page : P → K) (seat : P → ℕ) (i : ℕ) (k : K) (τ b : ℕ)
    (X X' : P → Bool) (h : ∀ p ∈ columns page seat i k τ, X p=X' p) :
    (L page seat i k τ b X : R) = L page seat i k τ b X' := by
  unfold L
  exact Finset.sum_congr rfl (fun p hp => by rw [h p hp])

/-- The actual b powers are shared across the column sums. This is the
equivalence between portwise expansion and an Appendix D mode row. -/
theorem regroup_modes (page : P → K) (seat : P → ℕ) (i : ℕ) (k : K) (τ n : ℕ)
    (C : ℕ → R) (X : P → Bool) :
    (∑ p ∈ columns page seat i k τ,
        (∑ b ∈ Finset.range n, C b * ((coord i (seat p):ℕ):R)^b)*bit R (X p)) =
      ∑ b ∈ Finset.range n, C b * L page seat i k τ b X := by
  simp only [Finset.sum_mul,mul_assoc,L,Finset.mul_sum]
  exact Finset.sum_comm

#print axioms tile_coordinates
#print axioms in_tile_exact
#print axioms moment_local
#print axioms regroup_modes
end J6R9PacketTiles
