import J6IntegerPrintedDecode
import J6ZeroTransport
import J6NativeHeightLift

/-! Fit and normalize an actual J6 rational layer factorization; carry
the same equality into the base finite receiving ring with no new bound
or guessed rational representative. -/
namespace J6FactorToInteger
open J6Mesh J6NativeHeight J6NativeHeightMesh J6NativeHeightClearing
open J6IntegerLayers J6IntegerDecode
open scoped Polynomial BigOperators Classical
set_option maxHeartbeats 950000

variable {U T P : Type*} [Fintype U] [DecidableEq U] [Fintype T] [Fintype P] [DecidableEq P]

theorem clear_factorization
    (physA physB : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (A B : (U → Bool) → Bool) (m q : ℕ)
    (loads : J6Recovery.Addr m → T → ℕ) (i : J6Recovery.Addr m)
    (hk : ∀ v, loads i v ≤ 2)
    (hcard : Fintype.card P = (index m i+J6Recovery.exp m i)*Fintype.card U+2*Fintype.card T)
    (hshape : rationalSlot physA physB read (point m i) =
      J6Recovery.layerSum m q (oldWeight A) (oldWeight B) loads i) :
    let n := sampleNum m i
    let d := sampleDen m i
    numerator physA physB read n d =
      factor (P:=U) n d (index m i) q (loads i) * (oldLayer A B n d)^(J6Recovery.exp m i) := by
  dsimp only
  let n := sampleNum m i
  let d := sampleDen m i
  have hd : d ≠ 0 := (mesh_bounds m i).1.ne'
  apply (Int.cast_injective (α:=ℚ))
  rw [explicit_cleared_numerator physA physB read n d hd,
    ← mesh_fraction m i, hshape,J6Recovery.layerSum_factorization,
    integer_factorization A B n d (index m i) q (J6Recovery.exp m i) (loads i) hd hk,
    ← mesh_fraction m i,hcard,J6Recovery.publicFactor]

theorem receiver_factorization
    (physA physB : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (A B : (U → Bool) → Bool) (m base q : ℕ)
    (loads : J6Recovery.Addr m → T → ℕ) (i : J6Recovery.Addr m)
    (hk : ∀ v, loads i v ≤ 2)
    (hP : Fintype.card P = M m)
    (hcard : Fintype.card P = (index m i+J6Recovery.exp m i)*Fintype.card U+2*Fintype.card T)
    (hshape : rationalSlot physA physB read (point m i) =
      J6Recovery.layerSum m q (oldWeight A) (oldWeight B) loads i) :
    let n := sampleNum m i
    let d := sampleDen m i
    let p := J6SourcePrecision.printed m base
    let z := J6NativeHeightResidue.residueSlot physA physB read
        (J6ZeroTransport.reduceBase p (J6NativeHeightDyadic.scalar m i))
    let u := factor (P:=U) n d (index m i) q (loads i)
    integerDecode p (J6Recovery.exp m i) (M m) d u z = (oldLayer A B n d,p) := by
  dsimp only
  let n := sampleNum m i
  let d := sampleDen m i
  let p := J6SourcePrecision.printed m base
  have hu := (public_pos (P:=U) n d (index m i) q (loads i)
    (mesh_bounds m i).1 (by unfold n sampleNum; exact neg_nonpos.mpr (Int.natCast_nonneg _))).ne'
  have hkern := J6NativeHeightDyadic.actual_scalar_clearing (J6ZeroTransport.reduceBase p) m i
  have hr := J6NativeHeightResidue.residueClearing physA physB read n d _ hkern
  have he := clear_factorization physA physB read A B m q loads i hk hcard hshape
  dsimp only at he
  rw [he,hP] at hr
  have hf := J6SourcePrecision.centered_fit_printed m base i
      (numerator physA physB read n d)
      (physical_height m (index m i) hP physA physB read n d (mesh_bounds m i).2.1 (mesh_bounds m i).2.2)
  rw [he] at hf
  exact residue_root p _ (M m) d _ _ _ hu (J6Recovery.odd_exp m i) hr.symm hf

#print axioms clear_factorization
#print axioms receiver_factorization
end J6FactorToInteger