import J4R43LiteralOutsideCentres
import J4R43LiteralOutsideTop
import J1PPrintedMesh

/-! Concrete finite source threshold for the original outer interval.
There is no independent assumed supply, cell-near-uniformity, or
active-centre certificate at the two odd extremes. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6ActiveRun J6R12Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3500000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem large_width_guard (s : ℕ) (big : 5*epsDen≤Nat.clog 2 s) :
    10≤stepA (Nat.clog 2 s) 0 := by
  have q : 5≤Nat.clog 2 s/epsDen :=
    (Nat.le_div_iff_mul_le (by norm_num [epsDen] : 0<epsDen)).mpr big
  have u : 5≤stepU (Nat.clog 2 s) 0 := by simpa [stepU] using q
  have h : stepA (Nat.clog 2 s) 0=2*stepU (Nat.clog 2 s) 0 := by simp [stepA]
  omega

theorem large_source_delta (s : ℕ) (big : 5*epsDen≤Nat.clog 2 s) :
    819200≤sourceDelta s := by
  have ob : 32<Nat.clog 2 s := by
    have n : 32<5*epsDen := by norm_num [epsDen]
    exact n.trans_le big
  have lower : 2^32≤s := ((Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp ob).le
  have pp : ((2:ℕ)^32)^9≤(sourceDelta s)^10 :=
    (Nat.pow_le_pow_left lower 9).trans (delta_pow_ge s)
  have hard : (819200:ℕ)^10<((2:ℕ)^32)^9 := by norm_num
  by_contra! h
  have hi := Nat.pow_le_pow_left h.le 10
  exact (not_lt_of_ge (pp.trans hi)) hard

theorem actual_large_root_band_guards (d : ColumnReady F reg (f:=f))
    (big : 5*epsDen≤Nat.clog 2 (oldRowSize F)) :
    16*reciprocal 3≤2^a₀ ∧
      1638400*(J9PrintedSchedule.arrayCard a₀)^2≤Nat.card (DWire F) := by
  let D := J9PrintedSchedule.arrayCard a₀
  have aw : 10≤a₀ := large_width_guard (oldRowSize F) big
  have ww : 16*reciprocal 3≤(2:ℕ)^10 := by norm_num [reciprocal]
  have dlt := large_source_delta (oldRowSize F) big
  have dc : 2*D^2*sourceDelta (oldRowSize F)≤Fintype.card (DWire F) := d.collision
  refine ⟨ww.trans (Nat.pow_le_pow_right (by decide) aw),?_⟩
  rw [Nat.card_eq_fintype_card]
  calc
    _ = 2*D^2*819200 := by ring
    _ ≤ _ := (Nat.mul_le_mul_left (2*D^2) dlt)
    _ ≤ _ := dc

#print axioms large_width_guard
#print axioms large_source_delta
#print axioms actual_large_root_band_guards
end
end J4R43LiteralOutside

