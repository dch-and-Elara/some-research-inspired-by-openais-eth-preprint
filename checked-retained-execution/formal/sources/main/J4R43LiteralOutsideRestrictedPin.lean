import J4R43LiteralOutsideHammingRun

/-! On the stated restriction, the one genuine positive slot
recovers the selected sign for every fixed setting of the other
signs, not only the two illustrative all-false inputs. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6ActiveRun J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5600000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "N" => oldColumnNetwork F reg

theorem pinned_hamming_recovers_sign (P : PhysicalPacking N a (Fin 64)) (t : ℤ)
    (v : W) (selected : v∈hitPins F reg P t) (σ τ : W→Bool)
    (same : ∀ u≠v,σ u=τ u) (equal : hitWeight F reg P t σ=hitWeight F reg P t τ) :
    σ v=τ v := by
  let T (z : W→Bool) := (hitPins F reg P t).filter (fun u=>z u=true)
  have erase : (T σ).erase v=(T τ).erase v := by
    ext u
    by_cases e : u=v
    · simp [e,T]
    · simp [T,e,same u e]
  have counts : (T σ).card=(T τ).card := equal
  cases s : σ v <;> cases r : τ v
  · rfl
  · exfalso
    have ns : v∉T σ := by simp [T,s]
    have rt : v∈T τ := by simp [T,r,selected]
    have h := Finset.card_erase_add_one rt
    rw [←erase,Finset.erase_eq_of_notMem ns,counts] at h
    omega
  · exfalso
    have st : v∈T σ := by simp [T,s,selected]
    have nr : v∉T τ := by simp [T,r]
    have h := Finset.card_erase_add_one st
    rw [erase,Finset.erase_eq_of_notMem nr,←counts] at h
    omega
  · rfl

variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem literal_positive_slot_recovers_designated_under_restriction
    (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (out : t.val=(((2^a₀:ℕ):ℤ)-1)) (hf : f.Monic) (hd : 0<f.natDegree)
    (v : W) (last : (P.seat (literalPin F v)).2.val+1=2^a₀)
    (σ τ : W→Bool) (same : ∀ u≠v,σ u=τ u)
    (sameRegister : originalOppositeSlot F reg P d t i hv 0 0 hf σ=
      originalOppositeSlot F reg P d t i hv 0 0 hf τ) :
    σ v=τ v := by
  have selected : v∈hitPins F reg P t.val := by
    rw [out]
    exact last_pin_makes_set_nonempty F reg P G v last
  obtain ⟨_,x,pa,pb⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd σ
  obtain ⟨_,y,_,_⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd τ
  rw [sameRegister,y] at x
  exact pinned_hamming_recovers_sign F reg P t.val v selected σ τ same
    ((hamming_comparison_unique _ _ pa pb x).symm)

#print axioms pinned_hamming_recovers_sign
#print axioms literal_positive_slot_recovers_designated_under_restriction
end
end J4R43LiteralOutside

