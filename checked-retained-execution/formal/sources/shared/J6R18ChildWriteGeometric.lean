import J6R18ChildWritePhysical
import J6R18ChildWriteRun

/-! Remove the depth-first recurrence from the actual entry bound. The
prefactor is explicit; this theorem does not charge the producer of
the descriptor tape or the surrounding recursion. -/
namespace J6R18ChildWrite
open AOracleMachineTime A1R10 A1R11 A1R12

def packetNonTreeFee (a e ell p i q b r c m : ℕ) (hp : 0<p) : ℕ :=
  let W := uvWidth e ell p
  rowWriteCap a e ell p i q b c m r hp+
    m*((2*b+4*q+8)+(b+q)+4)+W+W+
    m*(sourcePowerFee a e ell p q c hp+mulCap e ell p+2)+mulCap e ell p+12

def packetTreeScale (e ell p m r b q : ℕ) (hp : 0<p) : ℕ :=
  leafFee e ell p m r b q+uvWidth e ell p+(m+1)*choiceFee e ell p b hp

def packetFramingFee (e ell p q : ℕ) : ℕ :=
  (4*q+6*ell*(e*p+1)+16)+4

theorem packetFee_geometric (a e ell p i q b r c m : ℕ) (hp : 0<p) (h : r≤2^a) :
    packetFee a e ell p i q b r c m hp+packetFramingFee e ell p q ≤
      (m+2)^(2^a)*(packetNonTreeFee a e ell p i q b r c m hp+
        packetTreeScale e ell p m r b q hp+packetFramingFee e ell p q) := by
  let W := uvWidth e ell p
  let T := treeFee W (m+1) (leafFee e ell p m r b q) (choiceFee e ell p b hp) r
  let B := (m+2)^(2^a)
  let C := packetTreeScale e ell p m r b q hp
  let R := packetNonTreeFee a e ell p i q b r c m hp
  let F := packetFramingFee e ell p q
  have h₁ : packetFee a e ell p i q b r c m hp=R+T := by
    dsimp only [packetFee,R,packetNonTreeFee,W,T]
    omega
  have h₂ : T≤(m+2)^r*C := by
    simpa only [T,C,packetTreeScale] using
      treeFee_pow W (m+1) (leafFee e ell p m r b q) (choiceFee e ell p b hp) r
  have h₃ : (m+2)^r≤B := Nat.pow_le_pow_right (by omega) h
  have hTB : T≤B*C := h₂.trans (Nat.mul_le_mul_right C h₃)
  have hR : R≤B*R := Nat.le_mul_of_pos_left _ (by dsimp [B]; positivity)
  have hF : F≤B*F := Nat.le_mul_of_pos_left _ (by dsimp [B]; positivity)
  change packetFee a e ell p i q b r c m hp+F≤B*(R+C+F)
  rw [h₁,Nat.mul_add,Nat.mul_add]
  exact Nat.add_le_add (Nat.add_le_add hR hTB) hF

#print axioms packetFee_geometric
end J6R18ChildWrite

