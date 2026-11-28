import J6R110ScopeWordRatesNative
import J6R82LayoutDebitCore

/-! Bounds on the real copied frame and mask operands. There is no
wrapper for a fees-only supplier. -/
namespace J6R110ScopeWordRates
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R36ChildFramedRoute J6R48RawRoute
open J6R49SourceLayout J6R50SourceProducer J6R17ModeTape J6R14LayoutCost
open J6R31RootResidentTables J6R27OriginalGate J6R82LayoutDebit J6R54PublicFamily

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000
set_option Elab.async false

/-- Rectangular mode enumeration, retaining its actual operation formula. -/
def replayGeometryRoof (K : ℕ) : ℕ :=
  (350*K^2+66*K+8)+2*(3*K+1)+(3+K*(12*K+18))+
    (3+(45*K+51)*K)+buildCap K K K 0 0 K K K+10

/-- The two physical file passes and the actual next-site writer plus
R55/R102's source words. The separate dispatch and sidecar are not here. -/
def descendantSourceWordsRoof (K : ℕ) : ℕ :=
  (6+K*(59*K+70))+(3+K*(36*K+66))+
    (4+K*(locateFee K K+45*K+54))+replayGeometryRoof K+7+(40*K+45)+ordinalFee K K+3

theorem header_bank_fee_from_actual_header_count {a K : ℕ} (aW : a≤K)
    (hed : 2^(6*a)*2^(6*a)≤K) : headerBankFee a≤350*K^2+66*K+8 := by
  let n := (2:ℕ)^(6*a)
  have nK : n≤K := (Nat.le_mul_of_pos_right n (by positivity)).trans hed
  have h0 : 16*(6*a+1)*n≤16*(6*K+1)*K :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 (Nat.succ_le_succ (Nat.mul_le_mul_left 6 aW))) nK
  have h1 : (8*(6*a)+22)*(n*n)≤(48*K+22)*K := by
    have aa := Nat.mul_le_mul_left 48 aW
    exact Nat.mul_le_mul (by omega) hed
  have h2 : 4*n≤4*K := Nat.mul_le_mul_left 4 nK
  have h3 : (headerCap a+18)*(n*n)≤(206*K+24)*K := by
    have aa := Nat.mul_le_mul_left 206 aW
    unfold headerCap
    exact Nat.mul_le_mul (by omega) hed
  calc
    headerBankFee a = 16*(6*a+1)*n+(8*(6*a)+22)*(n*n)+4*n+4+
      (headerCap a+18)*(n*n)+4 := by unfold headerBankFee allPairsCap n; ring
    _ ≤ 16*(6*K+1)*K+(48*K+22)*K+4*K+4+(206*K+24)*K+4 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h0 h1) h2) 4) h3) 4
    _ = _ := by ring

theorem side_port_writer_is_bounded_by_actual_body_words
    {w own key prec page K : ℕ} (x : FramedEdge w own key prec page)
    (port : w≤K) (left : x.left.body.length≤K) (right : x.right.body.length≤K) :
    framedCopiesFee x≤14*K+62 := by
  have p := Nat.mul_le_mul_left 4 port
  have l := Nat.mul_le_mul_left 3 left
  have r := Nat.mul_le_mul_left 3 right
  unfold framedCopiesFee nextPortFee
  omega

theorem real_mask_row_copy_fits_width {q K : ℕ} (x : MaskRow q) (rank : q≤K)
    (l : x.address.labels.1.length≤K) (r : x.address.labels.2.length≤K)
    (bits : x.bits.length≤K) : copiedMaskFee x+5≤12*K+18 := by
  unfold copiedMaskFee
  omega

theorem real_replay_from_physical_extents {a q i copies p m n K : ℕ}
    (aW : a≤K) (rank : q+1≤K) (headerCount : 2^(6*a)*2^(6*a)≤K)
    (copiesW : copies≤K) (tilesW : 2^(i+1)≤K) (precW : p≤K)
    (maskCost : m≤K*(12*K+18)) (seatCount : n≤K) :
    selectedReplayFee a q i copies p m n ≤ replayGeometryRoof K := by
  have hdr := header_bank_fee_from_actual_header_count aW headerCount
  have build := buildCap_mono a (q+1) headerCount (le_refl 0) (le_refl 0) copiesW tilesW precW
  have build' : buildCap a (q+1) K 0 0 K K K≤buildCap K K K 0 0 K K K := by
    unfold buildCap headerTraffic spanFee keyCap pageCap tileCap layerCap weightCap recordStride
    gcongr
  have space : 3*(a+(q-a+13*a))+51≤45*K+51 := by omega
  have ranks : 2*(3*(q+1)+1)≤2*(3*K+1) := by omega
  unfold selectedReplayFee replayGeometryRoof
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hdr ranks) (Nat.add_le_add_left maskCost 3))
    (Nat.add_le_add_left (Nat.mul_le_mul space seatCount) 3)) (build.trans build')) 10

#print axioms header_bank_fee_from_actual_header_count
#print axioms side_port_writer_is_bounded_by_actual_body_words
#print axioms real_mask_row_copy_fits_width
#print axioms real_replay_from_physical_extents
end J6R110ScopeWordRates