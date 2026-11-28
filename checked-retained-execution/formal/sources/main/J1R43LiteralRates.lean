import J1R43LiteralNative
import J1R43LiteralAbundance

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6700000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! Exact finite equivalents of the two printed abundance rates, on the
same deterministic graph-only layout that reaches the native reads. -/
namespace J1R43Literal
open scoped BigOperators
open J1PhysicalHost J1PhysicalCertificate J1PhysicalIndependent J1PhysicalIncidence
open J1MainSourcePlacement J1MainSourceBridge MainProbe MainClonedCNF
open J1R14Query J1PPrinted J1PhysicalPrinted DiagonalAbundance
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B]

local notation "N" => Fintype.card (Vertex B)
local notation "r" => sourceR (printedLambda B)
local notation "Q" => sourceQ (printedLambda B)
local notation "K" => r^Q

theorem checked_J1_counts_power (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B))
    (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B)
    (vertices : List (Vertex B)) (allVertices : ∀ v,v∈vertices)
    (keys : List (ConfigKey M (Site B))) (keyNodup : keys.Nodup) (allKeys : ∀ k,k∈keys)
    (ports : List (Port (edges M))) (allPorts : ∀ e,e∈ports) :
    let H := reserveRun M b vertices ∅
    let z := selected M special H keys (List.finRange r) default
    let data := physicalData M special z.1
    let D := printableLayout M special H z.1 ports allPorts
    let k := Fintype.card (Diagonal data (pinSubset M H))
    (∀ i g, (N:ℚ)/(16*(r:ℚ)*(K:ℕ)) < ((ownedPins D i g Finset.univ).card:ℚ)) ∧
    (N:ℚ)/(16*(K:ℕ)) < k ∧ N^255 < 8*(16*k)^256 ∧
    (∀ i g, N^255 < 8*(16*r*(ownedPins D i g Finset.univ).card)^256) := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty (Symbol B) := ⟨default⟩
  have hN : 0<N := Fintype.card_pos
  obtain ⟨hr,hR,hQ,hs,_,_⟩ := actual_j1_guards N beta hN hScale hBeta
  change 2≤r at hr
  change 32≤mainRadius beta (printedLambda B) at hR
  change 6*mainRadius beta (printedLambda B)≤Q at hQ
  change 192*Q*r^2*K+6<N at hs
  have hq : 0<Q := by omega
  have hr0 : 0<r := (by decide : 0<(2:ℕ)).trans_le hr
  have hk0 : 0<K := pow_pos hr0 _
  have hsizeNat : 12≤N := by
    have ha : 1≤Q := hq
    have hb : 1≤r^2 := pow_pos hr0 _
    have hc : 1≤K := hk0
    have hl : 192≤192*Q*r^2*K := by
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 192 ha) hb) hc
    omega
  obtain ⟨_,_,cover,_,_,_,hits,_,_⟩ := checked_original_J1_layout M b beta hScale hBeta special default
    vertices allVertices keys keyNodup allKeys ports allPorts
  let H := reserveRun M b vertices ∅
  let z := selected M special H keys (List.finRange r) default
  let D := printableLayout M special H z.1 ports allPorts
  have hm : sourceMu H (Site B) (Symbol B)/2 = (H.card:ℚ)/(2*(r:ℚ)*(K:ℕ)) := by
    unfold sourceMu successProb
    simp only [Fintype.card_coe,Fintype.card_fin,Nat.cast_pow]
    have hrq : (0:ℚ)<r := by exact_mod_cast hr0
    field_simp [hrq.ne']
  have groups (i : Site B) (g : Symbol B) :
      (N:ℚ)/(16*(r:ℚ)*(K:ℕ)) < ((ownedPins D i g Finset.univ).card:ℚ) := by
    have hb := hits i g
    change sourceMu H (Site B) (Symbol B)/2<((ownedPins D i g Finset.univ).card:ℚ) at hb
    rw [hm] at hb
    exact from_reserved_card_floor N H.card r K _ hsizeNat cover hr0 hk0 hb
  have total := sum_owned_floor D special N K hk0 (by
    intro g
    simpa only [Fintype.card_fin] using groups special g)
  have hpow := printed_K_power N hN
  dsimp only
  refine ⟨groups,total,?_,?_⟩
  · have ht := finite_power_floor N 1 K _ hN (by decide) hk0 hpow (by simpa using total)
    simpa using ht
  · intro i g
    exact finite_power_floor N r K _ hN hr0 hk0 hpow (groups i g)

#print axioms checked_J1_counts_power

end
end J1R43Literal