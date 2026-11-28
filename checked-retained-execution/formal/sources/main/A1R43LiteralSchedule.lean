import J6R11Threshold
import J1PPrintedMesh

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000

/-! The original A1 packing schedule, not a larger auxiliary host.
For m simulated incidences take s=16*64^2*m, and h=L*floor(s/(DL)).
The source's own root slot and collision margins apply first at s/2;
they then prove both A2 low-dimension load capacity and activity of
the actual floored physical M. -/
namespace A1R43Literal
open J1PPrinted J6R11Threshold

def starSize (m : ℕ) : ℕ := 16*64^2*m

def nativeA (m : ℕ) : ℕ := J9PrintedSchedule.rootA (Nat.clog 2 (starSize m))
def smallA (m : ℕ) : ℕ := nativeA m-1
def fullCells (m : ℕ) : ℕ := J9PrintedSchedule.arrayCard (nativeA m)
def lengthL (m : ℕ) : ℕ := 2^nativeA m
def copies (m : ℕ) : ℕ := starSize m/(fullCells m*lengthL m)
def floorWires (m : ℕ) : ℕ := fullCells m*(copies m*lengthL m)
def half (m : ℕ) : ℕ := starSize m/2

theorem source_half (m : ℕ) : half m=32768*m := by
  unfold half starSize
  change 65536*m/2=32768*m
  omega

theorem twice_half (m : ℕ) : starSize m=2*half m := by
  rw [source_half]
  unfold starSize
  ring

theorem cutoff_below_half (m : ℕ) (hm : 0<m)
    (hq : 4≤(Nat.clog 2 (starSize m)).sqrt) :
    J9PrintedSchedule.leafThreshold (starSize m) (Nat.clog 2 (starSize m))<half m := by
  let q := (Nat.clog 2 (starSize m)).sqrt
  let t := half m
  have ht : 2≤t := by dsimp [t]; rw [source_half]; omega
  have hq' : 4≤q := hq
  have hmul : 4*(t-1)≤q*(t-1) := Nat.mul_le_mul_right _ hq'
  have h2 : 2*t≤4*(t-1) := by omega
  have ht1 : t-1+1=t := by omega
  have hqt : t*q=q*(t-1)+q := by
    calc
      t*q = (t-1+1)*q := by rw [ht1]
      _ = _ := by ring
  unfold J9PrintedSchedule.leafThreshold
  change (starSize m+q-1)/q<t
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<q)).2
  have he : starSize m=2*t := twice_half m
  omega

theorem source_dim_zero (m : ℕ) :
    stepA (Nat.clog 2 (starSize m)) 0=nativeA m := by
  simp [nativeA,stepA,stepU,J9PrintedSchedule.rootA,J9PrintedSchedule.rootU,epsDen]

theorem source_L_zero (m : ℕ) :
    stepL (Nat.clog 2 (starSize m)) 0=lengthL m := by
  rw [stepL,source_dim_zero,lengthL]

theorem source_D_zero (m : ℕ) :
    stepD (Nat.clog 2 (starSize m)) 0=fullCells m := by
  unfold stepD fullCells J9PrintedSchedule.arrayCard
  rw [source_dim_zero]

structure PrintedMargins (m : ℕ) : Prop where
  full_dim : smallA m+1=nativeA m
  active_half : J9PrintedSchedule.leafThreshold (starSize m) (Nat.clog 2 (starSize m))<half m
  wire_window : half m≤floorWires m ∧ floorWires m≤starSize m
  collision_A2 : 2*(J9PrintedSchedule.arrayCard (smallA m))^2*3≤m
  paired_capacity : 2*m≤(copies m*2^smallA m)*J9PrintedSchedule.arrayCard (smallA m)
  local_degree : 3≤sourceDelta (starSize m)
  u_pos : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (starSize m))

theorem printed_margins (m : ℕ) (hm : 0<m)
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (starSize m))) :
    PrintedMargins m := by
  have hu := (J9PrintedSchedule.rootU_range (Nat.clog 2 (starSize m))).1
  have hLambda : 16≤Nat.clog 2 (starSize m) := by omega
  have hq : 4≤(Nat.clog 2 (starSize m)).sqrt :=
    Nat.le_sqrt.mpr (by norm_num; omega)
  have hAct := cutoff_below_half m hm hq
  obtain ⟨hD,hLD,hΔ⟩ := source_packing_conditions (starSize m) (half m) 0 hU hAct
  rw [source_D_zero] at hD
  rw [source_L_zero,source_D_zero] at hLD
  rw [source_L_zero] at hΔ
  have hA : smallA m+1=nativeA m := by
    unfold smallA nativeA J9PrintedSchedule.rootA; omega
  have hD' : fullCells m=4096*J9PrintedSchedule.arrayCard (smallA m) := by
    unfold fullCells J9PrintedSchedule.arrayCard
    rw [←hA,show 2*(smallA m+1)=2*smallA m+2 by omega,pow_add]
    ring
  have hL' : lengthL m=2*2^smallA m := by
    rw [lengthL,←hA,pow_succ,mul_comm]
  have h3 : 3≤sourceDelta (starSize m) := by
    rw [hL'] at hΔ
    have pos : 0<(2:ℕ)^smallA m := pow_pos (by decide) _
    omega
  let d := fullCells m*lengthL m
  have dpos : 0<d := by
    dsimp [d]
    unfold fullCells lengthL J9PrintedSchedule.arrayCard
    positivity
  have dcap : d≤half m := by
    dsimp [d]
    rwa [mul_comm]
  have hs := Nat.mod_add_div (starSize m) d
  have hr := Nat.mod_lt (starSize m) dpos
  have he : d*(starSize m/d)=floorWires m := by
    change (fullCells m*lengthL m)*copies m=floorWires m
    unfold floorWires
    ring
  rw [he] at hs
  have hhalf := twice_half m
  have hlo : half m≤floorWires m := by omega
  have hhi : floorWires m≤starSize m := by omega
  refine ⟨hA,hAct,⟨hlo,hhi⟩,?_,?_,h3,hU⟩
  · have hg := (Nat.mul_le_mul_left (2*(fullCells m)^2) h3).trans hD
    rw [hD',source_half] at hg
    have same : 2*(4096*J9PrintedSchedule.arrayCard (smallA m))^2*3 =
        16777216*(2*(J9PrintedSchedule.arrayCard (smallA m))^2*3) := by ring
    rw [same] at hg
    omega
  · have same : floorWires m =
        8192*((copies m*2^smallA m)*J9PrintedSchedule.arrayCard (smallA m)) := by
      rw [floorWires,hD',hL']
      ring
    rw [same,source_half] at hlo
    omega

#print axioms cutoff_below_half
#print axioms source_dim_zero
#print axioms source_L_zero
#print axioms source_D_zero
#print axioms printed_margins
end A1R43Literal
