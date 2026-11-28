import J4R43LiteralOutsideValue

/-! Exact native marginal traversal. No matching cache or child
truth-table oracle is assumed. This simple version rechecks all actual
wire addresses on a local port visit; the polynomial bounds count
those comparisons as well. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5300000

structure NativeMeter (R : Type) where
  value : R
  addressOps : ℕ
  tableOps : ℕ
  ringOps : ℕ

def scanBoolean {A : Type} (test : A→Bool) : List A→Bool×ℕ
  | [] => (false,0)
  | x::xs =>
      let out := scanBoolean test xs
      (test x || out.1,out.2+1)

theorem scanBoolean_true {A : Type} (test : A→Bool) (xs : List A) :
    (scanBoolean test xs).1=true ↔ ∃ x∈xs,test x=true := by
  induction xs with
  | nil => simp [scanBoolean]
  | cons x xs ih =>
    simp only [scanBoolean,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h|⟨y,hy,ht⟩)
      · exact ⟨x,Or.inl rfl,h⟩
      · exact ⟨y,Or.inr hy,ht⟩
    · rintro ⟨y,h|h,hb⟩
      · exact Or.inl (h ▸ hb)
      · exact Or.inr ⟨y,h,hb⟩

theorem scanBoolean_fee {A : Type} (test : A→Bool) (xs : List A) :
    (scanBoolean test xs).2=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scanBoolean,ih,List.length_cons]

variable {R : Type}

def foldNative (combine : R→R→R) (neutral : R) : List (NativeMeter R)→NativeMeter R
  | [] => ⟨neutral,0,0,0⟩
  | x::xs =>
      let out := foldNative combine neutral xs
      ⟨combine x.value out.value, x.addressOps+out.addressOps,
        x.tableOps+out.tableOps, x.ringOps+out.ringOps+1⟩

theorem foldNative_cost_exact (combine : R→R→R) (neutral : R) (xs : List (NativeMeter R)) :
    (foldNative combine neutral xs).addressOps=(xs.map NativeMeter.addressOps).sum ∧
    (foldNative combine neutral xs).tableOps=(xs.map NativeMeter.tableOps).sum ∧
    (foldNative combine neutral xs).ringOps=(xs.map NativeMeter.ringOps).sum+xs.length := by
  induction xs with
  | nil => simp [foldNative]
  | cons x xs ih =>
      rcases ih with ⟨ha,ht,hr⟩
      constructor
      · change x.addressOps+(foldNative combine neutral xs).addressOps=
          x.addressOps+(xs.map NativeMeter.addressOps).sum
        rw [ha]
      constructor
      · change x.tableOps+(foldNative combine neutral xs).tableOps=
          x.tableOps+(xs.map NativeMeter.tableOps).sum
        rw [ht]
      · change x.ringOps+(foldNative combine neutral xs).ringOps+1=
          (x.ringOps+(xs.map NativeMeter.ringOps).sum)+(xs.length+1)
        rw [hr]
        omega

variable [CommRing R]

theorem foldNative_sum (xs : List (NativeMeter R)) :
    (foldNative (·+·) 0 xs).value=(xs.map NativeMeter.value).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [foldNative,List.map_cons,List.sum_cons,ih]

theorem foldNative_prod (xs : List (NativeMeter R)) :
    (foldNative (·*·) 1 xs).value=(xs.map NativeMeter.value).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [foldNative,List.map_cons,List.prod_cons,ih]

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg

def measuredColumnHit (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (e : E) : Bool×ℕ :=
  scanBoolean (fun r : E=>decide (Matches P t r e)) (Finset.univ.toList : List E)

theorem measured_hit_exact (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (e : E) :
    (measuredColumnHit F reg P t e).1=true ↔ columnHit P t e := by
  rw [measuredColumnHit,scanBoolean_true]
  simp [columnHit]

theorem measured_hit_fee (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (e : E) :
    (measuredColumnHit F reg P t e).2=Fintype.card E := by
  simp only [measuredColumnHit,scanBoolean_fee,Finset.length_toList,Finset.card_univ]

def paidWeight (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (e : E) (b : Bool) : NativeMeter R :=
  let hit := measuredColumnHit F reg P t e
  if hit.1 && b then ⟨1-κ,hit.2,0,1⟩ else ⟨1,hit.2,0,0⟩

theorem paid_weight_exact (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (e : E) (b : Bool) :
    (paidWeight F reg P t κ e b).value=columnArgumentWeight F reg P t κ e b := by
  unfold paidWeight columnArgumentWeight sourceColumnWeight
  by_cases h : columnHit P t e
  · have h' := (measured_hit_exact F reg P t e).mpr h
    cases b <;> simp [h,h',bit]
  · have h' : (measuredColumnHit F reg P t e).1=false :=
      Bool.eq_false_iff.mpr (fun q=>h ((measured_hit_exact F reg P t e).mp q))
    cases b <;> simp [h,h',bit]

theorem paid_weight_bounds (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (e : E) (b : Bool) :
    (paidWeight F reg P t κ e b).addressOps=Fintype.card E ∧
      (paidWeight F reg P t κ e b).tableOps=0 ∧ (paidWeight F reg P t κ e b).ringOps≤1 := by
  dsimp only [paidWeight]
  split <;> simp [measured_hit_fee]

#print axioms scanBoolean_true
#print axioms scanBoolean_fee
#print axioms foldNative_cost_exact
#print axioms foldNative_sum
#print axioms foldNative_prod
#print axioms measured_hit_exact
#print axioms measured_hit_fee
#print axioms paid_weight_exact
#print axioms paid_weight_bounds
end
end J4R43LiteralOutside

