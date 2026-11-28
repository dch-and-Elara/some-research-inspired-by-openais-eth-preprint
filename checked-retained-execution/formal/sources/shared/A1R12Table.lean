import A1R12Cross

/-! Sequential generation of the assignment-independent numeric cell
tapes, with a separate bit-write charge for each emitted register. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime

def mapMeter {A B : Type*} (q : A → Meter B) (width : ℕ) : List A → Meter (List B)
  | [] => ⟨[],0⟩
  | x::xs =>
    let a := q x
    let b := mapMeter q width xs
    ⟨a.result::b.result,a.steps+b.steps+width+4⟩

theorem mapMeter_exact {A B : Type*} (q : A → Meter B) (width cap : ℕ) (xs : List A)
    (H : ∀ x∈xs,(q x).steps≤cap) :
    (mapMeter q width xs).result=xs.map (fun x => (q x).result) ∧
    (mapMeter q width xs).steps≤xs.length*(cap+width+4) := by
  induction xs with
  | nil => simp [mapMeter]
  | cons x xs ih =>
    obtain ⟨ha,hc⟩ := ih (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨by simp [mapMeter,ha],?_⟩
    change (q x).steps+(mapMeter q width xs).steps+width+4≤(xs.length+1)*(cap+width+4)
    have hq := H x List.mem_cons_self
    rw [Nat.succ_mul xs.length]
    omega

def vectorMap {B : Type*} {n : ℕ} (q : Fin n → Meter B) (width : ℕ) : Meter (List B) :=
  mapMeter q width (List.finRange n)

theorem vectorMap_exact {B : Type*} {n : ℕ} (q : Fin n → Meter B) (width cap : ℕ)
    (H : ∀ x,(q x).steps≤cap) :
    (vectorMap q width).result=List.ofFn (fun x => (q x).result) ∧
    (vectorMap q width).steps≤n*(cap+width+4) := by
  simpa only [vectorMap,List.finRange,List.length_ofFn,List.map_ofFn,Function.comp_def] using
    mapMeter_exact q width cap (List.finRange n) (fun x _ => H x)

def matrixMap {B : Type*} {r c : ℕ} (q : Fin r → Fin c → Meter B) (width : ℕ) :
    Meter (List (List B)) :=
  vectorMap (fun i => vectorMap (q i) width) 0

theorem matrixMap_exact {B : Type*} {r c : ℕ} (q : Fin r → Fin c → Meter B) (width cap : ℕ)
    (H : ∀ i j,(q i j).steps≤cap) :
    (matrixMap q width).result=List.ofFn (fun i => List.ofFn (fun j => (q i j).result)) ∧
    (matrixMap q width).steps≤r*(c*(cap+width+4)+4) := by
  have h j := vectorMap_exact (q j) width cap (H j)
  obtain ⟨hr,hc⟩ := vectorMap_exact (fun i => vectorMap (q i) width) 0 (c*(cap+width+4))
    (fun i => (h i).2)
  refine ⟨?_,by simpa only [matrixMap,add_zero] using hc⟩
  rw [matrixMap,hr]
  congr 1
  funext i
  exact (h i).1

theorem getD_ofFn {B : Type*} {n : ℕ} (f : Fin n → B) (i : Fin n) (x : B) :
    (List.ofFn f).getD i.val x=f i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

#print axioms mapMeter_exact
#print axioms matrixMap_exact
#print axioms getD_ofFn
end A1R12
