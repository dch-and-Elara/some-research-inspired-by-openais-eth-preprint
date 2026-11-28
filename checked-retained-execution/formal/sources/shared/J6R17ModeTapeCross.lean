import J6R17ModeTapeRange
import J6R17ModeTapeHeaders
import Mathlib.Data.List.ProdSigma

/-! Sequential serialization of physical addresses. A mode carries
its actual unordered packet key, copy number, residue tile, and the
positive weight word. That final word encodes Taylor order plus one. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R15ModeCost J6R14LayoutCost J6R12CollisionEdges

structure RawMode (q : ℕ) where
  key : CellWord
  page : Word q
  tile : Word q
  weight : Word q

/-- Every append retains its intermediate output records in order.
The fee counts an explicit traverse/copy at each concatenation. -/
def flatMeter {A B : Type*} (stride : ℕ) (f : A→Meter (List B)) : List A→Meter (List B)
  | [] => ⟨[],0⟩
  | x::xs =>
    let a := f x
    let b := flatMeter stride f xs
    ⟨a.result++b.result,a.steps+b.steps+stride*a.result.length+8⟩

theorem flatMeter_exact {A B : Type*} (stride cap len : ℕ)
    (f : A→Meter (List B)) (g : A→List B) (xs : List A)
    (H : ∀ x∈xs,(f x).result=g x ∧ (f x).steps≤cap ∧ (g x).length=len) :
    let z := flatMeter stride f xs
    z.result=xs.flatMap g ∧ z.result.length=xs.length*len ∧
      z.steps≤xs.length*(cap+stride*len+8) := by
  induction xs with
  | nil => simp [flatMeter]
  | cons x xs ih =>
    let a := f x
    let b := flatMeter stride f xs
    obtain ⟨ha,hc,hl⟩ := H x List.mem_cons_self
    obtain ⟨hb,hbL,hbC⟩ := ih (fun _ hx => H _ (List.mem_cons_of_mem _ hx))
    change a.result=_ at ha
    change a.steps≤_ at hc
    change b.result=_ at hb
    change b.result.length=_ at hbL
    change b.steps≤_ at hbC
    refine ⟨?_,?_,?_⟩
    · change a.result++b.result=g x++xs.flatMap g
      rw [ha,hb]
    · change (a.result++b.result).length=(xs.length+1)*len
      rw [List.length_append,ha,hl,hbL,Nat.add_mul,one_mul,Nat.add_comm]
    · change a.steps+b.steps+stride*a.result.length+8≤(xs.length+1)*(cap+stride*len+8)
      rw [ha,hl,Nat.add_mul,one_mul]
      omega

def recordStride (a q : ℕ) : ℕ :=
  24*a+6*q+24

def weightStage {q : ℕ} (a : ℕ) (k : CellWord) (x y : Word q)
    (ws : List (Word q)) : Meter (List (RawMode q)) :=
  mapMeter (fun w=>⟨⟨k,x,y,w⟩,recordStride a q⟩) ws

def tileStage {q : ℕ} (a : ℕ) (k : CellWord) (x : Word q)
    (ts ws : List (Word q)) : Meter (List (RawMode q)) :=
  flatMeter (recordStride a q) (fun y=>weightStage a k x y ws) ts

def pageStage {q : ℕ} (a : ℕ) (k : CellWord)
    (ps ts ws : List (Word q)) : Meter (List (RawMode q)) :=
  flatMeter (recordStride a q) (fun x=>tileStage a k x ts ws) ps

def keyStage {q : ℕ} (a : ℕ) (ks : List CellWord)
    (ps ts ws : List (Word q)) : Meter (List (RawMode q)) :=
  flatMeter (recordStride a q) (fun k=>pageStage a k ps ts ws) ks

def weightCap (a q w : ℕ) : ℕ := (recordStride a q+6)*w
def layerCap (a q n fee out : ℕ) : ℕ := n*(fee+recordStride a q*out+8)
def tileCap (a q t w : ℕ) : ℕ := layerCap a q t (weightCap a q w) w
def pageCap (a q p t w : ℕ) : ℕ := layerCap a q p (tileCap a q t w) (t*w)
def keyCap (a q k p t w : ℕ) : ℕ := layerCap a q k (pageCap a q p t w) (p*(t*w))

def rawJoin {q : ℕ} (ks : List CellWord) (ps ts ws : List (Word q)) : List (RawMode q) :=
  ks.flatMap fun k=>ps.flatMap fun x=>ts.flatMap fun y=>ws.map fun w=>⟨k,x,y,w⟩

theorem weightStage_exact {q : ℕ} (a : ℕ) (k : CellWord) (x y : Word q)
    (ws : List (Word q)) :
    let z := weightStage a k x y ws
    z.result=ws.map (fun w=>⟨k,x,y,w⟩) ∧ z.result.length=ws.length ∧
      z.steps≤weightCap a q ws.length := by
  have H := mapMeter_exact (fun w : Word q=>⟨(⟨k,x,y,w⟩ : RawMode q),recordStride a q⟩)
    (fun w=>⟨k,x,y,w⟩) (recordStride a q) ws (fun _ _=>⟨rfl,le_rfl⟩)
  exact ⟨H.1,by rw [weightStage,H.1,List.length_map],H.2⟩

theorem tileStage_exact {q : ℕ} (a : ℕ) (k : CellWord) (x : Word q)
    (ts ws : List (Word q)) :
    let z := tileStage a k x ts ws
    z.result=(ts.flatMap fun y=>ws.map fun w=>⟨k,x,y,w⟩) ∧
    z.result.length=ts.length*ws.length ∧ z.steps≤tileCap a q ts.length ws.length :=
  flatMeter_exact _ _ _ (fun y=>weightStage a k x y ws)
    (fun y=>ws.map fun w=>⟨k,x,y,w⟩) ts
      (fun y _=>⟨(weightStage_exact a k x y ws).1,(weightStage_exact a k x y ws).2.2,List.length_map _⟩)

theorem pageStage_exact {q : ℕ} (a : ℕ) (k : CellWord) (ps ts ws : List (Word q)) :
    let z := pageStage a k ps ts ws
    z.result=(ps.flatMap fun x=>ts.flatMap fun y=>ws.map fun w=>⟨k,x,y,w⟩) ∧
    z.result.length=ps.length*(ts.length*ws.length) ∧
    z.steps≤pageCap a q ps.length ts.length ws.length :=
  flatMeter_exact _ _ _ (fun x=>tileStage a k x ts ws)
    (fun x=>ts.flatMap fun y=>ws.map fun w=>⟨k,x,y,w⟩) ps
      (fun x _=>by
        obtain ⟨he,hl,hc⟩ := tileStage_exact a k x ts ws
        exact ⟨he,hc,by simpa only [he] using hl⟩)

theorem keyStage_exact {q : ℕ} (a : ℕ) (ks : List CellWord) (ps ts ws : List (Word q)) :
    let z := keyStage a ks ps ts ws
    z.result=rawJoin ks ps ts ws ∧
    z.result.length=ks.length*(ps.length*(ts.length*ws.length)) ∧
    z.steps≤keyCap a q ks.length ps.length ts.length ws.length :=
  flatMeter_exact _ _ _ (fun k=>pageStage a k ps ts ws)
    (fun k=>ps.flatMap fun x=>ts.flatMap fun y=>ws.map fun w=>⟨k,x,y,w⟩) ks
      (fun k _=>by
        obtain ⟨he,hl,hc⟩ := pageStage_exact a k ps ts ws
        exact ⟨he,hc,by simpa only [he] using hl⟩)

def keyLimit {q : ℕ} (a : ℕ) (ps ts ws : List (Word q)) (H : List CellWord) : ℕ :=
  keyCap a q H.length ps.length ts.length ws.length

theorem keyCap_mono (a q : ℕ) {k p t w K P T W : ℕ}
    (hK : k≤K) (hP : p≤P) (hT : t≤T) (hW : w≤W) :
    keyCap a q k p t w≤keyCap a q K P T W := by
  unfold keyCap pageCap tileCap layerCap weightCap
  gcongr

#print axioms flatMeter_exact
#print axioms weightStage_exact
#print axioms tileStage_exact
#print axioms pageStage_exact
#print axioms keyStage_exact
#print axioms keyCap_mono
end J6R17ModeTape



