import AffineCompileTree
import AffineCostMatrix

namespace AffineCompile

open AffineEdge AffineCost
open AffineCost.Bit (Run)

/-- Generate both prefix branches, retaining the recursive list only within
this call. Every emitted bit string is made of explicit Boolean cells. -/
def bitCellWords : ℕ → Run (List Cells)
  | 0 => emit [[]]
  | q+1 =>
    let old := bitCellWords q
    let lo := mapList (fun xs => emit (false::xs)) old.value
    let hi := mapList (fun xs => emit (true::xs)) old.value
    let out := appendList lo.value hi.value
    ⟨out.value, 16+old.steps+lo.steps+hi.steps+out.steps⟩

theorem bitCellWords_length (q : ℕ) : (bitCellWords q).value.length = 2^q := by
  induction q with
  | zero => decide
  | succ q ih => simp [bitCellWords, ih, pow_succ, Nat.mul_two]

theorem bitCellWords_steps (q : ℕ) : (bitCellWords q).steps+64 ≤ 128*2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
    let xs := (bitCellWords q).value
    let lo := mapList (fun b : Cells => emit (false::b)) xs
    let hi := mapList (fun b : Cells => emit (true::b)) xs
    have hl : lo.steps ≤ 8+2^q*24 := by
      dsimp only [lo, xs]
      simpa only [bitCellWords_length] using
        mapList_steps (fun b : Cells => emit (false::b)) (bitCellWords q).value 8 (fun _ _ => le_rfl)
    have hh : hi.steps ≤ 8+2^q*24 := by
      dsimp only [hi, xs]
      simpa only [bitCellWords_length] using
        mapList_steps (fun b : Cells => emit (true::b)) (bitCellWords q).value 8 (fun _ _ => le_rfl)
    have hlen : lo.value.length = 2^q := by simp [lo, xs, bitCellWords_length]
    have hp : 0 < 2^q := Nat.pow_pos (by decide : 0 < (2:ℕ))
    change 16+(bitCellWords q).steps+lo.steps+hi.steps+(appendList lo.value hi.value).steps+64 ≤ _
    rw [appendList_steps, hlen, pow_succ]
    omega

@[simp] theorem decodeBits_cons (q : ℕ) (b : Bool) (xs : Cells) :
    decodeBits (q+1) (b::xs) = Fin.cons b (decodeBits q xs) := by
  funext t
  refine Fin.cases ?_ (fun i => ?_) t
  · simp [decodeBits]
  · simp [decodeBits]

theorem bitCellWords_decode (q : ℕ) :
    (bitCellWords q).value.map (decodeBits q) = bitWords q := by
  induction q with
  | zero =>
    have he : decodeBits 0 [] = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
    simp [bitCellWords, emit, bitWords, he]
  | succ q ih =>
    simp only [bitCellWords, appendList_value, mapList_value, emit, List.map_append,
      List.map_map, Function.comp_def, decodeBits_cons, bitWords]
    rw [← ih]
    simp only [List.map_map, Function.comp_def]

private theorem productList_map {A B C E : Type}
    (xs : List A) (ys : List B) (f : A → C) (g : B → E) :
    (xs.product ys).map (fun p => (f p.1,g p.2)) = (xs.map f).product (ys.map g) := by
  unfold List.product
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_map, Function.comp_def,
      List.map_cons, ih]

def cellWords (q : ℕ) : Run (List CellWord) :=
  let bs := bitCellWords q
  let out := productList bs.value bs.value
  ⟨out.value, 16+bs.steps+out.steps⟩

theorem cellWords_decode (q : ℕ) : (cellWords q).value.map (decodeWord q) = words q := by
  change (productList (bitCellWords q).value (bitCellWords q).value).value.map
    (fun p => (decodeBits q p.1, decodeBits q p.2)) = _
  rw [productList_value, productList_map _ _ (decodeBits q) (decodeBits q), bitCellWords_decode]
  rfl

theorem cellWords_length (q : ℕ) : (cellWords q).value.length = 4^q := by
  have h := congrArg List.length (cellWords_decode q)
  simpa only [List.length_map, words_length] using h

theorem cellWords_steps (q : ℕ) : (cellWords q).steps ≤ 256*4^q := by
  have h1 := bitCellWords_steps q
  have h2 := productList_steps (bitCellWords q).value (bitCellWords q).value
  have hp : 0 < 2^q := Nat.pow_pos (by decide : 0 < (2:ℕ))
  have hm := Nat.mul_le_mul_left (2^q) (show 1 ≤ 2^q by omega)
  have hd : (4:ℕ)^q = 2^q*2^q := by
    change ((2:ℕ)*2)^q = _
    rw [mul_pow]
  simp only [cellWords, bitCellWords_length] at *
  rw [hd]
  nlinarith only [h1,h2,hm,hp]

abbrev PackedTask (q : ℕ) := CellWord × CellWord × Fin q

def decodeTask {q : ℕ} (t : PackedTask q) : Task q :=
  (decodeWord q t.1, decodeWord q t.2.1, t.2.2)

def packedSchedule (q : ℕ) : Run (List (PackedTask q)) :=
  let ws := cellWords q
  let is := indexList q
  let tail := productList ws.value is.value
  let out := productList ws.value tail.value
  ⟨out.value, 16+ws.steps+is.steps+tail.steps+out.steps⟩

theorem packedSchedule_decode (q : ℕ) :
    (packedSchedule q).value.map decodeTask = tasks q := by
  let xs := (cellWords q).value
  let is := (indexList q).value
  let f (p : CellWord × Fin q) := (decodeWord q p.1, id p.2)
  change ((productList xs (productList xs is).value).value.map
    (fun p => (decodeWord q p.1, f p.2))) = _
  rw [productList_value, productList_value, productList_map _ _ (decodeWord q) f]
  dsimp only [f]
  rw [productList_map xs is (decodeWord q) id, List.map_id]
  dsimp only [xs,is]
  rw [cellWords_decode, indexList_value]
  rfl

theorem packedSchedule_length (q : ℕ) : (packedSchedule q).value.length = (4^q)*(4^q)*q := by
  have h := congrArg List.length (packedSchedule_decode q)
  simpa only [List.length_map, tasks_length] using h

def taskGenerationBound (D q : ℕ) : ℕ :=
  32+256*D+32*(q+1)^2+D*(32+40*q)+D*(32+40*(D*q))

theorem packedSchedule_steps (q : ℕ) :
    (packedSchedule q).steps ≤ taskGenerationBound (4^q) q := by
  have h1 := cellWords_steps q
  have h2 := indexList_steps q
  let xs := (cellWords q).value
  let is := (indexList q).value
  let tail := productList xs is
  have hlen : tail.value.length = 4^q*q := calc
    _ = xs.length*is.length := by
      dsimp only [tail]
      rw [productList_value]
      exact List.length_product _ _
    _ = _ := by simp only [xs,is,cellWords_length,indexList_value,List.length_finRange]
  have h3 : tail.steps ≤ 8+(4^q)*(32+40*q) := by
    simpa only [tail,xs,is,cellWords_length,indexList_value,List.length_finRange] using
      productList_steps xs is
  have h4 : (productList xs tail.value).steps ≤ 8+(4^q)*(32+40*(4^q*q)) := by
    simpa only [xs,cellWords_length,hlen] using productList_steps xs tail.value
  change 16+(cellWords q).steps+(indexList q).steps+tail.steps+
    (productList xs tail.value).steps ≤ _
  unfold taskGenerationBound
  omega

def compileDescriptor {q : ℕ} (is : List (Fin q)) (t : PackedTask q) : Run (Task q × Expr q) :=
  let generated := coefficientCells is t.1 t.2.1 t.2.2
  let tree := materialize generated.value
  ⟨(decodeTask t,tree.value), 16+generated.steps+tree.steps⟩

@[simp] theorem compileDescriptor_value {q : ℕ} (t : PackedTask q) :
    (compileDescriptor (List.finRange q) t).value = (decodeTask t, taskExpr (decodeTask t)) := by
  simp [compileDescriptor, taskExpr, decodeTask]

def descriptorGenerationBound (D q : ℕ) : ℕ :=
  16+coefficientGenerationBound D q+16*coreSize D q

theorem compileDescriptor_steps {q : ℕ} (t : PackedTask q) :
    (compileDescriptor (List.finRange q) t).steps ≤ descriptorGenerationBound (4^q) q := by
  have h := coefficientCells_steps (List.finRange q) (by simp) t.1 t.2.1 t.2.2
  have ht := taskExpr_size (decodeTask t)
  simp only [compileDescriptor, descriptorGenerationBound, materialize_steps,
    coefficientCells_value]
  change 16+(coefficientCells (List.finRange q) t.1 t.2.1 t.2.2).steps+
      16*(taskExpr (decodeTask t)).nodes ≤ _
  have hm := Nat.mul_le_mul_left 16 ht
  omega

/-- Generate all indexed coefficient tasks and fully materialized expression
descriptors from the dimension alone. Decoding a task retains the explicit
bit lists in two sequential-lookup closures. No labels are read here. -/
def compile (q : ℕ) : Run (List (Task q × Expr q)) :=
  let ts := packedSchedule q
  let is := indexList q
  let out := mapList (compileDescriptor is.value) ts.value
  ⟨out.value, 16+ts.steps+is.steps+out.steps⟩

theorem compile_value (q : ℕ) :
    (compile q).value = (tasks q).map (fun t => (t,taskExpr t)) := by
  simp only [compile, indexList_value, mapList_value, compileDescriptor_value]
  exact (List.map_map (f := decodeTask) (g := fun t => (t,taskExpr t))).symm.trans
    (congrArg (List.map fun t => (t,taskExpr t)) (packedSchedule_decode q))

theorem compile_length (q : ℕ) : (compile q).value.length = (4^q)*(4^q)*q := by
  rw [compile_value, List.length_map, tasks_length]

/-- Polynomial primitive-step bound with D = 4^q. This is the generation
charge, independent of the representation or numerical sizes of the labels. -/
def generationBound (D q : ℕ) : ℕ :=
  24+taskGenerationBound D q+32*(q+1)^2+D*D*q*(16+descriptorGenerationBound D q)

theorem compile_steps (q : ℕ) : (compile q).steps ≤ generationBound (4^q) q := by
  have h1 := packedSchedule_steps q
  have h2 := indexList_steps q
  have h3 := mapList_steps (compileDescriptor (indexList q).value)
    (packedSchedule q).value (descriptorGenerationBound (4^q) q) (fun t _ => by
      simpa only [indexList_value] using compileDescriptor_steps t)
  rw [packedSchedule_length] at h3
  simp only [compile, generationBound]
  omega

end AffineCompile
