import BANANA.NonPrecompact.LinearBoringInsertion

/-!
# Linear boring insertions as shape maps

The prefix-tree map which inserts one linear boring coordinate is
shape-preserving.  It skips exactly the inserted level.  Coordinate
projections give the duplication maps used by M3 in the linear vector-space
instance.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

private theorem insertIdx_append_singleton_of_le_length
    {α : Type*} (l : List α) (x c : α) (m : ℕ)
    (h : m ≤ l.length) :
    (l ++ [c]).insertIdx m x =
      l.insertIdx m x ++ [c] := by
  induction m generalizing l with
  | zero =>
      cases l <;> simp
  | succ m ih =>
      cases l with
      | nil =>
          simp at h
      | cons a l =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simp [List.insertIdx, ih l h]

theorem prefixCoords_appendBit
    (w : BinaryWord) (c : F2) (m : ℕ)
    (h : m ≤ w.bits.length) :
    prefixCoords (appendBit w c) m
        (by simpa [appendBit] using
          h.trans (Nat.le_add_right w.bits.length 1)) =
      prefixCoords w m h := by
  funext i
  simp [prefixCoords, appendBit]

/-- Once the insertion position is inside a word, appending a source bit
commutes with inserting the boring coordinate. -/
theorem insertLinearCoordinate_appendBit_of_le
    (m : ℕ) (e : LinearBoringRule m)
    (w : BinaryWord) (c : F2)
    (h : m ≤ w.bits.length) :
    insertLinearCoordinate m e (appendBit w c) =
      appendBit (insertLinearCoordinate m e w) c := by
  apply BinaryWord.ext
  have hchild : m ≤ (appendBit w c).bits.length := by
    simpa [appendBit] using h.trans (Nat.le_add_right w.bits.length 1)
  rw [insertLinearCoordinate_of_le m e (appendBit w c) hchild,
    insertLinearCoordinate_of_le m e w h]
  simp only [appendBit]
  rw [prefixCoords_appendBit w c m h]
  exact insertIdx_append_singleton_of_le_length
    w.bits (e (prefixCoords w m h)) c m h

/-- Insertion at the end of a word is literal append. -/
theorem insertLinearCoordinate_eq_append_of_length
    (m : ℕ) (e : LinearBoringRule m)
    (w : BinaryWord) (h : w.bits.length = m) :
    insertLinearCoordinate m e w =
      ⟨w.bits ++ [e (prefixCoords w m (by omega))]⟩ := by
  apply BinaryWord.ext
  rw [insertLinearCoordinate_of_le m e w (by omega)]
  subst m
  simp

/-- A linear boring coordinate insertion is a shape-preserving map of the
binary prefix successor tree. -/
def insertLinearCoordinateShapeMap
    (m : ℕ) (e : LinearBoringRule m) :
    ShapeMap binarySucc where
  toFun := insertLinearCoordinate m e
  injective' := insertLinearCoordinate_injective m e
  level_preserving' := by
    intro a b hab
    change a.bits.length = b.bits.length at hab
    simp only [length_insertLinearCoordinate]
    rw [hab]
  weak_succ' := by
    intro a b p c hsucc
    change
      (if p = [] then some (appendBit a c) else none) =
        some b at hsucc
    by_cases hp : p = []
    · subst p
      simp only [if_pos rfl, Option.some.injEq] at hsucc
      subst b
      by_cases hlt : a.bits.length < m
      · have ha :
            insertLinearCoordinate m e a = a :=
          insertLinearCoordinate_of_lt m e a hlt
        by_cases hchild : (appendBit a c).bits.length < m
        · have hb :
              insertLinearCoordinate m e (appendBit a c) =
                appendBit a c :=
            insertLinearCoordinate_of_lt m e (appendBit a c) hchild
          refine ⟨appendBit a c, ?_, ?_⟩
          · simp [binarySucc, ha]
          · rw [hb]
        · have hlen : (appendBit a c).bits.length = m := by
            simp [appendBit] at hchild ⊢
            omega
          have hb :=
            insertLinearCoordinate_eq_append_of_length
              m e (appendBit a c) hlen
          refine ⟨appendBit a c, ?_, ?_⟩
          · simp [binarySucc, ha]
          · rw [hb]
            change
              (a.bits ++ [c]) <+:
                (a.bits ++ [c]) ++
                  [e (prefixCoords (appendBit a c) m (by omega))]
            exact List.prefix_append _ _
      · have hge : m ≤ a.bits.length := Nat.le_of_not_gt hlt
        have hcomm :=
          insertLinearCoordinate_appendBit_of_le m e a c hge
        refine ⟨insertLinearCoordinate m e (appendBit a c), ?_, le_rfl⟩
        rw [hcomm]
        simp [binarySucc]
    · simp [hp] at hsucc
  root_le' := by
    intro a ha
    change a.bits.length = 0 at ha
    have habits : a.bits = [] := List.length_eq_zero_iff.mp ha
    change a.bits <+: (insertLinearCoordinate m e a).bits
    rw [habits]
    exact List.nil_prefix

/-- The level map of one insertion: levels below `m` are fixed and all
levels from `m` onwards are shifted by one. -/
theorem insertLinearCoordinateShapeMap_level
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord) :
    LevelTree.lev (insertLinearCoordinateShapeMap m e w) =
      if LevelTree.lev w < m then
        LevelTree.lev w
      else
        LevelTree.lev w + 1 := by
  change
    (insertLinearCoordinate m e w).bits.length =
      if w.bits.length < m then w.bits.length else w.bits.length + 1
  rw [length_insertLinearCoordinate]
  by_cases h : m ≤ w.bits.length
  · simp [h, Nat.not_lt.mpr h]
  · have hlt : w.bits.length < m := Nat.lt_of_not_ge h
    simp [h, hlt]

/-- One linear insertion skips exactly its insertion level. -/
theorem insertLinearCoordinateShapeMap_skipsOnly
    (m : ℕ) (e : LinearBoringRule m) :
    (insertLinearCoordinateShapeMap m e).SkipsOnly m := by
  ext n
  constructor
  · rintro ⟨w, hw⟩
    have hlev := insertLinearCoordinateShapeMap_level m e w
    change
      (if w.bits.length < m then
          w.bits.length else w.bits.length + 1) = n at hw
    by_cases h : w.bits.length < m
    · simp [h] at hw
      rw [← hw]
      omega
    · simp [h] at hw
      rw [← hw]
      omega
  · intro hn
    change n ≠ m at hn
    by_cases hnm : n < m
    · let w : BinaryWord := ⟨List.replicate n 0⟩
      refine ⟨w, ?_⟩
      have hlev := insertLinearCoordinateShapeMap_level m e w
      simpa [w, hnm] using hlev
    · have hmn : m < n := lt_of_le_of_ne
        (Nat.le_of_not_gt hnm) (Ne.symm hn)
      let w : BinaryWord := ⟨List.replicate (n - 1) 0⟩
      refine ⟨w, ?_⟩
      have hwge : ¬ (n - 1 < m) := by omega
      have hlev := insertLinearCoordinateShapeMap_level m e w
      simpa [w, hwge] using hlev

/-- Coordinate projection, viewed as a linear boring rule. -/
def coordinateRule (n m : ℕ) (h : n < m) :
    LinearBoringRule m where
  toFun := fun x => x ⟨n, h⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

/-- If a word of length `m` extends the edge carrying bit `c` at
coordinate `n`, insertion of the projection to coordinate `n` appends
exactly `c`.  This is the local identity behind M3. -/
theorem insert_coordinateRule_of_edge
    {n m : ℕ} (hnm : n < m)
    {a b : BinaryWord} {c : F2}
    (ha : a.bits.length = n)
    (hb : b.bits.length = m)
    (hedge : appendBit a c ≤ b) :
    insertLinearCoordinate m (coordinateRule n m hnm) b =
      appendBit b c := by
  have hbm : m ≤ b.bits.length := by omega
  rw [insertLinearCoordinate_eq_append_of_length
      m (coordinateRule n m hnm) b hb]
  apply BinaryWord.ext
  congr 1
  change
    prefixCoords b m hbm ⟨n, hnm⟩ = c
  have hpref : (a.bits ++ [c]) <+: b.bits := hedge
  have htake :
      b.bits.take (n + 1) = a.bits ++ [c] := by
    have hlen : (a.bits ++ [c]).length = n + 1 := by
      simp [ha]
    exact (List.prefix_iff_eq_take.mp hpref).symm.trans
      (by rw [hlen])
  have hget := congrArg (fun l : List F2 => l[n]?) htake
  simp [prefixCoords, hb, ha] at hget ⊢
  exact hget

end BinaryWord
end SuccessorTree.NonPrecompact
