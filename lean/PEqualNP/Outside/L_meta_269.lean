import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

theorem L_meta_269 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  constructor
  · constructor
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · refine ⟨{0, 5, 10}, ?_⟩
      constructor
      · decide
      · intro j g hj ha
        rcases (List.getElem?_eq_some_iff.mp hj) with ⟨hjlen, hjget⟩
        have hjlen' : j < 11 := by simpa using hjlen
        interval_cases j
        all_goals
          have hOp := congrArg PEqualNP.CircuitLowerBounds.Gate.op hjget
          simp at hOp
          rw [← hOp] at ha
          cases ha <;> simp

  · decide

end PEqualNP.Outside
