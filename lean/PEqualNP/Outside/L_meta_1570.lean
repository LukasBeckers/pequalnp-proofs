import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _hOp _hFan hEval
  let run : List Gate → List Bool → List Bool :=
    fun gs x => gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
      run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
  have run_length (gs : List Gate) (x : List Bool) :
      (run gs x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => simp [run]
    | cons g gs ih => rw [run_cons, ih]; simp; omega
  have run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
      (run gs x).getD w false = x.getD w false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]
  have input_value (x : Fin 13 → Bool) (p : Fin 13) :
      Circuit.eval ⟨gates, p⟩ (List.ofFn x) = x p := by
    change (run gates (List.ofFn x)).getD (p : ℕ) false = x p
    have hp : (p : ℕ) < (List.ofFn x).length := by simp
    rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp, List.getElem_ofFn]
  have missing_value (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gates.length ≤ w) :
      Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false := by
    change (run gates (List.ofFn x)).getD w false = false
    exact List.getD_eq_default _ _ (by simpa [run_length] using hw)
  have zero_mem : (0 : Fin 13) ∈ L 0 := by
    rw [hL 0]
    decide
  have one_mem : (1 : Fin 13) ∈ L 0 := by
    rw [hL 0]
    decide
  let xZero : Fin 13 → Bool := fun v => decide (v = 0)
  let xOne : Fin 13 → Bool := fun v => decide (v = 1)
  have evalZero : Circuit.eval ⟨gates, o 0⟩ (List.ofFn xZero) = true := by
    have hg : xZero 0 = true ∨ xZero 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → xZero v = true :=
      Or.inl (by decide)
    rw [hEval 0 xZero hg]
    exact decide_eq_true ⟨0, zero_mem, by decide⟩
  have evalOne : Circuit.eval ⟨gates, o 0⟩ (List.ofFn xOne) = true := by
    have hg : xOne 0 = true ∨ xOne 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → xOne v = true :=
      Or.inr (Or.inl (by decide))
    rw [hEval 0 xOne hg]
    exact decide_eq_true ⟨1, one_mem, by decide⟩
  have low : 13 ≤ o 0 := by
    by_contra hlt
    have hk : o 0 < 13 := Nat.lt_of_not_ge hlt
    have e0 := input_value xZero ⟨o 0, hk⟩
    have e1 := input_value xOne ⟨o 0, hk⟩
    have hz : (⟨o 0, hk⟩ : Fin 13) = 0 :=
      of_decide_eq_true (e0.symm.trans evalZero)
    have ho : (⟨o 0, hk⟩ : Fin 13) = 1 :=
      of_decide_eq_true (e1.symm.trans evalOne)
    exact absurd (hz.symm.trans ho) (by decide : (0 : Fin 13) ≠ 1)
  have high : o 0 < 13 + gates.length := by
    by_contra hge
    exact Bool.false_ne_true
      ((missing_value xZero (o 0) (Nat.le_of_not_gt hge)).symm.trans evalZero)
  let xOff : Fin 13 → Bool := fun v => decide (v ∉ L 0)
  have evalOff : Circuit.eval ⟨gates, o 0⟩ (List.ofFn xOff) = false := by
    have hg : xOff 0 = true ∨ xOff 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → xOff v = true :=
      Or.inr (Or.inr (fun v hv => decide_eq_true hv))
    rw [hEval 0 xOff hg]
    refine decide_eq_false ?_
    intro hex
    obtain ⟨v, hv, hx⟩ := hex
    exact (of_decide_eq_true hx) hv
  have not_both (t : Fin 13) (ht : t ≠ 0) : ¬ ((0 : Fin 13) ∈ L t ∧ (1 : Fin 13) ∈ L t) := by
    intro hboth
    rw [hL t] at hboth
    fin_cases t <;> simp [Finset.mem_insert, Finset.mem_singleton] at hboth ; exact ht rfl
  have evalCo (t : Fin 13) (ht : t ≠ 0) :
      Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    let x : Fin 13 → Bool := fun v => decide (v ∉ L t)
    have hdis : (0 : Fin 13) ∉ L t ∨ (1 : Fin 13) ∉ L t := by
      by_contra h
      exact not_both t ht (by simpa using h)
    have hex : ∃ v ∈ L 0, x v = true := by
      rcases hdis with h0 | h1
      · exact ⟨0, zero_mem, decide_eq_true h0⟩
      · exact ⟨1, one_mem, decide_eq_true h1⟩
    have hg : x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true := by
      rcases hdis with h0 | h1
      · exact Or.inl (decide_eq_true h0)
      · exact Or.inr (Or.inl (decide_eq_true h1))
    rw [hEval 0 x hg]
    exact decide_eq_true hex
  exact ⟨low, high, evalZero, evalOne, evalOff, evalCo⟩
