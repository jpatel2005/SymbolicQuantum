import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs
import SymbolicQuantum.QuantumTactics

open QGate QCircuit

lemma Qeval_QRange_succ_split {n start k : ℕ} :
〚QRange_H n start (k + 1)〛 = 〚QRange_H n start k ≫ QRange_H n (start + k) 1〛 := rfl

-- Disjoint commuting lemma for QRange_H
lemma QRange_H_disj_comm {n : ℕ} (start len target : ℕ)
(ht : target < n)
(h_disjoint : target ≥ start + len) :
∀ ψ, 〚QRange_H n start len〛 (〚app (H ⟨target, ht⟩)〛 ψ) =
〚app (H ⟨target, ht⟩)〛 (〚QRange_H n start len〛 ψ) := by {
  induction len generalizing start target ht with
  | zero =>
    simp [QRange_H, Qeval]
  | succ range_len ih =>
    intro ψ
    have h_range_len : start + range_len < n := by omega
    simp [QRange_H,Qeval,h_range_len,Qeval_gate]
    change 〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 (〚app (H ⟨target, ht⟩)〛 ψ)) =
      〚app (H ⟨target, ht⟩)〛 (〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 ψ))
    rw [ih start (target) (ht) (by omega)]
    simp [Qeval,Qeval_gate]
    rw [H_comm _ (by simp;omega)]
}

-- QRange can be split in reverse order of definition
lemma Qeval_QRange_succ_split_rev {n start k : ℕ} (h : start + k < n) :
  〚QRange_H n start (k + 1)〛 = 〚QRange_H n (start + k) 1 ≫ QRange_H n start k〛 := by {
  rw [Qeval_QRange_succ_split]
  have hc1 : start + k < n := by omega
  simp [QRange_H, hc1, Qeval, Qeval_gate]
  funext ψ
  change 〚app (H ⟨start + k, h⟩)〛 (〚QRange_H n start k〛 ψ) =
    〚QRange_H n start k〛 (〚app (H ⟨start + k, h⟩)〛 ψ)
  rw [QRange_H_disj_comm]
  exact Nat.le_refl _
}

lemma QRange_H_involutive_general (m n : ℕ) (h_bound : n ≤ m + 1) :
  ∀ (ψ : QState (m + 1)),
  〚QRange_H (m+1) 0 n〛 (〚QRange_H (m+1) 0 n〛 ψ) = ψ := by {
  induction n with
  | zero =>
    intro ψ
    simp [QRange_H, Qeval]
  | succ k ih =>
    intro ψ
    nth_rw 1 [Qeval_QRange_succ_split_rev (by linarith)]
    nth_rw 1 [Qeval]
    have hk : k < m + 1 := by omega
    simp [QRange_H, hk, Qeval, Qeval_gate]
    rw [H_involutive, ih (by omega)]
}

-- QRange_H applied to one state times another is equivalent to applying to
-- one state then multiplying by the other
lemma QRange_H_distrib_disjoint (m k : ℕ) (hk_bound : k ≤ m + 1) :
  ∀ (f g : BitString (m+1) → ℂ),
  (∀ (bs : BitString (m+1)) (v : Qubit) (j : Fin (m+1)),
     (j : ℕ) < k → g (fun i => if i = j then v else bs i) = g bs) →
  〚QRange_H (m + 1) 0 k〛 (fun bs => f bs * g bs)
  = (fun bs => (〚QRange_H (m + 1) 0 k〛 f) bs * g bs) := by {
  induction k with
  | zero =>
    simp [QRange_H, Qeval]
  | succ k' ih =>
    intros f g h_ignore
    have hk' : k' < m + 1 := by omega
    rw [QRange_H]
    simp [hk', Qeval, Qeval_gate]
    rw [ih (by omega) f g]
    {
      funext bs
      have h_inv_at_k : ∀ (v : Qubit), g (fun i ↦ if i = ⟨k', hk'⟩ then v else bs i) = g bs := by {
        intro v
        apply h_ignore bs v ⟨k', hk'⟩
        simp
      }
      simp [app_H, h_inv_at_k]
      cases hk' : bs ⟨k', hk'⟩ <;> ring_nf
    }
    {
      intros bs v j hj
      apply h_ignore bs v j
      exact Nat.lt_succ_of_lt hj
    }
}

lemma QRange_H_distrib_disjoint_gen (k y : ℕ) (hk_bound : k ≤ y) :
  ∀ (f g : BitString y → ℂ),
  (∀ (bs : BitString y) (v : Qubit) (j : Fin y),
     (j : ℕ) < k → g (fun i => if i = j then v else bs i) = g bs) →
  〚QRange_H y 0 k〛 (fun bs => f bs * g bs)
  = (fun bs => (〚QRange_H y 0 k〛 f) bs * g bs) := by {
  induction k with
  | zero =>
    simp [QRange_H, Qeval]
  | succ k' ih =>
    intros f g h_ignore
    have hk' : k' < y := by omega
    rw [QRange_H]
    simp [hk', Qeval, Qeval_gate]
    rw [ih (by omega) f g]
    {
      funext bs
      have h_inv_at_k : ∀ (v : Qubit), g (fun i ↦ if i = ⟨k', hk'⟩ then v else bs i) = g bs := by {
        intro v
        apply h_ignore bs v ⟨k', hk'⟩
        simp
      }
      simp [app_H, h_inv_at_k]
      cases hk' : bs ⟨k', hk'⟩ <;> ring_nf
    }
    {
      intros bs v j hj
      apply h_ignore bs v j
      exact Nat.lt_succ_of_lt hj
    }
}

lemma embed_prefix_ket0n_succ {n : ℕ} :
embed_prefix (ket0n (n + 1)) =
(embed_prefix (embed_prefix (ket0n n))) ⊗[⟨n, by omega⟩] (embed_prefix (embed_last ket0)) := by {
  funext bs
  unfold tensor_product embed_prefix embed_last mask_left mask_right ket0n ket0 basis_state
  simp
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext i
    exact congr_fun hc1 ⟨i, by omega⟩
  }
  {
    exfalso
    apply hc2
    funext x
    exact congr_fun hc1 ⟨n, by omega⟩
  }
  {
    exfalso
    apply hc1
    apply congr_fun at hc4
    apply congr_fun at hc5
    funext k
    by_cases h : k = n
    {
      have : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.eq_of_val_eq h
      rw [this]
      exact hc4 ⟨0, Nat.zero_lt_one⟩
    }
    exact hc5 ⟨k, by omega⟩
  }
}

lemma ket0n_succ_split (m n : ℕ) (h : n < m + 1) :
  embed_arb (by omega) (ket0n (n + 1)) =
  (fun bs => embed_arb (by omega) (ket0n n) bs * ket0 (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext k
    apply congr_fun at hc1
    rw [←hc1 ⟨k, by omega⟩]
  }
  {
    exfalso
    have : bs ⟨n, h⟩ = Qubit.zero := by
      have := congr_fun hc1
      rw [this ⟨n, Nat.lt_succ_self n⟩]
    apply hc2
    funext k
    rw [this]
  }
  {
    exfalso
    apply hc1
    funext k
    apply congr_fun at hc4
    apply congr_fun at hc5
    by_cases hk : k < n
    { rw [hc5 ⟨k, hk⟩] }
    {
      have hk_eq : k = n := by omega
      simp [hk_eq]
      rw [←hc4 0]
    }
  }
}

lemma ket0n_succ_split_gen (n k : ℕ) (h : n < k) :
  embed_arb (by omega) (ket0n (n + 1)) =
  (fun bs => embed_arb (by omega) (ket0n n) bs * ket0 (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext k
    apply congr_fun at hc1
    rw [←hc1 ⟨k, by omega⟩]
  }
  {
    exfalso
    have : bs ⟨n, h⟩ = Qubit.zero := by
      have := congr_fun hc1
      rw [this ⟨n, Nat.lt_succ_self n⟩]
    apply hc2
    funext k
    rw [this]
  }
  {
    exfalso
    apply hc1
    funext k
    apply congr_fun at hc4
    apply congr_fun at hc5
    by_cases hk : k < n
    { rw [hc5 ⟨k, hk⟩] }
    {
      have hk_eq : k = n := by omega
      simp [hk_eq]
      rw [←hc4 0]
    }
  }
}

lemma ketPn_succ_split (m n : ℕ) (h : n < m + 1) :
  embed_arb (by omega) (ketPn (n + 1)) =
  (fun bs => embed_arb (by omega) (ketPn n) bs * ketP (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  cases bs ⟨n,h⟩ <;> qsimp [mul_comm]
}
