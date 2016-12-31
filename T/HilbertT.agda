module T.HilbertT where

open import Basics

---------------------------------------
-- Hilbert system for constructive T --
---------------------------------------

-- Definition.

data ThmT (Γ : Cx modal) :  Ty modal -> Set where

  T-var : ∀ {A : Ty modal} -> (A ∈ Γ) -> ThmT Γ A
  T-k : ∀ {A B : Ty modal} ->  ThmT Γ (A => (B => A))
  T-s : ∀ {A B C : Ty modal} -> ThmT Γ ((A => B => C) => (A => B) => (A => C))
  T-MP : ∀ {A B : Ty modal} -> ThmT Γ (A => B) -> ThmT Γ A -> ThmT Γ B
  T-NEC : ∀ {A : Ty modal} -> ThmT · A -> ThmT Γ (□ A)
  T-prod1 : ∀ {A B : Ty modal} -> ThmT Γ (A => B => A ∧ B)
  T-prod2 : ∀ {A B : Ty modal} -> ThmT Γ (A ∧ B => A)
  T-prod3 : ∀ {A B : Ty modal} -> ThmT Γ (A ∧ B => B)
  T-axK : ∀ {A B : Ty modal} -> ThmT Γ (□(A => B) => □ A => □ B)
  T-axT : ∀ {A : Ty modal} -> ThmT Γ (□ A => A) 
  

-- Weakening, exchange, and contraction.

T-weak : ∀ {Γ Δ} {A}

    -> Γ ⊆ Δ    -> ThmT Γ A
    ------------------------
         -> ThmT Δ A

T-weak p (T-var x) = T-var (subsetdef x p)
T-weak p T-k = T-k
T-weak p T-s = T-s
T-weak p (T-MP d e) = T-MP (T-weak p d) (T-weak p e)
T-weak p (T-NEC d) = T-NEC d
T-weak p T-axK = T-axK
T-weak p T-prod1 = T-prod1
T-weak p T-prod2 = T-prod2
T-weak p T-prod3 = T-prod3
T-weak p T-axT = T-axT


T-exch : ∀ {Γ} {A B C} (Γ' : Cx modal)

    -> ThmT (Γ , A , B ++ Γ') C
    ---------------------------
    -> ThmT (Γ , B , A ++ Γ') C
    
T-exch Γ' (T-var p) = T-var (cx-exch {Δ = Γ'} p)
T-exch Γ' T-k = T-k
T-exch Γ' T-s = T-s
T-exch Γ' (T-MP p p₁) = T-MP (T-exch Γ' p) (T-exch Γ' p₁)
T-exch Γ' (T-NEC p) = T-NEC p
T-exch Γ' T-prod1 = T-prod1
T-exch Γ' T-prod2 = T-prod2
T-exch Γ' T-prod3 = T-prod3
T-exch Γ' T-axK = T-axK
T-exch Γ' T-axT = T-axT


T-contr : ∀ {Γ} {A C} (Γ' : Cx modal)

    -> ThmT (Γ , A , A ++ Γ') C
    ---------------------------
     -> ThmT (Γ , A ++ Γ') C

T-contr Γ' (T-var p) = T-var (cx-contr {Δ = Γ'} p)
T-contr Γ' T-k = T-k
T-contr Γ' T-s = T-s
T-contr Γ' (T-MP p q) = T-MP (T-contr Γ' p) (T-contr Γ' q)
T-contr Γ' (T-NEC p) = T-NEC p
T-contr Γ' T-prod1 = T-prod1
T-contr Γ' T-prod2 = T-prod2
T-contr Γ' T-prod3 = T-prod3
T-contr Γ' T-axK = T-axK
T-contr Γ' T-axT = T-axT


-- Deduction Theorem.

T-dedthm :  ∀ {Γ : Cx modal} {A B : Ty modal}

   -> ThmT (Γ , A) B
   -------------------
   -> ThmT Γ (A => B)

T-dedthm {Γ} {A} {.A} (T-var top) = T-MP (T-MP T-s T-k) (T-k {Γ} {A} {A})
T-dedthm (T-var (pop x)) = T-MP T-k (T-var x)
T-dedthm T-k = T-MP T-k T-k
T-dedthm T-s = T-MP T-k T-s
T-dedthm (T-MP d d₁) = T-MP (T-MP T-s (T-dedthm d)) (T-dedthm d₁)
T-dedthm (T-NEC d) = T-MP T-k (T-NEC d)
T-dedthm T-prod1 = T-MP T-k T-prod1
T-dedthm T-prod2 = T-MP T-k T-prod2
T-dedthm T-prod3 = T-MP T-k T-prod3
T-dedthm T-axK = T-MP T-k T-axK
T-dedthm T-axT = T-MP T-k T-axT

                       
-- Admissibility of Scott's rule.

T-normal-ded : ∀ {Γ : Cx modal} {A : Ty modal}

          -> ThmT Γ A
    ------------------------
    -> ThmT (boxcx Γ) (□ A)
                 
T-normal-ded (T-var x) = T-var (box∈cx x)
T-normal-ded T-k = T-NEC T-k
T-normal-ded T-s = T-NEC T-s
T-normal-ded (T-MP d e) =
  let x = T-normal-ded d in
  let y = T-normal-ded e in
    T-MP (T-MP T-axK x) y
T-normal-ded (T-NEC d) = T-NEC (T-NEC d)
T-normal-ded T-prod1 = T-NEC T-prod1
T-normal-ded T-prod2 = T-NEC T-prod2
T-normal-ded T-prod3 = T-NEC T-prod3
T-normal-ded T-axK = T-NEC T-axK
T-normal-ded T-axT = T-NEC T-axT


-- Admissibility of the T rule.

T-ruleT : ∀ {Γ : Cx modal} {A : Ty modal}

        -> ThmT Γ A
    -------------------
    -> ThmT (boxcx Γ) A

T-ruleT (T-var x) = T-MP T-axT (T-var (box∈cx x))
T-ruleT T-k = T-k
T-ruleT T-s = T-s
T-ruleT (T-MP p q) = T-MP (T-ruleT p) (T-ruleT q)
T-ruleT (T-NEC p) = T-NEC p
T-ruleT T-prod1 = T-prod1
T-ruleT T-prod2 = T-prod2
T-ruleT T-prod3 = T-prod3
T-ruleT T-axK = T-axK
T-ruleT T-axT = T-axT


-- Admissibility of the cut rule.

T-cut : ∀ {Γ : Cx modal} {A B : Ty modal}

   -> ThmT Γ A    -> ThmT (Γ , A) B
   -----------------------------------
             -> ThmT Γ B
                    
T-cut d (T-var top) = d
T-cut d (T-var (pop x)) = T-var x
T-cut d T-k = T-k
T-cut d T-s = T-s
T-cut d (T-MP p q) = T-MP (T-cut d p) (T-cut d q)
T-cut d (T-NEC p) = T-NEC p
T-cut d T-prod1 = T-prod1
T-cut d T-prod2 = T-prod2
T-cut d T-prod3 = T-prod3
T-cut d T-axK = T-axK
T-cut d T-axT = T-axT

