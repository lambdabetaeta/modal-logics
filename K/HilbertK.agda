module K.HilbertK where

open import Basics

---------------------------------------
-- Hilbert system for constructive K --
---------------------------------------

-- Definition.

data ThmK (Γ : Cx modal) :  Ty modal -> Set where

  K-var : ∀ {A : Ty modal} -> (A ∈ Γ) -> ThmK Γ A
  K-k : ∀ {A B : Ty modal} ->  ThmK Γ (A => (B => A))
  K-s : ∀ {A B C : Ty modal} -> ThmK Γ ((A => B => C) => (A => B) => (A => C))
  K-MP : ∀ {A B : Ty modal} -> ThmK Γ (A => B) -> ThmK Γ A -> ThmK Γ B
  K-NEC : ∀ {A : Ty modal} -> ThmK · A -> ThmK Γ (□ A)
  K-prod1 : ∀ {A B : Ty modal} -> ThmK Γ (A => B => A ∧ B)
  K-prod2 : ∀ {A B : Ty modal} -> ThmK Γ (A ∧ B => A)
  K-prod3 : ∀ {A B : Ty modal} -> ThmK Γ (A ∧ B => B)
  K-axK : ∀ {A B : Ty modal} -> ThmK Γ (□ (A => B) => □ A => □ B)


-- Weakening, exchange, and contraction.

K-weak : ∀ {Γ Δ} {A}

    -> Γ ⊆ Δ    -> ThmK Γ A
    ------------------------
         -> ThmK Δ A

K-weak p (K-var x) = K-var (subsetdef x p)
K-weak p K-k = K-k
K-weak p K-s = K-s
K-weak p (K-MP d e) = K-MP (K-weak p d) (K-weak p e)
K-weak p (K-NEC d) = K-NEC d
K-weak p K-axK = K-axK
K-weak p K-prod1 = K-prod1
K-weak p K-prod2 = K-prod2
K-weak p K-prod3 = K-prod3


K-exch : ∀ {Γ} {A B C} (Γ' : Cx modal)

    -> ThmK (Γ , A , B ++ Γ') C
    ---------------------------
    -> ThmK (Γ , B , A ++ Γ') C
    
K-exch Γ' (K-var p) = K-var (cx-exch {Δ = Γ'} p)
K-exch Γ' K-k = K-k
K-exch Γ' K-s = K-s
K-exch Γ' (K-MP p p₁) = K-MP (K-exch Γ' p) (K-exch Γ' p₁)
K-exch Γ' (K-NEC p) = K-NEC p
K-exch Γ' K-prod1 = K-prod1
K-exch Γ' K-prod2 = K-prod2
K-exch Γ' K-prod3 = K-prod3
K-exch Γ' K-axK = K-axK


K-contr : ∀ {Γ} {A C} (Γ' : Cx modal)

    -> ThmK (Γ , A , A ++ Γ') C
    ---------------------------
     -> ThmK (Γ , A ++ Γ') C

K-contr Γ' (K-var p) = K-var (cx-contr {Δ = Γ'} p)
K-contr Γ' K-k = K-k
K-contr Γ' K-s = K-s
K-contr Γ' (K-MP p q) = K-MP (K-contr Γ' p) (K-contr Γ' q)
K-contr Γ' (K-NEC p) = K-NEC p
K-contr Γ' K-prod1 = K-prod1
K-contr Γ' K-prod2 = K-prod2
K-contr Γ' K-prod3 = K-prod3
K-contr Γ' K-axK = K-axK


-- Deduction Theorem.

K-dedthm :  ∀ {Γ : Cx modal} {A B : Ty modal}

    -> ThmK (Γ , A) B
    -----------------
    -> ThmK Γ (A => B)

K-dedthm {Γ} {A} {.A} (K-var top) = K-MP (K-MP K-s K-k) (K-k {Γ} {A} {A})
K-dedthm (K-var (pop x)) = K-MP K-k (K-var x)
K-dedthm K-k = K-MP K-k K-k
K-dedthm K-s = K-MP K-k K-s
K-dedthm (K-MP d e) = K-MP (K-MP K-s (K-dedthm d)) (K-dedthm e)
K-dedthm (K-NEC d) = K-MP K-k (K-NEC d)
K-dedthm K-prod1 = K-MP K-k K-prod1
K-dedthm K-prod2 = K-MP K-k K-prod2
K-dedthm K-prod3 = K-MP K-k K-prod3
K-dedthm K-axK = K-MP K-k K-axK

                       
-- Admissibility of Scott's rule.

K-Scott : ∀ {Γ : Cx modal} {A : Ty modal}

          -> ThmK Γ A
    -----------------------
    -> ThmK (boxcx Γ) (□ A)
                 
K-Scott (K-var x) = K-var (box∈cx x)
K-Scott K-k = K-NEC K-k
K-Scott K-s = K-NEC K-s
K-Scott (K-MP d e) =
  let x = K-Scott d in
  let y = K-Scott e in
    K-MP (K-MP K-axK x) y
K-Scott (K-NEC d) = K-NEC (K-NEC d)
K-Scott K-prod1 = K-NEC K-prod1
K-Scott K-prod2 = K-NEC K-prod2
K-Scott K-prod3 = K-NEC K-prod3
K-Scott K-axK = K-NEC K-axK


-- Admissibility of the cut rule.

K-cut : ∀ {Γ : Cx modal} {A B : Ty modal}

    -> ThmK Γ A     -> ThmK (Γ , A) B
    -----------------------------------
             -> ThmK Γ B
                    
K-cut d (K-var top) = d
K-cut d (K-var (pop x)) = K-var x
K-cut d K-k = K-k
K-cut d K-s = K-s
K-cut d (K-MP p q) = K-MP (K-cut d p) (K-cut d q)
K-cut d (K-NEC e) = K-NEC e
K-cut d K-prod1 = K-prod1
K-cut d K-prod2 = K-prod2
K-cut d K-prod3 = K-prod3
K-cut d K-axK = K-axK
