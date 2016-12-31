module K4.HilbertK4 where

open import Basics

----------------------------------------
-- Hilbert system for constructive K4 --
----------------------------------------

-- Definition.

data ThmK4 (Γ : Cx modal) :  Ty modal -> Set where

  K4-var : ∀ {A : Ty modal} -> (A ∈ Γ) -> ThmK4 Γ A
  K4-k : ∀ {A B : Ty modal} ->  ThmK4 Γ (A => (B => A))
  K4-s : ∀ {A B C : Ty modal} -> ThmK4 Γ ((A => B => C) => (A => B) => (A => C))
  K4-MP : ∀ {A B : Ty modal} -> ThmK4 Γ (A => B) -> ThmK4 Γ A -> ThmK4 Γ B
  K4-NEC : ∀ {A : Ty modal} -> ThmK4 · A -> ThmK4 Γ (□ A)
  K4-prod1 : ∀ {A B : Ty modal} -> ThmK4 Γ (A => B => A ∧ B)
  K4-prod2 : ∀ {A B : Ty modal} -> ThmK4 Γ (A ∧ B => A)
  K4-prod3 : ∀ {A B : Ty modal} -> ThmK4 Γ (A ∧ B => B)
  K4-axK : ∀ {A B : Ty modal} -> ThmK4 Γ (□(A => B) => □ A => □ B)
  K4-ax4 : ∀ {A : Ty modal} -> ThmK4 Γ (□ A => □ □ A) 
  

-- Weakening, exchange, and contraction.

K4-weak : ∀ {Γ Δ} {A}

  -> Γ ⊆ Δ    -> ThmK4 Γ A
  ------------------------
       -> ThmK4 Δ A

K4-weak p (K4-var x) = K4-var (subsetdef x p)
K4-weak p K4-k = K4-k
K4-weak p K4-s = K4-s
K4-weak p (K4-MP d e) = K4-MP (K4-weak p d) (K4-weak p e)
K4-weak p (K4-NEC d) = K4-NEC d
K4-weak p K4-axK = K4-axK
K4-weak p K4-prod1 = K4-prod1
K4-weak p K4-prod2 = K4-prod2
K4-weak p K4-prod3 = K4-prod3
K4-weak p K4-ax4 = K4-ax4


K4-exch : ∀ {Γ} {A B C} (Γ' : Cx modal)

  -> ThmK4 (Γ , A , B ++ Γ') C
  ----------------------------
  -> ThmK4 (Γ , B , A ++ Γ') C
    
K4-exch Γ' (K4-var p) = K4-var (cx-exch {Δ = Γ'} p)
K4-exch Γ' K4-k = K4-k
K4-exch Γ' K4-s = K4-s
K4-exch Γ' (K4-MP p e) = K4-MP (K4-exch Γ' p) (K4-exch Γ' e)
K4-exch Γ' (K4-NEC p) = K4-NEC p
K4-exch Γ' K4-prod1 = K4-prod1
K4-exch Γ' K4-prod2 = K4-prod2
K4-exch Γ' K4-prod3 = K4-prod3
K4-exch Γ' K4-axK = K4-axK
K4-exch Γ' K4-ax4 = K4-ax4


K4-contr : ∀ {Γ} {A C} (Γ' : Cx modal)

  -> ThmK4 (Γ , A , A ++ Γ') C
  ----------------------------
    -> ThmK4 (Γ , A ++ Γ') C

K4-contr Γ' (K4-var p) = K4-var (cx-contr {Δ = Γ'} p)
K4-contr Γ' K4-k = K4-k
K4-contr Γ' K4-s = K4-s
K4-contr Γ' (K4-MP p q) = K4-MP (K4-contr Γ' p) (K4-contr Γ' q)
K4-contr Γ' (K4-NEC p) = K4-NEC p
K4-contr Γ' K4-prod1 = K4-prod1
K4-contr Γ' K4-prod2 = K4-prod2
K4-contr Γ' K4-prod3 = K4-prod3
K4-contr Γ' K4-axK = K4-axK
K4-contr Γ' K4-ax4 = K4-ax4


-- Deduction Theorem.

K4-dedthm :  ∀ {Γ : Cx modal} {A B : Ty modal}

  -> ThmK4 (Γ , A) B
  -------------------
  -> ThmK4 Γ (A => B)

K4-dedthm {Γ} {A} {.A} (K4-var top) =
  K4-MP (K4-MP K4-s K4-k) (K4-k {Γ} {A} {A})
K4-dedthm (K4-var (pop x)) = K4-MP K4-k (K4-var x)
K4-dedthm K4-k = K4-MP K4-k K4-k
K4-dedthm K4-s = K4-MP K4-k K4-s
K4-dedthm (K4-MP d e) = K4-MP (K4-MP K4-s (K4-dedthm d)) (K4-dedthm e)
K4-dedthm (K4-NEC d) = K4-MP K4-k (K4-NEC d)
K4-dedthm K4-prod1 = K4-MP K4-k K4-prod1
K4-dedthm K4-prod2 = K4-MP K4-k K4-prod2
K4-dedthm K4-prod3 = K4-MP K4-k K4-prod3
K4-dedthm K4-axK = K4-MP K4-k K4-axK
K4-dedthm K4-ax4 = K4-MP K4-k K4-ax4

                       
-- Admissibility of Scott's rule.

K4-Scott : ∀ {Γ : Cx modal} {A : Ty modal}

       -> ThmK4 Γ A
  ------------------------
  -> ThmK4 (boxcx Γ) (□ A)
                 
K4-Scott (K4-var x) = K4-var (box∈cx x)
K4-Scott K4-k = K4-NEC K4-k
K4-Scott K4-s = K4-NEC K4-s
K4-Scott (K4-MP d e) =
  let x = K4-Scott d in
  let y = K4-Scott e in
    K4-MP (K4-MP K4-axK x) y
K4-Scott (K4-NEC d) = K4-NEC (K4-NEC d)
K4-Scott K4-prod1 = K4-NEC K4-prod1
K4-Scott K4-prod2 = K4-NEC K4-prod2
K4-Scott K4-prod3 = K4-NEC K4-prod3
K4-Scott K4-axK = K4-NEC K4-axK
K4-Scott K4-ax4 = K4-NEC K4-ax4


-- Admissibility of the Four Rule.

K4-Four : ∀ {Γ : Cx modal} {A : Ty modal}

  -> ThmK4 (boxcx Γ ++ Γ) A
  --------------------------
  -> ThmK4 (boxcx Γ) (□ A)

K4-Four {·} (K4-var x) = K4-NEC (K4-var x)
K4-Four {Γ , A} (K4-var top) = K4-var top
K4-Four {Γ , A} (K4-var (pop x))
 with subsetdef x (swap-out (boxcx Γ) Γ (□ A))
... | top = K4-MP K4-ax4 (K4-var top)
... | pop q = K4-weak (concat-subset-1 (boxcx Γ) (· , □ A))
                      (K4-Four (K4-var q))
K4-Four K4-k = K4-NEC K4-k
K4-Four K4-s = K4-NEC K4-s
K4-Four (K4-MP p q) =
  K4-MP (K4-MP K4-axK (K4-Four p)) (K4-Four q)
K4-Four (K4-NEC d) = K4-NEC (K4-NEC d)
K4-Four K4-prod1 = K4-NEC K4-prod1
K4-Four K4-prod2 = K4-NEC K4-prod2
K4-Four K4-prod3 = K4-NEC K4-prod3
K4-Four K4-axK = K4-NEC K4-axK
K4-Four K4-ax4 = K4-NEC K4-ax4


-- Variant of the Four rule.

K4-Four-v : ∀ {Γ : Cx modal} {A : Ty modal}

    -> ThmK4 (boxcx Γ) A
  ------------------------
  -> ThmK4 (boxcx Γ) (□ A)

K4-Four-v {Γ} p =
  K4-Four (K4-weak (concat-subset-1 (boxcx Γ) Γ) p)


-- Admissibility of the cut rule.

K4-cut : ∀ {Γ : Cx modal} {A B : Ty modal}

  -> ThmK4 Γ A    -> ThmK4 (Γ , A) B
  -----------------------------------
           -> ThmK4 Γ B
                    
K4-cut d (K4-var top) = d
K4-cut d (K4-var (pop x)) = K4-var x
K4-cut d K4-k = K4-k
K4-cut d K4-s = K4-s
K4-cut d (K4-MP p q) = K4-MP (K4-cut d p) (K4-cut d q)
K4-cut d (K4-NEC p) = K4-NEC p
K4-cut d K4-prod1 = K4-prod1
K4-cut d K4-prod2 = K4-prod2
K4-cut d K4-prod3 = K4-prod3
K4-cut d K4-axK = K4-axK
K4-cut d K4-ax4 = K4-ax4

