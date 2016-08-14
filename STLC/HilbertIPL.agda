module STLC.HilbertIPL where

open import Basics

---------------------------------------
-- Hilbert system for intuitionistic propositional logic
---------------------------------------

-- Definition.

data ThmIPL (Γ : Cx simple) :  Ty simple -> Set where
  IPL-var : ∀ {A : Ty simple} -> (A ∈ Γ) -> ThmIPL Γ A
  IPL-k : ∀ {A B : Ty simple} ->  ThmIPL Γ (A => (B => A))
  IPL-s : ∀ {A B C : Ty simple} -> ThmIPL Γ ((A => B => C) => (A => B) => (A => C))
  IPL-MP : ∀ {A B : Ty simple} -> ThmIPL Γ (A => B) -> ThmIPL Γ A -> ThmIPL Γ B
  IPL-prod1 : ∀ {A B : Ty simple} -> ThmIPL Γ (A => B => A ∧ B)
  IPL-prod2 : ∀ {A B : Ty simple} -> ThmIPL Γ (A ∧ B => A)
  IPL-prod3 : ∀ {A B : Ty simple} -> ThmIPL Γ (A ∧ B => B)

-- Weakening and Exchange

IPL-weak : ∀ {Γ Δ} {A} -> Γ ⊆ Δ -> ThmIPL Γ A -> ThmIPL Δ A

IPL-weak p (IPL-var x) = IPL-var (subsetdef x p)
IPL-weak p IPL-k = IPL-k
IPL-weak p IPL-s = IPL-s
IPL-weak p (IPL-MP d d₁) = IPL-MP (IPL-weak p d) (IPL-weak p d₁)
IPL-weak p IPL-prod1 = IPL-prod1
IPL-weak p IPL-prod2 = IPL-prod2
IPL-weak p IPL-prod3 = IPL-prod3

-- Deduction Theorem

IPL-dedthm :  ∀ {Γ : Cx simple} {A B : Ty simple} -> ThmIPL (Γ , A) B -> ThmIPL Γ (A => B)

IPL-dedthm {Γ} {A} {.A} (IPL-var top) = IPL-MP (IPL-MP IPL-s IPL-k) (IPL-k {Γ} {A} {A})
IPL-dedthm (IPL-var (pop x)) = IPL-MP IPL-k (IPL-var x)
IPL-dedthm IPL-k = IPL-MP IPL-k IPL-k
IPL-dedthm IPL-s = IPL-MP IPL-k IPL-s
IPL-dedthm (IPL-MP d d₁) = IPL-MP (IPL-MP IPL-s (IPL-dedthm d)) (IPL-dedthm d₁)
IPL-dedthm IPL-prod1 = IPL-MP IPL-k IPL-prod1
IPL-dedthm IPL-prod2 = IPL-MP IPL-k IPL-prod2
IPL-dedthm IPL-prod3 = IPL-MP IPL-k IPL-prod3

--                                  ???      
-- Admissibility of the cut rule : -----------
--                                  ???

IPL-cut : ∀ {Γ : Cx simple} {A B : Ty simple}

           -> ThmIPL Γ A     -> ThmIPL (Γ , A) B
        -----------------------------------
                    -> ThmIPL Γ B
                    
IPL-cut d (IPL-var top) = d
IPL-cut d (IPL-var (pop x)) = IPL-var x
IPL-cut d IPL-k = IPL-k
IPL-cut d IPL-s = IPL-s
IPL-cut d (IPL-MP e e₁) = IPL-MP (IPL-cut d e) (IPL-cut d e₁)
IPL-cut d IPL-prod1 = IPL-prod1
IPL-cut d IPL-prod2 = IPL-prod2
IPL-cut d IPL-prod3 = IPL-prod3

