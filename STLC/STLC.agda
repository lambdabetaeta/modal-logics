module STLC.STLC where

infixl 0 _⊢_

open import Basics
open import Relation.Binary.PropositionalEquality

-- Definition

data _⊢_ (Γ : Cx simple) : Ty simple -> Set where

  STLC-var : ∀ {A}
  
    -> A ∈ Γ
    ---------
    -> Γ ⊢ A
               
  STLC-app : ∀ {A B}
  
    -> Γ ⊢ A => B    -> Γ ⊢ A
    --------------------------
            -> Γ ⊢ B
                          
  STLC-lam : ∀ {A B}
  
    -> (Γ , A) ⊢ B
    ---------------
    -> Γ ⊢ A => B
               
  STLC-prod : ∀ {A B}
  
    ->  Γ ⊢ A    -> Γ ⊢ B
    ---------------------
       -> Γ ⊢ A ∧ B
                     
  STLC-fst : ∀ {A B}
  
    -> Γ ⊢ A ∧ B
    ------------
     -> Γ ⊢ A
                 
  STLC-snd : ∀ {A B}
  
    -> Γ ⊢ A ∧ B
    ------------
     -> Γ ⊢ B


-- Weakening and exchange.


exch : ∀ {Γ A B C} (Γ' : Cx simple)

  -> (Γ , A , B) ++ Γ' ⊢ C
  --------------------------
  -> (Γ , B , A) ++ Γ' ⊢ C

exch Γ' (STLC-var x) = STLC-var (cx-exch {Δ = Γ'} x)
exch Γ' (STLC-app d d₁) = STLC-app (exch Γ' d) (exch Γ' d₁)
exch {C = A => B} Γ' (STLC-lam d) = STLC-lam (exch (Γ' , A) d)
exch Γ' (STLC-prod d d₁) = STLC-prod (exch Γ' d) (exch Γ' d₁)
exch Γ' (STLC-fst d) = STLC-fst (exch Γ' d)
exch Γ' (STLC-snd d) = STLC-snd (exch Γ' d)


weak : ∀ {Γ Γ' A}

  -> Γ ⊢ A    -> Γ ⊆ Γ'
  ---------------------
     ->  Γ' ⊢ A

weak (STLC-var x) f = STLC-var (f x)
weak (STLC-app d e) f =
  STLC-app (weak d f) (weak e f)
weak (STLC-lam d) f = STLC-lam (weak d (weakboth f))
weak (STLC-prod d e) f =
  STLC-prod (weak d f) (weak e f)
weak (STLC-fst d) f = STLC-fst (weak d f)
weak (STLC-snd d) f = STLC-snd (weak d f)


-- Cut.

cut : ∀ {Γ A B} -> (Γ' : Cx simple)

  -> Γ ⊢ A    ->  Γ , A ++ Γ' ⊢ B
  -------------------------------
        ->  Γ ++ Γ' ⊢ B

cut · d (STLC-var top) = d
cut · d (STLC-var (pop x)) = STLC-var x
cut (Γ' , B) d (STLC-var top) = STLC-var top
cut (Γ' , A') d (STLC-var (pop x)) =
  weak (cut Γ' d (STLC-var x)) (weakone subsetid)
cut Γ' d (STLC-app t u) = STLC-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (STLC-lam e) = STLC-lam (cut (Γ' , _) d e)
cut Γ' d (STLC-prod t u) = STLC-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (STLC-fst e) = STLC-fst (cut Γ' d e)
cut Γ' d (STLC-snd e) = STLC-snd (cut Γ' d e)
