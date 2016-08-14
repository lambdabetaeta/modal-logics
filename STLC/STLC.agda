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
 

  STLC-unit : 
  
    ---------
      Γ ⊢ T


-- Weakening and exchange.


STLC-exch : ∀ {Γ A B C} (Γ' : Cx simple)

  -> (Γ , A , B) ++ Γ' ⊢ C
  --------------------------
  -> (Γ , B , A) ++ Γ' ⊢ C

STLC-exch Γ' (STLC-var x) = STLC-var (cx-exch {Δ = Γ'} x)
STLC-exch Γ' (STLC-app d d₁) = STLC-app (STLC-exch Γ' d) (STLC-exch Γ' d₁)
STLC-exch {C = A => B} Γ' (STLC-lam d) = STLC-lam (STLC-exch (Γ' , A) d)
STLC-exch Γ' (STLC-prod d d₁) = STLC-prod (STLC-exch Γ' d) (STLC-exch Γ' d₁)
STLC-exch Γ' (STLC-fst d) = STLC-fst (STLC-exch Γ' d)
STLC-exch Γ' (STLC-snd d) = STLC-snd (STLC-exch Γ' d)
STLC-exch Γ' (STLC-unit) = STLC-unit


STLC-weak : ∀ {Γ A B}

     -> Γ ⊢ A
  --------------
  ->  Γ , B ⊢ A
             
STLC-weak (STLC-var x) = STLC-var (pop x)
STLC-weak (STLC-app d e) = STLC-app (STLC-weak d) (STLC-weak e)
STLC-weak (STLC-lam d) = STLC-lam (STLC-exch · (STLC-weak d) )
STLC-weak (STLC-prod d e) = STLC-prod (STLC-weak d) (STLC-weak e)
STLC-weak (STLC-fst d) = STLC-fst (STLC-weak d)
STLC-weak (STLC-snd d) = STLC-snd (STLC-weak d)
STLC-weak (STLC-unit) = STLC-unit


STLC-weak-many : ∀ {Γ Γ' A}

  -> Γ ⊢ A    -> Γ ⊆ Γ'
  ---------------------
     ->  Γ' ⊢ A

STLC-weak-many (STLC-var x) f = STLC-var (f x)
STLC-weak-many (STLC-app d e) f =
  STLC-app (STLC-weak-many d f) (STLC-weak-many e f)
STLC-weak-many (STLC-lam d) f = STLC-lam (STLC-weak-many d (weakboth f))
STLC-weak-many (STLC-prod d e) f =
  STLC-prod (STLC-weak-many d f) (STLC-weak-many e f)
STLC-weak-many (STLC-fst d) f = STLC-fst (STLC-weak-many d f)
STLC-weak-many (STLC-snd d) f = STLC-snd (STLC-weak-many d f)
STLC-weak-many (STLC-unit) f = STLC-unit


-- Cut.

STLC-cut : ∀ {Γ A B} -> (Γ' : Cx simple)

  -> Γ ⊢ A    ->  Γ , A ++ Γ' ⊢ B
  -------------------------------
        ->  Γ ++ Γ' ⊢ B

STLC-cut · d (STLC-var top) = d
STLC-cut · d (STLC-var (pop x)) = STLC-var x
STLC-cut (Γ' , B) d (STLC-var top) = STLC-var top
STLC-cut (Γ' , A') d (STLC-var (pop x)) =
  STLC-weak (STLC-cut Γ' d (STLC-var x)) 
STLC-cut Γ' d (STLC-app t u) = STLC-app (STLC-cut Γ' d t) (STLC-cut Γ' d u)
STLC-cut Γ' d (STLC-lam e) = STLC-lam (STLC-cut (Γ' , _) d e)
STLC-cut Γ' d (STLC-prod t u) = STLC-prod (STLC-cut Γ' d t) (STLC-cut Γ' d u)
STLC-cut Γ' d (STLC-fst e) = STLC-fst (STLC-cut Γ' d e)
STLC-cut Γ' d (STLC-snd e) = STLC-snd (STLC-cut Γ' d e)
STLC-cut Γ' d (STLC-unit) = STLC-unit


-- Useful lemmas for translation

STLC-unitize : ∀ {Γ A} -> (Δ : Cx simple) -> (trans-cx Γ ++ Δ ⊢ A) -> (trans-cx (boxcx Γ) ++ Δ ⊢ A)

STLC-unitize {·} · (STLC-var ())
STLC-unitize {Γ , _} · (STLC-var top) = STLC-app (STLC-var top) STLC-unit
STLC-unitize {Γ , _} · (STLC-var (pop p)) = STLC-weak (STLC-unitize · (STLC-var p))
STLC-unitize (Δ , A) (STLC-var top) = STLC-var top
STLC-unitize (Δ , B) (STLC-var (pop p)) = STLC-weak (STLC-unitize Δ (STLC-var p))
STLC-unitize Δ (STLC-app t u) = STLC-app (STLC-unitize Δ t) (STLC-unitize Δ u)
STLC-unitize {Γ} {A => B} Δ (STLC-lam t) = STLC-lam (STLC-unitize (Δ , A) t)
STLC-unitize Δ (STLC-prod t u) = STLC-prod (STLC-unitize Δ t) (STLC-unitize Δ u)
STLC-unitize Δ (STLC-fst t) = STLC-fst (STLC-unitize Δ t)
STLC-unitize Δ (STLC-snd t) = STLC-snd (STLC-unitize Δ t)
STLC-unitize Δ STLC-unit = STLC-unit
