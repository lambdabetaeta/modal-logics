module GL.DualGL where

infixl 0 _/_⊢_

open import Basics

-- Definition

data _/_⊢_ (Δ Γ : Cx modal) :  Ty modal -> Set where

  DGL-var : ∀ {A}
  
      -> A ∈ Γ
    -------------
    -> Δ / Γ ⊢ A
               
  DGL-app : ∀ {A B}
  
    -> Δ / Γ ⊢ A => B    -> Δ / Γ ⊢ A
    ---------------------------------
          -> Δ / Γ ⊢ B
                          
  DGL-lam : ∀ {A B}
  
     -> Δ / (Γ , A) ⊢ B
     ------------------
     -> Δ / Γ ⊢ A => B
               
  DGL-prod : ∀ {A B}
  
    -> Δ / Γ ⊢ A    -> Δ / Γ ⊢ B
    ----------------------------
       -> Δ / Γ ⊢ A ∧ B
                     
  DGL-fst : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    -----------------
      -> Δ / Γ ⊢ A
                 
  DGL-snd : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    ----------------
      -> Δ / Γ ⊢ B
                 
  DGL-boxI : ∀ {A}
  
     -> Δ / Δ ⊢ A
    ---------------
    -> Δ / Γ ⊢ □ A
               
  DGL-boxE : ∀ {A C}
  
    -> Δ / Γ ⊢ □ A    -> (Δ , A) / Γ ⊢ C
    ------------------------------------
              -> Δ / Γ ⊢ C

  DGL-boxY : ∀ {A}

    ------------------------------
    -> Δ / Γ ⊢ □ (□ A => A) => □ A
  


-- Weakening and exchange.


exch : ∀ {Δ Γ A B C} (Γ' : Cx modal)

    -> Δ / (Γ , A , B) ++ Γ' ⊢ C
    -----------------------------
    -> Δ / (Γ , B , A) ++ Γ' ⊢ C

exch Γ' (DGL-var x) = DGL-var (cx-exch {Δ = Γ'} x)
exch Γ' (DGL-app d d₁) = DGL-app (exch Γ' d) (exch Γ' d₁)
exch {C = A => B} Γ' (DGL-lam d) = DGL-lam (exch (Γ' , A) d)
exch Γ' (DGL-prod d d₁) = DGL-prod (exch Γ' d) (exch Γ' d₁)
exch Γ' (DGL-fst d) = DGL-fst (exch Γ' d)
exch Γ' (DGL-snd d) = DGL-snd (exch Γ' d)
exch Γ' (DGL-boxI d) = DGL-boxI d
exch Γ' (DGL-boxE d d₁) = DGL-boxE (exch Γ' d) (exch Γ' d₁)
exch Γ' (DGL-boxY) = DGL-boxY


exch-modal : ∀ {Δ Γ A B C} (Δ' : Cx modal)

    -> (Δ , A , B) ++ Δ' / Γ  ⊢ C
    ------------------------------
    -> (Δ , B , A) ++ Δ' / Γ ⊢ C
                    
exch-modal Δ' (DGL-var x) = DGL-var x
exch-modal Δ' (DGL-app d e) =
  DGL-app (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DGL-lam d) = DGL-lam (exch-modal Δ' d)
exch-modal Δ' (DGL-prod d e) =
  DGL-prod (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DGL-fst d) = DGL-fst (exch-modal Δ' d)
exch-modal Δ' (DGL-snd d) = DGL-snd (exch-modal Δ' d)
exch-modal Δ' (DGL-boxI d) =
  DGL-boxI (exch Δ' (exch-modal Δ' d))
exch-modal Δ' (DGL-boxE d e) =
  DGL-boxE (exch-modal Δ' d) (exch-modal (Δ' , _) e)
exch-modal Δ' (DGL-boxY) = DGL-boxY


weak : ∀ {Δ Γ Γ' A}

    -> Δ / Γ ⊢ A    -> Γ ⊆ Γ'
    -------------------------
         -> (Δ / Γ' ⊢ A)

weak (DGL-var x) f = DGL-var (f x)
weak (DGL-app d e) f = DGL-app (weak d f) (weak e f)
weak (DGL-lam d) f = DGL-lam (weak d (weakboth f))
weak (DGL-prod d e) f = DGL-prod (weak d f) (weak e f)
weak (DGL-fst d) f = DGL-fst (weak d f)
weak (DGL-snd d) f = DGL-snd (weak d f)
weak (DGL-boxI d) f = DGL-boxI d
weak (DGL-boxE d e) f =
  DGL-boxE (weak d f) (weak e f)
weak (DGL-boxY) f = DGL-boxY


weak-modal : ∀ {Δ Δ' Γ A}

   -> Δ / Γ ⊢ A    -> Δ ⊆ Δ'
   -------------------------
         -> Δ' / Γ ⊢ A

weak-modal (DGL-var p) f = DGL-var p
weak-modal (DGL-app t u) f = DGL-app (weak-modal t f)
                                           (weak-modal u f)
weak-modal (DGL-lam t) f = DGL-lam (weak-modal t f)
weak-modal (DGL-prod t u) f = DGL-prod (weak-modal t f)
                                               (weak-modal u f)
weak-modal (DGL-fst t) f = DGL-fst (weak-modal t f)
weak-modal (DGL-snd t) f = DGL-snd (weak-modal t f)
weak-modal (DGL-boxI t) f =
  DGL-boxI (weak (weak-modal t f) f)
weak-modal (DGL-boxE t u) f =
  DGL-boxE (weak-modal t f)
          (weak-modal u (weakboth f))
weak-modal (DGL-boxY) f = DGL-boxY


-- Cut.

cut : ∀ {Δ Γ A B} -> (Γ' : Cx modal)

    -> Δ / Γ ⊢ A    -> Δ / Γ , A ++ Γ' ⊢ B
    ---------------------------------------
             -> Δ / Γ ++ Γ' ⊢ B

cut · d (DGL-var top) = d
cut · d (DGL-var (pop x)) = DGL-var x
cut (Γ' , B) d (DGL-var top) = DGL-var top
cut (Γ' , A') d (DGL-var (pop x)) =
  weak (cut Γ' d (DGL-var x)) (weakone subsetid)
cut Γ' d (DGL-app t u) = DGL-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DGL-lam e) = DGL-lam (cut (Γ' , _) d e)
cut Γ' d (DGL-prod t u) = DGL-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DGL-fst e) = DGL-fst (cut Γ' d e)
cut Γ' d (DGL-snd e) = DGL-snd (cut Γ' d e)
cut Γ' d (DGL-boxI e) = DGL-boxI e
cut Γ' d (DGL-boxE t u) =
  DGL-boxE (cut Γ' d t)
           (cut Γ' (weak-modal d (weakone (subsetid ))) u)
cut Γ' d (DGL-boxY) = DGL-boxY


cut-modal : ∀ {Δ Γ A B} -> (Δ' : Cx modal)

    -> Δ / Δ ⊢ A    -> Δ , A ++ Δ' / Γ  ⊢ B
    ---------------------------------------
             -> Δ ++ Δ' / Γ ⊢ B

cut-modal Δ' d (DGL-var x) = DGL-var x
cut-modal Δ' d (DGL-app p q) =
  DGL-app (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DGL-lam e) = DGL-lam (cut-modal Δ' d e)
cut-modal Δ' d (DGL-prod p q) =
  DGL-prod (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DGL-fst e) = DGL-fst (cut-modal Δ' d e)
cut-modal Δ' d (DGL-snd e) = DGL-snd (cut-modal Δ' d e)
cut-modal Δ' d (DGL-boxI e) =
  DGL-boxI (cut Δ' (weak-modal d (concat-subset-1 _ Δ')) (cut-modal Δ' d e))
cut-modal Δ' d (DGL-boxE p q) =
  DGL-boxE (cut-modal Δ' d p) (cut-modal (Δ' , _) d q)
cut-modal Δ' d (DGL-boxY) = DGL-boxY
