module S4.DualS4 where

infixl 0 _/_⊢_

open import Basics

-- Definition

data _/_⊢_ (Δ Γ : Cx modal) :  Ty modal -> Set where

  DS4-var : ∀ {A}
  
     -> A ∈ Γ
    -------------
    -> Δ / Γ ⊢ A

  DS4-modal-var : ∀ {A}
  
     -> A ∈ Δ
    ------------
    -> Δ / Γ ⊢ A
               
  DS4-app : ∀ {A B}
  
    -> Δ / Γ ⊢ A => B    -> Δ / Γ ⊢ A
    ---------------------------------
          -> Δ / Γ ⊢ B
                          
  DS4-lam : ∀ {A B}
  
     -> Δ / (Γ , A) ⊢ B
     ------------------
     -> Δ / Γ ⊢ A => B
               
  DS4-prod : ∀ {A B}
  
    -> Δ / Γ ⊢ A    -> Δ / Γ ⊢ B
    ----------------------------
       -> Δ / Γ ⊢ A ∧ B
                     
  DS4-fst : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    -----------------
      -> Δ / Γ ⊢ A
                 
  DS4-snd : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    ----------------
      -> Δ / Γ ⊢ B
                 
  DS4-boxI : ∀ {A}
  
     -> Δ / · ⊢ A
    ---------------
    -> Δ / Γ ⊢ □ A
               
  DS4-boxE : ∀ {A C}
  
    -> Δ / Γ ⊢ □ A    -> (Δ , A) / Γ ⊢ C
    ------------------------------------
              -> Δ / Γ ⊢ C


-- Weakening and exchange.


exch : ∀ {Δ Γ A B C} (Γ' : Cx modal)

    -> Δ / (Γ , A , B) ++ Γ' ⊢ C
    -----------------------------
    -> Δ / (Γ , B , A) ++ Γ' ⊢ C

exch Γ' (DS4-var x) = DS4-var (cx-exch {Δ = Γ'} x)
exch Γ' (DS4-modal-var x) = DS4-modal-var x
exch Γ' (DS4-app d d₁) = DS4-app (exch Γ' d) (exch Γ' d₁)
exch {C = A => B} Γ' (DS4-lam d) = DS4-lam (exch (Γ' , A) d)
exch Γ' (DS4-prod d d₁) = DS4-prod (exch Γ' d) (exch Γ' d₁)
exch Γ' (DS4-fst d) = DS4-fst (exch Γ' d)
exch Γ' (DS4-snd d) = DS4-snd (exch Γ' d)
exch Γ' (DS4-boxI d) = DS4-boxI d
exch Γ' (DS4-boxE d d₁) = DS4-boxE (exch Γ' d) (exch Γ' d₁)


exch-modal : ∀ {Δ Γ A B C} (Δ' : Cx modal)

    -> (Δ , A , B) ++ Δ' / Γ  ⊢ C
    ------------------------------
    -> (Δ , B , A) ++ Δ' / Γ ⊢ C
                    
exch-modal Δ' (DS4-var x) = DS4-var x
exch-modal Δ' (DS4-modal-var x) =
  DS4-modal-var (subsetdef x (cx-exch {Δ = Δ'}))
exch-modal Δ' (DS4-app d e) =
  DS4-app (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DS4-lam d) = DS4-lam (exch-modal Δ' d)
exch-modal Δ' (DS4-prod d e) =
  DS4-prod (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DS4-fst d) = DS4-fst (exch-modal Δ' d)
exch-modal Δ' (DS4-snd d) = DS4-snd (exch-modal Δ' d)
exch-modal Δ' (DS4-boxI d) = DS4-boxI (exch-modal Δ' d)
exch-modal Δ' (DS4-boxE d e) =
  DS4-boxE (exch-modal Δ' d) (exch-modal (Δ' , _) e)


weak : ∀ {Δ Γ Γ' A}

    -> Δ / Γ ⊢ A    -> Γ ⊆ Γ'
    -------------------------
        -> (Δ / Γ' ⊢ A)

weak (DS4-var x) f = DS4-var (f x)
weak (DS4-modal-var x) f = DS4-modal-var x
weak (DS4-app d e) f = DS4-app (weak d f) (weak e f)
weak (DS4-lam d) f = DS4-lam (weak d (weakboth f))
weak (DS4-prod d e) f = DS4-prod (weak d f) (weak e f)
weak (DS4-fst d) f = DS4-fst (weak d f)
weak (DS4-snd d) f = DS4-snd (weak d f)
weak (DS4-boxI d) f = DS4-boxI d
weak (DS4-boxE d e) f =
  DS4-boxE (weak d f) (weak e f)


weak-modal : ∀ {Δ Δ' Γ A}

   -> Δ / Γ ⊢ A    -> Δ ⊆ Δ'
   -------------------------
         -> Δ' / Γ ⊢ A

weak-modal (DS4-var p) x = DS4-var p
weak-modal (DS4-modal-var p) x = DS4-modal-var (x p)
weak-modal (DS4-app t u) x = DS4-app (weak-modal t x)
                                     (weak-modal u x)
weak-modal (DS4-lam t) x = DS4-lam (weak-modal t x)
weak-modal (DS4-prod t u) x = DS4-prod (weak-modal t x)
                                       (weak-modal u x)
weak-modal (DS4-fst t) x = DS4-fst (weak-modal t x)
weak-modal (DS4-snd t) x = DS4-snd (weak-modal t x)
weak-modal (DS4-boxI t) x = DS4-boxI (weak-modal t x)
weak-modal (DS4-boxE t u) x =
  DS4-boxE (weak-modal t x)
           (weak-modal u (weakboth x))


-- Cut.

cut : ∀ {Δ Γ A B} -> (Γ' : Cx modal)

    -> Δ / Γ ⊢ A    -> Δ / Γ , A ++ Γ' ⊢ B
    ---------------------------------------
              -> Δ / Γ ++ Γ' ⊢ B

cut · d (DS4-var top) = d
cut · d (DS4-var (pop x)) = DS4-var x
cut (Γ' , B) d (DS4-var top) = DS4-var top
cut (Γ' , A') d (DS4-var (pop x)) =
  weak (cut Γ' d (DS4-var x)) (weakone subsetid)
cut Γ' d (DS4-modal-var p) = DS4-modal-var p
cut Γ' d (DS4-app t u) = DS4-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DS4-lam e) = DS4-lam (cut (Γ' , _) d e)
cut Γ' d (DS4-prod t u) = DS4-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DS4-fst e) = DS4-fst (cut Γ' d e)
cut Γ' d (DS4-snd e) = DS4-snd (cut Γ' d e)
cut Γ' d (DS4-boxI e) = DS4-boxI e
cut Γ' d (DS4-boxE t u) =
  DS4-boxE (cut Γ' d t)
           (cut Γ' (weak-modal d (weakone (subsetid ))) u)


cut-modal : ∀ {Δ Γ A B} -> (Δ' : Cx modal)

    -> Δ / · ⊢ A    -> Δ , A ++ Δ' / Γ  ⊢ B
    ---------------------------------------
             -> Δ ++ Δ' / Γ ⊢ B

cut-modal Δ' d (DS4-var x) = DS4-var x
cut-modal · d (DS4-modal-var top) = weak d subsetempty
cut-modal · d (DS4-modal-var (pop x)) = DS4-modal-var x
cut-modal (Δ' , B) d (DS4-modal-var top) = DS4-modal-var top
cut-modal (Δ' , A') d (DS4-modal-var (pop x)) =
  weak-modal (cut-modal Δ' d (DS4-modal-var x)) (weakone subsetid)
cut-modal Δ' d (DS4-app p q) =
  DS4-app (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DS4-lam e) = DS4-lam (cut-modal Δ' d e)
cut-modal Δ' d (DS4-prod p q) =
  DS4-prod (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DS4-fst e) = DS4-fst (cut-modal Δ' d e)
cut-modal Δ' d (DS4-snd e) = DS4-snd (cut-modal Δ' d e)
cut-modal Δ' d (DS4-boxI e) = DS4-boxI (cut-modal Δ' d e)
cut-modal Δ' d (DS4-boxE p q) =
  DS4-boxE (cut-modal Δ' d p) (cut-modal (Δ' , _) d q)
