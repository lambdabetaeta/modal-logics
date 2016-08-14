module K4.DualK4 where

infixl 0 _/_⊢_

open import Basics

-- Definition

data _/_⊢_ (Δ Γ : Cx modal) :  Ty modal -> Set where

  DK4-var : ∀ {A}
  
      -> A ∈ Γ
    -------------
    -> Δ / Γ ⊢ A
               
  DK4-app : ∀ {A B}
  
    -> Δ / Γ ⊢ A => B    -> Δ / Γ ⊢ A
    ---------------------------------
          -> Δ / Γ ⊢ B
                          
  DK4-lam : ∀ {A B}
  
     -> Δ / (Γ , A) ⊢ B
     ------------------
     -> Δ / Γ ⊢ A => B
               
  DK4-prod : ∀ {A B}
  
    -> Δ / Γ ⊢ A    -> Δ / Γ ⊢ B
    ----------------------------
       -> Δ / Γ ⊢ A ∧ B
                     
  DK4-fst : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    -----------------
      -> Δ / Γ ⊢ A
                 
  DK4-snd : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    ----------------
      -> Δ / Γ ⊢ B
                 
  DK4-boxI : ∀ {A}
  
     -> Δ / Δ ⊢ A
    ---------------
    -> Δ / Γ ⊢ □ A
               
  DK4-boxE : ∀ {A C}
  
    -> Δ / Γ ⊢ □ A    -> (Δ , A) / Γ ⊢ C
    ------------------------------------
              -> Δ / Γ ⊢ C


-- Weakening and exchange.


exch : ∀ {Δ Γ A B C} (Γ' : Cx modal)

    -> Δ / (Γ , A , B) ++ Γ' ⊢ C
    -----------------------------
    -> Δ / (Γ , B , A) ++ Γ' ⊢ C

exch Γ' (DK4-var x) = DK4-var (cx-exch {Δ = Γ'} x)
exch Γ' (DK4-app d d₁) = DK4-app (exch Γ' d) (exch Γ' d₁)
exch {C = A => B} Γ' (DK4-lam d) = DK4-lam (exch (Γ' , A) d)
exch Γ' (DK4-prod d d₁) = DK4-prod (exch Γ' d) (exch Γ' d₁)
exch Γ' (DK4-fst d) = DK4-fst (exch Γ' d)
exch Γ' (DK4-snd d) = DK4-snd (exch Γ' d)
exch Γ' (DK4-boxI d) = DK4-boxI d
exch Γ' (DK4-boxE d d₁) = DK4-boxE (exch Γ' d) (exch Γ' d₁)


exch-modal : ∀ {Δ Γ A B C} (Δ' : Cx modal)

    -> (Δ , A , B) ++ Δ' / Γ  ⊢ C
    ------------------------------
    -> (Δ , B , A) ++ Δ' / Γ ⊢ C
                    
exch-modal Δ' (DK4-var x) = DK4-var x
exch-modal Δ' (DK4-app d e) =
  DK4-app (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DK4-lam d) = DK4-lam (exch-modal Δ' d)
exch-modal Δ' (DK4-prod d e) =
  DK4-prod (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DK4-fst d) = DK4-fst (exch-modal Δ' d)
exch-modal Δ' (DK4-snd d) = DK4-snd (exch-modal Δ' d)
exch-modal Δ' (DK4-boxI d) =
  DK4-boxI (exch Δ' (exch-modal Δ' d))
exch-modal Δ' (DK4-boxE d e) =
  DK4-boxE (exch-modal Δ' d) (exch-modal (Δ' , _) e)


weak : ∀ {Δ Γ Γ' A}

    -> Δ / Γ ⊢ A    -> Γ ⊆ Γ'
    -------------------------
         -> (Δ / Γ' ⊢ A)

weak (DK4-var x) f = DK4-var (f x)
weak (DK4-app d e) f = DK4-app (weak d f) (weak e f)
weak (DK4-lam d) f = DK4-lam (weak d (weakboth f))
weak (DK4-prod d e) f = DK4-prod (weak d f) (weak e f)
weak (DK4-fst d) f = DK4-fst (weak d f)
weak (DK4-snd d) f = DK4-snd (weak d f)
weak (DK4-boxI d) f = DK4-boxI d
weak (DK4-boxE d e) f =
  DK4-boxE (weak d f) (weak e f)


weak-modal : ∀ {Δ Δ' Γ A}

   -> Δ / Γ ⊢ A    -> Δ ⊆ Δ'
   -------------------------
         -> Δ' / Γ ⊢ A

weak-modal (DK4-var p) f = DK4-var p
weak-modal (DK4-app t u) f = DK4-app (weak-modal t f)
                                           (weak-modal u f)
weak-modal (DK4-lam t) f = DK4-lam (weak-modal t f)
weak-modal (DK4-prod t u) f = DK4-prod (weak-modal t f)
                                               (weak-modal u f)
weak-modal (DK4-fst t) f = DK4-fst (weak-modal t f)
weak-modal (DK4-snd t) f = DK4-snd (weak-modal t f)
weak-modal (DK4-boxI t) f =
  DK4-boxI (weak (weak-modal t f) f)
weak-modal (DK4-boxE t u) f =
  DK4-boxE (weak-modal t f)
          (weak-modal u (weakboth f))


-- Cut.

cut : ∀ {Δ Γ A B} -> (Γ' : Cx modal)

    -> Δ / Γ ⊢ A    -> Δ / Γ , A ++ Γ' ⊢ B
    ---------------------------------------
             -> Δ / Γ ++ Γ' ⊢ B

cut · d (DK4-var top) = d
cut · d (DK4-var (pop x)) = DK4-var x
cut (Γ' , B) d (DK4-var top) = DK4-var top
cut (Γ' , A') d (DK4-var (pop x)) =
  weak (cut Γ' d (DK4-var x)) (weakone subsetid)
cut Γ' d (DK4-app t u) = DK4-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DK4-lam e) = DK4-lam (cut (Γ' , _) d e)
cut Γ' d (DK4-prod t u) = DK4-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DK4-fst e) = DK4-fst (cut Γ' d e)
cut Γ' d (DK4-snd e) = DK4-snd (cut Γ' d e)
cut Γ' d (DK4-boxI e) = DK4-boxI e
cut Γ' d (DK4-boxE t u) =
  DK4-boxE (cut Γ' d t)
           (cut Γ' (weak-modal d (weakone (subsetid ))) u)


cut-modal : ∀ {Δ Γ A B} -> (Δ' : Cx modal)

    -> Δ / Δ ⊢ A    -> Δ , A ++ Δ' / Γ  ⊢ B
    ---------------------------------------
             -> Δ ++ Δ' / Γ ⊢ B

cut-modal Δ' d (DK4-var x) = DK4-var x
cut-modal Δ' d (DK4-app p q) =
  DK4-app (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DK4-lam e) = DK4-lam (cut-modal Δ' d e)
cut-modal Δ' d (DK4-prod p q) =
  DK4-prod (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DK4-fst e) = DK4-fst (cut-modal Δ' d e)
cut-modal Δ' d (DK4-snd e) = DK4-snd (cut-modal Δ' d e)
cut-modal Δ' d (DK4-boxI e) =
  DK4-boxI (cut Δ' (weak-modal d (concat-subset-1 _ Δ')) (cut-modal Δ' d e))
cut-modal Δ' d (DK4-boxE p q) =
  DK4-boxE (cut-modal Δ' d p) (cut-modal (Δ' , _) d q)
