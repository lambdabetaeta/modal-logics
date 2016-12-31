module K.DualK where

infixl 0 _/_⊢_

open import Basics

--------------------------------------
-- Dual contexts for constructive K --
--------------------------------------

data _/_⊢_ (Δ Γ : Cx modal) :  Ty modal -> Set where

  DK-var : ∀ {A}
  
     -> A ∈ Γ
    -------------
    -> Δ / Γ ⊢ A
               
  DK-app : ∀ {A B}
  
    -> Δ / Γ ⊢ A => B    -> Δ / Γ ⊢ A
    ---------------------------------
             -> Δ / Γ ⊢ B
                          
  DK-lam : ∀ {A B}
  
     -> Δ / (Γ , A) ⊢ B
     ------------------
     -> Δ / Γ ⊢ A => B
               
  DK-prod : ∀ {A B}
  
    -> Δ / Γ ⊢ A    -> Δ / Γ ⊢ B
    ----------------------------
       -> Δ / Γ ⊢ A ∧ B
                     
  DK-fst : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    -----------------
      -> Δ / Γ ⊢ A
                 
  DK-snd : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    ----------------
      -> Δ / Γ ⊢ B
                 
  DK-boxI : ∀ {A}
  
     -> · / Δ ⊢ A
    ---------------
    -> Δ / Γ ⊢ □ A
               
  DK-boxE : ∀ {A C}
  
    -> Δ / Γ ⊢ □ A    -> (Δ , A) / Γ ⊢ C
    ------------------------------------
              -> Δ / Γ ⊢ C


-- Weakening and exchange.


exch : ∀ {Δ Γ A B C} (Γ' : Cx modal)

    -> Δ / Γ , A , B ++ Γ' ⊢ C
    --------------------------
    -> Δ / Γ , B , A ++ Γ' ⊢ C

exch Γ' (DK-var x) = DK-var (cx-exch {Δ = Γ'} x)
exch Γ' (DK-app p q) = DK-app (exch Γ' p) (exch Γ' q)
exch Γ' (DK-lam d) = DK-lam (exch (Γ' , _) d)
exch Γ' (DK-prod p q) = DK-prod (exch Γ' p) (exch Γ' q)
exch Γ' (DK-fst p) = DK-fst (exch Γ' p)
exch Γ' (DK-snd p) = DK-snd (exch Γ' p)
exch Γ' (DK-boxI p) = DK-boxI p
exch Γ' (DK-boxE p q) = DK-boxE (exch Γ' p) (exch Γ' q)


exch-modal : ∀ {Δ Γ A B C} (Δ' : Cx modal)

    -> Δ , A , B ++ Δ' / Γ ⊢ C
    ---------------------------
    -> Δ , B , A ++ Δ' / Γ ⊢ C
                    
exch-modal Δ' (DK-var x) = DK-var x
exch-modal Δ' (DK-app d e) =
  DK-app (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DK-lam d) = DK-lam (exch-modal Δ' d)
exch-modal Δ' (DK-prod d e) =
  DK-prod (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DK-fst d) = DK-fst (exch-modal Δ' d)
exch-modal Δ' (DK-snd d) = DK-snd (exch-modal Δ' d)
exch-modal Δ' (DK-boxI d) = DK-boxI (exch Δ' d)
exch-modal Δ' (DK-boxE d e) =
  DK-boxE (exch-modal Δ' d) (exch-modal (Δ' , _) e)


weak : ∀ {Δ Γ Γ' A}

    -> Δ / Γ ⊢ A    -> Γ ⊆ Γ'
    -------------------------
         -> (Δ / Γ' ⊢ A)

weak (DK-var x) f = DK-var (f x)
weak (DK-app d e) f = DK-app (weak d f) (weak e f)
weak (DK-lam d) f = DK-lam (weak d (weakboth f))
weak (DK-prod d e) f = DK-prod (weak d f) (weak e f)
weak (DK-fst d) f = DK-fst (weak d f)
weak (DK-snd d) f = DK-snd (weak d f)
weak (DK-boxI d) f = DK-boxI d
weak (DK-boxE d e) f =
  DK-boxE (weak d f) (weak e f)


weak-modal : ∀ {Δ Δ' Γ A}

   -> Δ / Γ ⊢ A    -> Δ ⊆ Δ'
   -------------------------
         -> Δ' / Γ ⊢ A

weak-modal (DK-var p) f = DK-var p
weak-modal (DK-app t u) f = DK-app (weak-modal t f)
                                           (weak-modal u f)
weak-modal (DK-lam t) f = DK-lam (weak-modal t f)
weak-modal (DK-prod t u) f = DK-prod (weak-modal t f)
                                               (weak-modal u f)
weak-modal (DK-fst t) f = DK-fst (weak-modal t f)
weak-modal (DK-snd t) f = DK-snd (weak-modal t f)
weak-modal (DK-boxI t) f = DK-boxI (weak t f)
weak-modal (DK-boxE t u) f =
  DK-boxE (weak-modal t f)
          (weak-modal u (weakboth f))


contr : ∀ {Δ Γ A C} (Γ' : Cx modal)

    -> Δ / Γ , A , A ++ Γ'  ⊢ C
    ---------------------------
      -> Δ / Γ , A ++ Γ' ⊢ C

contr · (DK-var top) = DK-var top
contr · (DK-var (pop x)) = DK-var x
contr (Γ' , C) (DK-var top) = DK-var top
contr (Γ' , B) (DK-var (pop x)) = weak (contr Γ' (DK-var x)) (weakone subsetid)
contr Γ' (DK-app p q) = DK-app (contr Γ' p) (contr Γ' q)
contr Γ' (DK-lam p) = DK-lam (contr (Γ' , _) p)
contr Γ' (DK-prod p q) = DK-prod (contr Γ' p) (contr Γ' q)
contr Γ' (DK-fst p) = DK-fst (contr Γ' p)
contr Γ' (DK-snd p) = DK-snd (contr Γ' p)
contr Γ' (DK-boxI p) = DK-boxI p
contr Γ' (DK-boxE p q) = DK-boxE (contr Γ' p) (contr Γ' q)


contr-modal : ∀ {Δ Γ A C} (Δ' : Cx modal)

    -> Δ , A , A ++ Δ' / Γ  ⊢ C
    ---------------------------
      -> Δ , A ++ Δ' / Γ ⊢ C

contr-modal Δ' (DK-var x) = DK-var x
contr-modal Δ' (DK-app p q) = DK-app (contr-modal Δ' p) (contr-modal Δ' q)
contr-modal Δ' (DK-lam p) = DK-lam (contr-modal Δ' p)
contr-modal Δ' (DK-prod p q) = DK-prod (contr-modal Δ' p) (contr-modal Δ' q)
contr-modal Δ' (DK-fst p) = DK-fst (contr-modal Δ' p)
contr-modal Δ' (DK-snd p) = DK-snd (contr-modal Δ' p)
contr-modal Δ' (DK-boxI p) = DK-boxI (contr Δ' p)
contr-modal Δ' (DK-boxE p q) = DK-boxE (contr-modal Δ' p) (contr-modal (Δ' , _) q)


-- Cut.

cut : ∀ {Δ Γ A B} -> (Γ' : Cx modal)

    -> Δ / Γ ⊢ A    -> Δ / Γ , A ++ Γ' ⊢ B
    ---------------------------------------
             -> Δ / Γ ++ Γ' ⊢ B

cut · d (DK-var top) = d
cut · d (DK-var (pop x)) = DK-var x
cut (Γ' , B) d (DK-var top) = DK-var top
cut (Γ' , A') d (DK-var (pop x)) =
  weak (cut Γ' d (DK-var x)) (weakone subsetid)
cut Γ' d (DK-app t u) = DK-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DK-lam e) = DK-lam (cut (Γ' , _) d e)
cut Γ' d (DK-prod t u) = DK-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DK-fst e) = DK-fst (cut Γ' d e)
cut Γ' d (DK-snd e) = DK-snd (cut Γ' d e)
cut Γ' d (DK-boxI e) = DK-boxI e
cut Γ' d (DK-boxE t u) =
  DK-boxE (cut Γ' d t)
          (cut Γ' (weak-modal d (weakone subsetid)) u)


cut-modal : ∀ {Δ Γ A B} -> (Δ' : Cx modal)

    -> · / Δ ⊢ A    -> Δ , A ++ Δ' / Γ  ⊢ B
    ---------------------------------------
             -> Δ ++ Δ' / Γ ⊢ B

cut-modal Δ' d (DK-var x) = DK-var x
cut-modal Δ' d (DK-app p q) =
  DK-app (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DK-lam e) = DK-lam (cut-modal Δ' d e)
cut-modal Δ' d (DK-prod p q) =
  DK-prod (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DK-fst e) = DK-fst (cut-modal Δ' d e)
cut-modal Δ' d (DK-snd e) = DK-snd (cut-modal Δ' d e)
cut-modal Δ' d (DK-boxI e) = DK-boxI (cut Δ' d e)
cut-modal Δ' d (DK-boxE p q) =
  DK-boxE (cut-modal Δ' d p) (cut-modal (Δ' , _) d q)
