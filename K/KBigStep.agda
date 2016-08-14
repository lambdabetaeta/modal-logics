module K.KBigStep where

open import Agda.Builtin.Unit public using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to pair)
open import Basics
open import K.DualK
import STLC.STLC as STLC

-- Big Step Normalisation

get-right-val : ∀ {Δ Γ Η Θ A} -> (A ∈ Θ) -> (Δ / Γ ⊢ Η / Θ) -> Val Δ Γ A
get-right-val () empty
get-right-val top (right p x) = x
get-right-val (pop q) (right p x) = get-right-val q p
get-right-val q (left p x) = get-right-val q p

-- E ⊢ M ⇓ v is to be read as "in environment E, M evaluates to whnf (val) v."

mutual

  data _⊢_⇓_ : ∀ {Η Θ Δ Γ A} -> (Δ / Γ ⊢ Η / Θ) -> (Η / Θ ⊢ A) -> (Val Δ Γ A) -> Set where


    whnf-var : ∀ {Δ Γ Η Θ A} {E : Δ / Γ ⊢ Η / Θ}
                                   -> (p : A ∈ Θ)
                   ------------------------------------------
                      ->  E ⊢ (DK-var p) ⇓ (get-right-val p E)


    whnf-lam : ∀ {Δ Γ Η Θ A B} {m : Η / Θ , A ⊢ B}  {E : Δ / Γ ⊢ Η / Θ}

                   -----------------------------------------------------
                      ->  E ⊢ (DK-lam  m) ⇓ (DK-val-lam E m)

    whnf-app : ∀ {Η Θ Δ Γ E A B} {m : Η / Θ ⊢ A => B} {n : Η / Θ ⊢ A}
                                 {f : Val Δ Γ (A => B)} {x : Val Δ Γ A} {v}

                     -> E ⊢ m ⇓ f    -> E ⊢ n ⇓ x     -> f $ x >> v
                   ------------------------------------------------------
                                -> E ⊢ (DK-app m n) ⇓ v

    whnf-boxI : ∀ {Δ Γ Η Θ A} {m : · / Η ⊢ A} {E : Δ / Γ ⊢ Η / Θ}

                   ---------------------------------------------
                     -> E ⊢ (DK-boxI m) ⇓ (DK-val-boxI E m)

    whnf-boxE : ∀ {Η Θ Δ Γ E A C} {m : Η / Θ ⊢ □ A}   {n : Η , A / Θ ⊢ C}
                                  {g : Val Δ Γ (□ A)} {v : Val (Δ , A) Γ C}
                                  {w : Val Δ Γ C}

                                  -> E ⊢ m ⇓ g
                     -> (ctxt-insert-left _ _ _ _ E) ⊢ n ⇓ v
                                  -> g % v >> w
                   --------------------------------------------
                           -> E ⊢ (DK-boxE m n) ⇓ w


    whnf-prod1 : ∀ {Δ Γ Η Θ A B}  {E : Δ / Γ ⊢ Η / Θ}
                   {m : Η / Θ ⊢ A} {n : Η / Θ ⊢ B}

                   -----------------------------------------------
                    -> E ⊢ (DK-prod1 m n) ⇓ (DK-val-prod1 E m n)

    whnf-prod2 : ∀ {Δ Γ Η Θ A B} {m : Η / Θ ⊢ A ∧ B} {E : Δ / Γ ⊢ Η / Θ} {v w}

                     ->  E ⊢ m ⇓ v      -> fst v >> w
                   -----------------------------------
                     -> E ⊢ (DK-prod2 m) ⇓ w


    whnf-prod3 : ∀ {Δ Γ Η Θ A B} {m : Η / Θ ⊢ A ∧ B} {E : Δ / Γ ⊢ Η / Θ} {v w}

                      -> E ⊢ m ⇓ v      -> snd v >> w     
                   ------------------------------------
                        -> E ⊢ (DK-prod3 m) ⇓ w


  -- Dealing with arrow elimination.
  
  data _$_>>_ {Δ Γ A B} :  Val Δ Γ (A => B) -> Val Δ Γ A -> Val Δ Γ B -> Set where

    eval-app-ne : ∀ {m v} ->  DK-val-ne m $ v >> (DK-val-ne (DK-ne-app m v))

    eval-app-lam : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {m v w} -> (right E v) ⊢ m ⇓ w -> (DK-val-lam E m) $ v >> w


  _$_ : ∀ {Δ Γ A B v} -> (f : Val Δ Γ (A => B)) -> (x : Val Δ Γ A) -> (f $ x >> v) -> Σ (Val Δ Γ B) (λ w -> w ≡ v)

  (DK-val-ne m $ v) eval-app-ne = pair (DK-val-ne (DK-ne-app m v)) refl
  (DK-val-lam E t $ v) (eval-app-lam p) = pair _ refl

  -- Dealing with first projection.
  
  data fst_>>_ {Δ Γ A B} :  Val Δ Γ (A ∧ B) -> Val Δ Γ A -> Set where

    eval-fst-ne : ∀ {x} -> fst (DK-val-ne x) >> (DK-val-ne (DK-ne-prod2 x))
    eval-fst-prod1 : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {a b v} -> E ⊢ a ⇓ v -> fst (DK-val-prod1 E a b) >> v

  fst-val-str : ∀ {Δ Γ A B v} -> (x : Val Δ Γ (A ∧ B)) -> (p : fst x >> v) -> Σ (Val Δ Γ A) (λ w -> w ≡ v)

  fst-val-str (DK-val-ne x) eval-fst-ne = pair (DK-val-ne (DK-ne-prod2 x)) refl
  fst-val-str (DK-val-prod1 E m n) (eval-fst-prod1 p) = eval-str E m p

  -- Dealing with second projection.

  data snd_>>_ {Δ Γ A B} : Val Δ Γ (A ∧ B) -> Val Δ Γ B -> Set where

    eval-snd-ne : ∀ {x} -> snd (DK-val-ne x) >> (DK-val-ne (DK-ne-prod3 x))
    eval-snd-prod1 : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {a b v} -> E ⊢ b ⇓ v -> snd (DK-val-prod1 E a b) >> v

  snd-val-str : ∀ {Δ Γ A B v} -> (x : Val Δ Γ (A ∧ B)) -> (p : snd x >> v) -> Σ (Val Δ Γ B) (λ w -> w ≡ v)
  snd-val-str (DK-val-ne x) eval-snd-ne = pair (DK-val-ne (DK-ne-prod3 x)) refl
  snd-val-str (DK-val-prod1 E m n) (eval-snd-prod1 p) = eval-str E n p

  -- Dealing with box-elimination.

  data _%_>>_ {Δ Γ A C} : Val Δ Γ (□ A) -> Val (Δ , A) Γ C -> Val Δ Γ C -> Set where
    eval-box-ne : ∀ {m v} ->  DK-val-ne m % v >> (DK-val-ne (DK-ne-boxE m v))

    eval-box-box : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ}
                           {m : · / Η ⊢ A}  {v : Val (Δ , A) Γ C}
                           {v' : Val · Δ A} {w : Val Δ Γ C}
                              -> (ctxt-to-modal-ctxt E) ⊢ m ⇓ v'
                              -> left (id-ctxt _ _) v' ⊢ (insert-val v) ⇓ w
                              -> (DK-val-boxI E m) % v >> w

  insert-val : ∀ {Δ Γ A} -> Val Δ Γ A -> Δ / Γ ⊢ A
  insert-val (DK-val-ne x) = {!!}
  insert-val (DK-val-lam E t) = {!!}
  insert-val (DK-val-prod1 E t u) = {!!}
  insert-val (DK-val-boxI E t) = {!!}

  _%_ : ∀ {Δ Γ A C w} -> (g : Val Δ Γ (□ A)) -> (v : Val (Δ , A) Γ C) -> (g % v >> w) -> Σ (Val Δ Γ C) (λ w' -> w' ≡ w)
  (DK-val-ne n % v) p = pair _ refl
  (DK-val-boxI E m % v) p = pair _ refl

  -- Evaluating to whnf.

  eval-str : ∀ {Δ Γ Η Θ A v} -> (E : Δ / Γ ⊢ Η / Θ)
         -> (t : Η / Θ ⊢ A) ->  E ⊢ t ⇓ v -> Σ (Val Δ Γ A) (λ w -> w ≡ v)

  eval-str E (DK-var p) (whnf-var .p) = pair (get-right-val p E) refl
  eval-str E (DK-app t u) (whnf-app p q r) with (eval-str E t p) | (eval-str E u q)
  eval-str E (DK-app t u) (whnf-app p q r)     | pair f refl | pair x refl = (f $ x) r
  eval-str E (DK-lam m) whnf-lam = pair (DK-val-lam E m) refl
  eval-str E (DK-prod1 m n) whnf-prod1 = pair (DK-val-prod1 E m n) refl
  eval-str E (DK-prod2 t) (whnf-prod2 p x) with (eval-str E t p)
  eval-str E (DK-prod2 t) (whnf-prod2 p x)    | pair v refl = fst-val-str v x
  eval-str E (DK-prod3 t) (whnf-prod3 p x) with (eval-str E t p)
  eval-str E (DK-prod3 t) (whnf-prod3 p x)    | pair v refl = snd-val-str v x
  eval-str E (DK-boxI m) whnf-boxI = pair (DK-val-boxI E m) refl
  eval-str E (DK-boxE t u) (whnf-boxE p q r)
    with (eval-str E t p) | (eval-str (ctxt-insert-left _ _ _ _ E) u q)
  ...  | pair g refl | pair v refl = (g % v) r

  -- v ↓ w is to be read "whnf v evaluates to nf w"

  boxvar : ∀ {Δ Γ A} -> Val (Δ , A) Γ (□ A)
  boxvar = DK-val-boxI (left empty (DK-val-ne (DK-ne-var top))) (DK-var top)

  data _↓_  {Δ Γ} : ∀ {A} -> (Val Δ Γ A) -> (Nf Δ Γ A) -> Set where

    nf-ne : ∀ {A v} {m : Ne Δ Γ Val A}
                              -> m ↓ne v
               -------------------------------------
                  -> (DK-val-ne m) ↓ (DK-nf-ne v)

    nf-lam : ∀ {A B v w} {f : Val Δ Γ (A => B)}
    
               -> (val-weak-many-right f (weakone (subsetid _))) $ (DK-val-ne (DK-ne-var top)) >> v   -> v ↓ w
               -------------------------------------------------------------------
                                -> f ↓ (DK-nf-lam w)

    nf-prod1 : ∀ {A B v' w'}
                 {m : Val Δ Γ (A ∧ B)}
                 {v : Val Δ Γ A} {w : Val Δ Γ B}
    
                -> fst m >> v   -> snd m >> w   -> v ↓ v'   -> w ↓ w'
               -------------------------------------------------------
                            -> m ↓ (DK-nf-prod1 v' w')


    nf-box : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {A}
               {m : · / Η ⊢ A} {v : Val · Δ A} {w : Nf · Δ A}
    
                 ->  (ctxt-to-modal-ctxt E) ⊢ m ⇓ v       -> v ↓ w
               -------------------------------------------------------------------
                     -> (DK-val-boxI E m) ↓ (DK-nf-boxI w) 


  data _↓ne_  {Δ Γ} : ∀ {A} -> (Ne Δ Γ Val A) -> (Ne Δ Γ Nf A) -> Set where
  
      nf-var : ∀ {A} {x : A ∈ Γ}
      
               -------------------------------------
                  -> (DK-ne-var x) ↓ne (DK-ne-var x)

      nf-app : ∀ {A B} {t : Ne Δ Γ Val (A => B)}
                       {v : Ne Δ Γ Nf (A => B)}
                       {u : Val Δ Γ A}
                       {w : Nf Δ Γ A}
      
                  -> t ↓ne v              -> u ↓ w
               -------------------------------------------
                  -> (DK-ne-app t u) ↓ne (DK-ne-app v w)
                  
      nf-prod2 : ∀ {A B} {t : Ne Δ Γ Val (A ∧ B)}
                         {v : Ne Δ Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (DK-ne-prod2 t) ↓ne (DK-ne-prod2 v)

      nf-prod3 : ∀ {A B} {t : Ne Δ Γ Val (A ∧ B)}
                         {v : Ne Δ Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (DK-ne-prod3 t) ↓ne (DK-ne-prod3 v)

      nf-boxE : ∀ {A C} {t : Ne Δ Γ Val (□ A)}
                        {v : Ne Δ Γ Nf (□ A)}
                        {u : Val (Δ , A) Γ C}
                        {w : Nf (Δ , A) Γ C}
      
                  -> t ↓ne v              -> u ↓ w
               -------------------------------------------
                  -> (DK-ne-boxE t u) ↓ne (DK-ne-boxE v w)


  quote-str : ∀ {Δ Γ A w} -> (v : Val Δ Γ A) -> v ↓ w -> Σ (Nf Δ Γ A) (λ w' -> w ≡ w')

  quote-str (DK-val-ne x) (nf-ne y) = pair (DK-nf-ne _) refl
  quote-str (DK-val-ne x) (nf-lam p q) = pair (DK-nf-lam _) refl
  quote-str (DK-val-ne x) (nf-prod1 p q r s) = pair (DK-nf-prod1 _ _) refl
  quote-str (DK-val-lam E t) (nf-lam p q) = pair (DK-nf-lam _) refl
  quote-str (DK-val-prod1 E t u) (nf-prod1 p q r s) = pair (DK-nf-prod1 _ _) refl
  quote-str (DK-val-boxI E t) (nf-box p q) = pair (DK-nf-boxI _) refl 

  quote-ne-str : ∀ {Δ Γ A w} -> (v : Ne Δ Γ Val A)
                 -> v ↓ne w -> Σ (Ne Δ Γ Nf A) (λ w' -> w ≡ w')

  quote-ne-str (DK-ne-var x) nf-var = pair (DK-ne-var x) refl
  quote-ne-str (DK-ne-app t u) (nf-app p x) = pair (DK-ne-app _ _) refl
  quote-ne-str (DK-ne-prod2 t) (nf-prod2 p) = pair (DK-ne-prod2 _) refl
  quote-ne-str (DK-ne-prod3 t) (nf-prod3 p) = pair (DK-ne-prod3 _) refl
  quote-ne-str (DK-ne-boxE t u) (nf-boxE p x) = pair (DK-ne-boxE _ _) refl


nf-to-val : ∀ {Δ Γ A} -> (Nf Δ Γ A) -> (Val Δ Γ A)
nf-to-term : ∀ {Δ Γ A} -> (Nf Δ Γ A) -> (Δ / Γ ⊢ A)
ne-nf-to-val-nf : ∀ {Δ Γ A} -> (Ne Δ Γ Nf A) -> (Ne Δ Γ Val A)
ne-nf-to-term :  ∀ {Δ Γ A} -> (Ne Δ Γ Nf A) -> (Δ / Γ ⊢ A)

nf-to-val (DK-nf-ne x) = DK-val-ne (ne-nf-to-val-nf x)
nf-to-val (DK-nf-lam t) = DK-val-lam (id-ctxt _ _) (nf-to-term t)
nf-to-val (DK-nf-prod1 t u) = DK-val-prod1 (id-ctxt _ _) (nf-to-term t) (nf-to-term u)
nf-to-val (DK-nf-boxI t) = DK-val-boxI (id-ctxt _ _) (nf-to-term t)

nf-to-term (DK-nf-ne p) = ne-nf-to-term p
nf-to-term (DK-nf-lam t) = DK-lam (nf-to-term t)
nf-to-term (DK-nf-prod1 t u) = DK-prod1 (nf-to-term t) (nf-to-term u)
nf-to-term (DK-nf-boxI t) = DK-boxI (nf-to-term t)

ne-nf-to-val-nf (DK-ne-var p) = DK-ne-var p
ne-nf-to-val-nf (DK-ne-app t u) = DK-ne-app (ne-nf-to-val-nf t) (nf-to-val u)
ne-nf-to-val-nf (DK-ne-prod2 t) = DK-ne-prod2 (ne-nf-to-val-nf t)
ne-nf-to-val-nf (DK-ne-prod3 t) = DK-ne-prod3 (ne-nf-to-val-nf t)
ne-nf-to-val-nf (DK-ne-boxE t u) = DK-ne-boxE (ne-nf-to-val-nf t) (nf-to-val u)

ne-nf-to-term (DK-ne-var p) = DK-var p
ne-nf-to-term (DK-ne-app t u) = DK-app (ne-nf-to-term t) (nf-to-term u)
ne-nf-to-term (DK-ne-prod2 t) = DK-prod2 (ne-nf-to-term t)
ne-nf-to-term (DK-ne-prod3 t) = DK-prod3 (ne-nf-to-term t)
ne-nf-to-term (DK-ne-boxE t u) = DK-boxE (ne-nf-to-term t) (nf-to-term u)

-- Translation to STLC

trans-K : ∀ {Δ Γ A} -> Δ / Γ ⊢ A -> trans-cx (boxcx Δ) ++ trans-cx Γ STLC.⊢ trans-ty A

trans-K (DK-var p) = STLC.STLC-var (subsetdef (∈-trans-cx p) (concat-subset-2 _ _))
trans-K (DK-app t u) = STLC.STLC-app (trans-K t) (trans-K u)
trans-K (DK-lam t) = STLC.STLC-lam (trans-K t)
trans-K (DK-prod1 t u) = STLC.STLC-prod1 (trans-K t) (trans-K u)
trans-K (DK-prod2 t) = STLC.STLC-prod2 (trans-K t)
trans-K (DK-prod3 t) = STLC.STLC-prod3 (trans-K t)
trans-K {Δ} {Γ} {□ A} (DK-boxI t) =
  let u = trans-K t in
    STLC.STLC-unitize (trans-cx Γ) (STLC.STLC-lam (STLC.STLC-weak-many u
    (weakone ((subst (λ x → x ⊆ trans-cx Δ ++ trans-cx Γ) (sym (leftid++ (trans-cx Δ))) (concat-subset-1 (trans-cx Δ) (trans-cx Γ)))))))
trans-K {Δ} {Γ} {_} (DK-boxE t u) =
  STLC.STLC-cut · (trans-K t) (let p = trans-K u in STLC.STLC-weak-many p (swap-out (trans-cx (boxcx Δ)) (trans-cx Γ) _))


