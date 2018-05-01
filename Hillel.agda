
module Hillel where

{-}
  Leftpad

  This is basically @plorglezomp's solution, but in Agda
}-}

module LeftPad where
  open import Data.Product using (Σ; _,_)

  open import Relation.Nullary using (Dec; yes; no)
  
  open import Data.Nat using (ℕ; _≤?_; _⊔_; _+_; _∸_)
  open import Data.Nat.Properties using (m≤n⇒m∸n≡0; m∸n+n≡m; m≤n⇒n⊔m≡n; m≤n⇒m⊔n≡n; ≰⇒≥)

  open import Data.Vec using (Vec; []; _∷_; replicate; _++_)
  open import Data.Char using (Char)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
  
  max-neg-plus-law : (m n : ℕ) → (m ⊔ n) ≡ m ∸ n + n
  max-neg-plus-law m n with n ≤? m
  max-neg-plus-law m n | yes n≤m rewrite m∸n+n≡m n≤m | m≤n⇒n⊔m≡n n≤m = refl
  max-neg-plus-law m n | no ¬n≤m with ≰⇒≥ ¬n≤m
  max-neg-plus-law m n | _ | m≤n rewrite m≤n⇒m∸n≡0 m≤n | m≤n⇒m⊔n≡n m≤n = refl
  
  left-pad : ({k} n : ℕ) → (c : Char) → (s : Vec Char k) → Σ (Vec Char (n ⊔ k)) λ padded → padded ≅ replicate {n = n ∸ k} c ++ s
  left-pad {k} n c s rewrite max-neg-plus-law n k = (replicate {n = n ∸ k} c) ++ s , refl

{-}
  Unique

  I prove the strengthened spec of unique

  I only assume we have decidable equality, not ordering. This limits the solution to O(n²),
  but this can be improved by strengthening the assumptions to ordered, and changing out
  Unique for some sort of ordered set.
}-}

module Unique where
  open import Agda.Primitive using (_⊔_)
  
  open import Data.Product using (Σ; _,_; _×_)

  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary using (DecSetoid; Setoid; IsEquivalence)

  open import Data.List using (List; _∷_; [])
  open import Data.List.Any using (Any; here; there)
  open import Data.List.All renaming (map to All-map)
  open import Data.List.Any.Properties using (++⁺ʳ)

  -- assume we have decidable inequality
  module _ {c ℓ} (S : DecSetoid c ℓ) where
    open import Data.List.Membership.DecSetoid S

    open DecSetoid S renaming (Carrier to X)

    -- A proof that xs is a list comprised of unique elements from zs
    data Unique : (xs : List X) → (uniques : List X) → Set (c ⊔ ℓ) where
      -- the empty list always contains a unique collection of elements
      empty : ∀ {xs} → Unique xs []
      -- given a list of unique elements (uniques) from xs, a proof x ∉ uniques, and a proof x ∈ xs
      -- we have that the list (x ∷ uniques) is also unique
      cons : ∀ {xs uniques} → Unique xs uniques → (x : X) → x ∉ uniques → x ∈ xs → Unique xs (x ∷ uniques)

    -- if we have a list of unique elements from xs, then we also have a list of unique elements from x ∷ xs
    weaken-unique : ∀ {xs uniques x} → Unique xs uniques → Unique (x ∷ xs) uniques
    weaken-unique empty = empty
    weaken-unique {x = x} (cons u x' p q) with x' ≟ x
    weaken-unique {x = x} (cons u x' p q) | yes z = cons (weaken-unique u) x' p (here z)
    weaken-unique {x = x} (cons u x' p q) | no ¬z = cons (weaken-unique u) x' p (there q)

    -- generate the list of unique elements from xs
    -- Produces:
    --     a list of unique elements of xs
    --     a proof that the returned list is actually unique, and from xs
    --     a proof that all elements in xs are in uniques
    unique : (xs : List X) → Σ (List X) (λ uniques → (Unique xs uniques) × (All (_∈ uniques) xs))
    unique [] = [] , empty , []
    unique (x ∷ xs) with unique xs
    unique (x ∷ xs) | uniques , uP , all-xs with x ∈? uniques
    unique (x ∷ xs) | uniques , uP , all-xs | yes ex = uniques , weaken-unique uP , ex ∷ all-xs
    unique (x ∷ xs) | uniques , uP , all-xs | no ¬ex = x ∷ uniques , cons (weaken-unique uP) x ¬ex here-refl , here-refl ∷ All-map (++⁺ʳ (x ∷ [])) all-xs
      where
        here-refl : {x : X} {xs : List X} → Any (S DecSetoid.≈ x) (x ∷ xs)
        here-refl = here (IsEquivalence.refl (DecSetoid.isEquivalence S))

module Zippers where
  open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using (+-suc; +-identityʳ)

  open import Data.Vec using (Vec; []; _∷_; reverse; _++_; [_])

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  
  -- Backwards and Forwards Vectors
  Bwd : ∀ {a} (A : Set a) → ℕ → Set a
  Bwd = Vec

  pattern _∷▹_ xz x = x ∷ xz

  Fwd : ∀ {a} (A : Set a)→ ℕ → Set a
  Fwd = Vec

  pattern _◃∷_ x xs = x ∷ xs

  record Zipper {a} (A : Set a) (m n : ℕ) : Set a where
    constructor _▹◃_
    field
      prev : Bwd A m
      post : Fwd A n

  infix 18 _▹◃_

  module _ {a} {A : Set a} where
    stepᵣ : {m n : ℕ} → Zipper A m (suc n) → Zipper A (suc m) n
    stepᵣ (prev ▹◃ (x ◃∷ post)) = (prev ∷▹ x) ▹◃ post

    stepₗ : {m n : ℕ} → Zipper A (suc m) n → Zipper A m (suc n)
    stepₗ ((xs ∷▹ x) ▹◃ post) = xs ▹◃ (x ◃∷ post)

    step-rl-id : {m n : ℕ} (xs : Zipper A (suc m) (suc n)) → stepₗ (stepᵣ xs) ≡ xs
    step-rl-id ((prev ∷▹ xₗ) ▹◃ (xᵣ ◃∷ post)) = refl

    step-lr-id : {m n : ℕ} (xs : Zipper A (suc m) (suc n)) → stepᵣ (stepₗ xs) ≡ xs
    step-lr-id ((prev ∷▹ xₗ) ▹◃ (xᵣ ◃∷ post)) = refl

    -- reverse, the slow way
    reverse' : {n : ℕ} → Vec A n → Vec A n
    reverse' [] = []
    reverse' {suc n} (x ∷ xs) with xs ++ [ x ]
    ... | xs' rewrite +-suc n 0 | +-identityʳ n = xs'

    zipper-move-to-start :{m n : ℕ} (xs : Zipper A m n) → Zipper A 0 (m ℕ+ n)
    zipper-move-to-start ([] ▹◃ post) = [] ▹◃ post
    zipper-move-to-start {suc m} {n = n} z@((x ∷ prev) ▹◃ post) with zipper-move-to-start (stepₗ z)
    ... | z' rewrite +-suc m n = z'

    zipper-move-to-end : {m n : ℕ} (xs : Zipper A m n) → Zipper A (m ℕ+ n) 0
    zipper-move-to-end {m} (prev ▹◃ []) rewrite +-identityʳ m = prev ▹◃ []
    zipper-move-to-end {m} {suc n} z@(prev ▹◃ (x ∷ post)) with zipper-move-to-end (stepᵣ z)
    ... | z' rewrite +-suc m n = z'



{-}
  Fulcrum

  Find the i that minimises
    | (Σ xs[0...i]) - (Σ xs[(i+1)..|xs|]) |
  in O(n) time and space

  I solve the generalised version where we start with i = 0

  As a sidenote, I recall a similar problem was discussed by Guy L. Steel, see here
      https://www.youtube.com/watch?v=ftcIcn8AmSY
  I started off with an approach like this, but worked out an even better way
}-}
module Fulcrum where
  open import Agda.Primitive using (_⊔_; lzero; lsuc)
  open import Level using (Lift; lift)

  open import Data.Product renaming (proj₁ to fst; proj₂ to snd; map to mapΣ) using (Σ; _,_; ∃; ∃₂; _×_)

  open import Data.Nat using (ℕ; _≤_; zero; suc; _≤?_; _≟_; _>_; _<″_; _≤″_; _∸_) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using (≰⇒>; ≤⇒≤″; m+n∸n≡m) renaming (+-suc to ℕ+-suc; +-identityʳ to ℕ+-identityʳ)
  
  open import Data.Integer using (ℤ; _+_; -_; _-_; ∣_∣)
  open ℤ using () renaming (pos to +_)
  open import Data.Integer.Properties using (+-comm; +-assoc; +-0-isCommutativeMonoid; +-inverseʳ; +-inverseˡ; +-identityˡ; +-identityʳ)

  open import Data.Sign using (Sign)
  
  open import Data.Vec using (Vec; []; _∷_; reverse; zipWith; map; [_]; _[_]=_; here; there; splitAt; take; drop; _++_; foldr; foldl)
  open import Data.Vec.Properties using ()
  
  open import Data.Fin using (Fin; zero; suc; raise; fromℕ≤″; toℕ)
  open import Data.Fin.Properties using (bounded)

  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
  open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

  open import Relation.Binary using (Rel; Setoid)

  open import Algebra using (Monoid; CommutativeMonoid)
  open import Algebra.Structures using (IsMonoid; IsCommutativeMonoid)

  open import Function using (_$_)


  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt

  -- A proof that an element is minimal, from xs, and its location
  data IsMin : {n : ℕ} → ℕ → (xs : Vec ℕ (suc n)) → Set where
    -- in the singleton list, x is always minimal
    single : {x : ℕ} → IsMin x [ x ]
    -- we are provided proof that x ≤ y, so we stick with x
    keep : {n : ℕ} {x y : ℕ} {xs : Vec ℕ (suc n)} → IsMin x xs → x ≤ y → IsMin x (y ∷ xs)
    -- we are provided proof that x > y, so we switch to y
    new : {n : ℕ} {x y : ℕ} {xs : Vec ℕ (suc n)} → IsMin x xs → x > y → IsMin y (y ∷ xs)

  -- while finding the min, we construct a proof the min is the min
  find-min : {n : ℕ} → (xs : Vec ℕ (suc n)) → Σ ℕ (λ z → IsMin z xs)
  find-min (x ∷ []) = x , single
  find-min (x ∷ x' ∷ xs) with find-min (x' ∷ xs)
  find-min (x ∷ x' ∷ xs) | z , p with z ≤? x
  find-min (x ∷ x' ∷ xs) | z , p | yes z≤x = z , keep p z≤x
  find-min (x ∷ x' ∷ xs) | z , p | no  z≰x with ≰⇒> z≰x
  ... | x<z = x , new p x<z

  -- convert an IsMin into a Fin, a bounded integer, and a proof that it is indeed in the correct location
  -- (mainly to demonstrate that IsMin _is_ actually enough information to index into the list)
  isMin-to-Fin : {n : ℕ} {z : ℕ} {xs : Vec ℕ (suc n)} → IsMin z xs → Σ (Fin (suc n)) (λ i → xs [ i ]= z)
  isMin-to-Fin single = zero , here
  isMin-to-Fin (keep m _) with isMin-to-Fin m
  isMin-to-Fin (keep m _) | i , p = (suc i) , (there p)
  isMin-to-Fin (new m _) = zero , here



  -- now on to fulcrum values


  -- Unfortunately, we can't get any more powerful (i.e. saying {B : ℕ → Set b}) without function extensionality
  module FoldLemmas {a b} {A : Set a} {B : Set b} (_∙_ : A → B → B) (_⊕_ : B → A → B)
           (assoc : ∀ a b c → (a ∙ b) ⊕ c ≡ a ∙ (b ⊕ c))
    where

    foldl' : ∀ {n} → B → Vec A n → B
    foldl' = foldl _ _⊕_

    foldr' : ∀ {n} → B → Vec A n → B
    foldr' = foldr _ _∙_

    foldr-initialʳ-outerʳ : {n : ℕ} (x : A) (α : B) (xs : Vec A n) → (foldr' (α ⊕ x) xs) ≡ (foldr' α xs) ⊕ x
    foldr-initialʳ-outerʳ x a [] = refl
    foldr-initialʳ-outerʳ x a (x₁ ∷ xs) rewrite foldr-initialʳ-outerʳ x a xs
                                              | sym $ assoc x₁ (foldr _ _∙_ a xs) x
                                              = refl

    foldl-initialˡ-outerˡ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → (foldl' (x ∙ b) xs) ≡ x ∙ (foldl' b xs)
    foldl-initialˡ-outerˡ x b [] = refl
    foldl-initialˡ-outerˡ x b (x₁ ∷ xs) rewrite assoc x b x₁
                                              | foldl-initialˡ-outerˡ x (b ⊕ x₁) xs
                                              = refl

    module CommutFoldLemmas (comm : ∀ a b → a ∙ b ≡ b ⊕ a) where
      foldl-initialʳ-outerʳ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldl' (b ⊕ x) xs ≡ foldl' b xs ⊕ x
      foldl-initialʳ-outerʳ x b xs rewrite sym $ comm x b
                                          | foldl-initialˡ-outerˡ x b xs
                                          | comm x (foldl' b xs)
                                          = refl
  
      foldl-initialʳ-outerˡ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldl' (b ⊕ x) xs ≡ x ∙ foldl' b xs
      foldl-initialʳ-outerˡ x b xs rewrite sym $ comm x b
                                          | foldl-initialˡ-outerˡ x b xs
                                          = refl
  
      foldl-initialˡ-outerʳ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldl' (x ∙ b) xs ≡ foldl' b xs ⊕ x
      foldl-initialˡ-outerʳ x b xs rewrite foldl-initialˡ-outerˡ x b xs
                                          | comm x (foldl' b xs)
                                          = refl

      foldr-initialˡ-outerˡ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldr' (x ∙ b) xs ≡ x ∙ foldr' b xs
      foldr-initialˡ-outerˡ x a xs rewrite comm x a
                                          | foldr-initialʳ-outerʳ x a xs
                                          | comm x (foldr' a xs)
                                          = refl
  
      foldr-initialʳ-outerˡ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldr' (b ⊕ x) xs ≡ x ∙ foldr' b xs
      foldr-initialʳ-outerˡ x a xs rewrite comm x a
                                          | foldr-initialʳ-outerʳ x a xs
                                          | comm x (foldr' a xs)
                                          = refl
  
      foldr-initialˡ-outerʳ : {n : ℕ} (x : A) (b : B) (xs : Vec A n) → foldr' (x ∙ b) xs ≡ foldr' b xs ⊕ x
      foldr-initialˡ-outerʳ x a xs rewrite comm x a
                                          | foldr-initialʳ-outerʳ x a xs
                                          = refl

  -- some algebra
  module MonoidFold {a} {A : Set a} {_∙_} {ε : A} (M : IsMonoid _≡_ _∙_ ε) where
    open Monoid (record { isMonoid = M }) using (assoc)
    open FoldLemmas _∙_ _∙_ assoc
      
    foldmr : {n : ℕ} → A → Vec A n → A
    foldmr a = foldr _ _∙_ a

    foldmr-addˡ : {n : ℕ} → (x : A) (a : A) (xs : Vec A n) → foldmr a (x ∷ xs) ≡ x ∙ foldmr a xs
    foldmr-addˡ x a [] = refl
    foldmr-addˡ x a (x₁ ∷ xs) rewrite foldmr-addˡ x₁ a xs = refl

    foldml : {n : ℕ} → A → Vec A n → A
    foldml a = foldl _ _∙_ a

    foldml-addʳ : {n : ℕ} (x : A) (a : A) (xs : Vec A n) → foldml a (x ∷ xs) ≡ foldml (a ∙ x) xs
    foldml-addʳ x a xs = refl

  module CommutMonoidFold {a} {A : Set a} {_∙_} {ε : A} (M : IsCommutativeMonoid _≡_ _∙_ ε) where
    open CommutativeMonoid (record { isCommutativeMonoid = M }) using (isMonoid; comm; assoc)
    open MonoidFold isMonoid

    open FoldLemmas _∙_ _∙_ assoc
    open CommutFoldLemmas comm

    foldml-addˡ : {n : ℕ} (x : A) (a : A) (xs : Vec A n) → foldml a (x ∷ xs) ≡ foldml (x ∙ a) xs
    foldml-addˡ x a xs rewrite comm a x = refl

    foldmr-addʳ : {n : ℕ} (x : A) (a : A) (xs : Vec A n) → foldmr a (x ∷ xs) ≡ (foldmr a xs ∙ x)
    foldmr-addʳ x a [] = comm x a
    foldmr-addʳ x a (x₁ ∷ xs) rewrite foldmr-addʳ x₁ a xs
                                    | comm x (foldr _ _∙_ a xs ∙ x₁)
                                    = refl

    -- under a commutative operation, a fold is the same
    foldm-same : {n : ℕ} (a : A) (xs : Vec A n) → foldmr a xs ≡ foldml a xs
    foldm-same a [] = refl
    foldm-same a (x ∷ xs) rewrite foldl-initialʳ-outerˡ x a xs
                                | foldm-same a xs
                                = refl

  -- in particular, we care about sum
  open MonoidFold (IsCommutativeMonoid.isMonoid (+-0-isCommutativeMonoid)) using () renaming (foldml to suml-from; foldmr to sumr-from)
  
  suml : {n : ℕ} → Vec ℤ n → ℤ
  suml xs = suml-from (+ 0) xs
  
  sumr : {n : ℕ} → Vec ℤ n → ℤ
  sumr xs = sumr-from (+ 0) xs


  -- the given definition of fulcrum values
  fv : (m {n} : ℕ) (xs : Vec ℤ n) → m ≤″ n → ℕ
  fv m xs (Data.Nat.less-than-or-equal refl) = ∣ sumr (take m xs) - sumr (drop m xs) ∣

  -- fv in several steps
  fv' : (m {n} : ℕ) (xs : Vec ℤ (m ℕ+ n)) → ℕ
  fv' m xs with splitAt m xs
  fv' m .(ys ++ zs) | ys , zs , refl with sumr ys | sumr zs
  ... | a | b = ∣ a - b ∣

  -- here's a setup which generates all the pairs in order, but with the first part reversed
  -- (in a generic way so we get theorems for free)
  module _ {a} {A : Set a} where
    splits-pair₀ : {n : ℕ} → Vec A n → Vec A 0 × Vec A n
    splits-pair₀ xs = [] , xs

    splits-pair₊ : {a b : ℕ} → Vec A a × Vec A (suc b) → Vec A (suc a) × Vec A b
    splits-pair₊ (as , x ∷ bs) = x ∷ as , bs

    splits-pair-lemma :  {a b : ℕ} {z : A} (xs : Vec A a) (ys : Vec A b) → (p : Vec A (suc a) × Vec A b) →
                         p ≡ splits-pair₊ (xs , z ∷ ys) →
                         (fst p ≡ z ∷ xs) × (snd p ≡ ys)
    splits-pair-lemma xs ys .(_ ∷ xs , ys) refl = refl , refl

    open Data.Vec using (_∷ʳ_)
    
--    open FoldLemmas {!!} {!!} {!!}

    splitAt′ : (m {n} : ℕ) → (xs : Vec A (m ℕ+ n)) → ∃₂ λ (ys : Vec A m) (zs : Vec A n) → (reverse ys) ++ zs ≡ xs
    splitAt′ zero xs = [] , xs , refl
    splitAt′ (suc m) (x ∷ xs) with splitAt′ m xs
    splitAt′ (suc m) (x ∷ .(reverse ys ++ zs)) | ys , zs , refl = x ∷ ys , zs , cong (_++ zs)
      {foldl (λ n → Vec A (suc n)) _ (x ∷ []) ys} {x ∷ reverse ys}
      {!!}

  -- now, let's look at a similar setup, but augmented with ℤ
  record Sums (m n : ℕ) : Set where
    field
      prev : Vec ℤ m
      post : Vec ℤ n
      a : ℤ
      b : ℤ
      a-proof : a ≡ sumr prev
      b-proof : b ≡ sumr post

  fv-pair₀ : {n : ℕ} → Vec ℤ n → Sums 0 n
  fv-pair₀ xs = record { prev = []
                       ; post = xs
                       ; a = + 0
                       ; b = sumr xs
                       ; a-proof = refl
                       ; b-proof = refl
                       }

  fv-pair₊ : {m n : ℕ} → Sums m (suc n) → Sums (suc m) n
  fv-pair₊ record { prev = prev
                  ; post = x ∷ post
                  ; a = a
                  ; b = b
                  ; a-proof = refl
                  ; b-proof = refl
                  }
                  = record { prev = x ∷ prev
                           ; post = post
                           ; a = x + a
                           ; b = (- x) + b
                           ; a-proof = refl
                           ; b-proof = lemma x (sumr post)
                           }
    where
      lemma : (x y : ℤ) → (- x) + (x + y) ≡ y
      lemma x y rewrite sym (+-assoc (- x) x y)
                      | +-inverseˡ x
                      | +-identityˡ y
                      = refl

{-

The splitAt operation on lists can be done efficiently, but only for a single (m : ℕ) argument. You can't step the process without
appending from the back, which is 𝓞(n), and makes computing every value 𝓞(n²).

However, if you let the first list be reversed, you can easily step the operation in 𝓞(1) time, making computing every pair 𝓞(n).

              xs , x ∷ ys  ---------------------->  xs ++ [ x ] , ys
               
                                      /\
                                      ||
                                      ||
                                      \/
                             
               xsᵣ , x ∷ ys -----------------------> x ∷ xsᵣ , ys
             
If we then apply sum to each of these, they are the same value in each case, because _+_ is commutative.
               
 sum (take m xs) , sum (drop m xs) ---------> sum (take (suc m) xs) , sum (drop (suc m) xs)

                                      ||
                                      ||

      sum (f₋ m xs) , sum (f₊ m xs) -----> sum (f₋ (suc m) xs) , sum (f₊ (suc m) xs)

-}





--  fv-pairs : {n : ℕ} → Vec ℤ n → Vec (ℤ × ℤ) (suc n)
--  fv-pairs xs with fv-pair₀ xs
--  fv-pairs [] | ε = [ project-sums ε ]
--  fv-pairs (x ∷ xs) | a , ([] , x' ∷ xs') , b = {!!}



  -- we can compute the value of _every_ fv, in 𝓞(n) time and space, and return the list of all of them
  every-fv : {n : ℕ} → (xs : Vec ℤ n) → Vec ℕ n
  every-fv {n} xs = let pairs = {!!}          -- 𝓞(n)
                     in map (λ { (a , b) → ∣ a - b ∣ }) pairs

  -- IsMin is prima-facie evidence that z is minimum, in the list, and gives where it is in the list (see isMin-to-Fin)
  fulcrum : {m : ℕ} → (xs : Vec ℤ (suc m)) → Σ ℕ (λ z → IsMin z (every-fv xs))
  fulcrum {m} xs = find-min (every-fv xs)
