
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

  -- assume we have decidable equality
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

{-}
  Fulcrum

  Find the i that minimises
    | (Σ xs[0..=i]) - (Σ xs[(i+1)..|xs|]) |
  in 𝓞(n) time and space

  I solve the generalised version where we start with i = 0

  As a sidenote, I recall a similar problem was discussed by Guy L. Steel, see here
      https://www.youtube.com/watch?v=ftcIcn8AmSY
  I started off with an approach like this, but worked out an even better way
}-}
module Fulcrum where
  open import Data.Product using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂)

  open import Data.Vec using (Vec; []; _∷_; foldr; [_]; _[_]=_; here; there; map; _++_; splitAt; take; drop)

  open import Data.Integer using (ℤ; _+_; +_; _-_; -_; ∣_∣)
  open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; +-assoc)

  open import Data.Nat using (ℕ; zero; suc; _≤″_; _≤_; _≤?_; _>_) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using (≰⇒>; ≰⇒≥)

  open import Data.Fin using (Fin; zero; suc; fromℕ≤″) 
  open import Data.Fin.Properties using ()

  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

  -- to start, finding the minimum of Vecs

  -- A proof that an element in the Vec xs is minimal, and its location
  data IsMin : {n : ℕ} → ℕ → (xs : Vec ℕ (suc n)) → Set where
    -- in the singleton list, x is always minimal
    single : {x : ℕ} → IsMin x [ x ]
    -- we are provided proof that x ≤ y, so we stick with x
    keep : {n : ℕ} {x y : ℕ} {xs : Vec ℕ (suc n)} → IsMin x xs → x ≤ y → IsMin x (y ∷ xs)
    -- we are provided proof that x > y, so we switch to y
    new : {n : ℕ} {x y : ℕ} {xs : Vec ℕ (suc n)} → IsMin x xs → x > y → IsMin y (y ∷ xs)

  -- construct a proof the min is the min, while finding it
  find-min : {n : ℕ} → (xs : Vec ℕ (suc n)) → Σ ℕ (λ m → IsMin m xs)
  find-min (x ∷ []) = x , single
  find-min (x ∷ x' ∷ xs) with find-min (x' ∷ xs)
  find-min (x ∷ x' ∷ xs) | z , p with z ≤? x
  find-min (x ∷ x' ∷ xs) | z , p | yes z≤x = z , keep p z≤x
  find-min (x ∷ x' ∷ xs) | z , p | no  z≰x with ≰⇒> z≰x
  ... | x<z = x , new p x<z

  -- convert an IsMin into a Fin, a bounded integer, and a proof that it is indeed in the correct location
  -- (mainly to demonstrate that IsMin is actually enough information to index into the list)
  isMin-to-Fin : {n : ℕ} {z : ℕ} {xs : Vec ℕ (suc n)} → IsMin z xs → ∃ λ (i : Fin (suc n)) → xs [ i ]= z
  isMin-to-Fin single = zero , here
  isMin-to-Fin (keep m _) with isMin-to-Fin m
  isMin-to-Fin (keep m _) | i , p = (suc i) , (there p)
  isMin-to-Fin (new m _) = zero , here


  -- and now, to actually write a fulcrum

  sum : ∀ {n} → Vec ℤ n → ℤ
  sum = foldr _ _+_ (+ 0)

  scanl : ∀ {a b} {A : Set a} {B : Set b} {m} →
          (B → A → B) → B → Vec A m → Vec B (suc m)
  scanl _∙_ b []       = b ∷ []
  scanl _∙_ b (a ∷ xs) = b ∷ scanl _∙_ (b ∙ a) xs

  -- Fast Fulcrum

  -- make fulcrum pairs, which start with a base number, by a scan
  -- Sketch:
  --   essentially, you can just pass the current sums along, add x to the left, subtract x from the right
  --   and this gets you the new sums for that index
  make-fulcrum-pairs : ∀ {n} → ℤ → Vec ℤ n → Vec (ℤ × ℤ) (suc n)
  make-fulcrum-pairs base xs = scanl (λ { (sumₗ , sumᵣ) x → sumₗ + x , sumᵣ - x }) (base , sum xs) xs

  fulcrum : {n : ℕ} → Vec ℤ n → ∃₂ λ (xs : Vec ℕ (suc n)) (m : ℕ) → IsMin m xs
  fulcrum xs = let sums = make-fulcrum-pairs (+ 0) xs
                   fulcrums = map (λ { (sumₗ , sumᵣ) → ∣ sumₗ - sumᵣ ∣ }) sums
                in fulcrums , find-min fulcrums

  -- Proof of Correctness

  theP : ∀ {x} {X Y : Set x} → X ≡ Y → X → Y
  theP refl x = x

  s≤″s : ∀ {m n} → m ≤″ n → suc m ≤″ suc n
  s≤″s (_≤″_.less-than-or-equal refl) = _≤″_.less-than-or-equal refl

  -- The fulcrum pair at index m is the sums of the two halves the vec xs, divided at m
  -- Have to start with a base of z for the induction to go through
  make-fulcrum-pairs-correctness : ∀ m {n} (z : ℤ) (xs : Vec ℤ n) (i : m ≤″ n) →
               (make-fulcrum-pairs z xs) [ fromℕ≤″ m (s≤″s i) ]= (
                    z + sum (take m (theP (cong (Vec _) (sym (_≤″_.proof i))) xs)) ,
                    sum (drop m (theP (cong (Vec _) (sym (_≤″_.proof i))) xs)))
  make-fulcrum-pairs-correctness zero z [] (_≤″_.less-than-or-equal refl) rewrite +-identityʳ z = here
  make-fulcrum-pairs-correctness zero z (x ∷ xs) (_≤″_.less-than-or-equal refl) rewrite +-identityʳ z = here
  make-fulcrum-pairs-correctness (suc m) z (x ∷ xs) (_≤″_.less-than-or-equal refl) with make-fulcrum-pairs-correctness m (z + x) xs (_≤″_.less-than-or-equal refl)
  ... | p with splitAt m xs
  make-fulcrum-pairs-correctness (suc m) z (x ∷ xs@.(ys ++ zs)) (_≤″_.less-than-or-equal refl) | p | ys , zs , refl
                           rewrite sym (+-assoc z x (sum ys))
                                 | +-comm x (sum xs)
                                 | +-assoc (sum xs) x (- x)
                                 | +-inverseʳ x
                                 | +-identityʳ (sum xs)
                                 = there p
