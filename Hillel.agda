
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

{-}
  Fulcrum

  Find the i that minimises
    | (Σ xs[0..=i]) - (Σ xs[(i+1)..|xs|]) |
  in O(n) time and space

  I solve the generalised version where we start with i = 0

  As a sidenote, I recall a similar problem was discussed by Guy L. Steel, see here
      https://www.youtube.com/watch?v=ftcIcn8AmSY
  I started off with an approach like this, but worked out an even better way
}-}
module Fulcrum where
  open import Data.Product using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂)

  open import Data.Vec using (Vec; []; _∷_; foldr; foldr₁; [_]; _[_]=_; here; there; map; splitAt; _++_)
  open import Data.Vec.Properties using (map-∘)

  open import Data.Integer using (ℤ; _+_; +_; _-_; -_; ∣_∣)
  open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; +-assoc)

  open import Data.Nat using (ℕ; zero; suc; _∸_; _≤″_; _≤_; _≤?_; _>_;  _<″_; _⊓_; pred) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using (≰⇒>; ≰⇒≥; m≤n⇒m⊓n≡m; m≤n⇒n⊓m≡m; n∸n≡0; ⊓-isSemigroup) renaming (+-identityʳ to ℕ+-identityʳ)

  open import Data.Fin using (Fin; zero; suc)

  open import Relation.Nullary using (Dec; yes; no)
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_; refl; sym; cong)


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

  sum : {n : ℕ} → Vec ℤ n → ℤ
  sum = foldr _ _+_ (+ 0)

  scanl : ∀ {a b} {A : Set a} {B : Set b} {m} →
          (B → A → B) → B → Vec A m → Vec B (suc m)
  scanl _∙_ b []       = b ∷ []
  scanl _∙_ b (a ∷ xs) = b ∷ scanl _∙_ (b ∙ a) xs


  -- amusingly, it turns out writing the specifying function was more annoying than writing the fast one

  idx-adjust : ∀ {n} → Σ ℕ (λ m → m ≤″ n) → Σ ℕ (λ m → m ≤″ suc n)
  idx-adjust (m , _≤″_.less-than-or-equal refl) = suc m , _≤″_.less-than-or-equal refl

  -- note this is 𝓞(n²)
  indicies : {n : ℕ} → Vec (∃ λ (m : ℕ) → m ≤″ n) n
  indicies {zero} = []
  indicies {suc n} = (1 , _≤″_.less-than-or-equal refl) ∷ (map idx-adjust indicies)

  sum-sides : {n : ℕ} → Vec ℤ n → ∃ (λ m → m ≤″ n) → ℤ × ℤ
  sum-sides xs (m , _≤″_.less-than-or-equal refl) with splitAt m xs
  sum-sides .(ys ++ zs) (m , _≤″_.less-than-or-equal refl) | ys , zs , refl = sum ys , sum zs

  fulcrum-slow : {n : ℕ} → Vec ℤ n → ∃₂ λ (xs : Vec ℕ (suc n)) (m : ℕ) → IsMin m xs
  fulcrum-slow {n} xs = let sums = map (sum-sides (+ 0 ∷ xs)) indicies
                            fulcrums = map (λ { (a , b) → ∣ a - b ∣ }) sums
                         in fulcrums , find-min fulcrums


  -- Fast Fulcrum
  fulcrum : {n : ℕ} → Vec ℤ n → ∃₂ λ (xs : Vec ℕ (suc n)) (m : ℕ) → IsMin m xs
  fulcrum xs = let sums = scanl (λ { (sumₗ , sumᵣ) x → sumₗ + x , sumᵣ - x }) (+ 0 , sum xs) xs
                   fulcrums = map (λ { (sumₗ , sumᵣ) → ∣ sumₗ - sumᵣ ∣ }) sums
                in fulcrums , find-min fulcrums


  -- Proof

  open P.≡-Reasoning

  help : ∀ n (xs : Vec ℤ n) x z →
       map (sum-sides (z + x ∷ xs)) (map idx-adjust indicies)
       ≡
       map (sum-sides (z ∷ x ∷ xs))
         (map idx-adjust (map idx-adjust indicies))
  help n xs x z rewrite sym (map-∘ idx-adjust idx-adjust (indicies {n}))
                      | sym (map-∘ (sum-sides (z + x ∷ xs)) idx-adjust (indicies {n}))
                      | sym (map-∘ (sum-sides (z ∷ x ∷ xs)) (λ x → idx-adjust (idx-adjust x)) (indicies {n}))
                      = cong (λ f → map f (indicies {n}))  {!!}

  -- proving the core logic is the same
  fulcrum-core-equiv : ∀ {m} (z : ℤ) (xs : Vec ℤ m) →
               scanl
                 (λ { (sumₗ , sumᵣ) x → sumₗ + x , sumᵣ + - x })
                 (z , sum xs)
                 xs
               ≡
               (z , + 0 + sum xs) ∷
                 map (sum-sides (z ∷ xs))
                   (map
                     idx-adjust
                     indicies)
  fulcrum-core-equiv z [] = refl
  fulcrum-core-equiv z (x ∷ xs) rewrite +-identityˡ (x + sum xs)
                                      | +-identityˡ x
                                      | +-identityʳ x
                                      | +-comm x (sum xs)
                                      | +-assoc (sum xs) x (- x)
                                      | +-inverseʳ x
                                      | +-identityʳ (sum xs)
                                      | fulcrum-core-equiv (z + x) xs
                                      | +-identityˡ (sum xs)
                                      = cong (_ ∷_) (cong (_ ∷_) {!!})


  fulcrum-equiv : {m : ℕ} → (xs : Vec ℤ m) → fulcrum xs ≡ fulcrum-slow xs
  fulcrum-equiv {m} xs = begin
                           fulcrum xs
                         ≡⟨ {!!} ⟩
                           fulcrum-slow xs
                         ∎
