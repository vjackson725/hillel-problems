
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
    | (Σ xs[0..i]) - (Σ xs[i..|xs|]) |
  in O(n) time and space

  I recall a similar problem was discussed by Guy L. Steel, see here
      https://www.youtube.com/watch?v=ftcIcn8AmSY
  The key trick is to notice that forward and backwards sums can be
  computed seperately, before you go about calculating their difference.
}-}
module Fulcrum where  
  open import Data.Product renaming (proj₁ to fst; proj₂ to snd) using (Σ; _,_)

  open import Data.Nat using (ℕ; _≤_; zero; suc; _≤?_; _≟_; _>_)
  open import Data.Nat.Properties using (≰⇒>)
  
  open import Data.Integer using (ℤ; _-_; ∣_∣)
  open import Data.Integer.Properties using (+-0-isCommutativeMonoid)
  
  open import Data.Vec using (Vec; []; _∷_; lookup; reverse; zipWith; map; [_]; _[_]=_; here; there)
  
  open import Data.Fin using (Fin; zero; suc; raise; fromℕ)
  
  open import Algebra using (Monoid; CommutativeMonoid)
  
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)


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
  -- a bit of kit first
  module _ {c ℓ} (M : Monoid c ℓ) where
    open Monoid M renaming (Carrier to A)

    -- A sort of generalised fold
    -- For each i, gives `fold _∙_ xs[0..i]`
    scan : {n : ℕ} → Vec A n → Vec A n
    scan xs = scan-tailrec ε xs
      where
        scan-tailrec : {n : ℕ} → A → Vec A n  → Vec A n
        scan-tailrec acc [] = []
        scan-tailrec acc (x ∷ xs) = let x' = acc ∙ x
                                    in x' ∷ scan-tailrec x' xs

  -- in particular, we care about the sum prefix
  sum-prefix : ∀ {n} → Vec ℤ n → Vec ℤ n
  sum-prefix = scan (CommutativeMonoid.monoid (record { isCommutativeMonoid = +-0-isCommutativeMonoid }))

  -- we can compute the value of _every_ fv, in 𝓞(n) time and space, and return the list of all of them
  -- (Because I'm doing a bit of trickery here, I probably should prove that this is a correct implementation of fv, but I'll leave that for now)
  every-fv : ∀ {n} → Vec ℤ n → Vec ℕ n
  every-fv xs = let forward  = sum-prefix xs                -- 𝓞(n)
                    -- a better list representation would make this even faster, but reverse is still linear
                    backward = sum-prefix (reverse xs)      -- 𝓞(n) + 𝓞(n) = 𝓞(n)
                    diffs    = zipWith _-_ forward backward -- 𝓞(n)
                    fvs      = map ∣_∣ diffs                -- 𝓞(n)
                 in fvs

  -- IsMin is prima-facie evidence that z is in the list, and where it is in the list (see isMin-to-Fin)
  fulcrum : {m : ℕ} → (xs : Vec ℤ (suc m)) → Σ ℕ (λ z → IsMin z (every-fv xs))
  fulcrum {m} xs = find-min (every-fv xs)
