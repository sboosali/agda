module Vector where


data Nat : Set where
 z : Nat
 s_ : Nat -> Nat
infixr 90 s_

data Vec (X : Set) : Nat -> Set where
 []   : Vec X z
 _::_ : {n : Nat} -> X -> Vec X n -> Vec X (s n)
infixr 20 _::_
-- Vec is "parametrized" by a Set X and "indexed" over the Set Nat
-- Vec is dependently-typed <- type ~> length ~> value

data Under : Nat -> Set where -- the set of naturals less than some natural
 Z< : {n : Nat} -> Under (s n)
 _S< : {n : Nat} -> Under n -> Under (s n)
 -- you can prove that zero < _+1
 -- a proof that x < n makes a proof that x+1 < n+1
infixl 90 _S<

_[_] : {X : Set}{n : Nat} -> Vec X n -> Under n -> X
[]      [   () ] -- [] : Vec _ z -- () : Under z -- "nothing is under zero" like the Faceless Men talk
x :: _  [   Z< ] = x
_ :: xs [ i S< ] = xs [ i ]
infix 10 _[_]


-- for "Under", i wanted a datatype such that all values under some number could share a type.
-- that way, you could pass any index of type "Under 3" (i.e. index is either 0 or 1 or 2) to a vector of type "Vec _ 3" (i.e. length is 3)
-- conversely and in particular, 0 (i.e. Z<) is under every positive number (i.e. s _)
-- Z<         : Under (s s s n) -- 0 < 3
-- S< Z<      : Under (s s s n) -- 1 < 3
-- S< (S< Z<) : Under (s s s n) -- 2 < 3
-- S< (S< (S< Z<)) :not U... -- 3 not< 3
-- different constructors can make the same datatypes (e.g. any Nat)

-- (type error)
-- xs : Vec Nat (s s z)
-- xs = (z :: s z :: s s z :: [])

xs : Vec Nat (s s s z)
xs = (z :: s z :: s s z :: [])

-- (type error)
-- xs : Vec Nat (s s s s z)
-- xs = (z :: s z :: s s z :: [])

1st : Under (s s s z)
1st = Z<

xs[0] = xs [ 1st ]

2nd : Under (s s s z)
2nd = Z< S<

xs[1] = xs [ 2nd ]

3rd : Under (s s s z)
3rd = Z< S< S<

xs[2] = xs [ 3rd ]

-- (type error)
-- -4th : Under (s s s z)
-- -4th = Z< S< S< S<

4th : Under (s s s s z)
4th = Z< S< S< S<

-- (type error)
-- xs[3] : Nat
-- xs[3] = xs [ 4th ]

-- agda -I Proof.agda
-- ? :typeOf 1st
-- ? :typeOf xs
