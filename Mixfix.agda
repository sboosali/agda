module Mixfix where

data Nat : Set where
 z : Nat
 s_ : Nat -> Nat
infixr 90 s_

_+_ : Nat -> Nat -> Nat
z + x = x
s x + y = s (x + y)
infixl 40 _+_

_*_ : Nat -> Nat -> Nat
z * _ = z
s x * y  =  y  +  x * y
infixl 50 _*_

_! : Nat -> Nat
z   ! = s z
s z ! = s z
s x ! = x ! * s x
infixl 70 _!

_-_ : Nat -> Nat -> Nat
z - _     = z
x - z     = x
s x - s y = x - y
infixl 40 _-_

fib : Nat -> Nat
fib z       = s z
fib (s z)   = s z
fib (s s x) = fib (s x) + fib x


data Bool : Set where
 false : Bool
 true  : Bool

-_ : Bool -> Bool
- false = true
- true = false
infixr 80 -_

_\/_ : Bool -> Bool -> Bool
true \/ _ = true
false \/ x = x
infixl 20 _\/_

_/\_ : Bool -> Bool -> Bool
false /\ _ = false
true  /\ x = x
infixl 30 _/\_

_≤_ : Nat -> Nat -> Bool
z     ≤ _        = true
(s _) ≤ z     = false
(s n) ≤ (s m) = n ≤ m

_≤_≤_ : Nat -> Nat -> Nat -> Bool
a ≤ x ≤ b = (a ≤ x) /\ (x ≤ b)

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else _ = x
if false then _ else y = y
infix 5 if_then_else_

_if_else_ : {A : Set} -> A -> Bool -> A -> A
x if c else y = if c then x else y
infixr 5 _if_else_


data List (A : Set) : Set where
 []   : List A
 _::_ : A -> List A -> List A
infixr 15 _::_

||_|| : {A : Set} -> List A -> Nat
|| [] ||      = z
|| _ :: xs || = s z + || xs ||
infix 10 ||_||


data Maybe (A : Set) : Set where
 None : Maybe A
 Some : A -> Maybe A

_?? : Set -> Set
T ?? = Maybe T

_[_] : {A : Set} -> List A -> Nat -> A ??
[] [ _ ]        = None
x :: _ [ z ]    = Some x
_ :: xs [ s i ] = xs [ i ]
infix 10 _[_]


-- idea: declare fixity DAG with parenthesized expressions
-- e.g.: "fixity (x * y) + z"  ->  fixity _*_ > fixity _+_

-- idea: declare associativity with parenthesized expressions
-- e.g.: "associativity (x + y) + z"  ->  infixl _+_


-- $ agda -I Mixfix.agad

-- ? s s z + s s s z
-- s s s s s z

-- ? s s z * s s s z
-- s s s s s s z

-- ? s s s s z !
-- s s s s s s s s s s s s s s s s s s s s s s s s z

-- ? fib (s s s s s z)
-- s s s s s s s s z

-- ? s s s z - s s z
-- s z

-- ? s s s z - s s z + s z
-- (same fixity, same associativity)
-- s s z


-- ? z ≤ s z ≤ s (s z)
-- true

-- ? if true then s z :: [] else []
-- s z :: []

-- ? s z :: [] if true else []
-- s z :: []

-- ? s z :: s s z :: s s s z :: []

-- ? || s z :: s s z :: s s s z :: [] ||
-- s s s z

-- ? (s z :: s s z :: s s s z :: []) [ s s z ]
-- s s s z

