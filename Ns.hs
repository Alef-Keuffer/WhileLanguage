{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UnicodeSyntax             #-}
{-# OPTIONS_HADDOCK show-extensions    #-}

module Ns where

-- * Grammar

type Var = String
type ℤ = Integer
type State = Var → ℤ

data A = N ℤ | V Var | A :+: A | A :⋆: A | A :-: A deriving Show
data B = T | F | A :=: A | A :≤: A | Not B | B :∧: B deriving Show
data S = Var :≔: A | Skip | S :︔: S | If B S S | While B S deriving Show

-- ** Substitution

-- | s[y↦v]
data (↦) a b = a :> b
infixr 6 ↦

(s << (y :> v)) x = if x == y then v else s x

-- ** Semantic functions

-- *** Arithmetic Semantics

𝓪 ∷ A → State → ℤ
𝓪 (N n) s     = n
𝓪 (V x) s     = s x
𝓪 (a :+: b) s = (𝓪 a s) + (𝓪 b s)
𝓪 (a :⋆: b) s = (𝓪 a s) * (𝓪 b s)
𝓪 (a :-: b) s = (𝓪 a s) - (𝓪 b s)

-- *** Boolean Semantics
𝓫 ∷ B → State → Bool
𝓫 T _           = True
𝓫 F _           = False
𝓫 (a1 :=: a2) s = (𝓪 a1 s) == (𝓪 a2 s)
𝓫 (a1 :≤: a2) s = (𝓪 a1 s) <= (𝓪 a2 s)
𝓫 (Not b) s     = not (𝓫 b s)
𝓫 (b1 :∧: b2) s = (𝓫 b1 s) && (𝓫 b2 s)

-- * Natural Semantics

-- ** Evaluation rules

-- *** \(ass_{ns}\)
s_ns (x :≔: a , s) = (s << (x :> 𝓪 a s)) -- ass_ns
s_ns (Skip, s) = s -- skip_ns
s_ns (c1 :︔: c2 , s) = s'' where --comp_ns
    s' = s_ns (c1,s)
    s'' = s_ns (c2,s')

s_ns (If b c1 c2 , s) = if (𝓫 b s) then s_ns (c1,s) else s_ns (c2,s) -- if_ns

s_ns (While b c , s) = s'' where -- while_ns
    s' = s_ns (c,s)
    s'' = if (𝓫 b s') then s_ns (While b c , s') else s


-- ** Programs

-- | Empty state. Initially the memory is filled with zeros.
es _ = 0

-- *** Swap

{- | SWAP
x ≔ x + y;
y ≔ x - y;
x ≔ x - y
-}

swap_ns s = s_ns (
    "x" :≔: V "x" :+: V "y" :︔:
    "y" :≔: V "x" :-: V "y" :︔:
    "x" :≔: V "x" :-: V "y"
    , s)

{-
>>> swapped = swap_ns (es << ("x" :> 3) << ("y" :> 4))
>>> swapped "x"
>>> swapped "y"
4
3
-}


{- MIN
if x ≤ y ∧ x ≤ z then
    m := x
else if y ≤ z then
    m := y
else
    m := z
-}

min_ns s = s_ns (
 If (V "x" :≤: V "y" :∧: V "x" :≤: V "z")
     ("m" :≔: V "x")
     (If (V "y" :≤: V "z")
         ("m" :≔: V "y")
         ("m" :≔: V "z")
     )
 , s)

-- >>> min_ns (es << ("x" :> 3) << ("y" :> 4) << ("z" :> 5)) "m"
-- 3

{- EXP
r := 1;
while 0 ≤ y do
  r := r ⋆ x;
  y := y - 1
-}

exp_ns s = s_ns (
    "r" :≔: N 1 :︔:
    While (N 0 :≤: V "y")
        (
            "r" :≔: V "r" :⋆: V "x" :︔:
            "y" :≔: V "y" :-: N 1
        )
    , s)

-- >>> exp_ns (es << ("x" :> 3) << ("y" :> 4)) "r"
-- 81

{- FACT
f := 1;
while 1 ≤ n do
  f := f ⋆ n;
  n := n - 1
-}

fact_ns s = s_ns (
    "f" :≔: N 1 :︔:
    While (N 1 :≤: V "n")
        (
            "f" :≔: V "f" :⋆: V "n" :︔:
            "n" :≔: V "n" :-: N 1
        )
    , s )

-- >>> fact_ns (es << ("n" :> 4)) "f"
-- 24





-- Extra
-- Synonyms
tt = True
ff = False

infix 8 :≤:
infix 8 :+:
infix 7 :∧:
infix 7 :≔:
infixl 1 :︔:

-- Not necessary for the language:

sub ∷ A → (Var,A) → A
sub (N n) _            = N n
sub (V x) (y,a0)       = if x == y then a0 else (V x)
sub (a1 :+: a2) (y,a0) = (sub a1 (y,a0)) :+: (sub a2 (y,a0))
sub (a1 :⋆: a2) (y,a0) = (sub a1 (y,a0)) :⋆: (sub a2 (y,a0))
sub (a1 :-: a2) (y,a0) = (sub a1 (y,a0)) :-: (sub a2 (y,a0))

