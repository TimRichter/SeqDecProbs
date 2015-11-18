> module Fraction2

> import NatDivisor
> import NatGCD
> import NatOperations
> import NatProperties
> import Syntax.PreorderReasoning
> import Unique
> import SubsetProperties

> %default total

----------------------------------------------------------------------
Positive natural numbers
----------------------------------------------------------------------

> ||| Define Positivity (any other suitable (unique !) 
> ||| predicate would do)
> |||
> data Positive : Nat -> Type where
>   SuccPos : {n : Nat} -> Positive (S n)

> ||| Positive is a unique predicate
> positiveUnique : {n : Nat} -> Unique (Positive n)
> positiveUnique SuccPos SuccPos = Refl

> ||| Positive natural numbers are closed under multiplication
> multPosPosIsPos : (m, n : Nat) -> 
>                   Positive m -> 
>                   Positive n ->
>                   Positive (m * n)
> multPosPosIsPos Z n SuccPos _       impossible
> multPosPosIsPos m Z _       SuccPos impossible
> multPosPosIsPos (S n) (S m) _ _ = SuccPos

> ||| Define positive natural numbers as the subset
> ||| of those natural numbers that are, surprise ... positive!
> |||
> PosNat : Type
> PosNat = Subset Nat Positive

the first projection gets a short name 
(should invent a short name for getWitness for every subset type, e.g. "el"?)

> nat : PosNat -> Nat
> nat = getWitness

> ||| Since positive is unique, to prove equality in PosNat it 
> ||| suffices to prove equality of the respective nat's
> |||
> eqFromNatEq : (m, n : PosNat) -> (nat m = nat n) -> m = n
> eqFromNatEq m n nmEQnn = 
>   subsetEqLemma1 {A = Nat} {P = Positive} m n nmEQnn positiveUnique

> ||| to make the proofs below independent of the particular
> ||| implementation of PosNat, we give a name to (Element 1 SuccPos):
> ||| (fromInteger: Nat -> PosNat of course can't be defined reasonably) 
> |||
> OnePosNat : PosNat
> OnePosNat = (Element 1 SuccPos)

> ||| the witness of OnePosNat is 1:
>
> onePosNatOne : nat OnePosNat = 1
> onePosNatOne = Refl

> infixl 5 *^

> ||| Multiplication on PosNat 
> 
> (*^) : PosNat -> PosNat -> PosNat
> (Element d dPos) *^ (Element e ePos) = 
>          Element (d * e) (multPosPosIsPos d e dPos ePos)

> ||| is just Nat-multiplication on the elements 
> |||
> multUpIsMult : (d, e: PosNat) -> nat (d *^ e) = nat d * nat e
> multUpIsMult (Element d dPos) (Element e ePos) = Refl
 
> ||| mult on PosNat is commutative
> |||
> multUpCommutative: (d, e : PosNat) -> d *^ e = e *^ d
> multUpCommutative d e = 
>   eqFromNatEq (d *^ e) (e *^ d) pf where
>     pf : nat (d *^ e) = nat (e *^ d)
>     pf = 
>       (nat (d *^ e))  ={ multUpIsMult d e }=
>       (nat d * nat e) ={ multCommutative (nat d) (nat e) }=
>       (nat e * nat d) ={ sym (multUpIsMult e d) }=
>       (nat (e *^ d))  QED  

> ||| mult on PosNat is associative
> |||
> multUpAssoc : (d, e, f : PosNat) -> d *^ (e *^ f) = (d *^ e) *^ f
> multUpAssoc d e f = 
>   eqFromNatEq (d *^ (e *^ f)) ((d *^ e) *^ f) pf where
>     pf : nat (d *^ (e *^ f)) = nat ((d *^ e) *^ f)
>     pf =
>        (nat (d *^ (e *^ f)))     ={ multUpIsMult d (e *^ f)                  }=
>        (nat d * nat (e *^ f))    ={ cong {f = \x => nat d * x} 
>                                                           (multUpIsMult e f) }=
>        (nat d * (nat e * nat f)) ={ multAssociative (nat d) (nat e) (nat f)  }=
>        ((nat d * nat e) * nat f) ={ cong {f = \x => x * nat f}
>                                                     (sym (multUpIsMult d e)) }=
>        (nat (d *^ e) * nat f)    ={ sym (multUpIsMult (d *^ e) f)            }=
>        (nat ((d *^ e) *^ f))     QED

> ||| 1 is right neutral for mult on PosNat
> multUpOneRightNeutral : (d : PosNat) -> d *^ OnePosNat = d
> multUpOneRightNeutral d =
>   eqFromNatEq (d *^ OnePosNat) d pf where
>     pf : nat (d *^ OnePosNat) = nat d
>     pf = 
>       (nat (d *^ OnePosNat))      ={ multUpIsMult d OnePosNat                }=
>       (nat d * nat OnePosNat)     ={ cong {f = \x => nat d * x} onePosNatOne }=
>       (nat d * 1)                 ={ multOneRightNeutral (nat d)             }=
>       (nat d)                     QED

---------------------------------------------------------------------------------
Fractions
---------------------------------------------------------------------------------

> ||| Define Fractions as Pairs of a Nat and a PosNat
> |||
> Fraction : Type
> Fraction = (Nat,PosNat)

Operations and Num instance
---------------------------

> plusFraction : Fraction -> Fraction -> Fraction
> plusFraction (n, d) (m, e) =
>   (n * (nat e) + m * (nat d), d *^ e )

> minusFraction : Fraction -> Fraction -> Fraction
> minusFraction (n, d) (m, e) =
>   (n * (nat e) - m * (nat d), d *^ e)

> multFraction : Fraction -> Fraction -> Fraction
> multFraction (n, d) (m, e) = (n * m, d *^ e)

> fromIntegerFraction : Integer -> Fraction
> fromIntegerFraction i = (fromInteger i, OnePosNat)

> instance Num Fraction where
>   (+) = plusFraction
>   --(-) = minusFraction
>   (*) = multFraction
>   --abs = id
>   fromInteger = fromIntegerFraction

Properties of Fraction operations 1 : those that prove equalities
-----------------------------------------------------------------

> ||| plus on Fractions is commutative
> |||
> plusFCommutative : (x : Fraction) -> (y : Fraction) -> (x + y) = (y + x)
> plusFCommutative (n,d) (m,e) = 
>     ((n, d) + (m, e))
>       ={ cong {f = \k => (k, d *^ e) } 
>          (plusCommutative (n * (nat e)) (m * (nat d))) }=
>     (m * (nat d) + n * (nat e), d *^ e)
>       ={ cong {f = \k => (m * (nat d) + n * (nat e), k)} 
>          (multUpCommutative d e)}=
>     ((m, e) + (n, d))
>       QED

> ||| mult on Fractions is commutative
> |||
> multFCommutative : (x : Fraction) -> (y : Fraction) -> (x * y) = (y * x)
> multFCommutative (n,d) (m,e) =
>     ((n,d) * (m,e))
>       ={ cong {f = \k => (k, d *^ e)} (multCommutative n m) }=
>     (m * n, d *^ e)
>       ={ cong {f = \k => (m * n, k)} (multUpCommutative d e) }=
>     ((m, e) * (n, d))
>       QED

> ||| zero is right neutral for plus on Fractions
> |||
> plusFZeroRightNeutral : (x : Fraction) -> x + (fromInteger 0) = x
> plusFZeroRightNeutral (n, d) = pf where
>   numEq : n * 1 + 0 * (nat d) = n
>   numEq =
>     (n * 1 + 0 * (nat d))  
>       ={ cong {f = \m => n * 1 + m} (multZeroLeftZero (nat d)) }=
>     (n * 1 + 0)
>       ={ plusZeroRightNeutral (n * 1) }=
>     (n * 1)
>       ={ multOneRightNeutral n }=
>     n   
>       QED
>
>   pf =
>     ((n, d) + (0, OnePosNat))               
>       ={ cong {f = \m => (m, d *^ OnePosNat)} numEq }=
>     (n, d *^ OnePosNat)                     
>       ={ cong {f = \m => (n, m)} (multUpOneRightNeutral d) }=
>     (n, d)  
>       QED


> ||| zero is left neutral for plus on Fractions
> |||
> plusFZeroLeftNeutral : (x : Fraction) -> (fromInteger 0) + x = x
> plusFZeroLeftNeutral x = trans  (plusFCommutative (fromInteger 0) x) 
>                             (plusFZeroRightNeutral x)

> ||| plus on Fractions is associative
> |||
> plusFAssociative : (x, y, z : Fraction) -> x + (y + z) = (x + y) + z
> plusFAssociative (n,d) (m,e) (l,f) = pf where
>   multComm' : (a, b, c : Nat) -> a * b * c = a * (c * b)
>   multComm' a b c =
>     (a * b * c)    ={ sym (multAssociative a b c) }=
>     (a * (b * c))  ={ cong {f = \k => a * k} (multCommutative b c) }=
>     (a * (c * b))  QED
>   multComm'' : (a, b, c : Nat) -> a * b * c = a * c * b
>   multComm'' a b c = trans (multComm' a b c) (multAssociative a c b)
>   numEq :  n * nat (e *^ f) + (m * nat f + l * nat e) * nat d = 
>           (n * nat e + m * nat d) * nat f + l * nat (d *^ e)
>   numEq =
>     (n * nat (e *^ f) + (m * nat f + l * nat e) * nat d)
>       ={ cong {f = \k => n * k + (m * nat f + l * nat e) * nat d}
>                                                     (multUpIsMult e f) }=
>     (n * (nat e * nat f) + (m * nat f + l * nat e) * nat d)
>       ={ cong {f = \k => k + (m * nat f + l * nat e) * nat d}
>                                    (multAssociative n (nat e) (nat f)) }=
>     (n * nat e * nat f + (m * nat f + l * nat e) * nat d)
>       ={ cong {f = \k => n * nat e * nat f + k} 
>          (multDistributesOverPlusLeft (m * nat f) (l * nat e) (nat d)) }=
>     (n * nat e * nat f + (m * nat f * nat d + l * nat e * nat d))
>       ={ plusAssociative (n * nat e * nat f) (m * nat f * nat d) 
>                                              (l * nat e * nat d)       }=
>     (n * nat e * nat f + m * nat f * nat d + l * nat e * nat d)
>       ={ cong {f = \k => n * nat e * nat f + k + l * nat e * nat d}
>                                         (multComm'' m (nat f) (nat d)) }=
>     (n * nat e * nat f + m * nat d * nat f + l * nat e * nat d)
>       ={ cong {f = \k => k + l * nat e * nat d} 
>          (sym (multDistributesOverPlusLeft (n * nat e) (m * nat d) 
>                                                              (nat f))) }=
>     ((n * nat e + m * nat d) * nat f + l * nat e * nat d)
>       ={ cong {f = \k => (n * nat e + m * nat d) * nat f + k} 
>                                          (multComm' l (nat e) (nat d)) }=
>     ((n * nat e + m * nat d) * nat f + l * (nat d * nat e))
>       ={ cong {f = \k => (n * nat e + m * nat d) * nat f + l * k} 
>                                       (sym (multUpIsMult d e))         }=
>     ((n * nat e + m * nat d) * nat f + l * nat (d *^ e))
>       QED
>
>   pf =          
>     ((n,d) + ((m,e) + (l,f)))
>       ={ cong {f = \k => (k, d *^ (e *^ f))} numEq                      }= 
>     ((n * nat e + m * nat d) * nat f + l * nat (d *^ e), d *^ (e *^ f))
>       ={ cong {f = \k => ((n * nat e + m * nat d) * nat f + l * nat (d *^ e), k)}
>                                                     (multUpAssoc d e f) }=
>     (((n,d) + (m,e)) + (l,f))
>       QED

> ||| 1 is right neutral for multiplication of Fractions
> |||
> multFOneRightNeutral : (x : Fraction) -> x * 1 = x
> multFOneRightNeutral (n,d) =
>   ((n,d) * (1, OnePosNat))
>     ={ cong {f = \k => (n * 1, k)} (multUpOneRightNeutral d) }= 
>   (n * 1, d)
>     ={ cong {f = \k => (k, d)} (multOneRightNeutral n) }=
>   (n, d)
>     QED

> ||| 1 is left neutral for multiplication of Fractions
>
> multFOneLeftNeutral : (x : Fraction) -> 1 * x = x
> multFOneLeftNeutral x = trans (multFCommutative 1 x) (multFOneRightNeutral x)


Interlude: An equivalence relation
----------------------------------

Rational numbers will be a quotient of Fractions by the relation

> FR : Fraction -> Fraction -> Type
> FR (n,d) (m,e) = n * (nat e) = m * (nat d)

> syntax  [x] "~" [y] = FR x y

which is an equivalence relation

> reflexiveFR : (x : Fraction) -> x ~ x
> reflexiveFR (n,d) = Refl

> reflexiveFR' : (x, y : Fraction) -> x = y -> x ~ y
> reflexiveFR' x x Refl = reflexiveFR x

> symmetricFR : (x, y : Fraction) -> (x ~ y) -> (y ~ x)
> symmetricFR (n,d) (m,e) ndFRme = sym ndFRme

For transitivity we need that multiplication by a positive number is
injective (should follow more or less immediately from 
NatProperties.multMultElimLeft)


see NatProperties.multMultElimLeft

> multPositiveLeftInjective : (m, n : Nat) -> (d : PosNat) -> (nat d) * m = (nat d) * n -> m = n
> multPositiveLeftInjective m n (Element d dPos) dmEQdn = 
>     multMultElimLeft d d m n Refl dNotZ dmEQdn where
>       positiveIsNotZ : (k : Nat) -> Positive k -> Not (k = Z)
>       positiveIsNotZ Z SuccPos _ impossible
>       positiveIsNotZ (S k) _  skEQZ = ZnotS (sym skEQZ)
>       dNotZ : Not (d = Z)
>       dNotZ = positiveIsNotZ d dPos


> transitiveFR : (x, y, z : Fraction) -> (x ~ y) -> (y ~ z) -> (x ~ z)
> transitiveFR (n,d) (m,e) (l,f) neIsmd mfIsle = 
>   multPositiveLeftInjective (n * (nat f)) (l * (nat d)) e pf where
>   pf : nat e * (n * nat f) = nat e * (l * (nat d))
>   pf =
>     (nat e * (n * nat f))
>     ={ multAssociative (nat e) n (nat f) }=
>     (nat e * n * nat f)
>     ={ cong {f = \k => k * nat f} (multCommutative (nat e) n) }=
>     (n * nat e * nat f)
>     ={ cong {f = \k => k * nat f} neIsmd }=
>     (m * nat d * nat f)
>     ={ sym (multAssociative m (nat d) (nat f)) }=
>     (m * (nat d * nat f))
>     ={ cong {f =\k => m * k} (multCommutative (nat d) (nat f)) }=
>     (m * (nat f * nat d))
>     ={ multAssociative m (nat f) (nat d) }=
>     (m * nat f * nat d)
>     ={ cong {f =\k => k * nat d} mfIsle }=
>     (l * nat e * nat d)
>     ={ cong {f = \k => k * nat d} (multCommutative l (nat e))}=
>     (nat e * l * nat d)
>     ={ sym (multAssociative (nat e) l (nat d)) }=
>     (nat e * (l * (nat d)))
>     QED

Properties of Fraction operations 2: those that only prove equivalences w.r.t. ~
--------------------------------------------------------------------------------

> ||| Multiplying any Fraction with 0 on the right gives a 
> ||| Fraction equivalent to 0
> |||
> multFZeroRightZero : (x : Fraction) -> (x * 0) ~ 0
> multFZeroRightZero (n,d) =
>     (n * 0 * 1)
>     ={ cong {f = \k => k * 1} (multZeroRightZero n) }=
>     (0 * 1)
>     ={ multZeroLeftZero 1 }=
>     0
>     ={ sym (multZeroLeftZero (nat (d *^ OnePosNat))) }=
>     (0 * nat (d *^ OnePosNat))
>     QED

> ||| Multiplying any Fraction with 0 on the left gives a 
> ||| Fraction equivalent to 0
> |||
> multFZeroLeftZero : (x : Fraction) -> (0 * x) ~ 0
> multFZeroLeftZero x = 
>   transitiveFR (0 * x) (x * 0) 0 pf (multFZeroRightZero x) where
>     pf : (0 * x) ~ (x * 0)
>     pf = reflexiveFR' (0 * x) (x * 0) (multFCommutative 0 x)

> ||| Distributivity (+ on the right) for Fractions up to equivalence
> |||
> multFDistributesOverPlusRight : (x,y,z : Fraction) -> 
>                                 (x * (y + z)) ~ ((x * y) + (x * z))
>
> multFDistributesOverPlusRight (n,d) (m,e) (l,f) = pf where
>   pf1 : nat (d *^ e) * nat (d *^ f) = nat d * nat (d *^ (e *^ f))
>   pf1 =
>     (nat (d *^ e) * nat (d *^ f))
>       ={ cong {f = \x => x * nat (d *^ f)} (multUpIsMult d e) }=
>     ((nat d * nat e) * nat (d *^ f))
>       ={ cong {f = \x => (nat d * nat e) * x} (multUpIsMult d f) }=
>     ((nat d * nat e) * (nat d * nat f))
>       ={ sym (multAssociative (nat d) (nat e) (nat d * nat f)) }=
>     (nat d * (nat e * (nat d * nat f)))
>       ={ cong {f = \k => nat d * k} (multAssociative (nat e) (nat d) (nat f)) }=
>     (nat d * (nat e * nat d * nat f))
>       ={ cong {f = \k => nat d * ( k * nat f)} (multCommutative (nat e) (nat d)) }=
>     (nat d * (nat d * nat e * nat f))
>       ={ cong {f = \k => nat d * k} (sym (multAssociative (nat d) (nat e) (nat f))) }=
>     (nat d * (nat d * (nat e * nat f)))
>       ={ cong {f = \x => nat d * (nat d * x)} (sym (multUpIsMult e f)) }=
>     (nat d * (nat d * nat ( e *^ f)))
>       ={ cong {f = \x => nat d * x} (sym (multUpIsMult d (e *^ f))) }=
>     (nat d * nat (d *^ (e *^ f)))
>       QED
>   pf2' : (w,x : Nat) -> (y,z : PosNat) -> w * (x * nat y) * nat z = w * x * nat (z *^ y)
>   pf2' w x y z =
>     (w * (x * nat y) * nat z)
>       ={ cong {f = \k => k * nat z} (multAssociative w x (nat y)) }=
>     (w * x * nat y * nat z)
>       ={ sym (multAssociative (w * x) (nat y) (nat z)) }=
>     (w * x * (nat y * nat z))
>       ={ cong {f = \k => w * x * k} (sym (multUpIsMult y z)) }=
>     (w * x * nat (y *^ z))
>       ={ cong {f =  \k => w * x * nat k} (multUpCommutative y z) }=
>     (w * x * nat (z *^ y))
>       QED
>   pf2 : (n * (m * nat f) + n * (l * nat e)) * nat d =
>         n * m * nat (d *^ f) + n * l * nat (d *^ e)
>   pf2 =
>     ((n * (m * nat f) + n * (l * nat e)) * nat d)
>       ={ multDistributesOverPlusLeft _ _ _ }=
>     (n * (m * nat f) * nat d + n * (l * nat e) * nat d)
>       ={ cong {f = \k => n * (m * nat f) * nat d + k} (pf2' n l e d)}=
>     (n * (m * nat f) * nat d + n * l * nat (d *^ e))
>       ={ cong {f = \k => k + n * l * nat (d *^ e)} (pf2' n m f d) }=
>     (n * m * nat (d *^ f) + n * l * nat (d *^ e))
>       QED
>   pf =
>     (n * (m * nat f + l * nat e) * nat ((d *^ e) *^ (d *^ f)))
>       ={ cong {f = \k => n * (m * nat f + l * nat e) * k}
>                                          (multUpIsMult (d *^ e) (d *^ f)) }=
>     (n * (m * nat f + l * nat e) * (nat (d *^ e) * (nat (d *^ f))))
>       ={ cong {f = \k => k * (nat (d *^ e) * nat (d *^ f)) } 
>                  (multDistributesOverPlusRight n (m * nat f) (l * nat e)) }=
>     ((n * (m * nat f) + n * (l * nat e)) * (nat (d *^ e) * nat (d *^ f))) 
>       ={ cong {f = \k => (n * (m * nat f) + n * (l * nat e)) * k} pf1     }=
>     ((n * (m * nat f) + n * (l * nat e)) * (nat d * nat (d *^ (e *^ f))))
>       ={ (multAssociative (n * (m * nat f) + n * (l * nat e)) (nat d) _ ) }=
>     ((n * (m * nat f) + n * (l * nat e)) * nat d * nat (d *^ (e *^ f)))
>       ={ cong {f = \k => k * nat (d *^ (e *^ f))} pf2                     }=
>     ((n * m * nat (d *^ f) + n * l * nat (d *^ e)) * nat (d *^ (e *^ f)))
>       QED


> ||| Distributivity (+ on the left) for Fractions up to equivalence
> |||
> multFDistributesOverPlusLeft :  (x,y,z : Fraction) -> 
>                                 ((x + y) * z) ~ ((x * z) + (y * z))
>
> multFDistributesOverPlusLeft x y z = 
>   transitiveFR ((x + y) * z) (z * x + z * y) (x * z + y * z) 
>     (transitiveFR ((x + y) * z) (z * (x + y)) (z * x + z * y)     
>       (reflexiveFR' ((x + y) * z) (z * (x + y)) (multFCommutative (x + y) z)) 
>       (multFDistributesOverPlusRight z x y))
>     (reflexiveFR' (z * x + z * y) (x * z + y * z) pf) where
>   pf : z * x + z * y = x * z + y * z
>   pf =
>     (z * x + z * y)
>     ={ cong {f = \k => z * x + k} (multFCommutative z y) }=
>     (z * x + y * z)
>     ={ cong {f = \k => k + y * z} (multFCommutative z x) }=
>     (x * z + y * z)
>     QED
   
prove that fraction plus and mult operations are ~ - invariant

> plusInvariant : (x, x' : Fraction) -> (x ~ x') -> 
>                 (y, y' : Fraction) -> (y ~ y') ->
>                 (x + y) ~ (x' + y')
> plusInvariant (n, Element d _) (n', Element d' _) nd'EQn'd
>               (m, Element e _) (m', Element e' _) me'EQm'e = pf where
>   helper : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * c) * (b * d)
>   helper a b c d =
>     ((a * b) * (c * d))  ={ sym (multAssociative a b (c * d))                    }=
>     (a * (b * (c * d)))  ={ cong {f = \x => a * x} (multAssociative b c d)       }=
>     (a * ((b * c) * d))  ={ cong {f = \x => a * (x * d)} (multCommutative b c)   }=
>     (a * ((c * b) * d))  ={ cong {f = \x => a * x} (sym (multAssociative c b d)) }=
>     (a * (c * (b * d)))  ={ multAssociative a c (b * d)                          }=
>     ((a * c) * (b * d))  QED
>   helper2 : (a, b, c, d, a', c' : Nat) -> (a * c = a' * c') ->
>             ((a * b) * (c * d)) = ((a' * d) * (c' * b))
>   helper2 a b c d a' c' acEQa'c' =
>     ((a * b) * (c * d))   ={ helper a b c d }=
>     ((a * c) * (b * d))   ={ cong {f = \x => x * (b * d)} acEQa'c' }=
>     ((a' * c') * (b * d)) ={ cong {f = \x => (a' * c') * x} (multCommutative b d) }=
>     ((a' * c') * (d * b)) ={ helper a' c' d b }=
>     ((a' * d) * (c' * b)) QED 
>   pf : ((n * e) + (m * d)) * (d' * e') = ((n' * e') + (m' * d')) * (d * e)
>   pf = 
>     (((n * e) + (m * d)) * (d' * e')) 
>       ={ multDistributesOverPlusLeft (n * e) (m * d) (d' * e') }=
>     (((n * e) * (d' * e')) + ((m * d) * (d' * e')))
>       ={ cong {f = \x => x + ((m * d) * (d' * e'))} (helper2 n e d' e' n' d nd'EQn'd) }=
>     (((n' * e') * (d * e)) + ((m * d) * (d' * e')))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + ((m * d) * x)} (multCommutative d' e') }=
>     (((n' * e') * (d * e)) + ((m * d) * (e' * d')))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + x} (helper2 m d e' d' m' e me'EQm'e) }=
>     (((n' * e') * (d * e)) + ((m' * d') * (e * d)))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + ((m' * d') * x)} (multCommutative e d) }=
>     (((n' * e') * (d * e)) + ((m' * d') * (d * e)))
>       ={ sym (multDistributesOverPlusLeft (n' * e') (m' * d') (d * e)) }=
>     (((n' * e') + (m' * d')) * (d * e))
>       QED


> multInvariant : (x, x' : Fraction) -> (x ~ x') -> 
>                 (y, y' : Fraction) -> (y ~ y') ->
>                 (x * y) ~ (x' * y')
> multInvariant (n, Element d _) (n', Element d' _) nd'EQn'd
>               (m, Element e _) (m', Element e' _) me'EQm'e = pf where
>   helper : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * c) * (b * d)
>   helper a b c d =
>     ((a * b) * (c * d))  ={ sym (multAssociative a b (c * d))                    }=
>     (a * (b * (c * d)))  ={ cong {f = \x => a * x} (multAssociative b c d)       }=
>     (a * ((b * c) * d))  ={ cong {f = \x => a * (x * d)} (multCommutative b c)   }=
>     (a * ((c * b) * d))  ={ cong {f = \x => a * x} (sym (multAssociative c b d)) }=
>     (a * (c * (b * d)))  ={ multAssociative a c (b * d)                          }=
>     ((a * c) * (b * d))  QED
>   pf : (n * m) * (d' * e') = (n' * m') * (d * e)
>   pf = 
>     ((n * m) * (d' * e')) ={ helper n m d' e' }=
>     ((n * d') * (m * e')) ={ cong {f = \x => x * (m * e')} nd'EQn'd }=
>     ((n' * d) * (m * e')) ={ cong {f = \x => (n' * d) * x} me'EQm'e }=
>     ((n' * d) * (m' * e)) ={ helper n' d m' e }=
>     ((n' * m') * (d * e)) QED




