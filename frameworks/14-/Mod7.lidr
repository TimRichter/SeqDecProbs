> module Mod7

> import SplitQuotient as SQ
> import Syntax.PreorderReasoning

 %default total

> n : Integer
> n = 7

> SQ.Base = Integer
> SQ.Relation x y = (Prelude.Classes.modBigInt x Mod7.n) = (Prelude.Classes.modBigInt y Mod7.n)
> SQ.normalize x = Prelude.Classes.modBigInt x Mod7.n

> f : Int -> Int
> f x = mod x 7 

> rel : Int -> Int -> Type
> rel x y = f x = f y

> test : (x, y : Int) -> rel x y -> f x = f y
> test x y xRely = xRely

 SQ.normalizeMapsRelatedToEQ x y xRely = xRely

 SQ.normalizeIsRelated x = really_believe_me x


 Modn : Type
 Modn = SQ.Quot

 allValues : List Modn
 allValues = map fromInteger [0..(n-1)]

testing computations mod n

 square : Modn -> Modn
 square x = x * x



