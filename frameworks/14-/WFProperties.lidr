> module WFProperties

> import Control.WellFounded

> %default total

> relInvIm : (a -> b) -> (b -> b -> Type) -> (a -> a -> Type)
> relInvIm f r x y = r (f x) (f y)

doesn't work:

 instance WellFounded r => WellFounded (relInvIm f r) where
   wellFounded = ?lala
 

