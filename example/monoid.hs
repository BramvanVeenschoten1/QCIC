module monoid

import function
       prelude
       
associative : Pi {0 a : Type}, (a -> a -> a) -> Type
associative f = Pi (x y z : a), eq (f x (f y z)) (f (f x y) z)

data semigroup (a : Type): Type where
  mk : Pi (sappend : a -> a -> a)
          (sappend_associative : associative sappend),
          semigroup a

sappend : Pi {0 a : Type}, semigroup a -> a -> a -> a
sappend (mk x _) = x

sappend_associative : Pi {0 a : Type}(x : semigroup a), associative (sappend x)
sappend_associative (mk _ x) = x

data monoid (a : Type): Type where
  mk : Pi (mempty : a)
          (mappend : a -> a -> a)
          (left_id  : Pi x : a, eq x (mappend x mempty))
          (right_id : Pi x : a, eq x (mappend mempty x))
          (mappend_assoc : associative mappend),
          monoid a

mempty : Pi {0 a : Type}, monoid a -> a
mempty (mk x _ _ _ _) = x

mappend : Pi {0 a : Type}, monoid a -> a -> a -> a
mappend (mk _ x _ _ _) = x

left_id : Pi {0 a : Type}(mon : monoid a)(x : a), eq x (mappend mon x (mempty mon))
left_id (mk _ _ x _ _) = x

right_id : Pi {0 a : Type}(mon : monoid a)(x : a), eq x (mappend mon (mempty mon) x)
right_id (mk _ _ _ x _) = x

mappend_associative : Pi {0 a : Type}(mon : monoid a), associative (mappend mon)
mappend_associative (mk _ _ _ _ x) = x

commutative : Pi {0 a : Type}, (a -> a -> a) -> Type
commutative f = Pi (x y : a), eq (f x y) (f y x)
