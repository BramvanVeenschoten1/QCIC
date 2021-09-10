module function

id : Pi {0 a : Type}, a -> a
id x = x

the : Pi (0 a : Type), a -> a
the a x = x

typeOf : Pi {0 a : Type}, a -> Type
typeOf x = a

const : Pi {0 a b : Type}, a -> b -> a
const x y = x

comp : Pi {0 a b c : Type}, (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

flip : Pi {0 a b c : Type}, (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

join : Pi {0 a b : Type}, (a -> a -> b) -> a -> b
join f x = f x x

ap : Pi {0 a b c : Type}, (a -> b -> c) -> (a -> b) -> a -> c
ap f g x = f x (g x)

on : Pi {0 a b c : Type}, (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)

