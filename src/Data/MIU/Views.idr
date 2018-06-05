module Data.MIU.Views


import public Data.Vect


%access public export


data NonEmpty : (xs : Vect n a) -> Type where
    IsNonEmpty : MIU.Views.NonEmpty (x :: xs)


implementation Uninhabited (MIU.Views.NonEmpty []) where
    uninhabited _ impossible


%access export


appendNonEmpty : MIU.Views.NonEmpty xs ->
                 {ys : Vect n a} ->
                 MIU.Views.NonEmpty (xs ++ ys)
appendNonEmpty _ {xs = x::xs} {ys} = IsNonEmpty {x = x} {xs = xs ++ ys}
