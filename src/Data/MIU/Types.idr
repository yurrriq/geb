module Data.MIU.Types

import public Data.Vect
import public Data.MIU.Views


%access public export


data Letter = M | I | U


implementation Eq Letter where
    M == M = True
    I == I = True
    U == U = True
    _ == _ = False


implementation Show Letter where
    show M = "M"
    show I = "I"
    show U = "U"


implementation Uninhabited (I = M) where
    uninhabited = \Refl impossible


implementation Uninhabited (U = M) where
    uninhabited = \Refl impossible


data String : Nat -> Type where
    Str : (xs : Vect n Letter) ->
          {auto ok : NonEmpty xs} ->
          MIU.Types.String n


implementation Eq (MIU.Types.String n) where
  (Str xs) == (Str ys) = xs == ys


implementation Show (MIU.Types.String xs) where
    show (Str xs) = concatMap show (M :: xs)
