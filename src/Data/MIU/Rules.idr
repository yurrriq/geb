module Data.MIU.Rules


import Data.MIU.Types
import Data.MIU.Views


%access export


ruleI : (str : MIU.Types.String (S k)) ->
        Maybe (MIU.Types.String (S k + 1))
ruleI (Str xs {ok}) =
    case last xs of
        I => pure (Str (xs ++ [U]) {ok = appendNonEmpty ok {ys=[U]}})
        _ => Nothing


ruleII : MIU.Types.String n ->
         MIU.Types.String (n + n)
ruleII (Str xs {ok}) = Str (xs ++ xs) {ok = appendNonEmpty ok}
