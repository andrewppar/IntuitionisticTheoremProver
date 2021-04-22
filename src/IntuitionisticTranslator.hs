module IntuitionisticTranslator (intuitionisticTranslate) where

import Data.Maybe
import Formula

intuitionisticTranslate :: Formula -> Maybe Formula
intuitionisticTranslate formula =
  if doubleNegationP formula
    then Just formula
    else intuitionisticTranslateInternal . simplifyContradictions $ formula

intuitionisticTranslateInternal :: Formula -> Maybe Formula
intuitionisticTranslateInternal f@(AtomicFormula _) = Just (Necessarily f)
intuitionisticTranslateInternal (And fs) = translateJunction "And" fs
intuitionisticTranslateInternal (Or fs) = translateJunction "Or" fs
intuitionisticTranslateInternal (Implies ant cons) =
  Just (Necessarily (Implies (Data.Maybe.fromJust (intuitionisticTranslateInternal ant)) (Data.Maybe.fromJust (intuitionisticTranslateInternal cons))))
intuitionisticTranslateInternal (Equivalent one two) =
  let maybeOne = Data.Maybe.fromJust . intuitionisticTranslateInternal $ one
      maybeTwo = Data.Maybe.fromJust . intuitionisticTranslateInternal $ two
   in if maybeOne == maybeTwo
        then Just (Necessarily (Implies (AtomicFormula "p") (AtomicFormula "p")))
        else
          Just
            ( And
                [ Necessarily (Implies maybeOne maybeTwo),
                  Necessarily (Implies maybeTwo maybeOne)
                ]
            )
intuitionisticTranslateInternal (Not f) =
  Just (Necessarily (Not (Data.Maybe.fromJust (intuitionisticTranslateInternal f))))
intuitionisticTranslateInternal (Possibly _) = Nothing
intuitionisticTranslateInternal (Necessarily _) = Nothing

simplifyContradictions :: Formula -> Formula
simplifyContradictions (AtomicFormula p) = AtomicFormula p
simplifyContradictions (Not p) = Not . simplifyContradictions $ p
simplifyContradictions (And ps) = And . map simplifyContradictions $ ps
simplifyContradictions (Or ps) = Or . map simplifyContradictions $ ps
simplifyContradictions (Equivalent p q) =
  if negationOfP p q
    then And . map simplifyContradictions $ [p, q]
    else Equivalent (simplifyContradictions p) (simplifyContradictions q)
simplifyContradictions (Implies p q) =
  Implies (simplifyContradictions p) (simplifyContradictions q)

translateJunction :: String -> [Formula] -> Maybe Formula
translateJunction junctionType fs =
  let possiblyTranslated = map intuitionisticTranslateInternal fs
   in if (filter (\x -> x == Nothing) possiblyTranslated) == []
        then case junctionType of --TODO Replace these strings with some other type
          "Or" -> Just (Or (map Data.Maybe.fromJust possiblyTranslated))
          "And" -> Just (And (map Data.Maybe.fromJust possiblyTranslated))
          otherwise -> Nothing
        else Nothing
