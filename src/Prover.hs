module Prover
  (ProofTreeStatus(..)
  , prove
  , ProofTree(..)
  , ResolutionModule(..)
  , PositiveReflexivity(..)
  , showProof)
    where


import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent
import Model
import IntuitionisticTranslator
import Data.Maybe
data ProofTree = Closed | Open | Node Hypersequent [ProofTree] deriving (Eq)

data ProofTreeStatus = Proved | CounterExample  | Unknown deriving (Eq, Show)

instance Show ProofTree where
  show = showProofTree 0

showProofTree :: Int -> ProofTree -> String
showProofTree n Closed =
  let prefix = foldr (\x acc -> x ++ acc) [] . take  n . repeat $ "  "
   in prefix ++ "X" ++ "\n"
showProofTree n Open =
  let prefix = foldr (\x acc -> x ++ acc) [] . take  n . repeat $ "  "
   in prefix ++ "O" ++ "\n"
showProofTree n (Node hypersequent prooftree) =
  let depth = foldr (\x acc -> x ++ acc) [] . take n . repeat $ "*"
      hyper = (showHypersequent True 0 (n + 1) hypersequent)
      recursiveCase = foldr (\x acc -> (showProofTree (n + 1) x) ++ acc) [] prooftree
   in depth ++ " " ++ hyper ++ recursiveCase


--serializeProofTree :: ProofTree -> Serialization -> String
--serializeProofTree

gatherOpenNodes :: ProofTree -> [Hypersequent]
gatherOpenNodes Open = []
gatherOpenNodes Closed = []
gatherOpenNodes (Node hypersequent [Open]) = [hypersequent]
gatherOpenNodes (Node hyper hypers) =
  foldr (\h acc -> (gatherOpenNodes h) ++ acc) [] hypers

extendProofTreeWithClosings :: ProofTree -> [ProofTree] -> ProofTree
extendProofTreeWithClosings Open _ = Open
extendProofTreeWithClosings Closed _ = Closed
extendProofTreeWithClosings tree@(Node _ [Open]) [] = tree
extendProofTreeWithClosings tree@(Node hypersequent [Open]) (proofTree:proofTrees) =
  let (Node root trees) = proofTree
   in if root == hypersequent
      then Node hypersequent trees
      else extendProofTreeWithClosings tree proofTrees
extendProofTreeWithClosings (Node hypersequent trees) potentialClosings =
  Node hypersequent (map (`extendProofTreeWithClosings` potentialClosings) trees)

prove :: Formula -> ProofTreeStatus
prove = fst . proveInternal

showProof :: Formula -> Either ProofTree Model
showProof form =
  let (status, tree) = proveInternal $ form
   in case status of
     Proved -> Left tree
     -- TODO: have proveInternal return a proofObject instead of a tree
     CounterExample ->
       Right .
       fromJust  .
       getCounterExample (canonicalizeFormula (fromJust (intuitionisticTranslate form))) .
       gatherOpenNodes $ tree
     Unknown -> Left tree

proveInternal :: Formula -> (ProofTreeStatus, ProofTree)
proveInternal form =
  let (proofTree, canonicalFormula) = generateStartingProofTree form
   in generateProofTree 0 canonicalFormula (Unknown, proofTree)


generateStartingProofTree  :: Formula -> (ProofTree, Formula)
generateStartingProofTree formula =
  let canonicalFormula =
        canonicalizeFormula . fromJust . intuitionisticTranslate $ formula
      sequent = makeSequent [] [canonicalFormula]
      hypersequent = World sequent []
   in ((Node hypersequent [Open]), canonicalFormula)

proofTreeRecursionLimit :: Int
proofTreeRecursionLimit = 15

generateProofTree :: Int -> Formula -> (ProofTreeStatus , ProofTree) -> (ProofTreeStatus, ProofTree)
generateProofTree depth originalFormula (status, tree)
  | status /= Unknown = (status, tree)
  | checkTreeClosed tree = (Proved, tree)
  | foundCounterExample originalFormula tree = (CounterExample, tree)
  | depth == proofTreeRecursionLimit = (Unknown, tree)
  | otherwise = let newTree =
                     treeRemoveDuplicates .
                     applyResolutionModules .
                     applyUniversalModalRules .
                     applyPropositionalRules .
                     applyParticularModalRules $ tree
                    --potentiallyNewerTree =
                    --  if newTree == tree
                    --     then applyUniversalModalRules  tree
                    --     else newTree
                    newDepth = depth + 1
                 in generateProofTree newDepth originalFormula (Unknown, newTree)

checkTreeClosed :: ProofTree -> Bool
checkTreeClosed Closed = True
checkTreeClosed Open = False
checkTreeClosed (Node hypersequent trees) =
  let openTrees = filter (\bool -> bool /= True) . map checkTreeClosed $ trees
   in openTrees == []

foundCounterExample :: Formula -> ProofTree -> Bool
foundCounterExample originalFormula tree =
  let openNodes  = gatherOpenNodes tree
      satisfieds = map (hypersequentSatisfies  (Not originalFormula)) openNodes
   in some (\bool -> bool == True) satisfieds

applyPropositionalRules :: ProofTree -> ProofTree
applyPropositionalRules Closed = Closed
applyPropositionalRules Open = Open
applyPropositionalRules (Node hypersequent [Open]) =
  let rootHypersequent = applyLeftNegation  .
                           applyRightNegation .
                           applyLeftConjunction .
                           applyRightDisjunction $ hypersequent
      hypersequents = mapAppend applyHypersequentRightConjunction .
                     applyHypersequentLeftDisjunction $ rootHypersequent
      newBranches = map (\hyper -> if hypersequentClosed hyper
                                      then Node hyper [Closed]
                                   else Node hyper [Open]) hypersequents
   in Node hypersequent (if newBranches == [] then [Open] else newBranches)
applyPropositionalRules (Node hypersequent hypersequents) =
  let recursiveCase  = map applyPropositionalRules hypersequents
   in (Node hypersequent recursiveCase)

applyLeftNegation :: Hypersequent -> Hypersequent
applyLeftNegation = applyNegation Negative

applyRightNegation :: Hypersequent -> Hypersequent
applyRightNegation = applyNegation Positive

applyNegation :: Polarity -> Hypersequent -> Hypersequent
applyNegation polarity (World seq hypersequents) =
  let transformedSequent =
        case polarity of
          Positive -> applySequentRightNegation seq
          Negative -> applySequentLeftNegation seq
      recursiveCase = map  (applyNegation polarity) hypersequents
   in World transformedSequent recursiveCase

applySequentLeftNegation :: Sequent -> Sequent
applySequentLeftNegation = applySequentNegation Negative

applySequentRightNegation :: Sequent -> Sequent
applySequentRightNegation = applySequentNegation Positive

applySequentNegation :: Polarity -> Sequent -> Sequent
applySequentNegation polarity sequent =
  let gatherFunction =
        case polarity of
          Positive ->  posFormulas
          Negative ->  negFormulas
      preserveFunction =
        case polarity of
          Positive -> negFormulas
          Negative -> posFormulas
      (relevantFormulas, irrelevantFormulas) =
        gatherNegations . gatherFunction $ sequent
      transformedFormulas = map negatum relevantFormulas
      untouchedFormulas = preserveFunction sequent
      resultFormulas = untouchedFormulas ++  transformedFormulas
   in case polarity of
     Positive ->
       makeSequent resultFormulas irrelevantFormulas
     Negative ->
       makeSequent  irrelevantFormulas resultFormulas

applyLeftConjunction :: Hypersequent -> Hypersequent
applyLeftConjunction = applySimpleJunction applyLeftSequentConjunction

applyLeftSequentConjunction :: Sequent ->  Sequent
applyLeftSequentConjunction = applySimpleSequentJunction Negative

applyRightDisjunction :: Hypersequent -> Hypersequent
applyRightDisjunction = applySimpleJunction applyRightSequentDisjunction

applyRightSequentDisjunction :: Sequent -> Sequent
applyRightSequentDisjunction = applySimpleSequentJunction Positive

applySimpleJunction :: (Sequent -> Sequent) -> Hypersequent -> Hypersequent
applySimpleJunction sequentRule  (World seq hypersequents) =
  let transformedSequent = sequentRule seq
      recursive = (map (applySimpleJunction sequentRule) hypersequents)
   in World transformedSequent recursive

applySimpleSequentJunction :: Polarity -> Sequent  -> Sequent
applySimpleSequentJunction polarity (Sequent negs poss) =
  let subformulaFunction =
         case polarity of
           Positive -> disjuncts
           Negative -> conjuncts
      (relevant, irrelevant) = (case polarity of
                                  Positive -> (gatherDisjunctions poss)
                                  Negative -> (gatherConjunctions negs))
      subformulas = mapAppend subformulaFunction relevant
   in case polarity of
     Positive -> (Sequent negs (irrelevant ++ subformulas))
     Negative -> (Sequent (irrelevant ++ subformulas) poss)

applyHypersequentRightConjunction :: Hypersequent -> [Hypersequent]
applyHypersequentRightConjunction = applyHypersequentComplexJunction applySequentRightConjunction

applyHypersequentLeftDisjunction :: Hypersequent -> [Hypersequent]
applyHypersequentLeftDisjunction = applyHypersequentComplexJunction applySequentLeftDisjunction

applyHypersequentComplexJunction :: (Sequent -> [Sequent]) -> Hypersequent -> [Hypersequent]
applyHypersequentComplexJunction sequentFunction (World seq  hypers) =
  let seqs = sequentFunction seq
      recursiveCase  =
        cartesianProduct . map (applyHypersequentComplexJunction sequentFunction ) $ hypers
--- This is too similar to the cartesian product code not to have
-- an  abstraction
--  TODO: Create that abstraction
   in if emptyListP recursiveCase
         then map (\sequent -> (World sequent [])) seqs
      else foldr (\seq result ->
        let intermediateResult =
              foldr (\hypersequentList acc ->
                (World seq hypersequentList): acc) [] recursiveCase
         in intermediateResult ++ result) [] seqs

applySequentRightConjunction :: Sequent  -> [Sequent]
applySequentRightConjunction = applySequentComplexJunction Positive

applySequentLeftDisjunction :: Sequent -> [Sequent]
applySequentLeftDisjunction = applySequentComplexJunction Negative

applySequentComplexJunction :: Polarity -> Sequent -> [Sequent]
applySequentComplexJunction polarity (Sequent negs poss) =
  let subformulaFunc =
         case polarity of
           Positive -> conjuncts
           Negative -> disjuncts
      gatherFunc =
        case polarity of
          Positive -> gatherConjunctions
          Negative -> gatherDisjunctions
      importantFormulas =
        case polarity of
          Positive -> poss
          Negative -> negs
      (relevant, irrelevant) = gatherFunc importantFormulas
      newRelevants = cartesianProduct . map  subformulaFunc $ relevant
   in if emptyListP relevant
         then [Sequent negs poss]
      else map (\forms ->
                  case polarity of
                    Positive -> Sequent negs (forms ++ irrelevant)
                    Negative -> Sequent (forms ++ irrelevant) poss) newRelevants

applyParticularModalRules :: ProofTree -> ProofTree
applyParticularModalRules = applyRightNecessity .  applyLeftPossibility

applyUniversalModalRules  :: ProofTree -> ProofTree
applyUniversalModalRules = applyRightPossibility .  applyLeftNecessity

data Universality = Universal | Particular


applyRightNecessity :: ProofTree ->  ProofTree
applyRightNecessity = applyModality Particular Positive

applyLeftPossibility :: ProofTree -> ProofTree
applyLeftPossibility = applyModality Particular Negative

applyRightPossibility :: ProofTree -> ProofTree
applyRightPossibility = applyModality Universal Positive

applyLeftNecessity :: ProofTree -> ProofTree
applyLeftNecessity = applyModality Universal Negative

applyModality :: Universality -> Polarity -> ProofTree -> ProofTree
applyModality _ _ Closed = Closed
applyModality _ _ Open = Open
applyModality universality polarity  (Node hypersequent [Open]) =
  let newHypersequent =
       case (universality, polarity) of
         (Particular, Positive) -> applyHypersequentRightNecessity hypersequent
         (Particular, Negative) -> applyHypersequentLeftPossibility hypersequent
         (Universal, Positive) -> applyHypersequentRightPossibility hypersequent
         (Universal, Negative) -> applyHypersequentLeftNecessity hypersequent
   in if hypersequentClosed newHypersequent
         then Node hypersequent [(Node newHypersequent [Closed])]
      else if hypersequent == newHypersequent
              then (Node hypersequent [Open])
           else Node hypersequent [(Node newHypersequent [Open])]
applyModality universality polarity (Node hypersequent branches) =
  (Node hypersequent (map (applyModality universality polarity) branches))

applyHypersequentLeftPossibility :: Hypersequent -> Hypersequent
applyHypersequentLeftPossibility =
  applyHypersequentExistentialModality Negative

applyHypersequentRightNecessity :: Hypersequent -> Hypersequent
applyHypersequentRightNecessity =
  applyHypersequentExistentialModality Positive

applyHypersequentExistentialModality :: Polarity -> Hypersequent -> Hypersequent
applyHypersequentExistentialModality polarity (World seq hypers) =
  --TODO: The first part of this and applyHypersequentUniversalModality are the same. We should abstract out a gather/begin function
  let gatherFunc =
        case polarity of
          Positive -> gatherNecessities . posFormulas
          Negative -> gatherPossibilities . negFormulas
      (relevant, irrelevant) = gatherFunc seq
      newFormulas =
         case polarity of
           Positive -> map necessity relevant
           Negative -> map possibility relevant
      newSequents =
         case polarity of
           Positive -> map (\form -> makeSequent [] [form]) newFormulas
           Negative -> map (\form -> makeSequent [form] []) newFormulas
      newHypers = map (\seq -> World seq []) newSequents
      originalSeq =
         case polarity of
           Positive -> makeSequent (negFormulas seq) irrelevant
           Negative -> makeSequent irrelevant (posFormulas seq)
      resultHypers =
        map (applyHypersequentExistentialModality polarity) (newHypers ++ hypers)
   in (World originalSeq resultHypers)

applyHypersequentRightPossibility :: Hypersequent -> Hypersequent
applyHypersequentRightPossibility =  applyHypersequentUniversalModality Positive

applyHypersequentLeftNecessity :: Hypersequent -> Hypersequent
applyHypersequentLeftNecessity = applyHypersequentUniversalModality Negative

applyHypersequentUniversalModality :: Polarity -> Hypersequent -> Hypersequent
applyHypersequentUniversalModality polarity (World seq hypers) =
  let gatherFunc =
        case polarity of
          Positive -> gatherPossibilities . posFormulas
          Negative -> gatherNecessities . negFormulas
      (relevant, irrelevant)  = gatherFunc seq
      newFormulas =
        case polarity of
          Positive -> map possibility relevant
          Negative -> map necessity relevant
      updatedHypersequents =
        map (addFormulasToAllWorlds polarity newFormulas) hypers
      newHypersequents =
         map (applyHypersequentUniversalModality polarity) updatedHypersequents
      newSequent = addFormulasToSequent polarity newFormulas seq
   in (World newSequent newHypersequents)

addFormulasToAllWorlds :: Polarity -> [Formula]  -> Hypersequent -> Hypersequent
addFormulasToAllWorlds polarity forms (World seq hypers) =
  let newSeq = addFormulasToSequent polarity forms seq
      newHypers = map (addFormulasToAllWorlds polarity forms) hypers
   in (World newSeq newHypers)

treeRemoveDuplicates :: ProofTree -> ProofTree
treeRemoveDuplicates Closed = Closed
treeRemoveDuplicates Open = Open
treeRemoveDuplicates (Node hyper branches) =
  let cleanHyper = hypersequentRemoveDuplicates hyper
      cleanBranches = map treeRemoveDuplicates branches
   in Node cleanHyper cleanBranches

--------------------------
--- Resolution Modules ---
--------------------------

-- @todo create separate module for proof trees
-- and create a separate module for resolution modules
-- that imports it.

applyResolutionModules :: ProofTree -> ProofTree
applyResolutionModules =
  treeRemoveDuplicates .
  potentiallyApplyModule RightModalLEM .
  potentiallyApplyModule PositiveReflexivity .
  potentiallyApplyModule OneRightNegation .
  potentiallyApplyModule PossiblyNotPossiblyNecessary

class (Show a) => ResolutionModule a where

  formulaPattern :: a -> Sequent -> Bool

  ruleToApply :: a -> Hypersequent -> Hypersequent

  formulaFilter :: a -> [Formula] -> [Formula]

  moduleMatches :: a -> Hypersequent -> Bool
  moduleMatches mod (World seq hypers) =
      formulaPattern mod seq || some (moduleMatches mod) hypers

  applyModule :: a -> Hypersequent -> ProofTree
  applyModule mod hypersequent =
    let cleanHypersequent = removeNonNecessaryForms mod hypersequent
        newHypersequent = ruleToApply mod cleanHypersequent
    in if hypersequentClosed newHypersequent
       then Node hypersequent [Node newHypersequent [Closed]]
       else error $ "Improper application of " ++ show mod ++ " Resolution Module\n" ++ show hypersequent ++ "\n\n" ++ show cleanHypersequent ++ "\n\n" ++ show newHypersequent

  removeNonNecessaryForms :: a -> Hypersequent -> Hypersequent
  removeNonNecessaryForms mod (World (Sequent _ poss) hypers) =
      let newSeq = makeSequent [] (formulaFilter mod poss)
       in World newSeq (map (removeNonNecessaryForms mod) hypers)


  potentiallyApplyModule :: a -> ProofTree -> ProofTree
  potentiallyApplyModule _ Open = Open
  potentiallyApplyModule _ Closed = Closed
  potentiallyApplyModule mod tree@(Node hypersequent [Open]) =
    if moduleMatches mod hypersequent
    then let (Node _ trees) = applyModule mod hypersequent
          in Node hypersequent trees
    else tree
  potentiallyApplyModule mod (Node hypersequent trees) =
    Node hypersequent (map (potentiallyApplyModule mod) trees)

data PositiveReflexivity = PositiveReflexivity deriving (Eq, Show)
instance ResolutionModule PositiveReflexivity where

  formulaPattern PositiveReflexivity (Sequent _ poss) =
    some (\f -> negationP f && Possibly (negatum f) `elem` poss) poss

  formulaFilter PositiveReflexivity [] = []
  formulaFilter PositiveReflexivity (Not f:xs) =
    if Possibly f `elem` xs
    then [Not f, Possibly f]
    else formulaFilter PositiveReflexivity xs
  formulaFilter PositiveReflexivity ((Possibly f):xs) =
    if Not f `elem` xs
    then [Not f, Possibly f]
    else formulaFilter PositiveReflexivity xs
  formulaFilter PositiveReflexivity (_:xs) =
    formulaFilter PositiveReflexivity xs

  ruleToApply PositiveReflexivity = applyHypersequentRightPossibility . applyRightNegation

data OneRightNegation = OneRightNegation deriving (Eq, Show)
instance ResolutionModule OneRightNegation where
  formulaPattern OneRightNegation (Sequent negs poss) =
   any (\forms -> some (\f -> negationP f && negatum f `elem` forms) forms) [negs, poss]

  formulaFilter OneRightNegation [] = []
  formulaFilter OneRightNegation (Not x:xs) =
    if x `elem` xs
    then [Not x, x]
    else formulaFilter OneRightNegation xs
  formulaFilter OneRightNegation (x:xs) =
    if Not x `elem` xs
    then [Not x, x]
    else formulaFilter OneRightNegation xs

  ruleToApply OneRightNegation = applyRightNegation . applyLeftNegation

data RightModalLEM = RightModalLEM deriving (Eq, Show)
instance ResolutionModule RightModalLEM where
  formulaPattern RightModalLEM (Sequent _ poss) =
    some (\f -> necessityP f && let subformula = necessity f
                                 in some (\otherF -> possibilityP otherF && negationOfP (possibility otherF) subformula) poss) poss

  formulaFilter RightModalLEM [] = []
  formulaFilter RightModalLEM (Necessarily x:xs) =
    if some (\form -> possibilityP form && negationOfP (possibility form) x) xs
    then [Necessarily x, Possibly (Not x)]
    else formulaFilter RightModalLEM xs
  formulaFilter RightModalLEM (Possibly x:xs) =
    if some (\form -> necessityP form && negationOfP (necessity form) x) xs
    then [Possibly x, Necessarily (Not x)]
    else formulaFilter RightModalLEM xs
  formulaFilter RightModalLEM (_:xs) =
    formulaFilter RightModalLEM xs

  ruleToApply RightModalLEM =
    applyLeftNegation .
    applyRightNegation .
    applyHypersequentRightPossibility .
    applyHypersequentRightNecessity


data PossiblyNotPossiblyNecessary = PossiblyNotPossiblyNecessary deriving (Eq, Show)
instance ResolutionModule PossiblyNotPossiblyNecessary where
  formulaPattern PossiblyNotPossiblyNecessary (Sequent _ poss) =
    some (\f -> possibilityP f &&
                negationP (possibility f) &&
                let subFormula  = negatum . possibility $ f
                 in some (\otherF -> possibilityP otherF &&
                           possibility otherF == Necessarily subFormula) poss) poss

  formulaFilter PossiblyNotPossiblyNecessary [] = []
  formulaFilter PossiblyNotPossiblyNecessary (Possibly (Not x):xs) =
    if Possibly (Necessarily x) `elem` xs
    then [Possibly (Not x), Possibly (Necessarily x)]
    else formulaFilter PossiblyNotPossiblyNecessary xs
  formulaFilter PossiblyNotPossiblyNecessary (Possibly (Necessarily x):xs) =
    if Possibly (Not x) `elem` xs
    then [Possibly (Necessarily x), Possibly (Not x)]
    else formulaFilter PossiblyNotPossiblyNecessary xs
  formulaFilter PossiblyNotPossiblyNecessary (_:xs) =
    formulaFilter PossiblyNotPossiblyNecessary xs

  ruleToApply PossiblyNotPossiblyNecessary  =
    applyRightNegation .
    applyHypersequentRightPossibility  .
    applyHypersequentRightNecessity .
    applyHypersequentRightPossibility 


p = (AtomicFormula "p")
q = (AtomicFormula "q")
np = (Not p)
pandq = (And [p, q])
--s1 = makeSequent  [] [p]
--s2 = makeSequent [p] [q]
--s3  = makeSequent [p] [np, pandq]
--s4 = makeSequent [] [np]
--h1  = (World s1 [(World s1 [])])
--h2 = (World s2 [(World s3 [(World s2 [])]), (World s4 [])])
--p1 = Node h1 [(Node h2 [(Node h2 [(Node h1 [Open])]), (Node h1 [Closed])])]

--f = Implies (And [p, Implies p q,Implies q (AtomicFormula "r")]) (AtomicFormula "r")
f  = (Not (Equivalent (Not (AtomicFormula "p")) (Not (Not (AtomicFormula "p")))))

(st, cf) = generateStartingProofTree f

func = applyResolutionModules . applyUniversalModalRules . applyPropositionalRules . applyParticularModalRules
s1 = func st
s2 = func s1
s3 = func s2
s4 = func s3



badHyper = (World (makeSequent []  [])[(World (makeSequent []  [(Necessarily (AtomicFormula "p")),(Necessarily (AtomicFormula "q")),(Possibly (And [(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))])),(Possibly (And [(Necessarily (AtomicFormula "p")),(Possibly (Not (AtomicFormula "q")))])),(And [(Necessarily (AtomicFormula "p")),(Possibly (Not (AtomicFormula "q")))]),(And [(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))])])[(World (makeSequent [(AtomicFormula "q")]  [(Necessarily (AtomicFormula "p")),(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "q"))),(And [(Necessarily (AtomicFormula "p")),(Possibly (Not (AtomicFormula "q")))]),(And [(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))]),(Not (AtomicFormula "q"))])[(World (makeSequent []  [(AtomicFormula "p"),(And [(Necessarily (AtomicFormula "p")),(Possibly (Not (AtomicFormula "q")))]),(And [(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))]),(Not (AtomicFormula "q"))])[])])])])
