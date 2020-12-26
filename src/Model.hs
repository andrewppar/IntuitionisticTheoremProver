module Model
  (Model (..)
  , satisfies
  , hypersequentSatisfies
  , getCounterExample
  , makeWorldsAndRelations
  , serializeModel
  )
    where
import Formula
import Sequent
import Hypersequent
import Utilities
import Debug.Trace
import Control.Parallel.Strategies

---------------
---- Models ---
---------------

data Model = Model {worlds :: [PossibleWorld]
                   , relations :: [(Int, Int)]
                   } deriving (Eq)

instance Show Model where
  show model =
    let ws = mapAppend (\w -> show w ++ "\n") . worlds $ model
        rs =
          mapAppend (\(r1,r2) -> show r1 ++ " -> " ++ show r2 ++ "\n") . relations $ model
     in "Worlds: \n " ++ ws ++ "\n" ++ "Relations: \n" ++ rs

--- Serialization

serializeModel :: Serialization -> Model -> IO()
serializeModel HTML = serializeModelToHTML

serializeModelToHTML :: Model -> IO()
serializeModelToHTML model =
  do template <- readFile "./utilities/model_html_template.html"
     let templateLines  = lines template
         withWorlds     = addWorldsToTemplateLines templateLines model
         withRelations  = addRelationsToTemplateLines withWorlds model
         withKey        = addKeyToTemplateLines withRelations model
      in do writeFile "./utilities/Model.html" (unlines withKey)

addWorldsToTemplateLines :: [String]  -> Model -> [String]
addWorldsToTemplateLines [] _ = []
addWorldsToTemplateLines (line:lines) model =
  if filter (/= ' ') line == "NODES"
     then generateWorldHTMLLines model ++ lines
     else line:addWorldsToTemplateLines lines model

generateWorldHTMLLines :: Model -> [String]
generateWorldHTMLLines model =
  let modelWorlds = worlds model
      modelLines =
        map (\world -> "{ id: " ++ show (tag world) ++ ", reflexive: false} ") modelWorlds
   in map (++ ",") (init modelLines) ++ [last modelLines]

addRelationsToTemplateLines :: [String] -> Model -> [String]
addRelationsToTemplateLines [] _ = []
addRelationsToTemplateLines (line:lines) model =
  if filter (/=  ' ') line == "RELATIONS"
     then generateRelationsHTMLLines model ++ lines
     else line:addRelationsToTemplateLines lines model

generateRelationsHTMLLines  :: Model -> [String]
generateRelationsHTMLLines model =
  let rels = relations model
      relationLines =
        map (\(relator, relatum) ->
             "{ source: nodes[" ++ show relator ++ "], target: nodes[" ++ show relatum ++ "], left: false, right:  true}") rels
   in map (++ ",") (init relationLines) ++ [last relationLines]

addKeyToTemplateLines  ::  [String] -> Model -> [String]
addKeyToTemplateLines lines model =
  let start = init lines
      header = "<h3>Key</h3>"
      modelWorlds = worlds model
      body = map (\world ->
        let trues = joinStrings "," . map show . trueFormulas $  world
            falses  = joinStrings "," . map show . falseFormulas $ world
         in  "<p>World " ++ show (tag world) ++ "<b>⊨</b>" ++ trues ++ "<b>⊭</b>" ++ falses ++ "</p>") modelWorlds
  in header:start ++ body ++ [last lines]

--- Accessing Worlds in Models

getWorldByTag :: Model -> Int -> PossibleWorld
getWorldByTag model tagInt =
  --NOTE: This isn't safe
 head . foldr
           (\world acc ->
             if tag world == tagInt
                then world:acc
                else acc) [] . worlds $ model

sortModels :: (Model ->  Bool) -> [Model] -> ([Model], [Model])
sortModels f =
  foldl (\(passing, notPassing) model -> if f model
                                         then (model:passing, notPassing)
                                         else (passing, model:notPassing)) ([], [])

consistentModelP :: Model -> Bool
consistentModelP = all consistentWorldP . worlds

consistentWorldP :: PossibleWorld -> Bool
consistentWorldP possibleWorld =
  null . setIntersection (trueFormulas possibleWorld) . falseFormulas $ possibleWorld

atomicModelP :: Model -> Bool
atomicModelP model = all (`atomicModelAtWorldP` model)  . worlds $ model

atomicModelAtWorldP :: PossibleWorld -> Model -> Bool
atomicModelAtWorldP world model =
  let modelWorld = getWorldByTag model . tag $ world
      trues = trueFormulas modelWorld
      falses = falseFormulas modelWorld
   in all atomicFormulaP trues && all atomicFormulaP falses

--- Possible Worlds

data PossibleWorld = PossibleWorld {trueFormulas :: [Formula]
                                   , falseFormulas :: [Formula]
                                   , tag ::  Int
                   } deriving (Eq, Ord)

instance Show PossibleWorld where
  show world = show (tag world) ++ " |= " ++ (show . trueFormulas $ world) ++ "|/= " ++ (show . falseFormulas $ world)

generateNextTag :: Int -> Int
generateNextTag int = int + 1

makeWorld :: [Formula] -> [Formula] -> Int -> PossibleWorld
makeWorld trueFormulas falseFormulas tag =
  let trues = slowRemoveDuplicates trueFormulas
      falses = slowRemoveDuplicates falseFormulas
   in PossibleWorld trues falses tag

addTrueFormula :: PossibleWorld -> Formula -> PossibleWorld
addTrueFormula (PossibleWorld true false tag) formula =
  PossibleWorld (formula:true) false tag

addFalseFormula :: PossibleWorld -> Formula -> PossibleWorld
addFalseFormula (PossibleWorld true false tag) formula =
  PossibleWorld true (formula:false) tag

formulaAtWorldP :: PossibleWorld -> Formula -> Bool
formulaAtWorldP (PossibleWorld trues falses _) form =
  form `elem` trues || form `elem` falses

getRelatedWorlds :: Model -> PossibleWorld -> [PossibleWorld]
getRelatedWorlds model@(Model _ relations) =
  map (getWorldByTag model)
 .  getRelatedWorldTags [] [] relations
 . tag

getRelatedWorldTags :: [Int]  -> [Int] -> [(Int, Int)] -> Int -> [Int]
getRelatedWorldTags accumulator visitedTags relations tag =
  let newVisitedTags = (tag:visitedTags)
      oneStepRelated =
        foldl (\acc (relator, relatum) ->
          if relator == tag && relatum /= tag && notElem relatum visitedTags
             then relatum:acc
             else acc) [] relations
      recursiveResults =
        mapAppend (getRelatedWorldTags accumulator newVisitedTags relations) oneStepRelated
   in tag:recursiveResults

makeWorldFromSequent :: Sequent -> Int -> PossibleWorld
makeWorldFromSequent (Sequent negs poss) = makeWorld negs poss

replaceWorldInModel :: Model -> PossibleWorld -> PossibleWorld -> Model
replaceWorldInModel (Model worlds relations) old new =
  let newWorlds = replaceWorldInWorlds worlds old new
   in Model newWorlds relations

addWorldToModel :: Model -> PossibleWorld -> [(Int, Int)] -> Model
addWorldToModel (Model worlds relations) world newRelations =
  Model (worlds ++ [world]) (relations ++ newRelations)

replaceWorldInWorlds ::  [PossibleWorld] -> PossibleWorld -> PossibleWorld -> [PossibleWorld]
replaceWorldInWorlds [] _ _  = []
replaceWorldInWorlds (world:worlds) old new =
  if world == old
     then new:replaceWorldInWorlds worlds old new
     else world:replaceWorldInWorlds worlds old new

getHighestTag :: Model -> Int
getHighestTag (Model worlds _) =
  foldl (\acc world -> if tag world > acc then tag world else acc) 0 worlds

------------------
-- Satisfaction --
------------------

hypersequentSatisfies :: Formula -> Hypersequent -> Bool
hypersequentSatisfies formula hyper =
  let models = buildModelsFromHypersequent  hyper 0
      potentialSatisfiedModels =
        map (\model -> satisfies formula model (getWorldByTag model 0)) models
      satisfiedModels =
        potentialSatisfiedModels `using`parList rdeepseq
   in some (== True) satisfiedModels

getCounterExample :: Formula -> [Hypersequent] -> Maybe Model
getCounterExample _ [] = Nothing
getCounterExample formula (h@(World seq _):_) =
  let models = buildModelsFromHypersequent h 0
      world = makeWorldFromSequent seq 0
      survivingModels =
        filter (\model ->
          let (_, maybeVal) =
                satisfiesInternal (Not formula) model  world
           in case maybeVal of
             Just True -> True
             _ -> False) models
 in if null survivingModels
       then Nothing
    else Just (head survivingModels)

satisfies :: Formula -> Model -> PossibleWorld -> Bool
satisfies form model world =
  world `elem` worlds model &&
     (let (_, value) = satisfiesInternal form model world
       in Just True == value)



debugMode = False
satisfiesIntermediate  :: Formula -> Model -> PossibleWorld -> (Model, Maybe Bool)
satisfiesIntermediate formula model  world =
  if debugMode
     then trace ("SatisfiesInternal: " ++ show formula ++ " " ++ show (tag world)) (satisfiesInternal formula model world)
     else satisfiesInternal formula model world

satisfiesInternal :: Formula -> Model -> PossibleWorld -> (Model, Maybe Bool)
-- TODO: There are probably  some good  abstractions  to  be made
-- in the quantified parts of this
satisfiesInternal form@(AtomicFormula _) model world
  | form `elem` trueFormulas world = (model, Just True)
  | form `elem` falseFormulas world = (model, Just False)
  | otherwise = (model, Nothing)
satisfiesInternal (Not (AtomicFormula string)) model world
  | AtomicFormula string `elem` trueFormulas world = (model, Just False)
  | AtomicFormula string `elem` falseFormulas world = (model, Just True)
  | otherwise = (model, Nothing)
satisfiesInternal (Not form) model world =
  let (newModel, recursiveValue) = satisfiesIntermediate form model world
      result = case recursiveValue of
                   Just True  -> (newModel, Just False)
                   Just False -> (newModel, Just True)
                   Nothing    -> (newModel, Nothing)
   in result
satisfiesInternal (And forms) model world =
  satisfiesJunctionInternal forms model world True
satisfiesInternal (Or forms) model world =
  satisfiesJunctionInternal forms model world False

satisfiesInternal (Necessarily form) model world =
  let relatedWorlds = getRelatedWorlds model world
   in satisfiesModalInternal form model relatedWorlds True
satisfiesInternal (Possibly form) model world =
  let relatedWorlds = getRelatedWorlds model world
   in satisfiesModalInternal form model relatedWorlds False

satisfiesJunctionInternal :: [Formula] -> Model -> PossibleWorld -> Bool -> (Model, Maybe Bool)
satisfiesJunctionInternal [] model _ startingValue =
  (model, Just startingValue)
satisfiesJunctionInternal (x:xs) model world startingValue =
  let (m, maybeValue) = satisfiesInternal x model world
   in  case maybeValue of
     Just value ->
       if value /= startingValue
          then (m, maybeValue)
          else satisfiesJunctionInternal  xs model world startingValue
     _ -> satisfiesJunctionInternal xs model world startingValue

satisfiesModalInternal :: Formula -> Model -> [PossibleWorld] -> Bool -> (Model, Maybe Bool)
satisfiesModalInternal _ model [] startingValue =
  (model, Just startingValue)
satisfiesModalInternal form model (world:worlds) startingValue =
  let (m, maybeValue) = satisfiesIntermediate form model world
   in case maybeValue of
     Just value ->
       if value /= startingValue
          then (m, Just value)
          else satisfiesModalInternal form m worlds startingValue
     _ -> satisfiesModalInternal form m worlds startingValue

buildModelsFromHypersequent :: Hypersequent -> Int -> [Model]
buildModelsFromHypersequent hypersequent rootTag =
  let (worlds, relations, _) = makeWorldsAndRelations hypersequent rootTag
      --baseModel = Model worlds relations
   in reduceComplexFormulas [Model worlds relations]
      --atoms = gatherAtomicFormulasInHypersequent hypersequent
      --atoms = gatherAtomicFormulasInModel baseModel
--   in completeModelWithFormulas baseModel atoms

makeWorldsAndRelations :: Hypersequent -> Int -> ([PossibleWorld], [(Int, Int)], Int)
makeWorldsAndRelations (World seq hypers) rootTag =
  let resultWorld = makeWorldFromSequent seq rootTag
   in foldl (\(accWorlds, accRelations, accTag) hyper@(World accSeq _) ->
     let nextTag = generateNextTag accTag
         newRoot = makeWorldFromSequent accSeq nextTag
         (updatedWorlds, updatedRels, lastTag) =
           makeWorldsAndRelations hyper nextTag
         newWorlds = accWorlds ++ updatedWorlds
         resultTag = tag resultWorld
         newRootTag = tag newRoot
         newRels = ((resultTag, newRootTag):accRelations) ++ updatedRels
      in (newWorlds, newRels, lastTag)) ([resultWorld], [], rootTag) hypers

reduceComplexFormulas :: [Model] -> [Model]
reduceComplexFormulas models =
  let newModels = mapAppend reduceComplexFormulasInternal models
      (atomicModels, nonAtomicModels) = sortModels atomicModelP newModels
   in if null nonAtomicModels
      then filter consistentModelP atomicModels
      -- We might be able to just use the else clause
      else filter consistentModelP atomicModels ++ reduceComplexFormulas nonAtomicModels


reduceComplexFormulasInternal :: Model -> [Model]
reduceComplexFormulasInternal model =
  foldl (flip reduceFormulasAtWorld) [model] (worlds model)

reduceFormulasAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceFormulasAtWorld world models =
  let newModels = reduceNegativePossibilityAtWorld world .
                  reducePositiveNecessityAtWorld world .
                  reducePositivePossibilityAtWorld world .
                  reduceNegativeNecessityAtWorld world .
                  reducePositiveConjunctionAtWorld world .
                  reduceNegativeConjunctionAtWorld world .
                  reducePositiveDisjunctionAtWorld world .
                  reduceNegativeDisjunctionAtWorld world .
                  reducePositiveNegationAtWorld world .
                  reduceNegativeNegationAtWorld world $ models
   in if all (atomicModelAtWorldP world) newModels
         then newModels
         else reduceFormulasAtWorld world newModels

reduceNegativePossibilityAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceNegativePossibilityAtWorld world =
  map (reduceUniversalAtWorld Negative world)

reducePositiveNecessityAtWorld :: PossibleWorld -> [Model] -> [Model]
reducePositiveNecessityAtWorld world =
  map (reduceUniversalAtWorld Positive world)

-- There's a bug here: Check m3 |-> m2
reduceUniversalAtWorld :: Polarity -> PossibleWorld -> Model -> Model
reduceUniversalAtWorld polarity world model@(Model _ relations) =
    let modelWorld = getWorldByTag model . tag $ world
        (relevantFormulas, irrelevantFormulas) = case polarity of
          Positive -> gatherNecessities . trueFormulas $ modelWorld
          Negative -> gatherPossibilities . falseFormulas $ modelWorld
        relatedWorlds = getRelatedWorlds model modelWorld
        unrelatedWorlds = setMinus (worlds model) relatedWorlds
        newForms = case polarity of
          Positive -> map necessity relevantFormulas
          Negative -> map possibility relevantFormulas
        updatedWorlds = map (\loopWorld ->
                               let currentTag = tag loopWorld
                               in if loopWorld == modelWorld
                                     then case polarity of
                                            Positive ->
                                                PossibleWorld (newForms  ++ irrelevantFormulas)
                                                              (falseFormulas loopWorld)
                                                              currentTag
                                            Negative ->
                                                PossibleWorld (trueFormulas loopWorld)
                                                              (newForms  ++ irrelevantFormulas)
                                                              currentTag
                                     else foldl
                                              (case polarity of
                                                 Positive -> addTrueFormula
                                                 Negative -> addFalseFormula)
                                                             loopWorld newForms) relatedWorlds
    in Model (updatedWorlds ++ unrelatedWorlds) relations

reducePositivePossibilityAtWorld :: PossibleWorld -> [Model] -> [Model]
reducePositivePossibilityAtWorld world =
  map (reduceParticularAtWorld Positive world)

reduceNegativeNecessityAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceNegativeNecessityAtWorld world =
  map (reduceParticularAtWorld Negative world)


reduceParticularAtWorld :: Polarity -> PossibleWorld -> Model -> Model
reduceParticularAtWorld polarity world model =
    let modelWorld = getWorldByTag model . tag $ world
        (relevantFormulas, irrelevantFormulas) = case polarity of
                                                   Positive -> gatherPossibilities . trueFormulas $ modelWorld
                                                   Negative -> gatherNecessities . falseFormulas $ modelWorld
        highestTag = getHighestTag model
        (newWorlds, _) = foldl (\(worlds, lastTag) formula ->
                                        let newTag = generateNextTag lastTag
                                        in case polarity of
                                          Positive -> (makeWorld [possibility formula] [] newTag:worlds, newTag)
                                          Negative -> (makeWorld [] [necessity formula] newTag:worlds, newTag)) ([], highestTag) relevantFormulas
        updatedWorld = case polarity of
          Positive -> makeWorld irrelevantFormulas (falseFormulas modelWorld) (tag world)
          Negative -> makeWorld (trueFormulas modelWorld) irrelevantFormulas (tag world)
        updatedModel = replaceWorldInModel model modelWorld updatedWorld
     in if null newWorlds
        then updatedModel
        else foldl (\acc newWorld ->
                      let accWorlds = worlds acc ++ [newWorld]
                          accRels   = relations acc ++ [(tag world, tag newWorld)]
                       in Model accWorlds accRels) updatedModel newWorlds


reduceNegativeConjunctionAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceNegativeConjunctionAtWorld world =
  mapAppend (reduceParticularJunctionAtWorld Negative world)


reducePositiveDisjunctionAtWorld :: PossibleWorld -> [Model] -> [Model]
reducePositiveDisjunctionAtWorld world =
  mapAppend (reduceParticularJunctionAtWorld Positive world)

reduceParticularJunctionAtWorld :: Polarity -> PossibleWorld -> Model -> [Model]
reduceParticularJunctionAtWorld polarity world model =
  let currentTag = tag world
      modelWorld = getWorldByTag model currentTag
      (relevantFormulas, irrelevantFormulas) = case polarity of
                                                  Positive -> gatherDisjunctions . trueFormulas $ modelWorld
                                                  Negative -> gatherConjunctions . falseFormulas $ modelWorld
      newFormulaGroups = cartesianProduct . map (case polarity of
                                              Positive -> disjuncts
                                              Negative -> conjuncts) $ relevantFormulas
      newWorlds = if null newFormulaGroups
                     then [modelWorld]
                     else map (\formulas -> case polarity of
                                             Positive -> makeWorld (formulas ++ irrelevantFormulas) (falseFormulas modelWorld) currentTag
                                             Negative -> makeWorld (trueFormulas modelWorld) (formulas ++ irrelevantFormulas) currentTag) newFormulaGroups
   in map (replaceWorldInModel model modelWorld) newWorlds

reducePositiveConjunctionAtWorld :: PossibleWorld -> [Model] -> [Model]
reducePositiveConjunctionAtWorld world =
  map (reduceUniversalJunctionAtWorld Positive world)

reduceNegativeDisjunctionAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceNegativeDisjunctionAtWorld world =
  map (reduceUniversalJunctionAtWorld Negative world)

reduceUniversalJunctionAtWorld :: Polarity -> PossibleWorld -> Model -> Model
reduceUniversalJunctionAtWorld polarity world model =
  let currentTag = tag world
      modelWorld = getWorldByTag model currentTag
      (relevantFormulas, irrelevantFormulas) = case polarity of
                                                 Positive -> gatherConjunctions . trueFormulas $ modelWorld
                                                 Negative -> gatherDisjunctions . falseFormulas $ modelWorld
      newFormulas = mapAppend (case polarity of
                                 Positive -> conjuncts
                                 Negative -> disjuncts) relevantFormulas
      updatedWorld = case polarity of
                       Positive -> makeWorld (newFormulas ++ irrelevantFormulas) (falseFormulas modelWorld) currentTag
                       Negative -> makeWorld (trueFormulas modelWorld) (newFormulas ++ irrelevantFormulas) currentTag
   in replaceWorldInModel model modelWorld updatedWorld

reducePositiveNegationAtWorld :: PossibleWorld -> [Model] -> [Model]
reducePositiveNegationAtWorld world =
  map (reduceNegationAtWorldInternal Positive world)

reduceNegativeNegationAtWorld :: PossibleWorld -> [Model] -> [Model]
reduceNegativeNegationAtWorld world =
  map (reduceNegationAtWorldInternal Negative world)

reduceNegationAtWorldInternal :: Polarity -> PossibleWorld -> Model -> Model
reduceNegationAtWorldInternal polarity world model =
  let currentTag = tag world
      modelWorld = getWorldByTag model currentTag
      (relevantFormulas, irrelevantFormulas) = case polarity of
                                                 Positive -> gatherNegations . trueFormulas $ modelWorld
                                                 Negative -> gatherNegations . falseFormulas $ modelWorld
      updatedFormulas = map negatum relevantFormulas
      updatedWorld = case polarity of
                       Positive -> makeWorld irrelevantFormulas (updatedFormulas ++ falseFormulas modelWorld) currentTag
                       Negative -> makeWorld (updatedFormulas ++ trueFormulas modelWorld) irrelevantFormulas currentTag
   in replaceWorldInModel model modelWorld updatedWorld

completeModelWithFormulas :: Model -> [Formula] -> [Model]
completeModelWithFormulas model =
  foldl (\acc form ->
    if null acc
       then completeModelWithFormula model form
       else mapAppend (`completeModelWithFormula` form) acc) []

completeModelWithFormula :: Model -> Formula -> [Model]
completeModelWithFormula base@(Model [] _) _ =  [base]
completeModelWithFormula (Model (world:worlds) relations) form =
  let recursiveModels = completeModelWithFormula (Model worlds relations) form
   in if formulaAtWorldP world form
         then map (\(Model ws rs) -> Model (world:ws) rs) recursiveModels
         else foldl (\acc (Model ws _) ->
           let newTrueWorld = addTrueFormula world form
               newTrueModel = Model (newTrueWorld:ws) relations
               newFalseWorld = addFalseFormula world form
               newFalseModel = Model (newFalseWorld:ws) relations
            in (newTrueModel:newFalseModel:acc)) [] recursiveModels

p = AtomicFormula "p"
q = AtomicFormula "q"

s0 = makeSequent [p,q]  []
s1 = makeSequent [p] []
s2 = makeSequent []  [p,q]

h1 = (World (makeSequent []  [])[(World (makeSequent []  [(AtomicFormula "p")])[]),(World (makeSequent []  [(Possibly (Not (AtomicFormula "p"))),(Not (AtomicFormula "p"))])[])])
--m1 = buildModelsFromHypersequent h1 0

f = Necessarily (Possibly (Or [Necessarily p, And [p, Not p]]))
h = World (makeSequent []  [])[World (makeSequent []  [Possibly (Or [Necessarily (AtomicFormula "p"),And [AtomicFormula "p",Not (AtomicFormula "p")]]),Or [Necessarily (AtomicFormula "p"),And [AtomicFormula "p",Not (AtomicFormula "p")]]])[]]

(ws, rs,t) = makeWorldsAndRelations h 0
world = head . tail $ ws
m  = Model ws rs
m1 = reduceNegativePossibilityAtWorld world m2
m2 = reducePositiveNecessityAtWorld world m3
m3 = reducePositivePossibilityAtWorld world m4
m4 = reduceNegativeNecessityAtWorld world m5
m5 = reducePositiveConjunctionAtWorld world m6
m6 = reduceNegativeConjunctionAtWorld world m7
m7 = reducePositiveDisjunctionAtWorld world m8
m8 = reduceNegativeDisjunctionAtWorld world m9
m9 = reducePositiveNegationAtWorld world m10
m10 = reduceNegativeNegationAtWorld world [m]




w = head . tail . worlds  $ m
ms = reduceNegativeDisjunctionAtWorld w [m]
newM = reduceParticularAtWorld Negative w (head ms)

--m = buildModelsFromHypersequent h 0
