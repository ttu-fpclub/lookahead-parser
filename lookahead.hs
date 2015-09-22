import Data.List(delete)
import Data.Set(Set)
import Data.Char
import Data.Ix
import Data.Proxy
import Data.Maybe
import Data.Array.ST
import Data.Array.IArray
import Data.Tree
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.State
import Control.Arrow

import Debug.Trace

data LL1Table n s = LL1Table (Set n) (Set s) (Array (Int, Int) (Maybe (Str n s)))
                    deriving (Show, Read, Eq)

data LR1Table n s = LR1Table (Set n) (Set s) Int
                                             (Array (Int, Int) (LR1Action n s))
                                             (Array (Int, Int) (Maybe Int))
                    deriving (Show, Read, Eq)

data LR1Action n s = Error | Shift Int | Reduce (Rule n s) | Accept
                     deriving (Show, Read, Eq)

data LR1Rule n s = LR1Rule (Rule n s) Int
                   deriving (Show, Read, Eq, Ord)

data LR1Prim n s = LR1Prim [LR1Rule n s] [(Either n s, LR1Prim n s)]
                   deriving (Show, Read)

-- TODO: The third argument (Bool) is an implementation detail for
--       toPrim; find a better way to do this
data LR1Node n s = LR1Node [LR1Rule n s] [(Either n s, Int)] Bool
                   deriving (Show, Read)

data CFG n s = CFG [Rule n s] n
               deriving (Show, Read, Eq)

data Rule n s = Rule n (Str n s)
                deriving (Show, Read, Eq, Ord)

data CorE s = Epsilon | ChE s -- Character or Epsilon
              deriving (Show, Read, Eq, Ord)

data CorS s = EOS | ChS s -- Character or String-Marker
              deriving (Show, Read, Eq, Ord)

type Str n s = [Either n s]

instance (Eq n, Eq s) => Eq (LR1Prim n s) where
    LR1Prim rr _ == LR1Prim rr' _ = rr == rr'

instance (Ord n, Ord s) => Ord (LR1Prim n s) where
    LR1Prim rr _ `compare` LR1Prim rr' _ = rr `compare` rr'

instance (Eq n, Eq s) => Eq (LR1Node n s) where
    LR1Node rr _ _ == LR1Node rr' _ _ = rr == rr'

instance (Ord n, Ord s) => Ord (LR1Node n s) where
    LR1Node rr _ _ `compare` LR1Node rr' _ _ = rr `compare` rr'

ll1Lookup :: (Ord n, Ord s) => (n, CorS s) -> LL1Table n s -> Maybe (Str n s)
ll1Lookup (n, s) (LL1Table ns ss arr) = do
  r <- Set.lookupIndex n ns
  c <- case s of
         EOS -> return $ Set.size ss
         ChS ch -> Set.lookupIndex ch ss
  guard $ inRange (bounds arr) (r, c)
  arr ! (r, c)

getRules :: CFG n s -> [Rule n s]
getRules (CFG x _) = x

getStart :: CFG n s -> n
getStart (CFG _ x) = x

getLHS :: Rule n s -> n
getLHS (Rule x _) = x

getRHS :: Rule n s -> Str n s
getRHS (Rule _ x) = x

firstCharE :: [s] -> CorE s
firstCharE (x:_) = ChE x
firstCharE [] = Epsilon

firstCharS :: [s] -> CorS s
firstCharS (x:_) = ChS x
firstCharS [] = EOS

mapBelt :: (([a], a, [a]) -> b) -> [a] -> [b]
mapBelt f = mapBelt' f []
    where mapBelt' _ _ [] = []
          mapBelt' f xs (y:ys) = f (xs, y, ys) : mapBelt' f (y:xs) ys

mapBeltM :: Monad m => (([a], a, [a]) -> m b) -> [a] -> m [b]
mapBeltM = (sequence .) . mapBelt

mapBeltM_ :: Monad m => (([a], a, [a]) -> m b) -> [a] -> m ()
mapBeltM_ = (sequence_ .) . mapBelt

foldE :: c -> (s -> c) -> CorE s -> c
foldE c _ Epsilon = c
foldE _ f (ChE ch) = f ch

foldS :: c -> (s -> c) -> CorS s -> c
foldS c _ EOS = c
foldS _ f (ChS ch) = f ch

eToS :: [CorE s] -> [CorS s]
eToS = concatMap (foldE [] ((:[]) . ChS))

sToE :: [CorS s] -> [CorE s]
sToE = concatMap (foldS [] ((:[]) . ChE))

eToChar :: [CorE s] -> [s]
eToChar = concatMap (foldE [] (:[]))

hoistMaybe :: Monad m => e -> Maybe a -> ExceptT e m a
hoistMaybe s Nothing = ExceptT . return $ Left s
hoistMaybe _ (Just x) = return x

type LHSReader n s = Reader (Str n s, CFG n s)

data First n s = First (Str n s) | First' (Str n s) |
                 FLit [CorE s] | FSum (First n s) (First n s)

reduceFirst :: (Ord s, Eq n) => First n s -> LHSReader n s (Set (CorE s))
reduceFirst (FLit lit) = return $ Set.fromList lit
reduceFirst (FSum f1 f2) = liftA2 Set.union (reduceFirst f1) (reduceFirst f2)
reduceFirst (First rhs) = do
  (lhs, _) <- ask
  case () of
    _ | rhs == lhs -> return Set.empty -- Assume fixed point is the empty set
      | otherwise -> reduceFirst (First' rhs)
reduceFirst (First' rhs) =
    case rhs of
      [] -> return $ Set.singleton Epsilon
      [Right t] -> return $ Set.singleton (ChE t)
      [Left n] -> do
               (_, CFG rules _) <- ask
               let rules' = filter ((== n) . getLHS) rules
               reduceFirst . foldr FSum (FLit []) $ map (First . getRHS) rules'
      (x:xs) -> do
               front <- reduceFirst (First [x])
               if Epsilon `Set.member` front then
                    (Set.delete Epsilon front `Set.union`) <$> reduceFirst (First xs)
                else
                    return front

firstSet :: (Ord s, Eq n) => CFG n s -> Str n s -> Set (CorE s)
firstSet cfg str = runReader (reduceFirst $ First' str) (str, cfg)

type LHSFReader n s = Reader (n, CFG n s)

data Follow n s = Follow n | Follow' n |
                  FoLit [CorS s] | FoSum (Follow n s) (Follow n s)

toLHSFR :: LHSReader n s a -> LHSFReader n s a
toLHSFR = withReader (first $ (: []) . Left)

reduceFollow :: (Ord s, Eq n) => Follow n s -> LHSFReader n s (Set (CorS s))
reduceFollow (FoLit lit) = return $ Set.fromList lit
reduceFollow (FoSum f1 f2) = liftA2 Set.union (reduceFollow f1) (reduceFollow f2)
reduceFollow (Follow rhs) = do
  (lhs, _) <- ask
  case () of
    _ | rhs == lhs -> return Set.empty -- Assume fixed point is the empty set
      | otherwise -> reduceFollow (Follow' rhs)
reduceFollow (Follow' rhs) = do
  (lhs, cfg@(CFG rules st)) <- ask
  res <- fmap Set.unions . forM rules $ \(Rule ll rr) ->
      fmap Set.unions . (`mapBeltM` rr) $ \(_, x, aft) ->
          case x of
            Right x -> return Set.empty
            Left n | n /= rhs -> return Set.empty
                   | null aft -> reduceFollow $ Follow ll
                   | otherwise -> do
                               let err = error "Epsilon in set after deletion!"
                                   frst = firstSet cfg aft
                                   frst' = Set.map (foldE err ChS) .
                                           Set.delete Epsilon $
                                           frst
                               oth <- if Epsilon `Set.member` frst then
                                          reduceFollow $ Follow ll
                                      else
                                          return Set.empty
                               return $ oth `Set.union` frst'
  if st == rhs then
      return $ Set.insert EOS res
  else
      return res

followSet :: (Ord s, Eq n) => CFG n s -> n -> Set (CorS s)
followSet cfg n = runReader (reduceFollow $ Follow' n) (n, cfg)

getNonterminals :: Ord n => CFG n s -> Set n
getNonterminals = Set.fromList . map getLHS . getRules

getTerminals :: Ord s => CFG n s -> Set s
getTerminals = Set.fromList . concatMap (concatMap (either (const []) (: [])) . getRHS)
               . getRules

buildTable :: (Ord s, Ord n) => CFG n s -> Either String (LL1Table n s)
buildTable cfg = let tt = getTerminals cfg
                     nt = getNonterminals cfg
                 in case buildTable'' (cfg, tt, nt) of
                      Left s -> Left s
                      Right x -> Right $ LL1Table nt tt x
    where buildTable'' :: (Ord n', Ord s') => (CFG n' s', Set s', Set n') ->
                          Either String (Array (Int, Int) (Maybe (Str n' s')))
          buildTable'' dat = runST $ runExceptT $ do
                               arr <- buildTable' dat
                               lift $ freeze arr
          buildTable' :: (Ord n', Ord s') => (CFG n' s', Set s', Set n') ->
                         ExceptT String (ST s0)
                         (STArray s0 (Int, Int) (Maybe (Str n' s')))
          buildTable' (cfg, tt, nt) = do
            arr <- lift $ newArray ((0, 0), (Set.size nt - 1, Set.size tt)) Nothing
            forM_ (getRules cfg) $ \(Rule lhs rhs) -> do
                let frst = firstSet cfg rhs
                forM_ (eToChar . Set.toList $ frst) $ \t ->
                      attemptWrite (tt, nt) arr lhs (ChS t) rhs
                when (Epsilon `Set.member` frst) $
                    forM_ (followSet cfg lhs) $ \t ->
                        attemptWrite (tt, nt) arr lhs t rhs
            return arr
          attemptWrite :: (Ord n', Ord s') => (Set s', Set n') ->
                          STArray s0 (Int, Int) (Maybe (Str n' s')) ->
                          n' -> CorS s' -> Str n' s' -> ExceptT String (ST s0) ()
          attemptWrite (tt, nt) arr' n t x = do
            n' <- hoistMaybe "Out of bounds" $ Set.lookupIndex n nt
            t' <- case t of
                    EOS -> return $ Set.size tt
                    ChS t -> hoistMaybe "Out of bounds" $
                               Set.lookupIndex t tt
            rr <- lift $ readArray arr' (n', t')
            unless (isNothing rr) $ throwError "Ambiguity in table"
            lift $ writeArray arr' (n', t') (Just x)

-- Type signatures listed in comments cannot be explicitly declared
-- without ScopedTypeVariables

doLL1Parse :: (Show n, Show s, Ord n, Ord s) =>
              LL1Table n s -> n -> [s] -> Either String (Tree (Either n s))
doLL1Parse table st ss = Node (Left st) <$> doParse (map ChS ss ++ [EOS]) [Left st]
    where -- doParse :: [CorS s] -> Str n s -> Either String (Forest (Either n s))
          doParse [] _ = Left "Ran out of input characters"
          doParse [EOS] [] = return []
          doParse _ [] = Left "Ran out of stack characters"
          doParse (s:ss) (n:ns) =
              case n of
                Right t
                    | s == ChS t -> doParse ss ns
                    | otherwise -> Left $ "Expected literal " ++ show t ++
                                          " found " ++ foldS "EOS" show s
                Left n' -> case ll1Lookup (n', s) table of
                             Nothing -> Left $ "Unexpected " ++ foldS "EOS" show s
                             (Just str) -> do
                                 rest <- doParse (s:ss) (str ++ ns)
                                 return [Node (Left n') rest]

doLL1Parse' :: (Show n, Show s, Ord n, Ord s) =>
              CFG n s -> [s] -> Either String (Tree (Either n s))
doLL1Parse' (CFG rules st) ss = do
  table <- buildTable $ CFG rules st
  doLL1Parse table st ss

getLR1InitialState :: (Eq n, Eq s) => CFG n s -> LR1Prim n s
getLR1InitialState (CFG rules st) = buildPrim $ toRulesT st
    where -- toRules :: [Rule n s] -> [LR1Rule n s]
          toRules xs = let base = map (\x -> LR1Rule x 0) xs
                       in (`concatMap` base) $ \(self@(LR1Rule (Rule n str) i)) ->
                           case drop i str of
                             [] -> base
                             (Right _):_ -> base
                             (Left n):_ -> toRulesT n ++ base
          -- toRulesT :: n -> [LR1Rule n s]
          toRulesT n = toRules $ filter (\(Rule lhs _) -> lhs == n) rules
          -- doTransitions :: LR1Rule n s -> Maybe (Either n s, LR1Prim n s)
          doTransitions (LR1Rule (Rule n str) i) =
              case drop i str of
                [] -> Nothing
                (x:xs) -> let next = LR1Rule (Rule n str) $ i + 1
                          in case xs of
                               (Left nt):_ -> Just (x, buildPrim $ next : toRulesT nt)
                               _ -> Just (x, buildPrim [next])
          -- buildPrim :: [LR1Rule n s] -> LR1Prim n s
          buildPrim xs = LR1Prim xs . mapMaybe doTransitions $ xs

primsTo :: (Ord n, Ord s) => LR1Prim n s -> Set (LR1Node n s)
primsTo l0 = execState (traversal l0 >> traversal1 l0) Set.empty
    where traversal :: (Ord n, Ord s) => LR1Prim n s -> State (Set (LR1Node n s)) ()
          traversal (LR1Prim rules st) = do
            vis <- get
            let curr = LR1Node rules [] False
            modify $ (Set.insert curr)
            unless (curr `Set.member` vis) $
                 mapM_ (traversal . snd) st
          traversal1 :: (Ord n, Ord s) => LR1Prim n s -> State (Set (LR1Node n s)) ()
          traversal1 (LR1Prim rules st) = do
            vis <- get
            let curr = LR1Node rules [] False
                currn = Set.lookupIndex curr vis
                alreadyDone = case currn of
                                Nothing -> False
                                Just x -> let LR1Node _ _ b = Set.elemAt x vis
                                          in b
            when (not alreadyDone) $ do
              forM_ st $ \(tr, prim) -> do
                   let LR1Prim pp _ = prim
                       prim' = LR1Node pp [] False
                   case Set.lookupIndex prim' vis of
                     Nothing -> return ()
                     Just n ->
                         modify $ modify' curr
                                    (\(LR1Node rr ns b) -> LR1Node rr ((tr, n) : ns) b)
              modify $ modify' curr (\(LR1Node rr ns _) -> LR1Node rr ns True)
              mapM_ (traversal1 . snd) st
          modify' :: Ord a0 => a0 -> (a0 -> a0) -> Set a0 -> Set a0
          modify' old f set = if Set.member old set then
                                 let Just curr = Set.lookupLE old set
                                 in Set.insert (f curr) . Set.delete curr $ set
                             else
                                 set

buildLR1Table :: (Ord n, Ord s) => CFG n s -> Either String (LR1Table n s)
buildLR1Table cfg@(CFG rules st) = runArrays
    where nodes = primsTo . getLR1InitialState $ cfg
          -- toRules :: [Rule n s] -> [LR1Rule n s]
          toRules xs = let base = map (\x -> LR1Rule x 0) xs
                       in (`concatMap` base) $ \(self@(LR1Rule (Rule n str) i)) ->
                           case drop i str of
                             [] -> base
                             (Right _):_ -> base
                             (Left n):_ -> toRulesT n ++ base
          -- toRulesT :: n -> [LR1Rule n s]
          toRulesT n = toRules $ filter (\(Rule lhs _) -> lhs == n) rules
          tt = getTerminals cfg
          nt = getNonterminals cfg
          initial :: (Set s', Set n') ->
                     ST ss (STArray ss (Int, Int) (LR1Action n' s'),
                            STArray ss (Int, Int) (Maybe Int))
          initial (tt', nt') = do
            a1 <- newArray ((0, 0), (Set.size nodes - 1, Set.size tt)) Error
            a2 <- newArray ((0, 0), (Set.size nodes - 1, Set.size nt - 1)) Nothing
            return (a1, a2)
          isFinal :: LR1Node n' s' -> Bool
          isFinal (LR1Node rs _ _) = any makesFinal rs
          makesFinal :: LR1Rule n' s' -> Bool
          makesFinal (LR1Rule (Rule _ rhs) n) = length rhs == n
          attemptWriteA1 :: (Eq n, Eq s) =>
                            STArray ss (Int, Int) (LR1Action n s) ->
                            (Int, Int) -> LR1Action n s ->
                            ExceptT String (ST ss) ()
          attemptWriteA1 arr pos act = do
            act0 <- lift $ readArray arr pos
            case act0 of
              Error -> lift $ writeArray arr pos act
              x | x == act -> return ()
                | otherwise -> throwError "Conflict between rules in table!"
          attemptWriteA2 :: STArray ss (Int, Int) (Maybe Int) ->
                            (Int, Int) -> Maybe Int ->
                            ExceptT String (ST ss) ()
          attemptWriteA2 arr pos act = do
            act0 <- lift $ readArray arr pos
            case act0 of
              Nothing -> lift $ writeArray arr pos act
              x | x == act -> return ()
                | otherwise -> throwError "Conflict between gotos in table!"
          doFreeze :: Ix i => STArray ss i e -> ST ss (Array i e)
          doFreeze = freeze
          -- doArrays :: ExceptT String (ST ss)
          --                   (Array (Int, Int) (LR1Action n s),
          --                    Array (Int, Int) (Maybe Int))
          doArrays = do
            (a1, a2) <- lift $ initial (tt, nt)
            forM_ nodes $ \(LR1Node rr tr _) -> do
                       let curr = Set.findIndex (LR1Node rr tr False) nodes
                       -- Shifts and Gotos
                       forM_ tr $ \(char, n) ->
                           case char of
                             Left non -> do
                                       col <- hoistMaybe "Out of bounds!" $
                                               Set.lookupIndex non nt
                                       attemptWriteA2 a2 (curr, col) $ Just n
                             Right ter -> do
                                       col <- hoistMaybe "Out of bounds!" $
                                               Set.lookupIndex ter tt
                                       attemptWriteA1 a1 (curr, col) $ Shift n
                       -- Reduces
                       when (isFinal $ LR1Node rr tr False) $ do
                           forM_ (filter makesFinal rr) $
                             \(LR1Rule rle@(Rule lhs rhs) _) -> do
                               if lhs == st then
                                   attemptWriteA1 a1 (curr, Set.size tt) Accept
                               else do
                                 forM_ (followSet cfg lhs) $ \ch -> do
                                   let err = hoistMaybe "Out of bounds!"
                                   col <- case ch of
                                            ChS ch -> err $ Set.lookupIndex ch tt
                                            EOS -> return $ Set.size tt
                                   attemptWriteA1 a1 (curr, col) $ Reduce rle
            a1' <- lift $ doFreeze a1
            a2' <- lift $ doFreeze a2
            return (a1', a2')
          -- runArrays :: Either String (LR1Table n s)
          runArrays = let nth = Set.findIndex (LR1Node (toRulesT st) [] undefined) nodes
                      in case runST $ runExceptT $ doArrays of
                           Left e -> Left e
                           Right (a1', a2') -> Right $ LR1Table nt tt nth a1' a2'

doLR1Parse :: (Show n, Show s, Ord n, Ord s) =>
              LR1Table n s -> n -> [s] -> Either String (Tree (Either n s))
doLR1Parse (LR1Table nt tt start a1 a2) st ss =
    case doParse (map ChS ss ++ [EOS]) [start] [] [] of
      Right [x] -> Right $ reverseTree x
      Right _ -> Left "Ambiguous tree at end of parse"
      Left e -> Left e
    where -- doParse :: [CorS s] -> [Int] -> [Either n s] -> Forest (Either n s) ->
          --            Either String (Forest (Either n s))
          doParse [] _ _ _ = Left "Out of characters in input string"
          doParse _ [] _ _ = Left "Out of states on stack"
          doParse (x:xs) (n:ns) stack ff =
              let col = case x of
                          EOS -> Set.size tt
                          ChS x -> Set.findIndex x tt
                  ChS x' = x
              in case a1 ! (n, col) of
                   Error -> Left $ "Unexpected " ++ show x
                   Shift n' -> let ff' = Node (Right x') [] : ff
                               in doParse xs (n':n:ns) (Right x' : stack) ff'
                   Reduce (Rule lhs rhs)
                    | take (length rhs) stack /= reverse rhs ->
                        Left $ "Expected " ++ show rhs ++ "; got " ++
                               show (take (length rhs) stack)
                    | otherwise ->
                        let len = length rhs
                            stack' = drop len stack
                            ns' = drop len (n:ns)
                            col' = Set.findIndex lhs nt
                            n' = a2 ! (head ns', col')
                            ff' = (Node (Left lhs) $ take len ff) : drop len ff
                        in case n' of
                             Nothing -> Left $ "No rule for goto on " ++ show lhs
                             Just n' -> doParse (x:xs) (n':ns') (Left lhs:stack') ff'
                   Accept -> Right [Node (Left st) ff]
          reverseTree (Node x ys) = Node x (map reverseTree $ reverse ys)

doLR1Parse' :: (Show n, Show s, Ord n, Ord s) =>
              CFG n s -> [s] -> Either String (Tree (Either n s))
doLR1Parse' (CFG rules st) ss = do
  table <- buildLR1Table $ CFG rules st
  doLR1Parse table st ss

{-
data LR1Rule n s = LR1Rule (Rule n s) Int
                   deriving (Show, Read, Eq, Ord)
data LR1Prim n s = LR1Prim [LR1Rule n s] [(Either n s, LR1Prim n s)]
data LR1Node n s = LR1Node [LR1Rule n s] [(Either n s, Int)] Bool
                   deriving (Show, Read)
data LR1Table n s = LR1Table (Set n) (Set s) Int (Array (Int, Int) (LR1Action n s))
                                                 (Array (Int, Int) (Maybe Int))
                    deriving (Show, Read, Eq)
data LR1Action n s = Error | Shift Int | Reduce (Rule n s) | Accept
                     deriving (Show, Read, Eq)
-}

nonrec :: CFG Char Char
nonrec = CFG [
          Rule 'S' [Right 'x', Left 'A'],
          Rule 'A' [Right 'y']
         ] 'S'

grammar :: CFG Char Char
grammar = CFG [
           Rule 'S' [Left 'A', Left 'B'],
           Rule 'A' [Right 'x', Left 'A'],
           Rule 'A' [],
           Rule 'B' [Right 'y', Left 'B'],
           Rule 'B' []
          ] 'S'

notLL1 :: CFG Char Char
notLL1 = CFG [
          Rule 'S' [Left 'A'],
          Rule 'S' [Right 'x'],
          Rule 'A' [Right 'x']
         ] 'S'

-- Treats uppercase letters as nonterminals, S as start symbol, and
-- all other characters as literals
parseGrammar :: [(Char, String)] -> CFG Char Char
parseGrammar = (`CFG` 'S') . map (uncurry $ \lhs -> Rule lhs . map liftToG)
    where liftToG ch
              | isUpper ch = Left ch
              | otherwise = Right ch

printNodeSet :: (Show n, Show s, Ord n, Ord s) => Set (LR1Node n s) -> IO ()
printNodeSet ss = do
  let xs = Set.toList ss
  forM_ xs $ \(LR1Node ys tr _) -> do
                    putStrLn $ show ys ++ " <> " ++ show tr
