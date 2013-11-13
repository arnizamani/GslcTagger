{-
    GslcTagger: Parts-of-speech tagger for GSLC corpus of spoken Swedish
    Copyright (C) 2013  Abdul Rahim Nizamani, University of Gothenburg

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
-}

{-# LANGUAGE FlexibleInstances #-}

module Main where

import System.Directory
import Prelude hiding (appendFile, readFile, writeFile)
import System.IO.UTF8 (appendFile, readFile, writeFile,hGetContents)
import qualified System.IO.UTF8 as U
import qualified System.IO as IO
import Data.List
import Control.Arrow ((&&&),(***),second)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Control.Parallel.Strategies
import Data.Char (isAlpha, isSpace, isDigit)
import Text.ParserCombinators.ReadP hiding (count)
import System.Environment (getArgs, getProgName)
import System.Time
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Maybe
import Control.Monad (join)
import Data.Function (on)
import Control.Exception 

-- Current version number
pversion = "0.2.1" -- modified 2013-11-13

-- | ? instead of if..then..else
infixr 1 ?
(?) True  x _ = x
(?) False _ y = y

notnull = not . null

-- | trims a string
wschars = " \t\r\n"
strip :: String -> String
strip = lstrip . rstrip
lstrip s = case s of
                  [] -> []
                  (x:xs) -> if elem x wschars
                            then lstrip xs
                            else s
rstrip = reverse . lstrip . reverse

bigrams :: [a] -> [(a,a)]
bigrams (_:[]) = []
bigrams x = zip x (tail x)

-- map and then filter in one run, reduces complexity from 2n to n
mapfilter :: (a -> b) -> (b -> Bool) -> [a] -> [b]
mapfilter _ _ [] = []
mapfilter m f (x:xs) = f result ? (result:(mapfilter m f xs)) $ (mapfilter m f xs)
                 where result = m x

defaultTag = "noun"
foreignTag = "uo"

maxRules = 5000

function x y = do
    text <- readFile x
    let t1 = unlines
             . map unwords
             . concat
             . map (\(word,tags) -> map (\t -> (word:t)) tags)
             . map (\x -> (head (head x),mergetags (map tail x)) ) -- [(String, [[String]])]
             . groupBy ((==) `on` head) -- [[[String]]]
             . map words  -- [[String]]
             $ lines text -- [String]
    writeFile y t1
    
mergetags xs =  map (\(x,y) -> [x,show y])
                . reverse
                . sortBy (compare `on` snd)
                . map (\x -> (fst (head x), sum (map snd x)))
                . groupBy ((==) `on` fst) -- [  [(String,Integer)]  ]
                . sortBy (compare `on` fst) -- [(String,Integer)]
                $ map (\[x,y] -> (x, (read y :: Integer))) xs

tagmap = Map.fromList [("uo",   "uo"  ),
                       ("ab",   "adv" ),
                       ("an",   "noun"),
                       ("jj",   "adj" ),
                       ("pc",   "adj" ),
                       ("ha",   "adv" ),
                       ("hs",   "adv" ),
                       ("pl",   "adv" ),
                       ("in",   "int" ),
                       ("kn",   "conj"),
                       ("sn",   "conj"),
                       ("nn",   "noun"),
                       ("pm",   "noun"),
                       ("rg",   "num" ),
                       ("ro",   "num" ),
                       ("vb",   "verb"),
                       ("ie",   "conj"),
                       ("pp",   "prep"),
                       ("dt",   "pron"),
                       ("hd",   "pron"),
                       ("pn",   "pron"),
                       ("ps",   "pron"),
                       ("hp",   "pron"),
                       ("adj",  "adj" ),
                       ("adv",  "adv" ),
                       ("fb",   "fb"  ),
                       ("int",  "int" ),
                       ("conj", "conj"),
                       ("noun", "noun"),
                       ("num",  "num" ),
                       ("ocm",  "ocm" ),
                       ("pron", "pron"),
                       ("prep", "prep"),
                       ("verb", "verb")]
type Word = String
type Tag = String

type Bigram = Map Word ([Word], [Word])
type Count = Map Word (Map Tag Int)

-- check one tag back or forward
-- any tag upto given length back or forward
-- all tags back or forward
data Context x =   OneW Int Word -- The word is w
                 | One Int x   -- The prev/next tag is t
                 | Any Int x   -- Any prev/next tag is t
                 | All Int (Vector x) -- All prev/next tags
                 | Both x x    -- Preceding tag and following tag
                 | BothW Word Int Word -- Current word and next/prev word
                 | BothT Word Int x    -- Current word and next/prev tag
    deriving (Eq)

data Unit a = Unit {word :: Word, ptag :: a, rtag :: a}

data Rule a = R (Maybe a) [Context a] a
    deriving (Eq, Ord)

data URule a = U (Maybe a) UContext a
    deriving (Eq, Ord)

data UContext =
      -- the current word is w
      CurrentWord Word
      -- The first 1,2,3,4 characters of a word are x
    | Prefix String
      -- The last 1,2,3,4 characters of a word are x
    | Suffix String
    -- Deleting the prefix x, |x|<=4, results in a word
    | DelPrefix String
      -- Deleting the suffix x, |x|<=4, results in a word
    | DelSuffix String
      -- Adding the character string x as a suffix results in a word (|x|<=4)
    | AddSuffix String
      -- Adding the character string x as a prefix results in a word (|x|<=4)
    | AddPrefix String
      -- Word w ever appears immediately to the left of the word
    | LeftWord Word 
      -- Word w ever appears immediately to the right of the word
    | RightWord Word 
      -- character z appears in the word
    | Appears Char
        deriving (Eq, Ord)
-- Initial statistics of the training corpus
--   includes: most frequent tag for every word

-- a tagger contains initial statistics, default tag, and set of patches/rules
type Tagger = ((Count,Tag),[Rule String])

newtag x = case Map.lookup x tagmap of
                Nothing -> defaultTag
                Just tag -> tag

getTags :: Count -> [Tag]
getTags m = nub . map fst . concatMap Map.toList . map snd $ Map.toList m

makeURules :: Ord a => Vector (Vector (Unit a)) -> Count -> Count -> Bigram -> [URule a]
makeURules v count1 count2 bigrams = rulesJust -- ++ rulesNothing
  where
    rulesNothing = nub $ map (\(U _ c t2) -> U Nothing c t2) rulesJust
    rulesJust = nub . concat $ rules
    rules = [ map (\c -> U (Just t1) c t2) $
                     [Prefix (take n cword) | n <- range]
                  ++ [Suffix (takeEnd n cword) | n <- range]
                  ++ [DelPrefix (take n cword) | n <- range, (drop n cword) `Map.member` count2]
                  ++ [DelSuffix (takeEnd n cword) | n <- range, dropEnd n cword `Map.member` count2]
                  ++ [LeftWord w | w <- (length leftw < 10 ? leftw $ [])]
                  ++ [RightWord w | w <- (length rightw < 10 ? rightw $ [])]
                  ++ [CurrentWord cword]
                  ++ map Appears cword
                  ++ ( map AddSuffix . nub
                     . filter (\x -> notnull x && length x <= 4)
                     . map (drop (length cword))
                     . filter (isPrefixOf cword) $ allwords)
                  ++ ( map AddPrefix . nub
                     . filter (\x -> notnull x && length x <= 4)
                     . map (dropEnd (length cword))
                     . filter (isSuffixOf cword) $ allwords)
                | ((t1,t2),indexes) <- indices,
                  (l,w) <- indexes,
                  let line = V.unsafeIndex v l,
                  let len = V.length line,
                  let cword = word (V.unsafeIndex line w),
                  let range = [1..(min 4 (length cword - 1))],
                  let leftw  = maybe [] fst $ Map.lookup cword bigrams,
                  let rightw = maybe [] snd $ Map.lookup cword bigrams
            ]
    indices = unknownIndices v count1
    allwords = map fst $ Map.toList count2

takeEnd :: Int -> [a] -> [a]
takeEnd n list = reverse $ take n $ reverse list
dropEnd :: Int -> [a] -> [a]
dropEnd n list = reverse $ drop n $ reverse list

makeRules :: Ord a => Vector (Vector (Unit a)) -> [Rule a]
makeRules v = nub . concat $ rules
  where
    rules = [ [R (Just t1) [One  i (ptag (V.unsafeIndex line (w+i)))] t2
                    | i <- [0,1,-1,2,-2,3,-3], (w+i) >= 0, (w+i) < len ]
              ++ [R (Just t1) [OneW i (word (V.unsafeIndex line (w+i)))] t2
                    | i <- [0,1,-1,2,-2], (w+i) >= 0, (w+i) < len]
              ++ [R (Just t1) [Both (ptag (V.unsafeIndex line (w-1))) (ptag (V.unsafeIndex line (w+1)))] t2
                    | w > 0, (w+1) < len]
              ++ [R (Just t1) [Any  i (ptag tag)] t2
                    | i <- [2,3,-2,-3],
                      w >= (i < 0 ? abs i $ 0),
                      w < (i > 0 ? len - i $ len ),
                      tag <- V.toList (V.unsafeSlice (w+(i<0 ? i $ 1)) (abs i) line) ]
              ++ [R (Just t1) [All  i (V.map ptag $ (V.unsafeSlice (w+(i<0 ? i $ 1)) (abs i) line))] t2
                    | i <- [2,3,-2,-3],
                      w >= (i < 0 ? abs i $ 0),
                      w < (i > 0 ? len - i $ len) ]
              ++ [R (Just t1) [BothW cword i (word (line V.! (w+i)))] t2
                    | i <- [1,-1],
                      w >= (i<0 ? (abs i) $ 0),
                      w < (i>0 ? len - i $ len ) ]
              ++ [R (Just t1) [BothT cword i (ptag (line V.! (w+i)))]  t2
                    | i <- [1,-1],
                      w >= (i<0 ? (abs i) $ 0),
                      w < (i>0 ? len - i $ len ) ]
              | ((t1,t2),indexes) <- errorIndices v,
                (l,w) <- indexes,
                let line = v V.! l,
                let len = V.length line,
                let cword = word ((v V.! l) V.! w)
            ]

-- Wrong tags with their indices        
errorIndices :: Ord a => Vector (Vector (Unit a)) -> [((a,a),[(Int,Int)])]
errorIndices corpus = 
    map (\l -> (fst (head l),map snd l)) . groupBy ((==) `on` fst) . sortBy (compare `on` fst) $ indices
  where
    indices = [ ((t1,t2), (l,w))
                 | (l,v) <- V.toList (V.indexed corpus),
                   (w,(Unit _ t1 t2)) <- V.toList (V.indexed v),
                   t1 /= t2
                 ]

-- Wrong tags of unknown words with their indices
unknownIndices :: Ord a => Vector (Vector (Unit a)) -> Count -> [((a, a),[(Int,Int)])]
unknownIndices corpus count = 
    map (\l -> (fst (head l),map snd l)) . groupBy ((==) `on` fst) . sortBy (compare `on` fst) $ indices
  where
    indices = [ ((t1, t2), (l,w))
                 | (l,v) <- V.toList (V.indexed corpus),
                   (w,(Unit word t1 t2)) <- V.toList (V.indexed v),
                   t1 /= t2,
                   not (word `Map.member` count)
                 ]
    t1map = Map.fromList . map (\x -> (x,1)) . V.toList . join
            $ V.map (V.map ptag . V.filter (\(Unit w t1 t2) -> t1 /= t2)) corpus

safeSlice :: Int -> Int -> Vector a -> Vector a
safeSlice start len v | (start+len) < 1 = V.empty
safeSlice start len v | start < 0 = safeSlice 0 (start+len) v
safeSlice start len v | (start+len) > V.length v = safeSlice (start) (V.length v - start) v
safeSlice start len v = V.slice start len v

-- score of a URule, 1 for a correct change, -1 for an incorrect change
scoreU :: Eq a => URule a -> Vector (Vector (Unit a)) -> Count -> Count -> Int
scoreU r v count1 count2 = V.sum $ V.map (scoreU' r count1 count2) v

scoreU' :: Eq a => URule a -> Count -> Count -> Vector (Unit a) -> Int
scoreU' (U t1 c t2) count1 count2 v = 
    V.sum $ V.imap (\i a -> if maybe True (==ptag a) t1 && maybe True (/=t2) t1 && matchesU c i (word a) && not (word a `Map.member` count1)
                               then rtag a == t2 ? 1 $ -1
                               else 0) v
  where
    matchesU (Prefix    s) _ w = isPrefixOf s w && length w > length s
    matchesU (Suffix    s) _ w = isSuffixOf s w && length w > length s
    matchesU (DelPrefix s) _ w = isPrefixOf s w && (drop (length s) w) `Map.member` count2
    matchesU (DelSuffix s) _ w = isSuffixOf s w && (dropEnd (length s) w) `Map.member` count2
    matchesU (AddSuffix s) _ w = (w ++ s) `Map.member` count2
    matchesU (AddPrefix s) _ w = (s ++ w) `Map.member` count2
    matchesU (LeftWord  s) i _ = fmap word (v V.!? (i-1)) == Just s
    matchesU (RightWord s) i _ = fmap word (v V.!? (i+1)) == Just s
    matchesU (CurrentWord s) _ w = s == w
    matchesU (Appears   s) _ w = s `elem` w

-- score of a rule, 1 for a correct change, -1 for an incorrect change
score :: Eq a => Rule a -> Vector (Vector (Unit a)) -> Int
score r v = V.sum $ V.map (score' r) v

score' :: Eq a => Rule a -> Vector (Unit a) -> Int
score' (R t1 contexts t2) v = 
    V.sum $ V.imap (\i' a -> if maybe True (==ptag a) t1 && all (\c -> matches c i' a v) contexts
                               then rtag a == t2 ? 1 $ -1
                               else 0) v
  where
    matches (OneW i w)       i' _ v | (i'+i) >= 0 && (i'+i) < V.length v
                                      = word (V.unsafeIndex v (i'+i)) == w
    matches (One  i tag)     i' _ v | (i'+i) >= 0 && (i'+i) < V.length v
                                      = ptag (V.unsafeIndex v (i'+i)) == tag
    matches (Both tag1 tag2) i' _ v | i' > 0 && (i'+1) < V.length v
                                      = (ptag (V.unsafeIndex v (i'-1)) == tag1) && (ptag (V.unsafeIndex v (i'+1)) == tag2)
    matches (BothW w1 i w2)  i' w v | (i'+i) >= 0 && (i'+i) < V.length v
                                      = (word w == w1) && (word (V.unsafeIndex v (i'+i)) == w2)
    matches (BothT w1 i tag) i' w v | (i'+i) >= 0 && (i'+i) < V.length v
                                      = (word w == w1) && (ptag (V.unsafeIndex v (i'+i)) == tag)
    matches (Any i tag)      i' _ v | i < 0 && i' >= (abs i) && i' < V.length v
                                      = V.any (==tag) (V.map ptag  (V.unsafeSlice (i'+i) (abs i) v))
    matches (Any i tag)      i' _ v | i >=0 && i' >= 0 && i' < (V.length v - i)
                                      = V.any (==tag) (V.map ptag $ V.unsafeSlice (i'+1) i v)
    matches (All i tags)     i' _ v | i < 0 && i' >= (abs i) && i' < V.length v
                                      = tags == (V.map ptag  (V.unsafeSlice (i'+i) (abs i) v))
    matches (All i tags)     i' _ v | i >=0 && i' >= 0 && i' < (V.length v - i)
                                      = tags == (V.map ptag  (V.unsafeSlice (i'+1) i v))
    matches _ _ _ _                   = False

-- apply URule (for unknown words)
applyU :: Eq a => URule a -> Count -> Count -> Vector (Vector (Word,a)) -> Vector (Vector (Word,a))
applyU r c1 c2 v = V.map (applyU' r c1 c2) v

applyU' :: Eq a => URule a -> Count -> Count -> Vector (Word,a) -> Vector (Word,a)
applyU' (U t1 c t2) c1 c2 v = 
    V.imap (\i (w,a) -> if maybe True (==a) t1 && maybe True (/=t2) t1 && match c i w && not (w `Map.member` c1)
                        then (w,t2)
                        else (w,a)) v
  where
    match (Prefix    s) i w = isPrefixOf s w && length w > length s
    match (Suffix    s) i w = isSuffixOf s w && length w > length s
    match (DelPrefix s) i w = isPrefixOf s w && (drop (length s) w) `Map.member` c2
    match (DelSuffix s) i w = isSuffixOf s w && (dropEnd (length s) w) `Map.member` c2
    match (AddSuffix s) i w = (w ++ s) `Map.member` c2
    match (AddPrefix s) i w = (s ++ w) `Map.member` c2
    match (LeftWord  s) i w = fmap fst (v V.!? (i-1)) == Just s
    match (RightWord s) i w = fmap fst (v V.!? (i+1)) == Just s
    match (CurrentWord s) _ w = s == w
    match (Appears   s) i w = s `elem` w

-- Vector-based rule application
applyV :: Eq a => Rule a -> Vector (Vector (Word,a)) -> Vector (Vector (Word,a))
applyV r = V.map (applyV' r)

applyV' :: Eq a => Rule a -> Vector (Word,a) -> Vector (Word,a)
applyV' (R t1 contexts t2) v = 
    V.imap (\i' (w,a) -> if maybe True (==a) t1
                               && all (\c -> matches2 c i' w v) contexts
                            then (w,t2)
                            else (w,a)) v
  where
    matches2 (OneW i w)       i' _ v | (i'+i) >= 0 && (i'+i) < V.length v
                                   = fst (V.unsafeIndex v (i'+i)) == w
    matches2 (One  i tag)     i' _ v | (i'+i) >= 0 && (i'+i) < V.length v
                                   = snd (V.unsafeIndex v (i'+i)) == tag
    matches2 (Both tag1 tag2) i' _ v | i' > 0 && (i'+1) < V.length v
                                   = (snd (V.unsafeIndex v (i'-1)) == tag1)
                                     && (snd (V.unsafeIndex v (i'+1)) == tag2)
    matches2 (BothW w1 i w2)  i' w v | (i'+i) >= 0 && (i'+i) < V.length v
                                   = (w == w1) && (fst (V.unsafeIndex v (i'+i)) == w2)
    matches2 (BothT w1 i tag) i' w v | (i'+i) >= 0 && (i'+i) < V.length v
                                   = (w == w1) && (snd (V.unsafeIndex v (i'+i)) == tag)
    matches2 (Any i tag)      i' _ v | i < 0 && i' >= (abs i) && i' < V.length v
                                   = V.any (==tag) (V.map snd  (V.unsafeSlice (i'+i) (abs i) v))
    matches2 (Any i tag)      i' _ v | i >=0 && i' >= 0 && i' < (V.length v - i)
                                   = V.any (==tag) (V.map snd $ V.unsafeSlice (i'+1) i v)
    matches2 (All i tags)     i' _ v | i < 0 && i' >= (abs i) && i' < V.length v
                                   = tags == (V.map snd  (V.unsafeSlice (i'+i) (abs i) v))
    matches2 (All i tags)     i' _ v | i >=0 && i' >= 0 && i' < (V.length v - i)
                                   = tags == (V.map snd  (V.unsafeSlice (i'+1) i v))
    matches2 _ _ _ _               = False

removeBlankLines :: String -> String
removeBlankLines = unlines . filter (/="") . lines

getPOS :: (String,String) -> (String,String,Int)
getPOS (a,b) | a == "" = ("","",0)
getPOS (a,b) | b == "" = (a,"",1)
getPOS (a,b) | (take 2 b) /= "(\"" = (a,"",2)
getPOS (a,b) = (a,b',i)
  where
    c = words b
    (b',i) = if (length c > 1) then (clear (head (tail c)),3) else ("",4)
    clear s = if last s == ')' then init s else s

frequency :: Ord a => [a] -> [(a,Int)]
frequency = map (\x -> (head x, length x)) . reverse . sortBy (compare `on` length) . group . sort

getWord :: String -> String
getWord s = if s' /= "" then reverse (tail s') else ""
    where s' = dropWhile (/='/') $ reverse s

getTag :: String -> String
getTag s = if((strip s)==s') then "" else s'
    where s' = reverse . takeWhile (/='/') $ reverse (strip s)

types :: [String] -> [String]
types xs =  undefined $ map (getWord) xs

compareV :: Eq a => Vector (Vector (Word,a)) -> Vector (Vector (Word,a)) -> Count -> IO ()
compareV test tagged count = do
    let testWords   = join $! test
    let taggedWords = join $! tagged
    let z = V.zip testWords $! taggedWords
    
    let known' = V.filter (\(x,y) -> (Map.member x count)) $! testWords
    let unknown' = V.filter (\(x,y) -> not (Map.member x count)) $! testWords
    let known = V.length known'
    let unknown = V.length unknown'
    
    let knownCorrect = V.length . V.filter (\((a,b),(x,y)) -> if a == x && Map.member a count then b == y else False) $ z
    let unknownCorrect = V.length . V.filter (\((a,b),(x,y)) -> if a == x && not (Map.member a count) then b == y else False) $ z
    let correct = knownCorrect + unknownCorrect
    -- let correct2 = length . filter (\((a,b),(x,y)) -> a == x && b == y) $ z
    let correct2 = V.length . V.filter (\(a,b) -> a == b) $! V.zip testWords taggedWords
    let l = V.length taggedWords
    putStrLn $ show knownCorrect ++  " known correct out of  " ++ show known ++ ", %=" ++ show ((fromIntegral  knownCorrect) / (fromIntegral  known) * 100)
    putStrLn $ show unknownCorrect ++ " unknown correct out of " ++ show unknown ++ ", %=" ++ show ((fromIntegral  unknownCorrect) / (fromIntegral  unknown) * 100)
    putStrLn $ show correct ++ " correct out of " ++ show l ++ ", %=" ++ show ((fromIntegral  correct) / (fromIntegral  l) * 100)
    putStrLn $ show correct2

compareTags t1 t2 = t1 == t2

threeLetters :: [[Word]] -> [(Word,Tag)]
threeLetters words' = 
    map (\x -> (fst (head x),
                                (
                                 head
                                . head
                                . reverse
                                . sortBy (compare `on` length)
                                . group
                                . sort
                                . map snd $ x)))
    . groupBy (\x y -> fst x == fst y)
    . sortBy (compare `on` fst)
    . map (\(x,y) -> ((reverse . take 3 . reverse $ x),y))
    . filter (\(x,y) -> length x > 3 && y /= "")
    . map breakWordTag
    . concat
    $ words'

allbigrams :: [[Token]] -> [(Token,Token)]
allbigrams = concat . filter notnull . map bigrams

breakWordTag :: Token -> (Word,Tag)
breakWordTag = getWord &&& getTag

type Token = String

getCount :: [[Word]] -> [(Word,Map.Map Tag Int)]
getCount words' = 
          map (\(a,b) -> (a, (getTagMap b)) )
        . map (\x -> ( fst (head x) , map snd x ) )
        . groupBy (\x y -> fst x == fst y)
        . sortBy (compare `on` fst)
        . filter (\(x,y) -> x /= "" && y /= "")
        . map breakWordTag
        . concat
        $ words'

getTagMap :: [Tag] -> Map.Map Tag Int
getTagMap = Map.fromList . frequency

-- get most frequent tags for each word
gettags :: [[Word]] -> [(Word,Tag)]
gettags words' = map (\x -> (fst (head x),
                                (
                                 head
                                . head
                                . reverse
                                . sortBy (compare `on` length)
                                . group
                                . sort
                                . map snd $ x)))
                . groupBy (\x y -> fst x == fst y)
                . sortBy (compare `on` fst)
                . filter (\(x,y) -> x /= "" && y /= "")
                . map breakWordTag
                . concat
                $ words'

-- get initially tagged content
initialTagger :: Count -> Map String (String,Int) -> Vector Word -> Vector (Word,Tag)
initialTagger _ _ v | V.length v == 1 && head (V.toList v) == "ha" = V.singleton ("ha","fb")
initialTagger _ _ v | V.length v == 1 && head (V.toList v) == "bra" = V.singleton ("bra","fb")
initialTagger tagger fcount v =
    V.length v > 3
      && V.length (V.filter (==True) $ V.map (\x -> Map.member x fcount) v) > 2 -- if all words are foreign
      && V.all (\x -> Map.member x fcount || isNumber x || not (Map.member x tagger)) v
        ? (V.map tagforeign v)
        $ (V.map tagword v)
  where
    -- tag foreign word
    tagforeign "" = ("","")
    tagforeign x | notnull x && (last x == '+') = (x,"ocm")
    tagforeign y@(x:xs) | (x == '+') = (y,"ocm")
    tagforeign x | isNumber x = (x,"num")
    tagforeign x = case Map.lookup x fcount of
                        Just (tg,_) -> (x,tg)
                        Nothing -> case Map.lookup x tagger of
                                    Nothing  -> (x,defaultTag)
                                    Just tmap -> (x,getMostFrequent x tmap fcount)
    tagword x | notnull x && (last x == '+') = (x,"ocm")
    tagword y@(x:xs) | (x == '+') = (y,"ocm")
    tagword x = (x,tag x)
    
    tag "" = ""
    tag x | isNumber x = "num"
    tag x = case Map.lookup x tagger of
              Nothing -> case Map.lookup x fcount of   -- unknown word
                            Nothing -> case (Map.lookup (filter (/=':') x) tagger) of
                                        Nothing -> defaultTag
                                        Just tagmap' -> getMostFrequent x tagmap' fcount
                            Just (tg,_) -> tg
              Just tagmap' -> let tg = getMostFrequent x tagmap' fcount -- known word
                              in if tg /= foreignTag && tg /= defaultTag
                                   then tg
                                   else case Map.lookup x fcount of
                                          Nothing -> defaultTag
                                          Just (tg',_) -> tg'

getMostFrequent :: Word -> Map Tag Int -> Map String (String,Int) -> Tag
getMostFrequent _ tagmap' _ | Map.null tagmap' = defaultTag
getMostFrequent x tagmap' fcount =
        let (tag,count) = maximumBy (compare `on` snd) . Map.toList $ tagmap'
            -- (tg,fc) = case Map.lookup x fcount of
            --            Nothing -> ("nil",0)
            --            Just (tg,c) -> (tg,c)
            -- tag = if tag'==tg then (fc > count ? tg $ tag') else tag'
        in if tag == "" then defaultTag else tag

isNumber x = case reverse (reads x :: [(Number,String)]) of
                    ((_,""):_) -> True
                    _          -> False

main :: IO ()
main = do
    args <- getArgs
    prg <- getProgName 
    if null args
    then printMsg prg
    else do
    if "--help" `elem` args || "-h" `elem` args
    then printHelp prg
    else do
    case (head args) of
        "count"   -> count (tail args)
        "update"  -> update (tail args)
        "merge"   -> merge (tail args)
        -- "bigrams" -> bigram (tail args)
        -- "unknown" -> unknown (tail args)
        "train"   -> train (tail args)
        "run"     -> run (tail args)
        "compare" -> compareResult (tail args)
        "stats"   -> do
            let filename = head (tail args)
            count <- readCount filename
            putStrLn $ "Types: " ++ show (Map.size count)
            putStrLn $ "Words: " ++ show (Map.fold (\m v -> v + Map.fold (\i j -> i + j) 0 m) 0 count)
            putStrLn $ "Tags: "
            mapM putStrLn . map show $ Map.toList $ (Map.fold (\m v -> Map.unionWith (+) m v) Map.empty count)
            return ()
        "freq"      -> do 
            let [tag,countfile,outfile] = drop 1 $ take 4 args
            count <- readCount countfile
            let c = Map.toList count
            let total = sum $ concat [[tint | (_,tint) <- Map.toList t] | (_,t) <- c]
            let wlist = [(word, tmap Map.! tag) | (word,tmap) <- c, Map.member tag tmap]
            let result = reverse $ sortBy (compare `on` snd) wlist
            let printed = unlines
                            $ map (\(w,t) -> w ++ " " ++ show t ++ " "
                                            ++ show ((fromIntegral t)/(fromIntegral total)*100.0))
                            $ result
            writeFile outfile printed
            putStrLn $ show (length result) ++ " words tagged as " ++ tag
        _         -> printHelp prg



count, update, merge, bigram, unknown, train, run :: [String] -> IO ()
count args | length args < 2 =
    putStrLn "Invalid arguments. Read the program help."
count (trainfile:ofile:_) = do
    training <- readFile' trainfile
    let twords = map words $ lines training
    let count = Map.fromList (getCount twords)
    writeCount count ofile
    putStrLn $ "Count file created: " ++ ofile

update (cfile:trainfile:_) = do
    count1 <- readCount cfile
    putStrLn $ "Count 1 size is: " ++ show (Map.size count1)
    training <- readFile' trainfile
    let twords = map words $ lines training
    let count2 = Map.fromList (getCount twords)
    putStrLn $ "Count 2 size is: " ++ show (Map.size count2)
    let count3 = mergeCounts count1 count2
    putStrLn $ "New count size is " ++ show (Map.size count3)
    writeCount count3 cfile
    putStrLn $ "Count file updated: " ++ cfile

merge (cfile:newfile:_) = do
    count1 <- readCount cfile
    putStrLn $ "Count 1 size is: " ++ show (Map.size count1)
    count2 <- readCount newfile
    putStrLn $ "Count 2 size is: " ++ show (Map.size count2)
    let count3 = mergeCounts count1 count2
    putStrLn $ "New count size is " ++ show (Map.size count3)
    writeCount count3 cfile
    putStrLn $ "Count file updated: " ++ cfile

bigram args | length args < 2 = printInvalidError
bigram (trainfile:ofile:_) = do
    training <- readFile trainfile
    let twords = map2 getWord . map words . filter notnull . map strip $ lines training
    putStrLn $ "Words : " ++ show (sum . map length $ twords)
    let types = Map.fromList . map (\w -> (w,1)) $ concat twords
    putStrLn $ "Types : " ++ show (Map.size types)
    let big = map fst . Map.toList . Map.fromList . map (\x -> (x,1))
                $ concatMap (\x -> zip x (tail x)) twords
    putStrLn $ "bigrams : " ++ show (length big)
    
    writeFile ofile $ unlines $ map (\(x,y) -> x ++ " " ++ y) big
    putStrLn $ "Bigram file created: " ++ ofile

readBigrams :: FilePath -> IO Bigram
readBigrams f = do
    text <- readFile' f
    if null text
    then return Map.empty
    else do
    let big = map (\(x:y:_) -> (x,y)) . filter (\x -> length x > 1)
                . map words . filter notnull . map strip . lines $ text
    let types = Map.fromList . map (\w -> (w,1)) $ concatMap (\(x,y) -> [x,y]) big
    let bigleft = map (\list -> (snd (head list),map fst list))
                    . filter notnull . groupBy ((==) `on` snd)
                    $ sortBy (compare `on` snd) big
    let bigright = map (\list -> (fst (head list),map snd list))
                    . filter notnull . groupBy ((==) `on` fst)
                    $ sortBy (compare `on` fst) big
    let leftmap = Map.fromList bigleft
    let rightmap = Map.fromList bigright
    let bigmap = Map.mapWithKey (\w _ -> (if Map.member w leftmap  then leftmap  Map.! w else [],
                                          if Map.member w rightmap then rightmap Map.! w else [])) types
    return bigmap
    
catchIO :: a -> IOException -> IO a
catchIO x _ = return x

unknown args | length args < 4 = printInvalidError
unknown (cfile:bfile:pfile:ofile:_) = do
    count <- readCount cfile
    putStrLn $ "Count size: " ++ show (Map.size count)
    big <- readBigrams bfile
    putStrLn $ "Bigrams: " ++ show (Map.size big)
    patch <- readFile' pfile
    text <- readFile' ofile
    let lines' = filter (\x -> notnull x && take 1 x /= "#")
                 . map strip . lines $ text
    let patches = map (\x -> read x :: (URule String)) $ lines'
    
    let ptokens' =  V.fromList
                    . map (\line -> V.fromList . map (getWord &&& (newtag . getTag)) $ words line)
                    . lines $ patch
    let ptokens = join ptokens' -- :: Vector (Word,Tag)
    putStrLn $ show (V.length ptokens) ++ " words in patch corpus"
    
    -- tag logic
    let ptags = V.map snd $ ptokens -- :: Vector Tag
    let ctags = getTags count       -- :: [Tag]
    let tags = filter (not . null) . nub $ (V.toList ptags) ++ ctags -- :: [Tag] unique tags
    let tagint = IntMap.fromList $ zip [1..] tags -- :: IntMap Int Tag
    let tagmap' =    Map.fromList $ zip tags [1..] -- :: Map Tag Int
    putStrLn $ show (length tags) ++ " tags: " ++ show tags
    putStrLn $ "Count: " ++ show (Map.size count)
    let pwords' = V.map (V.map fst) ptokens'
    
    --let icorpus' =  V.map (V.map (\x -> (x,"noun"))) pwords'
    --let icorpus'' = applyURules (patches) Map.empty count icorpus'    
    let icorpus' =  V.map (initialTagger count Map.empty) pwords'
    let icorpus'' = V.map (applyURules (patches) count count) icorpus'    
    
    let ptagsint = map (\x -> tagmap' Map.! x) (V.toList ptags)
    let icorpusint' = V.map (V.map (second (tagmap' Map.!))) icorpus''
    let pcorpusint' = V.map (V.map (second (tagmap' Map.!))) ptokens'
    start <- getClockTime
    rules <- unknownPatches tagint pcorpusint' icorpusint' ofile count count big
    --rules <- unknownPatches tagint pcorpusint' icorpusint' ofile Map.empty count big
    end <- getClockTime
    putStrLn $ show (length rules) ++ " new patches found."
    putStrLn $ "time: " ++ timeDiffToString (diffClockTimes end start)

train args = do -- (cfile:ufile:pfile:ofile:ffile:_) = do
    ofile <- parseArgs args "r"
    cfile <- parseArgs args "c"
    ufile <- parseArgs args "u"
    ffile <- parseArgs args "f"
    pfile <- parseArgs args "i"

    count <- readCount cfile
    
    -- read and parse lexical rules
    urules <- do utext <- readFile' ufile
                 if notnull utext
                 then do
                    let urules' = map (\x -> read x :: (URule String))
                                . filter (\x -> (not . null) x && take 1 x /= "#")
                                . map strip . lines $ utext
                    putStrLn $ show (length urules') ++ " unknown rules read."
                    return urules'
                 else  return []
    
    cf <- do file <- readFile' ffile
             if notnull file
             then do
                let fc = Map.fromList
                            . map (\(x:y:z:_) -> (x,(y,(read z :: Int))))
                            . map words $ lines file
                return fc
             else return Map.empty
    patch <- readFile' pfile
    text  <- readFile' ofile
    let lines' = filter (\x -> (not . null) x && take 1 x /= "#")
                 . map strip
                 . lines
                 $ text
    let patches = map (\x -> read x :: (Rule String)) $ lines'
    
    let ptokens' =  V.fromList
                    . map (\line -> V.fromList . map (getWord &&& getTag) $ words line)
                    . lines $ patch
    let ptokens = join ptokens' -- :: Vector (Word,Tag)
    putStrLn $ show (V.length ptokens) ++ " words in patch corpus"
    
    -- tag logic
    let ptags = V.map snd $ ptokens -- :: Vector Tag
    let ctags = getTags count       -- :: [Tag]
    let tags = filter (not . null) . nub $ (V.toList ptags) ++ ctags -- :: [Tag] unique tags
    let tagint = IntMap.fromList $ zip [1..] tags -- :: IntMap Int Tag
    let tagmap' =    Map.fromList $ zip tags [1..] -- :: Map Tag Int
    putStrLn $ show (length tags) ++ " tags: " ++ concat (map (\t -> show t ++ ", ") tags)
    let pwords = V.map (V.filter notnull . V.map fst) ptokens'
    let icorpus1 =  seq pwords $ V.map (initialTagger count cf) pwords 
    putStrLn $ show $ V.sum $ V.map V.length icorpus1
    --let icorpus2 = seq icorpus1 $ applyURules urules count count icorpus1
    let icorpus2 = foldl (\c r -> selfseq $ applyU r count count c) icorpus1 urules
    let icorpus3 = seq icorpus2 $ applyPatches count (patches) icorpus2
    let itags = seq icorpus3 (V.map snd . join $ icorpus3)
    
    let errors = V.length . V.filter (\(x,y) -> x /= y) $ V.zip ( itags) ptags
    putStrLn $ "Errors after initial tagging: " ++ show errors
    
    let ptagsint = map (\x -> tagmap' Map.! x) (V.toList ptags)
    let icorpusint' = V.map (V.map (second (tagmap' Map.!))) icorpus3
    let pcorpusint' = V.map (V.map (second (tagmap' Map.!))) ptokens'
    start <- getClockTime
    rules <- findPatches tagint pcorpusint' icorpusint' errors ofile
    end <- getClockTime
    putStrLn $ show (length rules) ++ " new patches found."
    putStrLn $ "time: " ++ timeDiffToString (diffClockTimes end start)
    --let rules' = map (intToTag tagint) rules
    --writeFile ofile (unlines $ map show (patches ++ rules'))

selfseq :: a -> a
selfseq a = a `seq` a
intToTag :: IntMap Tag -> Rule Int -> Rule Tag
intToTag imap (R t1 context t2) = R (fmap (imap IntMap.!) t1) (map con context) (imap IntMap.! t2)
  where
    con (One i t) = One i (imap IntMap.! t)
    con (Any i t) = Any i (imap IntMap.! t)
    con (All i t) = All i (V.map (\x -> imap IntMap.! x) t)
    con (OneW i w) = OneW i w
    con (Both t1 t2) = Both (imap IntMap.! t1) (imap IntMap.! t2)
    con (BothW w1 i w2) = BothW w1 i w2
    con (BothT w1 i t2) = BothT w1 i (imap IntMap.! t2)

intToTagU :: IntMap Tag -> URule Int -> URule Tag
intToTagU imap (U (Just t1) context t2) = U (Just (imap IntMap.! t1)) context (imap IntMap.! t2)
intToTagU imap (U Nothing context t2) = U Nothing context (imap IntMap.! t2)

-- | Compare two tagged files
compareResult :: [FilePath] -> IO ()
compareResult xs | length xs < 2 = printInvalidError
compareResult (f1:f2:fx) = do
    text1 <- readFile' f1
    text2 <- readFile' f2
    if null text1 || null text2
    then return ()
    else do
    count <- if notnull fx
             then readCount (head fx)
             else return Map.empty
    compareText text1 text2 count

compareText :: String -> String -> Count -> IO ()
compareText test tagged count = do
    let testWords   = map (getWord &&& getTag) . concatMap words . lines $ test
    let taggedWords = map (getWord &&& getTag) . concatMap words . lines $ tagged
    let z = zip testWords taggedWords
    
    let diff = filter (\((a,b),(x,y)) -> a == x && b /= y) z
    let f = frequency diff

    let known' = filter (\(x,y) -> (Map.member x count)) $ testWords
    let unknown' = filter (\(x,y) -> not (Map.member x count)) $ testWords
    let known = length known'
    let unknown = length unknown'
    
    let knownCorrect = length . filter (\((a,b),(x,y)) -> if a == x && Map.member a count then compareTags b y else False) $ z
    let unknownCorrect = length . filter (\((a,b),(x,y)) -> if a == x && not (Map.member a count) then compareTags b y else False) $ z
    let correct = knownCorrect + unknownCorrect
    -- let correct2 = length . filter (\((a,b),(x,y)) -> a == x && b == y) $ z
    let correct2 = length . filter (\(a,b) -> a == b) $ zip testWords taggedWords
    let l = length taggedWords
    if not (Map.null count)
    then do
    putStrLn $ show knownCorrect ++  " known correct out of  " ++ show known
                 ++ ", %=" ++ show ((fromIntegral  knownCorrect) / (fromIntegral  known) * 100)
    putStrLn $ show unknownCorrect ++ " unknown correct out of " ++ show unknown
                 ++ ", %=" ++ show ((fromIntegral  unknownCorrect) / (fromIntegral  unknown) * 100)
    else return ()
    putStrLn $ show correct ++ " correct out of " ++ show l ++ ", %=" ++ show ((fromIntegral  correct) / (fromIntegral  l) * 100)
    U.writeFile "temp.txt" $ unlines $ map (\(((a,b),(x,y)),i) -> a ++ "/" ++ b ++ ",  " ++ x ++ "/" ++ y ++ ":  " ++ show i) f
    --putStrLn $ "Top mismatches: "
    --putStrLn $ unlines $ map show $ take 100 f

parseArgs args arg = do
                let index = elemIndex ('-':arg) args
                if  isJust index
                    && length args > (fromJust index) + 1
                    && take 1 (args !! (fromJust index + 1)) /= "-"
                then do
                return $ args !! (fromJust index + 1)
                else do
                return ""

run args = do
    test <- parseArgs args "i"
    cfile <- parseArgs args "c"
    ufile <- parseArgs args "u"
    fcount <- parseArgs args "f"
    pfile <- parseArgs args "r"
    
    -- read the main Count file
    count <- readCount cfile
    
    -- read Count file for foreign words
    cf <- do file <- readFile' fcount
             if notnull file
             then do
                let fc = Map.fromList
                            . map (\(x:y:z:_) -> (x,(y,(read z :: Int))))
                            . map words $ lines file
                putStrLn $ "Foreign count: " ++ show (Map.size fc) ++ " words"
                return fc
             else return Map.empty
    
    -- read and parse lexical rules
    urules <- do utext <- readFile' ufile
                 if notnull utext
                 then do
                    let urules' = map (\x -> read x :: (URule String))
                                . filter (\x -> (not . null) x && take 1 x /= "#")
                                . map strip . lines $ utext
                    putStrLn $ show (length urules') ++ " unknown rules"
                    return urules'
                 else  return []
    
    -- read and parse contextual rules
    patches <- do text <- readFile' pfile
                  if notnull text
                  then do
                    let patches' = map (\x -> read x :: (Rule String))
                                    . filter (\x -> (not . null) x && take 1 x /= "#")
                                    . map strip . lines $ text
                    putStrLn $ show (length patches') ++ " patches"
                    return patches'
                  else  return []
    if test == ""
    then do
    putStrLn $ "Critical error: No input file provided for tagging."
    else do
    testtext <- readFile' test
    if notnull testtext
    then do
    -- -csv option indicates that the text is in utterance format (id, utterance, wordcount)
    let ut = isJust (elemIndex "-csv" args)
    let testlines = lines testtext
    putStrLn $ show (length testlines) ++ " lines to tag"
    let result = if ut
                 then unlines
                      . map (\(id,utter,cnt) -> id ++ "\t" ++
                                                        (applyPatchesToLine count cf urules patches ut utter)
                                                        ++ "\t" ++ cnt)
                      . map parseUline
                      $ testlines
                 else unlines . map (applyPatchesToLine count cf urules patches False)
                      $ testlines
    writeFile (test ++ ".tagged") result
    putStrLn $ "Patches applied. Result saved in " ++ test ++ ".tagged."
    
    let wlist = map (\(R _ [OneW _ w] _) -> w) . filter onew $ patches
    -- print the frequency of unknown words
    let unk = frequency
              -- . filter (\w -> not (elem w wlist))
              . filter (\w -> not (Map.member (filter (/=':') w) count))
              . filter (\w -> not $ isSuffixOf "+" w)
              . filter (\w -> not $ isPrefixOf "+" w)
              . filter (\w -> not (isNumber w))
              . filter (not . (flip Map.member) cf)
              . filter (not . (flip Map.member) count)
              . concatMap words
              . map (\line -> if ut then ((\(x,y,z) -> y) . parseUline $ line) else line)
              . lines $ testtext
    putStrLn $ "Unknown words: " ++ show (sum $ map snd unk)
    writeFile (test ++ ".unknown") . unlines $ map (\(a,i) -> a ++ " " ++ show i) unk
    putStrLn $ "Unknown words saved in " ++ (test ++ ".unknown.")
    else do
    putStrLn $ "Critical error: Input file does not exist."

printInvalidError = putStrLn "Invalid arguments. Read the program help."

-- | Reads Count file and parses it into a Count structure
readCount :: FilePath -> IO Count
readCount f = do
       text <- readFile' f
       if null text
       then return Map.empty
       else do
       let count = Map.fromListWith (Map.unionWith (+))
                   . map (\(x:p:q:_) -> (x,
                                         Map.singleton (newtag p) (read q :: Int) )
                         )
                   . mapfilter words notnull
                   . lines
                   $ text
       putStrLn $ "Count: " ++ show (Map.size count) ++ " words"
       return count

writeCount :: Count -> FilePath -> IO ()
writeCount count f =
    writeFile f $  unlines
                 . map concat
                 . map (intersperse " ")
                 . concat
                 . map (\(w,list) -> map (\(t,c) -> [w,t,show c]) list)
                 . map (\(w,t) -> (w, reverse . sortBy (compare `on` snd) $ Map.toList t))
                 $ Map.toList count

-- | Read file after checking its existence and permissions
readFile' :: FilePath -> IO String
readFile' f = do
       e <- doesFileExist f
       if not e
       then do
       putStrLn $ "File " ++ f ++ " does not exist."
       return ""
       else do
       p <- getPermissions f
       if not (readable p)
       then do
       putStrLn $ "Unable to read file " ++ f ++ "."
       return ""
       else do
       text <- readFile f
       return text
       
onew (R Nothing [OneW 0 _] _) = True
onew _ = False

parseUline :: String -> (String,String,String)
parseUline "" = ("","","")
parseUline line | isDigit (head line) =
    let (id,rest') = break (not . isDigit) line
        rest = if take 1 rest' == "\t" then drop 1 rest' else rest'
        (utter,wc') = if take 1 rest == "\t" then ("",drop 1 rest) else break (=='\t') rest
        wc = if take 1 wc' == "\t" then drop 1 wc' else wc'
    in (id,utter,wc)
parseUline line =
    let l = if take 1 line == "\t" then drop 1 line else line
        (utter,wc') = if take 1 l == "\t" then ("",drop 1 l) else break (=='\t') l
        wc = if take 1 wc' == "\t" then drop 1 wc' else wc'
    in ("0",utter,wc)

-- Apply patches on the given single line
applyPatchesToLine :: Count
                      -> Map String (String,Int)
                      -> [URule Tag]
                      -> [Rule Tag]
                      -> Bool
                      -> String
                      -> String
applyPatchesToLine c fc urules patches ut line =
                       unwords
                     . map (\(word,a) -> if ut then a else (word ++ "/" ++ a))
                     . V.toList
                     . (\v -> foldl' (flip applyV') v patches)
                     . applyURules urules c c
                     . initialTagger c fc
                     . V.fromList
                     $ words line

mergeCounts :: Count -> Count -> Count
mergeCounts c1 c2 = Map.unionWith (Map.unionWith (+)) c1 c2

printMsg  :: String -> IO ()
printMsg prg = do   
        putStrLn $ prg ++ " v" ++ pversion ++ ": POS tagger for the GSLC spoken language corpus."
        putStrLn $ "To get more help, use --help or -h."

printHelp :: String -> IO ()
printHelp prg = do
        putStrLn "Program options:"
        putStrLn $  prg ++ " " ++ "task options [optional parameters]"
        putStrLn $ "Tasks:"
        putStrLn $ "    count : build initial tagger from written pre-tagged corpus."
        putStrLn $ "   update : update Count from another pre-tagged file."
        putStrLn $ "    merge : merge second Count to the first Count."
        --putStrLn $ "  bigrams : build list of bigrams from the large corpus."
        --putStrLn $ "  unknown : learn rules for tagging unknown words."
        putStrLn $ "    train : learn contextual rules from spoken corpus."
        putStrLn $ "    run   : tag the given text file."
        putStrLn $ " compare  : test the tagger by comparing pre-tagged and post-tagged files."
        putStrLn $ "   stats  : show statistics of data in a count file."
        putStrLn $ "    freq  : print frequency of words with a particular tag."
        putStrLn $ "Options:"
        putStrLn $ "    count corpusfile outputfile"
        putStrLn $ "    update countfile taggedfile"
        putStrLn $ "    merge maincountfile countfile"
        --putStrLn $ "    bigrams corpusfile outputfile"
        --putStrLn $ "    unknown countfile bigramfile patchcorpus outputfile"
        putStrLn $ "    train -i speechcorpus -r rulefile [-c countfile -f foreigncountf]"
                        -- -u unknownrules]"
        putStrLn $ "    run -i inputfile [-c countfile -f foreigncount -r rulefile -csv]"
                        --  -u unknownrules]"
        putStrLn $ "    compare file1 file2 [countfile]"
        putStrLn $ "    stats countfile"
        putStrLn $ "    freq tag countfile outputfile"

-- Apply patches on the given corpus
applyPatches :: Count -> [Rule Tag] -> Vector (Vector (Word,Tag)) -> Vector (Vector (Word,Tag))
applyPatches _ [] corpus = corpus
applyPatches c patches corpus = foldl' (flip applyV) corpus patches
--applyPatches (r:patches) corpus =
--    applyPatches patches $! trace (show (length patches)) (applyV r $! corpus)
   
applyURules :: [URule Tag] -> Count -> Count -> Vector (Word,Tag) -> Vector (Word,Tag)
applyURules [] _ _ corpus = corpus
applyURules (r:patches) count1 count2 corpus =
        let p = applyU' r count1 count2 corpus
        in seq p (applyURules patches count1 count2 $ p)

-- Learns patches (rules) to correct errors in the initial tagging
findPatches :: IntMap Tag -> Vector (Vector (Word,Int))
              -> Vector (Vector (Word,Int))
              -> Int
              -> FilePath -- output file to save the patches
              -> IO [Rule Int]
findPatches imap pcorpus icorpus errors ofile = do
    let icorpus' = (V.map (V.map snd) icorpus)
    let pcorpus' = (V.map (V.map snd) pcorpus)
    let errors = V.filter (\(x,y) -> x /= y) $ V.zip (join icorpus') (join pcorpus')
    let corpus = V.map (\(v1,v2) -> V.map (\((w,t1),(_,t2)) -> Unit w t2 t1) $ V.zip v1 v2) $ V.zip (pcorpus) (icorpus)
    patches <- findPatches' imap corpus (V.length errors) ofile []
    return patches

-- Runs recursively, finds a new patch in each iteration
findPatches' :: IntMap Tag
                -> Vector (Vector (Unit Int))
                -> Int
                -> FilePath -- output file to save the patches
                -> [Rule Int] -- collect the patches
                -> IO [Rule Int]
findPatches' imap _ i ofile patches | length patches >= maxRules
    = return patches
findPatches' imap corpus errors ofile patches | errors <= 0 = return patches
findPatches' imap corpus errors ofile patches = do
    let allrules = makeRules corpus
    putStrLn $ "Rules to test: " ++ show (length allrules)
    patch <- nextPatch corpus allrules
    let newcorpus = seq patch $ V.map (applyPatch patch) corpus
    let newerrors = seq newcorpus $ V.length . V.map (\(Unit _ t1 t2) -> (t1,t2)) . V.filter (\(Unit w t1 t2) -> t1 /= t2) . join $ newcorpus
    case newerrors `seq` (newerrors < errors) of
        True -> do
            let x = (show $ intToTag imap patch)
            putStrLn $ "Patch: " ++ x ++ ", errors: " ++ show newerrors
            appendPatch (x ++ "\n") ofile 
            findPatches' imap newcorpus newerrors ofile (patch:patches)
        False -> return patches

      where applyPatch r v = V.map merge' . (\(a,b) -> V.zip (applyV' r a) b) . V.unzip . V.map sep $ v
            sep (Unit w t1 t2) = ((w,t1),t2)
            merge' ((w,t1), t2 )= Unit w t1 t2
  
appendPatch :: String -> FilePath -> IO ()
appendPatch s ofile =
    catch (appendFile ofile s)
          (\e -> do let err = (e :: IOException)
                    appendPatch s ofile)
-- only compute the errors of the rules, return the rule with minimum error count
nextPatch :: (Ord a) => Vector (Vector (Unit a)) -> [Rule a]
             -> IO (Rule a)
nextPatch corpus rules = do
    let newrules = parMap rpar (\rule -> (rule, score rule corpus)) rules
    let maxscore = snd $ maximumBy (compare `on` snd) newrules
    return
        . head
        . sort 
        . map fst
        . filter (\(x,y) -> y == maxscore)
        $ newrules

-- Learns patches (rules) to correct tagging errors for unknown words
unknownPatches :: IntMap Tag
                  -> Vector (Vector (Word,Int))
                  -> Vector (Vector (Word,Int))
                  -> FilePath -- output file to save the patches
                  -> Count -- check for unknown words
                  -> Count -- check for unknown words
                  -> Bigram -- used for some types of rules
                  -> IO [URule Int]
unknownPatches imap pcorpus icorpus ofile count1 count2 big = do
    let corpus = V.map (uncurry V.zip) $ V.zip icorpus pcorpus
    let unitcorpus = V.map (V.map (\((w,t1),(_,t2)) -> Unit w t1 t2)) corpus
    --let bigrams = nub . V.toList . join $ V.map (\v -> V.zip (V.map (fst . fst) v) (V.tail (V.map (fst . fst) v))) corpus
    let errors = V.length . V.filter (\((x1,y1),(x2,y2)) -> y1 /= y2 && not (x1 `Map.member` count1)) $ join corpus
    putStrLn $ "Errors after initial tagging: " ++ show errors
    patches <- unknown' imap unitcorpus errors ofile count1 count2 big []
    return patches

-- Runs recursively, finds a new patch in each iteration
unknown' :: IntMap Tag
                -> Vector (Vector (Unit Int))
                -> Int
                -> FilePath -- output file to save the patches
                -> Count
                -> Count
                -> Bigram
                -> [URule Int] -- collect the patches
                -> IO [URule Int]
unknown' imap _ _ _ _ _ _ patches | length patches >= maxRules
    = return patches
unknown' _ _ errors _ _ _ _ patches | errors <= 0 = return patches
unknown' imap corpus errors ofile count1 count2 bigrams patches = do
    let allrules = makeURules corpus count1 count2 bigrams
    putStrLn $ "Rules to test: " ++ show (length allrules)
    patch <- nextRule corpus allrules count1 count2
    let newcorpus = patch `seq` (V.map (applyPatch patch) corpus)
    let newerrors = newcorpus `seq` V.length
                    . V.filter (\(Unit w t1 t2) -> t1 /= t2 && not (w `Map.member` count1)) 
                    . join $ newcorpus
    let x = show $ intToTagU imap patch
    case newerrors `seq` (newerrors < errors) of
        True -> do
            putStrLn $ "Patch: " ++ x ++ ", errors: " ++ show newerrors
            appendPatch (x ++ "\n") ofile 
            unknown' imap newcorpus newerrors ofile count1 count2 bigrams (patch:patches)
        False -> do
                    putStrLn $ "errors: " ++ show errors
                    putStrLn $ "New errors: " ++ show newerrors
                    putStrLn $ "Patch: " ++ x ++ ", errors: " ++ show newerrors
                    return patches
      where applyPatch r v = V.map merge' . (\(a,b) -> V.zip (applyU' r count1 count2 a) b)
                             . V.unzip . V.map sep $ v
            sep (Unit w t1 t2) = ((w,t1),t2)
            merge' ((w,t1), t2 )= Unit w t1 t2

-- only compute the errors of the rules, return the rule with minimum error count
nextRule :: (Ord a) => Vector (Vector (Unit a)) -> [URule a] -> Count -> Count
             -> IO (URule a)
nextRule corpus rules count1 count2 = do
    let newrules = parMap rpar (\rule -> (rule, scoreU rule corpus count1 count2)) rules
    let maxscore = snd $ maximumBy (compare `on` snd) newrules
    --return maxscore
    return
        . head
        . sort
        . map fst
        . filter (\(x,y) -> y == maxscore)
        $ newrules

-- read tagger from taggerFile
-- tag the untagged file dataFile
-- store the tagged data in file result
runTagger :: FilePath -> FilePath -> FilePath -> IO ()
runTagger taggerFile dataFile result = do
    undefined

map2 f = map (\x -> map f x)
vmap2 f = V.map (\x -> V.map f x)
-------------------------------------------------------------------------------
--        Instance declarations and parsers
-------------------------------------------------------------------------------
instance Show UContext where
    show (Prefix    s) = "Prefix    " ++ s
    show (Suffix    s) = "Suffix    " ++ s
    show (DelPrefix s) = "DelPrefix " ++ s
    show (DelSuffix s) = "DelSuffix " ++ s
    show (AddSuffix s) = "AddSuffix " ++ s
    show (AddPrefix s) = "AddPrefix " ++ s
    show (LeftWord w)  = "LeftWord  " ++ w
    show (RightWord w) = "RightWord " ++ w
    show (CurrentWord w) = "CurrentWord " ++ w
    show (Appears c)   = "Appears   " ++ [c]
instance Show x => Show (Context x) where
    show (One i x)     = "One  (" ++ show i ++ ") " ++ show x
    show (OneW i x)    = "OneW (" ++ show i ++ ") " ++ x
    show (Any i x)     = "Any  (" ++ show i ++ ") " ++ show x
    show (All i xs)    = "All  (" ++ show i ++ ") " ++ show (V.toList xs)
    show (Both x y)    = "Both  " ++ show x ++ " " ++ show y
    show (BothW x i y) = "BothW " ++ x ++ " (" ++ show i ++ ") " ++ y
    show (BothT x i y) = "BothT " ++ x ++ " (" ++ show i ++ ") " ++ (show y)
instance Ord x => Ord (Context x) where
    compare (One i1 t1) (One i2 t2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (One i1 t1) (One i2 t2) = compare t1 t2
    compare (One _ _) _ = LT
    compare _ (One _ _) = GT
    compare (Any i1 t1) (Any i2 t2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (Any i1 t1) (Any i2 t2) = compare t1 t2
    compare (Any _ _) _ = LT
    compare _ (Any _ _) = GT
    compare (All i1 t1) (All i2 t2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (All i1 t1) (All i2 t2) = compare t1 t2
    compare (All _ _) _ = LT
    compare _ (All _ _) = GT
    compare (Both x1 y1) (Both x2 y2) | x1 /= x2 = compare x1 x2
    compare (Both x1 y1) (Both x2 y2) = compare y1 y2
    compare (Both _ _) _ = LT
    compare _ (Both _ _) = GT
    compare (OneW i1 w1) (OneW i2 w2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (OneW i1 w1) (OneW i2 w2) = compare w1 w2
    compare (OneW _ _) _ = LT
    compare _ (OneW _ _) = GT
    compare (BothT x1 i1 y1) (BothT x2 i2 y2) | x1 /= x2 = compare x1 x2
    compare (BothT x1 i1 y1) (BothT x2 i2 y2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (BothT x1 i1 y1) (BothT x2 i2 y2) = compare y1 y2
    compare (BothT _ _ _) _ = LT
    compare _ (BothT _ _ _) = GT
    compare (BothW x1 i1 y1) (BothW x2 i2 y2) | x1 /= x2 = compare x1 x2
    compare (BothW x1 i1 y1) (BothW x2 i2 y2) | abs i1 /= abs i2 = compare (abs i1) (abs i2)
    compare (BothW x1 i1 y1) (BothW x2 i2 y2) = compare y1 y2
instance Read (Context String) where
    readsPrec _ s = readP_to_S (readContext readToken) s
instance Show a => Show (URule a) where
    show (U (Just a) c b) = show a ++ " -> " ++ show b ++ " :: " ++ show c
    show (U Nothing c b) =  "_" ++ " -> " ++ show b ++ " :: " ++ show c
instance Show a => Show (Rule a) where
    show (R (Just t1) context t2) = show t1 ++ " -> " ++ show t2 ++ " :: "
                                    ++ concat (intersperse " && " (map show context))
    show (R Nothing context t2) = "_    -> " ++ show t2 ++ " :: " 
                                    ++ concat (intersperse " && " (map show context))
instance Read (URule String) where
    readsPrec _ s = readP_to_S (readURule readToken) s

instance Read (Rule String) where
    readsPrec _ s = readP_to_S (readRule readToken) s
readToken1 :: ReadP String
readToken1 = do  
    str <- munch1 (isAlpha)
    return str
readToken2 :: ReadP String
readToken2 = do
    char '"'
    str <- munch1 (isAlpha)
    char '"'
    return str
readToken = readToken1 <++ readToken2
readUContext :: ReadP UContext
readUContext = do
    skipSpaces
    cont <- munch1 isAlpha
    skipSpaces
    case cont of
        "Prefix"    -> munch1 (not . isSpace) >>= (return . Prefix)
        "Suffix"    -> munch1 (not . isSpace) >>= (return . Suffix)
        "DelPrefix" -> munch1 (not . isSpace) >>= (return . DelPrefix)
        "DelSuffix" -> munch1 (not . isSpace) >>= (return . DelSuffix)
        "AddSuffix" -> munch1 (not . isSpace) >>= (return . AddSuffix)
        "AddPrefix" -> munch1 (not . isSpace) >>= (return . AddPrefix)
        "LeftWord"  -> munch1 (not . isSpace) >>= (return . LeftWord)
        "RightWord" -> munch1 (not . isSpace) >>= (return . RightWord)
        "CurrentWord" -> munch1 (not . isSpace) >>= (return . CurrentWord)
        "Appears"   -> satisfy (not . isSpace) >>= (return . Appears)
        _ -> pfail

readContext :: ReadP a -> ReadP (Context a)
readContext p = do
    skipSpaces
    cont <- munch1 isAlpha
    skipSpaces
    case cont of
        "Both"  -> readBoth p
        "BothW" -> readBothW
        "BothT" -> readBothT p
        "OneW"  -> readOneW
        "One"   -> readOne p
        "Any"   -> readAny p
        "All"   -> readAll p
        _ -> pfail
readBothT p = do
    word <- munch1 (not . isSpace)
    i <- readInt
    tag <- p
    return (BothT word i tag)
readBothW = do
    word1 <- munch1 (not . isSpace)
    i <- readInt
    word2 <- munch1 (not . isSpace)
    return (BothW word1 i word2)
readBoth p = do
    tag1 <- p
    char ' '
    skipSpaces
    tag2 <- p
    return (Both tag1 tag2)
readOneW = do
    i <- readInt
    w <- munch1 (not . isSpace)
    return (OneW i w)
readOne p = do
    i <- readInt
    tag <- p
    return (One i tag)
readAny p = do
    i <- readInt
    tag <- p
    return (Any i tag)
readAll p = do
    i <- readInt
    char '['
    tags <- sepBy1 p (char ',')
    char ']'
    return (All i (V.fromList tags))
readInt :: ReadP Int
readInt = do
    skipSpaces
    char '('
    skipSpaces
    int <- readS_to_P (readsPrec 10)
    skipSpaces
    char ')'
    skipSpaces
    return int
readRule :: ReadP a -> ReadP (Rule a)
readRule p = do
    skipSpaces
    t1 <- ((char '_' >> return Nothing) <++ (p >>= (return . Just) ))
    skipSpaces
    string "->"
    skipSpaces
    t2 <- p
    skipSpaces
    string "::"
    skipSpaces
    c <- sepBy1 (readContext p) (skipSpaces >> string "&&" >> skipSpaces)
    return (R t1 c t2)
readURule :: ReadP a -> ReadP (URule a)
readURule p = do
    skipSpaces
    t1 <- ((char '_' >> return Nothing) <++ (p >>= (return . Just) ))
    skipSpaces
    string "->"
    skipSpaces
    t2 <- p
    skipSpaces
    string "::"
    skipSpaces
    c <- readUContext
    return (U t1 c t2)

digits = ["en","ett","två","tre","fyra","fem","sex","sju","åtta","nio",
          "först","första","förste","andra","tredje","fjärde","femte","sjätte","sjunde","åttonde","nionde"]
tens = ["tio","elva","tolv","tretton","fjorton","femton","sexton","sjutton","arton","nitton"]
deca = ["tjugo","trettio","fyrtio","femtio","sextio","sjutio","åttio","nittio","nitti"]
higher = ["hundra","tusen","miljon","miljard"]

newtype Number = N Integer

instance Read Number where
    readsPrec _ s = readP_to_S readNumeral s
instance Show Number where
    show (N i) = "N " ++ show i

readMaybe :: (Read a) => String -> Maybe a
readMaybe s = case reads s of
              [(x, "")] -> Just x
              _ -> Nothing

readNoll = (string "noll" <++ string "zero") >> return (N 0)
readEn   = (string "en" <++ string "one")  >> return (N 1)
readEtt  = (string "ett" <++ string "one") >> return (N 1)
readTvå  = (string "två" <++ string "two") >> return (N 2)
readTre  = (string "tre" <++ string "three") >> return (N 3)
readFyra = (string "fyra" <++ string "four") >> return (N 4)
readFem  = (string "fem" <++ string "five") >> return (N 5)
readSex  = (string "sex" <++ string "six") >> return (N 6)
readSju  = (string "sju" <++ string "seven") >> return (N 7)
readÅtta = (string "åtta" <++ string "eight") >> return (N 8)
readNio  = (string "nio" <++ string "nieo" <++ string "nie" <++ string "nine")  >> return (N 9)

readTio  = (string "tio" <++ string "tie" <++ string "ten") >> return (N 10)
readElva = (string "elva" <++ string "eleven")    >> return (N 11)
readTolv = (string "tolv" <++ string "twelve")    >> return (N 12)
readTret = (string "tretton" <++ string "thirteen") >> return (N 13)
readFjor = (string "fjorton" <++ string "fourteen") >> return (N 14)
readFemt = (string "femton" <++ string "fifteen")  >> return (N 15)
readSext = (string "sexton" <++ string "sixteen")  >> return (N 16)
readSjut = (string "sjutton" <++ string "seventeen") >> return (N 17)
readArto = (string "arton" <++ string "eighteen")   >> return (N 18)
readNitt = (string "nitton" <++ string "nineteen" <++ string "ninteen")  >> return (N 19)

readTjugo   = (string "tjugo" <++ string "tjuge" <++ string "tjugi" <++ string "tju" <++ string "twenty") >> return (N 20)
readTrettio = (string "trettio" <++ string "tretti" <++ string "thirty") >> return (N 30)
readFyrtio  = (string "fyrtio" <++ string "fyrti" <++ string "forty") >> return (N 40)
readFemtio  = (string "femtio" <++ string "femti" <++ string "fifty") >> return (N 50)
readSextio  = (string "sextio" <++ string "sexti" <++ string "sixty") >> return (N 60)
readSjutio  = (string "sjuttio" <++ string "sjutti" <++ string "seventy") >> return (N 70)
readÅttio   = (string "åttio" <++ string "åtti" <++ string "eighty") >> return (N 80)
readNittio  = (string "nittio" <++ string "nitti" <++ string "nitto" <++ string "ninety" <++ string "ninty") >> return (N 90)

readHundra  = (string "hundra" <++ string "hundred" <++ string "hundreds" <++ string "hundr") >> return (N 100)
readTusen   = (string "tusen" <++ string "thousand" <++ string "thousands") >> return (N 1000)
readMiljion = (string "miljon" +++ string "miljoner" <++ string "million" <++ string "millions") >> return (N 1000000)
readMiljard = (string "miljarder" <++ string "miljard" <++ string "biljoner" <++ string "biljon" <++ string "billion" <++ string "billions") >> return (N 1000000000)
readTriljon = (string "triljon" +++ string "triljoner" <++ string "trillion" <++ string "trillions") >> return (N 1000000000000)

readDigit = readNoll
            <++ readEn
            <++ readEtt
            <++ readTvå
            <++ readTre
            <++ readFyra
            <++ readFem
            <++ readSex
            <++ readSju
            <++ readÅtta
            <++ readNio

readTens =  readTio
            <++ readElva
            <++ readTret
            <++ readTolv
            <++ readFjor
            <++ readFemt
            <++ readSext
            <++ readSjut
            <++ readArto
            <++ readNitt

readDeca = do
    (N t) <- readTjugo <++ readTrettio <++ readFyrtio <++ readFemtio <++ readSextio <++ readSjutio <++ readÅttio <++ readNittio
    (N a) <- option (N 0) (readDigit +++ (string "säx" >> return (N 6)))
    return (N (t+a))
readHundreds =
    readHundra
    <++ (do
            (N d) <- (readTens +++ readDigit)
            (N h) <- readHundra
            return (N (d*h)))
readHundred = do
    (N h) <- readHundreds
    (N d) <- option (N 0) readUptoHundred
    return (N (h+d))
readThousands = 
    readTusen
    <++ (do
            (N d) <- readHundred <++ (readTens +++ readDigit +++ (string "et" >> return (N 1)))
            (N t) <- readTusen
            return (N (d*t)))
readThousand = do
    (N t) <- readThousands
    (N h) <- option (N 0) readHundreds
    (N d) <- option (N 0) readUptoHundred
    return (N (t+h+d))
readMillions = do
    readMiljion
    <++ (do
             (N d) <- readHundred <++ (readTens +++ readDigit)
             (N m) <- readMiljion
             return (N (d*m)))
readMillion = do
    (N m) <- readMillions
    (N t) <- option (N 0) readThousands
    (N h) <- option (N 0) readHundreds
    (N d) <- option (N 0) readUptoHundred
    return (N (m+t+h+d))
readBillions = do
    readMiljard
    <++ (do
             (N d) <- readHundred <++ (readTens +++ readDigit)
             (N m) <- readMiljard
             return (N (d*m)))
readBillion = do
    (N b) <- readBillions
    (N m) <- option (N 0) readMillions
    (N t) <- option (N 0) readThousands
    (N h) <- option (N 0) readHundreds
    (N d) <- option (N 0) readUptoHundred
    return (N (b+m+t+h+d))
readTrillions = do
    readTriljon
    <++ (do
             (N d) <- readHundred <++ (readTens +++ readDigit)
             (N m) <- readTriljon
             return (N (d*m)))
readTrillion = do
    (N tr) <- readTrillions
    (N b) <- option (N 0) readBillions
    (N m) <- option (N 0) readMillions
    (N t) <- option (N 0) readThousands
    (N h) <- option (N 0) readHundreds
    (N d) <- option (N 0) readUptoHundred
    return (N (tr+b+m+t+h+d))

readUptoHundred = readDeca +++ readTens +++ readDigit
readNumeral :: ReadP (Number)
readNumeral = readTrillion +++ readBillion +++ readMillion +++ readThousand +++ readHundred +++ readDeca +++ readTens +++ readDigit

