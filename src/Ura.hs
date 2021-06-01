{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Ura where

import Lang
import Data.List
import qualified Data.Map.Strict as M

data Ineq = CAExp :/=: CAExp deriving Show

data Restr = INCONSISTENT
           | RESTR [Ineq]
           deriving Show

isContradiction :: Ineq -> Bool
isContradiction (lhs :/=: rhs) = lhs == rhs

isTautology :: Ineq -> Bool
isTautology (ATOM a :/=: ATOM b) = a /= b
isTautology _ = False

instance Eq Ineq where
    (l1 :/=: r1) == (l2 :/=: r2)
      | (l1 == l2) && (r1 == r2) = True
      | (l1 == r2) && (r1 == l2) = True
      | otherwise = False

cleanRestr :: Restr -> Restr
cleanRestr INCONSISTENT = INCONSISTENT
cleanRestr (RESTR ineqs)
  | any isContradiction ineqs = INCONSISTENT
  | otherwise = RESTR $ nub $ filter (not . isTautology) ineqs

instance UPDATE Restr where
    INCONSISTENT +. _ = INCONSISTENT
    _ +. INCONSISTENT = INCONSISTENT
    (RESTR r1) +. (RESTR r2) = cleanRestr $ RESTR $ r1 ++ r2

type Subst = Env

dom :: Subst -> [CExp]
dom = M.keys

instance APPLY Ineq Subst where
    (l :/=: r) /. s = (l /. s) :/=: (r /. s)

instance (APPLY a s, APPLY b s) => APPLY (a, b) s where
    (ax, bx) /. s = (ax /. s, bx /. s)

instance APPLY Restr Subst where
    INCONSISTENT /. s = INCONSISTENT
    (RESTR ineqs) /. s = cleanRestr $ RESTR $ ineqs /. s

type Class = ([CExp], Restr)
type Classes = [Class]
type Conf = (State, Restr)

(.*.) :: Subst -> Subst -> Subst
sa .*. sb = M.fromList [ (v, (v /. sa) /. sb) | v <- d ]
  where d = nub $ dom sa ++ dom sb

data Contr = S Subst | R Restr deriving Show
type Split = (Contr, Contr)

-- Work around overlapping classes
(//.) :: Conf -> Contr -> Conf
((t, cx), rs) //. (S subst) = ((t, cx .*. subst), rs /. subst)
(cx, rs) //. (R restr) = (cx, rs +. restr)

(///.) :: Class -> Contr -> Class
(cx, rs) ///. (S subst) = (cx /. subst, rs /. subst)
(cx, rs) ///. (R restr) = (cx, rs +. restr)

data Clash = Var :=: Var deriving Show
type Clashes = [Clash]

type UnifRes = (Bool, Subst)

ufail :: UnifRes
ufail = (False, M.empty)

unify :: [CExp] -> [CExp] -> UnifRes
unify ces1 ces2
  | length ces1 /= length ces2 = ufail
  | otherwise = unify' [] chs
  where chs = zipWith (:=:) ces1 ces2

unify' :: Clashes -> Clashes -> UnifRes
unify' rchs [] = (True, M.fromList [(a, b) | a :=: b <- rchs])
unify' rchs chs@(ch:chs') =
  case ch of
    ATOM a :=: ATOM b | a == b -> unify' rchs chs'
    ATOM a :=: _ -> ufail
    CVA _ :=: caex@(ATOM _) -> moveCl rchs chs
    CVA _ :=: caex@(CVA _) -> moveCl rchs chs
    CVA _ :=: _ -> ufail
    CVE _ :=: _ -> moveCl rchs chs
    CONS a1 b1 :=: CONS a2 b2 -> unify' rchs ([a1 :=: a2, b1 :=: b2] ++ chs')
    CONS a1 b1 :=: _ -> ufail

moveCl :: Clashes -> Clashes -> UnifRes
moveCl rchs chs@(ch@(cvar :=: cexp):chs') =
  case [ y | (x :=: y) <- rchs, x == cvar ] of
    [] -> unify' (ch:rchs) chs'
    [y] | y == cexp -> unify' rchs chs'
    [_] -> ufail

idC :: Contr
idC = S M.empty

emptC :: Contr
emptC = R INCONSISTENT

data Tree = LEAF Conf | NODE Conf [Branch] deriving Show
type Branch = (Contr, Tree)

ptr :: Prog -> Class -> Tree
ptr p cl@(ces, r) = evalT c (mkFastProg p) 0
  where
    DEFINE f prms _ = head p
    ce = mkEnv prms ces
    c = ((CALL f prms, ce), r)

evalT :: Conf -> FastProg -> Int -> Tree
evalT c@((CALL f args, ce), r) p i = NODE c [ (idC, evalT c' p i) ]
  where
    DEFINE _ prms t' = getDef f p
    ce' = mkEnv prms (args /. ce)
    c' = ((t', ce'), r)

evalT c@((ALT cnd t1 t2, ce), r) p i = NODE c [ (cnt1, evalT c1' p i'), (cnt2, evalT c2' p i') ]
  where
    ((cnt1, cnt2), uce1, uce2, i') = ccond cnd ce i
    ((_, ce1), r1) = c //. cnt1
    c1' = ((t1, ce1 +. uce1), r1)
    ((_, ce2), r2) = c //. cnt2
    c2' = ((t2, ce2 +. uce2), r2)

evalT ((TRACE _ t, ce), r) p i = evalT ((t, ce), r) p i
evalT c@((RETURN _, _), _) _ _ = LEAF c

mkCAVar :: Int -> (CVar, Int)
mkCAVar i = (CVA i, i + 1)

mkCEVar :: Int -> (CVar, Int)
mkCEVar i = (CVE i, i + 1)

splitA :: CVar -> CExp -> Split
splitA cv@(CVA _) caexp = (S $ M.singleton cv caexp, R $ RESTR [ cv :/=: caexp ] )

splitE :: CVar -> Int -> (Split, Int)
splitE cv@(CVE _) i = ((S $ M.singleton cv (CONS cvh cvt), S $ M.singleton cv cva), i')
  where
    (cvh, i1) = mkCEVar i
    (cvt, i2) = mkCEVar i1
    (cva, i') = mkCAVar i2

ccond :: Cond -> Env -> Int -> (Split, Env, Env, Int)
ccond (EQA' x y) ce i =
  let x' = x /. ce
      y' = y /. ce
  in case (x', y') of
       (a, b) | a == b -> ((idC, emptC), M.empty, M.empty, i)
       (ATOM a, ATOM b) -> ((emptC, idC), M.empty, M.empty, i)
       (CVA _, a) -> (splitA x' a, M.empty, M.empty, i)
       (a, CVA _) -> (splitA y' a, M.empty, M.empty, i)

ccond (CONS' x vh vt va) ce i =
  let x' = x /. ce
   in case x' of
        CONS h t -> ((idC, emptC), M.fromList [(vh, h), (vt, t)], M.empty, i)
        ATOM a -> ((emptC, idC), M.empty, M.singleton va x', i)
        CVA _ -> ((emptC, idC), M.empty, M.singleton va x', i)
        CVE _ -> (split, M.fromList [(vh, ch), (vt, ct)], M.singleton va ca, i')
          where
            (split, i') = splitE x' i
            (S m1, S m2) = split
            (_, CONS ch ct) = head $ M.toList m1
            (_, ca) = head $ M.toList m2

xptr :: Prog -> Class -> Tree
xptr p cl = NODE c (cutT brs)
            where 
              tree = ptr p cl
              NODE c brs = tree

cutT :: [Branch] -> [Branch]
cutT [ ] = [ ]
cutT (b@(cnt, tree) : bs) = 
  case tree of
    LEAF (_, INCONSISTENT)    -> cutT bs
    NODE (_, INCONSISTENT) _  -> cutT bs
    LEAF c                    -> b : cutT bs
    NODE c bs'                -> b': cutT bs
                              where
                                tree' = NODE c (cutT bs')
                                b' = (cnt, tree')

type TLevel = [(Class, Tree)]
type Tab = [(Class, CExp)]

tab :: Prog -> Class -> Tab
tab p x = tab' [ (x, tree) ] [ ]
  where tree = xptr p x

tab' :: TLevel -> TLevel -> Tab
tab' ((xi, LEAF c) : lv1) lv2 = (xi, cex):tab' lv1 lv2
  where ((RETURN exp, ce), _) = c
        cex = exp /. ce
tab' ((xi, NODE _ bs) : lv1) lv2 = tab' lv1 lv2'
                                    where lv2' = tabB xi bs lv2
tab' [] [] = []
tab' [] lv2 = tab' lv2 []

tabB :: Class -> [Branch] -> TLevel -> TLevel
tabB xi ((cnt, tree):bs) lv = tabB xi bs ((xi ///. cnt, tree):lv)
tabB xi [] lv = lv

ura' :: Prog -> Class -> EVal -> Classes
ura' p x = urac (tab p x)

urac :: Tab -> EVal -> Classes
urac ((xi, cex):ptab') y = 
  case unify [cex] [y] of
    (False, _) -> tail
    (True,  s) -> case xi' of
                    (_, INCONSISTENT) -> tail
                    _                 -> xi' : tail
                  where xi' = xi /. s
  where tail = urac ptab' y
urac [] y = []

ura :: Prog -> Class -> EVal -> [(Subst, Restr)]
ura p x@(ces, r) y = map altRepr (ura' p x y)
  where 
    altRepr :: Class -> (Subst, Restr)
    altRepr xi@(cesi, ri@(RESTR rir)) = (si, ri')
      where 
        (True, si) = unify ces cesi
        ri' = RESTR [ ineq | ineq <- rir, ineq `notElem` rsir]
              where RESTR rsir =  r /. si
