module SM (Block, Instr(..), compileSM, splitIntoChunks) where

import Lang hiding (State)

import Data.List hiding (uncons)
import Control.Monad
import Control.Monad.State


type Block = [Instr]

data Instr = Push Atom
           | Cons
           | Split
           | Test -- is cons?
           | Eqa
           | Dup
           | Drop
           | Call FName
           | Return
           | Exit
           | Label FName
           | Jmp FName
           | CJmp FName
           | Locals Int
           | GetLocal Int
           | SetLocal Int
           deriving (Eq, Show)

data CState = CState { defs :: [FDef]
                     , dispatch :: [FName]
                     , nextLabel :: FName
                     , curLabel :: FName
                     , exprStack :: EVar
                     , callStack :: EVar
                     , localVars :: EVar
                     , nVars :: Int
                     , compWrap :: Term -> Term
                     , finalized :: Bool
                     , curInstr :: Instr
                     }

type SMCompiler = State CState

data Chunk = Chunk FName Block
    deriving (Eq, Show)

initialState :: CState
initialState = CState { defs = []
                      , dispatch = []
                      , nextLabel = ""
                      , curLabel = ""
                      , exprStack = ATOM "Nil"
                      , callStack = ATOM "Nil"
                      , localVars = ATOM "Nil"
                      , nVars = 0
                      , compWrap = id
                      , finalized = False
                      , curInstr = Exit
                      }

getFuncName :: Int -> FName
getFuncName f = "$" <> (show f)

registerFunc :: FDef -> SMCompiler ()
registerFunc f = modify (\x -> x { defs = f:(defs x) })

registerDispatch :: FName -> SMCompiler ()
registerDispatch f = modify (\x -> x { dispatch = nub $ f:(dispatch x) })

compileMain :: Block -> SMCompiler Prog
compileMain block = do
    fname <- compileBlock (block ++ [Label "$exit", Exit])
    registerDispatch "$exit"
    generateDispatch
    fs <- gets defs
    return $ (DEFINE "$start" [PVE "arg"]
               (CALL fname [PVE "arg", CONS (CONS (ATOM "$exit") (ATOM "Nil")) (ATOM "Nil"), ATOM "Nil"])
             ):fs

generateDispatch :: SMCompiler ()
generateDispatch = do
    names <- gets dispatch
    registerFunc $ DEFINE "$dispatch" [PVE "es", PVE "cs", PVE "lv", PVA "f"] $ d names
  where
    d [] = (RETURN (ATOM "dispatch failed"))
    d (x:xs) = (ALT (EQA' (ATOM x) (PVA "f")) (CALL x [PVE "es", PVE "cs", PVE "lv"]) (d xs))

splitIntoChunks :: Block -> [Chunk]
splitIntoChunks block =
    filter (\(Chunk _ b) -> not $ null b) $
        map (\(Chunk clabel cblock) -> Chunk clabel (reverse cblock)) $
            f block (Chunk "" []) 0
    where
      f [] cur _ = [cur]
      f (x:xs) cur@(Chunk clabel cblock) cnt =
          let end = (Chunk clabel (x:cblock)):(f xs (Chunk ("$R" <> (show cnt)) []) (cnt + 1)) in
              case x of
                Label label -> cur:(f xs (Chunk label [x]) cnt)
                Call _ -> end
                Test -> end
                Eqa -> end
                CJmp _ -> end
                _ -> f xs (Chunk clabel (x:cblock)) cnt

compileBlock :: Block -> SMCompiler FName
compileBlock block = do
    let chunks = splitIntoChunks block
    forM_ (zip chunks $ (map (\(Chunk clabel _) -> clabel) $ tail chunks) <> [""]) compileChunk
    let (Chunk label _) = head chunks
    return label

freshVarName :: SMCompiler VName
freshVarName = do
    n <- gets nVars
    modify (\x -> x { nVars = n + 1 })
    return $ "!" <> (show n)

freshEVar :: SMCompiler EVar
freshEVar = PVE <$> freshVarName

freshAVar :: SMCompiler EVar
freshAVar = PVA <$> freshVarName

compileChunk :: (Chunk, FName) -> SMCompiler ()
compileChunk ((Chunk clabel block), label) = do
    when (not $ null label) $ do
        registerDispatch label
    modify (\x -> x { nextLabel = label
                    , curLabel = clabel
                    , exprStack = PVE "es"
                    , callStack = PVE "cs"
                    , localVars = PVE "lv"
                    , nVars = 0
                    , compWrap = id
                    , finalized = False
                    , curInstr = Exit
                    })
    mapM_ compileInstr block
    isFinal <- gets finalized
    unless isFinal $ jmp label

panic :: String -> Exp -> SMCompiler Term
panic msg info = do
    label <- gets curLabel
    instr <- gets curInstr
    return $ RETURN (CONS (ATOM ("panic: " <> msg <> " in " <> label <> " in " <> (show instr))) info)

uncons :: Exp -> SMCompiler (Exp, Exp)
uncons value = do
    oldWrap <- gets compWrap
    car <- freshEVar
    cdr <- freshEVar
    p <- panic "uncons on an atom" value
    let newWrap body = oldWrap $ (ALT (CONS' value car cdr (PVA "_")) body p)
    modify (\x -> x { compWrap = newWrap })
    return (car, cdr)

convertToAVal :: Exp -> SMCompiler AVal
convertToAVal value = do
    oldWrap <- gets compWrap
    var <- freshAVar
    p <- panic "not an atom" value
    let newWrap body = oldWrap $ (ALT (CONS' value (PVE "_") (PVE "_") var) p body)
    modify (\x -> x { compWrap = newWrap })
    return var

pushToExprStack :: Exp -> SMCompiler ()
pushToExprStack value = modify (\x -> x { exprStack = CONS value (exprStack x) })

popFromExprStack :: SMCompiler Exp
popFromExprStack = do
    oldStack <- gets exprStack
    (val, newStack) <- uncons oldStack
    modify (\x -> x { exprStack = newStack })
    return val

pushToCallStack :: Exp -> SMCompiler ()
pushToCallStack value = modify (\x -> x { callStack = CONS value (callStack x) })

popFromCallStack :: SMCompiler Exp
popFromCallStack = do
    oldStack <- gets callStack
    (val, newStack) <- uncons oldStack
    modify (\x -> x { callStack = newStack })
    return val

listIndex :: Exp -> Int -> SMCompiler Exp
listIndex list 0 = do
    (val, _) <- uncons list
    return val
listIndex list n = do
    (car, cdr) <- uncons list
    listIndex cdr (n - 1)

listSetIndex :: Exp -> Int -> Exp -> SMCompiler Exp
listSetIndex list 0 val = do
    (_, cdr) <- uncons list
    return $ CONS val cdr
listSetIndex list n val = do
    (car, cdr) <- uncons list
    cdr' <- listSetIndex cdr (n - 1) val
    return $ CONS car cdr'

setBody :: Term -> SMCompiler ()
setBody body = do
    wrap <- gets compWrap
    label <- gets curLabel
    modify (\x -> x { finalized = True })
    registerFunc $ DEFINE label [PVE "es", PVE "cs", PVE "lv"] $ wrap body

saveLocals :: SMCompiler ()
saveLocals = do
    label <- gets nextLabel
    lv <- gets localVars
    pushToCallStack $ CONS (ATOM label) lv
    modify (\x -> x { localVars = ATOM "Nil" })

jmp :: FName -> SMCompiler ()
jmp label = do
    es <- gets exprStack
    cs <- gets callStack
    lv <- gets localVars
    setBody $ (CALL label [es, cs, lv])

cjmp :: FName -> SMCompiler ()
cjmp label = do
    next <- gets nextLabel
    cond <- popFromExprStack >>= convertToAVal
    es <- gets exprStack
    cs <- gets callStack
    lv <- gets localVars
    setBody $ (ALT (EQA' cond (ATOM "True"))
                  (CALL label [es, cs, lv])
                  (CALL next [es, cs, lv]))


returnFromFunction :: SMCompiler ()
returnFromFunction = do
    (returnLabel, locals) <- popFromCallStack >>= uncons
    es <- gets exprStack
    cs <- gets callStack
    setBody $ (CALL "$dispatch" [es, cs, locals, returnLabel])

condition :: Cond -> SMCompiler ()
condition cond = do
    next <- gets nextLabel
    es <- gets exprStack
    cs <- gets callStack
    lv <- gets localVars
    setBody $ (ALT cond 
                  (CALL next [CONS (ATOM "True") es, cs, lv])
                  (CALL next [CONS (ATOM "False") es, cs, lv]))

listOfNils :: Int -> Exp
listOfNils 0 = ATOM "Nil"
listOfNils n = CONS (ATOM "Nil") (listOfNils (n-1))

compileInstr :: Instr -> SMCompiler ()
compileInstr instr = do
    modify (\x -> x { curInstr = instr })
    case instr of
        Push atom -> pushToExprStack (ATOM atom)
        Cons -> do
            car <- popFromExprStack
            cdr <- popFromExprStack
            pushToExprStack (CONS car cdr)
        Split -> do
            val <- popFromExprStack
            (car, cdr) <- uncons val
            pushToExprStack cdr
            pushToExprStack car
        Test -> do
            val <- popFromExprStack
            condition $ CONS' val (PVE "_") (PVE "_") (PVA "_")
        Eqa -> do
            lhs <- popFromExprStack >>= convertToAVal
            rhs <- popFromExprStack >>= convertToAVal
            condition $ EQA' lhs rhs
        Dup -> do
            val <- popFromExprStack
            pushToExprStack val
            pushToExprStack val
        Drop -> void $ popFromExprStack
        Call label -> do
            saveLocals
            jmp label
        Return -> returnFromFunction
        Exit -> do
            val <- popFromExprStack
            setBody $ RETURN val
        Label _ -> return ()
        Jmp label -> jmp label
        CJmp label -> cjmp label
        Locals n -> modify (\x -> x { localVars = listOfNils n })
        GetLocal n -> do
            lv <- gets localVars
            val <- listIndex lv n
            pushToExprStack val
        SetLocal n -> do
            val <- popFromExprStack
            lv <- gets localVars
            lv' <- listSetIndex lv n val
            modify (\x -> x { localVars = lv' })

compileSM :: Block  -> Prog
compileSM block = evalState (compileMain block) initialState
