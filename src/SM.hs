{-# LANGUAGE OverloadedStrings #-}

module SM (Block, Instr(..), compileSM, splitIntoChunks) where

import Lang hiding (State)

import qualified Data.Text as T
import Debug.Trace
import Data.List hiding (uncons)
import Data.Maybe
import Control.Monad
import Control.Monad.State

import qualified Data.Map.Strict as M

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
           | Main [T.Text]
           | Trace
           deriving (Eq, Show)

data CState = CState { defs :: [FDef]
                     , nextLabel :: FName
                     , curLabel :: FName
                     , exprStack :: EVar
                     , callStack :: EVar
                     , localVars :: [EVar]
                     , nVars :: Int
                     , compWrap :: Term -> Term
                     , finalized :: Bool
                     , curInstr :: Instr
                     , curParams :: [Param]
                     , curLocals :: Int
                     , funcLocals :: M.Map FName Int
                     , callSites :: M.Map FName [FName]
                     , curFunc :: FName
                     , mainArgs :: [T.Text]
                     }

type SMCompiler = State CState

data Chunk = Chunk FName Block
    deriving (Eq, Show)

initialState :: CState
initialState = CState { defs = []
                      , nextLabel = ""
                      , curLabel = ""
                      , exprStack = ATOM "Nil"
                      , callStack = ATOM "Nil"
                      , localVars = []
                      , nVars = 0
                      , compWrap = id
                      , finalized = False
                      , curInstr = Exit
                      , curParams = []
                      , curLocals = 0
                      , funcLocals = M.empty
                      , callSites = M.empty
                      , curFunc = ""
                      , mainArgs = []
                      }

getFuncName :: Int -> FName
getFuncName f = "$" <> (T.pack $ show f)

registerFunc :: FDef -> SMCompiler ()
registerFunc f = modify (\x -> x { defs = f:(defs x) })

getFuncLocals :: FName -> SMCompiler Int
getFuncLocals fname = do
    locals <- gets funcLocals
    case M.lookup fname locals of
      Nothing -> error $ T.unpack $ "Calling undefined function " <> fname
      Just v -> return v

generateCall :: Exp -> Exp -> FName -> SMCompiler Term
generateCall exprStack callStack fname = do
    nLocals <- getFuncLocals fname
    return $ CALL fname ([exprStack, callStack] <> replicate nLocals (ATOM "Nil"))

generateJump :: FName -> SMCompiler Term
generateJump label = do
    es <- gets exprStack
    cs <- gets callStack
    lv <- gets localVars
    return $ CALL label $ [es, cs] <> lv

compileMain :: Block -> SMCompiler Prog
compileMain block = do
    void $ compileBlock (block ++ [Label "$exit", Locals 0, Exit])
    argv <- map PVE <$> gets mainArgs
    fs <- gets defs
    call <- generateCall (reprList $ reverse argv) (CONS (CONS (ATOM "$exit") (ATOM "Nil")) (ATOM "Nil")) "main"
    return $ (DEFINE "$start" argv call):fs

splitIntoChunks :: Block -> [Chunk]
splitIntoChunks block =
    filter (\(Chunk _ b) -> not $ null b) $
        map (\(Chunk clabel cblock) -> Chunk clabel (reverse cblock)) $
            f block (Chunk "" []) 0
    where
      f [] cur _ = [cur]
      f (x:xs) cur@(Chunk clabel cblock) cnt =
          let end = (Chunk clabel (x:cblock)):(f xs (Chunk ("$R" <> (T.pack $ show cnt)) []) (cnt + 1)) in
              case x of
                Label label -> cur:(f xs (Chunk label [x]) cnt)
                Call _ -> end
                Test -> end
                Eqa -> end
                CJmp _ -> end
                _ -> f xs (Chunk clabel (x:cblock)) cnt

registerChunk :: (Chunk, FName) -> SMCompiler ()
registerChunk ((Chunk clabel block), label) = do
    case block of
      (Label _):(Locals n):_ -> modify (\x -> x { curLocals = n })
      _ -> return ()
    modify (\x -> x { funcLocals = M.insert clabel (curLocals x) (funcLocals x) })
    let calls = [label | (Call label) <- block]
    forM_ calls $ \func -> do
        modify (\x -> x { callSites = M.alter (\v -> case v of 
                                                       Nothing -> Just $ [label]
                                                       Just xs -> Just $ label:xs
                                              ) func (callSites x)
                        })

compileBlock :: Block -> SMCompiler FName
compileBlock block = do
    let chunks = splitIntoChunks block
    let chunksWithNext = zip chunks $ (map (\(Chunk clabel _) -> clabel) $ tail chunks) <> [""]
    mapM_ registerChunk chunksWithNext
    cs <- gets callSites
    mapM_ compileChunk chunksWithNext
    let (Chunk label _) = head chunks
    return label

freshVarName :: SMCompiler VName
freshVarName = do
    n <- gets nVars
    modify (\x -> x { nVars = n + 1 })
    return $ "!" <> (T.pack  $ show n)

freshEVar :: SMCompiler EVar
freshEVar = PVE <$> freshVarName

freshAVar :: SMCompiler EVar
freshAVar = PVA <$> freshVarName

compileChunk :: (Chunk, FName) -> SMCompiler ()
compileChunk ((Chunk clabel block), label) = do
    modify (\x -> x { nVars = 0} )
    nLocals <- getFuncLocals clabel
    exprStackName <- freshEVar
    callStackName <- freshEVar
    localNames <- replicateM nLocals freshEVar
    modify (\x -> x { nextLabel = label
                    , curLabel = clabel
                    , exprStack = exprStackName
                    , callStack = callStackName
                    , localVars = localNames
                    , compWrap = id
                    , finalized = False
                    , curInstr = Exit
                    , curParams = [exprStackName, callStackName] <> localNames
                    })
    mapM_ compileInstr block
    isFinal <- gets finalized
    unless isFinal $ jmp label

panic :: T.Text -> Exp -> SMCompiler Term
panic msg info = do
    label <- gets curLabel
    func <- gets curFunc
    instr <- gets curInstr
    return $ RETURN (CONS (ATOM ("panic: " <> msg <> " in " <> label <> " (" <> func <> ") in " <> (T.pack $ show instr))) info)

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
    case oldStack of
      CONS car cdr -> do
          modify (\x -> x { exprStack = cdr })
          return car
      _ -> do
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

setBody :: Term -> SMCompiler ()
setBody body = do
    wrap <- gets compWrap
    label <- gets curLabel
    params <- gets curParams
    modify (\x -> x { finalized = True })
    registerFunc $ DEFINE label params $ wrap body

callFunction :: FName -> SMCompiler ()
callFunction fname = do
    lv <- gets localVars
    next <- gets nextLabel
    pushToCallStack $ CONS (ATOM next) (reprList lv)
    es <- gets exprStack
    cs <- gets callStack
    x <- generateCall es cs fname
    setBody x

jmp :: FName -> SMCompiler ()
jmp label = generateJump label >>= setBody

cjmp :: FName -> SMCompiler ()
cjmp label = do
    next <- gets nextLabel
    cond <- popFromExprStack >>= convertToAVal
    jTrue <- generateJump label
    jFalse <- generateJump next
    setBody $ ALT (EQA' cond (ATOM "True")) jTrue jFalse

generateDispatch :: AVar -> Exp -> FName -> SMCompiler (Term -> Term)
generateDispatch returnLabel locals fname = do
    nLocals <- getFuncLocals fname
    tmpVars <- replicateM nLocals freshEVar
    modify (\x -> x { localVars = tmpVars })
    let t = map (\x -> \body -> ALT (CONS' locals x locals (PVA "_")) body (RETURN (ATOM "failed to pop locals"))) tmpVars
    call <- generateJump fname
    let newBody = (foldr (.) id t) call
    return $ ALT (EQA' returnLabel (ATOM fname)) newBody

returnFromFunction :: SMCompiler ()
returnFromFunction = do
    current <- gets curFunc
    (returnLabel, locals) <- popFromCallStack >>= uncons
    possibleCallers <- (fromMaybe [] . M.lookup current) <$> gets callSites
    t <- mapM (generateDispatch returnLabel locals) ("$exit":possibleCallers)
    setBody $ (foldr (.) id t) (RETURN (ATOM $ "failed to return from " <> current))

condition :: Cond -> SMCompiler ()
condition cond = do
    next <- gets nextLabel

    pushToExprStack $ ATOM "True"
    jTrue <- generateJump next
    popFromExprStack

    pushToExprStack $ ATOM "False"
    jFalse <- generateJump next
    popFromExprStack

    setBody $ (ALT cond jTrue jFalse)

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
        Call label -> callFunction label
        Return -> returnFromFunction
        Exit -> do
            val <- popFromExprStack
            setBody $ RETURN val
        Label _ -> return ()
        Jmp label -> jmp label
        CJmp label -> cjmp label
        Locals n -> modify (\x -> x { curFunc = (curLabel x) })
        GetLocal n -> do
            lv <- gets localVars
            pushToExprStack $ lv !! n
        SetLocal n -> do
            val <- popFromExprStack
            lv <- gets localVars
            let (a, b) = splitAt n lv
            modify (\x -> x { localVars = a <> [val] <> (tail b) })
        Main argv -> modify (\x -> x { mainArgs = argv })
        Trace -> do
            val <- popFromExprStack
            oldWrap <- gets compWrap
            let newWrap body = oldWrap $ TRACE val body
            modify (\x -> x { compWrap = newWrap })

compileSM :: Block  -> Prog
compileSM block = evalState (compileMain block) initialState
