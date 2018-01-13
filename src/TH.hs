{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module TH where

import Protolude
import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Data.Coerce
import Data.Foldable (toList)
import GHC.Err (error)
import Data.List (lookup)

pattern Y :: Show a => a -> a
pattern Y a <- (\a -> trace ("DEBUG: " ++ show a) a -> a)
  where Y (!a) = trace ("DEBUG 2: " ++ show a) a `seq` a

data Variables = Var { typeArgs :: [Name], wrappedArgs :: [Name] }
  deriving Show

deriveVia :: Name -> Name -> Name -> Q [Dec]
deriveVia semi instanceType via_newtype = do
  DTyConI decs _ <- (dsInfo <=< reify) semi

  Just (DTyConI info1 insts1) <- dsReify semi
  Just (DTyConI info2 _) <- dsReify instanceType
  Just (DTyConI info3 _) <- dsReify via_newtype

  Y vars <- case (getKind info1, getKind info2, getKind info3) of
    (STAR, STAR:>CONSTRAINT, _) -> 
      pure Var { typeArgs = [], wrappedArgs = [] }

    (STAR:>CONSTRAINT, STAR, STAR:>STAR) -> 
      pure Var { typeArgs = [], wrappedArgs = [] }

    ((STAR:>STAR):>CONSTRAINT, STAR:>STAR, (STAR:>STAR):>(STAR:>STAR)) -> 
      pure Var { typeArgs = [], wrappedArgs = [] }

    -- deriveVia ''Functor ''PAIR ''WrappedBifunctor
    --
    -- instance Functor (PAIR z) where
    --   fmap :: forall a b. (a -> b) -> PAIR z a -> PAIR z b
    --   fmap = coerce (fmap @(WrappedBifunctor PAIR z) @a @b)
    (   (STAR:>STAR):>CONSTRAINT
      , (STAR:>STAR):>STAR
      , (STAR:>(STAR:>STAR)) :> (STAR:>(STAR:>STAR))) -> do
      zzz <- newName "zzz"
      pure Var { typeArgs = [], wrappedArgs = [zzz] }

    -- (STAR:>CONSTRAINT, STAR, STAR:>STAR) -> 
    --   undefined
    -- deriveVia ''Num ''Sorted ''WrappedApplicative
    -- instance Num a => Num (Sorted a) where
     --   (+) :: Sorted a -> Sorted a -> Sorted a
     --   (+) = coerce ((+) @(WrappedApplicative Sorted a))

    (STAR:>CONSTRAINT, STAR:>STAR, (STAR:>STAR):>(STAR:>STAR)) -> do
      xxx <- newName "xxx"
      pure Var { typeArgs = [], wrappedArgs = [xxx] }

    -- deriveVia ''IsZero ''Sorted ''WrappedNumEq
    -- 
    -- instance (Num a, Eq a) => IsZero (Sorted a) where
    --   isZero :: Sorted a -> Bool
    --   isZero = coerce (isZero @(WrappedNumEq (Sorted a)))
    (STAR:>CONSTRAINT, STAR:>STAR, STAR:>STAR) -> do
      yyy <- newName "yyy"
      pure Var { typeArgs = [yyy], wrappedArgs = [] }

    ( (STAR :> (STAR :> STAR)) :> CONSTRAINT
      , STAR :> (STAR :> STAR) 
      , (STAR :> (STAR :> STAR)) :> (STAR :> (STAR :> STAR))) ->
        -- yyy <- newName "yyy"
        pure Var { typeArgs = [], wrappedArgs = [] }

    (   (STAR:>STAR):>CONSTRAINT 
      , STAR:>(STAR:>STAR)
      , (STAR:>(STAR:>STAR)) :> (STAR:>(STAR:>STAR))) -> do
        yyy <- newName "yyy"
        pure Var { typeArgs = [], wrappedArgs = [yyy] }

  let 
    missingContext :: DCxt
    missingContext = 
      case (info1, insts1, info3) of
        (DDataD _ _ ze_num _ _ _, Just instances, DDataD _ _ ze_wrapAp _ _ _) -> 
          makeContext (whichVarsToLookOutFor ze_num ze_wrapAp instances)

        (DClassD _ ze_num _ _ _, Just instances, DDataD _ _ ze_wrapAp _ _ _) -> 
          makeContext (whichVarsToLookOutFor ze_num ze_wrapAp instances)

        (_, Nothing, _) -> []
        (DClassD {}, _, _) -> []

    whichVarsToLookOutFor :: Name -> Name -> [DDec] -> [(Name, Name)]
    whichVarsToLookOutFor ze_num ze_wrapAp = foldMap $ \case
      DInstanceD _ _ctx ty _decs -> 
        case ty of
          (DConT num `DAppT` (DConT wrappedApplicative `DAppT` DVarT _ `DAppT` DVarT a))
            | ze_num    == num
            , ze_wrapAp == wrappedApplicative 
            , Var { typeArgs = [], wrappedArgs = [new] } <- vars
           -> [(a, new)]

          DConT isZero `DAppT` (DConT wrappedShow `DAppT` DVarT a) 
            | ze_num    == isZero
            , ze_wrapAp == wrappedShow 
            , Var { typeArgs = [new], wrappedArgs = [] } <- vars
           -> [(a, new)]

          DConT _ `DAppT` DConT _ -> []

          DConT _ `DAppT ` ((DConT _ `DAppT` DVarT _) `DAppT` DVarT _) -> []

          DAppT (DConT _) (DAppT (DConT _) (DVarT _)) -> []

          DAppT (DConT _) (DAppT (DAppT DArrowT (DVarT _)) (DVarT _)) -> []

          DAppT (DConT _) (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) -> []

          DAppT (DConT _) (DAppT (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) (DVarT _)) -> []
  
          DAppT (DConT _) (DAppT (DAppT (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) (DVarT _)) (DVarT _)) -> []


          DAppT (DConT _) (DSigT (DAppT (DConT _) (DVarT _)) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DConT _) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) (DVarT _)) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DConT _) (DAppT (DConT _) (DConT _))) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DConT _) (DConT _)) (DAppT (DAppT DArrowT DStarT) DStarT)) -> []

          DAppT (DConT _) (DSigT (DAppT (DConT _) (DVarT _)) (DAppT (DAppT DArrowT DStarT) (DAppT (DAppT DArrowT DStarT) DStarT))) -> []

          DAppT (DConT _) (DSigT (DConT _) (DAppT (DAppT DArrowT DStarT) (DAppT (DAppT DArrowT DStarT) DStarT))) -> []

          DAppT (DConT _) (DSigT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DAppT (DAppT DArrowT DStarT) (DAppT (DAppT DArrowT DStarT) DStarT))) -> []

          DAppT (DConT _) (DSigT (DAppT (DAppT (DAppT (DConT _) (DVarT _)) (DVarT _)) (DVarT _)) (DAppT (DAppT DArrowT DStarT) (DAppT (DAppT DArrowT DStarT) DStarT))) -> []
  
          a -> error ("ERROR WITH whichVarsToLookOutFor: " ++ show a)
          
          -- _ -> []
 
    makeContext :: [(Name, Name)] -> [DPred]
    makeContext vars' = do
      let has :: DPred -> Maybe DPred
          has = \case
             DAppPr f (DVarT a) -> do
               a' <- lookup a vars'
               f' <- has f
               pure (DAppPr f' (DVarT a'))

             DConPr name' -> 
               case lookup name' vars' of
                  Just a ->  pure $ DConPr a
                  Nothing -> pure $ DConPr name'

             _ -> Nothing

      case insts1 of
        Just instances -> 
          flip foldMap instances $ \case 
              DInstanceD _ ctx _ _ -> foldMap (toList . has)  ctx

      --  TODO order of typeArgs / wrappedArgs
    saturatedInstanceType :: DType    
    saturatedInstanceType = foldl (\acc x -> acc `DAppT` DVarT x) (DConT instanceType) (typeArgs vars ++ wrappedArgs vars)

    instanceHead :: DType
    instanceHead = DConT semi `DAppT` saturatedInstanceType

    coerceType :: DType
    coerceType 
      | Var { wrappedArgs = [], typeArgs = [] } <- vars
      = DConT via_newtype `DAppT` DConT instanceType

      | Var { typeArgs = [], wrappedArgs = [xxx] } <- vars
      = (DConT via_newtype `DAppT` DConT instanceType) `DAppT` DVarT xxx

      | Var { typeArgs = [xxx], wrappedArgs = [] } <- vars
      = DConT via_newtype `DAppT` (DConT instanceType `DAppT` DVarT xxx)

      | Var { typeArgs = [xxx], wrappedArgs = [_] } <- vars
      = (DConT via_newtype `DAppT` DConT instanceType) `DAppT` DVarT xxx

    methods :: [DDec]
    (_, _, methods) = classAndMethods decs

    methods' :: [DDec]
    methods' = methods >>= coerceMethod coerceType instanceType saturatedInstanceType

  pure $ case vars of
    Var { typeArgs = [], wrappedArgs = [] } -> 
      sweeten [DInstanceD Nothing [] instanceHead methods']

    Var { typeArgs = [x], wrappedArgs = [] } -> 
      sweeten [DInstanceD Nothing missingContext instanceHead methods']

    Var { typeArgs = [], wrappedArgs = [x] } -> 
      sweeten [DInstanceD Nothing missingContext instanceHead methods']

    Var { typeArgs = [y], wrappedArgs = [x] } -> 
      sweeten [DInstanceD Nothing missingContext instanceHead methods']

classAndMethods :: DDec -> (Name, Name, [DDec])
classAndMethods (DClassD _ctx semi [getName -> name] [] methods) = (semi, name, methods)
classAndMethods _                                                = error "ERROR WITH classAndMethods"

removeForall :: DType -> DType
removeForall = \case
  DForallT _ _ ty -> removeForall ty
  DAppT f x       -> removeForall f `DAppT` removeForall x
  DSigT f x       -> removeForall f `DSigT` removeForall x
  x               -> x

coerceMethod :: DType -> Name -> DType -> DDec -> [DDec]
coerceMethod _ _ _ DDefaultSigD{} = [] 
coerceMethod wrapped_app_ty instanceType saturatedInstanceType (DLetDec (DSigD methodName methodTy)) = [signature, definition]

  where
  signature :: DDec
  signature = DLetDec $ DSigD methodName (removeWith f ty) where
    ty :: DType
    DForallT [DKindedTV f _] _ ty = methodTy

  definition :: DDec
  definition = DLetDec $ DValD (DVarPa methodName) body

  body :: DExp
  body = 
    DVarE 'coerce
    `DAppE`
    method' (DVarE methodName `DAppTypeE` wrapped_app_ty) (map getName vars) where 
      vars = case methodTy of
        DForallT _ _ (DForallT vars' _ _) -> vars'
        _ -> []

  method' :: DExp -> [Name] -> DExp
  method' = foldl (\acc x -> acc `DAppTypeE` DVarT x)

  removeWith :: Name -> DType -> DType
  removeWith f_name = \case
    DAppT f x ->
      DAppT (removeWith f_name f) (removeWith f_name x)

    DForallT tyVars ctxs ty
      | let vars = [ var | var <- tyVars, getName var /= instanceType ]
     -> if null vars
        then removeWith f_name ty
        else DForallT
          vars
          ctxs
          (removeWith f_name ty)

    DArrowT ->
      DArrowT

    DVarT var
      | var == f_name
     -> saturatedInstanceType

      | otherwise
     -> DVarT var

    a -> a

getName :: DTyVarBndr -> Name
getName = \case
  DPlainTV  name   -> name
  DKindedTV name _ -> name

infixr :>
data KIND = STAR | KIND :> KIND | CONSTRAINT
  deriving Show

getKind :: DDec -> KIND
getKind (DDataD _ _ _ [] _ _) =
  STAR

getKind (DDataD _ _ _ [DKindedTV _ kind] _ _) = 
  case kind of
    DStarT -> 
      STAR :> STAR

getKind (DDataD _ _ _ [DKindedTV _ kind, DKindedTV _ kind'] _ _) = 
  case (kind, kind') of
    (DStarT, DStarT) -> 
      STAR :> (STAR :> STAR)

    ((DArrowT `DAppT` DStarT) `DAppT` DStarT, DStarT) -> 
      (STAR :> STAR) :> (STAR :> STAR)

    ((DArrowT `DAppT` DVarT k) `DAppT` DStarT, DVarT k') | k == k' -> 
      (STAR :> STAR) :> (STAR :> STAR)

getKind (DDataD _ _ _ [DKindedTV _ kind, DKindedTV _ kind', DKindedTV _ kind''] _ _) = 
  case (kind, kind', kind'') of
    ( (DArrowT `DAppT` DVarT k) `DAppT` ((DArrowT `DAppT` DVarT k1) `DAppT` DStarT)
      , DVarT k'
      , DVarT k1' ) | (k, k1) == (k', k1') -> (STAR:>(STAR:>STAR)) :> (STAR:>(STAR:>STAR))

  -- [DKindedTV p ((DArrowT `DAppT` DVarT k) `DAppT` ((DArrowT `DAppT` DVarT k1) `DAppT` DStarT))
  -- ,DKindedTV a (DVarT k),DKindedTV b (DVarT k1)] 

getKind (DClassD _ _  [DKindedTV _ kind] _ _) = 
  case kind of
    DStarT ->
      STAR :> CONSTRAINT
    (DArrowT `DAppT` DStarT) `DAppT` DStarT -> 
      (STAR :> STAR) :> CONSTRAINT

    (DArrowT `DAppT` DStarT) `DAppT` ((DArrowT `DAppT` DStarT) `DAppT` DStarT) -> 
      (STAR :> (STAR :> STAR)) :> CONSTRAINT

    a -> error ("ERROR WITH getKind DClassD --> " ++ show a)

getKind a = error ("ERROR WITH getKind --> " ++ show a)
