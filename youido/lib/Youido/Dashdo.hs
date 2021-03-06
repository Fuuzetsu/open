{-# LANGUAGE OverloadedStrings, ExistentialQuantification, ScopedTypeVariables,
   ExtendedDefaultRules, FlexibleContexts, TemplateHaskell,
   OverloadedLabels, TypeOperators, DataKinds, KindSignatures #-}

module Youido.Dashdo (dashdoGlobal, dashdo, DashdoReq (Initial, InitialWith)) where

import Youido.Types
import Youido.Serve
import Dashdo.Types hiding (FormFields)
import Dashdo.Serve
import Dashdo
import Dashdo.Files
import Control.Monad.IO.Class
import Network.Wai
import Data.Text.Lazy (toStrict)
import Data.Text (Text, pack, unpack, intercalate)
import Data.Monoid
import qualified Data.Text.Lazy as TL
import Lucid
import GHC.OverloadedLabels
import GHC.TypeLits
import Data.Proxy
import Lucid.Bootstrap
import Lucid.Bootstrap3
import Lucid.PreEscaped
import Lens.Micro.Platform


-- | include this once to get global JS and app UUID routes
dashdoGlobal' :: MonadIO m => m (Handler m)
dashdoGlobal' = do
  uuid <- liftIO $ getRandomUUID
  let h1 = H $ \(_ :: "uuid" :/ () ) -> return $ toStrict uuid
  let h2 = H $ \(_ :: "js" :/ "dashdo.js" :/ () ) -> return $ JS dashdoJS
  return $ h1 <> h2

ffsStrict :: [(TL.Text, TL.Text)] -> [(Text, Text)]
ffsStrict ffs = map (\(k,v)-> (TL.toStrict k, TL.toStrict v)) ffs

ffsLazy :: [(Text, Text)] -> [(TL.Text, TL.Text)]
ffsLazy ffs = map (\(k,v)-> (TL.fromStrict k, TL.fromStrict v)) ffs

-- request for a dashdo app
data DashdoReq = Initial
               | InitialWith [(Text, Text)]
               | Submit [(TL.Text, TL.Text)]
               | Action Text [(TL.Text, TL.Text)]

instance FromRequest DashdoReq where
  fromRequest rq = case fromRequest rq of
    Just (Get (Right ()))-> Just Initial
    Just (Post (Left ((_ :/ Name actName (FormFields ffs) :: "action" :/ Name FormFields))))
       -> Just $ Action actName ffs
    Just (Post (Right (FormFields ffs)))
       -> Just $ Submit ffs
    Just (Get (Left ((_ :/ FormFields ffs :: "with" :/ FormFields))))
       -> Just $ InitialWith $ ffsStrict ffs
    Nothing -> Nothing

instance ToURL DashdoReq where
  toURL (InitialWith pars)
    = "/with?"<>(intercalate "&" $ map (\(k,v)->k<>"="<>v) pars)
  toURL _ = "/"

dashdoHandler' :: forall s m t. (KnownSymbol s, MonadIO m, Show t) => Key s -> Dashdo m t -> m (s :/ DashdoReq -> m (MAjax (Html ())))
dashdoHandler' _ d = do
  (_, ff, acts) <- dashdoGenOut d (initial d) []
  let fst3 (x,_,_) = x
      submitPath = pack $ "/"++(symbolVal (Proxy::Proxy s))
      wrapper :: TL.Text -> Html ()
      wrapper h = container_ $ form_ [ action_ submitPath,
                                       method_ "post", id_ "dashdoform"]
                                     $ preEscaped $ TL.toStrict h
      dispatch (_ :/ Initial) = do
        (iniHtml, _, _) <- dashdoGenOut d (initial d) []
        return $ NoAjax $ wrapper iniHtml
      dispatch (_ :/ InitialWith ffs) = do
        let newval = parseForm (initial d) ff $ ffsLazy ffs
        (iniHtml, _, _) <- dashdoGenOut d newval []
        return $ NoAjax $ wrapper iniHtml
      dispatch (_ :/ Submit ffs) = do
        let newval = parseForm (initial d) ff ffs
        (thisHtml, _, _) <- dashdoGenOut d newval []
        return $ Ajax $ wrapper thisHtml
      dispatch (_ :/ Action nm ffs) = do
        let newval = parseForm (initial d) ff ffs
        thisHtml <- case lookup nm acts of
                      Nothing -> do
                        liftIO $ putStrLn $ "Error: no such action"++ unpack nm
                        fmap fst3 $ dashdoGenOut d newval []
                      Just go -> do
                        ares <- go newval
                        case ares of
                          DoNothing -> fmap fst3 $  dashdoGenOut d newval []
                          Reset -> fmap fst3 $ dashdoGenOut d (initial d) []
                          Goto url -> return $
                             "<div data-dashdo-redirect=\""<> TL.pack url <> "\"></div>"
        return $ Ajax $ wrapper thisHtml
  return dispatch

dashdoGlobal :: MonadIO m => YouidoT m ()
dashdoGlobal = do
  dgh <- liftY $ dashdoGlobal'
  handlers %= (dgh:)

dashdo :: forall s m t . (KnownSymbol s, MonadIO m, Show t) => Key s -> Dashdo m t -> YouidoT m ()
dashdo k dd = do
  dh <- liftY $ dashdoHandler' k dd
  handle dh