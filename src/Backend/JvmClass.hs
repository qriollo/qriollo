
{-# LANGUAGE FlexibleInstances #-}

module Backend.JvmClass(
        JClassName,
        JMethodName,
        JJar(..),
        JClass(..),
        JAccessFlag(..),
        JPoolEntry(..),
        JDescriptor(..),
        JType(..),
        JConstant(..),
        JField(..),
        JMethod(..),
        JAttribute(..),
        JInnerClass(..),
        JStackMapFrame(..),
        JException(..),
        JOp(..),
        JLabel,
        Byte, bytecode,
    ) where

import qualified Data.Map as Map(
        Map, empty, lookup, insert, findWithDefault, toList, keys
    )
import Control.Monad(foldM, zipWithM_)
import Control.Monad.Trans.State.Lazy(State, get, put, modify, evalState)
import Data.Char(ord)
import Data.List((\\))
import Data.Bits((.|.))

---- Structures for representing a .class file

type JClassName = String
type JMethodName = String

data JJar = JJar {
              jJar_mainClass :: JClassName,
              jJar_classes   :: [(JClassName, JClass)]
            } 

data JClass = JClass {
                jClass_minorVersion :: Integer,
                jClass_majorVersion :: Integer,
                jClass_constantPool :: [JConstant],
                jClass_accessFlags  :: [JAccessFlag],
                jClass_thisClass    :: JPoolEntry,
                jClass_superClass   :: JPoolEntry,
                jClass_fields       :: [JField],
                jClass_methods      :: [JMethod],
                jClass_attributes   :: [JAttribute]
              }

data JAccessFlag = JAccessFlag_Public
                 | JAccessFlag_Static
                 | JAccessFlag_Abstract

data JPoolEntry = JPoolEntry Integer
  deriving Eq

data JDescriptor = JDescriptor [JType] JType
  deriving Eq

data JType = JType_Void
           | JType_Int
           | JType_Char
           | JType_Boolean
           | JType_Array JType
           | JType_Reference String
  deriving Eq

data JConstant = JConstant_Class       JPoolEntry
               | JConstant_Descriptor  JDescriptor
               | JConstant_Type        JType
               | JConstant_UTF8        String
               | JConstant_NameAndType JPoolEntry JPoolEntry
               | JConstant_MethodRef   JPoolEntry JPoolEntry
               | JConstant_FieldRef    JPoolEntry JPoolEntry
               | JConstant_Integer     Integer
  deriving Eq

data JField = JField {
                jField_flags       :: [JAccessFlag],
                jField_name        :: JPoolEntry,
                jField_type        :: JPoolEntry,
                jField_attributes  :: [JAttribute]
              }

data JMethod = JMethod {
                 jMethod_flags      :: [JAccessFlag],
                 jMethod_name       :: JPoolEntry,
                 jMethod_descriptor :: JPoolEntry,
                 jMethod_attributes :: [JAttribute]
               }

data JAttribute =
     JAttribute_Code {
       jAttribute_Code_name :: JPoolEntry,
       jAttribute_Code_maxStack :: Integer,
       jAttribute_Code_maxLocals :: Integer,
       jAttribute_Code_code :: [JOp],
       jAttribute_Code_exceptions :: [JException],
       jAttribute_Code_attributes :: [JAttribute]
     }
   | JAttribute_InnerClasses {
       jAttribute_InnerClasses_name :: JPoolEntry,
       jAttribute_InnerClasses_innerClasses :: [JInnerClass]
     }
   | JAttribute_StackMapTable {
       jAttribute_StackMapTable_name :: JPoolEntry,
       jAttribute_StackMapTable_stackMapFrames :: [JStackMapFrame]
     }

data JStackMapFrame = JStackMapFrame_Same Integer

data JInnerClass =
     JInnerClass {
       jInnerClass_innerClassInfo :: JPoolEntry,
       jInnerClass_outerClassInfo :: JPoolEntry,
       jInnerClass_innerNameIndex :: JPoolEntry,
       jInnerClass_accessFlags    :: [JAccessFlag]
     }

data JException = JException_NONE

type JLabel = String

data JOp = JOp_Return
         | JOp_Areturn
         | JOp_Pop
         | JOp_Dup
         | JOp_I2C
         | JOp_New JPoolEntry
         | JOp_Bipush Integer
         | JOp_Sipush Integer
         | JOp_Aload_0
         | JOp_Aload_1
         | JOp_Aload_2
         | JOp_Aload_3
         | JOp_Astore_0
         | JOp_Astore_1
         | JOp_Astore_2
         | JOp_Astore_3
         | JOp_Iconst_0
         | JOp_Iconst_1
         | JOp_Iconst_2
         | JOp_Iconst_3
         | JOp_Iconst_4
         | JOp_Iconst_5
         | JOp_InvokeVirtual JPoolEntry
         | JOp_InvokeSpecial JPoolEntry
         | JOp_InvokeStatic  JPoolEntry
         | JOp_GetStatic JPoolEntry
         | JOp_PutStatic JPoolEntry
         | JOp_Anewarray JPoolEntry
         | JOp_Aaload
         | JOp_Aastore
         | JOp_CheckCast JPoolEntry
         | JOp_Label JLabel -- pseudo-instruction
         | JOp_Goto JLabel
         | JOp_IfEq JLabel
         | JOp_IfLt JLabel
         | JOp_IfCmpEq JLabel
         | JOp_IfCmpLe JLabel
         | JOp_InstanceOf JPoolEntry
         | JOp_TableSwitch [JLabel]
         | JOp_Ldc JPoolEntry
         | JOp_Ldc_w JPoolEntry
         | JOp_IAdd
         | JOp_ISub
         | JOp_IInc Byte Byte
         | JOp_Istore_0
         | JOp_Istore_1
         | JOp_Istore_2
         | JOp_Iload_0
         | JOp_Iload_1
         | JOp_Iload_2

---- Dump to bytecode

type Byte = Integer

class Bytecode a where
  bytecode :: a -> [Byte]

u1 :: Integer -> [Integer]
u1 x | 0 <= x && x < 256 = [x]
     | otherwise = error "(Backend.Jvm.u1: byte fuera de rango)"

u1chr :: Char -> [Integer]
u1chr = u1 . fromIntegral . ord

u2 :: Integer -> [Integer]
u2 x | 0 <= x && x < 256 ^ 2 = u1 (x `div` 256) ++ u1 (x `mod` 256)
     | otherwise = error "(Backend.Jvm.u2: word fuera de rango)"

u4 :: Integer -> [Integer]
u4 x | 0 <= x && x < 256 ^ 4 = u2 (x `div` 256^2) ++ u2 (x `mod` 256^2)
     | otherwise = error "(Backend.Jvm.u4: dword fuera de rango)"

u2le :: Integer -> [Integer]
u2le x | 0 <= x && x < 256 ^ 2 = u1 (x `mod` 256) ++ u1 (x `div` 256)
       | otherwise = error "(Backend.Jvm.u2le: word fuera de rango)"

u4le :: Integer -> [Integer]
u4le x | 0 <= x && x < 256 ^ 4 = u2le (x `mod` 256^2) ++ u2le (x `div` 256^2)
       | otherwise = error "(Backend.Jvm.u4le: dword fuera de rango)"


uUTF8 :: String -> [Integer]
uUTF8 = map (fromIntegral . ord)

instance Bytecode JAccessFlag where
  bytecode JAccessFlag_Public   = [0x00, 0x01]
  bytecode JAccessFlag_Static   = [0x00, 0x08]
  bytecode JAccessFlag_Abstract = [0x04, 0x00]

length' :: [a] -> Integer
length' = fromIntegral . length

flagsOr :: Integer -> [[Integer]] -> [Integer]
flagsOr n =
  foldr (\ flag result ->
           if length' flag /= n
            then error "(Backend.Jvm.flagsOr: flags tienen longitud inválida)"
            else zipWith (.|.) flag result)
        (take (fromIntegral n) (repeat 0))

instance Bytecode a => Bytecode [a] where
  bytecode = concatMap bytecode

instance Bytecode JJar where
  bytecode jJar =
      let (fileEntries, fileHeaders) = entries 0 rawEntries
       in
         fileEntries ++
         fileHeaders ++
         zipEnd fileEntries fileHeaders
    where
      numEntries :: Integer
      numEntries = length' rawEntries

      rawEntries :: [(String, [Byte])]
      rawEntries = map (\ (clsname, cls) ->
                          (clsname ++ ".class", bytecode cls))
                       (jJar_classes jJar) ++
                   [("META-INF/MANIFEST.MF",
                     uUTF8 (
                       "Manifest-Version: 1.0\n" ++
                       "Created-By: Qriollo\n" ++
                       "Main-Class: " ++ jJar_mainClass jJar ++ "\n" ++
                       "\n"))]

      entries :: Integer -> [(String, [Byte])] -> ([Byte], [Byte])
      entries _   [] = ([], [])
      entries acc ((filename, bytes) : rest) =
        let (fileEntry, fileHeader) = entry acc filename bytes
            (restEntries, restHeaders) = entries (acc + length' fileEntry) rest
         in
          (fileEntry ++ restEntries,
           fileHeader ++ restHeaders)

      entry :: Integer -> String -> [Byte] -> ([Byte], [Byte])
      entry offset filename bytes = (fileEntry, fileHeader)
        where 
          fileEntry :: [Byte]
          fileEntry = 
            u4le 0x04034b50 ++
            u2le 0x000a ++              -- version needed to extract
            u2le 0x0000 ++              -- general purpose bit flag
            u2le 0x0000 ++              -- compression method (no compression)
            u2le 0x0000 ++              -- last mod file time
            u2le 0x0000 ++              -- last mod file date
            u4le 0 ++                   -- crc32
            u4le (length' bytes) ++     -- compressed size
            u4le (length' bytes) ++     -- uncompressed size
            u2le (length' filename) ++  -- filename length
            u2le 0 ++                   -- extra field length
            concatMap u1chr filename ++ -- filename
                                        -- extra field (empty)
            bytes
          fileHeader :: [Byte]
          fileHeader =
            u4le 0x02014b50 ++
            u2le 0x000a ++              -- version made by
            u2le 0x000a ++              -- version needed to extract
            u2le 0x0000 ++              -- general purpose bit flag
            u2le 0x0000 ++              -- compression method (no compression)
            u2le 0x0000 ++              -- last mod file time
            u2le 0x0000 ++              -- last mod file date
            u4le 0 ++                   -- crc-32
            u4le (length' bytes) ++     -- compressed size
            u4le (length' bytes) ++     -- uncompressed size
            u2le (length' filename) ++  -- filename length
            u2le 0 ++                   -- extra field length
            u2le 0 ++                   -- file comment length
            u2le 0 ++                   -- disk number where file starts
            u2le 0 ++                   -- internal file attributes
            u4le 0 ++                   -- external file attributes
            u4le offset ++              -- relative offset of local file header
            concatMap u1chr filename    -- filename
                                        -- extra field (empty)
                                        -- file comment (empty)

      zipEnd :: [Byte] -> [Byte] -> [Byte]
      zipEnd fileEntries fileHeaders =
        u4le 0x06054b50 ++
        u2le 0x00 ++                  -- number of this disk
        u2le 0x00 ++                  -- number of the disk with the
                                      -- start of the central directory

        u2le numEntries ++            -- total number of entries in the
                                      -- central directory on this disk

        u2le numEntries ++            -- total number of entries in the
                                      -- central directory

        u4le (length' fileHeaders) ++ -- size of the central directory
        u4le (length' fileEntries) ++ -- offset of start of central directory
        u2le 0                        -- comment length
                                      -- comment (empty)

instance Bytecode JClass where
  bytecode jClass = 
    u4 0xcafebabe ++
    u2 (jClass_minorVersion jClass) ++
    u2 (jClass_majorVersion jClass) ++
    -- constant pool
    u2 (length' (jClass_constantPool jClass) + 1) ++
    bytecode (jClass_constantPool jClass) ++
    flagsOr 2 (map bytecode (jClass_accessFlags jClass)) ++
    bytecode (jClass_thisClass jClass) ++
    bytecode (jClass_superClass jClass) ++
    -- interfaces:
    u2 0 ++ --EMPTY 
    -- fields:
    u2 (length' (jClass_fields jClass)) ++
    bytecode (jClass_fields jClass) ++
    -- methods:
    u2 (length' (jClass_methods jClass)) ++
    bytecode (jClass_methods jClass) ++
    -- attributes:
    u2 (length' (jClass_attributes jClass)) ++
    bytecode (jClass_attributes jClass)

descriptorToString :: JDescriptor -> String
descriptorToString (JDescriptor ts t) =
  "(" ++ concatMap typeToString ts ++ ")" ++ typeToString t

typeToString :: JType -> String
typeToString JType_Void          = "V"
typeToString JType_Int           = "I"
typeToString JType_Char          = "C"
typeToString JType_Boolean       = "Z"
typeToString (JType_Array t)     = "[" ++ typeToString t
typeToString (JType_Reference s) = "L" ++ s ++ ";"

instance Bytecode JPoolEntry where
  bytecode (JPoolEntry n) = u2 n

instance Bytecode JConstant where
  bytecode (JConstant_Class entry) =
    [0x07] ++     -- CONSTANT_Class
    bytecode entry
  bytecode (JConstant_Type typ) =
    bytecode (JConstant_UTF8 (typeToString typ))
  bytecode (JConstant_Descriptor descriptor) =
    bytecode (JConstant_UTF8 (descriptorToString descriptor))
  bytecode (JConstant_UTF8 string) =
      [0x01] ++   -- CONSTANT_Utf8
      u2 (length' bs) ++
      bs
    where
      bs = uUTF8 string
  bytecode (JConstant_NameAndType name typ) =
      [0x0c] ++   -- CONSTANT_NameAndType
      bytecode name ++
      bytecode typ
  bytecode (JConstant_MethodRef cls nameAndType) =
      [0x0a] ++   -- CONSTANT_MethodRef
      bytecode cls ++
      bytecode nameAndType
  bytecode (JConstant_FieldRef cls nameAndType) =
      [0x09] ++   -- CONSTANT_FieldRef
      bytecode cls ++
      bytecode nameAndType
  bytecode (JConstant_Integer n) =
      [0x03] ++   -- CONSTANT_Integer
      u4 n

instance Bytecode JField where
  bytecode jField =
    flagsOr 2 (map bytecode (jField_flags jField)) ++
    bytecode (jField_name jField) ++
    bytecode (jField_type jField) ++
    -- attributes:
    u2 (length' (jField_attributes jField)) ++
    bytecode (jField_attributes jField)

instance Bytecode JMethod where
  bytecode jMethod =
    flagsOr 2 (map bytecode (jMethod_flags jMethod)) ++
    bytecode (jMethod_name jMethod) ++
    bytecode (jMethod_descriptor jMethod) ++
    -- attributes:
    u2 (length' (jMethod_attributes jMethod)) ++
    bytecode (jMethod_attributes jMethod)

instance Bytecode JAttribute where
  bytecode jCode@(JAttribute_Code _ _ _ _ _ _) =
      bytecode (jAttribute_Code_name jCode) ++
      u4 thisLength ++
      u2 (jAttribute_Code_maxStack jCode) ++
      u2 (jAttribute_Code_maxLocals jCode) ++
      u4 (length' bCode) ++
      bCode ++
      u2 (length' (jAttribute_Code_exceptions jCode)) ++
      bExceptions ++
      u2 (length' (jAttribute_Code_attributes jCode)) ++
      bAttributes
    where
      thisLength :: Integer
      thisLength =
        12 +
        length' bCode +
        length' bExceptions +
        length' bAttributes

      bCode :: [Byte]
      bCode = opBytecode (jAttribute_Code_code jCode)

      bExceptions :: [Byte]
      bExceptions = bytecode (jAttribute_Code_exceptions jCode)

      bAttributes :: [Byte]
      bAttributes = bytecode (jAttribute_Code_attributes jCode)
  bytecode jInnerClasses@(JAttribute_InnerClasses _ _) =
      bytecode (jAttribute_InnerClasses_name jInnerClasses) ++
      u4 thisLength ++
      u2 (length' (jAttribute_InnerClasses_innerClasses jInnerClasses)) ++
      bInnerClasses
    where
      thisLength :: Integer
      thisLength = 2 + length' bInnerClasses

      bInnerClasses :: [Byte]
      bInnerClasses =
        bytecode (jAttribute_InnerClasses_innerClasses jInnerClasses)
  bytecode jStackMapTable@(JAttribute_StackMapTable _ _) =
      bytecode (jAttribute_StackMapTable_name jStackMapTable) ++
      u4 thisLength ++
      u2 (length' (jAttribute_StackMapTable_stackMapFrames jStackMapTable)) ++
      bStackMapFrames
    where
      thisLength :: Integer
      thisLength = 2 + length' bStackMapFrames

      bStackMapFrames :: [Byte]
      bStackMapFrames =
        bytecode (jAttribute_StackMapTable_stackMapFrames jStackMapTable)

instance Bytecode JStackMapFrame where
  bytecode (JStackMapFrame_Same k)
    | 0 <= k && k < 64 = [k]

instance Bytecode JInnerClass where
  bytecode jInnerClass =
    bytecode (jInnerClass_innerClassInfo jInnerClass) ++
    bytecode (jInnerClass_outerClassInfo jInnerClass) ++
    bytecode (jInnerClass_innerNameIndex jInnerClass) ++
    flagsOr 2 (map bytecode (jInnerClass_accessFlags jInnerClass))

instance Bytecode JException where
  bytecode JException_NONE =
    error "(Backend.Jvm: manejo de excepciones en la JVM no implementada aún)"

----

data JOpState =
     JOpState {
         jOpCurrentPosition :: Integer,

         -- Destination of each label
         jOpLabelDestinations :: Map.Map JLabel Integer,

         -- Positions in the bytecode that should be backpatched
         jOpPendingBackpatches :: Map.Map JLabel [JBackpatch]
     }

data JBackpatch =
     JBackpatch {
         jBackpatch_source      :: Integer,
         jBackpatch_labelOffset :: Integer,
         jBackpatch_labelSize   :: Integer
     }

type JOpM = State JOpState

opBytecode :: [JOp] -> [Byte]
opBytecode code =
    evalState (assemble code) initialState
  where
    initialState :: JOpState
    initialState = JOpState {
                     jOpCurrentPosition = 0,
                     jOpLabelDestinations = Map.empty,
                     jOpPendingBackpatches = Map.empty
                   }

    assemble :: [JOp] -> JOpM [Byte]
    assemble code = do
      bytecode <- opsbytes code
      state <- get
      () <- checkNoPendingBackpatches
      foldM solveBackpatches
            bytecode
            (Map.toList (jOpLabelDestinations state))

    checkNoPendingBackpatches :: JOpM ()
    checkNoPendingBackpatches = do
      state <- get
      let ls = Map.keys (jOpPendingBackpatches state) \\
               Map.keys (jOpLabelDestinations state)
       in
        if null ls
         then return ()
         else error (
                "(opBytecode: " ++
                "el destino de las etiquetas de la JVM " ++ show ls
                 ++ " no fue definido)")

    opsbytes :: [JOp] -> JOpM [Byte]
    opsbytes []         = return []
    opsbytes (op : ops) = do
      bop  <- opbytes op
      modify (\ state -> state {
        jOpCurrentPosition = jOpCurrentPosition state +
                             fromIntegral (length bop)
      })
      bops <- opsbytes ops
      return $ bop ++ bops

    opbytes :: JOp -> JOpM [Byte]
    opbytes (JOp_Bipush n)
      | 0 <= n && n < 2^7   = return $ [0x10] ++ u1 n
    opbytes (JOp_Sipush n)
      | 0 <= n && n < 2^15  = return $ [0x11] ++ u2 n
    opbytes JOp_Return      = return $ [0xb1]
    opbytes JOp_Areturn     = return $ [0xb0]
    opbytes JOp_Pop         = return $ [0x57]
    opbytes JOp_Dup         = return $ [0x59]
    opbytes JOp_I2C         = return $ [0x92]
    opbytes (JOp_New entry) = return $ [0xbb] ++ bytecode entry
    opbytes JOp_Aload_0     = return $ [0x2a]
    opbytes JOp_Aload_1     = return $ [0x2b]
    opbytes JOp_Aload_2     = return $ [0x2c]
    opbytes JOp_Aload_3     = return $ [0x2d]
    opbytes JOp_Astore_0    = return $ [0x4b]
    opbytes JOp_Astore_1    = return $ [0x4c]
    opbytes JOp_Astore_2    = return $ [0x4d]
    opbytes JOp_Astore_3    = return $ [0x4e]
    opbytes (JOp_InvokeVirtual entry) = return $ [0xb6] ++ bytecode entry
    opbytes (JOp_InvokeSpecial entry) = return $ [0xb7] ++ bytecode entry
    opbytes (JOp_InvokeStatic entry)  = return $ [0xb8] ++ bytecode entry
    opbytes (JOp_GetStatic entry) = return $ [0xb2] ++ bytecode entry
    opbytes (JOp_PutStatic entry) = return $ [0xb3] ++ bytecode entry
    opbytes (JOp_Anewarray entry) = return $ [0xbd] ++ bytecode entry
    opbytes JOp_Iconst_0 = return $ [0x03]
    opbytes JOp_Iconst_1 = return $ [0x04]
    opbytes JOp_Iconst_2 = return $ [0x05]
    opbytes JOp_Iconst_3 = return $ [0x06]
    opbytes JOp_Iconst_4 = return $ [0x07]
    opbytes JOp_Iconst_5 = return $ [0x08]
    opbytes JOp_Aaload  = return $ [0x32]
    opbytes JOp_Aastore = return $ [0x53]
    opbytes (JOp_CheckCast entry) = return $ [0xc0] ++ bytecode entry
    opbytes (JOp_Label label) = do
      modify (\ state -> state {
        jOpLabelDestinations = Map.insert label (jOpCurrentPosition state)
                                                (jOpLabelDestinations state)
      })
      return []
    opbytes (JOp_Goto label) = do
      addPendingBackpatchFor label 1 2
      return $ [0xa7] ++ [0, 0]
    opbytes (JOp_IfEq label) = do
      addPendingBackpatchFor label 1 2
      return $ [0x99] ++ [0, 0]
    opbytes (JOp_IfLt label) = do
      addPendingBackpatchFor label 1 2
      return $ [0x9b] ++ [0, 0]
    opbytes (JOp_IfCmpEq label) = do
      addPendingBackpatchFor label 1 2
      return $ [0x9f] ++ [0, 0]
    opbytes (JOp_IfCmpLe label) = do
      addPendingBackpatchFor label 1 2
      return $ [0xa4] ++ [0, 0]
    opbytes (JOp_InstanceOf entry) =
      return $ [0xc1] ++ bytecode entry
    opbytes (JOp_TableSwitch labels) = do
      pos <- getCurrentPosition
      let padsize = (4 - (pos + 1) `mod` 4) `mod` 4
          padding = take (fromIntegral padsize) (repeat 0x0)
       in do
         zipWithM_
           (\ i label -> addPendingBackpatchFor
                           label
                           (1 + padsize + 12 + 4 * i)
                           4)
           [0..]
           labels 
         return $ [0xaa] ++
                  padding ++
                  -- default: address of the first branch
                  --          (should not be taken(!))
                  u4 (1 + padsize + 12 + 4 * fromIntegral (length labels)) ++
                  -- low:
                  u4 0 ++
                  -- high:
                  u4 (fromIntegral (length labels) - 1) ++
                  -- jump offsets:
                  take (4 * length labels) (repeat 0x0)
    opbytes (JOp_Ldc (JPoolEntry n))
      | 0 <= n && n < 256 = return $ [0x12] ++ u1 n
      | otherwise         = return $ [0x13] ++ bytecode (JPoolEntry n)
    opbytes JOp_IAdd = return [0x60]
    opbytes JOp_ISub = return [0x64]
    opbytes (JOp_IInc l i) = return $ [0x84] ++ u1_signed l ++ u1_signed i
    opbytes JOp_Istore_0 = return [0x3b]
    opbytes JOp_Istore_1 = return [0x3c]
    opbytes JOp_Istore_2 = return [0x3d]
    opbytes JOp_Iload_0 = return [0x1a]
    opbytes JOp_Iload_1 = return [0x1b]
    opbytes JOp_Iload_2 = return [0x1c]

    getCurrentPosition :: JOpM Integer
    getCurrentPosition = do
      state <- get
      return $ jOpCurrentPosition state

    addPendingBackpatchFor :: JLabel -> Integer -> Integer -> JOpM ()
    addPendingBackpatchFor label labelOffset labelSize = do
      src <- getCurrentPosition
      addPendingBackpatch
        label
        (JBackpatch {
          jBackpatch_source = src,
          jBackpatch_labelOffset = labelOffset,
          jBackpatch_labelSize = labelSize
        })

    addPendingBackpatch :: JLabel -> JBackpatch -> JOpM ()
    addPendingBackpatch label pendingBackpatch = do
      modify (\ state -> state {
        jOpPendingBackpatches =
          Map.insert
            label
            (pendingBackpatch :
             Map.findWithDefault [] label (jOpPendingBackpatches state))
            (jOpPendingBackpatches state)
      })

    solveBackpatches :: [Byte] -> (JLabel, Integer) -> JOpM [Byte]
    solveBackpatches code (label, dst) = do
        state <- get
        foldM solveBackpatch
              code
              (Map.findWithDefault []
                  label
                  (jOpPendingBackpatches state))
      where
        solveBackpatch :: [Byte] -> JBackpatch -> JOpM [Byte]
        solveBackpatch code backpatch =
          let src = jBackpatch_source backpatch
              labelPos = src + jBackpatch_labelOffset backpatch
              labelSize = jBackpatch_labelSize backpatch
              delta = dst - src
              deltaBytes = signed labelSize delta
              (code1, code2) = splitAt (fromIntegral labelPos) code
           in return $ code1 ++
                       deltaBytes ++
                       drop (fromIntegral labelSize) code2

    signed :: Integer -> Integer -> [Byte]
    signed 2 n = u2_signed n
    signed 4 n = u4_signed n

    u1_signed :: Integer -> [Byte]
    u1_signed k
      | k > 0 = u1 k
      | k < 0 = u1 (2 ^ 8 + k)

    u2_signed :: Integer -> [Byte]
    u2_signed k
      | k > 0 = u2 k
      | k < 0 = u2 (2 ^ 16 + k)

    u4_signed :: Integer -> [Byte]
    u4_signed k
      | k > 0 = u4 k
      | k < 0 = u4 (2 ^ 32 + k)

