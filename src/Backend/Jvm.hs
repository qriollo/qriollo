
-- Este archivo es parte de Qriollo.

-- Qriollo is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- Qriollo is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with Qriollo.  If not, see <http://www.gnu.org/licenses/>.

module Backend.Jvm(
        compileToJvm, JvmOptions(..), JvmOptionsToplevel(..)
    ) where

import Data.Char(chr, ord)
import Control.Monad(zipWithM)
import Control.Monad.Trans.State.Lazy(State, get, modify, runState)
import Data.List(findIndex, isPrefixOf)
import qualified Data.Map as Map(
        Map, empty, lookup, insert, fromList, toList, findWithDefault
    )

import ExpressionE
import ExpressionL
import ExpressionK
import Backend.JvmClass

data JvmOptionsToplevel = JvmOpt_ToplevelExit
                        | JvmOpt_ToplevelShowAsString
  deriving (Read, Eq)

data JvmOptions = JvmOptions {
                    jvoToplevel :: JvmOptionsToplevel
                  }

data JvmState =
   JvmState {
     jvsClasses :: Map.Map String JClass,
     jvsLabelClassIndices :: Map.Map IdK JPoolEntry,
     jvsLabelParameters :: Map.Map IdK [IdK],
     jvsCurrentClassName :: JClassName,
     jvsDefinedRegisters :: Map.Map Integer (),
     jvsNextFreshLabel :: Integer,
     jvsStringCasts :: Map.Map JClassName (JPoolEntry, JPoolEntry)
   }
type JvmM = State JvmState

type JFieldIndex = Integer

data JClassSignature =
     JClassSignature {
         jClassSignature_name       :: JClassName,
         jClassSignature_flags      :: [JAccessFlag],
         jClassSignature_superclass :: JClassName
     }

data JMethodSignature =
     JMethodSignature {
         jMethodSignature_classname  :: JClassName,
         jMethodSignature_name       :: JMethodName,
         jMethodSignature_flags      :: [JAccessFlag],
         jMethodSignature_descriptor :: JDescriptor,
         jMethodSignature_code       :: Maybe [JOp],
         jMethodSignature_codeAttrs  :: [JAttribute]
     }

data JMethodRefSignature =
     JMethodRefSignature {
         jMethodRefSignature_class      :: JClassName,
         jMethodRefSignature_name       :: JMethodName,
         jMethodRefSignature_descriptor :: JDescriptor
     }

java_lang_System_out :: JFieldRefSignature
java_lang_System_out =
  JFieldRefSignature {
     jFieldRefSignature_class = "java/lang/System",
     jFieldRefSignature_name = "out",
     jFieldRefSignature_type =
       JType_Reference "java/io/PrintStream"
  }

java_io_PrintStream_print :: JMethodRefSignature
java_io_PrintStream_print =
  JMethodRefSignature {
      jMethodRefSignature_class = "java/io/PrintStream",
      jMethodRefSignature_name  = "print",
      jMethodRefSignature_descriptor =
        JDescriptor [JType_Reference "java/lang/Object"] JType_Void 
  }

java_io_PrintStream_println :: JMethodRefSignature
java_io_PrintStream_println =
  JMethodRefSignature {
      jMethodRefSignature_class = "java/io/PrintStream",
      jMethodRefSignature_name  = "println",
      jMethodRefSignature_descriptor =
        JDescriptor [JType_Reference "java/lang/Object"] JType_Void 
  }

java_io_PrintStream_print_char :: JMethodRefSignature
java_io_PrintStream_print_char =
  JMethodRefSignature {
      jMethodRefSignature_class = "java/io/PrintStream",
      jMethodRefSignature_name  = "print",
      jMethodRefSignature_descriptor =
        JDescriptor [JType_Char] JType_Void 
  }

java_lang_System_exit :: JMethodRefSignature
java_lang_System_exit =
  JMethodRefSignature {
     jMethodRefSignature_class = "java/lang/System",
     jMethodRefSignature_name  = "exit",
     jMethodRefSignature_descriptor =
       JDescriptor [JType_Int] JType_Void 
  }

java_lang_Integer_valueOf :: JMethodRefSignature
java_lang_Integer_valueOf =
  JMethodRefSignature {
     jMethodRefSignature_class = "java/lang/Integer",
     jMethodRefSignature_name  = "valueOf",
     jMethodRefSignature_descriptor =
       JDescriptor [JType_Int] (JType_Reference "java/lang/Integer")
  }

java_lang_Integer_intValue :: JMethodRefSignature
java_lang_Integer_intValue =
  JMethodRefSignature {
     jMethodRefSignature_class = "java/lang/Integer",
     jMethodRefSignature_name  = "intValue",
     jMethodRefSignature_descriptor =
       JDescriptor [] JType_Int
  }

java_lang_Integer_equals :: JMethodRefSignature
java_lang_Integer_equals =
  JMethodRefSignature {
     jMethodRefSignature_class = "java/lang/Object",
     jMethodRefSignature_name  = "equals",
     jMethodRefSignature_descriptor =
       JDescriptor [JType_Reference "java/lang/Object"]
                   JType_Boolean
  }

data JFieldSignature =
     JFieldSignature {
         jFieldSignature_name       :: JMethodName,
         jFieldSignature_flags      :: [JAccessFlag],
         jFieldSignature_type       :: JType,
         jFieldSignature_attributes :: [JAttribute]
     }

data JFieldRefSignature =
     JFieldRefSignature {
         jFieldRefSignature_class :: JClassName,
         jFieldRefSignature_name  :: JMethodName,
         jFieldRefSignature_type  :: JType
     }

length' :: [a] -> Integer
length' = fromIntegral . length

base :: Integer -> Integer -> String
base b 0 = "0"
base b n = rec b n
  where
    alphabet :: String
    alphabet =
      "0123456789abcdefghijklmnopqrstuvwxyz"
    rec :: Integer -> Integer -> String
    rec b 0 = []
    rec b n = rec b (n `div` b) ++ [alphabet !! fromIntegral (n `mod` b)]

patchList :: Integer -> [a] -> (a -> a) -> [a]
patchList i xs f = let (ys, e : zs) = splitAt (fromIntegral i) xs in
                     ys ++ [f e] ++ zs

exprToJClasses :: JvmOptions -> [Pragma] -> JClassName -> ExprK ->
                  [(JClassName, JClass)]
exprToJClasses jvmOptions pragmas mainClassName expr =
    case runState (compile expr) initialState of
      (_, state) -> Map.toList (jvsClasses state)
  where
    initialState :: JvmState
    initialState =
      JvmState {
        jvsClasses = Map.fromList [
          (mainClassName,
           emptyClass (JClassSignature {
                          jClassSignature_name = mainClassName,
                          jClassSignature_flags = [JAccessFlag_Public],
                          jClassSignature_superclass = superclass
                      }))
        ],
        jvsLabelClassIndices = Map.empty,
        jvsLabelParameters = Map.empty,
        jvsCurrentClassName = "",
        jvsDefinedRegisters = Map.empty,
        jvsNextFreshLabel = 0,
        jvsStringCasts = Map.empty
      }

    superclass :: JClassName
    superclass = head $
                 concatMap pragmaJvmExtends pragmas ++ ["java/lang/Object"]
      where
        pragmaJvmExtends :: Pragma -> [String]
        pragmaJvmExtends (ForeignPragma ForeignLangJvm declaration) =
          case words declaration of
            ["extends", cls] -> [cls]
            _ -> []
        pragmaJvmExtends _ = []


    emptyClass :: JClassSignature -> JClass
    emptyClass signature =
      JClass {
          -- Note: we use major version <50 to avoid building
          -- a StackMapTable.
          jClass_majorVersion = 49,
          jClass_minorVersion = 0,
          jClass_constantPool = [
            -- 1
            JConstant_Class (JPoolEntry 2),
            -- 2
            JConstant_UTF8 (jClassSignature_name signature),
            -- 3
            JConstant_Class (JPoolEntry 4),
            -- 4
            JConstant_UTF8 (jClassSignature_superclass signature),
            -- 5
            JConstant_UTF8 "Code",
            -- 6
            JConstant_UTF8 "InnerClasses",
            -- 7
            JConstant_UTF8 "StackMapTable"
          ],
          jClass_accessFlags  = jClassSignature_flags signature,
          jClass_thisClass    = JPoolEntry 1,
          jClass_superClass   = JPoolEntry 3,
          jClass_fields       = [],
          jClass_methods      = [],
          jClass_attributes   = []
      }

    jAddEmptyClass :: JClassSignature -> JvmM ()
    jAddEmptyClass signature = do
      modify (\ state -> state {
        jvsClasses = Map.insert (jClassSignature_name signature)
                                (emptyClass signature)
                                (jvsClasses state)
      })
      -- Reference <init> method of the superclass 
      superclassInitEntry <- jAddMethodRef
          (jClassSignature_name signature)
          (JMethodRefSignature {
             jMethodRefSignature_class =
               jClassSignature_superclass signature,
             jMethodRefSignature_name  = "<init>",
             jMethodRefSignature_descriptor = JDescriptor [] JType_Void
          })
      -- Add <init> method for this class
      jAddMethod
          (JMethodSignature {
             jMethodSignature_classname  = jClassSignature_name signature,
             jMethodSignature_name       = "<init>",
             jMethodSignature_flags      = [],
             jMethodSignature_descriptor = JDescriptor [] JType_Void,
             jMethodSignature_codeAttrs  = [],
             jMethodSignature_code       = Just
                 [
                     JOp_Aload_0,
                     JOp_InvokeSpecial superclassInitEntry,
                     JOp_Return
                 ]
          })

    getClass :: JClassName -> JvmM JClass
    getClass clsname = do
      state <- get
      return $ Map.findWithDefault
                     (error
                       ("(exprToJClasses: clase no definida: " ++
                        clsname ++
                        ")"))
                     clsname
                     (jvsClasses state)

    modifyClass :: JClassName -> (JClass -> JClass) -> JvmM ()
    modifyClass clsname f = do
      cls <- getClass clsname
      modify (\ state -> state {
        jvsClasses = Map.insert clsname (f cls) (jvsClasses state)
      })

    jAddInnerClass :: JClassName -> JClassSignature -> JvmM JPoolEntry
    jAddInnerClass outerName signature = do
        cls <- getClass outerName
        i <- case findIndex isJAttribute_InnerClasses
                            (jClass_attributes cls) of
               Nothing -> do
                   innerclassesNameIdx <- jAddPoolEntry outerName
                                          (JConstant_UTF8 "InnerClasses")
                   modifyClass outerName (\ cls -> cls {
                       jClass_attributes =
                         jClass_attributes cls ++
                         [JAttribute_InnerClasses {
                            jAttribute_InnerClasses_name =
                              innerclassesNameIdx,
                            jAttribute_InnerClasses_innerClasses = []
                         }]
                   })
                   return $ length' (jClass_attributes cls)
               Just i  -> return (fromIntegral i)
        innerClsnameIdx <- jAddPoolEntry outerName
                               (JConstant_UTF8
                                 (jClassSignature_name signature))
        innerClsinfoIdx <- jAddPoolEntry outerName
                               (JConstant_Class innerClsnameIdx)
        jAddEmptyClass signature
        modifyClass outerName
          (\ cls -> cls {
            jClass_attributes =
              patchList i (jClass_attributes cls)
                (\ attr ->
                   attr {
                       jAttribute_InnerClasses_innerClasses =
                       jAttribute_InnerClasses_innerClasses attr ++ [
                         JInnerClass {
                           jInnerClass_innerClassInfo = innerClsinfoIdx,
                           jInnerClass_outerClassInfo = JPoolEntry 0,
                           jInnerClass_innerNameIndex = innerClsnameIdx,
                           jInnerClass_accessFlags    =
                             jClassSignature_flags signature
                         }
                       ]
                   })
          })
        return innerClsinfoIdx
      where
        isJAttribute_InnerClasses (JAttribute_InnerClasses _ _) = True
        isJAttribute_InnerClasses _ = False

    jAddPoolEntry :: JClassName -> JConstant -> JvmM JPoolEntry
    jAddPoolEntry clsname constant = do
        cls <- getClass clsname
        case findIndex (== constant) (jClass_constantPool cls) of
          Just i  -> return $ JPoolEntry (fromIntegral (i + 1))
          Nothing -> do
            modifyClass clsname
              (\ cls -> cls {
                jClass_constantPool = jClass_constantPool cls ++ [constant]
              })
            cls <- getClass clsname
            return $ JPoolEntry (length' (jClass_constantPool cls))

    jAddMethod :: JMethodSignature -> JvmM ()
    jAddMethod signature = do
        nameEntry <-
          jAddPoolEntry
            clsname
            (JConstant_UTF8 (jMethodSignature_name signature))
        descriptorEntry <-
          jAddPoolEntry
            clsname
            (JConstant_Descriptor (jMethodSignature_descriptor signature))
        modifyClass clsname
          (\ cls -> cls {
            jClass_methods = jClass_methods cls ++
                             [method nameEntry descriptorEntry]
          })
      where
        clsname :: JClassName
        clsname = jMethodSignature_classname signature
        method :: JPoolEntry -> JPoolEntry -> JMethod
        method nameEntry descriptorEntry = JMethod {
          jMethod_flags = jMethodSignature_flags signature,
          jMethod_name  = nameEntry,
          jMethod_descriptor = descriptorEntry,
          jMethod_attributes = codeAttributeFor
                                 (jMethodSignature_code signature)
        }
        codeAttributeFor :: Maybe [JOp] -> [JAttribute]
        codeAttributeFor Nothing     = []
        codeAttributeFor (Just code) = [
              JAttribute_Code {
                jAttribute_Code_name = JPoolEntry 5,
                jAttribute_Code_maxStack = 64,
                jAttribute_Code_maxLocals = 64,
                jAttribute_Code_code = code,
                jAttribute_Code_exceptions = [],
                jAttribute_Code_attributes =
                  jMethodSignature_codeAttrs signature
              }
          ]

    jAddMethodRef :: JClassName -> JMethodRefSignature -> JvmM JPoolEntry
    jAddMethodRef clsname signature = do
        classNameEntry <-
          jAddPoolEntry
            clsname
            (JConstant_UTF8 (jMethodRefSignature_class signature))
        classEntry <-
          jAddPoolEntry
            clsname
            (JConstant_Class classNameEntry)
        nameEntry <-
          jAddPoolEntry
            clsname
            (JConstant_UTF8 (jMethodRefSignature_name signature))
        descriptorEntry <-
          jAddPoolEntry
            clsname
            (JConstant_Descriptor (jMethodRefSignature_descriptor signature))
        nameAndTypeEntry <-
          jAddPoolEntry clsname (JConstant_NameAndType
                                   nameEntry
                                   descriptorEntry)
        methodRefEntry <-
          jAddPoolEntry clsname (JConstant_MethodRef
                                   classEntry
                                   nameAndTypeEntry)
        return methodRefEntry

    jAddField :: JClassName -> JFieldSignature -> JvmM ()
    jAddField clsname signature = do
      typeEntry <-
        jAddPoolEntry
          clsname
          (JConstant_Type (jFieldSignature_type signature))
      nameEntry <-
        jAddPoolEntry
          clsname
          (JConstant_UTF8 (jFieldSignature_name signature))
      modifyClass clsname (\ cls -> cls {
          jClass_fields =
            jClass_fields cls ++
              [JField {
                  jField_flags = jFieldSignature_flags signature,
                  jField_name  = nameEntry,
                  jField_type  = typeEntry,
                  jField_attributes = jFieldSignature_attributes signature
              }]
      })

    jAddFieldRef :: JClassName -> JFieldRefSignature -> JvmM JPoolEntry
    jAddFieldRef clsname signature = do
        classNameEntry <-
          jAddPoolEntry
            clsname
            (JConstant_UTF8 (jFieldRefSignature_class signature))
        classEntry <-
          jAddPoolEntry
            clsname
            (JConstant_Class classNameEntry)
        nameEntry <-
          jAddPoolEntry
            clsname
            (JConstant_UTF8 (jFieldRefSignature_name signature))
        typeEntry <-
          jAddPoolEntry
            clsname
            (JConstant_Type (jFieldRefSignature_type signature))
        nameAndTypeEntry <-
          jAddPoolEntry clsname (JConstant_NameAndType
                                   nameEntry
                                   typeEntry)
        fieldRefEntry <-
          jAddPoolEntry clsname (JConstant_FieldRef
                                   classEntry
                                   nameAndTypeEntry)
        return fieldRefEntry

    jFreshLabel :: JvmM JLabel
    jFreshLabel = do
      state <- get
      modify (\ state -> state {
        jvsNextFreshLabel = jvsNextFreshLabel state + 1
      })
      return $ "Label_" ++ show (jvsNextFreshLabel state)

    compile :: ExprK -> JvmM ()
    compile expr = do

      -- Abstract class for representing continuations

      cont_class_info_index <- jAddInnerClass mainClassName
        (JClassSignature {
            jClassSignature_name  = innerClassName mainClassName "Cont",
            jClassSignature_flags = [JAccessFlag_Static,
                                     JAccessFlag_Abstract],
            jClassSignature_superclass = "java/lang/Object"
        })

      jAddMethod
        (JMethodSignature {
            jMethodSignature_classname = innerClassName mainClassName "Cont",
            jMethodSignature_name = "cont",
            jMethodSignature_flags = [JAccessFlag_Abstract],
            jMethodSignature_descriptor =
                JDescriptor [] JType_Void,
            jMethodSignature_codeAttrs  = [],
            jMethodSignature_code = Nothing
        })

      -- Toplevel continuation

      c_Top_index <-
        jAddInnerClass mainClassName
          (JClassSignature {
              jClassSignature_name  = innerClassName mainClassName "Top",
              jClassSignature_flags = [JAccessFlag_Static],
              jClassSignature_superclass =
                innerClassName mainClassName "Cont"
          })
 
      modify (\ state -> state {
          -- Toplevel continuation
          jvsLabelClassIndices =
            Map.insert (-1) c_Top_index
                       (jvsLabelClassIndices state),
          jvsLabelParameters =
            Map.insert (-1) [0]
                       (jvsLabelParameters state)
      })

      m_PrintStream_println_topindex <-
        jAddMethodRef
          (innerClassName mainClassName "Top")
          java_io_PrintStream_println

      m_System_exit_topindex <-
        jAddMethodRef
          (innerClassName mainClassName "Top")
          java_lang_System_exit

      -- Add global field representing register 0

      field_reg0_topindex <- getRegisterFieldIndex
                               (innerClassName mainClassName "Top")
                               0

      field_java_lang_System_out_topindex <-
        jAddFieldRef
            (innerClassName mainClassName "Top")
            java_lang_System_out

      toplevelCode <-
        case jvoToplevel jvmOptions of
          JvmOpt_ToplevelShowAsString -> do
            -- Toplevel show the resulting string
            setCurrentClassName (innerClassName mainClassName "Top")
            (internalToJvmEntry, _) <- jStringCasts
            m_PrintStream_print_topindex <-
              jAddMethodRef
                (innerClassName mainClassName "Top")
                java_io_PrintStream_print
            return [
                  -- Cast reg0 to string and print
                  JOp_GetStatic field_java_lang_System_out_topindex,
                  JOp_GetStatic field_reg0_topindex,
                  JOp_InvokeStatic internalToJvmEntry,
                  JOp_InvokeVirtual m_PrintStream_print_topindex,
                  -- exit
                  JOp_Iconst_0,
                  JOp_InvokeStatic m_System_exit_topindex,
                  JOp_Return
              ]
          JvmOpt_ToplevelExit -> do
            -- Toplevel function exits
            return [
                  JOp_Iconst_0,
                  JOp_InvokeStatic m_System_exit_topindex,
                  JOp_Return
              ]

      jAddMethod
        (JMethodSignature {
            jMethodSignature_classname = innerClassName mainClassName "Top",
            jMethodSignature_name = "cont",
            jMethodSignature_flags = [],
            jMethodSignature_descriptor =
                JDescriptor [] JType_Void,
            jMethodSignature_codeAttrs  = [],
            jMethodSignature_code = Just toplevelCode
        })

      -- Main

      m_Cont_cont_index <-
        jAddMethodRef
          mainClassName
          (JMethodRefSignature {
              jMethodRefSignature_class =
                innerClassName mainClassName "Cont",
              jMethodRefSignature_name  = "cont",
              jMethodRefSignature_descriptor = JDescriptor [] JType_Void
          })

      m_Integer_valueOf_index <-
        jAddMethodRef mainClassName java_lang_Integer_valueOf

      setCurrentClassName (innerClassName mainClassName "Start")

      -- Start continuation
      c_Start_index <-
        jAddInnerClass mainClassName
          (JClassSignature {
              jClassSignature_name  = innerClassName mainClassName "Start",
              jClassSignature_flags = [JAccessFlag_Static],
              jClassSignature_superclass =
                innerClassName mainClassName "Cont"
          })
      mainCode <- visit expr
      jAddMethod
        (JMethodSignature {
            jMethodSignature_classname =
              innerClassName mainClassName "Start",
            jMethodSignature_name = "cont",
            jMethodSignature_flags = [],
            jMethodSignature_descriptor =
                 JDescriptor [] JType_Void,
            jMethodSignature_codeAttrs  = [],
            jMethodSignature_code = Just mainCode
        })
      m_Start_init_index <-
        jAddMethodRef
          mainClassName
          (JMethodRefSignature {
              jMethodRefSignature_class =
                innerClassName mainClassName "Start",
              jMethodRefSignature_name  = "<init>",
              jMethodRefSignature_descriptor = JDescriptor [] JType_Void
          })

      contClassIndex <- jAddClassRef mainClassName
                                     (innerClassName mainClassName "Cont")
      continuationRegIndex <- getRegisterFieldIndex mainClassName (-1)
      jAddMethod
        (JMethodSignature {
            jMethodSignature_classname = mainClassName,
            jMethodSignature_name = "main",
            jMethodSignature_flags = [JAccessFlag_Public,
                                      JAccessFlag_Static],
            jMethodSignature_descriptor =
                 JDescriptor
                   [JType_Array (JType_Reference "java/lang/String")]
                   JType_Void,
            jMethodSignature_codeAttrs  = [
                --
                -- XXX: When using major version >=50
                -- a StackMapTable attribute should be
                -- added. This does not seem to be working fine.
                -- We fallback to versions <50.
                --
                -- Alternatively, use version >=50 and
                -- "-XX:-UseSplitVerifier" flag on runtime.
                --
                ----JAttribute_StackMapTable {
                ----  jAttribute_StackMapTable_name = JPoolEntry 7,
                ----  jAttribute_StackMapTable_stackMapFrames = [
                ----    JStackMapFrame_Same 10
                ----  ]
                --}
            ],
            jMethodSignature_code = Just (
                 [
                   -- -- push new "Top" object and initialize it
                   JOp_New c_Start_index,
                   JOp_Dup,
                   JOp_InvokeSpecial m_Start_init_index,
                   JOp_PutStatic continuationRegIndex,

                   -- LOOP: invoke the continuation
                   JOp_Label "loop",
                   JOp_GetStatic continuationRegIndex,   -- 3 bytes
                   JOp_CheckCast contClassIndex,         -- 3 bytes
                   JOp_InvokeVirtual m_Cont_cont_index,  -- 3 bytes
                   JOp_Goto "loop",

                   JOp_Return
                 ]
            )
        })

    innerClassName :: JClassName -> String -> JClassName 
    innerClassName outerName innerName = outerName ++ "$" ++ innerName

    labelClassName :: IdK -> JClassName
    labelClassName (-1)  = innerClassName mainClassName "Top"
    labelClassName label = innerClassName mainClassName ("L" ++ mangle label)
      where
        -- Note: do not mix uppercase and lowercase, since
        -- classes result in filenames which might be case
        -- insensitive.
        mangle :: Integer -> String
        mangle = base 36

    jAddClassRef :: JClassName -> JClassName -> JvmM JPoolEntry
    jAddClassRef clsname referredClassName = do
      classNameEntry <-
        jAddPoolEntry
          clsname
          (JConstant_UTF8 referredClassName)
      jAddPoolEntry
        clsname
        (JConstant_Class classNameEntry)

    jStringCasts :: JvmM (JPoolEntry, JPoolEntry)
    jStringCasts = do
        currentClassName <- getCurrentClassName
        state <- get
        case Map.lookup currentClassName (jvsStringCasts state) of
          Nothing -> do
            entries <- jAddStringCasts
            modify (\ state -> state {
              jvsStringCasts =
                Map.insert currentClassName
                           entries
                           (jvsStringCasts state)
            })
            return entries
          Just entries  -> return entries
      where
        jAddStringCasts :: JvmM (JPoolEntry, JPoolEntry)
        jAddStringCasts = do
          currentClassName <- getCurrentClassName
          jAddStringCastInternalToJvm
          internalToJvmEntry <- jAddMethodRef
            currentClassName
            (JMethodRefSignature {
                jMethodRefSignature_class = currentClassName,
                jMethodRefSignature_name  = "string_ij",
                jMethodRefSignature_descriptor =
                    JDescriptor [JType_Reference "java/lang/Object"]
                                (JType_Reference "java/lang/String")
            })
          jAddStringCastJvmToInternal
          jvmToInternalEntry <- jAddMethodRef
            currentClassName
            (JMethodRefSignature {
                jMethodRefSignature_class = currentClassName,
                jMethodRefSignature_name  = "string_ji",
                jMethodRefSignature_descriptor =
                    JDescriptor [JType_Reference "java/lang/String"]
                                (JType_Reference "java/lang/Object")
            })
          return (internalToJvmEntry, jvmToInternalEntry)

        jAddStringCastInternalToJvm :: JvmM ()
        jAddStringCastInternalToJvm = do
          currentClassName <- getCurrentClassName
          objectArrayIndex <- jAddClassRef currentClassName
                                           "[Ljava/lang/Object;"
          stringBuilderIndex <- jAddClassRef currentClassName
                                             "java/lang/StringBuilder"
          stringBuilderInitIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/StringBuilder",
                  jMethodRefSignature_name  = "<init>",
                  jMethodRefSignature_descriptor = JDescriptor [] JType_Void
              })
          stringBuilderAppendCharIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/StringBuilder",
                  jMethodRefSignature_name  = "append",
                  jMethodRefSignature_descriptor =
                    JDescriptor [JType_Char]
                                (JType_Reference "java/lang/StringBuilder")
              })
          stringBuilderToStringIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/StringBuilder",
                  jMethodRefSignature_name  = "toString",
                  jMethodRefSignature_descriptor =
                    JDescriptor []
                                (JType_Reference "java/lang/String")
              })
          integerIndex <- jAddClassRef currentClassName
                                       "java/lang/Integer"
          intValueIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/Integer",
                  jMethodRefSignature_name  = "intValue",
                  jMethodRefSignature_descriptor =
                    JDescriptor []
                                (JType_Int)
              })
          jAddMethod
            (JMethodSignature {
                jMethodSignature_classname = currentClassName,
                jMethodSignature_name = "string_ij",
                jMethodSignature_flags = [JAccessFlag_Static],
                jMethodSignature_descriptor =
                    JDescriptor [JType_Reference "java/lang/Object"]
                                (JType_Reference "java/lang/String"),
                jMethodSignature_codeAttrs  = [],
                jMethodSignature_code = Just [
                    JOp_New stringBuilderIndex,
                    JOp_Dup,
                    JOp_InvokeSpecial stringBuilderInitIndex,
                    JOp_Astore_1,
                    JOp_Label "loop_start",
                    JOp_Aload_0,
                    JOp_InstanceOf objectArrayIndex,
                    JOp_IfEq "loop_end",
                    JOp_Aload_1,
                    JOp_Aload_0,
                    JOp_CheckCast objectArrayIndex,
                    JOp_Iconst_0,
                    JOp_Aaload,
                    JOp_CheckCast integerIndex,
                    JOp_InvokeVirtual intValueIndex,
                    JOp_I2C,
                    JOp_InvokeVirtual stringBuilderAppendCharIndex,
                    JOp_Pop,
                    JOp_Aload_0,
                    JOp_CheckCast objectArrayIndex,
                    JOp_Iconst_1,
                    JOp_Aaload,
                    JOp_Astore_0,
                    JOp_Goto "loop_start",
                    JOp_Label "loop_end",
                    JOp_Aload_1,
                    JOp_InvokeVirtual stringBuilderToStringIndex,
                    JOp_Areturn
                ]
            })

        jAddStringCastJvmToInternal :: JvmM ()
        jAddStringCastJvmToInternal = do
          currentClassName <- getCurrentClassName
          intValueOfIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/Integer",
                  jMethodRefSignature_name  = "valueOf",
                  jMethodRefSignature_descriptor =
                    JDescriptor [JType_Int]
                                (JType_Reference "java/lang/Integer")
              })
          stringLengthIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/String",
                  jMethodRefSignature_name  = "length",
                  jMethodRefSignature_descriptor =
                    JDescriptor [] JType_Int
              })
          charAtIndex <-
            jAddMethodRef
              currentClassName
              (JMethodRefSignature {
                  jMethodRefSignature_class = "java/lang/String",
                  jMethodRefSignature_name  = "charAt",
                  jMethodRefSignature_descriptor =
                    JDescriptor [JType_Int] JType_Char
              })
          objectIndex <- jAddClassRef currentClassName
                                      "java/lang/Object"
          jAddMethod
            (JMethodSignature {
                jMethodSignature_classname = currentClassName,
                jMethodSignature_name = "string_ji",
                jMethodSignature_flags = [JAccessFlag_Static],
                jMethodSignature_descriptor =
                    JDescriptor [JType_Reference "java/lang/String"]
                                (JType_Reference "java/lang/Object"),
                jMethodSignature_codeAttrs  = [],
                jMethodSignature_code =
                  Just $ [
                    JOp_Iconst_0,
                    JOp_InvokeStatic intValueOfIndex,
                    JOp_Astore_1,
                    JOp_Aload_0,
                    JOp_InvokeVirtual stringLengthIndex,
                    JOp_Iconst_1,
                    JOp_ISub,
                    JOp_Istore_2,
                    JOp_Label "loop_start",
                    JOp_Iload_2,
                    JOp_IfLt "loop_end",
                    JOp_Iconst_2,
                    JOp_Anewarray objectIndex,
                    JOp_Dup,
                    JOp_Iconst_0,
                    JOp_Aload_0,
                    JOp_Iload_2,
                    JOp_InvokeVirtual charAtIndex,
                    JOp_InvokeStatic intValueOfIndex,
                    JOp_Aastore,
                    JOp_Dup,
                    JOp_Iconst_1,
                    JOp_Aload_1,
                    JOp_Aastore,
                    JOp_Astore_1,
                    JOp_IInc 2 (-1),
                    JOp_Goto "loop_start",
                    JOp_Label "loop_end",
                    JOp_Aload_1,
                    JOp_Areturn
                ]
            })

    visit :: ExprK -> JvmM [JOp]

    visit (RecordK vals id expr) = do
        currentClassName <- getCurrentClassName
        objectClassIndex <- jAddClassRef currentClassName "java/lang/Object"
        pushLenVals <- jPushInteger (length' vals)
        regIndex <- getRegisterFieldIndex currentClassName id
        exprCode <- visit expr
        pushVals <- mapM visitV vals
        setContents <- zipWithM setValue [0..] pushVals 
        return $
            pushLenVals ++
            [JOp_Anewarray objectClassIndex] ++
            concat setContents ++
            [JOp_PutStatic regIndex] ++
            exprCode
      where
        setValue :: Integer -> [JOp] -> JvmM [JOp]
        setValue i pushValue = do
          pushI <- jPushInteger i
          return (
            [JOp_Dup] ++
            pushI ++
            pushValue ++
            [JOp_Aastore]
           )

    visit (SelectK i val id expr) = do
        currentClassName <- getCurrentClassName
        pushVal <- visitV val
        pushI <- jPushInteger i
        regIndex <- getRegisterFieldIndex currentClassName id
        exprCode <- visit expr
        objectArrayIndex <- jAddClassRef currentClassName
                                         "[Ljava/lang/Object;"
        return (
            pushVal ++ 
            [JOp_CheckCast objectArrayIndex] ++
            pushI ++
            [JOp_Aaload] ++
            [JOp_PutStatic regIndex] ++
            exprCode
          )

    visit (AppK val vals) = do
        pushVal  <- visitV val
        pushVals <- mapM visitV vals
        m_Cont_cont_index <-
          jAddMethodRef
            mainClassName
            (JMethodRefSignature {
                jMethodRefSignature_class =
                    innerClassName mainClassName "Cont",
                jMethodRefSignature_name  = "cont",
                jMethodRefSignature_descriptor = JDescriptor [] JType_Void
            })
        paramList <- getFunctionParamList val (length' pushVals)
        currentClassName <- getCurrentClassName
        setArguments <- mapM setRegister paramList
        continuationRegIndex <- getRegisterFieldIndex currentClassName (-1)
        return $
            pushVal ++
            [JOp_PutStatic continuationRegIndex] ++
            concat (reverse pushVals) ++
            concat setArguments ++
            [JOp_Return]
      where
        setRegister :: Integer -> JvmM [JOp]
        setRegister regNumber = do
            currentClassName <- getCurrentClassName
            regIndex <- getRegisterFieldIndex currentClassName regNumber
            return [JOp_PutStatic regIndex]
        getFunctionParamList :: ValueK -> Integer -> JvmM [IdK]
        getFunctionParamList (LabelK f) n = do
          state <- get
          case Map.lookup f (jvsLabelParameters state) of
            Just params -> return params
            Nothing     ->
              error ("(compileToJvm/getFunctionParamList: " ++
                     "etiqueta no definida)")
        getFunctionParamList _          n = return [0..n - 1]

    visit (LetK decls expr) = do
        mapM_ declareLabelClass decls
        mapM_ visitDecl decls

        setCurrentClassName (innerClassName mainClassName "Start")
        visit expr
      where
        declareLabelClass :: DeclarationK -> JvmM ()
        declareLabelClass (ValueDK f params _) = do
          classIndex <-
            jAddInnerClass mainClassName
              (JClassSignature {
                  jClassSignature_name  = labelClassName f,
                  jClassSignature_flags = [JAccessFlag_Static],
                  jClassSignature_superclass =
                      innerClassName mainClassName "Cont"
              })
          modify (\ state -> state {
            jvsLabelClassIndices =
              Map.insert f classIndex
                         (jvsLabelClassIndices state),
            jvsLabelParameters =
              Map.insert f params
                         (jvsLabelParameters state)
          })
        visitDecl :: DeclarationK -> JvmM ()
        visitDecl (ValueDK f _ body) = do
          setCurrentClassName (labelClassName f)
          bodyCode <- visit body
          return ()
          jAddMethod
            (JMethodSignature {
                jMethodSignature_classname = labelClassName f,
                jMethodSignature_name = "cont",
                jMethodSignature_flags = [],
                jMethodSignature_descriptor =
                    JDescriptor [] JType_Void,
                jMethodSignature_codeAttrs  = [],
                jMethodSignature_code = Just (
                  bodyCode
                )
            })

    visit (SwitchK val exprs) = do
        pushVal <- visitV val
        labels <- mapM (const jFreshLabel) exprs
        branches <- zipWithM visitBranch labels exprs

        currentClassName <- getCurrentClassName

        integerClassIndex <- jAddClassRef currentClassName
                                          "java/lang/Integer"
        methodIntegerIntValueIndex <-
          jAddMethodRef currentClassName java_lang_Integer_intValue

        return (
            pushVal ++
            -- Cast Integer back to int
            [JOp_CheckCast integerClassIndex] ++
            [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
            [JOp_TableSwitch labels] ++
            concat branches
          )
      where
        visitBranch :: JLabel -> ExprK -> JvmM [JOp]
        visitBranch label expr = do
          exprCode <- visit expr
          return (
              [JOp_Label label] ++
              exprCode
            )
    visit (PrimitiveK PrimRef [val] [id] [expr]) =
      visit (RecordK [val] id expr)
    visit (PrimitiveK PrimDeref [val] [id] [expr]) =
      visit (SelectK 0 val id expr)
    visit (PrimitiveK PrimAssign [vref, vval] result [expr]) = do
      currentClassName <- getCurrentClassName
      objectArrayIndex <- jAddClassRef currentClassName
                                       "[Ljava/lang/Object;"
      pushVref <- visitV vref
      pushVval <- visitV vval
      push0 <- jPushInteger 0
      bindResult <- unitEffectOrValue result
      exprCode <- visit expr
      return (
          pushVref ++
          [JOp_CheckCast objectArrayIndex] ++
          push0 ++
          pushVval ++
          [JOp_Aastore] ++
          bindResult ++
          exprCode
        )
    visit (PrimitiveK PrimFixnumAdd [val1, val2] [id] [expr]) =
      liftPrimitiveK_FixFix_Fix val1 val2 id expr [JOp_IAdd]
    visit (PrimitiveK PrimFixnumSub [val1, val2] [id] [expr]) = do
      liftPrimitiveK_FixFix_Fix val1 val2 id expr [JOp_ISub]
    visit (PrimitiveK PrimFixnumEq [val1, val2] [] [expr1, expr2]) = do
      liftPrimitiveK_FixFix_Branch2 val1 val2 expr1 expr2 JOp_IfCmpEq
    visit (PrimitiveK PrimFixnumLe [val1, val2] [] [expr1, expr2]) = do
      liftPrimitiveK_FixFix_Branch2 val1 val2 expr1 expr2 JOp_IfCmpLe
    visit (PrimitiveK PrimBoxed [val] [] [expr1, expr2]) = do
      currentClassName <- getCurrentClassName
      objectArrayIndex <- jAddClassRef currentClassName
                                      "[Ljava/lang/Object;"
      label <- jFreshLabel
      pushVal <- visitV val
      expr1Code <- visit expr1
      expr2Code <- visit expr2
      return (    
          pushVal ++
          [JOp_InstanceOf objectArrayIndex] ++
          [JOp_IfEq label] ++
          -- boxed
          expr1Code ++
          [JOp_Label label] ++
          -- unboxed
          expr2Code
        )
    visit (PrimitiveK PrimTag [val] [id] [expr]) = do
      currentClassName <- getCurrentClassName
      objectArrayIndex <- jAddClassRef currentClassName
                                      "[Ljava/lang/Object;"
      regIndex <- getRegisterFieldIndex currentClassName id
      label1 <- jFreshLabel
      label2 <- jFreshLabel
      push0 <- jPushInteger 0
      pushVal <- visitV val
      exprCode <- visit expr
      return (    
          pushVal ++
          [JOp_Dup] ++
          [JOp_InstanceOf objectArrayIndex] ++
          [JOp_IfEq label1] ++
          -- boxed
            [JOp_CheckCast objectArrayIndex] ++
            push0 ++
            [JOp_Aaload] ++
            [JOp_PutStatic regIndex] ++
          [JOp_Goto label2] ++
          [JOp_Label label1] ++
          -- unboxed
            [JOp_PutStatic regIndex] ++
          [JOp_Label label2] ++
          exprCode
        )
    visit (PrimitiveK PrimPutChar [val] result [expr]) = do
      currentClassName <- getCurrentClassName
      fieldSystemOut <- jAddFieldRef currentClassName java_lang_System_out
      pushVal <- visitV val
      integerClassIndex <- jAddClassRef currentClassName
                                        "java/lang/Integer"
      methodIntegerIntValueIndex <-
        jAddMethodRef currentClassName java_lang_Integer_intValue -- ()I
      methodPrintCharIndex <-
        jAddMethodRef currentClassName java_io_PrintStream_print_char
                                                                  -- (C)V
      exprCode <- visit expr
      bindResult <- unitEffectOrValue result
      return (
        [JOp_GetStatic fieldSystemOut] ++
        pushVal ++
        [JOp_CheckCast integerClassIndex] ++
        [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
        [JOp_InvokeVirtual methodPrintCharIndex] ++
        bindResult ++
        exprCode
       )
    visit (ForeignK (ForeignSignature ForeignLangJvm string argTypes retType)
                    args
                    id
                    expr) = do
        currentClassName <- getCurrentClassName
        pushArgs       <- zipWithM visitForeignArg argTypes args
        exprCode       <- visit expr
        (initializeCode, invokeCode)
                       <- invokeForeignDecl string
        castResultCode <- castJvmToInternal retType
        regIndex       <- getRegisterFieldIndex currentClassName id
        return (
            initializeCode ++
            concat pushArgs ++
            invokeCode ++
            castResultCode ++
            [JOp_PutStatic regIndex] ++
            exprCode
          )
      where
        visitForeignArg :: ForeignType -> ValueK -> JvmM [JOp]
        visitForeignArg ForeignUnit _ = return []
        visitForeignArg typ arg = do
          argCode <- visitV arg
          castCode <- castInternalToJvm typ
          return (
              argCode ++
              castCode
            )

        methodArgTypes :: [JType]
        methodArgTypes = map foreignTypeToJType argTypes

        methodRetType :: JType
        methodRetType = foreignTypeToJType retType

        foreignTypeToJType :: ForeignType -> JType
        foreignTypeToJType ForeignFixnum = JType_Int
        foreignTypeToJType ForeignChar   = JType_Char
        foreignTypeToJType ForeignString =
            JType_Reference "java/lang/String"
        foreignTypeToJType ForeignUnit   = JType_Void
        foreignTypeToJType ForeignBool = JType_Boolean
        foreignTypeToJType (ForeignPtr clsName) =
          JType_Reference clsName
        foreignTypeToJType _ =
          error "foreignTypeToJType: type not implemented"

        castInternalToJvm :: ForeignType -> JvmM [JOp]
        castInternalToJvm ForeignFixnum = do
           currentClassName <- getCurrentClassName
           integerClassIndex <- jAddClassRef currentClassName
                                        "java/lang/Integer"
           methodIntegerIntValueIndex <-
             jAddMethodRef currentClassName java_lang_Integer_intValue -- ()I
           return (
               [JOp_CheckCast integerClassIndex] ++
               [JOp_InvokeVirtual methodIntegerIntValueIndex]
             )
        castInternalToJvm ForeignChar = do
          castInternalToJvm ForeignFixnum
        castInternalToJvm ForeignString = do
          (internalToJvmEntry, _) <- jStringCasts
          return [JOp_InvokeStatic internalToJvmEntry]
        castInternalToJvm ForeignUnit =
          error "(compileToJvm: No se deberían visitar argumentos de tipo ())"
        castInternalToJvm ForeignBool = do
           currentClassName <- getCurrentClassName
           integerClassIndex <- jAddClassRef currentClassName
                                        "java/lang/Integer"
           methodIntegerValueOfIndex <-
             jAddMethodRef currentClassName java_lang_Integer_valueOf
                -- (I)Integer
           methodIntegerEqualsIndex <-
             jAddMethodRef currentClassName java_lang_Integer_equals
                -- (Integer,Integer)Z
           push0 <- jPushInteger 0
           methodIntegerValueOfIndex <-
             jAddMethodRef currentClassName java_lang_Integer_valueOf
           return (
               [JOp_CheckCast integerClassIndex] ++
               push0 ++
               [JOp_InvokeStatic methodIntegerValueOfIndex] ++
               [JOp_InvokeVirtual methodIntegerEqualsIndex]
             )
        castInternalToJvm (ForeignPtr clsName) = do
          currentClassName <- getCurrentClassName
          classIndex <- jAddClassRef currentClassName clsName
          return [JOp_CheckCast classIndex]
        castInternalToJvm _ =
          error "castInternalToJvm: Cast for type not implemented"

        castJvmToInternal :: ForeignType -> JvmM [JOp]
        castJvmToInternal ForeignFixnum = do
          currentClassName <- getCurrentClassName
          methodIntegerValueOfIndex <-
            jAddMethodRef currentClassName java_lang_Integer_valueOf
              -- (I)Integer
          return [JOp_InvokeStatic methodIntegerValueOfIndex]
        castJvmToInternal ForeignChar = do
          currentClassName <- getCurrentClassName
          methodIntegerValueOfIndex <-
            jAddMethodRef currentClassName java_lang_Integer_valueOf
              -- (C)Integer
          return [JOp_InvokeStatic methodIntegerValueOfIndex]
        castJvmToInternal ForeignBool = do
          currentClassName <- getCurrentClassName
          methodIntegerValueOfIndex <-
             jAddMethodRef currentClassName java_lang_Integer_valueOf
                -- (I)Integer
          labelTrue <- jFreshLabel
          labelEnd <- jFreshLabel
          push0 <- jPushInteger 0
          push1 <- jPushInteger 1
          return ([JOp_IfEq labelTrue] ++
                  push0 ++
                  [JOp_Goto labelEnd] ++
                  [JOp_Label labelTrue] ++
                  push1 ++
                  [JOp_Label labelEnd] ++
                  [JOp_InvokeStatic methodIntegerValueOfIndex])
        castJvmToInternal ForeignUnit = do
          currentClassName <- getCurrentClassName
          methodIntegerValueOfIndex <-
            jAddMethodRef currentClassName java_lang_Integer_valueOf
          push0 <- jPushInteger 0
          return $ push0 ++
                   [JOp_InvokeStatic methodIntegerValueOfIndex]
        castJvmToInternal ForeignString = do
          (_, jvmToInternalEntry) <- jStringCasts
          return [JOp_InvokeStatic jvmToInternalEntry]
        castJvmToInternal (ForeignPtr _) =
          return []

        isVoid :: JType -> Bool
        isVoid JType_Void = True
        isVoid _          = False

        staticMethodDescriptor :: JDescriptor
        staticMethodDescriptor =
          JDescriptor
            (filter (not . isVoid) methodArgTypes) methodRetType

        -- Do not include first argument
        virtualMethodClass :: String
        virtualMethodClass =
          case methodArgTypes of
            (JType_Reference cls : _) -> cls
            _ -> error (
                   "La declaración gringa del tipo de\n" ++
                   "    " ++ string ++ "\n" ++
                   "debe tomar como primer parámetro un Pendorcho.")

        virtualMethodDescriptor :: JDescriptor
        virtualMethodDescriptor =
          case methodArgTypes of
            (_ : args) ->
              JDescriptor (filter (not . isVoid) args) methodRetType
            _ -> error (
                   "La declaración gringa del tipo de\n" ++
                   "    " ++ string ++ "\n" ++
                   "debe tomar al menos un parámetro.")

        specialMethodClass :: String
        specialMethodClass =
          case methodRetType of
            (JType_Reference cls) -> cls
            _ -> error (
                   "La declaración gringa del tipo de\n" ++
                   "    " ++ string ++ "\n" ++
                   "debe devolver un Pendorcho.")

        specialMethodDescriptor :: JDescriptor
        specialMethodDescriptor =
          JDescriptor
            (filter (not . isVoid) methodArgTypes) JType_Void

        invokeForeignDecl :: String -> JvmM ([JOp], [JOp])
        invokeForeignDecl str =
          case words str of
            ["invokestatic", cls, meth] -> do
              currentClassName <- getCurrentClassName
              methSignature <-
                jAddMethodRef currentClassName
                     (JMethodRefSignature {
                          jMethodRefSignature_class = cls,
                          jMethodRefSignature_name  = meth,
                          jMethodRefSignature_descriptor =
                            staticMethodDescriptor
                       })
              return ([], [JOp_InvokeStatic methSignature])
            ["getstatic", cls, fieldName] | null methodArgTypes -> do
              currentClassName <- getCurrentClassName
              fieldIndex <-
                jAddFieldRef currentClassName
                  (JFieldRefSignature {
                      jFieldRefSignature_class = cls,
                      jFieldRefSignature_name = fieldName,
                      jFieldRefSignature_type = methodRetType
                  })
              return ([], [JOp_GetStatic fieldIndex])
            [meth] | meth /= "new" -> do
              currentClassName <- getCurrentClassName
              methSignature <-
                jAddMethodRef currentClassName
                     (JMethodRefSignature {
                          jMethodRefSignature_class =
                            virtualMethodClass,
                          jMethodRefSignature_name  = meth,
                          jMethodRefSignature_descriptor =
                            virtualMethodDescriptor
                       })
              return ([], [JOp_InvokeVirtual methSignature])
            ["new"] -> do
              currentClassName <- getCurrentClassName
              clsIndex <- jAddClassRef currentClassName specialMethodClass
              methSignature <-
                jAddMethodRef currentClassName
                     (JMethodRefSignature {
                          jMethodRefSignature_class =
                            specialMethodClass,
                          jMethodRefSignature_name  = "<init>",
                          jMethodRefSignature_descriptor =
                            specialMethodDescriptor
                       })
              return ([JOp_New clsIndex, JOp_Dup],
                      [JOp_InvokeSpecial methSignature])
            _ -> error $
             "Declaraciones gringas posibles para la JVM:\n" ++
             "  \"invokestatic <nombre_de_la_clase> <nombre_del_método>\"\n" ++
             "  \"getstatic <nombre_de_la_clase> <nombre_del_campo>\"\n" ++
             "  \"<nombre_del_método>\"\n" ++
             "  \"new\"\n"
    visit (ForeignK (ForeignSignature lang _ _ _) _ _ _) =
      error ("(compileToPy: lenguaje gringo no soportado: " ++
             show lang ++ ")")

    -- Binary fixnum operation
    liftPrimitiveK_FixFix_Fix :: ValueK -> ValueK -> IdK -> ExprK ->
                                 [JOp] -> JvmM [JOp]
    liftPrimitiveK_FixFix_Fix val1 val2 id expr code = do 
      currentClassName <- getCurrentClassName
      integerClassIndex <- jAddClassRef currentClassName
                                        "java/lang/Integer"
      methodIntegerIntValueIndex <-
        jAddMethodRef currentClassName java_lang_Integer_intValue -- ()I
      methodIntegerValueOfIndex <-
        jAddMethodRef currentClassName java_lang_Integer_valueOf -- (I)Integer
      regIndex <- getRegisterFieldIndex currentClassName id
      pushVal1 <- visitV val1
      pushVal2 <- visitV val2
      exprCode <- visit expr
      return (    
          pushVal1 ++
          [JOp_CheckCast integerClassIndex] ++
          [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
          pushVal2 ++
          [JOp_CheckCast integerClassIndex] ++
          [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
          code ++
          [JOp_InvokeStatic methodIntegerValueOfIndex] ++
          [JOp_PutStatic regIndex] ++
          exprCode
        )

    -- Binary fixnum comparison operation
    liftPrimitiveK_FixFix_Branch2 :: ValueK -> ValueK -> ExprK -> ExprK ->
                                     (JLabel -> JOp) -> JvmM [JOp]
    liftPrimitiveK_FixFix_Branch2 val1 val2 expr1 expr2 ifcmpop = do
      currentClassName <- getCurrentClassName
      integerClassIndex <- jAddClassRef currentClassName
                                        "java/lang/Integer"
      methodIntegerIntValueIndex <-
        jAddMethodRef currentClassName java_lang_Integer_intValue -- ()I
      pushVal1 <- visitV val1
      pushVal2 <- visitV val2
      label <- jFreshLabel
      expr1Code <- visit expr1
      expr2Code <- visit expr2
      return (    
          pushVal1 ++
          [JOp_CheckCast integerClassIndex] ++
          [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
          pushVal2 ++
          [JOp_CheckCast integerClassIndex] ++
          [JOp_InvokeVirtual methodIntegerIntValueIndex] ++
          [ifcmpop label] ++
          expr2Code ++
          [JOp_Label label] ++
          expr1Code
        )

    unitEffectOrValue :: [IdK] -> JvmM [JOp]
    unitEffectOrValue [] = return [] -- for effect
    unitEffectOrValue [id] = do
      currentClassName <- getCurrentClassName
      regIndex <- getRegisterFieldIndex currentClassName id
      push0 <- visitV (ConstantK (FixnumC 0))
      -- for value
      return (
          push0 ++
          [JOp_PutStatic regIndex]
        )

    visitV :: ValueK -> JvmM [JOp]
    visitV (LabelK label) = do
      currentClassName <- getCurrentClassName
      labelClassIndex <- jAddClassRef currentClassName
                                      (labelClassName label)
      initMethodIndex <-
        jAddMethodRef
          currentClassName
          (JMethodRefSignature {
              jMethodRefSignature_class = labelClassName label,
              jMethodRefSignature_name  = "<init>",
              jMethodRefSignature_descriptor = JDescriptor [] JType_Void
          })
      return [
         JOp_New labelClassIndex,
         JOp_Dup,
         JOp_InvokeSpecial initMethodIndex
       ]
    visitV (VarK id) = do
      currentClassName <- getCurrentClassName
      regIndex <- getRegisterFieldIndex currentClassName id
      return [
        JOp_GetStatic regIndex
       ]
    visitV (ConstantK (FixnumC n)) = do
      currentClassName <- getCurrentClassName
      methodIntegerValueOfIndex <-
        jAddMethodRef currentClassName java_lang_Integer_valueOf
      pushN <- jPushInteger n
      return $ 
          pushN ++
          [JOp_InvokeStatic methodIntegerValueOfIndex]
    visitV (ConstantK (CharC c)) =
      visitV (ConstantK (FixnumC (fromIntegral (ord c))))
    visitV (SelK i id) = do
      currentClassName <- getCurrentClassName
      pushI <- jPushInteger i
      regIndex <- getRegisterFieldIndex currentClassName id
      objectArrayIndex <- jAddClassRef currentClassName
                                       "[Ljava/lang/Object;"
      return (
          [JOp_GetStatic regIndex] ++
          [JOp_CheckCast objectArrayIndex] ++
          pushI ++
          [JOp_Aaload]
        )

    jPushInteger :: Integer -> JvmM [JOp]
    jPushInteger 0 = return [JOp_Iconst_0]
    jPushInteger 1 = return [JOp_Iconst_1]
    jPushInteger 2 = return [JOp_Iconst_2]
    jPushInteger 3 = return [JOp_Iconst_3]
    jPushInteger 4 = return [JOp_Iconst_4]
    jPushInteger 5 = return [JOp_Iconst_5]
    jPushInteger n
      | 0 <= n && n < 2^7  = return [JOp_Bipush n]
      | 0 <= n && n < 2^15 = return [JOp_Sipush n]
      | 0 <= n && n < 2^31 = do
        currentClassName <- getCurrentClassName
        entry <- jAddPoolEntry currentClassName (JConstant_Integer n)
        return [JOp_Ldc entry]
      -- TODO: >31 bits (?)

    getCurrentClassName :: JvmM JClassName
    getCurrentClassName = do
      state <- get
      return $ jvsCurrentClassName state

    setCurrentClassName :: JClassName -> JvmM ()
    setCurrentClassName clsname = do
      modify (\ state -> state {
          jvsCurrentClassName = clsname
      })

    getRegisterFieldIndex :: JClassName -> Integer -> JvmM JPoolEntry
    getRegisterFieldIndex clsname registerNumber = do
      state <- get
      case Map.lookup registerNumber (jvsDefinedRegisters state) of
        Just _  -> return () -- already defined
        Nothing -> do
          jAddField mainClassName
              (JFieldSignature {
                  jFieldSignature_name  = registerName,
                  jFieldSignature_flags = [JAccessFlag_Static],
                  jFieldSignature_type  = JType_Reference
                                            "java/lang/Object",
                  jFieldSignature_attributes = []
              })
          modify (\ state -> state {
              jvsDefinedRegisters =
                Map.insert registerNumber () (jvsDefinedRegisters state)
          })
      jAddFieldRef
          clsname
          (JFieldRefSignature {
              jFieldRefSignature_class = mainClassName,
              jFieldRefSignature_name = registerName,
              jFieldRefSignature_type =
                JType_Reference "java/lang/Object"
          })
      where
        registerName :: String
        registerName = if registerNumber == -1
                        then "continuation"
                        else "reg" ++ show registerNumber

compileToJvm :: JvmOptions -> [Pragma] -> String -> ExprK -> String
compileToJvm jvmOptions pragmas mainClassName expr =
    dump . bytecode $ JJar {
      jJar_mainClass = mainClassName,
      jJar_classes = exprToJClasses jvmOptions pragmas mainClassName expr
    }
  where
    dump :: [Integer] -> String
    dump = map (chr . fromIntegral)

