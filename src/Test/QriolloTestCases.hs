
module Test.QriolloTestCases(stringProgramTestCases, prelude) where

prelude :: String
prelude =
    " chirimbolo diestro 10 : " ++
    " chirimbolo zurdo   30 ++ " ++
    " chirimbolo zurdo   90 := " ++
    " " ++
    " una Lista de coso es " ++
    "   bien Vacía " ++
    "   bien : coso [coso] " ++
    " " ++
    " el ++ de [coso] en [coso] en [coso] " ++
    "   dada []       ys da ys " ++
    "   dada (x : xs) ys da x : (xs ++ ys) " ++
    " el := es PRIM.asignar "

-- All programs must return strings, i.e. lists of chars
stringProgramTestCases :: [(String, String)]
stringProgramTestCases = [

   (" el programa es ['a'] ", "a"),

   (
    " cualidad Mostrable para coso " ++
    "   el mostrar de coso en [Letra] " ++
    " boludo " ++
    "" ++
    " encarnar Mostrable para Letra " ++
    "   el mostrar dado x da x : Vacía " ++
    " boludo " ++
    "" ++
    " el programa es mostrar 'a' ",
    "a"
   ),

   (
    " cualidad Mostrable para coso " ++
    "   el mostrar de coso en [Letra] " ++
    " boludo " ++
    "" ++
    " encarnar Mostrable para Letra " ++
    "   el mostrar dado x da [x] " ++
    " boludo " ++
    "" ++
    " una Cadena tiene " ++
    "   las letras de [Letra] " ++
    " boludo " ++
    "" ++
    " encarnar Mostrable para Cadena " ++
    "   el mostrar es letras " ++
    " boludo " ++
    "" ++
    " el programa es mostrar (Cadena cuyas letras son ['a', 'b', 'c']) ",
    "abc"
   ),

   -- Test constructor representation: constants
   (
    " una Empanada es " ++
    "   bien Carne " ++
    "   bien Pollo " ++
    "   bien Caprese " ++
    "   bien Humita " ++
    "   bien Verdura " ++
    " " ++
    " el nombre de Empanada en [Letra] " ++
    "  dada Carne   da ['C','a','r','n', 'e'] " ++
    "  dada Pollo   da ['P','o','l','l', 'o'] " ++
    "  dada Caprese da ['C','a','p','r','e','s','e'] " ++
    "  dada Humita  da ['H','u','m','i','t','a'] " ++
    "  dada Verdura da ['V','e','r','d','u','r','a'] " ++
    " " ++
    " el juntar de [[Letra]] en [Letra] en [Letra] " ++
    "   dada []     _   da [] " ++
    "   dada [x]    _   da x  " ++
    "   dada (x:xs) sep da x ++ sep ++ juntar xs sep " ++
    " " ++
    " el aplicarf de (coso en cosito) en [coso] en [cosito] " ++
    " dadas f []       da [] " ++
    " dadas f (x : xs) da f x : aplicarf f xs " ++
    " " ++
    " el programa es " ++
    "   juntar " ++
    "     (aplicarf nombre [Verdura, Humita, Caprese, Pollo, Carne]) " ++
    "     [',', ' '] ",
    "Verdura, Humita, Caprese, Pollo, Carne"
   ),

   -- Test constructor representation: safe untagged
   (
    " chirimbolo zurdo   45 . " ++
    " chirimbolo zurdo   45 < " ++
    " chirimbolo zurdo   55 - " ++
    " chirimbolo zurdo   55 + " ++
    " chirimbolo zurdo   65 * " ++
    " chirimbolo zurdo   75 / " ++
    " chirimbolo zurdo   75 % " ++
    " chirimbolo diestro 85 ^ " ++
    " " ++
    " el . de (meng en zut) en (ful en meng) en ful en zut " ++
    "   dadas f g x da f (g x) " ++
    " " ++
    " una Posta es " ++
    "   bien No " ++
    "   bien Sí " ++
    " " ++
    " un Nat es " ++
    "   bien O " ++
    "   bien S Nat " ++
    " " ++
    " el predecesor de Nat en Nat " ++
    "   dado (S n) da n " ++
    "   dado z     da z " ++
    " " ++
    " el + de Nat en Nat en Nat " ++
    "  dados O y da y " ++
    "  dados x y da S (predecesor x + y) " ++
    " " ++
    " el - de Nat en Nat en Nat " ++
    "  dados (S x) O     da S x " ++
    "  dados (S x) (S y) da x - y " ++
    "  dados O _         da O " ++
    " " ++
    " el < de Nat en Nat en Posta " ++
    "  dados O     O     da No " ++
    "  dados O     _     da Sí " ++
    "  dados (S x) O     da No " ++
    "  dados (S x) (S y) da x < y " ++
    " " ++
    " el * de Nat en Nat en Nat " ++
    "  dados O     _   da O " ++
    "  dados (S x) y   da y + x * y " ++
    " " ++
    " el cociente_y_resto de Nat en Nat en (Nat, Nat) " ++
    "  dados n m da " ++
    "    mirar n < m " ++
    "      si Sí da (O, n) " ++
    "      si No da " ++
    "         mirar cociente_y_resto (n - m) m " ++
    "           si (q, r) da (S q, r)" ++
    "         boludo " ++
    "    boludo " ++
    " " ++
    " el pri de (coso, cosito) en coso " ++
    "   dado (x, _) da x " ++
    " " ++
    " el segu de (coso, cosito) en cosito " ++
    "   dado (_, x) da x " ++
    " " ++
    " el / de Nat en Nat en Nat " ++
    "  dados n m da pri (cociente_y_resto n m) " ++
    " " ++
    " el % de Nat en Nat en Nat " ++
    "  dados n m da segu (cociente_y_resto n m) " ++
    " " ++
    " el ^ de Nat en Nat en Nat " ++
    "  dados b O     da S O " ++
    "  dados b (S n) da b * b ^ n " ++
    " " ++
    " el s1  es S " ++
    " el s2  es s1 . s1 " ++
    " el s4  es s2 . s2 " ++
    " el s8  es s4 . s4 " ++
    " " ++
    " los dígitos de [Letra] es " ++
    "     ['0','1','2','3','4','5','6','7','8','9'] " ++
    " " ++
    " el espichar de () en coso " ++
    "   dado () da espichar () " ++
    " " ++
    " el letra_a_dígito de Letra en Nat " ++
    "   dado '0' da O " ++
    "   dado '1' da s1 O " ++
    "   dado '2' da s2 O " ++
    "   dado '3' da (s2 . s1) O " ++
    "   dado '4' da s4 O " ++
    "   dado '5' da (s4 . s1) O " ++
    "   dado '6' da (s4 . s2) O " ++
    "   dado '7' da (s4 . s2 . s1) O " ++
    "   dado '8' da s8 O " ++
    "   dado '9' da (s8 . s1) O " ++
    "   dado _   da O " ++
    " " ++
    " el iésimo de [coso] en Nat en coso " ++
    "   dado []     _     da espichar () " ++
    "   dado (x:_)  O     da x " ++
    "   dado (_:xs) (S i) da iésimo xs i " ++
    " " ++
    " el dígito_a_letra de Nat en Letra " ++
    "    es iésimo dígitos " ++
    " " ++
    " el invertir de [coso] en [coso] " ++
    "   dada []     da [] " ++
    "   dada (y:ys) da invertir ys ++ [y] " ++
    " " ++
    " el diego es (s8 . s2) O " ++
    " " ++
    " el cadena_a_nat de [Letra] en Nat " ++
    "   dado ds da leer (invertir ds) " ++
    " donde " ++
    "   el leer " ++
    "     dado []     da O " ++
    "     dado (d:ds) da diego * leer ds + letra_a_dígito d " ++
    " boludo " ++
    " " ++
    " el nat_a_cadena de Nat en [Letra] " ++
    "   dado O da ['0'] " ++
    "   dado n da mostrar n " ++
    "   donde el mostrar  " ++
    "     dado O da [] " ++
    "     dado n da mostrar (n / diego) ++ [dígito_a_letra (n % diego)] " ++
    "   boludo " ++
    " " ++
    " el mostrar_nat de Nat en [Letra] " ++
    "   dado O     da ['O'] " ++
    "   dado (S x) da 'S' : mostrar_nat x " ++
    " " ++
    " el programa es " ++
    "   nat_a_cadena (" ++
    "     (cadena_a_nat ['9','9'] + cadena_a_nat ['1']) + " ++
    "     cadena_a_nat ['2'] ^ cadena_a_nat ['3'] " ++
    "   ) ",
    "108"
   ),

   -- Test constructor representation: tagged
   (
    " un T es bien A Letra " ++
    "         bien B T Letra T " ++
    " " ++
    " el preorder de T en [Letra] " ++
    "   dado (A x)       da [x] " ++
    "   dado (B t1 x t2) da [x] ++ preorder t1 ++ preorder t2 " ++
    " " ++
    " el inorder de T en [Letra] " ++
    "   dado (A x)       da [x] " ++
    "   dado (B t1 x t2) da inorder t1 ++ [x] ++ inorder t2 " ++
    " " ++
    " el postorder de T en [Letra] " ++
    "   dado (A x)       da [x] " ++
    "   dado (B t1 x t2) da postorder t1 ++ postorder t2 ++ [x] " ++
    " " ++
    " el programa es " ++
    "    preorder árbol ++ ['.'] ++ " ++
    "    inorder árbol ++ ['.'] ++ " ++
    "    postorder árbol ++ ['.'] " ++
    " donde el árbol es (B (B (A 'a') 'b' (A 'c')) " ++
    "                      'd' " ++
    "                      (B (A 'e') 'f' (A 'g'))) boludo ",
    "dbacfeg.abcdefg.acbegfd."),

   -- Test constructor representation: transparent
   (
    " un T1 es bien T1 Letra " ++
    " un T2 es bien T2 T1 " ++
    " un T3 es bien T3 T2 " ++
    " un T4 es bien T4 T3 " ++
    " " ++
    " la f dado (T2 (T1 x)) da ['(',x,')'] " ++
    " la g dado (T4 (T3 x)) da x " ++
    " el programa es " ++
    "    f (g (T4 (T3 (T2 (T1 'z')))))",
    "(z)"),

   -- Test constructor representation: untagged
   (
    " un Chabón tiene " ++
    "   el nombre   de Letra " ++
    "   el apellido de Letra " ++
    " boludo " ++
    " " ++
    " el mostrar " ++
    "    dado (Chabón cuyo nombre es n " ++
    "                 cuyo apellido es a) " ++
    "    da   ['n',':',n,',','a',':',a]" ++
    " el programa es mostrar (Chabón cuyo nombre es 'J' " ++
    "                                cuyo apellido es 'P') ",
    "n:J,a:P"),

   -- Test references and closures
   (
    " un Nat es " ++
    "   bien O " ++
    "   bien S Nat " ++
    " " ++
    " el mostrar " ++
    "   dado O da ['O'] " ++
    "   dado (S n) da 'S' : mostrar n " ++
    " " ++
    " el crear_contador de () en (() en Nat) " ++
    " dado () da ponele que " ++
    "      el contador de Ref de Nat es Ref O " ++
    "      el siguiente de () en Nat dado () da " ++
    "         ponele que " ++
    "           el valor es PRIM.desref contador " ++
    "           el _     es contador := S (PRIM.desref contador) " ++
    "         en valor " ++
    "    en siguiente " ++
    " el programa es " ++
    "    mostrar (c1 ()) ++ [','] ++ " ++
    "    mostrar (c1 ()) ++ [','] ++ " ++
    "    mostrar (c1 ()) ++ [','] ++ " ++
    "    mostrar (c1 ()) ++ [','] ++ " ++
    "    mostrar (c2 ()) ++ [','] ++ " ++
    "    mostrar (c2 ()) ++ [','] ++ " ++
    "    mostrar (c2 ()) ++ [','] ++ " ++
    "    mostrar (c1 ()) " ++
    " donde " ++
    "   el c1 es crear_contador() " ++
    "   el c2 es crear_contador() " ++
    " boludo ",
    "O,SO,SSO,SSSO,O,SO,SSO,SSSSO"),

   -- Pattern matching of references 
   (
    " un Nat es " ++
    "    bien O " ++
    "    bien S Nat " ++
    " la f " ++
    "    dado (Ref O)         da ['a'] " ++
    "    dado (Ref (S O))     da ['b'] " ++
    "    dado (Ref (S (S O))) da ['c'] " ++
    "    dado _               da ['d'] " ++
    " el programa es f (Ref (S (S O)))",
    "c"
   ),

   -- Pattern matching of references 
   (
    " un Nat es " ++
    "    bien O " ++
    "    bien S Nat " ++
    " la f " ++
    "    dado (Ref O)         da ['a'] " ++
    "    dado (Ref (S O))     da ['b'] " ++
    "    dado (Ref (S (S O))) da ['c'] " ++
    "    dado _               da ['d'] " ++
    " el programa es f (Ref (S (S (S O))))",
    "d"
   ),

   -- Test binary search
   (
    " la f de Numerito en [Letra] " ++
    " dado 0# da ['0'] " ++
    " dado 1# da ['1'] " ++
    " dado 4# da ['4'] " ++
    " dado 9# da ['9'] " ++
    " dado 16# da ['1','6'] " ++
    " dado 25# da ['2','5'] " ++
    " dado 36# da ['3','6'] " ++
    " dado 49# da ['4','9'] " ++
    " dado 64# da ['6','4'] " ++
    " dado 81# da ['8','1'] " ++
    " dado 100# da ['1','0','0'] " ++
    " dado 121# da ['1','2','1'] " ++
    " dado 144# da ['1','4','4'] " ++
    " dado 169# da ['1','6','9'] " ++
    " dado 196# da ['1','9','6'] " ++
    " dado 225# da ['2','2','5'] " ++
    " dado 256# da ['2','5','6'] " ++
    " dado 289# da ['2','8','9'] " ++
    " dado 324# da ['3','2','4'] " ++
    " dado 361# da ['3','6','1'] " ++
    " dado 400# da ['4','0','0'] " ++
    " dado 441# da ['4','4','1'] " ++
    " dado 484# da ['4','8','4'] " ++
    " dado 529# da ['5','2','9'] " ++
    " dado 576# da ['5','7','6'] " ++
    " dado 625# da ['6','2','5'] " ++
    " dado 676# da ['6','7','6'] " ++
    " dado 729# da ['7','2','9'] " ++
    " dado 784# da ['7','8','4'] " ++
    " dado 841# da ['8','4','1'] " ++
    " dado 900# da ['9','0','0'] " ++
    " dado 961# da ['9','6','1'] " ++
    " dado 1024# da ['1','0','2','4'] " ++
    " dado 1089# da ['1','0','8','9'] " ++
    " dado 1156# da ['1','1','5','6'] " ++
    " dado 1225# da ['1','2','2','5'] " ++
    " dado 1296# da ['1','2','9','6'] " ++
    " dado 1369# da ['1','3','6','9'] " ++
    " dado 1444# da ['1','4','4','4'] " ++
    " dado 1521# da ['1','5','2','1'] " ++
    " dado 1600# da ['1','6','0','0'] " ++
    " dado 1681# da ['1','6','8','1'] " ++
    " dado 1764# da ['1','7','6','4'] " ++
    " dado 1849# da ['1','8','4','9'] " ++
    " dado 1936# da ['1','9','3','6'] " ++
    " dado 2025# da ['2','0','2','5'] " ++
    " dado 2116# da ['2','1','1','6'] " ++
    " dado 2209# da ['2','2','0','9'] " ++
    " dado 2304# da ['2','3','0','4'] " ++
    " dado 2401# da ['2','4','0','1'] " ++
    " dado 2500# da ['2','5','0','0'] " ++
    " dado 2601# da ['2','6','0','1'] " ++
    " dado 2704# da ['2','7','0','4'] " ++
    " dado 2809# da ['2','8','0','9'] " ++
    " dado 2916# da ['2','9','1','6'] " ++
    " dado 3025# da ['3','0','2','5'] " ++
    " dado 3136# da ['3','1','3','6'] " ++
    " dado 3249# da ['3','2','4','9'] " ++
    " dado 3364# da ['3','3','6','4'] " ++
    " dado 3481# da ['3','4','8','1'] " ++
    " dado 3600# da ['3','6','0','0'] " ++
    " dado 3721# da ['3','7','2','1'] " ++
    " dado 3844# da ['3','8','4','4'] " ++
    " dado 3969# da ['3','9','6','9'] " ++
    " dado 4096# da ['4','0','9','6'] " ++
    " dado 4225# da ['4','2','2','5'] " ++
    " dado 4356# da ['4','3','5','6'] " ++
    " dado 4489# da ['4','4','8','9'] " ++
    " dado 4624# da ['4','6','2','4'] " ++
    " dado 4761# da ['4','7','6','1'] " ++
    " dado 4900# da ['4','9','0','0'] " ++
    " dado 5041# da ['5','0','4','1'] " ++
    " dado 5184# da ['5','1','8','4'] " ++
    " dado 5329# da ['5','3','2','9'] " ++
    " dado 5476# da ['5','4','7','6'] " ++
    " dado 5625# da ['5','6','2','5'] " ++
    " dado 5776# da ['5','7','7','6'] " ++
    " dado 5929# da ['5','9','2','9'] " ++
    " dado 6084# da ['6','0','8','4'] " ++
    " dado 6241# da ['6','2','4','1'] " ++
    " dado 6400# da ['6','4','0','0'] " ++
    " dado 6561# da ['6','5','6','1'] " ++
    " dado 6724# da ['6','7','2','4'] " ++
    " dado 6889# da ['6','8','8','9'] " ++
    " dado 7056# da ['7','0','5','6'] " ++
    " dado 7225# da ['7','2','2','5'] " ++
    " dado 7396# da ['7','3','9','6'] " ++
    " dado 7569# da ['7','5','6','9'] " ++
    " dado 7744# da ['7','7','4','4'] " ++
    " dado 7921# da ['7','9','2','1'] " ++
    " dado 8100# da ['8','1','0','0'] " ++
    " dado 8281# da ['8','2','8','1'] " ++
    " dado 8464# da ['8','4','6','4'] " ++
    " dado 8649# da ['8','6','4','9'] " ++
    " dado 8836# da ['8','8','3','6'] " ++
    " dado 9025# da ['9','0','2','5'] " ++
    " dado 9216# da ['9','2','1','6'] " ++
    " dado 9409# da ['9','4','0','9'] " ++
    " dado 9604# da ['9','6','0','4'] " ++
    " dado 9801# da ['9','8','0','1'] " ++
    " dado _     da ['z'] " ++
    " el programa es " ++
    "   rec [0#,1#,2#,3#,4#,5#,6#,7#,8#,9#,10#,11#,12#,13#,14#,15#," ++
    "    16#,17#,18#,19#,20#,21#,22#,23#,24#,25#,26#,27#,28#,29#,30#," ++
    "    31#,32#,33#,34#,35#,36#,37#,38#,39#,40#,41#,42#,43#,44#,45#," ++
    "    46#,47#,48#,49#,50#,51#,52#,53#,54#,55#,56#,57#,58#,59#,60#," ++
    "    61#,62#,63#,64#,65#,66#,67#,68#,69#,70#,71#,72#,73#,74#,75#," ++
    "    76#,77#,78#,79#,80#,81#,82#,83#,84#,85#,86#,87#,88#,89#,90#," ++
    "    91#,92#,93#,94#,95#,96#,97#,98#,99#] " ++
    " donde el rec " ++
    " dado []     da [] " ++
    " dado (x:xs) da f x ++ rec xs " ++
    " boludo ",
    "01zz4zzzz9zzzzzz16zzzzzzzz25zzzzzzzzzz36zzzzzzzzzzzz49" ++
    "zzzzzzzzzzzzzz64zzzzzzzzzzzzzzzz81zzzzzzzzzzzzzzzzzz"
   ),

   -- Test definition of mutually recursive values
   (
    " la g es f " ++
    " donde " ++
    "   la x es f 'a' " ++
    "   la f " ++
    "      dado 'a' da 'z' " ++
    "      dado _   da x  " ++
    " boludo " ++
    " el programa es g 'b' : [] ",
    "z"
   ),

   -- Mutually recursive values: even / odd
   (
    " un Nat es " ++
    "    bien O " ++
    "    bien S Nat " ++
    " el primero de (coso, cosito) en coso " ++
    "    dado (x, _) da x " ++
    " la p de Nat en Letra es primero par " ++
    " donde " ++
    "   el par de (Nat en Letra, Numerito) es (" ++
    "     la que dado O     da 's' " ++
    "            dado (S n) da primero impar n, " ++
    "     3# " ++
    "   ) " ++
    "   el impar de (Nat en Letra, Numerito) es (" ++
    "      la que dado O     da 'n' " ++
    "             dado (S n) da primero par n, " ++
    "      7# " ++
    "   ) " ++
    " boludo " ++
    " el programa es p (S (S (S (S (S O))))) : [] ",
    "n"
   ),

   -- Mutually recursive values with effects
   (
    " chirimbolo diestro 20 /// " ++
    " el /// de () en a en a " ++
    "   dados _ y da y " ++
    " el programa es " ++
    "   PRIM.desref r " ++
    " donde " ++
    "   la r es Ref \"start\" " ++
    "   la a es r := \"bad\" /// b " ++
    "   la b es r := \"good\" /// 1# " ++
    " boludo ",
    "good"
   ),

   -- sentinel
   (" el programa es Vacía ", "")
 ]

