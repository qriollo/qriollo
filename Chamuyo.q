entregar
  (
    :=,
    desref,
    ccc,
    invocar,
    $,
    ;,
    ||, &&, xor, negar,
    todos, no_todos, alguno, ninguno,
    todo_el_mundo, no_todo_el_mundo, alguien, nadie,
    Igualable,
      ==,
    !=, <=, <, >=, >,
    :,
    <<, >>,
    .,
    ->,
    ..,
    ...,
    pi1, pi2,
    letra_a_numerito,
    numerito_a_letra,
    espichar,
    Concatenable,
      cero,
      ++,
    pegotear,
    Mónada,
      fija,
      >>=,
    Digital,
      digitalizar,
      levantar_dígitos,
    Posta,
      Sí,
      No,
    Quizá,
      Nada,
      Este,
    siempre,
    plegard, plegari, dar_vuelta, filtrar, zierre, para_cada,
    Funtor,
      fap,
    Comparación,
      MENOR,
      IGUAL,
      MAYOR,
    Ordenable,
      comparar,
    Mostrable,
      mostrar,
    Numérico,
      +, -, *, /, %,
    Lógico,
      &, |, ^, ~,
    escupir,
    escupirm,
    escupir_letra,
  )

chirimbolo diestro  50 ;
chirimbolo diestro  75 $
chirimbolo diestro 100 :=
chirimbolo zurdo   150 >>=
chirimbolo diestro 200 ||
chirimbolo diestro 300 &&
chirimbolo zurdo   450 ==
chirimbolo zurdo   450 !=
chirimbolo zurdo   450 <=
chirimbolo zurdo   450 <
chirimbolo zurdo   450 >=
chirimbolo zurdo   450 >
chirimbolo diestro 500 :
chirimbolo diestro 500 ++
chirimbolo zurdo   550 |
chirimbolo diestro 600 ..
chirimbolo diestro 600 ...
chirimbolo zurdo   650 +
chirimbolo zurdo   650 -
chirimbolo zurdo   650 ^
chirimbolo zurdo   750 *
chirimbolo zurdo   750 /
chirimbolo zurdo   750 %
chirimbolo zurdo   750 &
chirimbolo diestro 800 >>
chirimbolo diestro 800 <<
chirimbolo prefijo 825 ~
chirimbolo diestro 900 .
chirimbolo zurdo   950 ->

OJO. Efectos secundarios y referencias

el ;  de coso en cosito en cosito
  dados _ x da x

el desref de Ref de coso en coso
  es PRIM.desref

el := de Ref de coso en coso en ()
  es PRIM.asignar

OJO. Continuaciones

el ccc de (Cont de coso en coso) en coso
  es PRIM.ccc

el invocar de (Cont de coso) en coso en cosito
  es PRIM.invocar

OJO. Funciones

el -> de coso en (coso en cosito) en cosito
  dados x f da f x

el $ de (coso en cosito) en coso en cosito
     dada f da f

el . de (mengano en zutano)
     en (fulano en mengano)
     en fulano en zutano
  dadas f g x da f (g x)

el siempre de coso en cosito en coso
  dados x _ da x

OJO. Postas

una Posta es
  OJO. No alterar el orden de los constructores.
  bien Sí
  bien No

el && de Posta en Posta en Posta
  dados Sí x da x
  dados No _ da No

el || de Posta en Posta en Posta
  dados No x da x
  dados Sí _ da Sí

el xor de Posta en Posta en Posta
  dados Sí Sí da No
  dados Sí No da Sí
  dados No Sí da Sí
  dados No No da No

el negar de Posta en Posta
  dado Sí da No
  dado No da Sí

el todos de [Posta] en Posta
  es plegard (el &&) Sí

el no_todos de [Posta] en Posta
  es negar . todos

el alguno de [Posta] en Posta
  es plegard (el ||) No

el ninguno de [Posta] en Posta
  es negar . alguno

el todo_el_mundo de (coso en Posta) en [coso] en Posta
  dado p da todos . fap p

el no_todo_el_mundo de (coso en Posta) en [coso] en Posta
  dado p da no_todos . fap p

el alguien de (coso en Posta) en [coso] en Posta
  dado p da alguno . fap p

el nadie de (coso en Posta) en [coso] en Posta
  dado p da ninguno . fap p

OJO. Pares

el pi1 de (coso, cosito) en coso
  dado (x, _) da x

el pi2 de (coso, cosito) en cosito
  dado (_, x) da x

OJO. Letras

el letra_a_numerito de Letra en Numerito
  es PRIM.letra_a_numerito

el numerito_a_letra de Numerito en Letra
  es PRIM.numerito_a_letra

OJO. Espichar

el espichar de Numerito en coso
  es PRIM.espichar

OJO. Listas

una Lista de a es
  bien Vacía
  bien : a [a]

el plegard de (coso en cosito en coso)
           en cosito
           en [coso] en cosito
  dadas f z []       da z
  dadas f z (x : xs) da f x (plegard f z xs)

el plegari de (cosito en coso en coso)
           en cosito
           en [coso] en cosito
  dadas f z []       da z
  dadas f z (x : xs) da plegari f (f z x) xs

el zierre de (fulano en mengano en zutano)
          en [fulano] en [mengano] en [zutano]
  dados f []       _        da []
  dados f (_ : _)  []       da []
  dados f (x : xs) (y : ys) da f x y : zierre f xs ys

el para_cada de (coso en ()) en [coso] en ()
  dados f []       da ()
  dados f (x : xs) da f x; para_cada f xs

el dar_vuelta de [coso] en [coso]
  dada xs da rec xs []
donde
  el rec de [coso] en [coso] en [coso]
  dadas []       ys da ys
  dadas (x : xs) ys da rec xs (x : ys)
boludo

el filtrar de (coso en Posta) en [coso] en [coso]
  dados p [] da []
  dados p (x : xs)
     si p x da x : filtrar p xs
     si no  da filtrar p xs

OJO. Quizás

un Quizá de a es
  bien Nada
  bien Este a

OJO. Igualable

cualidad Igualable para coso
  el == de coso en coso en Posta
boludo

el != de coso en coso en Posta
      con Igualable para coso
  dados x y da negar (x == y)

encarnar Igualable para Posta
  el ==
    dados Sí Sí da Sí
    dados Sí No da No
    dados No Sí da No
    dados No No da Sí
boludo

encarnar Igualable para (a, b) con (Igualable para a,
                                    Igualable para b)
  el ==
    dados (a1, b1) (a2, b2) da a1 == a2 && b1 == b2
boludo

encarnar Igualable para [coso] con Igualable para coso
  el ==
    dados []       []       da Sí
    dados []       (_ : _)  da No
    dados (_ : _)  []       da No
    dados (x : xs) (y : ys) da x == y && xs == ys
boludo

encarnar Igualable para Quizá de coso con Igualable para coso
  el ==
    dados Nada     Nada     da Sí
    dados Nada     (Este _) da No
    dados (Este _) Nada     da No
    dados (Este x) (Este y) da x == y
boludo

encarnar Igualable para Ref de coso
  el == es PRIM.igual_ref
boludo

OJO. Comparación

una Comparación es
  bien MENOR
  bien IGUAL
  bien MAYOR

cualidad Ordenable para coso
  el comparar de coso en coso en Comparación
boludo

encarnar Ordenable para [coso] con Ordenable para coso
  el comparar
    dados []       []       da IGUAL
    dados []       (_ : _)  da MENOR
    dados (_ : _)  []       da MAYOR
    dados (x : xs) (y : ys) da
      mirar comparar x y
        si MENOR da MENOR
        si MAYOR da MAYOR
        si IGUAL da comparar xs ys
      boludo
boludo

OJO. Lógico

cualidad Lógico para coso
  el |  de coso en coso en coso
  el &  de coso en coso en coso
  el ^  de coso en coso en coso
  el ~  de coso en coso
boludo 

encarnar Lógico para Posta
  el |  es (el ||)
  el &  es (el &&)
  el ^  es xor
  el ~
    dado Sí da No
    dado No da Sí
boludo

encarnar Lógico para [coso] con Lógico para coso
  el |  es zierre (el |)
  el &  es zierre (el &)
  el ^  es zierre (el ^)
  el ~  es fap    (el ~)
boludo

el <= de coso en coso en Posta
      con Ordenable para coso
  dados x y da
    mirar comparar x y
    si MAYOR da No
    si no    da Sí
    boludo

el <  de coso en coso en Posta
      con Ordenable para coso
  dados x y da
    mirar comparar x y
    si MENOR da Sí
    si no    da No
    boludo

el >= de coso en coso en Posta
      con Ordenable para coso
  dados x y da
    mirar comparar x y
    si MENOR da No
    si no    da Sí
    boludo

el >  de coso en coso en Posta
      con Ordenable para coso
  dados x y da
    mirar comparar x y
    si MAYOR da Sí
    si no    da No
    boludo

OJO. Funtores

cualidad Funtor para bolsa
  el fap de (coso en cosito)
         en bolsa de coso
         en bolsa de cosito
boludo

encarnar Funtor para PRIM.Lista
  el fap
    dadas f []       da []
    dadas f (x : xs) da f x : fap f xs
boludo

OJO. Mónadas

cualidad Mónada para bolsa
  la fija de coso en bolsa de coso
  el >>=  de bolsa de coso
          en (coso en bolsa de cosito)
          en bolsa de cosito
boludo

encarnar Mónada para Falible
  la fija es Joya
  el >>=
    dados (Joya x)     f da f x
    dados (Cagó fuego) _ da Cagó fuego
boludo

encarnar Mónada para Lista
  la fija dado x da [x]
  el >>= dados xs f da pegotear (fap f xs)
boludo

OJO. Concatenable

cualidad Concatenable para a
  el cero de a
  el ++ de a en a en a
boludo

encarnar Concatenable para [coso]
  el cero es []
  el ++
    dadas []       ys da ys
    dadas (x : xs) ys da x : xs ++ ys
boludo

encarnar Concatenable para Texto
  el cero es ""
  el ++ dados (Texto xs) (Texto ys) da Texto (xs ++ ys)
boludo

el pegotear de [coso] en coso
           con Concatenable para coso
  es plegard (el ++) cero

OJO. Mostrable

cualidad Mostrable para a
  el mostrar de a en Texto
boludo

encarnar Mostrable para Posta
  el mostrar
    dado Sí da "Sí"
    dado No da "No"
boludo

encarnar Mostrable para ()
  el mostrar dado () da "()"
boludo

encarnar Mostrable para (coso1, coso2) con (
           Mostrable para coso1,
           Mostrable para coso2,
         )
  el mostrar
    dado (x1, x2) da "(" ++
      mostrar x1 ++ ", " ++
      mostrar x2 ++
    ")"
boludo

encarnar Mostrable para Letra
  el mostrar dada x da Texto ['\'', x, '\'']
boludo

encarnar Mostrable para [coso] con Mostrable para coso
  el mostrar dada xs da "[" ++ mostrar_lista xs ++ "]"
  donde
    el mostrar_lista de [coso] en Texto
                     con Mostrable para coso
      dados []       da ""
      dados [x]      da mostrar x
      dados (x : xs) da mostrar x ++ ", " ++ mostrar_lista xs
  boludo
boludo

encarnar Mostrable para Texto
  el mostrar dado (Texto s) da "\"" ++ mostrar_cadena s ++ "\""
  donde
    el mostrar_cadena de [Letra] en Texto
      dados []       da ""
      dados (x : xs) da Texto [x] ++ mostrar_cadena xs
  boludo
boludo

encarnar Mostrable para Comparación
  el mostrar
    dado IGUAL da "IGUAL"
    dado MENOR da "MENOR"
    dado MAYOR da "MAYOR"
boludo

encarnar Mostrable para Ref de coso
                   con Mostrable para coso
  el mostrar dado (Ref x)
               da "(Ref " ++ mostrar x ++ ")"
boludo

encarnar Mostrable para Quizá de coso
                    con Mostrable para coso
  el mostrar
    dado Nada     da "Nada"
    dado (Este x) da "(Este " ++ mostrar x ++ ")"
boludo

encarnar Mostrable para Falible de coso
                    con Mostrable para coso
  el mostrar
    dado (Joya x)     da "(Joya " ++ mostrar x ++ ")"
    dado (Cagó fuego) da "(Cagó " ++ mostrar fuego ++ ")"
boludo

encarnar Mostrable para a en b
  el mostrar dada _ da "<fun>"
boludo

OJO. Salida estándar de los pobres

el escupir_letra es PRIM.escupir_letra

el escupir de Texto en ()
  dado (Texto letras) da
    para_cada escupir_letra letras

el escupirm de coso en () con Mostrable para coso
  dado x da
    escupir (mostrar x);
    escupir "\n"

OJO. Un tipo es digital si se puede convertir ida y vuelta
OJO. en una lista de numeritos.

cualidad Digital para coso
  el digitalizar      de coso en [Numerito]
  el levantar_dígitos de [Numerito] en coso
boludo

OJO. Números

cualidad Numérico para coso
  el +  de coso en coso en coso
  el -  de coso en coso en coso
  el *  de coso en coso en coso
  el /  de coso en coso en coso
  el %  de coso en coso en coso
boludo

OJO. Numeritos

encarnar Numérico para Numerito
  el +  es PRIM.sumar_numerito
  el -  es PRIM.restar_numerito
  el *  es PRIM.multiplicar_numerito
  el /  es PRIM.dividir_numerito
  el %  es PRIM.resto_numerito
boludo

encarnar Lógico para Numerito
  el |  es PRIM.o_numerito
  el &  es PRIM.y_numerito
  el ^  es PRIM.xor_numerito
  el ~  es PRIM.no_numerito
boludo

el << es PRIM.mover_izq_numerito
el >> es PRIM.mover_der_numerito

encarnar Igualable para Numerito
  el == es PRIM.igual_numerito
boludo

encarnar Ordenable para Numerito
  el comparar
    dados x y
       si PRIM.igual_numerito x y da IGUAL
       si PRIM.menor_numerito x y da MENOR
       si no da MAYOR
boludo

encarnar Mostrable para Numerito
  el mostrar
    dado 0# da "0#"
    dado n  da mostrar_dígitos (en_base n 10#) ++ "#"
  donde
    el en_base de Numerito en Numerito en [Numerito]
    dados 0# _ da []
    dados n  b da
      en_base (PRIM.dividir_numerito n b) b ++ [PRIM.resto_numerito n b]

    el mostrar_dígitos de [Numerito] en Texto
    dado [] da ""
    dado (0# : ds) da "0" ++ mostrar_dígitos ds
    dado (1# : ds) da "1" ++ mostrar_dígitos ds
    dado (2# : ds) da "2" ++ mostrar_dígitos ds
    dado (3# : ds) da "3" ++ mostrar_dígitos ds
    dado (4# : ds) da "4" ++ mostrar_dígitos ds
    dado (5# : ds) da "5" ++ mostrar_dígitos ds
    dado (6# : ds) da "6" ++ mostrar_dígitos ds
    dado (7# : ds) da "7" ++ mostrar_dígitos ds
    dado (8# : ds) da "8" ++ mostrar_dígitos ds
    dado (9# : ds) da "9" ++ mostrar_dígitos ds
    dado (_  : ds) da "_" ++ mostrar_dígitos ds

  boludo
boludo

encarnar Digital para Numerito
  el digitalizar
    dado n  da [n]
  el levantar_dígitos
    dado []     da 0#
    dado (x:xs) da PRIM.sumar_numerito x (levantar_dígitos xs)
boludo

el .. dados i j
  si i > j da []
  si no    da i : (i + 1..j)

el ... dados i j
  si i >= j da []
  si no     da i : (i + 1...j)

