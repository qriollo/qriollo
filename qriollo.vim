" Vim syntax file
" Language:     Qriollo

if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword qriolloPreproc chirimbolo gringo gringa gringos gringas
syn keyword qriolloPreproc SI BOLUDO BOLUDA GRINGO GRINGA GRINGOS GRINGAS
syn keyword qriolloReserved zurdo diestro prefijo
syn keyword qriolloReserved PRIM Pendorcho
syn keyword qriolloReserved C Py Jvm
""Ref Numerito Letra Texto Flotante Pendorcho Posta Sí No Lista Vacía Falible Joya Cagó Mónada fija""
syn keyword qriolloInclude enchufar entregar
syn keyword qriolloStructure boludo boluda cualidad encarnar mirar tiene tienen donde
syn keyword qriolloKeyword ante bien che como con cuyo cuya cuyos cuyas da dado dada dados dadas de el la los las en es son no para pero ponele que si un una unas unos

syn region qriolloString
           \ start=+"+  skip=+\\\\\|\\"+ end=+"+ contains=qriolloSpecialChar
           \ contains=pythonEscape,pythonSpaceError,pythonDoctest,@Spell

syn match qriolloCharacter "[^a-zA-Z0-9_']'\([^\\]\|\\[^']\+\|\\'\)'"lc=1 contains=qriolloSpecialChar
syn match qriolloNumber "\<[0-9]\+[#]\="

syn match qriolloSpecialChar
          \ contained "\\[\"\\'&\\abfnrtv]"

syn region qriolloComment start="OJO[.]" end="$" keepend

hi def link qriolloPreproc       PreProc
hi def link qriolloReserved      Function
hi def link qriolloInclude       Include
hi def link qriolloStructure     Structure
hi def link qriolloKeyword       Keyword
hi def link qriolloString        String
hi def link qriolloCharacter     Character
hi def link qriolloSpecialChar   SpecialChar
hi def link qriolloNumber        Number
hi def link qriolloComment       Comment

syn sync minlines=200
syn sync maxlines=500

let b:current_syntax = "qriollo"

