(TeX-add-style-hook
 "tt"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "letterpaper" "left=125pt" "right=125pt") ("babel" "english") ("hyperref" "colorlinks" "linkcolor=blue" "citecolor=blue" "urlcolor=blue") ("biblatex" "backend=biber" "isbn=false" "url=false")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "geometry"
    "babel"
    "amsmath"
    "amssymb"
    "amsfonts"
    "amsthm"
    "graphicx"
    "mathpartir"
    "xspace"
    "mathtools"
    "tikz-cd"
    "bbm"
    "tabularx"
    "hyperref"
    "biblatex")
   (TeX-add-symbols
    '("id" ["argument"] 2)
    '("idfunc" ["argument"] 0)
    '("bif" 1)
    '("kancoe" 2)
    '("kancomp" 2)
    '("kanfill" 2)
    '("ol" 1)
    '("Path" 2)
    '("jdsub" 3)
    '("jdformula" 2)
    '("jdcofibeq" 3)
    '("jdcofib" 2)
    '("jdcofibeqtp" 3)
    '("tmtp" 2)
    '("judg" 2)
    '("defeqtp" 4)
    '("jdeqtp" 4)
    '("oftp" 3)
    '("wftp" 2)
    '("wfctx" 2)
    '("tup" 2)
    '("refl" 1)
    '("indidb" 1)
    '("indid" 1)
    '("ind" 1)
    '("rec" 1)
    '("unpack" 4)
    '("pack" 2)
    '("tek" 2)
    '("fak" 2)
    '("tokn" 1)
    '("Parens" 1)
    "R"
    "Q"
    "N"
    "Z"
    "I"
    "cI"
    "C"
    "A"
    "LL"
    "RR"
    "J"
    "Set"
    "cSet"
    "Hom"
    "Cat"
    "DCat"
    "scat"
    "grpd"
    "op"
    "cube"
    "B"
    "E"
    "one"
    "cone"
    "two"
    "three"
    "four"
    "inter"
    "parto"
    "mono"
    "cs"
    "tok"
    "tou"
    "toa"
    "tol"
    "rank"
    "dimension"
    "dom"
    "cod"
    "ran"
    "mul"
    "colim"
    "obj"
    "morph"
    "Ty"
    "Tm"
    "U"
    "emptyt"
    "unit"
    "ttt"
    "inc"
    "inlsym"
    "inrsym"
    "inl"
    "inr"
    "rform"
    "rintro"
    "relim"
    "rcomp"
    "runiq"
    "Weak"
    "Vble"
    "Exch"
    "Subst"
    "Empty"
    "Ext"
    "TExt"
    "Var"
    "TVar"
    "Arr"
    "suc"
    "CZ"
    "CS"
    "CT"
    "emptyctx"
    "production"
    "conv"
    "ctx"
    "Type"
    "jdeq"
    "defeq"
    "fst"
    "snd"
    "formula"
    "Sub"
    "Cofibs"
    "cofib"
    "abort"
    "app"
    "ct"
    "Bool"
    "True"
    "False"
    "bneg"
    "natpar"
    "pv"
    "prdsym"
    "prd"
    "lprd"
    "tprd"
    "dprd"
    "lam"
    "lamt"
    "lamu"
    "Lam"
    "lamk"
    "smsym"
    "sm"
    "lsm"
    "tsm"
    "dsm")
   (LaTeX-add-environments
    '("blockquote" LaTeX-env-args ["argument"] 0))
   (LaTeX-add-bibliographies
    "./sources")
   (LaTeX-add-amsthm-newtheorems
    "thm"
    "lem"
    "cor"
    "prop"
    "alg"
    "axiom"
    "defn"
    "conj"
    "prob"
    "exmp"
    "rem"
    "claim"
    "note"))
 :latex)

