(TeX-add-style-hook
 "TypeSystem"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("amsart" "11pt")))
   (TeX-run-style-hooks
    "latex2e"
    "amsart"
    "amsart11"))
 :latex)

