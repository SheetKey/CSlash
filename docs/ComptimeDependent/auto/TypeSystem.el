(TeX-add-style-hook
 "TypeSystem"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("amsart" "11pt")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "urladdr")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "email")
   (TeX-run-style-hooks
    "latex2e"
    "amsart"
    "amsart11")
   (LaTeX-add-environments
    '("blockquote" LaTeX-env-args ["argument"] 0)))
 :latex)

