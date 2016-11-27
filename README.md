# The James construction in Agda

The code in this directory is described in the article "The James construction and π4(S3) in
homotopy type theory" (submitted). Here is a short description of every file present here:

- `Base.agda` : contains the basic notions of homotopy type theory used in the other files (mostly
  copy-pasted from the HoTT-Agda library)
- `PathInduction.agda` : contains the `path-induction` machinery, and many operations on squares
- `Pushout.agda` : contains the definition of pushouts
- `JamesTwoMaps.agda` : contains the definition of the types `JA` and `J∞A`, and of the two maps
  between them
- `JamesFirstComposite.agda` : contains the proof that the first composite (going from `J∞A` to
  itself) is the identity
- `JamesSecondComposite.agda` : contains the proof that the second composite (going from `JA` to
  itself) is the identity
- `JamesContractibility.agda` : contains the proof that the pushout used to show that `JA` is
  equivalent to `ΩΣA` is contractible
- `JamesAll.agda` : imports the last four files

The files `PathInductionSimplified.agda` and `ExPathInduction.agda` are independent from the rest
and are used only to provide nicer code fragments in the paper (for the description of the
`path-induction` mechanisme and the example of a coherence operation).

The script `copycodeandextract.sh` (which calls `extract.py` internally) is used to split the code
into code fragments for inclusion in a LaTeX file (requires Agda and Python).