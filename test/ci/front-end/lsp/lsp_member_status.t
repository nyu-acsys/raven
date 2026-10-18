Each member gets the worst status of the procedures checked for it: a loop counts
towards the procedure it is in, and a func's contract towards the func. A module
summarizes the members nested in it, including those it inherits, such as the lemmas
for the axioms of its interface.

  $ dune exec -- raven --shh --lsp-mode --lsp-annotations ./lsp_member_status.rav | python3 lsp_member_status.py
  2 func M.double verified
  8 func M.bad failed
  14 proc M.sum failed
  28 proc M.wrong failed
  34 lemma M.fine verified
  39 proc loop_fails failed
  50 lemma Good.Inner.zero verified
  55 lemma Good.one verified
  63 type Fst.T -
  64 val Fst.id -
  65 func Fst.comp -
  66 func Fst.frame -
  67 func Fst.valid -
  68 func Fst.fpuAllowed -
  62 lemma Fst.compAssoc verified inherited
  62 lemma Fst.compCommute failed inherited
  62 lemma Fst.compFrameInv verified inherited
  62 lemma Fst.compId verified inherited
  62 lemma Fst.compValid verified inherited
  62 lemma Fst.fpuValid verified inherited
  62 lemma Fst.frameId verified inherited
  62 lemma Fst.idValid verified inherited
  62 lemma Fst.weak_frameCompInv verified inherited
  1 module M failed verified=2 failed=3
  48 module Good verified verified=2
  49 module Good.Inner verified verified=1
  62 module Fst failed verified=8 failed=1

Members not checked after the error limit was reached are skipped.

  $ dune exec -- raven --shh --lsp-mode --lsp-annotations --max-errors=1 ./lsp_member_status.rav | python3 lsp_member_status.py
  2 func M.double verified
  8 func M.bad failed
  14 proc M.sum skipped
  28 proc M.wrong skipped
  34 lemma M.fine skipped
  39 proc loop_fails failed
  50 lemma Good.Inner.zero skipped
  55 lemma Good.one skipped
  63 type Fst.T -
  64 val Fst.id -
  65 func Fst.comp -
  66 func Fst.frame -
  67 func Fst.valid -
  68 func Fst.fpuAllowed -
  1 module M failed verified=1 skipped=3 failed=1
  48 module Good skipped skipped=2
  49 module Good.Inner skipped skipped=1
  62 module Fst -

With type errors nothing is verified, so no member has a status.

  $ cat > type_error.rav <<EOF
  > proc p() { var x: Int := true; }
  > EOF
  $ dune exec -- raven --shh --lsp-mode --lsp-annotations ./type_error.rav | python3 lsp_member_status.py
  1 proc p -
