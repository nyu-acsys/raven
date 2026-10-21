The obligations whose fingerprints an edit of fingerprints.rav changes.

  $ fp() { dune exec -- raven --shh --fingerprints "$1" | tr -d '\r' | grep -v successful | awk '{print $2, $1}' | sort; }
  $ fp fingerprints.rav > base
  $ changed() { sed "$1" fingerprints.rav > variant.rav; fp variant.rav | join base - | awk '$2 != $3 {s = s " " $1} END {print (s == "" ? "none" : substr(s, 2))}'; }
  $ cut -d' ' -f1 base
  N.g_pos
  N.uses_g
  callee
  caller
  double_nonneg
  unrelated
  $ changed 's/x.f := n + n;/x.f := 2 * n;/'
  callee
  $ changed 's/ensures own(x.f, double(n), 1.0)/ensures own(x.f, double(n), 1.0) \&\& n >= 0/'
  callee caller
  $ changed 's/{ n + n }/{ 2 * n }/'
  callee caller double_nonneg
  $ changed 's/ensures double(n) >= 0/ensures double(n) >= n/'
  callee caller double_nonneg
  $ changed 's/^{}$/{ assert n >= 0; }/'
  double_nonneg
  $ changed 's/z := y + 1;/z := 1 + y;/'
  unrelated
  $ changed 's/M.g(n) >= 1/M.g(n) > 0/'
  N.g_pos N.uses_g
  $ changed '1s/^/\n\n/'
  none
