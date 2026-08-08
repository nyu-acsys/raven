Source files with CRLF line endings lex the same as LF ones. The sources are
written here with explicit \r\n rather than checked in, since .gitattributes
normalizes every committed .rav to LF on checkout.

A CRLF file verifies, including through line and block comments:

  $ printf 'field f: Int   // trailing comment\r\n\r\n/* a block comment\r\n   spanning lines */\r\nproc foo(x: Ref) returns (r: Int)\r\n  requires own(x.f, 1)\r\n{\r\n  val y := x.f\r\n  return y\r\n}\r\n' > crlf_ok.rav
  $ dune exec -- raven --shh ./crlf_ok.rav
  Verification successful.

Reported locations are unaffected by the carriage return, which belongs to the
line break rather than to the line's text, and a CRLF break still ends a
statement the way an LF one does -- neither statement below is written with a
semicolon. The two runs differ only in the file name:

  $ printf 'field f: Int\r\n\r\ninv i(x: Ref) { own(x.f, 1) }\r\n\r\nproc bar(x: Ref)\r\n  requires i(x)\r\n{\r\n  unfold i(x)\r\n  val y := x.f\r\n}\r\n' > crlf_err.rav
  $ printf 'field f: Int\n\ninv i(x: Ref) { own(x.f, 1) }\n\nproc bar(x: Ref)\n  requires i(x)\n{\n  unfold i(x)\n  val y := x.f\n}\n' > lf_err.rav
  $ dune exec -- raven --shh ./crlf_err.rav
  [Error] File "./crlf_err.rav", line 10, columns 0-1:
  10 | }
       ^
  Verification Error: Missing fold for unfolded invariant i(x).
  [Error] File "./crlf_err.rav", line 8, columns 2-13:
  8 |   unfold i(x)
        ^^^^^^^^^^^
  Related Location: i(x) was unfolded here.
  [1]
  $ dune exec -- raven --shh ./lf_err.rav
  [Error] File "./lf_err.rav", line 10, columns 0-1:
  10 | }
       ^
  Verification Error: Missing fold for unfolded invariant i(x).
  [Error] File "./lf_err.rav", line 8, columns 2-13:
  8 |   unfold i(x)
        ^^^^^^^^^^^
  Related Location: i(x) was unfolded here.
  [1]

A stray carriage return that is not part of a line break stays a lexical error:

  $ printf 'field f: Int\rfield g: Int\n' > stray_cr.rav
  $ dune exec -- raven --shh ./stray_cr.rav
  [Error] File "./stray_cr.rav", line 1, columns 12-12:
  1 | field f: Intfield g: Int
                  ^
  Syntax Error: Unexpected character ''.
  [1]
