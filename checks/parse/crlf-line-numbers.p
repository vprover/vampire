% Parser regression test (CRLF line endings): this file uses \r\n line ends;
% each used to be counted as two lines. Expected: parse error reported on line 4.
fof(a1, axiom, p).
fof(bad, axiom, q & ).
