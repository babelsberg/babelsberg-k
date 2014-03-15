require "./babelsberg-records.k"

module BABELSBERG-MRECORDS-SYNTAX
  imports BABELSBERG-RECORDS-SYNTAX

  syntax Statement ::= Variable "." Label ":=" Expression  [strict(1 3)]
endmodule

module BABELSBERG-MRECORDS
  imports BABELSBERG-MRECORDS-SYNTAX
  imports BABELSBERG-RECORDS

  // S-AsgnField
  rule <k> X.L := V:Expression => checkSat(#getAssignments(C && X.L = V && #getStays(E), Fd), C) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>
  // S-AsgnFieldUnsat is taken care of in Int semantics
endmodule
