require "./babelsberg-int.k"

module BABELSBERG-RECORDS-SYNTAX
  imports BABELSBERG-INT-SYNTAX

  syntax Label      ::= Id

  syntax RecordExpression ::= Label ":" Expression                  [strict(2)]
                            | RecordExpression "," RecordExpression [left, seqstrict]
  syntax Expression  ::= "{" RecordExpression "}"                   [strict]
                       | Expression "." Label                       [strict(1)]

  syntax RecordValue      ::= Label ":" Value                       [strict(2)]
                            | RecordValue "," RecordValue           [left, seqstrict]
  syntax Value      ::= "{" RecordValue "}"

  syntax RecordType ::= Label ":" Type
                      | RecordType "," RecordType [left]
  syntax Type       ::= Number | Bool | "{" RecordType "}"
endmodule

module BABELSBERG-RECORDS
  imports BABELSBERG-INT
  imports BABELSBERG-RECORDS-SYNTAX

  // E-Rec
  // realized by [strict] annotation above
  // E-Field
  rule ({ L : V } . L) => V // E-Field-One
  rule ({ L : V, A } . L) => V // E-Field-First
  rule ({ X : V, A } . L) => ({ A } . L) // E-Field-Not-First

  // Types? Need to read about them in the K types tutorial
endmodule
