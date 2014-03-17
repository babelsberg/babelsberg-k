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

module BABELSBERG-SYNTAX
  imports BABELSBERG-RECORDS-SYNTAX
endmodule

module BABELSBERG-RECORDS
  imports BABELSBERG-INT
  imports BABELSBERG-RECORDS-SYNTAX

  // E-Rec expressed in strict annotations in syntax
  // E-Field
  rule ({ L : V } . L) => V
  rule ({ L : V, A } . L) => V
  rule ({ B, L : V, A } . L) => V
  rule ({ B, L : V } . L) => V

  // Types? Need to read about them in the K types tutorial

  // Todo: Constraint construction
endmodule
