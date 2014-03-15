require "./babelsberg-int.k"

module BABELSBERG-RECORDS-SYNTAX
  imports BABELSBERG-INT-SYNTAX

  syntax Label      ::= Id

  syntax RecordExpression ::= Label ":" Expression                  [strict(2)]
                            | RecordExpression "," RecordExpression [left, seqstrict]
  syntax Expression  ::= "{" RecordExpression "}"		    [strict]
  	               | Expression "." Label			    [strict(1)]

  syntax RecordValue      ::= Label ":" Value                       [strict(2)]
                            | RecordValue "," RecordValue           [left, seqstrict]
  syntax Value      ::= "{" RecordValue "}"
endmodule

module BABELSBERG-RECORDS
  imports BABELSBERG-INT
  imports BABELSBERG-RECORDS-SYNTAX

  // E-Rec expressed in strict annotations in syntax
  // E-Field
  rule ({ L : V, A } . L) => V
  rule ({ B, L : V, A } . L) => V
  rule ({ B, L : V } . L) => V
endmodule
