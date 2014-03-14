module BABELSBERG-CONSTRAINT-SYNTAX
  syntax AtomicConstraint   ::= CExpression "<=" CExpression
                              | CExpression ">=" CExpression
                              | CExpression "=" CExpression

  syntax Constraint         ::= AtomicConstraint
                              > Constraint "&&" Constraint      [left]

  syntax CExpression        ::= Number | Variable
                              | CExpression "/" CExpression     [left]
                              | CExpression "*" CExpression     [left]
                              > CExpression "+" CExpression     [left]
                              > CExpression "-" CExpression     [left]
endmodule
