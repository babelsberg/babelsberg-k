module BABELSBERG-INT-CONSTRAINT-SYNTAX
  syntax AtomicConstraint   ::= CExpression "<=" CExpression
                              | CExpression ">=" CExpression
                              | CExpression "=" CExpression

  syntax Constraint         ::= AtomicConstraint
                              | "!" Constraint
                              > Constraint "&&" Constraint      [left]

  syntax CExpression        ::= Number | Variable
                              | CExpression "/" CExpression     [left]
                              | CExpression "*" CExpression     [left]
                              > CExpression "+" CExpression     [left]
                              > CExpression "-" CExpression     [left]
endmodule

module BABELSBERG-INT-SYNTAX
  imports BABELSBERG-INT-CONSTRAINT-SYNTAX

  syntax Statement          ::= Variable ":=" Expression        [strict(2)]
                              | "always" Constraint
                              | "weak" "always" Constraint
                              | Statement ";" Statement         [left]

  syntax Expression         ::= Number | Variable
                              | Expression "/" Expression       [strict, left]
                              | Expression "*" Expression       [strict, left]
                              > Expression "+" Expression       [strict, left]
                              > Expression "-" Expression       [strict, left]

  syntax Number             ::= Int | Float  // a builtin
  syntax Variable           ::= Id           // a builtin
  syntax Value              ::= Bool | Number
endmodule

module BABELSBERG-INT
  imports BABELSBERG-INT-SYNTAX

  syntax KResult            ::= Value

  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> .List </C> // the constraints

    // in/out, for communication with the solver
    <in stream="stdin"> .List </in>
    <out stream="stdout"> .List </out>
  </T>

  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>

  // Arithmetic
  rule (I1:Int / I2:Int):Expression => I1 /Int I2
  rule (I1:Int * I2:Int):Expression => I1 *Int I2
  rule (I1:Int + I2:Int):Expression => I1 +Int I2
  rule (I1:Int - I2:Int):Expression => I1 -Int I2
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2

  // S-Asgn
  rule <k> X := V => . ...</k> <E>... X |-> (_ => V) ...</E>
  rule <k> X := V => . ...</k> <E> Rho:Map (. => X |-> V) </E> when notBool (X in keys(Rho))

  // S-Always
  rule <k> always C0:Constraint => . ...</k> <C>... (. => ListItem(C0))</C>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
endmodule
