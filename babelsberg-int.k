require "./cassowary-gateway.k"
require "./babelsberg.k"

module BABELSBERG-INT-SYNTAX
  imports BABELSBERG-CONSTRAINT-SYNTAX

  syntax Statement          ::= "skip"
                              | Variable ":=" Expression        [strict(2)]
                              | "always" Constraint
                              | "weak" "always" Constraint
                              | Statement ";" Statement         [left]
			      | "unsat"

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
  imports CASSOWARY-GATEWAY

  // tell K to stop evaluation when a Value is found
  syntax KResult            ::= Value

  // state
  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> . </C> // the current constraint system
  </T>

  // E-Var
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>

  // E-Op
  rule (I1:Int / I2:Int):Expression => I1 /Int I2
  rule (I1:Int * I2:Int):Expression => I1 *Int I2
  rule (I1:Int + I2:Int):Expression => I1 +Int I2
  rule (I1:Int - I2:Int):Expression => I1 -Int I2
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2

  // S-Asgn
  rule <k> X := V:Number => . ...</k>
       <E> E => #getAssignments(C && X = V && #getStays(E)) </E>
       <C> C => C </C>

  // S-Always
  rule <k> always C0:Constraint => . ...</k>
       <E> E => #getAssignments(C && C0 && #getStays(E)) </E>
       <C> C => C && C0 </C>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
endmodule
