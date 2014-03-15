require "./cassowary-gateway.k"

module BABELSBERG-INT-SYNTAX
  syntax AtomicConstraint   ::= Expression "<=" Expression
                              | Expression ">=" Expression
                              | Expression "=" Expression

  syntax Constraint         ::= AtomicConstraint
                              > Constraint "&&" Constraint      [left]

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
  syntax Value              ::= Bool | Number | Constraint
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
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
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

  // S-Unsat
  // TODO... this should really be in the S-Asgn and S-Always rules
  rule <k>_ => unsat</k> <E> (-1 |-> -2) => .Map </E>

  syntax K ::= "checkSat" "(" Map "," Constraint ")"
  // S-Asgn
  rule <k> X := V:Number => checkSat(#getAssignments(C && X = V && #getStays(E), Fd), C) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>

  // S-Always
  rule <k> always C0:Constraint => checkSat(#getAssignments(C && C0 && #getStays(E), Fd), C && C0) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>

  // S-unsat -- Hack, we're using an invalid mapping (-1 -> -2) as marker for unsat
  rule <k> checkSat((-1 |-> -2), C) ~> _ => unsat </k>
  // S-sat
  rule <k> checkSat(E, C) => . ...</k> <E> _ => E </E> <C> _ => C </C>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
endmodule
