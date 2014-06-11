require "./cassowary-gateway.k"
require "./operations.k"

module BABELSBERG-INT-SYNTAX
  imports OPERATIONS

  syntax Statement ::= "skip"
                     | Variable ":=" Expression  [strict(2)]
		     | "always" Constraint
                     | Statement ";" Statement   [left]
	             | "unsat" | "unknown"

  syntax Constraint         ::= "True" | AtomicConstraint | Priority AtomicConstraint
                              | Constraint LogicalOp Constraint [left]

  syntax AtomicConstraint   ::= Expression CompareOp Expression [left]

  syntax Expression         ::= Number | Variable
                              | Expression MulOp Expression       [strict, left]
                              > Expression AddOp Expression       [strict, left]

  syntax Number             ::= Float
  syntax Variable           ::= Id
  syntax Value              ::= Number

  // tell K to stop evaluation when a Value is found
  syntax KResult            ::= Value
endmodule

module BABELSBERG-CONSTRAINT-SYNTAX
  imports Operations

  syntax ConstraintL ::= "T" | AtomicConstraintL | Priority AtomicConstraintL
                       | ConstraintL LogicalOp ConstraintL [left]

  syntax AtomicConstraintL ::= ExpressionL CompareOp ExpressionL [left]

  syntax ExpressionL ::= NumberL | VariableL
                       | ExpressionL MulOp ExpressionL       [strict, left]
                       > ExpressionL AddOp ExpressionL       [strict, left]

  syntax NumberL   ::= Float
  syntax VariableL ::= Id
  syntax ValueL    ::= Number

  // tell K to stop evaluation when a Value is found
  syntax KResult   ::= ValueL
endmodule

module BABELSBERG-INT
  imports BABELSBERG-INT-SYNTAX
  imports CASSOWARY-GATEWAY

  // state
  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> . </C> // the current constraint system
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
  </T>

  // E-Num
  // realized by [strict] annotation above
  // E-Var
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>
  // E-Op
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2

  syntax K ::= "#mapTo(" K ")" [function]
  // ToNum
  rule #mapTo(N:Number) => N:NumberL
  // ToVar
  rule #mapTo(V:Variable) => V:VariableL
  // ToArith
  rule #mapTo(E1 O:ArithOp E2) => #mapTo(E1) O:ArithOp #mapTo(E2)
  // ToCompare
  rule #mapTo(E1 O:CompareOp E2) => #mapTo(E1) O:CompareOp #mapTo(E2)
  // ToTrue
  rule #mapTo(True:Constraint) => (1.0 = 1.0):AtomicConstraintL
  // ToPriority
  rule #mapTo(P:Priority C) => P #mapTo(C)
  // ToCombine
  rule #mapTo(C1 O:LogicalOp C2) => #mapTo(C1) O:LogicalOp #mapTo(C2)

  syntax Map ::= "#mapFrom" "(" Map "," Constraint ")" [function]
  // FromEmpty
  rule #mapFrom(M, .) => M
  // FromOne
  rule #mapFrom(M, V:VariableL = N:NumberL && C:ConstraintL) => #mapFrom(M (V:Variable |-> N:Number), C)
  rule #mapFrom(M, C:AtomicConstraintL) => #mapFrom(M, C && .:AtomicConstraintL)

  syntax K ::= "#solve" "(" Constraint ")" [function]
             | "#solved" "(" Constraint ")" [function]
	     | "||=" "(" Map ")"
	     | "/||="
  // getModel (represent call to the solver)
  rule <k> #solve(C) => #solved(#getModel(#mapTo(C:Constraint), Fd)) ...</k> <Cassowary> Fd </Cassowary>

  // Unsat
  rule #solved(1.0 = 2.0) => /||=

  // Solve
  rule #solved(Ec) => ||=(#mapFrom(., Ec))

  syntax AtomicConstraint ::= "#stay" "(" Map ")" [function]
  // StayEmpty
  rule #stay(.) => .
  // StayOne
  rule #stay((X:Variable |-> V:Value) E0:Map) => (weak X = V) && #stay(E0)

  // S-Asgn
  rule <k> X := V:Expression => #solve(C && X = V && #stay(E)) ~> X := V ...</k> <E> E </E> <C> C </C>
  rule <k> ||=(Ec) ~> X := V => skip ...</k> <E> _ => Ec </E>
  // S-AsgnUnsat
  rule <k> /||= ~> X := V => unsat ...</k>

  // S-Always
  rule <k> always C0 => #solve(C && C0 && #stay(E)) ~> always C && C0 ...</k> <E> E </E> <C> C </C>
  rule <k> ||=(Ec) ~> always C => skip ...</k> <E> _ => Ec </E> <C> _ => C </C>
  // S-AlwaysUnsat
  rule <k> /||= ~> always C => unsat ...</k>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]

  // S-SeqSkip
  rule <k> skip ~> S2 => S2 </k>

  // S-SeqUnsat
  // TODO: figure out why this doesn't work
  // rule <k> unsat ~> _  => unsat </k>
endmodule
