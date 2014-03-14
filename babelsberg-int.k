require "builtins/builtins.k"
require "io/uris.k"

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
  imports URIS

  imports BABELSBERG-INT-SYNTAX

  // K-specific
  syntax KResult            ::= Value

  // getModel expresses E ||= C
  // it gets stuck if no model is available, so we don't need an explicit "unsat" case
  syntax Map ::= "#getModel" "(" Constraint "," String ")" [function]
               | "#writeAndPoll" "(" Constraint "," Int ")" [function]
	       | "#poll" "(" Int "," K ")" [function]
	       | "#checkResultOfRead" "(" Int "," TCPAnswer ")" [function]
	       | "#closeAndConvert" "(" Int "," String ")" [function]
	       | "#convert" "(" K "," Constraint ")" [function]
	       | "#convertRest" "(" Map "," Constraint ")" [function]
  rule #getModel(C, Path) => #writeAndPoll(C, #open(Path))
  rule #writeAndPoll(C, Fd) => #poll(Fd, #write(Fd, K2String(C)))
  rule #poll(Fd:Int, _) => #checkResultOfRead(Fd, #read(Fd, 10000)) // try to read all
  rule #checkResultOfRead(Fd:Int, ReadResult:String) => #closeAndConvert(Fd, ReadResult)
  rule #checkResultOfRead(Fd:Int, _) => #poll(Fd, #write(Fd, "")) // eof-case
  rule #closeAndConvert(Fd, ReadResult) => #convert(#close(Fd), #parse(ReadResult, "Constraint"))
  rule #convert(_, Constraint) => #convertRest(.Map, Constraint)
  rule #convertRest(M, V = N && C) => #convertRest(M (V |-> N), C)
  rule #convertRest(M, V = N) => #convertRest(M (V |-> N), .)
  rule #convertRest(M, .) => M
  // getStays converts Map into stay constraints
  syntax Constraint ::= "#getStays" "(" Constraint "," Map ")" [function]
  rule #getStays(C, (X |-> V) Rest) => #getStays(C && X = V, Rest) [function]
  rule #getStays(C, .) => C

  // state
  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> 1=1 </C> // the actual constraint system
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
  rule <k> X := V:Number => . ...</k>
       <E> E => #getModel(C && (X = V) && #getStays(1 = 1, E), "./z3") </E>
       <C> C => C </C>

  // S-Always
  rule <k> always C0:Constraint => . ...</k>
       <E> E => #getModel(C && C0 && #getStays(1 = 1, E), "./z3") </E>
       <C> C => C && C0 </C>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
endmodule
