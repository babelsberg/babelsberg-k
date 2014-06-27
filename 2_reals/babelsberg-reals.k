require "./cassowary-gateway.k"

module BABELSBERG-REALS-SYNTAX
  syntax Statement          ::= "skip"
                              | Variable ":=" Expression
                              | "always" Constraint
			      | "once" Constraint
                              | Statement ";" Statement         [left]
			      | "fail"
			      | "if" Expression "then" Statement "else" Statement
			      | "while" Expression "do" Statement

  syntax Constraint         ::= Expression | "weak" Expression
                              | Constraint "&&" Constraint [left]

  syntax Expression         ::= Constant | Variable
                              | Expression "/" Expression  [left, strict]
                              | Expression "*" Expression  [left, strict]
                              > Expression "+" Expression  [left, strict]
                              > Expression "-" Expression  [left, strict]
  	 		      > Expression "<=" Expression [left, strict]
                              > Expression ">=" Expression [left, strict]
                              > Expression "=" Expression  [left, strict]
			      > Expression "&&" Expression [left, strict]
			      > Expression "||" Expression [left, strict]

  syntax Constant           ::= "#t" | "#f" | "nil" | Float
  syntax Variable           ::= Id"?" | Id
  syntax Value              ::= Constant
endmodule

module BABELSBERG-CONSTRAINT-SYNTAX
  imports BABELSBERG-REALS-SYNTAX

  syntax SConstraint ::= SAtomicConstraint | "[[weak]]" SConstraint
                       | SConstraint "[[||]]" SConstraint | SConstraint "[[&&]]" SConstraint
  syntax SAtomicConstraint ::= SExpression "[[<=]]" SExpression
                            | SExpression "[[=]]" SExpression
			    | SExpression "[[>=]]" SExpression
  syntax SExpression ::= SConstant | SVariable
                      | SExpression "[[/]]" SExpression       [left]
                      | SExpression "[[*]]" SExpression       [left]                      
                      > SExpression "[[+]]" SExpression       [left]
                      > SExpression "[[-]]" SExpression       [left]
  syntax SConstant ::= "[[" Constant "]]"
  syntax SVariable ::= "[[" Variable "]]"
endmodule

module BABELSBERG-TYPE-SYNTAX
  syntax Type ::= "Boolean" | "Undefined" | "Real"

  syntax Bool ::= Type "==Type" Type [function]
  rule Boolean ==Type Boolean => true
  rule Real ==Type Real => true
  rule Undefined ==Type Undefined => true
  rule T1 ==Type T2 => false
endmodule

module BABELSBERG-REALS
  imports BABELSBERG-REALS-SYNTAX
  imports BABELSBERG-CONSTRAINT-SYNTAX
  imports BABELSBERG-TYPE-SYNTAX
  imports CASSOWARY-GATEWAY

  // tell K to stop evaluation when a Value is found
  syntax KResult            ::= Value | Type

  syntax Bool ::= Expression "==Value" Value [function]
  rule #t ==Value #t => true
  rule #f ==Value #f => true
  rule #t ==Value #f => false
  rule #f ==Value #t => false

  // state
  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> . </C> // the current constraint system
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
  </T>

  // Typing rules
  syntax Type ::= "tc(" K ")" [function]
  rule tc(nil) => Undefined
  rule tc(#t) => Boolean
  rule tc(#f) => Boolean
  rule tc(_:Float) => Real
  rule <k> tc(_:Variable) => tc(V) ...</k> <E>... X |-> V ...</E>
  rule <k> tc(X:Variable) => Undefined ...</k> <E> E </E> when notBool (X in keys(E))
  rule tc(X?) => tc(X)
  rule tc(E1 + E2) => tc(E1) when tc(E1) ==Type tc(E2)
  rule tc(E1 - E2) => tc(E1) when tc(E1) ==Type tc(E2)
  rule tc(E1 * E2) => tc(E1) when tc(E1) ==Type tc(E2)
  rule tc(E1 / E2) => tc(E1) when tc(E1) ==Type tc(E2)
  rule tc(E1 <= E2) => Boolean when tc(E1) ==Type tc(E2)
  rule tc(E1 >= E2) => Boolean when tc(E1) ==Type tc(E2)
  rule tc(E1 = E2) => Boolean when tc(E1) ==Type tc(E2)
  rule tc(E1 && E2) => Boolean when tc(E1) ==Type Boolean andBool tc(E2) ==Type Boolean
  rule tc(E1 || E2) => Boolean when tc(E1) ==Type Boolean andBool tc(E2) ==Type Boolean

  syntax Bool ::= "tcC(" K ")" [function]
  rule tcC(C) => true when tc(C) ==Type Boolean
  rule tcC(X = E) => true when tc(X) ==Type Undefined
  rule tcC(X = nil) => true
  rule tcC(weak C) => tcC(C)

  // Evaluation
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>
  rule <k> X:Variable => nil ...</k> <E> E </E> when notBool (X in keys(E))
  rule X? => X
  rule E1 + E2 => E1 +Float E2 when tc(E1 / E2) ==Type Real
  rule E1 - E2 => E1 -Float E2 when tc(E1 - E2) ==Type Real
  rule E1 * E2 => E1 *Float E2 when tc(E1 * E2) ==Type Real
  rule E1 / E2 => E1 /Float E2 when tc(E1 / E2) ==Type Real
  rule E1 <= E2 => E1 <=Float E2 when tc(E1 <= E2) ==Type Boolean andBool tc(E1) ==Type Real
  rule E1 >= E2 => E1 >=Float E2 when tc(E1 >= E2) ==Type Boolean andBool tc(E1) ==Type Real
  // rule E1 = E2 => E1 =Float E2 when tc(E1 = E2) ==Type Boolean andBool tc(E1) ==Type Real
  rule E1 = E2 => E1 ==Value E2 when tc(E1 = E2) ==Type Boolean andBool tc(E1) ==Type Boolean
  rule E1:Constant && E2:Constant => (E1 ==Value #t) andBool (E2 ==Value #t) when tc(E1 && E2) ==Type Boolean
  rule E1:Constant || E2:Constant => (E1 ==Value #t) orBool (E2 ==Value #t) when tc(E1 || E2) ==Type Boolean

  // ToMapping
  syntax K ::= "mapTo(" K ")" [function]
  rule mapTo(C:Constant) => [[ C ]]
  rule mapTo(X:Variable) => [[ X ]]
  rule mapTo(E1 / E2) => mapTo(E1) [[/]] mapTo(E2)
  rule mapTo(E1 * E2) => mapTo(E1) [[*]] mapTo(E2)
  rule mapTo(E1 + E2) => mapTo(E1) [[+]] mapTo(E2)
  rule mapTo(E1 - E2) => mapTo(E1) [[-]] mapTo(E2)
  rule mapTo(E1 = E2) => mapTo(E1) [[=]] mapTo(E2)
  rule mapTo(E1 <= E2) => mapTo(E1) [[<=]] mapTo(E2)
  rule mapTo(E1 >= E2) => mapTo(E1) [[>=]] mapTo(E2)
  rule mapTo(C1 || C2) => mapTo(C1) [[||]] mapTo(C2)
  rule mapTo(C1 && C2) => mapTo(C1) [[&&]] mapTo(C2)
  rule mapTo(weak C) => [[weak]] mapTo(C)

  // FromMapping
  syntax Map ::= "mapFrom" "(" Map "," SConstraint ")" [function]
  rule mapFrom(M, .) => M
  rule mapFrom(M, [[X:Variable]] [[=]] [[V:Constant]] [[&&]] C) => mapFrom(M (X |-> V), C)
  rule mapFrom(M, C:SAtomicConstraint) => mapFrom(M, C [[&&]] .)

  // Solve and Fail
  syntax K ::= "solve" "(" Constraint ")" [function]
             | "solved" "(" SConstraint ")" [function]
	     | "||=" "(" Map ")"
  // getModel (represent call to the solver)
  rule <k> solve(C) => solved(#getModel(mapTo(C), Fd)) ...</k> <Cassowary> Fd </Cassowary>
  rule solved(Ec:SConstraint) => ||=(mapFrom(., Ec))
  rule solved([[1.0]] [[=]] [[2.0]]) => fail
  rule <k> ||=(Ec) => skip ...</k> <E> _ => Ec </E>

  // Stay
  syntax Constraint ::= "stay" "(" Map ")" [function]
  rule stay(.) => .
  rule stay((X |-> V) E0:Map) => (weak X:Variable = V:Constant) && stay(E0)

  // Sequence Rules
  rule X := E => (once X = nil ~> once X = E)
  rule <k> once C0 => solve(C && stay(E) && C0) ...</k> <E> E </E> <C> C </C>
  rule <k> always C0 => solve(C && stay(E) && C0) </k> <E> E </E> <C> C => (C && C0) </C>
  rule S1 ; S2 => S1 ~> S2 [structural]
  rule skip ~> S2 => S2 [structural]
  rule fail ~> _  => fail [structural]
  rule <k> if E then S1 else S2 => S1 ...</k> when E ==Value #t
  rule <k> if E then S1 else S2 => S2 ...</k> when E ==Value #f
  rule <k> while E do S => S ~> while E do S ...</k> when E ==Value #t
  rule <k> while E do S => skip ...</k> when E ==Value #f
endmodule
