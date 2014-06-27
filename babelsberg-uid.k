// The UID version of Babelsberg, with references and mutable records
// references are Int values, whereas the only included base type is
// floats. This is how we distinguish them

require "./cassowary-gateway.k"

module BABELSBERG-CONSTRAINT-SYNTAX
  syntax Constraint         ::= AtomicConstraint | "weak" AtomicConstraint
                              | Constraint "&&" Constraint [left]
                              | Constraint "||" Constraint [left]

  syntax AtomicConstraint   ::= Expression "<=" Expression [left]
                              | Expression ">=" Expression [left]
                              | Expression "=" Expression [left]
			      | Variable "==" Variable [left]
			      | Variable "=R=" Variable [left]

  syntax Expression         ::= Constant | Variable
                              | Expression "/" Expression       [strict, left]
                              | Expression "*" Expression       [strict, left]
                              > Expression "+" Expression       [strict, left]
                              > Expression "-" Expression       [strict, left]

  syntax Constant           ::= Float
  syntax Variable           ::= Id
  syntax Value              ::= Constant

  // helper to represent record fields
  syntax Variable ::= "[" Variable "," Label "]"
endmodule

module BABELSBERG-UID-SYNTAX
  imports BABELSBERG-CONSTRAINT-SYNTAX

  syntax Statement          ::= "skip"
                              | Variable ":=" Expression        [strict(2)]
                              | "always" Constraint
                              | Statement ";" Statement         [left]
			      | "unsat"
			      | Variable "." Label ":=" Expression [strict]
			      | Variable ":=" "new" Object

  syntax Expression         ::= Reference
			      | Expression "." Label            [strict, left]
			      | Object // only in K?

  syntax Label              ::= Id

  syntax Value              ::= Reference
                              | Constraint // only in K?
			      | Label // only in K?

  syntax Reference	    ::= Int

  syntax Object ::= "{" RecordExpression "}"

  // Helper
  syntax RecordExpression ::= Label ":" Expression                  [strict(2)]
                            | RecordExpression "," RecordExpression [left, seqstrict]
endmodule

module BABELSBERG-UID
  imports BABELSBERG-UID-SYNTAX
  imports CASSOWARY-GATEWAY

  syntax KResult            ::= Value

  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <H> .Map </H> // the heap
    <C> . </C> // the current constraint system
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
  </T>
  // E-Num
  // realized by including it as KResult
  // E-Var
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>
  // E-Op
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2
  // E-Field
  rule ({ L : V } . L) => V // E-Field-One
  rule ({ L : V, A } . L) => V // E-Field-First
  rule ({ X : V, A } . L) => ({ A } . L) // E-Field-Not-First
  // E-Ref
  // realized by including it as KResult

  syntax K ::= "#mapTo(" K ")" [function]
  // ToNum
  rule #mapTo(N:Constant) => N
  // ToVar
  rule #mapTo(V:Variable) => V
  // ToRef
  rule #mapTo(R:Reference) => R
  // ToArith
  rule #mapTo(E1 / E2) => #mapTo(E1) / #mapTo(E2)
  rule #mapTo(E1 * E2) => #mapTo(E1) * #mapTo(E2)
  rule #mapTo(E1 + E2) => #mapTo(E1) + #mapTo(E2)
  rule #mapTo(E1 - E2) => #mapTo(E1) - #mapTo(E2)
  // ToCompare
  rule #mapTo(E1 = E2) => #mapTo(E1) = #mapTo(E2)
  rule #mapTo(E1 <= E2) => #mapTo(E1) <= #mapTo(E2)
  rule #mapTo(E1 >= E2) => #mapTo(E1) >= #mapTo(E2)
  // ToIdentical
  rule #mapTo(X == Y) => #mapTo(X) = #mapTo(Y)
  // ToPriority
  rule #mapTo(weak C) => weak #mapTo(C)
  // ToCombine
  rule #mapTo(C1 || C2) => #mapTo(C1) || #mapTo(C2)
  rule #mapTo(C1 && C2) => #mapTo(C1) && #mapTo(C2)

  // The next two rules are special. They need to evaluate their arguments
  // before they can proceed
  // ToFieldVar
  // rule <k> #eval(R) Before #mapTo(E.L) After </k>
  //   => <k> Before [R, L] After </k>
  // rule <k> Before #mapTo(E.L) => [#mapTo(R), L] After </k>
  //   => <k> E #eval Before #mapTo(E.L) After </k>
  // ToRecEq
  // rule <k> #eval({ RecordExpression } =r= { RecordExpression }) Before #mapTo(E) After </k>
  //   => <k> Before [R, L] After </k>
  // rule <k> Before #mapTo(E.L) => [#mapTo(R), L] After </k>
  //   => <k> E #eval Before #mapTo(E.L) After </k>

  syntax Map ::= "#mapFrom" "(" Map "," Constraint ")" [function]
  // FromEmpty
  rule #mapFrom(M, .) => M
  // FromOne
  rule #mapFrom(M, V:Variable = N && C) => #mapFrom(M (V |-> N), C)
  rule #mapFrom(M, C:AtomicConstraint) => #mapFrom(M, C && .)

  syntax K ::= "#solve" "(" Constraint ")" [function]
             | "#solved" "(" Constraint ")" [function]
	     | "||=" "(" Map ")"
	     | "/||="
  // getModel (represent call to the solver)
  rule <k> #solve(C) => #solved(#getModel(#mapTo(C), Fd)) ...</k> <Cassowary> Fd </Cassowary>

  // Unsat
  rule #solved(1.0 = 2.0) => /||=

  // Solve
  rule #solved(Ec) => ||=(#mapFrom(., Ec))

  syntax AtomicConstraint ::= "#stay" "(" Map ")" [function]
  // StayEmpty
  rule #stay(.) => .
  // StayOne
  rule #stay((X |-> V) E0:Map) => (weak X = V) && #stay(E0)

  // S-Asgn
  rule <k> X := V:Expression => #solve(C && X = V && #stay(E) && #stay(H)) ~> X := V ...</k>
       <E> E </E> <H> H </H> <C> C </C>
  rule <k> ||=(Ec) ~> X := V => skip ...</k> <E> _ => Ec </E>
  // S-AsgnUnsat
  rule <k> /||= ~> X := V => unsat ...</k>

  // S-AsgnField
  rule <k> X.L := V:Expression => #solve(C && X.L = V && #stay(E) && #stay(H)) ~> X.L := V ...</k>
       <E> E </E> <H> H </H> <C> C </C>
  rule <k> ||=(Ec) ~> X.L := V => skip ...</k> <E> _ => Ec </E>
  // S-AsgnFieldUnsat
  rule <k> /||= ~> X.L := V => unsat ...</k>

  // S-AsgnNew
  rule <k> X := new { R } => #solve(C && X = size(keys(H:Map)) && #stay(E) && #stay(H:Map)) ~> X := new { R } ...</k>
       <E> E </E> <H> H </H> <C> C </C>
  rule <k> ||=(Ec) ~> X := new { R } => skip ...</k> <E> _ => Ec </E> <H> H => (H (size(H) |-> { R })) </H>
  // S-AsgnNewUnsat
  rule <k> /||= ~> X.L := V => unsat ...</k>

  // S-Always
  rule <k> always C0 => #solve(C && C0 && #stay(E) && #stay(H)) ~> always C && C0 ...</k> <E> E </E> <C> C </C>
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

  syntax Type ::= "#typeOf" "(" Expression ")" [function]
                | "#typeOf" "(" Constraint ")" [function]
  syntax Bool ::= "#typeable" "(" Type "," Type ")" [function]
  rule #typeable(Boolean, Boolean) => true:Bool
  rule #typeable(Num, Num) => true:Bool
  rule #typeable({ R }, { R }) => true:Bool

  // T-ConsOne
  rule #typeOf(C:Constraint) => Boolean
  // T-ConsMulti
  rule #typeOf(C1 || C2) => Boolean
  rule #typeOf(C1 && C2) => Boolean
  // T-Atomic
  rule #typeOf(E1 = E2) => Boolean when #typeable(#typeOf(E1), #typeOf(E2))
  rule #typeOf(E1 <= E2) => Boolean when #typeable(#typeOf(E1), #typeOf(E2))
  rule #typeOf(E1 >= E2) => Boolean when #typeable(#typeOf(E1), #typeOf(E2))
  // T-Num
  rule #typeOf(N:Constant) => Num
  // T-Arith
  rule #typeOf(E1 / E2) => Num // when (#typeOf(E1) ==String "Num") andBool (#typeOf(E2) ==String "Num")
  rule #typeOf(E1 * E2) => Num // when (#typeOf(E1) ==String "Num") andBool (#typeOf(E2) ==String "Num")
  rule #typeOf(E1 + E2) => Num // when (#typeOf(E1) ==String "Num") andBool (#typeOf(E2) ==String "Num")
  rule #typeOf(E1 - E2) => Num // when (#typeOf(E1) ==String "Num") andBool (#typeOf(E2) ==String "Num")
  // T-Rec
  //rule #typeOf({ RE }) => { #typeOf(RE) }
  //rule #typeOf(L: E) => L: #typeOf(E)
  //rule #typeOf(L: E, RE) => L: #typeOf(E), RE
  // T-Field
  //rule #typeOf({ L : V }.L) => #typeOf(V)
  //rule #typeOf({ L : V, A }.L) => #typeOf(V)
  //rule #typeOf({ X : V, A }.L) => #typeOf({A}.L)

  // ToLabel
  // rule #mapTo(L:Label) => L
  // ToRec
  // rule #mapTo(E1 = { L: E }) => #mapTo(E1) >> #mapTo(L) = #mapTo(E)
  // rule #mapTo(E1 = { L: E, R }) => (#mapTo(E1) >> #mapTo(L) = #mapTo(E)) && #mapTo(E1 = { R })
  // ToField
  // rule #mapTo(V.L) => #mapTo(V) >> #mapTo(L)

  // XXX - to string mapping should in be in cassowary-gateway.k
  // rule #printCExp(X:Id >> L:Id) => Id2String(X) +String ">>" +String Id2String(L)

  // FromField
  // rule #mapFrom(M, (V:Id >> L:Id) = N:Constant && C) => #mapFrom(M (V |-> { (L: N):RecordValue }), C)
  //      when notBool(V in keys(M))
  // rule #mapFrom(M, (V:Variable >> L:Id) = N:Constant && C) => #mapFrom(M,

  // rule #mapFrom(M, (V:Variable_L:Label) = N:Constant && C) => #mapFrom(update(M, V |-> {M[V]:RecordValue, L: N}), C)
  //     when V in keys(M)
  // TODO: support nested records

  // TODO: Update always rules with typechecks
endmodule
