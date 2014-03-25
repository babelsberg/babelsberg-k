require "./babelsberg-int.k"

module BABELSBERG-RECORDS-SYNTAX
  imports BABELSBERG-INT-SYNTAX

  syntax Label      ::= Id

  syntax RecordExpression ::= Label ":" Expression                  [strict(2)]
                            | RecordExpression "," RecordExpression [left, seqstrict]
  syntax Expression  ::= "{" RecordExpression "}"                   [strict]
                       | Expression "." Label                       [left, strict(1)]

  syntax RecordValue      ::= Label ":" Value                       [strict(2)]
                            | RecordValue "," RecordValue           [left, seqstrict]
  syntax Value      ::= "{" RecordValue "}"

  syntax RecordType ::= Label ":" Type
                      | RecordType "," RecordType [left]
  syntax Type       ::= "Num" | "Boolean" | "{" RecordType "}"
endmodule

module BABELSBERG-CONSTRAINT-SYNTAX
  imports BABELSBERG-INT-SYNTAX // identical
  syntax Variable ::= Variable ">>" Id // to represent record fields
endmodule

module BABELSBERG-RECORDS
  imports BABELSBERG-INT
  imports BABELSBERG-RECORDS-SYNTAX

  // E-Rec
  // realized by [strict] annotation above
  // E-Field
  rule ({ L : V } . L) => V // E-Field-One
  rule ({ L : V, A } . L) => V // E-Field-First
  rule ({ X : V, A } . L) => ({ A } . L) // E-Field-Not-First

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
  rule #typeOf(N:Number) => Num
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
  // rule #mapFrom(M, (V:Id >> L:Id) = N:Number && C) => #mapFrom(M (V |-> { (L: N):RecordValue }), C)
  //      when notBool(V in keys(M))
  // rule #mapFrom(M, (V:Variable >> L:Id) = N:Number && C) => #mapFrom(M,

  // rule #mapFrom(M, (V:Variable_L:Label) = N:Number && C) => #mapFrom(update(M, V |-> {M[V]:RecordValue, L: N}), C)
  //     when V in keys(M)
  // TODO: support nested records

  // TODO: Update always rules with typechecks
endmodule

