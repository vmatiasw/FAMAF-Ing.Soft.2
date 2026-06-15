sig Elem{}

sig Bag{E:Elem -> one {i:Int|i>=0}}{Elem = E.Int}

pred union[b,bˋ,u:Bag]{
	all e:Elem | u.E[e] = b.E[e] + bˋ.E[e]
}

assert TestUnion{all b,bˋ:Bag| some u:Bag | union[b,bˋ,u]}
check TestUnion for 8
// Requiere el siguiente axioma de generacion para andar:
fact BagGenerator {
	some b:Bag | b.E[Elem] = 0
	all b:Bag, e:Elem | some bˋ:Bag | bˋ.E = b.E + e->(b.E[e]+1)
}
