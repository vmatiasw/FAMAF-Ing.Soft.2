sig Elem{}

sig Set{E:set Elem}

pred union[s,sˋ,u:Set]{
	u.E = s.E + sˋ.E
}

assert TestUnion{all s,sˋ:Set| some u:Set | union[s,sˋ,u]}
check TestUnion for 8
// Requiere el siguiente axioma de generacion para andar:
//fact SetGenerator {
//	some s:Set | no s.E
//	all s:Set, e:Elem | some sˋ:Set | sˋ.E = s.E +e
//}
