open util/ordering[Book]
open book/chapter2/addressBook2e

fact Transicion {
	all b:Book, bˋ:next[b]|
	(some  n:Name, t:Target | add[b,bˋ,n,t])
	// or (some  n:Name, t:Target | del[b,bˋ,n,t]) -- no preserva
	or b.addr = bˋ.addr //caso lookup[b,n]
}

assert SiempreCorresponde {
	all b:Book,  bˋ:next[b], n:Name, a:Addr |
	a in lookup[b,n] implies a in lookup[bˋ,n]
	//n->a in b.addr implies n->a in bˋ.addr -- no es lo mismo
}
check SiempreCorresponde for 6
