// ESTA BIEN PERO MAL!!, osea la estructura del Grafo deberia ser como la del SubGrafo

sig Nodo {}
sig Grafo {aristas: set Nodo->Nodo}{some aristas}
fact {one Grafo}
sig SubGrafo {
	nodos: set Nodo,
	aristas: nodos->nodos
}{some aristas}

pred Aciclico {
	all g:Grafo, n:Nodo | 
		n->n not in *(g.aristas)
}

pred NoDirigido {
	all g:Grafo, disj n,m:Nodo |
		n->m in g.aristas 
		implies m->n in g.aristas
}

pred FuertementeConexo {
	all g:Grafo, disj n,m:Nodo |
		n->m in ^(g.aristas)
		and m->n in ^(g.aristas)
}

pred ConUnaComponenteFuertementeConexa {
	all g:Grafo | some s:SubGrafo | 
	s.aristas in g.aristas
	and ComponenteFuertementeConexa[s]
}
pred ComponenteFuertementeConexa[s:SubGrafo] {
	all disj n,m:s.nodos |
	n->m in ^(s.aristas)
	and m->n in ^(s.aristas)
}

pred Conexo {
	all g:Grafo, disj n,m:Nodo |
	n->m in ^(g.aristas+~(g.aristas))
}

pred ConUnaComponenteConexa {
	all g:Grafo | some s:SubGrafo | 
	s.aristas in g.aristas
	and ComponenteConexa[s]
}
pred ComponenteConexa[s:SubGrafo] {
	all disj n,m:s.nodos |
	n->m in ^(s.aristas+~(s.aristas))
}

assert Test1 {
	FuertementeConexo
	implies not Aciclico
}
//check Test1 for 4

assert Test2 {
	FuertementeConexo
	implies (not Aciclico and Conexo)
}
//check Test2 for 4

assert Test3 {
	Conexo //FuertementeConexo
	and NoDirigido
	implies not Aciclico
}
//check Test3 for 4

assert Test4 {
	ConUnaComponenteFuertementeConexa
	implies ConUnaComponenteConexa
}
//check Test4 for 4

assert Test5 {
	ConUnaComponenteFuertementeConexa
	implies not Aciclico
}
//check Test5 for 4

assert Test6 {
	Conexo
	implies ConUnaComponenteConexa
}
check Test6 for 4 // por que da error?

