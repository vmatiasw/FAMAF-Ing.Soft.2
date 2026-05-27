sig Nodo {}

pred Aciclico[E:Nodo->Nodo]{
	(^E)&iden = none->none
}

pred NoCompartenHijos[E:Nodo->Nodo]{
	all disj p1, p2:Nodo | p1->p2 not in E.(~E)
}

assert DerivacionNoCompartenHijos {
	all E:Nodo->Nodo |
		NoCompartenHijos[E]
	iff	E.(~E) in iden
}
//check DerivacionNoCompartenHijos for 6 -- correcta

pred TieneRaiz[E:Nodo->Nodo]{
	one r:Nodo | all n:Nodo | r->n in *E
}

pred AncestroComun[E:Nodo->Nodo]{
	all n,m:Nodo | some a:Nodo | a->n in *E and a->m in *E
}
assert DerivacionAncestroComun{
	all E:Nodo->Nodo |
		AncestroComun[E]
	iff	all n,m:Nodo | n->m in (~*E).*E
	iff	Nodo->Nodo in (~*E).*E
}
//check DerivacionAncestroComun for 6 -- correcta

pred EsArbol[E:Nodo->Nodo]{
	Aciclico[E] and NoCompartenHijos[E] and TieneRaiz[E]
}

assert EsArbol2{
	all E:Nodo->Nodo | 
		EsArbol[E] iff 	
		(Aciclico[E]
		and NoCompartenHijos[E] 
		and AncestroComun[E]) }
//check EsArbol2 for 6

// check {all E:Nodo->Nodo | TieneRaiz[E] implies AncestroComun[E]} -- no vale la vuelta

one sig Arbol {E: set Nodo -> Nodo}{EsArbol[E]}

//run {} for 6
