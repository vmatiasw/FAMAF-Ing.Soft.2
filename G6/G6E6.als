sig Nodo, Etiqueta {}

fun Caminos(t:Nodo->Etiqueta->Nodo):Nodo->Nodo{
	{n,m:Nodo | some e:Etiqueta | n->e->m in t}
}

sig lts {
	nodos: set Nodo,
	n0: one nodos,
	etiquetas: set Etiqueta,
	transiciones: set nodos->etiquetas->nodos
}{all m:nodos | n0->m in ^(Caminos[transiciones])}
