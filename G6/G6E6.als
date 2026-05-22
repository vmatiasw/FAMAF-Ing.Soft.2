sig Nodo, Etiqueta {}
sig Tau extends Etiqueta {}{lone Tau}

fun Caminos(t:Nodo->Etiqueta->Nodo):Nodo->Nodo{
	{n,m:Nodo | some e:Etiqueta | n->e->m in t}
}

sig LTS {
	nodos: set Nodo,
	n0: one nodos,
	etiquetas: set Etiqueta,
	transiciones: set nodos->etiquetas->nodos
}{all m:nodos | n0->m in ^(Caminos[transiciones])}

pred Bisimulacion[S,T:LTS, R:Nodo->Nodo]{
	Simulacion[S,T,R] and Simulacion[T,S,~R]
}

fun CaminosDebiles[T:LTS]:Nodo->Nodo {
	{s,sˋ:Nodo | some tau:Tau | 
	s->tau->sˋ in T.transiciones}}

pred TransicionDebil[T:LTS,t,tˋ:Nodo,a:Etiqueta]{
	(some tt,ttˋ:Nodo |
			t->tt in *(CaminosDebiles[T])
			and tt->a->ttˋ in T.transiciones
			and ttˋ->tˋ in *(CaminosDebiles[T]))
	or some tau:Tau | a = tau 
		and t->tˋ in *(CaminosDebiles[T])
}

pred SimulacionDebil[S,T:LTS, R:Nodo->Nodo]{
	all a:Etiqueta, s,t, sˋ:Nodo | 
		s->t in R and s->a->sˋ in S.transiciones
		implies some tˋ:Nodo | 
			TransicionDebil[T,t,tˋ,a] and sˋ->tˋ in R
}

pred Simulacion[S,T:LTS, R:Nodo->Nodo]{
	all a:Etiqueta, s,t, sˋ:Nodo | 
		s->t in R and s->a->sˋ in S.transiciones
		implies some tˋ:Nodo | 
			t->a->tˋ in T.transiciones and sˋ->tˋ in R
}

assert Ttran{all T:LTS, t,tˋ:Nodo, a:Etiqueta | 
	t->a->tˋ in T.transiciones implies TransicionDebil[T,t,tˋ,a]}
//check Ttran for 4

pred BisimulacionDebil[S,T:LTS, R:Nodo->Nodo]{
	SimulacionDebil[S,T,R] and SimulacionDebil[T,S,~R]
}

assert T1 {all S,T:LTS, R:Nodo->Nodo | 
	Bisimulacion[S,T,R] implies Simulacion[S,T,R]}
//check T1 for 4

assert T2 {all S,T:LTS, R:Nodo->Nodo | 
	Bisimulacion[S,T,R] implies BisimulacionDebil[S,T,R]}
//check T2 for 4

assert T4 {all S,T:LTS, R:Nodo->Nodo |
	Simulacion[S,T,R] implies SimulacionDebil[S,T,R]}
//check T4 for 2

assert T3a {all S,T:LTS, R,Rˋ:Nodo->Nodo | 
	Simulacion[S,T,R] 
	and Simulacion[S,T,Rˋ]
	implies Simulacion[S,T,R.Rˋ] }
check T3a for 4

assert T3b {all S,T:LTS, R,Rˋ:Nodo->Nodo | 
	SimulacionDebil[S,T,R] 
	and SimulacionDebil[S,T,Rˋ]
	implies SimulacionDebil[S,T,R.Rˋ] }
//check T3b for 4

assert T3c {all S,T:LTS, R,Rˋ:Nodo->Nodo | 
	Bisimulacion[S,T,R] 
	and Bisimulacion[S,T,Rˋ]
	implies Bisimulacion[S,T,R.Rˋ] }
//check T3c for 4

assert T3d {all S,T:LTS, R,Rˋ:Nodo->Nodo | 
	BisimulacionDebil[S,T,R] 
	and BisimulacionDebil[S,T,Rˋ]
	implies BisimulacionDebil[S,T,R.Rˋ] }
//check T3d for 2

run { some disj S,T:LTS, 
		R: S.nodos->T.nodos, 
		Strans, Ttrans:Nodo->Etiqueta->Nodo |
	//Simulacion[S,T,R]
	//Bisimulacion[S,T,R]
	SimulacionDebil[S,T,R] and not Simulacion[S,T,R]
	and Strans = S.transiciones
	and Ttrans = T.transiciones
	and no T.nodos & S.nodos
	and #T.nodos = 4
	and #T.etiquetas = 2
	and #T.transiciones = 5
	and #S.nodos = 3
	and #T.transiciones = 5
	and #S.etiquetas = 2
	and #R <= 5
} for 3 but 7 Nodo
