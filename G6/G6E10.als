open util/ordering[Estado]
open util/integer
open util/sequniv

fun Discos[]:set Int{ {i:Int | 0<=i and i<=3} }

pred Seguridad[v:seq Int]{
	all disj i, j:{n:one Int | 0<=n and n<#v}|
		i<j implies v[i] > v[j]
}

sig Estado {
	v1: seq Int,
	v2: seq Int,
	v3: seq Int
}{
	v1.elems + v2.elems + v3.elems = Discos[]
	no v1.elems&v2.elems + 
		v2.elems&v3.elems + v3.elems&v1.elems
	Seguridad[v1]
	Seguridad[v2]
	Seguridad[v3]
}

fact Estado0 {
	first[].v1.elems = Discos[]
}

pred Objetivo[e:Estado]{e.v3.elems = Discos[]}

fact EstadosDistintos {
	all disj e,eˋ:Estado | 
	(e.v1=eˋ.v1 and e.v2=eˋ.v2 and e.v3=eˋ.v3)
	implies Objetivo[e]
}

fact EstadoFinal {
	Objetivo[last[]]
}

pred Movimiento[I, Iˋ,F,Fˋ:seq Int]{
		Iˋ=I.delete[lastIdx[I]]
	and 	Fˋ=F.add[last[I]]
	and	one (I.elems&Fˋ.elems)
}

fact Transicion {
	all e:Estado, eˋ:next[e] |
	Objetivo[e]
	implies Objetivo[eˋ]
	else	Movimiento[e.v1,eˋ.v1,e.v2,eˋ.v2]
	or 	Movimiento[e.v1,eˋ.v1,e.v3,eˋ.v3]
	or 	Movimiento[e.v2,eˋ.v2,e.v1,eˋ.v1]
	or 	Movimiento[e.v2,eˋ.v2,e.v3,eˋ.v3]
	or 	Movimiento[e.v3,eˋ.v3,e.v1,eˋ.v1]
	or 	Movimiento[e.v3,eˋ.v3,e.v2,eˋ.v2]
}

run {} for 16
