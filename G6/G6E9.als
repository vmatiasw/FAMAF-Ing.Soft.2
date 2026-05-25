open util/integer
open util/ordering[Estado]

abstract sig Elem {}
abstract sig Persona extends Elem {tiempo: one Int}
one sig Indiana, Padre, Novia, Suegro extends Persona {}
one sig Linterna extends Elem {}

fact Velocidades {
	Indiana.tiempo = 5
	Padre.tiempo = 20
	Novia.tiempo = 10
	Suegro.tiempo = 25
}

sig Estado {
	origen: set Elem,
	destino: set Elem,
	tiempoAcumulado: one Int
}{
	origen + destino = Elem
	no origen & destino
}

fact Estado0 {
	let e0 = first[] | 
	e0.origen = Elem and e0.tiempoAcumulado = 0
}

fact EstadoFinal {
	let ef = last[] |
	ef.destino = Elem and ef.tiempoAcumulado <= 60
}

pred Movimiento[I, Iˋ,F,Fˋ:set Elem, t,tˋ:Int]{
	let M = I&Fˋ|
		some M
	and 	Iˋ=I-M
	and	Fˋ=F+M
	and 	Linterna in M
	and  some M&Persona
	and 	#(M&Persona) <=2
	and	tˋ= add[t, max[(Persona&M).tiempo]]
}

fact Transicion {
	all e:Estado, eˋ:next[e] |
	let 	O=e.origen, 		   Oˋ=eˋ.origen, 
		D=e.destino, 		   Dˋ=eˋ.destino,
		t=e.tiempoAcumulado, tˋ=eˋ.tiempoAcumulado |
		(t=tˋ and O=Oˋ and D=Dˋ)
	or	Movimiento[O,Oˋ,D,Dˋ,t,tˋ]
	or	Movimiento[D,Dˋ,O,Oˋ,t,tˋ]
}


run {} for 6 but 7 Int
