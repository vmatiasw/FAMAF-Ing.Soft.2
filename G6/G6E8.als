open util/ordering[Estado]

abstract sig Elem {}
one sig Bote extends Elem {}

abstract sig Persona extends Elem {}
abstract sig Adulto extends Persona {}
abstract sig Peque extends Persona {}
abstract sig Nene, Nena extends Peque {}
one sig Criminal extends Peque {}
one sig Nene1, Nene2 extends Nene {}
one sig Nena1, Nena2 extends Nena {}
one sig Policia, Madre, Padre extends Adulto {}

pred OrillaSegura[O:set Elem]{
		((some (Nena & O) and Padre in O)
		implies Madre in O)
	and 	((some (Nene & O) and Madre in O)
		implies Padre in O)
	and 	((#(Persona&O) > 1 and Criminal in O) 
		implies Policia in O)
}

sig Estado {
	destino: set Elem,
	origen: set Elem
}{
	destino + origen = Elem
	no origen & destino
	OrillaSegura[origen]
	OrillaSegura[destino]
}

fact Estado0 {
	let e0 = first[] | e0.origen = Elem
}

fact EstadoFinal {
	let ef = last[] | ef.destino = Elem
}

pred Mover[I, Iˋ,F,Fˋ:set Elem]{
	let M = I&Fˋ | 
		Iˋ=I-M
		and Fˋ=F+M 
		and  #(M&Adulto) >=1
		and #(M&Persona) <=2
}

fact Transicion {
	all e:Estado, eˋ:next[e] |
	let O = e.origen, Oˋ= eˋ.origen, 
	D=e.destino, Dˋ=eˋ.destino |
		(Bote in ((O&Oˋ)+(D&Dˋ)) 
		implies (O=Oˋ and D=Dˋ))
	and 	(Bote in O&Dˋ implies Mover[O,Oˋ,D,Dˋ])
	and 	(Bote in D&Oˋ implies Mover[D,Dˋ,O,Oˋ])
}

run {} for 30
