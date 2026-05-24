sig Interprete {}
sig Cancion {}
sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	interpretes = canciones.interpretaciones
	canciones = interpretaciones.interpretes
}

assert TestConsistencia {
	all C:Catalogo |
		(all c:C.canciones | some i:C.interpretes | 
			c->i in C.interpretaciones)
		and
		(all i:C.interpretes | some c:C.canciones | 
			c->i in C.interpretaciones)
}
//check TestConsistencia for 5 but 1 Catalogo

pred Add[c,cˋ:Catalogo, i:Cancion->Interprete]{
	one i
	and cˋ.canciones = c.canciones
	and cˋ.interpretes = c.interpretes
	and cˋ.interpretaciones = c.interpretaciones + i
}
pred TestAdd {some disj c,cˋ: Catalogo, 
	i: Cancion->Interprete, 
	I,Iˋ: set Cancion->Interprete | 
		Add[c,cˋ,i] 
		and I=c.interpretaciones 
		and Iˋ=cˋ.interpretaciones
}
//run TestAdd for 4 but 2 Catalogo

pred Del[c,cˋ:Catalogo, i:Cancion->Interprete]{
	one i
	and cˋ.canciones = c.canciones
	and cˋ.interpretes = c.interpretes
	and cˋ.interpretaciones = c.interpretaciones - i
}
pred TestDel {some disj c,cˋ: Catalogo, 
	i: Cancion->Interprete, 
	I,Iˋ: set Cancion->Interprete
 | Del[c,cˋ,i] and I=c.interpretaciones and Iˋ=cˋ.interpretaciones
}
//run TestDel for 4 but 2 Catalogo

fun GroupInterpByCanc[c:Catalogo]:Interprete->Interprete{
	let I = c.interpretaciones | (~I).I
}
assert TestGroupInterpByCanc {all C:Catalogo | 
	GroupInterpByCanc[C]
	= {i1,i2:Interprete | 
		some c:Cancion | 
		c->i1 in C.interpretaciones 
		and c->i2 in C.interpretaciones}}
//check TestGroupInterpByCanc for 5

