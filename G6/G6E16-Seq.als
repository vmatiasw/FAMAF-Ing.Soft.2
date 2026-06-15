open util/ordering[Index]
sig Index, Elem{}

sig Seq {
    elems: Index -> lone Elem
}{
	let I = elems.Elem | I.^prev in I
}

pred add[s,sˋ:Seq,i:Index,e:Elem]{
let E = s.elems, Eˋ=sˋ.elems, I=E.Elem, 
Max = {j :I | no (I & j.nexts)}{	
	(some E[i.prev]) implies Eˋ[i] = e
	(some i.prev and no E[i.prev]) implies Eˋ[Max.next] = e // 
	// si es mas alla del ultimo, se agrega al final
	(no i.prev) implies Eˋ[i] = e
	all j: Index {
        	j in i.prevs implies Eˋ[j] = E[j]
		j in i.nexts implies Eˋ[j] = E[j.prev]
		// Obs: no existe j.prev = last[] ni last[].next
	}	
	//#Eˋ = #E +1 // invariante para 
	//solucionar falsos positivos por problemas de cota
}}
//run add for 2

pred del[s,sˋ:Seq,i:Index]{
let E = s.elems, Eˋ=sˋ.elems {
	all j: Index {
        	j in i.prevs implies Eˋ[j] = E[j]
		(j = i or j in i.nexts) implies Eˋ[j] = E[j.next]
	}
}}
//run del for 2

assert InversaDelAdd{all s,sˋ:Seq, i:Index, e:Elem | 
		add[s,sˋ,i,e] implies del[sˋ,s,i]}
//check InversaDelAdd for 3 // c.ej espurio por la cota.
// No tiene solucion finita, siempre tendra el problema en el 
// limite. se puede acotar algo mas el antecedente:
assert InversaDelAddCorregido{all s,sˋ:Seq, i:Index, e:Elem |
		no s.elems[last[]] implies //Hay idx disponible
		add[s,sˋ,i,e] implies del[sˋ,s,i]}
//check InversaDelAddCorregido for 3
// No necesita accioma generador. Mas bien uno de capacidad.

assert AddTotal {
    all s:Seq, i:Index, e:Elem |
        some sˋ:Seq |
            add[s,sˋ,i,e]
}
check AddTotal for 2 //deberia fallar solo porque no existe sˋ
// debido a la cota. y este problema tampoco puede solucionarse de 
// forma finita con axiomas de generacion.
