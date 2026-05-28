// No todo el comportamiento observable del Concreto
// es permitido por el abstracto, por lo que esta mal.
// pero un subconjunto del concreto si. por lo que no 
// esta la lo hecho, pero no es lo que se pide.

open book/chapter2/addressBook1h as Abs -- Modelo Abstracto
open book/chapter2/addressBook2e as Ref -- Modelo Concreto

one sig AddrMap {
	map: Ref/Addr one -> one Abs/Addr
}{
	Abs/Addr = Ref/Addr.map
	Ref/Addr = map.Abs/Addr
}
fun ShowAddrMap[]:Ref/Addr->Abs/Addr{AddrMap.map}

one sig NameMap {
	map: Ref/Alias one -> one Abs/Name
}{
	Abs/Name = Ref/Alias.map
	Ref/Alias = map.Abs/Name
}
fun ShowNameMap[]:Ref/Alias->Abs/Name{NameMap.map}

fun alphaAddr[T:Ref/Target]:Abs/Addr{AddrMap.map[T]}

fun alphaName[A:Ref/Alias]:Abs/Name{NameMap.map[A]}

fun alphaBook[B:Ref/Book]:Abs/Book{ // Depende de existencia
	{b:Abs/Book | 
	b.addr = (~(NameMap.map)).(B.addr).(AddrMap.map) }
}

assert Refinamiento {
	all 	B,Bˋ:Ref/Book, N:Ref/Alias, T:Ref/Target,
		aB:alphaBook[B], aBˋ:alphaBook[Bˋ],
		aN:alphaName[N], aT:alphaAddr[T] |
	(Ref/add[B,Bˋ,N,T] implies Abs/add[aB,aBˋ,aN,aT])
	and 
	(N->T in B.addr -- si no, el abstracto no hace nada.
	and Ref/del[B,Bˋ,N,T] implies Abs/del[aB,aBˋ,aN])
	and
	Abs/lookup[aB,aN] in
	{aA:Abs/Addr | one A:Ref/lookup[B,N] | 
	aA = alphaAddr[A]}
	-- Problema: Ref puede devolver dir de 
	-- personas en grupos las cuales no estan agendadas
}
check Refinamiento for 6 but 2 Abs/Book, 2 Ref/Book -- Anda solo refinando a Add

// ---------- Calculo auxiliar / Bocetos

pred TestAdd[	B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target,
			b,bˋ:Abs/Book, n:Abs/Name, a:Abs/Addr]{
	let	aB = alphaBook[B], aBˋ= alphaBook[Bˋ],
		aN = alphaName[N], aT = alphaAddr[T] |
	//#B.addr = 2 and #b.addr = 2 and #Bˋ.addr = 3 and 
	Ref/add[B,Bˋ,N,T] and Abs/add[aB,aBˋ,aN,aT]
	and (	aB.addr=b.addr 
		and	aBˋ.addr=bˋ.addr 
		and	aN=n 
		and 	aT=a)
}

//run TestAdd for 4 but 2 Abs/Book, 2 Ref/Book

assert RefinamientoDel {
	all 	B,Bˋ:Ref/Book, N:Ref/Alias, T:Ref/Addr,  
		bˋ:Abs/Book, aB:alphaBook[B], aBˋ:alphaBook[Bˋ],
		aN:alphaName[N] |
	Abs/del[aB,bˋ,aN] -- para ver b` por si aB`!=b`
	implies
	(N->T in B.addr -- si no, el abstracto no hace nada.
	and Ref/del[B,Bˋ,N,T] implies Abs/del[aB,aBˋ,aN])
}

//check RefinamientoDel for 6 but 3 Abs/Book, 2 Ref/Book -- No refina a Del


assert RefinamientoLookup {
	all B:Ref/Book, N:Ref/Alias,
	aB:alphaBook[B], aN:alphaName[N] |
	Abs/lookup[aB,aN] in
	{aA:Abs/Addr | 
	one A:Ref/lookup[B,N] | 
	aA = alphaAddr[A]} 
}

//check RefinamientoLookup for 3 but 1 Ref/Book, 1 Abs/Book -- No refina lookup


