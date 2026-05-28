open book/chapter2/addressBook1h as Abs -- Modelo Abstracto
open book/chapter2/addressBook2e as Ref -- Modelo Concreto
open util/ordering[Adds] as Adds
open util/ordering[Dels] as Dels

------------------ Dels
sig Dels{
	toDel: set Abs/Name,
	book: one Abs/Book
}
fact DelsFinal {no Dels/last[].toDel}
fact DelsTransicion {
	all e:Dels, eˋ:next[e] |
	(some n:e.toDel|
		Abs/del[e.book,eˋ.book,n]
		and eˋ.toDel=e.toDel - n)
	or (eˋ.toDel = e.toDel and eˋ.book = e.book)
}

------------------ Adds
sig Adds{
	toAdd: set Abs/Name -> Abs/Addr,
	book: one Abs/Book
}
fact AddsFinal {no Adds/last[].toAdd}
fact AddsTransicion {
	all e:Adds, eˋ:next[e] |
	(some n:Abs/Name, a:Abs/Addr|
		n->a in e.toAdd
		and Abs/add[e.book,eˋ.book,n,a]
		and eˋ.toAdd=e.toAdd - n->a)
	or (eˋ.toAdd = e.toAdd and eˋ.book = e.book)
}

------------------ Mapeos
one sig AddrMap {
	map: Ref/Addr one -> one Abs/Addr
}{
	Abs/Addr = Ref/Addr.map
	Ref/Addr = map.Abs/Addr
}
fun ShowAddrMap[]:Ref/Addr->Abs/Addr{AddrMap.map}

one sig NameMap {
	map: Ref/Name -> Abs/Name
}{
	Abs/Name = Ref/Name.map
	Ref/Name = map.Abs/Name
    	all al: Ref/Alias | one map[al]
    	all g: Ref/Group | some map[g]
	all ab: Abs/Name | one map.ab
}
fun ShowNameMap[]:Ref/Name->Abs/Name{NameMap.map}

------------------ Alphas
fun alphaAddr[T:Ref/Target]:Abs/Addr{AddrMap.map[T]}

fun alphaName[A:Ref/Name]:Abs/Name{NameMap.map[A]}

fun alphaBook[B:Ref/Book]:Abs/Book{ // Depende de existencia
	{b:Abs/Book | 
	b.addr = (~(NameMap.map)).(^(B.addr)).(AddrMap.map)}
}

------------------ Tests para ver comportamiento
pred TestAdd {	
	some B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target,
		aB:alphaBook[B], aBˋ:alphaBook[Bˋ]|
	Ref/add[B,Bˋ,N,T] 
	and Adds/first[].book=aB
	and Adds/first[].toAdd=aBˋ.addr-aB.addr

	 // para mas placer
	some disj a,b:Adds | a.book != b.book
	some Ref/Group.(Ref/Book.addr)
	some Ref/Addr
}
//run TestAdd for 3 but 2 Ref/Book

pred TestDel {
	all disj a,b:Dels | a.book != b.book // para mas placer
	
	some B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target,
		aB:alphaBook[B], aBˋ:alphaBook[Bˋ]|
	Ref/del[B,Bˋ,N,T] 
	and Dels/first[].book=aB
	and Dels/first[].toDel=(aB.addr-aBˋ.addr).Abs/Addr
}
//run TestDel for 3 but 2 Ref/Book

------------------ Chequeamos refinamiento
assert RefinamientoAdd {
	all 	B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target,
		aB:alphaBook[B], aBˋ:alphaBook[Bˋ]|
	Ref/add[B,Bˋ,N,T] 
	and Adds/first[].book=aB
	and Adds/first[].toAdd=aBˋ.addr-aB.addr
	implies Adds/last[].book.addr=aBˋ.addr
}
//check RefinamientoAdd for 5 but 2 Ref/Book

assert RefinamientoDel {
	all 	B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target,
		aB:alphaBook[B], aBˋ:alphaBook[Bˋ]|
	Ref/del[B,Bˋ,N,T] 
	and Dels/first[].book=aB
	and Dels/first[].toDel=(aB.addr-aBˋ.addr).Abs/Addr
	implies Dels/last[].book.addr=aBˋ.addr
}
//check RefinamientoDel for 5 but 2 Ref/Book

assert RefinamientoLookup {
	all 	B:Ref/Book, N:Ref/Name,
		aB:alphaBook[B], aN:alphaName[N] |
	Abs/lookup[aB,aN] = alphaAddr[Ref/lookup[B,N]]
}
check RefinamientoLookup for 6 but 1 Ref/Book, 1 Abs/Book


