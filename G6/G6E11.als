open book/chapter2/addressBook1h as Abs -- Modelo Abstracto
open book/chapter2/addressBook2e as Ref -- Modelo Concreto

one sig AddrMap {
	map: Ref/Addr one -> one Abs/Addr
}{
	Abs/Addr = Ref/Addr.map
	Ref/Addr = map.Abs/Addr
}
fact ShowAddrMap {some A:AddrMap.map | some A}

one sig NameMap {
	map: Ref/Name one -> one Abs/Name
}{
	Abs/Name = Ref/Name.map
	Ref/Name = map.Abs/Name
}
fact ShowNameMap {some N:NameMap.map | some N}

fun alphaAddr[T:Ref/Target]:Abs/Addr{AddrMap.map[T]}

fun alphaName[N:Ref/Name]:Abs/Name{NameMap.map[N]}

fun alphaBook[B:Ref/Book]:Abs/Book{ // Depende de existencia
	{b:Abs/Book | 
	b.addr = (~(NameMap.map)).(B.addr).(AddrMap.map) }
}

assert Refinamiento {
	all B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target|
	let	aB = alphaBook[B], aBˋ= alphaBook[Bˋ],
		aN = alphaName[N], aT = alphaAddr[T] |
	(some aB and some aBˋ) -- para que de el resultado
	implies
		(Ref/add[B,Bˋ,N,T] implies Abs/add[aB,aBˋ,aN,aT])
	//and	(Ref/del[B,Bˋ,N,T] implies Abs/del[aB,aBˋ,aN])
}

//check Refinamiento for 6 -- Anda solo refinando a Add

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
	all B,Bˋ:Ref/Book, N:Ref/Name, T:Ref/Target|
	let	aB = alphaBook[B], aBˋ= alphaBook[Bˋ],
		aN = alphaName[N]|
	(some aB and some aBˋ -- para q la f de el resultado
		and (one bˋ:Abs/Book| Ref/del[B,Bˋ,N,T]
			implies Abs/del[aB,bˋ,aN])) -- para ver bˋ
	implies
	(Ref/del[B,Bˋ,N,T] implies Abs/del[aB,aBˋ,aN])
}

check RefinamientoDel for 2 -- No refina a Del
