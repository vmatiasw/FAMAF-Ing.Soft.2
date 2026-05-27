open book/chapter2/addressBook2e

pred DosNiveles[b:Book]{
	let E = b.addr | E.E not in E and E.E.E in E.E
}
fun ShowEE[]:Name->Target{
	{n:Name, t:Target | 
	some b:Book | n->t in (b.addr).(b.addr)}
}
//run DosNiveles for 3 but 1 Book

pred HayGrupoNoVacio[b:Book]{
	some g:Group | some g.(b.addr)
}

run HayGrupoNoVacio for 2 but 1 Book
