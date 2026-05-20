sig Elem {}
sig Rel {
	el: set Elem,
	re: set el->el
}

fact {one Rel and all r:Rel | 3 <= #r.el}

pred Reflexiva[r:Rel]{all e:r.el | e->e in r.re}

pred Transitiva[r:Rel]{
	all e, m, n:r.el | 
		e->m in r.re
		and m->n in r.re
		implies e->n in r.re
}
pred Antisimetrica[r:Rel]{
	all disj e, m:r.el | 
		not (e->m in r.re and m->e in r.re)
}

pred PreOrden[r:Rel]{Reflexiva[r] and Transitiva[r]}

pred OrdenParcial[r:Rel]{PreOrden[r] and Antisimetrica[r]}

pred OrdenTotal[r:Rel]{
	OrdenParcial[r] and
	all e, m:r.el | e->m in r.re or m->e in r.re
}

pred OrdenEstricto[r:Rel]{
	Transitiva[r] and Antisimetrica[r]
	and all n:r.el | n->n not in r.re
}

pred ConMinimo[r:Rel]{some n:r.el | all m:r.el | n->m in r.re}

pred ConMaximo[r:Rel]{some n:r.el | all m:r.el | m->n in r.re}

assert T1 {all r: Rel | OrdenParcial[r] implies OrdenTotal[r]}
//check T1 for 5 //falla

assert T2 {all r: Rel | Antisimetrica[r] and OrdenParcial[r] implies ConMinimo[r]}
check T2 for 3 //falla
