sig Elem {}
sig Rel {
	el: set Elem,
	re: set el->el
}

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

pred ConMinimo[r:Rel]{some n:r.el | EsMinimo[r, n]}
pred EsMinimo[r:Rel, m:Elem]{all n:r.el | m->n in r.re}
pred ConMaximo[r:Rel]{some n:r.el | EsMaximo[r, n]}
pred EsMaximo[r:Rel, m:Elem]{all n:r.el | n->m in r.re}

assert T1 {all r: Rel | OrdenParcial[r] implies OrdenTotal[r]}
//check T1 for 5 //falla

assert T2 {all r: Rel | OrdenParcial[r] implies ConMinimo[r]}
//check T2 for 3 //falla

assert T3 {all r: Rel | some n:r.el, m:r.el | 
	OrdenParcial[r] and EsMinimo[r, n] and EsMaximo[r, m]
	implies n != m}
//check T3 for 3 //falla

assert T4 {all r, t:Rel |
	OrdenEstricto[r] and OrdenEstricto[t]
	implies OrdenEstricto[r+t]}
//check T4 for 2 // falla

assert T5 {all r, t:Rel |
	OrdenEstricto[r] and OrdenEstricto[t]
	implies OrdenEstricto[r.t]}
check T5 for 2
