sig Workstation {
	workers : some Worker,
	succ : set Workstation
}
one sig Begin, End in Workstation {}

abstract sig Worker {}

abstract sig Product {}
sig Material extends Product {}
sig Component extends Product {
	parts : some Product,
	workstation : one Workstation
}

fact {
	// Every worker works in one workstation
	workers in Workstation one -> Worker
	
	// Components cannot be their own parts
	all c : Component | c not in c.^parts

	// The workstations form a single line between begin and end
	all w : Workstation - End | one w.succ
	no End.succ
	Workstation in Begin.*succ

	// The parts of a component must be assembled before it in the production line
	all c : Component, d : c.^parts & Component | c.workstation in d.workstation.^succ
}

run Example1 {
	some disj w0,w1,w2,w3 : Workstation,
		 disj c0,c1,c2,c3 : Component,
		 disj m0,m1 : Material,
		 disj r0,r1,r2,r3,h0,h1,h2 : Worker {
		Workstation = w0+w1+w2+w3
		Component = c0+c1+c2+c3
		Material = m0+m1
		Worker = r0+r1+r2+r3+h0+h1+h2
		Begin = w0
		End = w3
		succ = w0->w1+w1->w2+w2->w3
		workers = w0->(r0+r1+r2)+w1->h0+w2->(h1+h2)+w3->r3
		workstation = (c0+c1)->w3+c2->w2+c3->w0
		parts = c0->c3+c1->(c2+c3)+c2->(m0+m1)+c3->m0
	}
} for 7

