sig Node {
	succ : one Node,
	inbox : set Node
}
fact Ring {
	all n : Node | Node in n.*succ
}

run Example1 {
	some disj n0,n1,n2,n3,n4 : Node {
		succ = n0->n3+n3->n4+n4->n1+n1->n2+n2->n0
		inbox = n0->n2+n2->(n0+n4)+n3->(n0+n3)
	}
} for 5
