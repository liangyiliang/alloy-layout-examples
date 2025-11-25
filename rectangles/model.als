open util/ordering[Coordinate]

sig Coordinate {}

sig Rectangle {
	xs : some Coordinate,
	ys : some Coordinate
}

fact Positions {
	// Non-overlaping
	all disj a,b : Rectangle | no a.xs & b.xs or no a.ys & b.ys
	// Contiguous
	all a : Rectangle, disj x1,x2 : a.xs | x1.nexts & x2.prevs in a.xs
	all a : Rectangle, disj y1,y2 : a.ys | y1.nexts & y2.prevs in a.ys
}

run Example1 {
	some disj a,b : Rectangle,
		 disj p0,p1,p2 : Coordinate {
		Rectangle = a+b
		Coordinate = p0+p1+p2
		xs = a->Coordinate + b->(p1+p2)
		ys = a->p0 + b->(p1+p2)
	}
} for 3 Coordinate, 2 Rectangle
