open util/ordering[VSS] as V
open util/ordering[TTD] as D

-- virtual sub-sections of the track, totally ordered
sig VSS {
	ttd : one TTD
}
sig TTD {}

-- auxiliary relations
fun start : TTD -> VSS {
	{ t : TTD, v : VSS | v = min[ttd.t] }
}
fun end : TTD -> VSS {
	{ t : TTD, v : VSS | v = max[ttd.t] }
}

-- enforce total partition of the track into TDDs/VSSs
fact trackSections {
	all t : TTD | some ttd.t
	all t : TTD | ttd.t = t.start.*V/next & t.end.*V/prev
	all t:TTD-D/last | t.end.V/next = (t.D/next).start
	D/first.start = V/first
	D/last.end= V/last
}

-- trains
sig Train {
	vss : some VSS
}

-- auxiliary relations
fun front : Train -> VSS {
	{ t : Train, v : VSS | v = max[t.vss] }
}
fun rear : Train -> VSS {
	{ t : Train, v : VSS | v = min[t.vss] }
}

-- enforce no train overlap
fact trains {
	all t : Train | t.vss = t.rear.*V/next & t.front.*V/prev
	all disj t1,t2 : Train {
		some t1.vss & t2.vss
		implies t1.front = t2.rear or t1.rear = t2.front
	}
}

run Example1 {
	some disj d0,d1,d2 : TTD,
	     disj v0,v1,v2,v3,v4,v5 : VSS,
		 disj t0,t1,t2 : Train {
		TTD = d0+d1+d2
		VSS = v0+v1+v2+v3+v4+v5
		Train = t0+t1+t2
		D/next = d0->d1+d1->d2
		V/next = v0->v1+v1->v2+v2->v3+v3->v4+v4->v5
		start = d0->v0+d1->v3+d2->v5
		end = d0->v2+d1->v4+d2->v5
		front = t0->v4+t1->v4+t2->v5
		rear = t0->v2+t1->v4+t2->v4
	}
} for 3 TTD, 6 VSS, 3 Train
