open util/ordering[VSS] as V
open util/ordering[TTD] as D

-- virtual sub-sections of the track, totally ordered
sig VSS {}

-- trackside train detection sections, totally ordered
sig TTD {
	start : one VSS,		-- first VSS of the TTD
	end   : one VSS,		-- last VSS of the TTD
} { end.gte[start] }


-- enforce total partition of the track into TDDs/VSSs
fact trackSections {
	all ttd:TTD-D/last | ttd.end.V/next = (ttd.D/next).start
	D/first.start = V/first
	D/last.end= V/last
}

-- auxiliary relation for visualization
fun ttd : VSS->TTD {
	{ v : VSS, t:TTD | v in t.end.*V/prev & t.start.*V/next }
}

-- trains
sig Train {
	front : one VSS,
	rear : one VSS
} { front.gte[rear] }

-- auxiliary relation for visualization
fun vss : Train -> VSS {
	{ t : Train, v : VSS | v in t.front.*V/prev & t.rear.*V/next}
}


fact noTrainOverlap {
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
} for 3 TTD, 6 VSS, exactly 3 Train
