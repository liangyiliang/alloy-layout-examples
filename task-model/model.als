abstract sig Task {}
sig Atomic extends Task {}
sig Composite extends Task {
	subtasks : seq Task
}
one sig Root in Task {}

// Derived parent relationship
fun parent : Task -> Task {
	{ a,b : Task | a in elems[b.subtasks] }	
}

// Derived successor relationship between sibling tasks
fun succ : Task -> Task {
	{ x, y : Task | some p : Task | x+y in elems[p.subtasks] and idxOf[p.subtasks,y] = idxOf[p.subtasks,x].next }
}


fact Tree {
	no Root.parent
	all t : Task-Root | one t.parent
	all t : Task | t not in t.^parent
}

fact Composite {
	all t : Composite | not lone elems[t.subtasks] and not hasDups[t.subtasks]
}


run Example1 {
	some disj c0,c1,c2 : Composite,
	     disj a0,a1,a2,a3,a4,a5,a6 : Atomic {
			Root = c0
			parent = (c1+c2+a6)->c0+(a0+a1+a2+a3)->c1+(a4+a5)->c2
			succ = c1->c2+c2->a6+a0->a1+a1->a2+a2->a3+a4->a5
	}
} for exactly 10 Task
