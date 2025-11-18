open util/graph[Philosopher]

-- a philosopher has a fork and another philosopher on either side
sig Philosopher {
  disj leftFork, rightFork: one Fork
}

-- a fork
sig Fork {}

fun leftPhil : Philosopher -> Philosopher {
	leftFork.~rightFork
}

fun rightPhil : Philosopher -> Philosopher {
	rightFork.~leftFork
}

-- a fact that describes the  table setting
fact setTheTable {
  ring[leftPhil]
  all f: Fork {
    lone p: Philosopher | p.leftFork = f
    lone p: Philosopher | p.rightFork = f
  }
}


run Example1 {} for exactly 5 Philosopher, exactly 6 Fork
