abstract sig Object {
	parent : lone Dir
}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

fact unique_names {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.entries & name.n)
}

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone object.d
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Entry.object = Object - Root
}

fact one_directory_per_entry {
  // Entries must belong to exactly one a directory
  all e : Entry | one entries.e
}

fun descendants [o : Object] : set Object {
  o.^(entries.object)
}

pred reachable [o : Object] {
  o in Root + descendants[Root]
}

fact no_indirect_containment {
  // Directories cannot descend from themselves
  all d : Dir | d not in descendants[d]
}

fact parent {
	parent = ~(entries.object)
}

run Example {
	some disj r,d0,d1,d2,d3 : Dir,
	     disj e0,e1,e2,e3,e4,e5,e6,e7,e8 : Entry,
         disj f0,f1,f2,f3,f4 : File,
		 disj n0,n1,n2,n3,n4 : Name {
		Dir = r+d0+d1+d2+d3
		Root = r
		Entry = e0+e1+e2+e3+e4+e5+e6+e7+e8
		File = f0+f1+f2+f3+f4
		Name = n0+n1+n2+n3+n4
		entries = r->(e7+e8)+d3->(e0+e1+e2+e3)+d2->(e4+e5+e6)
		name = e7->n0+e8->n4+e0->n4+e1->n3+e2->n2+e3->n1+e4->n0+e5->n3+e6->n4
		object = e7->d3+e8->f4+e0->d2+e1->f2+e2->f1+e3->f0+e4->d1+e5->d0+e6->f3
	}
}
