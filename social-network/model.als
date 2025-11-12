sig User {
	follows : set User,
	posts : set Photo,
	sees : set Photo
}

sig Photo {}

fact follows {
	no follows & iden
}

fact sees {
	sees in follows.posts
}

run Example1 {
	some disj a,b,c,d,e : User,
		 disj x,y,z,w,v : Photo {
		User = a+b+c+d+e
		follows = a->c+b->a+b->c+c->b-d->e+e->d
		Photo = x+y+z+w+v
		posts = b->(z+w)+c->v+d->(x+y)
		sees = a->v+b->v+c->(z+w)+e->x
	}
} for 5
