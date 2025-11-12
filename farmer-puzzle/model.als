abstract sig Object { eats: set Object }
one sig Farmer, Fox, Chicken, Grain extends Object {}

sig near, far in Object {}

fact eating { eats = Fox->Chicken + Chicken->Grain }

fact noclones { Object = near + far }

run Example1 {
	near = Farmer+Fox+Chicken
	far  = Grain
}
