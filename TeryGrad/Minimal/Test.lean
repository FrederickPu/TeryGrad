import TeryGrad.Minimal.Types

#check 2::[]
#eval ((1::(NArray.nil []))::(NArray.nil _) : NArray Nat [1, 1])

#eval (N[] : NArray Nat [0])
#check N[N[N[1, 2], N[3, 4], N[5, 6]], N[N[1, 2], N[3, 4], N[5, 6]]]

#eval N[N[1], N[2]] * N[N[1], N[2]]
#eval N[N[N[1, 2], N[3, 4], N[5, 6]], N[N[1, 2], N[3, 4], N[5, 6]]] + N[N[N[1, 2], N[3, 4], N[5, 6]], N[N[1, 2], N[3, 4], N[5, 6]]]
