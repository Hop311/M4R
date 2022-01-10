
import M4R.Matsumura

open M4R

#eval (Finset.range 10).length

#eval ∑ x in (Finset.range 10).toInt, (3 : Int)
#eval ∏ x in (Finset.range 3).toInt, x + (1 : Int)

#eval ∑ Int.ofNat in (Finset.range 10)
#eval ∑ (fun x => Int.ofNat x.fst* x.snd) in (Finset.antidiagonal 7)
