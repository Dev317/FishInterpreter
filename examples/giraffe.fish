let swap = \ x . (snd(x), fst(x)) in
let res1 = swap(42,17) in 

let fact = rec fact(n) .
  if (n == 0) then 1
  else n * fact(n - 1)
in
let res2 = fact(5) in

let power = rec power(input) .
  let x = fst(input) in
  let n = snd(input) in
  if (n == 0) then 1
  else x * power(x,n-1)
in
let res3 = power(2,10) in

let sameLastChar = \ input .
  let s1 = fst(input) in
  let s2 = snd(input) in
  index(s1,length(s1)-1) == index(s2,length(s2)-1)
in
let res4 = sameLastChar("abcz","abcdefghijklmnopqrstuvwxyz") in 


let slice = rec slice(input) .
  let s = fst(input) in
  let p = snd(input) in
  let base = fst(p) in
  let len = snd(p) in
  if (len == 0) then ""
  else concat(index(s,base), slice (s,(base + 1, len - 1)))
in
let res5 = slice("abcdefghijklmnopqrstuvwxyz", (10, 10)) in 

let comment = "Assumes nonnegative arguments" in
let lessthanorequal = rec lessthanorequal(nm) .
  let n = fst(nm) in
  let m = snd(nm) in
  if (n == 0) then true 
  else if (m == 0) then false
  else lessthanorequal(n-1,m-1)
in
let res6 = (lessthanorequal(5,6), lessthanorequal(6,5)) in 

< res1 = res1
, res2 = res2
, res3 = res3
, res4 = res4
, res5 = res5
, res6 = res6 >