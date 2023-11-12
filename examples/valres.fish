let f = ref(\ x . x) in
(f := \ x . x + 1);
!f(true)