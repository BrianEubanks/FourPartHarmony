

one sig Staff {
  head: one Note
}



sig Note {
  s: one Int,
  a: one Int,
  t: one Int,
  b: one Int,
  next: lone Note
}

//
// Set of Possible notes 1 - 11
//
pred irange(n:Int) {
   n = {0} or
                   n = {1} or
                  n = {2} or
                   n = {3} or
                   n = {4} or
                   n = {5} or
                   n = {6} or
                   n = {7} or
                   n = {8} or
                   n = {9} or
                  n = {10} or
                   n = {11}
}
fact prange {
  all n: Note | irange[n.s] and irange[n.a] and irange[n.t] and irange[n.b]
}



//
// Set of Triads 
//   Double root
//   Root in Bass
//
// Positions of perspective T,A,S. Ignoring Bass, 
// n4 = B, n1 = S
//
pred triad[n4,n3,n2,n1: Int] {
// 1st Position 
/*                          (n1 = {0} and n2 = {2} and n3 = {4} and n4 = {7}) or
                          (n1 = {1} and n2 = {3} and n3 = {5} and n4 = {8}) or
                          (n1 = {2} and n2 = {4} and n3 = {6} and n4 = {9}) or
                          (n1 = {3} and n2 = {5} and n3 = {7} and n4 = {10}) or
                          (n1 = {4} and n2 = {6} and n3 = {8} and n4 = {11}) or
                          (n1 = {5} and n2 = {7} and n3 = {9} and n4 = {5}) or
                          (n1 = {6} and n2 = {8} and n3 = {10} and n4 = {6}) or

                          (n1 = {0} and n2 = {9} and n3 = {11} and n4 = {7}) or
                          (n1 = {1} and n2 = {10} and n3 = {5} and n4 = {8}) or
                          (n1 = {2} and n2 = {11} and n3 = {6} and n4 = {9}) or
                          (n1 = {3} and n2 = {5} and n3 = {7} and n4 = {10}) or
                          (n1 = {4} and n2 = {6} and n3 = {8} and n4 = {11}) or
*/
// 2nd Position
                          (n1 = {0} and n2 = {2} and n3 = {4} and n4 = {7}) or
                          (n1 = {1} and n2 = {3} and n3 = {5} and n4 = {8}) or
                          (n1 = {2} and n2 = {4} and n3 = {6} and n4 = {9}) or
                          (n1 = {3} and n2 = {5} and n3 = {7} and n4 = {10}) or
                          (n1 = {4} and n2 = {6} and n3 = {8} and n4 = {11}) or
                          (n1 = {5} and n2 = {7} and n3 = {9} and n4 = {5}) or
                          (n1 = {6} and n2 = {8} and n3 = {10} and n4 = {6}) or

                          (n1 = {0} and n2 = {9} and n3 = {11} and n4 = {7}) or
                          (n1 = {1} and n2 = {10} and n3 = {5} and n4 = {8}) or
                          (n1 = {2} and n2 = {11} and n3 = {6} and n4 = {9}) or
                          (n1 = {3} and n2 = {5} and n3 = {7} and n4 = {10}) or
                          (n1 = {4} and n2 = {6} and n3 = {8} and n4 = {11}) or
// 3rd Position
                          (n1 = {0} and n2 = {4} and n3 = {7} and n4 = {2}) or
                          (n1 = {1} and n2 = {5} and n3 = {8} and n4 = {3}) or
                          (n1 = {2} and n2 = {6} and n3 = {9} and n4 = {4}) or
                          (n1 = {3} and n2 = {7} and n3 = {10} and n4 = {5}) or
                          (n1 = {4} and n2 = {8} and n3 = {11} and n4 = {6}) or
                          (n1 = {5} and n2 = {9} and n3 = {5} and n4 = {7}) or
                          (n1 = {6} and n2 = {10} and n3 = {6} and n4 = {8}) or

                          (n1 = {0} and n2 = {11} and n3 = {7} and n4 = {9}) or
                          (n1 = {1} and n2 = {5} and n3 = {8} and n4 = {10}) or
                          (n1 = {2} and n2 = {6} and n3 = {9} and n4 = {11}) or
                          (n1 = {3} and n2 = {7} and n3 = {10} and n4 = {5}) or
                          (n1 = {4} and n2 = {8} and n3 = {11} and n4 = {6}) 
}

pred allTriad{
  all n: Note | triad[n.s,n.a,n.t,n.b]
}


//
// Set of 5ths for Parallel 5ths
//
pred ser5[n1,n2: Int] {
  (n1 = {0} and n2 = {4} ) or
                          (n1 = {1} and n2 = {5} ) or
                          (n1 = {2} and n2 = {6} ) or
                          (n1 = {3} and n2 = {7} ) or
                          (n1 = {4} and n2 = {8} ) or
                          (n1 = {5} and n2 = {9} ) or
                          (n1 = {6} and n2 = {10} ) or
                          (n1 = {7} and n2 = {11} ) or
                          (n1 = {8} and n2 = {5} ) or
                          (n1 = {9} and n2 = {6} ) or
                          (n1 = {10} and n2 = {7} ) or
                          (n1 = {11} and n2 = {8} ) 
}
pred par5 {
  some n1,n2: Note | n1 !=n2 and n1.next = n2 and 
                             ( (ser5[n1.s,n1.a] and ser5[n2.s,n2.a]) or
                               (ser5[n1.s,n1.t] and ser5[n2.s,n2.t]) or
                               (ser5[n1.t,n1.a] and ser5[n2.t,n2.a]) or
                               (ser5[n1.s,n1.b] and ser5[n2.s,n2.b]) or
                               (ser5[n1.b,n1.t] and ser5[n2.b,n2.t]) or
                               (ser5[n1.b,n1.a] and ser5[n2.b,n2.a]) )
}

//
// Set of Octaves for Parallel 8ths
//
pred ser8[n1,n2: Int] {
  (n1 = {0} and n2 = {7} ) or
                          (n1 = {1} and n2 = {8} ) or
                          (n1 = {2} and n2 = {9} ) or
                          (n1 = {3} and n2 = {10} ) or
                          (n1 = {4} and n2 = {11} ) or
                          //(n1 = {5} and n2 = {0} ) or
                          //(n1 = {6} and n2 = {1} ) or
                          (n1 = {7} and n2 = {0} ) or
                          (n1 = {8} and n2 = {1} ) or
                          (n1 = {9} and n2 = {2} ) or
                          (n1 = {10} and n2 = {3} ) or
                          (n1 = {11} and n2 = {4} ) 
}
pred par8 {
  some n1,n2: Note | n1 !=n2 and n1.next = n2 and 
                             ( (ser8[n1.s,n1.a] and ser8[n2.s,n2.a]) or
                               (ser8[n1.s,n1.t] and ser8[n2.s,n2.t]) or
                               (ser8[n1.t,n1.a] and ser8[n2.t,n2.a]) or
                               (ser8[n1.s,n1.b] and ser8[n2.s,n2.b]) or
                               (ser8[n1.b,n1.t] and ser8[n2.b,n2.t]) or
                               (ser8[n1.b,n1.a] and ser8[n2.b,n2.a]) )
}





pred A {
  all n: Note | n not in n.^next
}

fact allreachable {
   no n: Note, s: Staff | n not in s.head.*next
}

fact { #Note.s > 1}

fact {
 no n: Note, s1,s2: Staff | n in s1.head.*next and n in s2.head.*next and s1 != s2
}

fact { 
  no n: Note | n.s = n.next.s
}



pred show{
  A and  !par5 and allTriad
}

run show for 5 Int, exactly 4 Note
